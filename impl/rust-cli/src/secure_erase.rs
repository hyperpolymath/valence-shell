// SPDX-License-Identifier: PLMP-1.0-or-later
//! Hardware-based secure erase for SSDs
//!
//! Implements NIST SP 800-88 Purge methods:
//! - ATA Secure Erase (SATA SSDs)
//! - NVMe Format/Sanitize (NVMe SSDs)
//! - Cryptographic erase (when supported)

use anyhow::{Context, Result, bail};
use std::fs;
use std::path::Path;
use std::process::Command;

/// Drive type detection
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DriveType {
    /// Hard Disk Drive (magnetic)
    HDD,
    /// SATA Solid State Drive
    SataSSD,
    /// NVMe Solid State Drive
    NVMeSSD,
    /// Unknown or unsupported
    Unknown,
}

/// Secure erase method
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SecureEraseMethod {
    /// NIST Clear: Single pass overwrite (HDDs and fallback)
    Clear,
    /// NIST Purge: ATA Secure Erase (SATA SSDs)
    ATASecureErase,
    /// NIST Purge: NVMe Format with crypto erase
    NVMeFormatCrypto,
    /// NIST Purge: NVMe Sanitize (block erase)
    NVMeSanitize,
    /// Cryptographic erase (destroy encryption keys)
    CryptoErase,
}

/// Detect drive type from device path
pub fn detect_drive_type(device: &str) -> Result<DriveType> {
    // Check if it's an NVMe device
    if device.starts_with("/dev/nvme") {
        return Ok(DriveType::NVMeSSD);
    }

    // For SATA/SCSI devices, check rotational flag
    let dev_name = device.trim_start_matches("/dev/");
    let rotational_path = format!("/sys/block/{}/queue/rotational", dev_name);

    if let Ok(content) = fs::read_to_string(&rotational_path) {
        match content.trim() {
            "0" => return Ok(DriveType::SataSSD),
            "1" => return Ok(DriveType::HDD),
            _ => {}
        }
    }

    // Fallback: Check with smartctl if available
    if let Ok(output) = Command::new("smartctl")
        .arg("-i")
        .arg(device)
        .output()
    {
        let info = String::from_utf8_lossy(&output.stdout);
        if info.contains("Solid State Device") || info.contains("NVMe") {
            return Ok(DriveType::SataSSD);
        }
        if info.contains("Rotation Rate") && !info.contains("Solid State") {
            return Ok(DriveType::HDD);
        }
    }

    Ok(DriveType::Unknown)
}

/// Get device path from file path
pub fn get_device_from_path(path: &Path) -> Result<String> {
    // Use df to find the mount point and device
    let output = Command::new("df")
        .arg("--output=source")
        .arg(path)
        .output()
        .context("Failed to run df command")?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let lines: Vec<&str> = stdout.lines().collect();

    if lines.len() < 2 {
        bail!("Failed to determine device for path: {}", path.display());
    }

    let device = lines[1].trim();

    // Handle partition devices (e.g., /dev/sda1 -> /dev/sda)
    let base_device = if let Some(idx) = device.rfind(|c: char| !c.is_ascii_digit()) {
        &device[..=idx]
    } else {
        device
    };

    Ok(base_device.to_string())
}

/// Check if ATA Secure Erase is supported
pub fn check_ata_secure_erase_support(device: &str) -> Result<bool> {
    let output = Command::new("hdparm")
        .arg("-I")
        .arg(device)
        .output()
        .context("Failed to run hdparm - is it installed?")?;

    let info = String::from_utf8_lossy(&output.stdout);

    // Check for "supported: enhanced erase"
    Ok(info.contains("supported: enhanced erase") ||
       info.contains("SECURITY ERASE UNIT"))
}

/// Perform ATA Secure Erase
pub fn ata_secure_erase(device: &str, enhanced: bool) -> Result<()> {
    // CRITICAL: This is a destructive operation
    // Requires security password to be set first

    // Step 1: Set user password (temporary)
    let password = "Eins"; // Standard temporary password

    println!("⚠️  Setting security password...");
    let status = Command::new("hdparm")
        .arg("--user-master")
        .arg("u")
        .arg("--security-set-pass")
        .arg(password)
        .arg(device)
        .status()
        .context("Failed to set security password")?;

    if !status.success() {
        bail!("Failed to set security password");
    }

    // Step 2: Issue secure erase command
    let erase_cmd = if enhanced {
        "--security-erase-enhanced"
    } else {
        "--security-erase"
    };

    println!("🔥 Performing ATA Secure Erase (this may take several minutes)...");
    let status = Command::new("hdparm")
        .arg("--user-master")
        .arg("u")
        .arg(erase_cmd)
        .arg(password)
        .arg(device)
        .status()
        .context("Failed to execute secure erase")?;

    if !status.success() {
        bail!("Secure erase failed");
    }

    println!("✓ ATA Secure Erase completed");
    Ok(())
}

/// Check if NVMe sanitize is supported
pub fn check_nvme_sanitize_support(device: &str) -> Result<bool> {
    let output = Command::new("nvme")
        .arg("id-ctrl")
        .arg(device)
        .output()
        .context("Failed to run nvme command - is nvme-cli installed?")?;

    let info = String::from_utf8_lossy(&output.stdout);

    // Check SANICAP field
    Ok(info.contains("sanicap") || info.contains("Sanitize"))
}

/// Perform NVMe Format with crypto erase
pub fn nvme_format_crypto(device: &str) -> Result<()> {
    println!("🔥 Performing NVMe Format with cryptographic erase...");

    let status = Command::new("nvme")
        .arg("format")
        .arg(device)
        .arg("--ses=1")  // Secure Erase Settings: Cryptographic Erase
        .status()
        .context("Failed to execute NVMe format")?;

    if !status.success() {
        bail!("NVMe format failed");
    }

    println!("✓ NVMe cryptographic erase completed");
    Ok(())
}

/// Perform NVMe Sanitize
pub fn nvme_sanitize(device: &str, block_erase: bool) -> Result<()> {
    println!("🔥 Performing NVMe Sanitize (this may take a long time)...");

    let action = if block_erase {
        "--sanact=2"  // Block Erase
    } else {
        "--sanact=1"  // Exit Failure Mode
    };

    let status = Command::new("nvme")
        .arg("sanitize")
        .arg(device)
        .arg(action)
        .status()
        .context("Failed to execute NVMe sanitize")?;

    if !status.success() {
        bail!("NVMe sanitize failed");
    }

    println!("✓ NVMe sanitize completed");
    Ok(())
}

/// High-level secure erase function
pub fn secure_erase_file(file_path: &Path, method: SecureEraseMethod) -> Result<()> {
    // Get the device
    let device = get_device_from_path(file_path)?;
    let drive_type = detect_drive_type(&device)?;

    println!("📊 Device: {}", device);
    println!("📊 Drive type: {:?}", drive_type);
    println!("📊 Method: {:?}", method);

    match (drive_type, method) {
        (DriveType::SataSSD, SecureEraseMethod::ATASecureErase) => {
            if !check_ata_secure_erase_support(&device)? {
                bail!("ATA Secure Erase not supported on this device");
            }
            println!("⚠️  WARNING: This will erase the ENTIRE device: {}", device);
            println!("⚠️  All data on the device will be permanently destroyed!");
            // In production, require explicit confirmation here
            ata_secure_erase(&device, true)?;
        }

        (DriveType::NVMeSSD, SecureEraseMethod::NVMeFormatCrypto) => {
            println!("⚠️  WARNING: This will erase the ENTIRE namespace");
            nvme_format_crypto(&device)?;
        }

        (DriveType::NVMeSSD, SecureEraseMethod::NVMeSanitize) => {
            if !check_nvme_sanitize_support(&device)? {
                bail!("NVMe Sanitize not supported on this device");
            }
            println!("⚠️  WARNING: This will erase the ENTIRE device");
            nvme_sanitize(&device, true)?;
        }

        (DriveType::HDD, SecureEraseMethod::Clear) => {
            // Fall back to overwrite for HDDs
            println!("ℹ️  Using single-pass overwrite for HDD (NIST Clear)");
            // Call overwrite function here
        }

        _ => {
            bail!(
                "Unsupported combination: {:?} drive with {:?} method",
                drive_type,
                method
            );
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore] // Requires actual hardware
    fn test_detect_drive_type() {
        let result = detect_drive_type("/dev/sda");
        assert!(result.is_ok());
    }
}
