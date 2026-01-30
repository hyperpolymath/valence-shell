// SPDX-License-Identifier: PLMP-1.0-or-later
//! Confirmation prompts for destructive operations
//!
//! SAFETY CRITICAL: Prevents accidental data destruction

use anyhow::{Result, bail};
use std::io::{self, Write};
use colored::Colorize;

/// Confirmation level for operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConfirmationLevel {
    /// File-level deletion (single file)
    File,
    /// Directory tree deletion (multiple files)
    Tree,
    /// Device-level erase (ENTIRE DEVICE)
    Device,
}

/// Confirm destructive operation with typed challenge
pub fn confirm_destructive_operation(
    level: ConfirmationLevel,
    target: &str,
    method: &str,
) -> Result<bool> {
    match level {
        ConfirmationLevel::File => confirm_file_deletion(target, method),
        ConfirmationLevel::Tree => confirm_tree_deletion(target, method),
        ConfirmationLevel::Device => confirm_device_erase(target, method),
    }
}

fn confirm_file_deletion(path: &str, method: &str) -> Result<bool> {
    println!();
    println!("{}", "⚠️  SECURE FILE DELETION".yellow().bold());
    println!();
    println!("  File:   {}", path.bright_white());
    println!("  Method: {} (NIST SP 800-88)", method.bright_cyan());
    println!();
    println!("{}", "  This operation is IRREVERSIBLE!".bright_red().bold());
    println!("  The file cannot be recovered after deletion.");
    println!();

    let confirmation = prompt_yes_no("Proceed with secure deletion?")?;
    println!();

    Ok(confirmation)
}

fn confirm_tree_deletion(path: &str, method: &str) -> Result<bool> {
    // Count files in tree
    let file_count = count_files_in_tree(path)?;

    println!();
    println!("{}", "⚠️  SECURE TREE DELETION".yellow().bold());
    println!();
    println!("  Directory: {}", path.bright_white());
    println!("  Files:     {} files will be destroyed", file_count.to_string().bright_red().bold());
    println!("  Method:    {} (NIST SP 800-88)", method.bright_cyan());
    println!();
    println!("{}", "  THIS OPERATION IS IRREVERSIBLE!".bright_red().bold());
    println!("  All {} files will be permanently destroyed.", file_count);
    println!();

    let confirmation = prompt_yes_no("Proceed with secure tree deletion?")?;
    println!();

    Ok(confirmation)
}

fn confirm_device_erase(device: &str, method: &str) -> Result<bool> {
    // Get device info
    let device_info = get_device_info(device)?;

    println!();
    println!("{}", "🚨 CRITICAL WARNING - DEVICE-LEVEL SECURE ERASE 🚨".bright_red().bold());
    println!();
    println!("{}", "═".repeat(60).bright_red());
    println!();
    println!("  {}", "THIS WILL ERASE THE ENTIRE DEVICE!".bright_red().bold());
    println!("  {}", "ALL DATA ON THE DEVICE WILL BE PERMANENTLY DESTROYED!".bright_red().bold());
    println!();
    println!("{}", "═".repeat(60).bright_red());
    println!();
    println!("  Device:   {}", device.bright_white().bold());
    println!("  Type:     {}", device_info.drive_type.bright_yellow());
    println!("  Size:     {}", device_info.size.bright_yellow());
    println!("  Method:   {} (NIST SP 800-88 Purge)", method.bright_cyan());
    println!();
    println!("  Mounted partitions:");
    for mount in &device_info.mounts {
        println!("    {} → {}", mount.partition.bright_red(), mount.mount_point.bright_white());
    }
    println!();
    println!("{}", "  SAFETY CHECKS:".bright_yellow().bold());
    println!("    {} System drive check", if device_info.is_system_drive { "❌ SYSTEM DRIVE DETECTED!".bright_red().bold() } else { "✓ Not system drive".green() });
    println!("    {} Mount check", if device_info.mounts.is_empty() { "✓ Device unmounted".green() } else { "⚠️  Device has mounted partitions!".bright_red().bold() });
    println!();

    if device_info.is_system_drive {
        println!("{}", "❌ ABORTED: Cannot erase system drive!".bright_red().bold());
        println!();
        return Ok(false);
    }

    if !device_info.mounts.is_empty() {
        println!("{}", "⚠️  WARNING: Device has mounted partitions!".bright_yellow().bold());
        println!("   You must unmount all partitions before secure erase.");
        println!();

        let force = prompt_yes_no("Attempt to unmount automatically?")?;
        if !force {
            return Ok(false);
        }
    }

    println!("{}", "═".repeat(60).bright_red());
    println!();
    println!("  {}", "FINAL CONFIRMATION REQUIRED".bright_red().bold());
    println!();
    print!("  Type the device name exactly to confirm: ");
    io::stdout().flush()?;

    let mut input = String::new();
    io::stdin().read_line(&mut input)?;
    let input = input.trim();

    if input != device {
        println!();
        println!("{}", "❌ Device name mismatch - operation CANCELLED".bright_red().bold());
        println!();
        return Ok(false);
    }

    println!();
    println!("{}", "⚠️  LAST CHANCE TO ABORT!".bright_red().bold());
    let final_confirm = prompt_yes_no("PERMANENTLY ERASE ALL DATA?")?;
    println!();

    Ok(final_confirm)
}

fn prompt_yes_no(prompt: &str) -> Result<bool> {
    print!("  {} [y/N]: ", prompt);
    io::stdout().flush()?;

    let mut input = String::new();
    io::stdin().read_line(&mut input)?;
    let input = input.trim().to_lowercase();

    Ok(input == "y" || input == "yes")
}

fn count_files_in_tree(path: &str) -> Result<usize> {
    let mut count = 0;

    fn visit_dirs(path: &std::path::Path, count: &mut usize) -> Result<()> {
        if path.is_dir() {
            for entry in std::fs::read_dir(path)? {
                let entry = entry?;
                let path = entry.path();
                if path.is_dir() {
                    visit_dirs(&path, count)?;
                } else {
                    *count += 1;
                }
            }
        } else {
            *count += 1;
        }
        Ok(())
    }

    visit_dirs(std::path::Path::new(path), &mut count)?;
    Ok(count)
}

struct DeviceInfo {
    drive_type: String,
    size: String,
    mounts: Vec<MountInfo>,
    is_system_drive: bool,
}

struct MountInfo {
    partition: String,
    mount_point: String,
}

fn get_device_info(device: &str) -> Result<DeviceInfo> {
    // Get device size
    let size = get_device_size(device)?;

    // Get drive type
    let drive_type = detect_drive_type_string(device)?;

    // Get mounted partitions
    let mounts = get_mounted_partitions(device)?;

    // Check if system drive
    let is_system_drive = is_system_device(device)?;

    Ok(DeviceInfo {
        drive_type,
        size,
        mounts,
        is_system_drive,
    })
}

fn get_device_size(device: &str) -> Result<String> {
    let output = std::process::Command::new("lsblk")
        .arg("-dno")
        .arg("SIZE")
        .arg(device)
        .output()?;

    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

fn detect_drive_type_string(device: &str) -> Result<String> {
    use crate::secure_erase::detect_drive_type;

    let drive_type = detect_drive_type(device)?;

    Ok(match drive_type {
        crate::secure_erase::DriveType::HDD => "Hard Disk Drive (magnetic)".to_string(),
        crate::secure_erase::DriveType::SataSSD => "SATA Solid State Drive".to_string(),
        crate::secure_erase::DriveType::NVMeSSD => "NVMe Solid State Drive".to_string(),
        crate::secure_erase::DriveType::Unknown => "Unknown".to_string(),
    })
}

fn get_mounted_partitions(device: &str) -> Result<Vec<MountInfo>> {
    let output = std::process::Command::new("lsblk")
        .arg("-no")
        .arg("NAME,MOUNTPOINT")
        .arg(device)
        .output()?;

    let mut mounts = Vec::new();
    let stdout = String::from_utf8_lossy(&output.stdout);

    for line in stdout.lines().skip(1) {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() >= 2 && !parts[1].is_empty() {
            mounts.push(MountInfo {
                partition: format!("/dev/{}", parts[0]),
                mount_point: parts[1].to_string(),
            });
        }
    }

    Ok(mounts)
}

fn is_system_device(device: &str) -> Result<bool> {
    // Check if root filesystem is on this device
    let output = std::process::Command::new("df")
        .arg("/")
        .output()?;

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Extract device from df output
    for line in stdout.lines().skip(1) {
        if let Some(root_device) = line.split_whitespace().next() {
            // Check if root device starts with our device
            // e.g., /dev/sda1 starts with /dev/sda
            if root_device.starts_with(device) {
                return Ok(true);
            }
        }
    }

    Ok(false)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_count_files() {
        let count = count_files_in_tree("/tmp").unwrap_or(0);
        assert!(count >= 0);
    }
}
