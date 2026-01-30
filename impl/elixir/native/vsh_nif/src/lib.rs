// SPDX-License-Identifier: PLMP-1.0-or-later
//! Rust NIF for Valence Shell secure erase operations
//!
//! Exposes hardware-based secure erase functions to Elixir

use rustler::Atom;

// Import from vsh crate
use vsh::secure_erase::{
    ata_secure_erase, check_ata_secure_erase_support, check_nvme_sanitize_support,
    detect_drive_type, nvme_format_crypto, nvme_sanitize, DriveType,
};

mod atoms {
    rustler::atoms! {
        ok,
        error,
        hdd,
        sata_ssd,
        nvme_ssd,
        unknown,
    }
}

rustler::init!("Elixir.VSH.SecureErase");

/// Detect drive type
#[rustler::nif]
fn detect_drive_type_nif(device: String) -> (Atom, String) {
    match detect_drive_type(&device) {
        Ok(DriveType::HDD) => (atoms::ok(), "hdd".to_string()),
        Ok(DriveType::SataSSD) => (atoms::ok(), "sata_ssd".to_string()),
        Ok(DriveType::NVMeSSD) => (atoms::ok(), "nvme_ssd".to_string()),
        Ok(DriveType::Unknown) => (atoms::ok(), "unknown".to_string()),
        Err(e) => (atoms::error(), format!("{:#}", e)),
    }
}

/// Check ATA Secure Erase support
#[rustler::nif]
fn check_ata_support_nif(device: String) -> (Atom, String) {
    match check_ata_secure_erase_support(&device) {
        Ok(true) => (atoms::ok(), "supported".to_string()),
        Ok(false) => (atoms::ok(), "not_supported".to_string()),
        Err(e) => (atoms::error(), format!("{:#}", e)),
    }
}

/// Check NVMe Sanitize support
#[rustler::nif]
fn check_nvme_sanitize_support_nif(device: String) -> (Atom, String) {
    match check_nvme_sanitize_support(&device) {
        Ok(true) => (atoms::ok(), "supported".to_string()),
        Ok(false) => (atoms::ok(), "not_supported".to_string()),
        Err(e) => (atoms::error(), format!("{:#}", e)),
    }
}

/// Perform ATA Secure Erase
/// NOTE: Confirmation must be handled on Elixir side before calling
#[rustler::nif]
fn ata_secure_erase_nif(device: String, enhanced: bool) -> (Atom, String) {
    match ata_secure_erase(&device, enhanced) {
        Ok(()) => (atoms::ok(), "erase_complete".to_string()),
        Err(e) => (atoms::error(), format!("{:#}", e)),
    }
}

/// Perform NVMe Format with crypto erase
/// NOTE: Confirmation must be handled on Elixir side before calling
#[rustler::nif]
fn nvme_format_crypto_nif(device: String) -> (Atom, String) {
    match nvme_format_crypto(&device) {
        Ok(()) => (atoms::ok(), "erase_complete".to_string()),
        Err(e) => (atoms::error(), format!("{:#}", e)),
    }
}

/// Perform NVMe Sanitize
/// NOTE: Confirmation must be handled on Elixir side before calling
#[rustler::nif]
fn nvme_sanitize_nif(device: String, block_erase: bool) -> (Atom, String) {
    match nvme_sanitize(&device, block_erase) {
        Ok(()) => (atoms::ok(), "erase_complete".to_string()),
        Err(e) => (atoms::error(), format!("{:#}", e)),
    }
}
