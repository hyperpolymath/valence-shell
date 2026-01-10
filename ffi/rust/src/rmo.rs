// SPDX-License-Identifier: AGPL-3.0-or-later
//! RMO (Remove-Match-Obliterate) Secure Deletion
//!
//! This module implements secure file deletion for GDPR "right to be forgotten"
//! compliance. Unlike normal deletion which just removes directory entries,
//! RMO overwrites file content multiple times before deletion.
//!
//! # Security Model
//!
//! RMO provides defense against:
//! - File recovery from magnetic media (multiple overwrite passes)
//! - Memory forensics (zeroization of buffers)
//! - Timing attacks (constant-time operations where possible)
//!
//! # Limitations
//!
//! - Cannot guarantee deletion on SSDs with wear leveling
//! - Cannot guarantee deletion on copy-on-write filesystems (ZFS, Btrfs)
//! - Cannot prevent recovery from filesystem journals
//! - For true security, use full-disk encryption + key destruction
//!
//! # Proof Status
//!
//! Theorem `obliterate_leaves_no_trace` - PENDING (to be added to Coq)

use crate::errors::{FfiError, FfiResult};
use rand::RngCore;
use std::fs::{File, OpenOptions};
use std::io::{Seek, SeekFrom, Write};
use std::path::Path;
use zeroize::Zeroize;

/// Default number of overwrite passes
pub const DEFAULT_PASSES: usize = 3;

/// Block size for overwrite operations (4KB - typical filesystem block)
const BLOCK_SIZE: usize = 4096;

/// Overwrite patterns for secure deletion
#[derive(Debug, Clone, Copy)]
pub enum OverwritePattern {
    /// All zeros (0x00)
    Zeros,
    /// All ones (0xFF)
    Ones,
    /// Random data
    Random,
    /// Alternating pattern (0x55 = 01010101)
    Alternating55,
    /// Alternating pattern (0xAA = 10101010)
    AlternatingAA,
    /// DoD 5220.22-M compliant pattern
    DoDPattern(u8),
}

impl OverwritePattern {
    /// Fill a buffer with this pattern
    fn fill_buffer(&self, buffer: &mut [u8], rng: &mut impl RngCore) {
        match self {
            OverwritePattern::Zeros => buffer.fill(0x00),
            OverwritePattern::Ones => buffer.fill(0xFF),
            OverwritePattern::Random => rng.fill_bytes(buffer),
            OverwritePattern::Alternating55 => buffer.fill(0x55),
            OverwritePattern::AlternatingAA => buffer.fill(0xAA),
            OverwritePattern::DoDPattern(byte) => buffer.fill(*byte),
        }
    }
}

/// Secure deletion configuration
#[derive(Debug, Clone)]
pub struct RmoConfig {
    /// Number of overwrite passes
    pub passes: usize,
    /// Verify overwrites by reading back
    pub verify: bool,
    /// Patterns to use for each pass
    pub patterns: Vec<OverwritePattern>,
}

impl Default for RmoConfig {
    fn default() -> Self {
        // DoD 5220.22-M style: zeros, ones, random
        Self {
            passes: DEFAULT_PASSES,
            verify: false,
            patterns: vec![
                OverwritePattern::Zeros,
                OverwritePattern::Ones,
                OverwritePattern::Random,
            ],
        }
    }
}

impl RmoConfig {
    /// Create a config with custom number of passes
    pub fn with_passes(passes: usize) -> Self {
        let mut patterns = Vec::with_capacity(passes);
        for i in 0..passes {
            patterns.push(match i % 3 {
                0 => OverwritePattern::Zeros,
                1 => OverwritePattern::Ones,
                _ => OverwritePattern::Random,
            });
        }
        Self {
            passes,
            verify: false,
            patterns,
        }
    }

    /// Gutmann 35-pass secure deletion
    pub fn gutmann() -> Self {
        let patterns = vec![
            // Passes 1-4: Random
            OverwritePattern::Random,
            OverwritePattern::Random,
            OverwritePattern::Random,
            OverwritePattern::Random,
            // Passes 5-31: Specific patterns for magnetic media
            OverwritePattern::DoDPattern(0x55),
            OverwritePattern::DoDPattern(0xAA),
            OverwritePattern::DoDPattern(0x92),
            OverwritePattern::DoDPattern(0x49),
            OverwritePattern::DoDPattern(0x24),
            OverwritePattern::DoDPattern(0x00),
            OverwritePattern::DoDPattern(0x11),
            OverwritePattern::DoDPattern(0x22),
            OverwritePattern::DoDPattern(0x33),
            OverwritePattern::DoDPattern(0x44),
            OverwritePattern::DoDPattern(0x55),
            OverwritePattern::DoDPattern(0x66),
            OverwritePattern::DoDPattern(0x77),
            OverwritePattern::DoDPattern(0x88),
            OverwritePattern::DoDPattern(0x99),
            OverwritePattern::DoDPattern(0xAA),
            OverwritePattern::DoDPattern(0xBB),
            OverwritePattern::DoDPattern(0xCC),
            OverwritePattern::DoDPattern(0xDD),
            OverwritePattern::DoDPattern(0xEE),
            OverwritePattern::DoDPattern(0xFF),
            OverwritePattern::DoDPattern(0x92),
            OverwritePattern::DoDPattern(0x49),
            OverwritePattern::DoDPattern(0x24),
            OverwritePattern::DoDPattern(0x6D),
            OverwritePattern::DoDPattern(0xB6),
            OverwritePattern::DoDPattern(0xDB),
            // Passes 32-35: Random
            OverwritePattern::Random,
            OverwritePattern::Random,
            OverwritePattern::Random,
            OverwritePattern::Random,
        ];
        Self {
            passes: 35,
            verify: false,
            patterns,
        }
    }
}

/// Securely delete a file with default configuration
///
/// # Arguments
/// * `path` - Path to file to delete
/// * `passes` - Number of overwrite passes
///
/// # Proof Status
/// PENDING - obliterate_precondition and obliterate_leaves_no_trace
pub fn secure_delete(path: &Path, passes: usize) -> FfiResult<()> {
    let config = RmoConfig::with_passes(passes);
    secure_delete_with_config(path, &config)
}

/// Securely delete a file with custom configuration
pub fn secure_delete_with_config(path: &Path, config: &RmoConfig) -> FfiResult<()> {
    // Get file size
    let metadata = std::fs::metadata(path)
        .map_err(|e| FfiError::RmoError(format!("Failed to get file metadata: {}", e)))?;

    let file_size = metadata.len() as usize;

    if file_size == 0 {
        // Empty file - just delete
        std::fs::remove_file(path)
            .map_err(|e| FfiError::RmoError(format!("Failed to delete file: {}", e)))?;
        return Ok(());
    }

    // Open file for writing
    let mut file = OpenOptions::new()
        .write(true)
        .open(path)
        .map_err(|e| FfiError::RmoError(format!("Failed to open file for overwrite: {}", e)))?;

    // Create RNG for random patterns
    let mut rng = rand::thread_rng();

    // Allocate buffer (will be zeroized on drop)
    let mut buffer = vec![0u8; BLOCK_SIZE];

    // Perform overwrite passes
    for (pass_num, pattern) in config.patterns.iter().take(config.passes).enumerate() {
        // Seek to beginning
        file.seek(SeekFrom::Start(0))
            .map_err(|e| FfiError::RmoError(format!("Seek failed on pass {}: {}", pass_num, e)))?;

        let mut bytes_written = 0usize;

        while bytes_written < file_size {
            let chunk_size = std::cmp::min(BLOCK_SIZE, file_size - bytes_written);

            // Fill buffer with pattern
            pattern.fill_buffer(&mut buffer[..chunk_size], &mut rng);

            // Write buffer
            file.write_all(&buffer[..chunk_size])
                .map_err(|e| FfiError::RmoError(format!("Write failed on pass {}: {}", pass_num, e)))?;

            bytes_written += chunk_size;
        }

        // Ensure data is flushed to disk
        file.sync_all()
            .map_err(|e| FfiError::RmoError(format!("Sync failed on pass {}: {}", pass_num, e)))?;

        // Verify if requested
        if config.verify {
            verify_overwrite(&mut file, file_size, &buffer[..], pattern, &mut rng)?;
        }
    }

    // Zeroize buffer before dropping
    buffer.zeroize();

    // Close file handle
    drop(file);

    // Truncate file to zero length (optional extra step)
    let file = OpenOptions::new()
        .write(true)
        .truncate(true)
        .open(path)
        .map_err(|e| FfiError::RmoError(format!("Failed to truncate: {}", e)))?;
    drop(file);

    // Finally, delete the file
    std::fs::remove_file(path)
        .map_err(|e| FfiError::RmoError(format!("Failed to delete file: {}", e)))?;

    Ok(())
}

/// Verify that overwrite was successful by reading back
fn verify_overwrite(
    file: &mut File,
    file_size: usize,
    _expected: &[u8],
    pattern: &OverwritePattern,
    rng: &mut impl RngCore,
) -> FfiResult<()> {
    use std::io::Read;

    // Random patterns can't be verified
    if matches!(pattern, OverwritePattern::Random) {
        return Ok(());
    }

    file.seek(SeekFrom::Start(0))
        .map_err(|e| FfiError::RmoError(format!("Verify seek failed: {}", e)))?;

    let mut verify_buffer = vec![0u8; BLOCK_SIZE];
    let mut expected_buffer = vec![0u8; BLOCK_SIZE];
    pattern.fill_buffer(&mut expected_buffer, rng);

    let mut bytes_verified = 0usize;

    while bytes_verified < file_size {
        let chunk_size = std::cmp::min(BLOCK_SIZE, file_size - bytes_verified);

        file.read_exact(&mut verify_buffer[..chunk_size])
            .map_err(|e| FfiError::RmoError(format!("Verify read failed: {}", e)))?;

        if verify_buffer[..chunk_size] != expected_buffer[..chunk_size] {
            return Err(FfiError::RmoError(
                "Verification failed: data mismatch".to_string()
            ));
        }

        bytes_verified += chunk_size;
    }

    verify_buffer.zeroize();
    expected_buffer.zeroize();

    Ok(())
}

/// Securely wipe and delete all files in a directory
///
/// # Warning
/// This is a destructive operation that cannot be undone.
pub fn secure_delete_directory(path: &Path, passes: usize) -> FfiResult<()> {
    if !path.is_dir() {
        return Err(FfiError::RmoError("Not a directory".to_string()));
    }

    let config = RmoConfig::with_passes(passes);

    // Recursively process directory
    secure_delete_directory_recursive(path, &config)?;

    // Remove the now-empty directory
    std::fs::remove_dir(path)
        .map_err(|e| FfiError::RmoError(format!("Failed to remove directory: {}", e)))?;

    Ok(())
}

fn secure_delete_directory_recursive(path: &Path, config: &RmoConfig) -> FfiResult<()> {
    for entry in std::fs::read_dir(path)
        .map_err(|e| FfiError::RmoError(format!("Failed to read directory: {}", e)))?
    {
        let entry = entry
            .map_err(|e| FfiError::RmoError(format!("Failed to read entry: {}", e)))?;
        let entry_path = entry.path();

        if entry_path.is_dir() {
            secure_delete_directory_recursive(&entry_path, config)?;
            std::fs::remove_dir(&entry_path)
                .map_err(|e| FfiError::RmoError(format!("Failed to remove dir: {}", e)))?;
        } else {
            secure_delete_with_config(&entry_path, config)?;
        }
    }

    Ok(())
}

/// Estimate time for secure deletion
pub fn estimate_deletion_time(file_size: u64, passes: usize) -> std::time::Duration {
    // Rough estimate: 50MB/s write speed
    const BYTES_PER_SECOND: u64 = 50 * 1024 * 1024;

    let total_bytes = file_size * passes as u64;
    let seconds = total_bytes / BYTES_PER_SECOND;

    std::time::Duration::from_secs(seconds.max(1))
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_secure_delete_file() {
        let tmp = tempdir().unwrap();
        let file_path = tmp.path().join("test_file.txt");

        // Create test file
        std::fs::write(&file_path, "sensitive data here").unwrap();
        assert!(file_path.exists());

        // Secure delete
        secure_delete(&file_path, 3).unwrap();

        // File should be gone
        assert!(!file_path.exists());
    }

    #[test]
    fn test_secure_delete_empty_file() {
        let tmp = tempdir().unwrap();
        let file_path = tmp.path().join("empty.txt");

        // Create empty file
        std::fs::write(&file_path, "").unwrap();
        assert!(file_path.exists());

        // Secure delete
        secure_delete(&file_path, 3).unwrap();

        // File should be gone
        assert!(!file_path.exists());
    }

    #[test]
    fn test_overwrite_patterns() {
        let mut buffer = vec![0u8; 16];
        let mut rng = rand::thread_rng();

        OverwritePattern::Zeros.fill_buffer(&mut buffer, &mut rng);
        assert!(buffer.iter().all(|&b| b == 0x00));

        OverwritePattern::Ones.fill_buffer(&mut buffer, &mut rng);
        assert!(buffer.iter().all(|&b| b == 0xFF));

        OverwritePattern::Alternating55.fill_buffer(&mut buffer, &mut rng);
        assert!(buffer.iter().all(|&b| b == 0x55));
    }

    #[test]
    fn test_gutmann_config() {
        let config = RmoConfig::gutmann();
        assert_eq!(config.passes, 35);
        assert_eq!(config.patterns.len(), 35);
    }
}
