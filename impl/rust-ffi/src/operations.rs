// SPDX-License-Identifier: AGPL-3.0-or-later
//! Filesystem Operations Module
//!
//! This module provides additional filesystem operations and utilities
//! that complement the core FfiContext operations.
//!
//! # Operation Categories
//!
//! 1. **Atomic Operations** - Operations that are atomic at the filesystem level
//! 2. **Batch Operations** - Operations on multiple files/directories
//! 3. **Query Operations** - Non-modifying operations (stat, exists, etc.)
//! 4. **Permission Operations** - Unix permission management

use crate::errors::{FfiError, FfiResult, PosixError};
use crate::preconditions::Preconditions;
use std::fs::{self, Metadata, Permissions};
use std::path::{Path, PathBuf};
use std::time::SystemTime;

/// File type enumeration matching Coq definitions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileType {
    /// Regular file
    RegularFile,
    /// Directory
    Directory,
    /// Symbolic link
    Symlink,
    /// Block device
    BlockDevice,
    /// Character device
    CharDevice,
    /// Named pipe (FIFO)
    Fifo,
    /// Unix domain socket
    Socket,
    /// Unknown file type
    Unknown,
}

impl FileType {
    /// Convert from std::fs::FileType
    pub fn from_std(ft: std::fs::FileType) -> Self {
        if ft.is_file() {
            FileType::RegularFile
        } else if ft.is_dir() {
            FileType::Directory
        } else if ft.is_symlink() {
            FileType::Symlink
        } else {
            // Check for special file types on Unix
            #[cfg(unix)]
            {
                use std::os::unix::fs::FileTypeExt;
                if ft.is_block_device() {
                    return FileType::BlockDevice;
                }
                if ft.is_char_device() {
                    return FileType::CharDevice;
                }
                if ft.is_fifo() {
                    return FileType::Fifo;
                }
                if ft.is_socket() {
                    return FileType::Socket;
                }
            }
            FileType::Unknown
        }
    }

    /// Get Coq constructor name
    pub fn coq_name(&self) -> &'static str {
        match self {
            FileType::RegularFile => "File",
            FileType::Directory => "Dir",
            FileType::Symlink => "Symlink",
            FileType::BlockDevice => "BlockDev",
            FileType::CharDevice => "CharDev",
            FileType::Fifo => "Fifo",
            FileType::Socket => "Socket",
            FileType::Unknown => "Unknown",
        }
    }
}

/// File information structure
#[derive(Debug, Clone)]
pub struct FileInfo {
    /// Path to the file
    pub path: PathBuf,
    /// File type
    pub file_type: FileType,
    /// Size in bytes
    pub size: u64,
    /// Last modification time
    pub modified: Option<SystemTime>,
    /// Last access time
    pub accessed: Option<SystemTime>,
    /// Creation time (if available)
    pub created: Option<SystemTime>,
    /// Unix permissions (mode bits)
    #[cfg(unix)]
    pub mode: u32,
    /// Owner user ID
    #[cfg(unix)]
    pub uid: u32,
    /// Owner group ID
    #[cfg(unix)]
    pub gid: u32,
    /// Number of hard links
    #[cfg(unix)]
    pub nlink: u64,
}

impl FileInfo {
    /// Create FileInfo from path
    pub fn from_path(path: &Path) -> FfiResult<Self> {
        let metadata = fs::metadata(path)?;
        Self::from_metadata(path.to_path_buf(), &metadata)
    }

    /// Create FileInfo from symlink (doesn't follow)
    pub fn from_symlink(path: &Path) -> FfiResult<Self> {
        let metadata = fs::symlink_metadata(path)?;
        Self::from_metadata(path.to_path_buf(), &metadata)
    }

    /// Create from metadata
    fn from_metadata(path: PathBuf, metadata: &Metadata) -> FfiResult<Self> {
        #[cfg(unix)]
        use std::os::unix::fs::MetadataExt;

        Ok(Self {
            path,
            file_type: FileType::from_std(metadata.file_type()),
            size: metadata.len(),
            modified: metadata.modified().ok(),
            accessed: metadata.accessed().ok(),
            created: metadata.created().ok(),
            #[cfg(unix)]
            mode: metadata.mode(),
            #[cfg(unix)]
            uid: metadata.uid(),
            #[cfg(unix)]
            gid: metadata.gid(),
            #[cfg(unix)]
            nlink: metadata.nlink(),
        })
    }
}

/// Directory entry for listing operations
#[derive(Debug, Clone)]
pub struct DirEntry {
    /// Entry name (not full path)
    pub name: String,
    /// Full path
    pub path: PathBuf,
    /// File type
    pub file_type: FileType,
}

/// List directory contents
///
/// # Coq Reference
/// ```coq
/// Definition list_directory (path : Path) (fs : Filesystem) : option (list Path) :=
///   match lookup path fs with
///   | Some (Dir entries) => Some (map fst entries)
///   | _ => None
///   end.
/// ```
pub fn list_directory(path: &Path) -> FfiResult<Vec<DirEntry>> {
    if !path.exists() {
        return Err(FfiError::Posix(PosixError::Enoent));
    }

    if !path.is_dir() {
        return Err(FfiError::Posix(PosixError::Enotdir));
    }

    let mut entries = Vec::new();

    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let file_type = entry.file_type()
            .map(FileType::from_std)
            .unwrap_or(FileType::Unknown);

        entries.push(DirEntry {
            name: entry.file_name().to_string_lossy().to_string(),
            path: entry.path(),
            file_type,
        });
    }

    Ok(entries)
}

/// Check if path exists
///
/// # Coq Reference
/// ```coq
/// Definition path_exists (path : Path) (fs : Filesystem) : Prop :=
///   exists entry, lookup path fs = Some entry.
/// ```
pub fn path_exists(path: &Path) -> bool {
    path.exists()
}

/// Check if path is a directory
pub fn is_directory(path: &Path) -> bool {
    path.is_dir()
}

/// Check if path is a regular file
pub fn is_file(path: &Path) -> bool {
    path.is_file()
}

/// Check if path is a symbolic link
pub fn is_symlink(path: &Path) -> bool {
    path.symlink_metadata()
        .map(|m| m.file_type().is_symlink())
        .unwrap_or(false)
}

/// Get file size
pub fn file_size(path: &Path) -> FfiResult<u64> {
    let metadata = fs::metadata(path)?;
    Ok(metadata.len())
}

/// Create parent directories if they don't exist
///
/// # Proof Status
/// PENDING - mkdir_p_reversible theorem
pub fn mkdir_p(path: &Path) -> FfiResult<()> {
    fs::create_dir_all(path)?;
    Ok(())
}

/// Set file permissions (Unix)
#[cfg(unix)]
pub fn chmod(path: &Path, mode: u32) -> FfiResult<()> {
    use std::os::unix::fs::PermissionsExt;

    if !path.exists() {
        return Err(FfiError::Posix(PosixError::Enoent));
    }

    let permissions = Permissions::from_mode(mode);
    fs::set_permissions(path, permissions)?;
    Ok(())
}

/// Change file ownership (Unix)
#[cfg(unix)]
pub fn chown(path: &Path, uid: Option<u32>, gid: Option<u32>) -> FfiResult<()> {
    use std::os::unix::ffi::OsStrExt;

    if !path.exists() {
        return Err(FfiError::Posix(PosixError::Enoent));
    }

    let path_cstr = std::ffi::CString::new(path.as_os_str().as_bytes())
        .map_err(|_| FfiError::InvalidPath("Path contains null byte".to_string()))?;

    let uid = uid.map(|u| u as libc::uid_t).unwrap_or(u32::MAX as libc::uid_t);
    let gid = gid.map(|g| g as libc::gid_t).unwrap_or(u32::MAX as libc::gid_t);

    let result = unsafe { libc::chown(path_cstr.as_ptr(), uid, gid) };

    if result != 0 {
        let errno = std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
        return Err(FfiError::Posix(PosixError::from_errno(errno)));
    }

    Ok(())
}

/// Touch a file (create or update timestamp)
pub fn touch(path: &Path) -> FfiResult<()> {
    if path.exists() {
        // Update modification time
        let now = filetime::FileTime::now();
        filetime::set_file_mtime(path, now)
            .map_err(|e| FfiError::Io(e))?;
    } else {
        // Create empty file
        fs::write(path, "")?;
    }
    Ok(())
}

/// Atomic file write using rename
///
/// Writes to a temporary file then atomically renames to target.
/// This ensures the file is never in a partial state.
///
/// # Proof Status
/// PENDING - atomic_write_safe theorem
pub fn atomic_write(path: &Path, content: &[u8]) -> FfiResult<()> {
    let parent = path.parent()
        .ok_or_else(|| FfiError::InvalidPath("No parent directory".to_string()))?;

    // Create temp file in same directory (for same-filesystem rename)
    let temp_name = format!(".{}.tmp.{}",
        path.file_name().unwrap_or_default().to_string_lossy(),
        std::process::id()
    );
    let temp_path = parent.join(&temp_name);

    // Write to temp file
    fs::write(&temp_path, content)?;

    // Sync to disk
    let file = fs::File::open(&temp_path)?;
    file.sync_all()?;
    drop(file);

    // Atomic rename
    fs::rename(&temp_path, path)?;

    // Sync parent directory (important for durability)
    #[cfg(unix)]
    {
        if let Ok(dir) = fs::File::open(parent) {
            let _ = dir.sync_all();
        }
    }

    Ok(())
}

/// Copy file with verification
pub fn verified_copy(src: &Path, dst: &Path) -> FfiResult<()> {
    Preconditions::copy_file(src, dst)?;

    // Read source
    let content = fs::read(src)?;
    let src_hash = hash_content(&content);

    // Write destination
    fs::write(dst, &content)?;

    // Verify
    let dst_content = fs::read(dst)?;
    let dst_hash = hash_content(&dst_content);

    if src_hash != dst_hash {
        // Clean up failed copy
        let _ = fs::remove_file(dst);
        return Err(FfiError::RmoError("Copy verification failed".to_string()));
    }

    Ok(())
}

/// Calculate hash of content for verification
fn hash_content(content: &[u8]) -> [u8; 32] {
    use sha2::{Sha256, Digest};
    let mut hasher = Sha256::new();
    hasher.update(content);
    hasher.finalize().into()
}

/// Recursive directory size calculation
pub fn directory_size(path: &Path) -> FfiResult<u64> {
    if !path.is_dir() {
        return Err(FfiError::Posix(PosixError::Enotdir));
    }

    fn calculate_size(path: &Path) -> std::io::Result<u64> {
        let mut total = 0u64;

        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_dir() {
                total += calculate_size(&path)?;
            } else {
                total += entry.metadata()?.len();
            }
        }

        Ok(total)
    }

    calculate_size(path).map_err(FfiError::from)
}

/// Count files in directory (recursive)
pub fn count_files(path: &Path) -> FfiResult<usize> {
    if !path.is_dir() {
        return Err(FfiError::Posix(PosixError::Enotdir));
    }

    fn count(path: &Path) -> std::io::Result<usize> {
        let mut total = 0;

        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_dir() {
                total += count(&path)?;
            } else {
                total += 1;
            }
        }

        Ok(total)
    }

    count(path).map_err(FfiError::from)
}

/// Find files matching a predicate
pub fn find_files<F>(root: &Path, predicate: F) -> FfiResult<Vec<PathBuf>>
where
    F: Fn(&Path) -> bool,
{
    let mut results = Vec::new();
    find_files_recursive(root, &predicate, &mut results)?;
    Ok(results)
}

fn find_files_recursive<F>(path: &Path, predicate: &F, results: &mut Vec<PathBuf>) -> FfiResult<()>
where
    F: Fn(&Path) -> bool,
{
    if path.is_dir() {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();

            if predicate(&path) {
                results.push(path.clone());
            }

            if path.is_dir() {
                find_files_recursive(&path, predicate, results)?;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_file_type_detection() {
        let tmp = tempdir().unwrap();

        // Create file
        let file_path = tmp.path().join("test.txt");
        fs::write(&file_path, "content").unwrap();

        let info = FileInfo::from_path(&file_path).unwrap();
        assert_eq!(info.file_type, FileType::RegularFile);

        // Create directory
        let dir_path = tmp.path().join("subdir");
        fs::create_dir(&dir_path).unwrap();

        let info = FileInfo::from_path(&dir_path).unwrap();
        assert_eq!(info.file_type, FileType::Directory);
    }

    #[test]
    fn test_list_directory() {
        let tmp = tempdir().unwrap();

        fs::write(tmp.path().join("a.txt"), "").unwrap();
        fs::write(tmp.path().join("b.txt"), "").unwrap();
        fs::create_dir(tmp.path().join("subdir")).unwrap();

        let entries = list_directory(tmp.path()).unwrap();
        assert_eq!(entries.len(), 3);
    }

    #[test]
    fn test_atomic_write() {
        let tmp = tempdir().unwrap();
        let path = tmp.path().join("atomic.txt");

        atomic_write(&path, b"test content").unwrap();

        assert!(path.exists());
        assert_eq!(fs::read_to_string(&path).unwrap(), "test content");
    }

    #[test]
    fn test_directory_size() {
        let tmp = tempdir().unwrap();

        fs::write(tmp.path().join("a.txt"), "12345").unwrap();
        fs::write(tmp.path().join("b.txt"), "123").unwrap();

        let size = directory_size(tmp.path()).unwrap();
        assert_eq!(size, 8);
    }
}
