// SPDX-License-Identifier: MPL-2.0
//! Journal storage: record framing and the storage interface.
//!
//! The shell's persisted state is one append-only file of records. This
//! module is the byte level of it: how a record is framed, how a file is
//! decoded, and the small interface through which bytes reach the disk.
//!
//! It follows the Agda model in `proofs/agda/JournalFraming.agda` and
//! `proofs/agda/JournalModel.agda`. The model is not machine-linked to this
//! code; the names are kept the same so the two can be read side by side,
//! and [`SimStorage`] implements the model's file and crash semantics so the
//! crash tests exercise the same assumptions the proofs make.
//!
//! # Record format
//!
//! ```text
//! | length: u32, little-endian | payload: `length` bytes | SHA-256 of payload: 32 bytes |
//! ```
//!
//! * A record cut short at any point is rejected by its length alone
//!   (model: `step-torn`).
//! * Whatever [`decode`] accepts is, byte for byte, a run of well-formed
//!   records at the front of the input (model: `decode-sound`).
//! * The checksum makes it unlikely that bytes never written as a record are
//!   accepted as one. It is an integrity check against accidental damage,
//!   not an authentication code: anyone who can write the file can write a
//!   valid record.
//!
//! # Durability
//!
//! [`Storage::append`] is not durable until [`Storage::sync`] returns.
//! [`Storage::replace`] is all-or-nothing and durable when it returns. The
//! assumption about a crash, shared with the model: synced bytes survive,
//! and bytes appended since the last sync survive as a prefix.

use sha2::{Digest, Sha256};
use std::fs;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

/// Width of the length field.
pub const HEADER_LEN: usize = 4;
/// Width of the checksum.
pub const SUM_LEN: usize = 32;
/// Longest payload the length field can carry (model: `Frameable`).
pub const MAX_PAYLOAD: usize = u32::MAX as usize;

/// A payload too long for the length field.
#[derive(Debug, thiserror::Error)]
#[error("journal record of {0} bytes exceeds the {MAX_PAYLOAD}-byte limit")]
pub struct PayloadTooLong(pub usize);

fn checksum(payload: &[u8]) -> [u8; SUM_LEN] {
    Sha256::digest(payload).into()
}

/// Append the frame for `payload` to `out` (model: `frame`).
pub fn write_frame(out: &mut Vec<u8>, payload: &[u8]) -> Result<(), PayloadTooLong> {
    let len = u32::try_from(payload.len()).map_err(|_| PayloadTooLong(payload.len()))?;
    out.reserve(HEADER_LEN + payload.len() + SUM_LEN);
    out.extend_from_slice(&len.to_le_bytes());
    out.extend_from_slice(payload);
    out.extend_from_slice(&checksum(payload));
    Ok(())
}

/// The frame for `payload`.
pub fn frame(payload: &[u8]) -> Result<Vec<u8>, PayloadTooLong> {
    let mut out = Vec::new();
    write_frame(&mut out, payload)?;
    Ok(out)
}

/// Read one record from the front of `bytes` (model: `step`). Returns the
/// payload and the number of bytes the record occupies, or `None` if `bytes`
/// does not start with a well-formed record.
fn step(bytes: &[u8]) -> Option<(&[u8], usize)> {
    let header: [u8; HEADER_LEN] = bytes.get(..HEADER_LEN)?.try_into().ok()?;
    let len = u32::from_le_bytes(header) as usize;
    let payload_end = HEADER_LEN.checked_add(len)?;
    let frame_end = payload_end.checked_add(SUM_LEN)?;
    let payload = bytes.get(HEADER_LEN..payload_end)?;
    let sum = bytes.get(payload_end..frame_end)?;
    (sum == checksum(payload)).then_some((payload, frame_end))
}

/// The result of decoding a journal file (model: `Decoded`).
#[derive(Debug, PartialEq, Eq)]
pub struct Decoded<'a> {
    /// The payloads of the records accepted, in order.
    pub records: Vec<&'a [u8]>,
    /// How many bytes those records occupy. The bytes from here to the end
    /// of the input were not accepted; the journal is clean exactly when
    /// this equals the input length.
    pub accepted: usize,
}

/// Decode as many records as the front of `bytes` holds (model: `decode`).
pub fn decode(bytes: &[u8]) -> Decoded<'_> {
    let mut records = Vec::new();
    let mut accepted = 0;
    while let Some((payload, used)) = step(&bytes[accepted..]) {
        records.push(payload);
        accepted += used;
    }
    Decoded { records, accepted }
}

/// Where the journal's bytes live (model: `File`, with `append`, `sync` and
/// atomic replacement).
pub trait Storage {
    /// The whole contents, or `None` if nothing has been stored yet.
    fn read(&mut self) -> io::Result<Option<Vec<u8>>>;

    /// Add `bytes` at the end. Not durable until [`Storage::sync`].
    fn append(&mut self, bytes: &[u8]) -> io::Result<()>;

    /// Make everything appended so far durable.
    fn sync(&mut self) -> io::Result<()>;

    /// Replace the whole contents with `bytes`. All-or-nothing, and durable
    /// when it returns: after a crash the contents are the old ones (as any
    /// crash of them) or exactly `bytes`.
    fn replace(&mut self, bytes: &[u8]) -> io::Result<()>;
}

impl<S: Storage + ?Sized> Storage for Box<S> {
    fn read(&mut self) -> io::Result<Option<Vec<u8>>> {
        (**self).read()
    }
    fn append(&mut self, bytes: &[u8]) -> io::Result<()> {
        (**self).append(bytes)
    }
    fn sync(&mut self) -> io::Result<()> {
        (**self).sync()
    }
    fn replace(&mut self, bytes: &[u8]) -> io::Result<()> {
        (**self).replace(bytes)
    }
}

/// [`Storage`] in one file on disk.
///
/// The file is created readable and writable by its owner only, is never
/// opened through a symlink, and must be a regular file owned by the
/// current user; group and other permission bits on an existing file are
/// removed before it is used.
#[derive(Debug)]
pub struct FileStorage {
    path: PathBuf,
    file: Option<fs::File>,
}

impl FileStorage {
    /// Storage at `path`. Nothing is opened or created until first use.
    pub fn new(path: impl Into<PathBuf>) -> Self {
        Self {
            path: path.into(),
            file: None,
        }
    }

    /// The file this storage reads and writes.
    pub fn path(&self) -> &Path {
        &self.path
    }

    fn options() -> fs::OpenOptions {
        let mut options = fs::OpenOptions::new();
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            options
                .mode(0o600)
                .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC);
        }
        options
    }

    /// Check, through the open descriptor, that `file` is ours to use, and
    /// remove group and other access.
    #[cfg(unix)]
    fn vet(&self, file: &fs::File) -> io::Result<()> {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        let meta = file.metadata()?;
        if !meta.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("{} is not a regular file", self.path.display()),
            ));
        }
        let euid = nix::unistd::geteuid().as_raw();
        if meta.uid() != euid {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                format!("{} is owned by another user", self.path.display()),
            ));
        }
        if meta.mode() & 0o077 != 0 {
            file.set_permissions(fs::Permissions::from_mode(0o600))?;
        }
        Ok(())
    }

    #[cfg(not(unix))]
    fn vet(&self, _file: &fs::File) -> io::Result<()> {
        Ok(())
    }

    fn parent(&self) -> &Path {
        match self.path.parent() {
            Some(dir) if !dir.as_os_str().is_empty() => dir,
            _ => Path::new("."),
        }
    }

    /// Make a created or renamed directory entry durable.
    fn sync_dir(&self) -> io::Result<()> {
        #[cfg(unix)]
        {
            fs::File::open(self.parent())?.sync_all()?;
        }
        Ok(())
    }

    /// The open append handle, creating the file on first use.
    fn handle(&mut self) -> io::Result<&mut fs::File> {
        if self.file.is_none() {
            let existed = self.path.symlink_metadata().is_ok();
            let file = Self::options().append(true).create(true).open(&self.path)?;
            self.vet(&file)?;
            if !existed {
                self.sync_dir()?;
            }
            self.file = Some(file);
        }
        // The branch above filled `self.file`.
        self.file
            .as_mut()
            .ok_or_else(|| io::Error::other("journal file handle missing"))
    }
}

impl Storage for FileStorage {
    fn read(&mut self) -> io::Result<Option<Vec<u8>>> {
        let mut file = match Self::options().read(true).open(&self.path) {
            Ok(file) => file,
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e),
        };
        self.vet(&file)?;
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes)?;
        Ok(Some(bytes))
    }

    fn append(&mut self, bytes: &[u8]) -> io::Result<()> {
        self.handle()?.write_all(bytes)
    }

    fn sync(&mut self) -> io::Result<()> {
        self.handle()?.sync_data()
    }

    fn replace(&mut self, bytes: &[u8]) -> io::Result<()> {
        let name = self
            .path
            .file_name()
            .ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidInput, "journal path has no file name")
            })?
            .to_string_lossy()
            .into_owned();
        let temp = self.parent().join(format!(
            "{name}.{}.{:016x}.tmp",
            std::process::id(),
            rand_suffix()
        ));
        let written = (|| {
            let mut file = Self::options().write(true).create_new(true).open(&temp)?;
            file.write_all(bytes)?;
            file.sync_all()?;
            fs::rename(&temp, &self.path)
        })();
        if let Err(e) = written {
            // Best effort: a leftover temporary file is ignored by `read`.
            let _ = fs::remove_file(&temp);
            return Err(e);
        }
        // The old handle points at the replaced file.
        self.file = None;
        self.sync_dir()
    }
}

/// A value that differs between calls, for temporary file names. Uniqueness
/// is enforced by `create_new`; this only makes collisions unlikely.
fn rand_suffix() -> u64 {
    use std::collections::hash_map::RandomState;
    use std::hash::{BuildHasher, Hasher};
    RandomState::new().build_hasher().finish()
}

/// [`Storage`] in memory, with the model's crash semantics.
///
/// It keeps the bytes that would be on disk (`durable`) apart from the bytes
/// appended since the last sync (`pending`), exactly as the model's `File`
/// does. [`SimStorage::crash_images`] lists every content a crash could
/// leave (model: `Crash`). Cloning shares the state, so a test can keep a
/// handle to storage it has given away.
#[derive(Debug, Clone, Default)]
pub struct SimStorage {
    state: std::rc::Rc<std::cell::RefCell<SimState>>,
}

#[derive(Debug, Default)]
struct SimState {
    exists: bool,
    durable: Vec<u8>,
    pending: Vec<u8>,
    /// One entry per storage call that changed something: the state after
    /// it.
    trace: Vec<SimPoint>,
    /// Fail the next calls of these kinds (to test error handling).
    fail_append: bool,
    fail_sync: bool,
    fail_replace: bool,
}

/// The simulated file after one storage call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimPoint {
    /// Bytes that would survive any crash.
    pub durable: Vec<u8>,
    /// Bytes appended and not yet synced.
    pub pending: Vec<u8>,
}

impl SimPoint {
    /// Every content a crash at this point could leave: the durable bytes
    /// followed by each prefix of the pending bytes.
    pub fn crash_images(&self) -> Vec<Vec<u8>> {
        (0..=self.pending.len())
            .map(|cut| {
                let mut image = self.durable.clone();
                image.extend_from_slice(&self.pending[..cut]);
                image
            })
            .collect()
    }
}

impl SimStorage {
    /// Empty storage: nothing has been stored yet.
    pub fn new() -> Self {
        Self::default()
    }

    /// Storage whose durable contents are `bytes`, as after a restart.
    pub fn with_contents(bytes: Vec<u8>) -> Self {
        let storage = Self::default();
        {
            let mut state = storage.state.borrow_mut();
            state.exists = true;
            state.durable = bytes;
        }
        storage
    }

    /// The current state of the simulated file.
    pub fn point(&self) -> SimPoint {
        let state = self.state.borrow();
        SimPoint {
            durable: state.durable.clone(),
            pending: state.pending.clone(),
        }
    }

    /// The state after each storage call so far that changed something.
    pub fn trace(&self) -> Vec<SimPoint> {
        self.state.borrow().trace.clone()
    }

    /// Every content a crash now could leave.
    pub fn crash_images(&self) -> Vec<Vec<u8>> {
        self.point().crash_images()
    }

    /// Make appends fail until turned off.
    pub fn fail_append(&self, fail: bool) {
        self.state.borrow_mut().fail_append = fail;
    }

    /// Make syncs fail until turned off.
    pub fn fail_sync(&self, fail: bool) {
        self.state.borrow_mut().fail_sync = fail;
    }

    /// Make replacements fail until turned off.
    pub fn fail_replace(&self, fail: bool) {
        self.state.borrow_mut().fail_replace = fail;
    }
}

impl SimState {
    fn record(&mut self) {
        self.trace.push(SimPoint {
            durable: self.durable.clone(),
            pending: self.pending.clone(),
        });
    }
}

fn injected(what: &str) -> io::Error {
    io::Error::other(format!("simulated {what} failure"))
}

impl Storage for SimStorage {
    fn read(&mut self) -> io::Result<Option<Vec<u8>>> {
        let state = self.state.borrow();
        if !state.exists {
            return Ok(None);
        }
        let mut bytes = state.durable.clone();
        bytes.extend_from_slice(&state.pending);
        Ok(Some(bytes))
    }

    fn append(&mut self, bytes: &[u8]) -> io::Result<()> {
        let mut state = self.state.borrow_mut();
        if state.fail_append {
            return Err(injected("append"));
        }
        state.exists = true;
        state.pending.extend_from_slice(bytes);
        state.record();
        Ok(())
    }

    fn sync(&mut self) -> io::Result<()> {
        let mut state = self.state.borrow_mut();
        if state.fail_sync {
            return Err(injected("sync"));
        }
        let pending = std::mem::take(&mut state.pending);
        state.durable.extend_from_slice(&pending);
        state.record();
        Ok(())
    }

    fn replace(&mut self, bytes: &[u8]) -> io::Result<()> {
        let mut state = self.state.borrow_mut();
        if state.fail_replace {
            return Err(injected("replace"));
        }
        state.exists = true;
        state.durable = bytes.to_vec();
        state.pending.clear();
        state.record();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frames(payloads: &[&[u8]]) -> Vec<u8> {
        let mut out = Vec::new();
        for payload in payloads {
            write_frame(&mut out, payload).unwrap();
        }
        out
    }

    #[test]
    fn frame_layout_is_length_payload_checksum() {
        let bytes = frame(b"ab").unwrap();
        assert_eq!(bytes.len(), HEADER_LEN + 2 + SUM_LEN);
        assert_eq!(&bytes[..HEADER_LEN], &2u32.to_le_bytes());
        assert_eq!(&bytes[HEADER_LEN..HEADER_LEN + 2], b"ab");
        assert_eq!(&bytes[HEADER_LEN + 2..], &checksum(b"ab"));
    }

    /// Model: `decode-clean`.
    #[test]
    fn frames_decode_to_their_payloads() {
        let payloads: [&[u8]; 4] = [b"one", b"", b"three", &[0u8; 300]];
        let bytes = frames(&payloads);
        let decoded = decode(&bytes);
        assert_eq!(decoded.records, payloads);
        assert_eq!(decoded.accepted, bytes.len());
    }

    /// Model: `decode-crash` with nothing synced. Every prefix of a run of
    /// frames decodes to the whole records it contains, and nothing else.
    #[test]
    fn every_prefix_decodes_to_whole_records_only() {
        let payloads: [&[u8]; 3] = [b"alpha", b"", b"gamma-gamma"];
        let bytes = frames(&payloads);
        let mut boundaries = vec![0];
        for payload in payloads {
            boundaries.push(boundaries.last().unwrap() + HEADER_LEN + payload.len() + SUM_LEN);
        }
        for cut in 0..=bytes.len() {
            let whole = boundaries.iter().filter(|&&b| b != 0 && b <= cut).count();
            let decoded = decode(&bytes[..cut]);
            assert_eq!(decoded.records, &payloads[..whole], "cut at {cut}");
            assert_eq!(decoded.accepted, boundaries[whole], "cut at {cut}");
        }
    }

    /// Model: `decode-sound`. For arbitrary bytes, the accepted records
    /// re-encode to exactly the accepted front of the input.
    #[test]
    fn accepted_records_reencode_to_the_accepted_bytes() {
        let good = frames(&[b"x", b"yy"]);
        let mut inputs: Vec<Vec<u8>> = vec![
            Vec::new(),
            vec![0; 3],
            vec![0xff; 64],
            good.clone(),
            [good.as_slice(), &[1, 2, 3]].concat(),
        ];
        // A flipped bit anywhere in a good journal.
        for i in 0..good.len() {
            let mut damaged = good.clone();
            damaged[i] ^= 0x01;
            inputs.push(damaged);
        }
        for input in inputs {
            let decoded = decode(&input);
            assert_eq!(frames(&decoded.records), &input[..decoded.accepted]);
        }
    }

    /// A changed byte in a record rejects that record and everything after
    /// it; earlier records are kept.
    #[test]
    fn damage_rejects_the_record_and_what_follows() {
        let first = frame(b"first").unwrap();
        let bytes = frames(&[b"first", b"second", b"third"]);
        for i in first.len()..first.len() + HEADER_LEN + 6 + SUM_LEN {
            let mut damaged = bytes.clone();
            damaged[i] ^= 0x80;
            let decoded = decode(&damaged);
            assert_eq!(decoded.records, [b"first"], "byte {i}");
            assert_eq!(decoded.accepted, first.len(), "byte {i}");
        }
    }

    #[test]
    fn a_length_field_past_the_end_is_rejected_without_overflow() {
        let mut bytes = u32::MAX.to_le_bytes().to_vec();
        bytes.extend_from_slice(&[7; 40]);
        assert_eq!(decode(&bytes).accepted, 0);
    }

    #[test]
    fn sim_storage_keeps_pending_apart_until_sync() {
        let mut storage = SimStorage::new();
        assert_eq!(storage.read().unwrap(), None);
        storage.append(b"ab").unwrap();
        assert_eq!(storage.read().unwrap().unwrap(), b"ab");
        assert_eq!(
            storage.crash_images(),
            vec![b"".to_vec(), b"a".to_vec(), b"ab".to_vec()]
        );
        storage.sync().unwrap();
        assert_eq!(storage.crash_images(), vec![b"ab".to_vec()]);
        storage.append(b"c").unwrap();
        storage.replace(b"xyz").unwrap();
        assert_eq!(storage.crash_images(), vec![b"xyz".to_vec()]);
        assert_eq!(storage.trace().len(), 4);
    }

    #[cfg(unix)]
    mod file {
        use super::super::*;
        use std::os::unix::fs::PermissionsExt;

        fn storage() -> (tempfile::TempDir, FileStorage) {
            let dir = tempfile::tempdir().unwrap();
            let storage = FileStorage::new(dir.path().join("journal"));
            (dir, storage)
        }

        fn mode(path: &Path) -> u32 {
            fs::metadata(path).unwrap().permissions().mode() & 0o777
        }

        #[test]
        fn read_of_a_missing_file_is_none() {
            let (_dir, mut storage) = storage();
            assert_eq!(storage.read().unwrap(), None);
        }

        #[test]
        fn append_sync_read_round_trip() {
            let (_dir, mut storage) = storage();
            storage.append(b"one").unwrap();
            storage.append(b"two").unwrap();
            storage.sync().unwrap();
            assert_eq!(storage.read().unwrap().unwrap(), b"onetwo");
            assert_eq!(mode(storage.path()), 0o600);
        }

        #[test]
        fn replace_swaps_contents_and_later_appends_follow_it() {
            let (dir, mut storage) = storage();
            storage.append(b"old").unwrap();
            storage.replace(b"new").unwrap();
            storage.append(b"+more").unwrap();
            storage.sync().unwrap();
            assert_eq!(storage.read().unwrap().unwrap(), b"new+more");
            assert_eq!(mode(storage.path()), 0o600);
            let names: Vec<_> = fs::read_dir(dir.path())
                .unwrap()
                .map(|e| e.unwrap().file_name())
                .collect();
            assert_eq!(names, ["journal"], "no temporary file is left behind");
        }

        #[test]
        fn an_existing_file_with_loose_permissions_is_tightened() {
            let (_dir, mut storage) = storage();
            fs::write(storage.path(), b"").unwrap();
            fs::set_permissions(storage.path(), fs::Permissions::from_mode(0o644)).unwrap();
            storage.append(b"secret").unwrap();
            assert_eq!(mode(storage.path()), 0o600);
        }

        #[test]
        fn a_symlink_is_refused_and_its_target_untouched() {
            let (dir, mut storage) = storage();
            let target = dir.path().join("target");
            fs::write(&target, b"keep me").unwrap();
            std::os::unix::fs::symlink(&target, storage.path()).unwrap();

            assert!(storage.append(b"x").is_err());
            assert!(storage.read().is_err());
            assert_eq!(fs::read(&target).unwrap(), b"keep me");

            // Replacement renames over the link itself, never through it.
            storage.replace(b"fresh").unwrap();
            assert_eq!(fs::read(&target).unwrap(), b"keep me");
            assert_eq!(storage.read().unwrap().unwrap(), b"fresh");
        }

        #[test]
        fn a_directory_in_place_of_the_file_is_refused() {
            let (_dir, mut storage) = storage();
            fs::create_dir(storage.path()).unwrap();
            assert!(storage.append(b"x").is_err());
            assert!(storage.read().is_err());
        }
    }
}
