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

/// What follows the accepted records in a journal file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tail {
    /// Nothing. The journal is clean.
    Clean,
    /// An incomplete record: the file ends before the record's length field,
    /// payload or checksum does. This is what an interrupted append leaves,
    /// and all it can leave if a crash keeps a prefix of what was written.
    Torn,
    /// A complete record whose checksum does not match its payload. An
    /// interrupted append cannot produce this; the file has been damaged.
    Damaged,
}

/// The result of decoding a journal file (model: `Decoded`).
#[derive(Debug, PartialEq, Eq)]
pub struct Decoded<'a> {
    /// The payloads of the records accepted, in order.
    pub records: Vec<&'a [u8]>,
    /// How many bytes those records occupy. The bytes from here to the end
    /// of the input were not accepted.
    pub accepted: usize,
    /// What the bytes that were not accepted are.
    ///
    /// The distinction has one blind spot. Damage to a length field that
    /// makes the record appear to run past the end of the file looks the
    /// same as an interrupted append, and is reported as [`Tail::Torn`].
    pub tail: Tail,
}

/// Classify the bytes after the last accepted record.
fn classify_tail(rest: &[u8]) -> Tail {
    if rest.is_empty() {
        return Tail::Clean;
    }
    let Some(header) = rest.get(..HEADER_LEN) else {
        return Tail::Torn;
    };
    // The slice is exactly HEADER_LEN bytes, so the conversion cannot fail.
    let len = header
        .try_into()
        .map(|bytes: [u8; HEADER_LEN]| u32::from_le_bytes(bytes) as usize)
        .unwrap_or(usize::MAX);
    let complete = HEADER_LEN
        .checked_add(len)
        .and_then(|end| end.checked_add(SUM_LEN))
        .is_some_and(|frame_end| frame_end <= rest.len());
    if complete {
        Tail::Damaged
    } else {
        Tail::Torn
    }
}

/// Decode as many records as the front of `bytes` holds (model: `decode`).
pub fn decode(bytes: &[u8]) -> Decoded<'_> {
    let mut records = Vec::new();
    let mut accepted = 0;
    while let Some((payload, used)) = step(&bytes[accepted..]) {
        records.push(payload);
        accepted += used;
    }
    let tail = classify_tail(&bytes[accepted..]);
    Decoded {
        records,
        accepted,
        tail,
    }
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

    /// Keep `bytes` that the journal did not accept, so that dropping them
    /// from the journal destroys nothing. Returns a description of where
    /// they were put.
    fn set_aside(&mut self, bytes: &[u8]) -> io::Result<String>;
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
    fn set_aside(&mut self, bytes: &[u8]) -> io::Result<String> {
        (**self).set_aside(bytes)
    }
}

/// [`Storage`] in one file on disk.
///
/// The file is created readable and writable by its owner only, is never
/// opened through a symlink, and must be a regular file owned by the
/// current user; group and other permission bits on an existing file are
/// removed before it is used.
///
/// # Single owner
///
/// One `FileStorage` must own its path. Nothing here stops a second one,
/// in this process or another, from using the same path, and if it does,
/// writes are lost: after one of them replaces the file, the other keeps
/// appending to the file that was replaced. Keeping a second owner out
/// (an exclusive lock held for the life of the shell) is the caller's job
/// and is not done yet; see route plan section 14.3, step C3.
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
            // O_NONBLOCK: a FIFO in place of the file must fail or open at
            // once, not block before it can be checked. It has no effect on
            // reads and writes of a regular file.
            options
                .mode(0o600)
                .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK);
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
        // A second name for the file means writes here would land in
        // whatever that other name is, which may not be ours to change.
        if meta.nlink() != 1 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "{} has {} hard links; refusing to use it",
                    self.path.display(),
                    meta.nlink()
                ),
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
            let file = Self::options().append(true).create(true).open(&self.path)?;
            self.vet(&file)?;
            // The open may have created the file, now or on an earlier
            // attempt whose directory sync failed. Sync the directory every
            // time a handle is established, so no append is acknowledged
            // while the file's directory entry might not be durable.
            self.sync_dir()?;
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

    fn set_aside(&mut self, bytes: &[u8]) -> io::Result<String> {
        let mut name = self.path.clone().into_os_string();
        name.push(format!(".rejected.{:016x}", rand_suffix()));
        let aside = PathBuf::from(name);
        let mut file = Self::options().write(true).create_new(true).open(&aside)?;
        file.write_all(bytes)?;
        file.sync_all()?;
        self.sync_dir()?;
        Ok(aside.display().to_string())
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
    state: std::sync::Arc<std::sync::Mutex<SimState>>,
}

#[derive(Debug, Default)]
struct SimState {
    exists: bool,
    durable: Vec<u8>,
    pending: Vec<u8>,
    /// One entry per storage call that changed something: the state after
    /// it.
    trace: Vec<SimPoint>,
    /// Byte runs handed to `set_aside`.
    aside: Vec<Vec<u8>>,
    /// Fail the next calls of these kinds (to test error handling).
    fail_append: bool,
    /// Fail appends after writing this many bytes of them.
    fail_append_after: Option<usize>,
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
    fn lock(&self) -> std::sync::MutexGuard<'_, SimState> {
        // A panic while the lock is held cannot leave the plain data in an
        // unusable state, so a poisoned lock is still safe to read.
        self.state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// Empty storage: nothing has been stored yet.
    pub fn new() -> Self {
        Self::default()
    }

    /// Storage whose durable contents are `bytes`, as after a restart.
    pub fn with_contents(bytes: Vec<u8>) -> Self {
        let storage = Self::default();
        {
            let mut state = storage.lock();
            state.exists = true;
            state.durable = bytes;
        }
        storage
    }

    /// The current state of the simulated file.
    pub fn point(&self) -> SimPoint {
        let state = self.lock();
        SimPoint {
            durable: state.durable.clone(),
            pending: state.pending.clone(),
        }
    }

    /// The state after each storage call so far that changed something.
    pub fn trace(&self) -> Vec<SimPoint> {
        self.lock().trace.clone()
    }

    /// Every content a crash now could leave.
    pub fn crash_images(&self) -> Vec<Vec<u8>> {
        self.point().crash_images()
    }

    /// Byte runs set aside so far.
    pub fn set_aside_bytes(&self) -> Vec<Vec<u8>> {
        self.lock().aside.clone()
    }

    /// Make appends fail until turned off.
    pub fn fail_append(&self, fail: bool) {
        self.lock().fail_append = fail;
    }

    /// Make appends fail after writing their first `bytes` bytes, as a real
    /// write can; `None` turns it off.
    pub fn fail_append_after(&self, bytes: Option<usize>) {
        self.lock().fail_append_after = bytes;
    }

    /// Make syncs fail until turned off.
    pub fn fail_sync(&self, fail: bool) {
        self.lock().fail_sync = fail;
    }

    /// Make replacements fail until turned off.
    pub fn fail_replace(&self, fail: bool) {
        self.lock().fail_replace = fail;
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
        let state = self.lock();
        if !state.exists {
            return Ok(None);
        }
        let mut bytes = state.durable.clone();
        bytes.extend_from_slice(&state.pending);
        Ok(Some(bytes))
    }

    fn append(&mut self, bytes: &[u8]) -> io::Result<()> {
        let mut state = self.lock();
        if state.fail_append {
            return Err(injected("append"));
        }
        if let Some(limit) = state.fail_append_after {
            state.exists = true;
            let written = limit.min(bytes.len());
            state.pending.extend_from_slice(&bytes[..written]);
            state.record();
            return Err(injected("partial append"));
        }
        state.exists = true;
        state.pending.extend_from_slice(bytes);
        state.record();
        Ok(())
    }

    fn sync(&mut self) -> io::Result<()> {
        let mut state = self.lock();
        if state.fail_sync {
            return Err(injected("sync"));
        }
        let pending = std::mem::take(&mut state.pending);
        state.durable.extend_from_slice(&pending);
        state.record();
        Ok(())
    }

    fn replace(&mut self, bytes: &[u8]) -> io::Result<()> {
        let mut state = self.lock();
        if state.fail_replace {
            return Err(injected("replace"));
        }
        state.exists = true;
        state.durable = bytes.to_vec();
        state.pending.clear();
        state.record();
        Ok(())
    }

    fn set_aside(&mut self, bytes: &[u8]) -> io::Result<String> {
        self.lock().aside.push(bytes.to_vec());
        Ok("memory".to_string())
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
        assert_eq!(decoded.tail, Tail::Clean);
    }

    /// A cut anywhere inside a record is an interrupted append; a changed
    /// byte in a whole record's payload or checksum is damage.
    #[test]
    fn a_cut_record_is_torn_and_a_changed_record_is_damaged() {
        let first = frame(b"first").unwrap();
        let bytes = frames(&[b"first", b"second", b"third"]);

        // Every cut that is not on a record boundary.
        let boundaries = [
            0,
            first.len(),
            first.len() + frame(b"second").unwrap().len(),
        ];
        for cut in 0..bytes.len() {
            let expected = if boundaries.contains(&cut) {
                Tail::Clean
            } else {
                Tail::Torn
            };
            assert_eq!(decode(&bytes[..cut]).tail, expected, "cut at {cut}");
        }

        // A flipped bit in the second record's payload or checksum, with the
        // third record still after it.
        for i in first.len() + HEADER_LEN..first.len() + HEADER_LEN + 6 + SUM_LEN {
            let mut damaged = bytes.clone();
            damaged[i] ^= 0x01;
            let decoded = decode(&damaged);
            assert_eq!(decoded.records, [b"first"], "byte {i}");
            assert_eq!(decoded.tail, Tail::Damaged, "byte {i}");
        }
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

    #[test]
    fn sim_storage_can_fail_an_append_part_way() {
        let mut storage = SimStorage::new();
        storage.fail_append_after(Some(2));
        assert!(storage.append(b"abcd").is_err());
        assert_eq!(storage.point().pending, b"ab");
        storage.fail_append_after(None);
        storage.append(b"cd").unwrap();
        assert_eq!(storage.point().pending, b"abcd");
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

        /// A FIFO with no peer blocks a plain `open`. The storage must
        /// refuse it without waiting.
        #[test]
        fn a_fifo_in_place_of_the_file_is_refused_without_blocking() {
            let (dir, storage) = storage();
            nix::unistd::mkfifo(storage.path(), nix::sys::stat::Mode::S_IRWXU).unwrap();

            let (done, finished) = std::sync::mpsc::channel();
            std::thread::spawn(move || {
                let mut storage = storage;
                let outcome = (storage.read().is_err(), storage.append(b"x").is_err());
                let _ = done.send(outcome);
                drop(dir);
            });
            let outcome = finished
                .recv_timeout(std::time::Duration::from_secs(10))
                .expect("storage calls on a FIFO must not block");
            assert_eq!(outcome, (true, true));
        }

        #[test]
        fn a_file_with_a_second_hard_link_is_refused_and_left_alone() {
            let (dir, mut storage) = storage();
            let other = dir.path().join("someone-elses");
            fs::write(&other, b"theirs").unwrap();
            fs::set_permissions(&other, fs::Permissions::from_mode(0o644)).unwrap();
            fs::hard_link(&other, storage.path()).unwrap();

            assert!(storage.append(b"x").is_err());
            assert!(storage.read().is_err());
            assert_eq!(fs::read(&other).unwrap(), b"theirs");
            assert_eq!(mode(&other), 0o644, "its permissions are not changed");
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
