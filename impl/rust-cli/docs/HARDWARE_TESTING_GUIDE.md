# Hardware Secure Erase Testing Guide

## CRITICAL SAFETY WARNINGS

🚨 **THESE OPERATIONS PERMANENTLY DESTROY ALL DATA ON THE TARGET DEVICE**

### Before You Begin

- ✅ Use a **SPARE/SACRIFICIAL** drive only
- ✅ Verify you have **NO IMPORTANT DATA** on the test drive
- ✅ **TRIPLE-CHECK** the device path before testing
- ❌ **NEVER** test on your system drive
- ❌ **NEVER** test on drives with data you care about
- ❌ **NEVER** test on production systems

## Step 1: Identify Safe Test Hardware

### Find Your System Drive (DO NOT USE THIS)

```bash
# Identify your system drive
df / | tail -1 | awk '{print $1}'

# Example output: /dev/nvme1n1p3 (system is on nvme1n1)
```

**WRITE DOWN YOUR SYSTEM DRIVE AND NEVER USE IT FOR TESTING**

### Find a Safe Test Drive

You need a spare drive that:
- Is NOT your system drive
- Contains NO important data
- Is either:
  - External USB drive
  - Secondary internal drive
  - Old SSD/HDD you're willing to destroy

```bash
# List all block devices
lsblk -o NAME,SIZE,TYPE,MOUNTPOINT,MODEL

# Example output:
# NAME        SIZE TYPE MOUNTPOINT          MODEL
# nvme0n1   476.9G disk                     SK hynix BC511 NVMe  <- Eclipse drive (safe to test)
# nvme1n1   232.9G disk                     Samsung SSD 960 EVO  <- SYSTEM DRIVE (DO NOT TEST)
# sda       500G   disk                     WD Blue USB          <- Safe to test
```

### Verify Drive is Unmounted

```bash
# Check if the test drive has mounted partitions
lsblk /dev/sda  # Replace with your test device

# If mounted, unmount first:
sudo umount /dev/sda1  # Replace with actual partition
```

## Step 2: Non-Destructive Tests

### Test 1: Drive Type Detection

```bash
# Start the daemon
cd /var/mnt/eclipse/repos/valence-shell/impl/elixir
iex -S mix

# In IEx:
{:ok, drive_type} = VSH.SecureErase.detect_drive_type("/dev/sda")
# Expected: {:ok, :hdd} or {:ok, :sata_ssd} or {:ok, :nvme_ssd}
```

### Test 2: Check Secure Erase Support

**For SATA SSDs:**
```elixir
# In IEx:
{:ok, result} = VSH.SecureErase.check_ata_support("/dev/sda")
# Expected: {:ok, "supported"} or {:ok, "not_supported"}
```

**For NVMe SSDs:**
```elixir
# In IEx:
{:ok, result} = VSH.SecureErase.check_nvme_sanitize_support("/dev/nvme0n1")
# Expected: {:ok, "supported"} or {:ok, "not_supported"}
```

### Test 3: Command Line Detection (Rust CLI)

```bash
# Build the Rust CLI first
cd /var/mnt/eclipse/repos/valence-shell/impl/rust-cli
cargo build --release

# Test drive detection (read-only)
sudo lsblk /dev/sda
sudo hdparm -I /dev/sda | grep -i security  # For SATA
sudo nvme id-ctrl /dev/nvme0n1 | grep -i sanitize  # For NVMe
```

## Step 3: Destructive Tests (POINT OF NO RETURN)

⚠️ **FINAL WARNING**: These tests will **PERMANENTLY ERASE** the test drive!

### Verify Test Device One More Time

```bash
# Triple-check this is NOT your system drive
SYSTEM_DRIVE=$(df / | tail -1 | awk '{print $1}' | sed 's/[0-9]*$//')
TEST_DRIVE="/dev/sda"  # YOUR TEST DEVICE

if [[ "$TEST_DRIVE" == "$SYSTEM_DRIVE"* ]]; then
    echo "❌ ABORT: This is your system drive!"
    exit 1
else
    echo "✓ Safe to proceed - not system drive"
fi
```

### Test 4A: ATA Secure Erase (SATA SSD)

```bash
# In IEx (daemon must be running):
VSH.SecureErase.ata_secure_erase("/dev/sda", enhanced: true)

# Expected output:
# 🚨 CRITICAL WARNING - DEVICE-LEVEL SECURE ERASE 🚨
#
# THIS WILL ERASE THE ENTIRE DEVICE!
# ALL DATA ON THE DEVICE WILL BE PERMANENTLY DESTROYED!
#
# Device:   /dev/sda
# Type:     sata_ssd
# Size:     500GB
# Method:   ATA Secure Erase (Enhanced) (NIST SP 800-88 Purge)
#
# SAFETY CHECKS:
#   ✓ Not system drive
#   ✓ Device unmounted
#
# FINAL CONFIRMATION REQUIRED
# Type the device name exactly to confirm: /dev/sda
#
# ⚠️  LAST CHANCE TO ABORT!
# PERMANENTLY ERASE ALL DATA? [y/N]: y

# If successful:
# {:ok, "erase_complete"}
```

### Test 4B: NVMe Format (NVMe SSD - Fast)

```bash
# In IEx:
VSH.SecureErase.nvme_format_crypto("/dev/nvme0n1")

# Expected: Similar confirmation flow, then cryptographic erase (seconds)
```

### Test 4C: NVMe Sanitize (NVMe SSD - Slow but Thorough)

```bash
# In IEx:
VSH.SecureErase.nvme_sanitize("/dev/nvme0n1", block_erase: true)

# Expected: Similar confirmation flow, then block erase (hours)
```

### Test 5: JSON-RPC Integration (via Rust CLI)

```bash
# Terminal 1: Start daemon
cd /var/mnt/eclipse/repos/valence-shell/impl/elixir
iex -S mix

# Terminal 2: Test JSON-RPC call
cd /var/mnt/eclipse/repos/valence-shell/impl/rust-cli
cargo build --release

# Add hardware_erase command to Rust CLI (see below)
./target/release/vsh
vsh> hardware_erase /dev/sda
```

## Step 4: Verification

After a successful erase, verify:

```bash
# 1. Check device is accessible
sudo fdisk -l /dev/sda

# 2. Verify data is gone (try to mount - should fail)
sudo mount /dev/sda1 /mnt
# Expected: mount: /mnt: special device /dev/sda1 does not exist

# 3. Check SMART data (if available)
sudo smartctl -a /dev/sda
```

## Testing Checklist

- [ ] Identified system drive and confirmed it's NOT the test device
- [ ] Selected spare/sacrificial test drive
- [ ] Verified test drive is unmounted
- [ ] Ran non-destructive tests (detection, capability check)
- [ ] Verified test drive one final time
- [ ] Successfully completed destructive test
- [ ] Verified data was erased
- [ ] Documented any issues or unexpected behavior

## Recommended Test Devices

| Type | Good For Testing | Notes |
|------|------------------|-------|
| Old USB flash drive | Basic testing | Fast, cheap, easily replaced |
| Spare SATA SSD | ATA Secure Erase | Need SATA connection |
| Spare NVMe SSD | NVMe Format/Sanitize | Fastest testing |
| Old external HDD | Fallback testing | Not for SSD-specific tests |

## Safety Features to Verify

During testing, confirm these safety features work:

1. **System drive protection** - Try to erase system drive (should ABORT)
2. **Mount detection** - Try with mounted device (should warn and offer unmount)
3. **Typed challenge** - Type wrong device name (should CANCEL)
4. **Final confirmation** - Answer 'n' to final prompt (should CANCEL)
5. **Capability detection** - Try unsupported method (should error gracefully)

## Troubleshooting

### "Permission denied"
```bash
# Run with sudo
sudo iex -S mix
```

### "Device is frozen" (ATA Secure Erase)
```bash
# Suspend/resume to unfreeze
sudo systemctl suspend
# Press power button to resume
```

### "hdparm not found"
```bash
# Install hdparm
sudo dnf install hdparm  # Fedora
sudo apt install hdparm  # Ubuntu/Debian
```

### "nvme command not found"
```bash
# Install nvme-cli
sudo dnf install nvme-cli  # Fedora
sudo apt install nvme-cli  # Ubuntu/Debian
```

## Example Test Session

```bash
# 1. Check system drive (DO NOT USE THIS)
$ df / | tail -1 | awk '{print $1}'
/dev/nvme1n1p3  # System is on nvme1n1 - AVOID THIS

# 2. List all drives
$ lsblk
NAME        SIZE TYPE MOUNTPOINT
nvme0n1   476.9G disk            # <- Safe to test (Eclipse drive, non-system)
nvme1n1   232.9G disk            # <- DO NOT TEST (system drive)
├─nvme1n1p1  1G part /boot
├─nvme1n1p2  2G part [SWAP]
└─nvme1n1p3 230G part /

# 3. Start daemon and test
$ cd /var/mnt/eclipse/repos/valence-shell/impl/elixir
$ iex -S mix

iex> {:ok, drive_type} = VSH.SecureErase.detect_drive_type("/dev/nvme0n1")
{:ok, :nvme_ssd}

iex> {:ok, result} = VSH.SecureErase.check_nvme_sanitize_support("/dev/nvme0n1")
{:ok, "supported"}

# 4. DESTRUCTIVE TEST (only if you're CERTAIN)
iex> VSH.SecureErase.nvme_format_crypto("/dev/nvme0n1")
# ... follow confirmation prompts ...
{:ok, "erase_complete"}
```

## Next Steps

Would you like me to:
1. Add a `hardware_erase` command to the Rust CLI for easier testing?
2. Create a test script that uses a loop device (safe, no real hardware needed)?
3. Add detailed logging to track what happens during erase operations?

**Current recommendation**: Start with the **Eclipse drive (/dev/nvme0n1)** if it doesn't have critical data, since you mentioned it's for repos/data storage. But verify no important repos are on it first!