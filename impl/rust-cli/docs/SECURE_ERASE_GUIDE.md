# Secure Erase User Guide

## NIST SP 800-88 Compliance

Valence Shell implements **NIST SP 800-88 Rev. 1** guidelines for media sanitization.

## Quick Reference

| Drive Type | Method | Time | Standard | Use Case |
|------------|--------|------|----------|----------|
| HDD | `clear` | Seconds | NIST Clear | GDPR, normal deletion |
| HDD | `purge` | Seconds | NIST Purge | High security |
| SSD (SATA) | `ata-secure-erase` | Minutes | NIST Purge | End-of-life, repurpose |
| SSD (NVMe) | `nvme-format` | Seconds | NIST Purge | Quick secure erase |
| SSD (NVMe) | `nvme-sanitize` | Hours | NIST Purge | Maximum security |
| Any | Physical destruction | N/A | NIST Destroy | Decommissioning |

## File-Level Deletion

### NIST Clear (Default - GDPR Compliant)
```bash
# Single pass overwrite with zeros
obliterate /path/to/file

# Or explicitly:
obliterate /path/to/file --method=clear
```

**What it does**:
- 1 pass of zeros over file data
- Sufficient for modern drives (post-2001)
- GDPR "right to erasure" compliant
- Defeats casual recovery

**When to use**:
- Normal secure file deletion
- GDPR compliance
- Privacy protection
- De-identification

### NIST Purge (High Security)
```bash
# Single pass random + verification
obliterate /path/to/file --method=purge --verify
```

**What it does**:
- 1 pass of cryptographically random data
- Verification pass to ensure overwrite
- Defeats laboratory recovery (NIST Purge)

**When to use**:
- Classified information
- Trade secrets
- High-value data
- Regulatory compliance (HIPAA, PCI-DSS)

### Recursive Deletion
```bash
# Secure delete entire directory tree
obliterate_tree /path/to/directory --method=clear
```

## Device-Level Secure Erase (SSDs)

⚠️ **WARNING**: These commands erase the **ENTIRE device**, not just individual files!

### Auto-Detect (Recommended)
```bash
# Automatically detects drive type and uses appropriate method
hardware_erase /dev/sda
```

### SATA SSD - ATA Secure Erase
```bash
# Uses ATA SECURITY ERASE UNIT command
hardware_erase /dev/sda --method=ata-secure-erase
```

**What it does**:
- Firmware command to erase all flash cells
- Bypasses wear leveling
- Resets device to factory state
- Time: 1-5 minutes typically

**Requirements**:
- SATA SSD with ATA Secure Erase support
- `hdparm` utility installed
- Root/sudo access

**Why necessary for SSDs**:
- Overwrite doesn't work (wear leveling redirects)
- Hidden reserved blocks not accessible
- Only firmware knows true physical locations

### NVMe SSD - Format with Crypto Erase
```bash
# Fast cryptographic erase
hardware_erase /dev/nvme0n1 --method=nvme-format
```

**What it does**:
- Destroys encryption key (instant)
- All data becomes unrecoverable garbage
- Time: Seconds

**Best for**:
- Quick secure erase
- Repurposing drives
- Encrypted SSDs

### NVMe SSD - Sanitize (Maximum Security)
```bash
# Complete block-level erase
hardware_erase /dev/nvme0n1 --method=nvme-sanitize
```

**What it does**:
- Physical block erase across entire device
- Overwrites all cells including over-provisioned space
- Time: Several hours

**Best for**:
- Maximum security requirements
- Classified data
- End-of-life disposal

## Detection and Verification

### Check Drive Type
```bash
# Identify if drive is HDD or SSD
vsh-info /dev/sda
```

### Check Secure Erase Support
```bash
# For SATA SSDs
hdparm -I /dev/sda | grep "supported: enhanced erase"

# For NVMe SSDs
nvme id-ctrl /dev/nvme0n1 | grep -i sanitize
```

## Common Scenarios

### Scenario 1: Delete Sensitive File (GDPR)
```bash
obliterate /home/user/tax-returns.pdf
# Method: NIST Clear (1 pass)
# Time: < 1 second
# Compliance: GDPR Article 17
```

### Scenario 2: Wipe Project Directory
```bash
obliterate_tree /home/user/confidential-project/
# Method: NIST Clear (recursive)
# Time: Seconds to minutes
# Compliance: GDPR, data minimization
```

### Scenario 3: Selling/Donating SSD
```bash
# SATA SSD:
hardware_erase /dev/sda --method=ata-secure-erase

# NVMe SSD:
hardware_erase /dev/nvme0n1 --method=nvme-format

# Compliance: NIST Purge
# Result: All personal data irrecoverable
```

### Scenario 4: Classified Data Disposal
```bash
# Step 1: File-level purge
obliterate /path/to/classified --method=purge --verify

# Step 2: Device-level sanitize
hardware_erase /dev/nvme0n1 --method=nvme-sanitize

# Step 3: Physical destruction (if required)
# [Physical shredding/degaussing]
```

## Limitations and Caveats

### SSDs
❌ **File-level overwrite DOES NOT work reliably**
- Wear leveling redirects writes
- Over-provisioned blocks not accessible
- Old data may remain in flash cells

✅ **Use hardware secure erase instead**
- ATA Secure Erase (SATA)
- NVMe Format/Sanitize (NVMe)

### Cloud/Network Storage
❌ **Local secure erase may not affect backups**
- Cloud sync may have copies
- Network shares may have snapshots
- Backup systems may retain versions

✅ **Also secure-delete from**:
- Cloud storage APIs
- Backup systems
- Snapshot storage
- Version control

### Encrypted Drives
✅ **Cryptographic erasure is fastest**
- Destroy encryption key
- All data becomes unrecoverable
- No need to overwrite

⚠️ **Ensure key destruction is complete**
- TPM-stored keys
- Key escrow systems
- Recovery keys

## Legal and Compliance

### GDPR (EU)
- **Article 17**: Right to erasure
- **Requirement**: Irreversible deletion
- **Method**: NIST Clear sufficient

### HIPAA (US Healthcare)
- **§164.310(d)(2)(i)**: Disposal standard
- **Requirement**: Unusable, unreadable, indecipherable
- **Method**: NIST Purge recommended

### PCI-DSS (Payment Cards)
- **Requirement 9.8**: Secure media disposal
- **Method**: NIST Purge or physical destruction

### NIST SP 800-88
- **Clear**: Logical overwrite (1 pass)
- **Purge**: Physical or logical (defeats lab recovery)
- **Destroy**: Physical destruction

## Troubleshooting

### "ATA Secure Erase not supported"
- Check with: `hdparm -I /dev/sda | grep -i security`
- Some drives disable this feature
- Solution: Use `nvme-format` (if NVMe) or `purge` method

### "Device is frozen"
- ATA Secure Erase may be frozen by BIOS
- Solution: Suspend/resume system to unfreeze
- Or: Hot-plug the drive

### "Sanitize not supported"
- Not all NVMe drives support sanitize
- Solution: Use `nvme-format` instead

### "Permission denied"
- Requires root/sudo access
- Solution: `sudo vsh` or run as root

## Tool Requirements

```bash
# For SATA SSDs:
sudo apt install hdparm  # Debian/Ubuntu
sudo dnf install hdparm  # Fedora

# For NVMe SSDs:
sudo apt install nvme-cli  # Debian/Ubuntu
sudo dnf install nvme-cli  # Fedora
```

## References

- NIST SP 800-88 Rev. 1 (2014): Guidelines for Media Sanitization
- ATA8-ACS: ATA/ATAPI Command Set
- NVMe 1.4: NVM Express Specification
- GDPR Article 17: Right to erasure
- CyBoK v1.0: Secure Deletion section
