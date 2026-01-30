# Secure Deletion Standards for Valence Shell RMO

## Standards Compliance

### NIST SP 800-88 Rev. 1 (Guidelines for Media Sanitization)

**Clear** (Logical sanitization):
- **Method**: 1 pass overwrite
- **Pattern**: Zeros, ones, or random data
- **Use case**: Normal file deletion, GDPR compliance
- **Protection**: Prevents casual data recovery

**Purge** (Physical/logical sanitization):
- **HDDs**: Cryptographic erase, degaussing, or physical destruction
- **SSDs**: Firmware secure erase (ATA Secure Erase, NVMe Format/Sanitize)
- **Use case**: High-security deletion, end-of-life
- **Protection**: Defeats laboratory recovery

**Destroy**:
- **Method**: Physical destruction (shredding, incineration, disintegration)
- **Use case**: Maximum security, decommissioning
- **Protection**: Complete media destruction

### CyBoK (Cyber Security Body of Knowledge)

- **Modern HDDs**: Single pass sufficient (high bit density)
- **SSDs**: Hardware-based secure erase only (wear leveling defeats overwrite)
- **Cryptographic erasure**: Encrypt data, destroy keys (instant, reliable)

### UK NCSC Guidelines

- **Standard**: 1 pass of zeros
- **Enhanced**: 1 pass + verification
- **SSDs**: Use manufacturer secure erase

### BSI (German Federal Office)

- **Normal**: 1 pass random or zeros
- **High**: 2 passes + verification
- **Very High**: Physical destruction

## Valence Shell RMO Implementation

### Tier 1: GDPR Compliance (Default)
```rust
// Single pass overwrite (NIST Clear)
obliterate(file, method: "clear")  // 1 pass zeros
```

### Tier 2: Enhanced Security
```rust
// Verified overwrite
obliterate(file, method: "nist-purge", verify: true)  // 1 pass + verify
```

### Tier 3: High Security (SSD-aware)
```rust
// Hardware secure erase for SSDs
obliterate(file, method: "hardware-erase")  // ATA Secure Erase/NVMe Sanitize

// Cryptographic erasure
obliterate(file, method: "crypto-erase")    // Destroy encryption key
```

### Tier 4: Maximum Security
```rust
// Hardware + verification + physical
obliterate(file, method: "destroy")         // Triggers physical destruction workflow
```

## Why Not Gutmann/DoD 5220.22-M?

1. **Gutmann (35 passes)**: Designed for 1990s MFM/RLL drives
   - Modern drives: 1 pass sufficient (NIST, CyBoK, NCSC)
   - Gutmann himself: "unnecessary for modern drives"

2. **DoD 5220.22-M (3 passes)**: Superseded by NIST SP 800-88
   - DoD now uses NIST 800-88
   - 3 passes provide no additional security on modern drives

3. **SSD Problem**: Overwrite-based methods unreliable
   - Wear leveling redirects writes
   - Hidden reserved blocks
   - Need firmware commands

## Implementation Priority

1. ✅ **Clear** (1 pass) - GDPR, normal use
2. ✅ **Purge** (verified) - High security
3. ⏸️ **Hardware erase** - SSD support (ATA/NVMe)
4. ⏸️ **Crypto erase** - Key destruction
5. ⏸️ **Destroy** - Physical destruction workflow

## References

- NIST SP 800-88 Rev. 1 (2014)
- CyBoK v1.0 (2019)
- UK NCSC Secure Sanitisation Guide
- BSI Technical Guideline TG 03203
- Peter Gutmann, "Secure Deletion of Data from Magnetic and Solid-State Memory" (1996)
- Peter Gutmann, "Epilogue" (2008) - "The legacy encodings are not relevant to modern drives"
