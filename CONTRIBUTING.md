# Contributing to Valence Shell

Thank you for your interest in contributing to Valence Shell! This project welcomes contributions across multiple perimeters using the **Tri-Perimeter Contribution Framework (TPCF)**.

## Quick Start

1. **Read this guide** to understand the contribution model
2. **Choose your perimeter** based on trust level and scope
3. **Follow the workflow** for your perimeter
4. **Submit your contribution** via pull/merge request

## Tri-Perimeter Contribution Framework (TPCF)

Valence Shell uses a graduated trust model with three contribution perimeters:

### 🔴 Perimeter 1: Core (Restricted - Maintainer Only)

**What**: Formal proofs, core algorithms, security-critical code

**Who**: Project maintainers with formal methods expertise

**Files**:
- `proofs/coq/*.v` - Coq proofs
- `proofs/lean4/*.lean` - Lean 4 proofs
- `proofs/agda/*.agda` - Agda proofs
- `proofs/isabelle/*.thy` - Isabelle proofs
- `proofs/mizar/*.miz` - Mizar proofs
- `impl/ocaml/filesystem_ffi.ml` - FFI layer

**Requirements**:
- Formal verification expertise
- Proof assistant proficiency
- Security review process
- Maintainer approval required

**How to Contribute**:
1. **Discuss first**: Open an issue to propose changes
2. **Get approval**: Maintainers will assess feasibility
3. **Submit RFC**: Formal Request for Comments document
4. **Review process**: May take weeks, involves proof checking
5. **Merge**: Requires 2+ maintainer approvals

### 🟡 Perimeter 2: Extensions (Reviewed - Trusted Contributors)

**What**: Implementations, optimizations, new features

**Who**: Experienced contributors with track record

**Files**:
- `impl/elixir/` - Elixir implementation
- `scripts/` - Demonstration scripts
- `docs/` - Technical documentation
- Build system (justfile, Containerfile)
- CI/CD pipelines

**Requirements**:
- Familiarity with formal specifications
- Code review by maintainer
- Tests must pass
- Documentation required

**How to Contribute**:
1. **Fork the repository**
2. **Create feature branch**: `git checkout -b feature/your-feature`
3. **Implement with tests**: Match formal specifications
4. **Update documentation**: Keep docs in sync
5. **Submit PR/MR**: Reference related issues
6. **Address review**: May require iterations
7. **Merge**: Requires 1 maintainer approval

### 🟢 Perimeter 3: Community Sandbox (Open - Anyone)

**What**: Examples, tutorials, experimental features, tooling

**Who**: Anyone! Open contribution model

**Files**:
- `examples/` - Example scripts and use cases
- `tutorials/` - Learning materials
- `tools/` - Helper utilities
- `docs/blog/` - Blog posts
- Community documentation

**Requirements**:
- Basic testing
- Clear documentation
- LICENSE compliance
- Code of Conduct adherence

**How to Contribute**:
1. **Fork and branch**
2. **Create your contribution**
3. **Add README**: Explain what it does
4. **Submit PR/MR**: Self-documenting
5. **Merge**: Can be merged by any maintainer quickly

**Examples**:
- Tutorial: "Getting Started with Formal Verification"
- Tool: `vsh-visualizer` (shows operation sequences)
- Example: `photo-backup-script` using vsh
- Blog post: "Why Reversibility Matters"

## Development Setup

### Prerequisites

**Minimum** (to run examples):
- Git
- One of: OCaml 5.0+, Elixir 1.15+, Bash

**Full Development** (to modify proofs):
- Coq 8.18+
- Lean 4.3+
- Agda 2.6.4+
- Isabelle 2024
- Z3 4.12+
- Just (command runner)
- Nix (recommended for reproducible builds)

### Setup Instructions

```bash
# Clone the repository
git clone https://github.com/Hyperpolymath/valence-shell.git
# OR
git clone https://gitlab.com/non-initiate/rhodinised/vsh.git

cd valence-shell

# With Nix (recommended)
nix develop
just build-all

# Without Nix (manual setup)
# Install proof assistants per their documentation
# Then:
just build-coq
just build-lean4
just test-all
```

## Contribution Workflow

### 1. Find or Create an Issue

- Check existing issues: https://github.com/Hyperpolymath/valence-shell/issues
- Create new issue if needed
- Discuss approach before major work

### 2. Fork and Branch

```bash
# Fork on GitHub/GitLab, then:
git clone https://github.com/YOUR_USERNAME/valence-shell.git
cd valence-shell
git checkout -b feature/descriptive-name
```

**Branch Naming**:
- `feature/` - New features
- `fix/` - Bug fixes
- `docs/` - Documentation
- `proof/` - Proof additions/fixes
- `refactor/` - Code refactoring

### 3. Make Changes

**For Proofs (Perimeter 1)**:
- Modify `.v` (Coq), `.lean` (Lean 4), `.agda` (Agda), etc.
- Ensure proofs compile: `just verify-proofs`
- Update cross-references if adding theorems
- Document in `proofs/README.md`

**For Implementations (Perimeter 2)**:
- Match formal specifications exactly
- Add tests: `scripts/test_*.sh` or `test/`
- Update `impl/*/README.md`
- Check against demo: `just demo`

**For Community (Perimeter 3)**:
- Be creative!
- Focus on usefulness and clarity
- Add examples of usage

### 4. Test Your Changes

```bash
# Run all tests
just test-all

# Verify specific system
just build-coq
just build-lean4

# Run demos
just demo

# Check formatting (if applicable)
just lint
```

### 5. Commit Your Changes

**Commit Message Format**:

```
<type>(<scope>): <subject>

<body>

<footer>
```

**Types**:
- `feat`: New feature
- `fix`: Bug fix
- `proof`: Proof addition/modification
- `docs`: Documentation
- `refactor`: Code refactoring
- `test`: Test additions
- `chore`: Build/tooling changes

**Examples**:

```
feat(proof): Add file copy operation reversibility

Proves that copy(src, dest, fs) can be undone by:
1. delete(dest, fs) - remove copy
2. restore(src, old_content, fs) - restore if src was modified

Includes theorems in Coq and Lean 4.

Closes #123
```

```
docs(tutorial): Add beginner's guide to reversible operations

Explains:
- What reversibility means
- How Valence Shell guarantees it
- Examples with mkdir/rmdir

Target audience: developers new to formal verification
```

### 6. Push and Create PR/MR

```bash
git push origin feature/descriptive-name
```

Then create Pull Request (GitHub) or Merge Request (GitLab):
- **Title**: Clear, descriptive
- **Description**: What, why, how
- **Link issues**: "Fixes #123" or "Relates to #456"
- **Perimeter**: Tag which perimeter (1, 2, or 3)
- **Testing**: Describe how you tested

### 7. Code Review

**Perimeter 1**: Rigorous review, may take time
**Perimeter 2**: Standard review, iterate if needed
**Perimeter 3**: Quick review, usually fast merge

**Reviewers may ask**:
- Clarifications
- Changes to implementation
- Additional tests
- Documentation improvements

**Be patient and collaborative!**

## Coding Standards

### Proof Code

**Coq**:
- Follow Software Foundations style
- Use meaningful theorem names
- Add comments for complex proofs
- Avoid `admit`/`Admitted` in main branch

**Lean 4**:
- Use `snake_case` for definitions
- Use `CamelCase` for types
- Provide type signatures explicitly
- Use `sorry` only in drafts

**Agda**:
- Unicode symbols where conventional
- Pattern matching preferred over case splits
- Implicit arguments where clear

### Implementation Code

**OCaml**:
- Follow Jane Street style guide
- Type annotations on public functions
- No `Obj.magic` or `unsafe` operations
- Document FFI boundaries

**Elixir**:
- Follow Elixir style guide
- @spec for all public functions
- Pattern matching over conditionals
- Doctests where applicable

### Documentation

- Markdown for text documents
- AsciiDoc for technical documentation
- Code examples should be tested
- Keep CLAUDE.md updated for AI assistants

## Testing

### Proof Verification

```bash
# Verify all proofs compile
just verify-proofs

# Individual systems
just build-coq
just build-lean4
just build-agda
just build-isabelle
```

### Implementation Testing

```bash
# Run all tests
just test-all

# Demo script (comprehensive)
./scripts/demo_verified_operations.sh

# Specific operations
./scripts/test_mkdir_rmdir.sh
```

### Continuous Integration

All PRs/MRs automatically run:
- Proof compilation (all systems)
- Implementation tests
- Documentation builds
- Linting (where applicable)

Must pass before merge.

## Documentation

### What to Document

**Proofs**: Theorem statements, key lemmas, proof strategies
**Implementations**: Public APIs, preconditions, examples
**Examples**: Usage, expected output, prerequisites

### Where to Document

- **In-code comments**: Technical details
- **README files**: Directory-level overviews
- **docs/**: Design documents, reports
- **CLAUDE.md**: Keep updated for AI context
- **CHANGELOG.md**: User-facing changes

## Licensing

All contributions must be compatible with:
- **MIT License** (permissive)
- **Palimpsest License v0.8** (attribution + history)

By contributing, you agree to license your contributions under both licenses.

See [LICENSE.txt](LICENSE.txt) for full text.

## Recognition

Contributors are recognized in:
- `MAINTAINERS.md` (for sustained contributions)
- Git commit history (always preserved)
- Release notes
- Academic papers (if research contribution)
- `.well-known/humans.txt`

## Communication

### Channels

- **GitHub Issues**: Feature requests, bug reports
- **GitLab Issues**: Alternative (main dev repo)
- **Discussions**: General questions (TBD)
- **Email**: For sensitive matters (see MAINTAINERS.md)

### Response Times

- **Perimeter 3**: Usually within 7 days
- **Perimeter 2**: Usually within 14 days
- **Perimeter 1**: May take 30+ days (proof review is intensive)

### Getting Help

**Stuck on proofs?**
- Check `proofs/README.md`
- Review similar theorems
- Ask in issue comments
- Reference Software Foundations textbook

**Unclear about specifications?**
- Read formal model documentation
- Check existing implementations
- Ask for clarification in issue

**General questions?**
- Open a discussion (GitHub)
- Tag with `question` label

## Code of Conduct

All contributors must follow our [Code of Conduct](CODE_OF_CONDUCT.md).

**Summary**:
- Be respectful and professional
- Welcome diverse perspectives
- Focus on ideas, not people
- Harassment will not be tolerated

## First-Time Contributors

Welcome! Here are good first issues:

**Perimeter 3** (Easy):
- Add example scripts
- Improve documentation
- Write tutorials
- Fix typos

**Perimeter 2** (Moderate):
- Add tests
- Improve error messages
- Optimize build scripts
- Port implementations

**Perimeter 1** (Advanced):
- Extend proofs to new operations
- Add proof in new system
- Prove admitted lemmas

Look for issues tagged `good-first-issue` or `help-wanted`.

## Maintainer Duties

Maintainers will:
- Review contributions promptly
- Provide constructive feedback
- Merge when ready
- Maintain welcoming environment
- Uphold quality standards

Maintainers may not:
- Merge without review (Perimeter 1-2)
- Ignore Code of Conduct violations
- Make breaking changes without discussion

See [MAINTAINERS.md](MAINTAINERS.md) for current maintainers.

## RSR Compliance

This project follows the **Rhodium Standard Repository (RSR) Framework**.

Contributions should maintain:
- ✅ Type safety (proof systems guarantee this)
- ✅ Memory safety (OCaml, no unsafe)
- ✅ Offline-first (no network dependencies)
- ✅ Test coverage (verify before merge)
- ✅ Documentation (keep updated)

See [RSR_COMPLIANCE.md](RSR_COMPLIANCE.md) for details.

## Academic Contributions

If your contribution is part of academic research:

1. **Cite the project**: See CITATION.cff (TBD)
2. **Coordinate publication**: Discuss with maintainers
3. **Open access**: Prefer open-access venues
4. **Share data**: Make proofs/benchmarks reproducible

See `docs/academic-papers.md` for related publications.

## Thank You!

Your contributions make Valence Shell better for everyone. Whether you're fixing a typo or proving a complex theorem, your work is valued.

Questions? Open an issue or check [CLAUDE.md](CLAUDE.md) for project context.

---

**Last Updated**: 2025-11-22
**Version**: 1.0
**Maintainer**: See [MAINTAINERS.md](MAINTAINERS.md)
