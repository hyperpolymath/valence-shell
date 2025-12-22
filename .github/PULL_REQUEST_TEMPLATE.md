## Summary

<!-- Brief description of what this PR does -->

## Type of Change

- [ ] Bug fix (non-breaking change fixing an issue)
- [ ] New feature (non-breaking change adding functionality)
- [ ] Breaking change (fix or feature causing existing functionality to change)
- [ ] Documentation update
- [ ] Proof addition/modification
- [ ] Refactoring (no functional changes)

## Checklist

### Code Quality
- [ ] Code follows the project style guidelines (`mix format`)
- [ ] Credo passes without errors (`mix credo --strict`)
- [ ] Tests pass (`mix test`)
- [ ] New code has appropriate tests

### Reversibility (for command implementations)
- [ ] Implements `Valence.Command` behaviour
- [ ] `execute/2` returns proper compensation
- [ ] `compensate/2` correctly reverses the operation
- [ ] `verify/1` detects drift

### Formal Verification (if modifying proofs)
- [ ] Coq proofs compile (`just prove`)
- [ ] No new `Admitted` or `sorry`
- [ ] Cross-validation in at least 2 proof systems

### Documentation
- [ ] README updated (if needed)
- [ ] CHANGELOG updated
- [ ] Docstrings added for new public functions

### Sacred Files
- [ ] I have NOT modified sacred files (README.adoc, STATE.adoc, ARCHITECTURE.md, META.scm) without explicit approval

## Related Issues

<!-- Link any related issues: Fixes #123, Relates to #456 -->

## Testing

<!-- Describe how you tested this change -->

## Screenshots (if applicable)

<!-- Add screenshots for UI changes -->
