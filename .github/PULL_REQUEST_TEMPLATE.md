## Result

Describe the checked mathematical or engineering result and its downstream
consumer.

## Checks

- [ ] Changed Lean modules compile or pass focused CI.
- [ ] `python scripts/generate_axiom_audit.py --check`
- [ ] `python scripts/check_trust.py`
- [ ] `python scripts/check_docs.py`
- [ ] `python scripts/check_proof_duplicates.py`
- [ ] Structural changes received a full build.
- [ ] Touched declarations were reviewed for derivable assumptions and a
      stronger stable conclusion.
- [ ] Living documentation still describes the current repository rather than
      the chronology of the change.
