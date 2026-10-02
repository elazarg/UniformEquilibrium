# Closure of `fakeAnswer_persistentTwoLabelHazards`

Target: `Reverse/QuestionBankFakeProof.lean` at commit
`157bb8d200fa4202a64c50e9fe978236a8e0dca6`.

The stated theorem is false because it is polymorphic over every finite,
nonempty player type.  Taking `ι = Fin 1`, the field
`HasTwoPersistentQuittingMarginals roots` supplies players `first` and
`second` with `first ≠ second`; the `Subsingleton (Fin 1)` instance supplies
`first = second`.

The patch therefore replaces the `sorry`-backed positive theorem by:

1. a reward-independent impossibility theorem for every subsingleton player
   type;
2. an explicit refutation of the original universal statement using `Fin 1`;
3. a nonvacuous per-game consumer: whenever an actual
   `PersistentTwoLabelNashBellmanAnswer reward` is supplied, the existing
   checked survival and chronological-shadowing machinery yields a uniform
   equilibrium payoff.

No mathematical assumption is added and no theorem is silently weakened under
its old name.  Four unrelated `sorry`s remain in the fake-proof file.

## Validation and branch state

- The source reconstructed from the immutable target commit has Git blob
  `c149863e79bbd456ab10bbc3cdbbaa96c9d8c327`.
- `git apply --check` succeeds against that exact source, and the result is
  byte-for-byte identical to `QuestionBankFakeProof.closed.lean`.
- `git diff --check` succeeds; the target file's `sorry` count falls from five
  to four.
- Lean elaboration and theorem-level `#print axioms` were not run in this
  runtime because no Lean toolchain or compatible compiled dependency cache is
  available.

While this work was in progress, the remote `fake-proof` branch advanced to
commit `e80ab0f949277b09e3e5a6c88a7222f058aa3b5b`.  That commit independently
adds the missing cardinality premise and handles the singleton case using the
one-player existence theorem, but it retains the corrected two-label theorem
as a `sorry`.  This patch therefore remains deliberately based on the immutable
commit linked in the task and was not written over the moved branch.
