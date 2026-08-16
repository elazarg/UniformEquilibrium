# Exact joint-reset law regression

This bounded experiment checks the formulas in
[the exact joint-reset lift](../../docs/JOINT_RESET_LIFT.md) using exact rational
arithmetic.

The general identities are proved in Lean in
[`TerminalSemanticJointResetLift`](../../UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticJointResetLift.lean).
This experiment remains a reproducible implementation-level regression for
the sparse exact-arithmetic model.

Run from the repository root:

```text
python Experiments/joint_reset_law/joint_reset_law.py
```

The program checks:

- one four-player semantic chronology against its sparse joint-reset law;
- payoff-spine, cap-identity, debt, and two-anchor sensitivity identities;
- 900 deterministic arbitrary-law semiconjugacy instances for one through
  five players; and
- all 4,096 products of the 64 syntactic two-player reset modes for the
  idempotence, left-regular-band, and support-union laws.

Inputs are generated deterministically in the source; the randomized sweep
uses seed `195`. All computed values are `fractions.Fraction` values, so the
assertions involve exact equality rather than floating-point tolerances.

The experiment assumes the finite quitting reward-table and semantic-prefix
formulas stated in the joint-reset lift. It checks only the bounded instances
above. It is not a proof of the general semiconjugacy, not a Lean check, and
not evidence for a positive debt floor or semialgebraic barrier. In particular,
the invariant convex hull of reset images can contain negative-debt vertices,
so the experiment does not prove a positive debt barrier.
