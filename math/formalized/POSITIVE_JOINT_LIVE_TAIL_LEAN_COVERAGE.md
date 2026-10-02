# Positive joint survival and cap transport: Lean coverage

Packet: [POSITIVE_JOINT_LIVE_TAIL_AND_CAP_LIVE_BOUNDARY.md](POSITIVE_JOINT_LIVE_TAIL_AND_CAP_LIVE_BOUNDARY.md).
Moved unchanged from `exports/`; SHA-256
`7f4a691fe79efbe3ccb2444ad05ce54fbf4400f153dc7b605a581cfe1f26df67`.

## Literal profile theorems

[`FiniteWordSemanticSplice.lean`](../../UniformEquilibrium/Quitting/Root/FiniteWordSemanticSplice.lean)
proves:

- `isAsymptoticNash_tail_of_literalRootStack_joint_pos`: the actual arbitrary
  behavioral tail is approximate Nash with error divided by joint survival.
- `exists_diagonal_tail_limit_of_literalRootStack_nash_ratio`: vanishing
  divided error produces a strict subsequence of those same tails converging
  to a diagonal semantic pair and its fixed uniform-equilibrium payoff.
- `quittingFiniteRootWordSemanticPrefix_eq_foldr`: the separate payoff and
  cap folds equal the native semantic prefix action on all algebraic pairs.
- `literalRootStack_debt_le_referenceDebt_add_transmittedSeams`: actual
  splice debt is bounded by algebraic prefix debt, the positive cap discrepancy
  multiplied by opponent survival, and the absolute payoff discrepancy
  multiplied by joint survival.
- `growingWord_referenceSeams_completion`: the stated vanishing discrepancies
  give actual payoff convergence, actual unrestricted exploitability tending
  to zero, and the fixed uniform target.

The finite-word one-sided cap inequality is
`quittingFiniteRootWordCap_sub_le_opponentSurvival_mul_posPart` in
[`CommonPrefixCapStability.lean`](../../UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean).

## Specializations and boundary example

[`FiniteWordSurvivalSeams.lean`](../../UniformEquilibrium/Quitting/Root/FiniteWordSurvivalSeams.lean)
proves exact-chain diagonal preservation, vanishing tail debt under a positive
joint floor, convergence of both tail coordinates to the varying diagonal
reference, and erasure of bounded discrepancies by their respective vanishing
survival coefficients. The reference need not itself converge.

[`HostClearingBoundary.lean`](../../UniformEquilibrium/Quitting/Examples/HostClearingBoundary.lean)
keeps the original and marked profiles distinct. It proves the original
joint/deleted clocks, the actual diagonal all-Continue tail, the marked
singleton coalition's mass one, the host's complete cap and debt zero, and the
outsider's literal immediate-Quit gain one. Clearing the host does not change
the other players' behavior.

## Verification

All three new modules and the modified cap-transport dependency passed targeted
Lean checks and named dependency builds. Parent review checked the actual-tail
quantifiers, distinct survival coefficients, varying references, and the two
separate profiles in the counterexample. The integrated full `lake build`,
including the exhaustive axiom audit, passed with 11435 jobs. Trust,
import-graph, documentation, duplicate-proof, reward-bound, and
redundant-hypothesis checks passed.
