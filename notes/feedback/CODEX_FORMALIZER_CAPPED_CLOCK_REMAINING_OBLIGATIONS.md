# Capped-clock packet: remaining formalization obligations

The source is
`math/exports/CAPPED_CLOCK_DEVIATION_DOMINATION_AND_QUIET_EXTENSION.md`.
The packet is not fully formalized. The integrated interfaces and source
constructors are described in [the toolkit](../../docs/TOOLKIT.md).

## Checked scope

The deterministic and expected-clock inequalities allow general nonnegative
nonincreasing evaluations. So does the actual full behavioral-cap comparison
at reconstructed quiet parent profiles, by
`outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockEvaluatedFullBehavioralCap.lean`).
Its right side contains survivor debts in the parent game.
`quittingBehaviorEvaluatedDeviationDebt_liftDeletedProfile`
(`UniformEquilibrium/Quitting/Classification/PlayerDeletionEvaluatedPayoff.lean`)
preserves survivor debts under the existing Never lift for arbitrary clock
evaluations and arbitrary deleted-player predicates.
`quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockEvaluatedChildDeletionAdapter.lean`)
combines these results for every actual child behavioral profile, with debts
in the literal deleted child game on its right side. Its evaluation is
nonnegative and nonincreasing. The terminal adapter supplies the checked
fixed-target quiet-extension and four-player existence theorems.

`quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_error`
in the same evaluated child-deletion adapter transports a common reward-row
error to the actual Never lift and unrestricted behavioral debts. It charges
the row error times the evaluation at time zero, not twice that amount.
The `quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_rowError`
corollary charges just the row error when the evaluation at zero is at most
one. Separate Never/future/joining errors share the deterministic proof in
`CappedClockPointwiseDomination.lean`; the older Never-only theorem retains
its sharper clock-dependent correction. The cap transport factors through
one common-allowance argument instead of duplicating the exact proof.

The raw reward criterion has exact real and rational LP alternatives. Its
zero-weight case is equivalent to exact singleton block dispensability.
`cappedClockExpectedActualGain_le_iff_rewardRows`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockExpectationNecessity.lean`)
characterizes universal terminal expectation domination by the same fixed
nonnegative weights and reward rows. Dirac laws supply necessity; this is
not a necessity theorem for arbitrary behavioral debt comparisons.
The paired-family constructor preserves arbitrary nonsingleton coordinates
of the three surviving players and supplies a uniform-equilibrium payoff.
Every member fails exact singleton block deletion for every player.
The family and its deletion-3 child admit no balanced singleton cycle of any
period, by `not_nonempty_balancedSingletonCycleCertificate` and
`not_nonempty_balancedSingletonCycleCertificate_deleteThree`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedCycleExclusion.lean`).

## Work still needed

The terminating child-first rational search and its original-parent consumer
are proved in Research, including exact Never preservation and rational
amplification selection. Their scope is recorded in
[the rational producer note](CODEX_FORMALIZER_CAPPED_CLOCK_RATIONAL_PRODUCER.md).
The remaining packet work is:

1. Seal the additional example conclusions: slack values, terminal Nash laws,
   payoffs and caps, absence of pure terminal Nash equilibria, robustness under
   reward perturbations, and the comparison with the capped-joint hypothesis.
2. Formalize the solved table failing every deletion LP, the missing-Never
   example with zero child singleton, and the sparse-calendar missed response
   with its consecutive-menu repair.
3. Formalize the auxiliary strict inverse-row sharpness theorem: the positive
   inverse classification, forced vertex visits and block survival, the
   continuation-floor equivalence, and the quantitative response-debt bound.
   Its hypotheses concern an exact balanced singleton schedule, not all child
   equilibria or approximate ties.

These are known results supplied by the packet. This record does not assert
that the weighted criterion covers every four-player game, that its weights
are optimal, or that a finite-calendar implementation is complete without
testing the intervening gaps.
