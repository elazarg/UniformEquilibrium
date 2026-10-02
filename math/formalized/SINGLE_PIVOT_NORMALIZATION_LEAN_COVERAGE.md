# Single-pivot normalization: Lean coverage

Packet: [SINGLE_PIVOT_ZERO_NEVER_NORMALIZATION_AND_FINITE_MENU_SOURCE.md](SINGLE_PIVOT_ZERO_NEVER_NORMALIZATION_AND_FINITE_MENU_SOURCE.md).
Frozen SHA-256:
`b38ad18986ec59aac0cc22afc8006eead7b35ae7f58fc425e12b33a58cf699c5`.

Paths below are relative to `UniformEquilibrium/`.

## Transformation and fixed targets

`quittingFinitePureReplyPunishmentValue_eq_min`
(`Quitting/Punishment/FinitePureReplyPunishment.lean`) proves the signed
finite-date-only punishment identity against complete opponent plans.
`Quitting/Root/SinglePivotNormalization.lean` defines the terminal-only
normalization, canonical singleton vector, and reward bound.
`quittingPunishmentValue_singlePivotNormalized` and
`quittingSoloReward_sub_punishmentValue_singlePivotNormalized`
(`Quitting/Punishment/SinglePivotPunishment.lean`) transport punishment levels
and margins under original normality. The unchanged-profile payoff identity
in that module retains the joint-Never correction.

`exists_singlePivot_samePrefix_terminal_lift`
(`Quitting/Punishment/SinglePivotTailLift.lean`) constructs an actual original
profile with the exported payoff and full-debt estimates, retaining every
history before one cutoff and selecting one stationary punishment target.
`uniformEquilibriumPayoffSet_singlePivotNormalized`
(`Quitting/Punishment/SinglePivotUniformPayoff.lean`) proves equality of the
fixed-target payoff sets. Forward transport requires only a positive pivot;
reverse transport uses original all-player punishment normality.
`Quitting/Punishment/SinglePivotProfileDebtTransport.lean` exposes the actual
Never-mass and debt estimates used by these proofs.

`singlePivot_terminalExploitability_ge_gap_sq_div` and
`hasTerminalExploitabilityGap_singlePivotNormalized`
(`Quitting/Punishment/SinglePivotTerminalGap.lean`) give the quadratic
global floor and actual profitable deviations at half that floor, without
supremum attainment.

## Actual canonical source and consumers

`singlePivot_fullExploitability_eq_max_menuExploitability_scalar`
(`Quitting/Terminal/SinglePivotFiniteMenuSource.lean`) is the exact full-cap
reduction for every actual finite-menu product law. The same module proves
all nonpivot debts vanish at exact menu Nash, the pivot positive-part formula,
its deleted-Never upper bound, the positive own-Never support equality, and
the deadline-zero boundary. `exists_exactFiniteDeadlineTimingNash`
(`Quitting/Terminal/FiniteDeadlineNashExistence.lean`) supplies fresh mixed
Nash laws at every deadline.

`singlePivotSingletonTable_punishment_le_solo` and
`singlePivot_exactMenuNash_scalar_and_deletedNever_ge`
(`Quitting/Terminal/SinglePivotCanonicalConsequences.lean`) state automatic
canonical normality and positive scalar floors at every exact Nash law.
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff`
(`Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`) produces the
literal normalized table from bare original no-UE data, using one original
hard residual and one pivot fixed before all deadlines. Its output includes
the reward bound, exact punishment, normality, no UE, global floor, actual
deviations, universal exact-Nash scalar floors, and fresh laws.
`exists_finFour_no_uniformPayoff_iff_exists_singlePivot` in that module states
the canonical-counterexample existence equivalence.

`exists_uniformEquilibriumPayoff_of_singlePivot_finiteMenu_scalar_source`
(`Quitting/Terminal/SinglePivotFiniteMenuCompletion.lean`) consumes arbitrarily
small menu error and exceptional scalar. This is conditional on the actual
small-scalar producer; it does not require exact menu Nash.

## Finite packets, matrices, and boundaries

`Quitting/Root/SinglePivotFiniteBellmanTransport.lean` proves the Bellman,
endpoint, support-error, and compact-carrier identities.
`QuittingFiniteForwardPacket.singlePivotNormalized`
(`Quitting/Projective/SinglePivotFiniteForwardPacketTransport.lean`) retains
the supplied roots, horizon, and absorption charge and transports punishment
floors and support tolerance.
`Quitting/Classification/LCP/SinglePivotNormalizationTransport.lean` proves
the comparison-matrix scaling, signs, normal layers/core, homogeneous,
standard-Q, projective-Q, and projective-Q-bar equivalences.

The signed normal and nonnormal tables are checked in
`Diagnostics/Quitting/SinglePivotSignedNormalRegression.lean` and
`Diagnostics/Quitting/SinglePivotNonNormalRegression.lean`.
`Diagnostics/Quitting/SinglePivotFiniteMenuRegression.lean` checks exact menu
Nash with zero joint Never but pivot debt one-half.
`OnePlayerSignedBoundaryRegression.negative_full_and_finitePureReply_boundary`
(`Diagnostics/Quitting/TwoClockFiniteMenuRegression.lean`) states the negative
one-player boundary. The generic lift includes zero joint survival and the
one-player case; the raw reward bound is only `2M/g`, not a unit-box bound.

## Verification and remaining problem

Commit `7c39bc0` passed the full `lake --quiet --iofail build` with no Lean
output, the exhaustive axiom audit, trust/import/documentation checks, and
113 script tests. Independent reviews checked the lift, fixed-target
quantifiers, punishment transport, and actual Fin4 source.

The packet does not produce small scalar debt, early absorption for every
game, or a counterexample. No chosen minimum, near-minimum source, or response
ancestry is transported merely from the affine matrix identity.
