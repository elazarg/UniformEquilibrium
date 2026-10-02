# Renewed phases and fixed-box sources: proof-mining audit

Author: CODEX_ROOT, recording the independent Astra formalization audit.
Audit date: 2026-09-06. Initial checkpoint: `c0aa4ed`; the literal-word
adapters and exact recharge strengthenings are integrated through `c6ca930`,
with a silent full build and repository checks.

## Question and status

Which useful strengthenings follow from the renewed-phase accounting and
fixed-box source theorems, and which source obligations remain distinct?
The initial pass was read-only. Subsequent checked compositions are recorded
separately from the remaining proposals. No arbitrary-game producer was derived.

## Renewed phases: covered supplied-data theorem

`QuittingRenewedActualProfileSequence`
(`UniformEquilibrium/Quitting/Root/RenewedActualProfileDebtRecharge.lean`)
retains actual behavioral sources and endpoints, unrestricted cap attainment,
and equality of each cap child with the next source. Its debt identities
require neither punishment normality nor absence of a uniform payoff.

`quittingLiteralExactWordBoxPath`
(`UniformEquilibrium/Quitting/Bellman/Finite/LiteralExactPrefixBoxPath.lean`)
retains the literal endpoint, source decoration, word length, and actual
absorption charge. The empty word retains its source decoration.
`QuittingRenewedLiteralExactWordSequence.toRenewedPathSequence`
(`UniformEquilibrium/Quitting/Root/RenewedLiteralExactWordSequence.lean`)
reuses the identical decorated child as the next path source.
`finFour_renewedLiteralExactWord_capacityRecharge`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourRenewedLiteralExactWordCapacity.lean`)
then gives the Fin4 necessary-capacity-recharge conclusion.

The common positive vertical debt drop is supplied separately. It is not
inferred from absorption expenditure. These adapters do not construct the
infinite renewed sequence described in the separate late-reset packet.

## Integrated recharge strengthenings

The following retain information discarded by the packet's linear lower
bounds. They are short consequences of existing checked accounting, not new
research mathematics. They passed the silent full build in `c6ca930`.

1. Retain the sum of actual phase absorption charges, the initial state's own
   capacity, and the terminal capacity in the recharge inequality. Dropping
   only the nonnegative terminal capacity improves both the packet's uniform
   expenditure bound and its global boundary constant.
2. State the exact cross-player debt ledger: total cross-player injection is
   total vertical debt drop plus total cap-response gain plus the terminal
   minus initial total-debt boundary. No uniform phase lower bound is needed.

The formalization also removes the positive phase-expenditure hypothesis
entirely from the exact absorption ledger. It applies to arbitrary families
of finite paths, then to arbitrary actual exact words with chosen source
decorations. Empty words, zero-charge phases, and horizontal changes that
are not cap responses are allowed. The horizontal term still uses the
identical next decorated source that occurs in the telescope. A positive
uniform expenditure is needed only for the separate linear-growth corollary.

The inputs are
`sum_verticalCharge_add_terminalPotentialDifference_le_sum_recharge`
(`MathUE/RenewedChargedPathPotentialRecharge.lean`),
`horizontalDebtInjection_eq_neg_capGain_add_cross`, and
`sum_horizontalDebtInjection_eq_sum_verticalDrop_add_boundary`
(`UniformEquilibrium/Quitting/Root/RenewedActualProfileDebtRecharge.lean`).

## Further candidates, not yet formalized

For the full boxed exact relation, changing only the starting state's root
decoration should preserve the set of reachable path charges. The edge
equations depend on its tail payoff, not that decoration. A proof would
transport the first edge and handle the empty path separately. This is a
proposed path-transport lemma, not a checked capacity-invariance theorem.
It would not permit replacing literal semantic ancestry by payoff equality.

The fixed-box characterization
`quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot`
(`UniformEquilibrium/Quitting/Projective/FixedBoxForwardCharacterization.lean`)
suggests replacing the fixed padding of two by any fixed positive padding:
choose the stationary approximation error correspondingly smaller. The
sequential source already stays in the reward box. The required source and
translation adjustments have not been formalized.

A second extension would add the solved all-singleton-self-payoffs-nonpositive
branch explicitly, removing the positive-singleton hypothesis from the
combined statement. Neither suggestion removes normality from the current
necessity theorem. The sure-root consumer does not assert stationary
repetition of its root.

## Parent and child reset sources must remain distinct

`eventually_every_exactRoot_has_debtDrop_and_absorption_at_immediateQuitCapReset`
(`UniformEquilibrium/Quitting/Root/NestedImmediateQuitCapExactPrefixExit.lean`)
spends debt at the reset parent `profiles time`. Its immediate-Quit cap
premise concerns `profiles (time+1)`. The late-renewal packet starts from the
actual reset child and gives different quantitative constants. The existing
parent theorem is therefore not the missing child-renewal adapter.

The pure-time prefix-selection theorems in
`UniformEquilibrium/Quitting/Root/PureTimeCapPrefixSelection.lean` provide
recursive ingredients, not the complete escaping-clock genealogy.

## Overlapping first-quitter packet remains incomplete

The pair inequalities in
`MathUE/Probability/OverlappingFirstStopping.lean` and
`MathUE/Probability/IndependentFirstStoppingPair.lean` do not yet cover the
export's equality classification. The actual terminal-outcome mass bridge
and quantitative game consumer are integrated through `98ea672`.
Size-two-support rigidity and the uniform-six-coordinate nonrealizability
example pass a targeted production build in
`UniformEquilibrium/Quitting/Paths/PairOnlyTerminalLawRigidity.lean`; their
full-build integration is pending. The explicit simplex certificate for the
candidate law and equality/sharpness results remain in progress.
No completion claim follows merely from the generic square-root inequality.

## Next checks

The main polynomial characterization is integrated in `98ea672`; its literal
boundary regressions remain pending. Retain the reset-child producers and
pair-law equality/sharpness obligations as separate work. A fresh Astra
cross-queue dependency/mining pass is running.
