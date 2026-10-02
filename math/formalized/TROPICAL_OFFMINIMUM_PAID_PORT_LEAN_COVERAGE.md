# Tropical descent to an off-minimum paid port: Lean coverage

Packet: [FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md](FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md).
Frozen SHA-256:
`52c87dac80db59733cf4f3bbdb26bcdf9a915060d94a94acc5bc29df5a51a027`.

## Actual source and chronology

`exists_periodOne_literalPaidCapChain_of_fourPlayer_noUniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/PeriodOneOffMinimumPaidPort.lean`
constructs the period-one source and a common strict subsequence from the
four-player no-uniform-payoff hypothesis. It produces two to four literal
unilateral updates, with attained unrestricted caps and one common positive
gain floor. The support-cardinality cases have the exported chain lengths.
Zero-share outsiders retain their original finite hazards.

The final edge is Quit0. Its source stays a fixed distance above minimum
total debt. `StationaryOffMinimumQuitNowPort.eventually_paid_initialRow`
retains the reached date-zero row, stationary continuation, positive local
endpoint gap, and own, opponent, and joint Continue half floors.

The supporting subset endpoint and coalition-law limits are in
`UniformEquilibrium/Quitting/Cycles/PeriodOneStationarySubsetLimits.lean`.
The two-owner zero-cross case uses the derived negative outsider in
`MathUE/LinearProgramming/TwoPointHomogeneousObstruction.lean`.
The singleton blocker and collar use
`UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean`
and `UniformEquilibrium/Diagnostics/Quitting/CompleteCapSingletonLimitCollar.lean`.

## Literal final law and minimum-face separation

`LiteralStationaryPaidCapChain.finalTarget_terminalOutcomeMass_tendsto_singleton`
and `StationaryOffMinimumQuitNowPort.cluster_cap_eq_and_minimumFace_gap`
in `UniformEquilibrium/Diagnostics/Quitting/PeriodOnePaidPortAdapters.lean`
prove the final recorded child's full singleton-law limit and the payer-cap
gap at every source cluster point against every minimum-face point.

`StationaryOffMinimumQuitNowPort.toCapPinSource` in
`UniformEquilibrium/Diagnostics/Quitting/PaidPortFirstExactRootHandoff.lean`
feeds the same roots, payer, and gain to the existing first-exact-root
dichotomy. It does not supply minimum-source ancestry or renewal.

## Duplicated-cyclic boundary

`UniformEquilibrium/Diagnostics/Quitting/DuplicatedCyclicReactivationRegression.lean`
uses the packet's zero-diagonal singleton table, zero nonsingleton rewards,
core hazards tending to zero, and the duplicate's squared hazard.
`UniformEquilibrium/Diagnostics/Quitting/DuplicatedCyclicReactivationBoundary.lean`
proves first-Never gain tending to one sixth for every core owner, second
Never and removed-owner Quit0 gains tending to one, literal updates, and
eventual unrestricted cap attainment for all three core-first choices.
`carrier_minimum_totalDebt_eq_zero` supplies the actual all-Never carrier
minimizer with total debt zero.

The export's phrase "unique profitable second Never deletion" is scoped to
the two remaining leading-core support owners. This scope is explicit in the
support-owner argument of
`math/notes/CODEX_SNELL__AGGREGATE_PAID_ORIENTATION_FINITE_ATOM_AND_NORMALIZED_PASSPORT.md`.
`eventually_selectedRemainingGain_pos_and_otherGain_neg` proves the positive
and negative gains of those two owners on the same eventual tail. No
uniqueness across all four players is claimed: the lower-order duplicate
is not one of those two support owners.

## Verification and remaining boundary

The integrated full `lake build`, including the exhaustive axiom audit,
passed with 11461 jobs. The main source/paid-port theorem and limit adapters
also passed earlier full builds. The boundary module passed its targeted
warning-as-error check and independent static source review.

The packet supplies the off-minimum paid row and actual tropical ancestry.
It does not supply ancestry from a minimum-fibre realizer, source renewal,
an approximate equilibrium, or an unconditional uniform-equilibrium payoff.
