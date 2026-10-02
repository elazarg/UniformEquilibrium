# Nested terminal cap-child coverage

Author: CODEX_ROOT. The integration through `88709a1` passed the silent full
build, trust scan, import-graph, duplicate, telescope, and documentation checks.
An independent Astra audit checked the packet's affirmative conclusions.

Frozen source: `FIN4_NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT.md`,
SHA-256 `4962a0e951e2e02fbf1a5df77894494098fc7feee6b7811592193f116ec3c8ec`.

## Declaration map

- `quittingPureTimeCapChild_source_facts` and
  `quittingForcedContinueReversePrefixProfile_eq_child`
  (`UniformEquilibrium/Quitting/Root/NestedCapChildFixedDebtor.lean`) retain
  literal owner-forced genealogy and survival. The generic single-profile
  child constructor is `quittingPureTimeCapChild`
  (`UniformEquilibrium/Quitting/Root/PureTimeCapChild.lean`).
- `quittingPureTimeCapChild_owner_zeroDebt_and_deadlineAbsorption`
  (`UniformEquilibrium/Quitting/Root/CapChildDeadlineAbsorption.lean`) states
  zero owner debt and actual zero live mass after the prescribed deadline.
- `HasTerminalExploitabilityGap.exists_infiniteSurvival_fixedOutsiderResponse`
  (`UniformEquilibrium/Quitting/Root/NestedCapChildInfiniteSurvivalDebtor.lean`)
  uses the literal infinite joint-survival product before all requested
  starting depths. At each starting depth it selects one outsider and one
  bounded finite-or-Never cap-attaining response, before every later depth.
  It retains the exact gain of the copied behavioral response, the actual
  window-times-gap debt floor, and the infinite-product-times-gap floor.
- `exists_coherentOutsiderCapClock_on_pureTimeCapChildren`,
  `quittingCapClock_eventually_shift_or_cofinally_reset`, and
  `quittingCapClock_eventually_shift_iff_not_cofinally_reset`
  (`UniformEquilibrium/Quitting/Root/CoherentPureTimeCapClock.lean`) give
  coherent complete caps and exclusive alternatives, including permanent
  Never. Finite last-reset arithmetic uses `Nat.succ_sub_succ_eq_sub` and
  `Nat.sub_zero`; no new clock-specific arithmetic definition is needed.
- `quittingNestedSourceAndChild_terminalPayoff_bellman` and
  `quittingNestedSourceAndChild_outsiderEndpointSeam_expanded`
  (`UniformEquilibrium/Quitting/Root/NestedChildBellmanEndpointDifference.lean`)
  state the literal child Bellman identity and all four terms of the
  outsider endpoint difference.
- `quittingNestedCapChild_owner_rootNash`,
  `summable_nestedChildSeam_quitPayoffDifference`,
  `summable_nestedChildSeam_absorbingContributionDifference`, and
  `summable_nestedChildSeam_survivalDifference_mul_source`
  (`UniformEquilibrium/Quitting/Root/NestedOwnerRootNashSeamSummable.lean`)
  prove owner root optimality and the separate summable first, second, and
  fourth terms. The third displacement term is not assumed summable.
- `tendsto_forcedContinue_opponentSurvival_one_of_summable_marginalHazard`
  (`UniformEquilibrium/Quitting/Paths/SummableRootSurvival.lean`) gives the
  coefficient limit without early positive survival or distinctness.

## Scope

The mathematical core holds for arbitrary finite player sets under its
explicit source assumptions. The Fin4 no-uniform-payoff hypothesis supplies
hazard summability through the separate actual-prefix capacity adapter.
The theorem does not construct outsider root Nash, summable outsider Nash
defects, finite-clock complete semantics, a returned source, or a uniform
payoff. The packet's explanations of these nonclaims are not represented
as checked counterexample constructions.
