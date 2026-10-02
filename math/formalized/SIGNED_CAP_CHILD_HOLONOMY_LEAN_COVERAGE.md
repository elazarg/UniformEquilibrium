# Signed cap-child displacement and reset dichotomy coverage

Author: CODEX_ROOT. Integration through `c2789f0` passed the silent full
build and trust, import-graph, duplicate, telescope, and documentation checks.
An independent Astra review checked the complete packet against the
declarations and their actual-source adapters.

Frozen packet: `FIN4_SIGNED_CAP_CHILD_HOLONOMY_RESET_DICHOTOMY.md`,
SHA-256 `e1c11306e9fe953c03ab661b74356f1a88c9ad04b7021439033c4b2b6c2590ef`.

## Declaration map

- `terminalChildPayoffDisplacement_next_eq`,
  `abs_quittingForcedContinueOwnerCorrection_le_two_mul`, and
  `abs_terminalChildPayoffDisplacement_next_sub_le`
  (`UniformEquilibrium/Quitting/Root/ForcedContinuePayoffDisplacement.lean`)
  prove the signed affine recurrence and quantitative bounds. The correction
  bound uses twice the reward bound, strengthening the packet's factor four.
- `quittingForcedContinueOwnerCorrection_eq_sum_opponentCoalitionMass`
  (`UniformEquilibrium/Quitting/Root/ForcedContinueOwnerCorrectionCoalitionSum.lean`)
  gives the full owner-deleted coalition expansion, including the empty
  coalition's continuation-minus-singleton contribution.
- `summable_abs_terminalChildPayoffDisplacement_increment`
  (`UniformEquilibrium/Quitting/Root/TerminalChildPayoffDisplacementSequence.lean`)
  gives finite variation and convergence.
  `exists_terminalCapChildDisplacement_limit_series`
  (`UniformEquilibrium/Quitting/Root/TerminalChildPayoffDisplacementSeries.lean`)
  states the infinite-product and absolutely summable weighted-series formula
  for the literal actual child genealogy, from every starting depth.
- `quittingNestedCapChild_eventuallyShift_or_negativeHolonomy`
  (`UniformEquilibrium/Quitting/Root/SignedCapChildHolonomyDichotomy.lean`)
  retains one coherent complete-cap clock and its actual displacement limit.
  Cofinal resets force the limit below the negative full debt floor, rather
  than only negative half the floor. Early positive survival is unnecessary.
  Clock exclusivity, including Never, is proved by
  `quittingCapClock_eventually_shift_iff_not_cofinally_reset`
  (`UniformEquilibrium/Quitting/Root/CoherentPureTimeCapClock.lean`).
- `finFour_summable_actualExactPrefix_hazard_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourActualPrefixHazard.lean`)
  supplies summable hazards from the actual exact genealogy under failure
  of uniform-payoff existence.
  `HasTerminalExploitabilityGap.exists_infiniteSurvival_fixedOutsiderResponse`
  (`UniformEquilibrium/Quitting/Root/NestedCapChildInfiniteSurvivalDebtor.lean`)
  supplies the fixed outsider and common positive debt floor.
- `nonzero_displacement_limit_seam_not_tendsto_zero_not_summable` and
  `harmonic_displacement_finite_variation_zero_limit_not_summable`
  (`MathUE/DisplacementSeamScalarBoundaries.lean`) prove the two scalar
  boundary tests: a nonzero limiting displacement obstructs seam decay,
  while zero limit and finite variation need not imply summable values.

## Scope

The generic identities apply to finite player sets with the displayed
genealogy and summability assumptions. Fin4 is used in the separate
counterexample-side hazard producer. The result does not make outsider
roots Nash, construct a re-equilibrated source, charge a horizontal
installation, or produce a uniform payoff. The scalar boundary examples
are not quitting-game counterexamples. No summability of displacement
values is inferred from summability of their increments.
