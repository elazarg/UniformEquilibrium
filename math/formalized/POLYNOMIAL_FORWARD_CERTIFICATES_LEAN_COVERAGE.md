# Polynomial forward certificates: Lean coverage

Packet: `POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md`.
Frozen SHA-256:
`14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`.
Main characterization checkpoint: `98ea672`.
Boundary examples and completed coverage checkpoint: `bc9a439`.
Both are pushed and passed full silent builds and repository checks.

Paths are relative to the project root. The packet is retained byte for byte;
this record supplies its subsequent Lean status.

## Input removal and semantic necessity

`hasFloorFreeExactFiniteForwardPackets_iff_exact` and
`hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted`
(`UniformEquilibrium/Quitting/Projective/FloorFreeForwardPacketInputRemoval.lean`)
remove the punishment-floor input without changing the supplied box.
The finite burn-in proof is in
`UniformEquilibrium/Quitting/Bellman/Finite/FiniteEndpointErrorPunishmentFloor.lean`.
The deleted number of initial construction rows is fixed before the requested
surviving charge, and all retained endpoints have the floor.

`quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot`
(`UniformEquilibrium/Quitting/Projective/FixedBoxForwardCharacterization.lean`)
proves the normal Fin4 fixed-box necessity alternative under a positive
singleton reward. The finite sure-root characterization is in
`UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean`.
The source adapters use the proved forward trichotomy and literal stationary
or restarted terminal payoffs; the printed reverse-S.3 claim is not an input.

## Actual capacity-to-polynomial construction

`exists_quittingRobustPath_eq_compactFiniteHorizonMaxCharge`,
`upperSemicontinuous_quittingRobustCompactFiniteHorizonMaxCharge`, and
`measurable_quittingRobustChargedRelation_value`
(`UniformEquilibrium/Quitting/Projective/RobustChargedRelationCapacity.lean`)
cover finite-horizon attainment and upper semicontinuity, and bounded
all-horizon Borel capacity. Length-zero paths are included.

`UniformEquilibrium/Quitting/Projective/RobustChargedRelationSmoothing.lean`
constructs a smooth function by one-sided convolution of the actual capacity.
`MathUE/Interval/RationalPolynomialChargedDrift.lean` constructs one native
rational polynomial from simultaneous derivative approximation, with full
charge-scaled endpoint drift. Its approximation dependencies include the
actual tensor Bernstein derivative construction and rational coefficient
approximation, not a supplied polynomial-existence premise.

`exists_quittingRobustChargedRelation_rationalPotential_of_finiteBudget`
(`UniformEquilibrium/Quitting/Projective/RobustChargedRelationPolynomialSeparator.lean`)
proves the floor-free separator. Its arbitrary-floor counterpart is
`exists_quittingFloorRobustChargedRelation_rationalPotential_of_finiteBudget`
(`UniformEquilibrium/Quitting/Projective/FloorRobustPolynomialSeparator.lean`).
Both quantify over every edge of the inner relation. The converse uses
telescoping and bounded oscillation, not extreme-value attainment for an
arbitrary bounded function.

`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
(`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`)
is the full stated no-uniform-payoff characterization: normal Fin4, a positive
singleton, the fixed reward box enlarged by two, no sure-quitter root at the
semantic punishment vector, and one rational polynomial at a positive rational
tolerance at most one quarter. The polynomial is constructed under no uniform
payoff, not accepted as an additional forward premise.

## Literal boundary examples

- Section 7.1: `UniformEquilibrium/Quitting/Root/AllContinueWeightedRoot.lean`
  gives the exact all-Continue defect and zero-charge relation, including
  failure after translating below a singleton reward.
- Section 7.2: `UniformEquilibrium/Quitting/Examples/ZeroRewardEntryFloor.lean`
  gives the actual below-floor entry and its concatenation with arbitrarily
  many charged loops. `UniformEquilibrium/Quitting/Examples/NonNormalFloorFailure.lean`
  computes the two-player punishment values and the constant exact-Nash
  all-Continue annotation violating the quarter floor. Its charge is zero.
- Section 7.3: `ThreeOwnerRobustCycle.no_potential`
  (`UniformEquilibrium/Quitting/Examples/ThreeOwnerRobustCycle.lean`) excludes
  every potential on the displayed exact charged three-cycle, with literal
  roots, successors, rewards, and all-player normality.
- Section 7.4: `SureRootNonrepeatability.suppliedProfile_exactTerminalNash`,
  `SureRootNonrepeatability.punishmentValue_eq_punishment`, and
  `SureRootNonrepeatability.owner_coordinateNashDefect_terminalValue`
  (`UniformEquilibrium/Quitting/Examples/SureRootNonrepeatability.lean`)
  give the actual unrestricted terminal Nash profile, semantic punishment
  computation, and strict one-eighth repeatability defect. The module also
  constructs the alternative constant exact source.

## Strengthenings and nonclaims

The analytic separator works in arbitrary finite coordinate dimension,
without normality, singleton-sign, or a reward-containing inner-box premise.
Floor vectors may be arbitrary real vectors. These strengthen the analytic
part only; they do not remove hypotheses from the semantic Fin4 equivalence.

`ThreeOwnerRobustCycle.exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Examples/ThreeOwnerRobustCycleUniformPayoff.lean`)
also makes the example's uniform-payoff existence a direct checked consequence
of the polynomial characterization. It does not select a numerical payoff.

There is no arbitrary-game positive producer, concrete negative polynomial,
degree bound, computation of the punishment vector, or new complete
certificate-checking algorithm. General finite-quitting UE remains open.

## Verification

The full `lake --quiet --iofail build`, including exhaustive axiom audit,
passed with zero output. Trust, import reachability, import-checker regression
tests, cross-lane proof duplication, redundant telescope hypotheses,
documentation, and whitespace checks passed. A subsequent independent Astra
read-only audit found no substantive Section 7 omission and checked that the
main implementations construct their advertised objects. That audit did not
run a separate build.
