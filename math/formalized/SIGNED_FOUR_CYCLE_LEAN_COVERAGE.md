# Signed four-cycle Lean coverage

The useful stated content of
`HETEROGENEOUS_SIGNED_SINGLETON_FOUR_CYCLE_PRODUCER.md` is covered by the
declarations below. The frozen packet was moved unchanged from `exports/`.
Its SHA-256 before and after the move is
`8dabb5e019ed9542f76058b1ae34919791c510117226e1cdae3cf0de5b1d9e33`.

## Actual source and conclusions

- `SignedFourCycleSingletonData` and
  `weighted_singleton_comparison_balances`
  (`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`)
  compute the signed comparison coefficients and balance equations from the
  actual reward table. No equilibrium or cycle is a source field.
- `SignedFourCycleCoefficients` in `MathUE/SignedFourCycleAlgebra.lean` and
  `SignedFourCycleStrictData` in `MathUE/SignedFourCycleWeights.lean` supply
  the characteristic identity, smaller eigenvalue, positive weights, tails,
  hazards, reconstruction identities, and survival product.
- `targetValue` and `coarse_bellman`
  (`UniformEquilibrium/Quitting/Cycles/SignedFourCycleValues.lean`) give the
  literal resolvent target and rotated values.
- `next_coarse_owner_eq`, `coarse_soloFloor`, `certificate`, and
  `targetValue_isUniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Cycles/SignedFourCycleCertificate.lean`)
  construct the actual certificate and prove its computed fixed target is a
  uniform-equilibrium payoff against unrestricted behavioral deviations.
- `hasFiniteMenuFullEarlyAbsorption`
  (`UniformEquilibrium/Quitting/Cycles/SignedFourCycleFiniteEarlyAbsorption.lean`)
  retains the exact requested error, terminal window, survival bound, and
  lower-deadline quantifiers. Its output has small unrestricted terminal
  exploitability, not merely displayed-menu regret.

Own singleton levels and nonsingleton rewards have arbitrary real signs.
The generic finite-output proof is
`finiteMenuFullEarlyAbsorption_of_terminalProfiles_liveMassZero`
(`UniformEquilibrium/Quitting/Terminal/TerminalProfileFiniteEarlyAbsorption.lean`).

## Fixtures and open class

The Diagnostics files `SignedFourCycleMatrixFixtures.lean`,
`SignedFourCycleRawSpectralFixtures.lean`, and
`SignedFourCycleValueFixtures.lean` under
`UniformEquilibrium/Diagnostics/Quitting/` check the three rational tables,
positive inverses, matrix classifications, smaller-root data, exact hazards,
coarse values, and rejection of the larger root.

`coarse_profile_not_exactNash`
(`UniformEquilibrium/Diagnostics/Quitting/SignedFourCycleCoarseNonNash.lean`)
uses an actual behavioral deviation earning two instead of one. It concerns
the coarse profile, not the refined equilibrium construction.

`isOpen_hasSignedFourCycleStrictTests`
(`MathUE/SignedFourCycleStrictOpenness.lean`) proves openness of the raw tests.
`ofSingletonMatrixStrictTests` and `ofSingletonMatrixStrictTests_strictTests`
(`UniformEquilibrium/Quitting/Cycles/SignedFourCycleStrictSourceBridge.lean`)
construct actual source data in the reverse direction.

`exists_relative_open_uniformPayoff_neighborhood`
(`UniformEquilibrium/Diagnostics/Quitting/SignedFourCycleNeighborhood.lean`)
combines the twelve-coordinate neighborhood, full normal core, standard-Q,
absence of a homogeneous simplex solution, failure of projective-Q-bar,
noncyclicity under positive row scaling and relabeling, and actual reward-table
production of the fixed UE target and full finite early absorption.
`exists_common_open_matrix_regime_neighborhood`
(`UniformEquilibrium/Diagnostics/Quitting/SignedFourCycleMatrixRegimeOpenness.lean`)
also covers both heterogeneous fixtures' matrix regimes.

## Coverage boundaries and verification

The strict floor consequences of the packet's formula (11) are named public
theorems; its exact quotient expressions are not separately named equalities.
Exact determinant numerals and internal mesh/censor counters are not exposed:
checked inverse identities and the headline finite-output quantifiers cover
their uses. These are proof-presentation differences, not weakened headline
conclusions.

The packet does not establish arbitrary Fin4 existence, exact coarse Nash,
or a positive terminal-gap source. None is asserted by this formalization.

All listed modules are integrated and included in the exhaustive axiom audit.
The final full `lake --quiet --iofail build` passed with zero diagnostics.
Trust, import-graph, documentation, duplicate-proof, redundant-hypothesis,
and whitespace checks passed. The core certificate and relevant source
interfaces also received independent semantic reviews.
