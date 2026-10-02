# Geometric pivot compression and exact repair: Lean coverage

Packet: `GEOMETRIC_PIVOT_TAIL_COMPRESSION_AND_EXACT_REPAIR_LP.md`.
Frozen SHA-256:
`238b7bd0b75dd367d1ae4d09845e1ba4e47b26435a2a2b416223668ea38fd13d`.
Integrated checkpoint: `eb41e93`.

Paths below are relative to the project root. The packet is preserved byte
for byte. Its original statements about not yet being Lean-checked describe
the export's preparation, not this subsequent coverage record.

## Actual geometric compression

`exists_geometric_pivot_payoff_eq_and_caps_le`
(`UniformEquilibrium/Quitting/Terminal/GeometricPivotCapDomination.lean`)
constructs a replacement of an arbitrary complete pivot stopping law against
fixed finite opponent laws. It preserves the prescribed payoff vector and
weakly lowers every unrestricted behavioral cap. The same module's
`quittingIndependentTerminalOutcomeLaw_geometric_pivot_eq` preserves the
labelled outcome law, including Never. The pivot cap is unchanged by its own
replacement. Head atoms, Never mass, the zero-tail case, and the geometric
component are handled in `MathUE/ProbabilityMassFunction/GeometricPivotStoppingLaw.lean`.

The signed response formula and its actual early contribution are in
`UniformEquilibrium/Quitting/Terminal/FiniteOpponentPivotResponseFormula.lean`.
The three late endpoints remain necessary for arbitrary signed singleton
rewards; no positive survival denominator is assumed.

## Exact finite optimization and behavioral infimum

`QuittingPivotRepairLPInput` in
`UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean` stores actual
finite opponent laws and computes the coefficients from them. Its
`exists_objective_minimizer` proves compact feasible-mass attainment.
`constraintGain_affine` in the companion `PivotRepairFiniteLPBoundary.lean`
proves the finite affine constraint surface.

`exists_objective_minimizer_eq_behavioral_infimum`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`)
identifies that minimum with the infimum over every behavioral pivot strategy.
It uses actual source compression and actual approximation of the boundary,
not a field assuming the desired equality. `geometric_exploitability_eq_objective`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairExactObjective.lean`)
gives exact realization when the first geometric atom matches the mass data.

`exists_law_boundary_approximation_of_reward_bound`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralApproximation.lean`)
preserves the payoff vector and Never atom while controlling the boundary
error by twice the reward bound times the first-atom perturbation.
The zero-nonpivot-singleton specialization removes the factor two.
An attained LP optimizer is not asserted to be an attained behavioral optimum.

`exists_rationalAffineConstraintFunctional_of_actual_source`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairRationalCoefficients.lean`)
constructs the exact rational affine constraints when the actual reward entries
and finite opponent atoms are rational. It does not select those opponents.

## Finite-menu consumer and outer source

`exists_finite_menu_of_feasible_mass_signed_of_reward_bound`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteMenuConsumer.lean`)
retains the actual censored laws, Never mass, finite deadline, arbitrary
terminal window, full-exploitability estimate with censor cost `4*M*β`, and
literal survival identity. Its positive-pivot-singleton specialization also
bounds survival by the LP value divided by that singleton, plus the censored
mass. The reward-bound and zero-tail edge cases are included.

`singlePivotFiniteMenuScalarSource_iff_smallPivotRepairValue` and
`singlePivotFiniteMenuScalarSource_iff_fullEarlyAbsorption`
(`UniformEquilibrium/Quitting/Terminal/SinglePivotRepairSourceEquivalence.lean`)
prove the canonical source equivalences. The two-endpoint simplification is
in the same module. The stronger signed, arbitrary-pivot theorem
`smallPivotRepairValue_iff_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairUniformPayoffCharacterization.lean`)
identifies the actual small-inner-value source with existence of one fixed
uniform-equilibrium payoff. Neither direction supplies that source for an
arbitrary game.

## Boundary examples and rational repair

`behavioral_repair_infimum_zero_not_attained`
(`UniformEquilibrium/Diagnostics/Quitting/PivotRepairNonattainedAllLaws.lean`)
proves the packet's explicit nonattainment example against every behavioral
pivot strategy. The zero LP point is in `PivotRepairNonattainedZeroLP.lean`.
`third_endpoint_strictly_needed` in `PivotRepairSignedThirdEndpoint.lean`
proves the signed endpoint obstruction from the actual two-player table.
The zero-reward payoff and exploitability boundary is independently covered
by `zero_terminalPayoff` and `zero_terminalExploitability` in
`UniformEquilibrium/Diagnostics/Quitting/FiniteMenuSignedZeroBoundaryRegression.lean`.

The rational table and actual opponent laws are in
`UniformEquilibrium/Diagnostics/Quitting/PivotRepairRationalFixture.lean`.
The lower-bound module proves the inequality for every feasible mass;
the response-coefficient module computes the actual branch coefficients.
`optimizerGeometric_payoff`, `optimizerGeometric_cap`, and
`optimizerGeometric_debt` (`PivotRepairRationalOptimizer.lean`) expose all
four coordinates of the actual geometric profile. Its exploitability is
exactly `1584/5243`.

`exploitability_ge_1584_div_5243_of_pivotBehavior` and
`pivotBehavior_exploitability_infimum_eq` (`PivotRepairRationalOptimality.lean`)
state the unrestricted behavioral lower bound and exact infimum literally;
`optimizerPivotBehavior_exploitability_eq` supplies the attaining strategy.

`afterOneProfile_eq_update_optimizer` and `afterTwoProfile_eq_update_afterOne`
(`PivotRepairRationalSequentialReplacement.lean`) identify the two actual
Never replacements. Each is proved to attain its player's full behavioral
cap. The final actual payoff and cap vectors are both `(1,7,7,0)`;
`afterTwo_isExactTerminalNash` proves zero-error terminal Nash. These modules
all reside in `UniformEquilibrium/Diagnostics/Quitting/` and are included in
the exhaustive project axiom audit.

## Scope and verification

The results cover arbitrary finite players and signed rewards for compression
and inner optimization. Positive pivot singleton reward is used for the
LP-based survival bound; zero nonpivot singleton rewards justify only the
two-endpoint simplification. The outer opponent selection is not proved
convex, attained, or arbitrarily small. The numerical replacements establish
one example, not convergence of an iterative repair algorithm.

After integration the full `lake --quiet --iofail build` passed with zero
output, including the exhaustive axiom audit. Trust, import-graph,
documentation, cross-lane proof-duplicate, redundant-hypothesis, and whitespace
checks passed. The production proofs and literal source/consumer interfaces
were reviewed separately from the frozen mathematical export.
