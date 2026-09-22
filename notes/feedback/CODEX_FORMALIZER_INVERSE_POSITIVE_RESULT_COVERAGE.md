# Inverse-positive packet: result coverage

Source:
`math/formalized/INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md`.
This records independent result coverage and identifies intermediate proof
steps superseded by the stronger degree argument. It does not assert a
line-by-line formalization of the packet's proof.
The result modules passed the full silent build and exhaustive production
axiom audit. A separate declaration-level review found no remaining
independent game conclusion or boundary example in the packet.

## Reuse the stronger checked endpoint

`finFour_exists_uniformEquilibriumPayoff_of_nonnegative_inverse`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourNonnegativeInverseCriterion.lean`)
already proves the packet's raw four-player existence criterion, including
zero inverse entries. Its degree proof replaces the packet's strict-core
implicit-function and index route; that alternative proof need not be
reconstructed solely for its provenance.

The useful universal localization results are already proved, not merely
bypassed. `tendsto_hazard_zero_of_no_uniformEquilibriumPayoff` and
`auxiliaryDiscounted_fixedPoint_sum_lt_of_no_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/AuxiliaryDiscountedLocalization.lean`)
use the actual auxiliary table of the original game under original-game
nonexistence. Their threshold controls every fixed point.
`finFour_auxiliaryDiscounted_fixedPoint_scaled_sum_lt_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`)
gives a uniform bound on hazard divided by discount, without inverse positivity.
`tendstoUniformlyOn_quittingDiscountedDisplacement_scaled`
(`UniformEquilibrium/Quitting/Stationary/DiscountedUniformScaling.lean`)
separately proves the affine first-order displacement limit uniformly on
bounded sets of signed hazards. These do not assert the exact asymptotic
of every fixed point.

The reward-transport results are also available:
`abs_quittingContinuationBestResponseValue_sub_le_of_reward_close`,
`abs_quittingTerminalExploitability_sub_le_of_reward_close`, and
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
(`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`).
They control the full behavioral cap, exploitability, and existence under
reward-table limits. No new payoff-continuity or deviation-cap argument is
needed.

## Checked approximation and its boundaries

The generic strict approximation is proved by
`exists_pos_strictlyPositiveInverse_sub_offDiagonalOnes`
(`MathUE/LinearProgramming/NonnegativeInverseApproximation.lean`). For every
finite coordinate type of cardinality at least three, it chooses one positive
threshold before all positive perturbations below that threshold. The actual
matrix inverse is strictly positive, its determinant sign is preserved, and
its diagonal is unchanged. The original diagonal need not vanish.
The proof reuses Mathlib's Neumann series and the canonical `offDiagonalOnes`;
`first_or_second_inverse_correction_pos` in the same file proves the entrywise
coverage by the first two correction terms. This module passed a silent named
build. It is distinct from mere openness of the strictly positive class.

The same module proves the two-dimensional obstruction by
`not_hasStrictlyPositiveInverse_fin_two_of_diagonal_zero`. Its inverse-diagonal
identity also covers singular matrices under the matrix-inverse convention.

`CycleFourNonnegativeInverse.perturbedMatrix_inverse_eq`,
`CycleFourNonnegativeInverse.perturbedMatrix_det_neg`,
`CycleFourNonnegativeInverse.opposite_entries_inverse_and_first_correction_eq_zero`,
and `CycleFourNonnegativeInverse.inverse_add_first_add_second_correction_pos`
(`MathUE/LinearProgramming/Examples/CycleFourNonnegativeInverse.lean`)
cover the explicit perturbation by one twentieth and the second-order boundary
test. This module and its approximation dependency passed a silent named build.

## Checked class comparisons and reward adapter

The two exact matrices, their determinants and positive inverses, and the
zero-coordinate anchor calculation are proved in
`MathUE/LinearProgramming/Examples/PositiveInverseFourMatrices.lean`.
The namespaces `PositiveInverseFourMatrices.NegativeDeterminant` and
`PositiveInverseFourMatrices.Paired` separate the two fixtures. This module
passed a silent named build. Its negative-graph results exclude relabeled
negative Hamiltonian cycles and supply the displayed covering six-edge walk
with repeated owners.

`UniformEquilibrium/Quitting/Classification/LCP/PositiveInverseFourMatrixComparisons.lean`
proves the full matrix standard Q, its homogeneous obstruction, the
non-projective-Q principal on players zero, one, and three, failure of
projective Q-bar, and full normal core. Its
`not_nonempty_signedFourCycleSingletonData_of_reindex` excludes the named
once-per-owner cycle input under every relabeling, not longer calendars.
`paired_r0Degree_eq_one` gives the positive-determinant example's canonical
degree. This module passed a silent named build.

`exists_pos_strictlyPositiveInverse_singletonMatrix_rewardApproximation`
(`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseRewardApproximation.lean`)
realizes the approximation by literal reward tables. The same module proves
the exact matrix identity, preservation of own-singleton and nonsingleton
coordinates, and the entrywise reward-distance bound. One positive threshold
works for every smaller positive perturbation. It passed a silent named build.
The existing reward-limit theorem supplies its semantic consumer.

## Checked localization counterexample

`UniformEquilibrium/Quitting/Classification/LCP/AdditiveCoalitionLocalizationCounterexample.lean`
defines the literal additive reward completion.
`quittingDiscountedDisplacement_eq` factors its actual polynomial displacement.
`quittingDiscountedClippedMap_smallHazard` certifies the displayed interior
fixed point, and `quittingDiscountedClippedMap_eq_self_of_two_sure` supplies
every cube hazard with two distinct sure quitters at every discount parameter.
`allQuit_terminalNash` controls unrestricted behavioral deviations at the
all-sure stationary profile. The module passed a silent named build. This
refutes localization from matrix assumptions alone, not uniform-equilibrium
existence.

## Superseded proof steps

The packet's exact all-root asymptotic (hazard divided by discount converges
to inverse matrix times anchor) and eventual unique interior fixed point are
not represented by located declarations. Under the packet's full hypotheses
they are steps in the replaced contradiction proof, not separate missing
game conclusions. The uniform bound above does not prove that exact limit.
A determinant-free formulation under independently supplied localization
would be an additional reusable interface, including positive-determinant
cases, not a dependency of the raw existence theorem already proved.
