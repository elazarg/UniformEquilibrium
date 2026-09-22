# Inverse-positive packet: remaining result coverage

Source:
`math/exports/INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md`.
This is a declaration-level dependency audit, not a completion record. The
remaining items below are results supplied by the packet, not requests for
new mathematics.

## Reuse the stronger checked endpoint

`finFour_exists_uniformEquilibriumPayoff_of_nonnegative_inverse`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourNonnegativeInverseCriterion.lean`)
already proves the packet's raw four-player existence criterion, including
zero inverse entries. Its degree proof replaces the packet's strict-core
implicit-function and index route; that alternative proof need not be
reconstructed solely for its provenance.

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

## Independent results still to formalize

The two exact matrices, their determinants and positive inverses, and the
zero-coordinate anchor calculation are proved in
`MathUE/LinearProgramming/Examples/PositiveInverseFourMatrices.lean`.
The namespaces `PositiveInverseFourMatrices.NegativeDeterminant` and
`PositiveInverseFourMatrices.Paired` separate the two fixtures. This module
passed a silent named build; it makes no strategic or class-comparison claim.

1. **Class-comparison examples.** For the determinant-minus-three matrix,
   retain the non-projective-Q principal, failure of projective Q-bar, full normal core,
   and absence of relabeled negative Hamiltonian cycles. Also retain the
   displayed covering walk with repeated owners: the packet does not exclude
   longer calendars. Reuse `isStandardQMatrix_of_positive_rightInverse` and
   `noHomogeneousSimplexSolution_of_positive_leftInverse`
   (`UniformEquilibrium/Quitting/Classification/LCP/PositiveInverse.lean`).

2. **Localization counterexample.** Define the additive coalition completion,
   compute its actual discounted displacement, certify the displayed small
   interior fixed point and the remote fixed points with at least two sure
   quitters, and prove the all-sure profile's exact terminal Nash property.
   Reuse `quittingDiscountedClippedMap_eq_self_iff`
   (`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`).
   This is the literal regression against deriving global localization from
   the matrix hypotheses alone.

3. **Literal reward perturbation.** Using the matrix approximation theorem,
   prove that subtracting the same amount from every off-own singleton
   coordinate gives precisely the stated matrix perturbation, preserves all
   own-singleton and nonsingleton coordinates, and has the stated reward
   distance. The existing reward-limit theorem is its consumer; a second
   proof of the main existence criterion adds no result coverage.

The strict-inverse limit and eventual interior-branch uniqueness used only
inside the packet's contrary no-equilibrium proof are not separate missing
game conclusions. A reusable formulation under independently supplied
localization would be an additional interface, not a dependency of the raw
existence theorem already proved.
