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

## Independent results still to formalize

1. **Strict inverse approximation.** In dimension at least three, subtracting
   a sufficiently small positive multiple of the off-diagonal all-ones matrix
   from an invertible matrix with nonnegative inverse preserves the diagonal
   and determinant sign and makes the inverse strictly positive. This matrix
   result does not need a zero-diagonal premise.
   `isOpen_hasStrictlyPositiveInverse`
   (`MathUE/LinearProgramming/PositiveInverseOpenness.lean`) proves openness,
   not this density statement. Reuse `offDiagonalOnes`
   (`MathUE/LinearAlgebra/UniformNonsingularity.lean`).

2. **Approximation boundaries.** Prove the zero-diagonal two-dimensional
   obstruction. Extend the existing four-cycle example in
   `MathUE/LinearProgramming/Examples/CycleFourNonnegativeInverse.lean`
   with the packet's perturbation of size one twentieth, exact inverse, and
   second-order positivity calculation. The unperturbed determinant,
   nonnegative inverse, unique regular test root, and failure of R0 are
   already proved.

3. **Distinct arithmetic and class-comparison examples.** Add the
   determinant-minus-three and determinant-forty-five matrices with their
   positive inverses. For the former, retain the zero-coordinate anchor,
   non-projective-Q principal, failure of projective Q-bar, full normal core,
   and absence of relabeled negative Hamiltonian cycles. Also retain the
   displayed covering walk with repeated owners: the packet does not exclude
   longer calendars. Reuse `isStandardQMatrix_of_positive_rightInverse` and
   `noHomogeneousSimplexSolution_of_positive_leftInverse`
   (`UniformEquilibrium/Quitting/Classification/LCP/PositiveInverse.lean`).

4. **Localization counterexample.** Define the additive coalition completion,
   compute its actual discounted displacement, certify the displayed small
   interior fixed point and the remote fixed points with at least two sure
   quitters, and prove the all-sure profile's exact terminal Nash property.
   Reuse `quittingDiscountedClippedMap_eq_self_iff`
   (`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`).
   This is the literal regression against deriving global localization from
   the matrix hypotheses alone.

5. **Literal reward perturbation.** After the matrix approximation theorem,
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
