# Nonnegative inverse criterion beyond four players

## Checked theorem

`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse`
(`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`)
is integrated and passed the full silent build and axiom audit. A separate
declaration-level review verified
the determinant-sign transport, the threshold quantifiers, and selection of
one fixed payoff target for the original game.

For every natural number `n` with `3 ≤ n` and every quitting reward table
on `Fin n`, let its singleton comparison matrix be `M`. If `M.det < 0`
and every entry of `M⁻¹` is nonnegative, the original quitting game has a
uniform-equilibrium payoff. The payoff target is fixed before the accuracy;
all behavioral deviations and all sufficiently large horizons are covered.
No restrictions on own-singleton levels or nonsingleton rewards are added.

This extends the player-count scope of
`math/formalized/INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md`.
The source packet's four-player theorem is already checked; this additional
composition is not being attributed to the packet.

## Existing proof chain

1. For a strictly positive inverse, derive full R0 using
   `isR0Matrix_of_strictlyPositiveInverse`
   (`MathUE/LinearProgramming/PositiveInverseR0.lean`). Its positive-left-inverse
   proof is shared with the existing semantic homogeneous-solution theorem,
   which delegates through the canonical dictionary.
2. Apply `r0Degree_eq_sign_det_of_nonnegative_inverse`
   (`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`): the degree is
   minus one.
3. Apply `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one`
   (`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`).
   This theorem already covers arbitrary `Fin n`.
4. Approximate an entrywise nonnegative inverse by strictly positive inverses
   using `exists_pos_strictlyPositiveInverse_singletonMatrix_rewardApproximation`
   (`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseRewardApproximation.lean`).
   This is where `3 ≤ n` is used. The perturbation is a literal reward table
   and preserves determinant sign.
5. Use `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
   (`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`)
   to obtain one uniform payoff for the original table.

No arbitrary-player theorem deriving R0 from nonexistence is required.
Strict inverse positivity supplies R0 for the approximating games.
The interface makes no claim for a nonnegative determinant and
does not resolve arbitrary finite-player quitting games.

## Reuse in remaining degree packets

The stationary-response quotient and guarded crossed-response packets can
reuse the generic nonnegative-inverse degree computation even for quotient
matrices with nonzero diagonal. Canonical local/global degree comparison
and signed root sums are in `MathUE/LinearProgramming/R0Degree.lean` and
`MathUE/LinearProgramming/R0DegreeSum.lean`.
`hasFDerivAt_quittingDiscountedDisplacement_zero`
(`UniformEquilibrium/Quitting/Stationary/DiscountedAmbientDerivative.lean`)
supplies the ambient derivative.

Their response-invariant embedding or guarded permutation, clipped-map degree
comparison, and actual original-game adapter still need implementation.
A quotient matrix is not automatically the singleton matrix of a smaller
quitting game; the existing full-singleton criterion does not supply that
missing semantic connection.
