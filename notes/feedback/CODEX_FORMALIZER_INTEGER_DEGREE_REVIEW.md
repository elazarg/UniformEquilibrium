# Integer degree packet: scope audit and bounded proof mining

This is a static audit of
`math/formalized/INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md`
against its implemented declarations. No Lean or Lake command ran in this
review; the root agent owns the shared build queue. Compilation and checkpoint
status must come from that owner's checks. The suggestions below compose
existing APIs; they are not newly checked declarations.

## Endpoint coverage

The central endpoints match the source's substantive game claims:

- `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one`
  (`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`)
  accepts only the actual reward table, full singleton R0, and degree different
  from one. Its scope is every `Fin n`, including dimension zero.
- `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`)
  derives both full R0 and degree one from original-game nonexistence alone.
- `exists_uniformEquilibriumPayoff_of_finite_support_degree_test`
  (`UniformEquilibrium/Quitting/Classification/LCP/FiniteSupportDegreeCriterion.lean`)
  implements the finite test with any positive test anchor, for nonempty `Fin n`.
- `exists_uniformEquilibriumPayoff_of_negativeDegreeFourMatrix` and
  `eventually_exists_uniformEquilibriumPayoff_near_negativeDegreeFourMatrix`
  (`UniformEquilibrium/Quitting/Classification/LCP/NegativeDegreeFourMatrixCriterion.lean`)
  retain arbitrary own-singleton levels and nonsingleton rewards.
- `finFour_exists_uniformEquilibriumPayoff_of_nonnegative_inverse`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourNonnegativeInverseCriterion.lean`)
  allows zero inverse entries and derives R0 only in its contrary branch.

The final semantic predicate fixes its payoff before accuracy, chooses one
behavioral profile and threshold for each positive accuracy, and controls every
later horizon and every whole behavioral deviation. The definition was inspected
in `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform.lean`.
The canonical `quittingSingletonMatrix` has explicit `Matrix` result type in
`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`, so
the inverse criterion uses matrix inversion.

The all-fixed-point requirement survives the adapters:
`auxiliaryDiscounted_fixedPoint_scaled_sum_lt_of_no_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/AuxiliaryDiscountedQuantitativeLocalization.lean`)
chooses its radius and threshold before discount and before hazard. Its source
is original-game nonexistence and auxiliary full R0; the latter is transported
by literal singleton-matrix equality. The preceding localization theorem
completes a prescribed hazard cluster to a complete Bellman germ and invokes
the original-game auxiliary endpoint consumer. No normality, selected root,
test-anchor identification, or auxiliary nonexistence is silently supplied to
the public sufficient criterion.

The concrete file `MathUE/LinearProgramming/Examples/NegativeDegreeFourMatrix.lean`
contains the complete rational support inventory, degree minus one, standard Q,
positive determinant, mixed inverse signs, full noncopositivity, the zero-anchor
coordinate test, failed strict complementarity, and an infinite inhomogeneous
root set. The stability and comparison files preserve the advertised bounded
comparisons, including relabeling and positive row/column scaling exclusions.

## Exact limits of coverage

No missing main criterion or strategic adapter was found. The two minor
literal source assertions identified by the review are also proved:
`NegativeDegreeFourMatrixComparisons.cornerPrincipal_not_isCopositive`
(`UniformEquilibrium/Quitting/Classification/LCP/NegativeDegreeFourMatrixComparisons.lean`)
and `CycleFourNonnegativeInverse.exists_box_localDegree_at_allOnes_eq_neg_one`
(`MathUE/LinearProgramming/Examples/CycleFourNonnegativeInverse.lean`).
The latter is a local index, not an R0 degree: that matrix is not R0.
The completed declarations passed the root-owned full silent build, including
the production axiom audit.

The integer is the canonical signed box-complementarity degree defined by
`r0Degree` (`MathUE/LinearProgramming/R0Degree.lean`). The proof uses a common
positive scalar chart and checked signed-index properties. It does not supply
a separate identification with an externally defined Brouwer degree on every
bounded open neighborhood. Archive readiness for the implemented criterion is
therefore compatible with this explicit representation limit; a claim that
every abstract Brouwer-framework statement in the prose was formalized would
be too strong.

## Strongest bounded reuse opportunities

1. **Expose the already implemented player-count strengthening.** The raw
   R0/degree criterion and positive-anchor finite support criterion hold for
   every `Fin n`, not only four players. The source's final disclaimer about
   an unrestricted player-count theorem should distinguish this conditional
   matrix criterion from general UE existence. Bare nonexistence supplying
   full R0 remains a separate four-player endpoint here.

2. **General open cylinders from any strict inventory.** Compose
   `eventually_r0Degree_eq_of_strict_support_inventory`
   (`MathUE/LinearProgramming/SupportTestStability.lean`) with
   `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one`. Any zero-diagonal
   matrix with negative columns, nonsingular large principals, strict accepted
   and strictly rejected support tests, and degree different from one has a
   neighborhood whose literal singleton matrices all force UE, in every
   nonempty `Fin n`. The concrete negative-degree neighborhood is already this
   construction's special case. Strict rejection is essential to this API;
   accepted-root strictness alone is not its entire stability hypothesis.

3. **Nonnegative-inverse criterion in arbitrary dimension with an exact
   normality hypothesis.** For `Fin n`, combine all-player punishment normality
   with `isR0Matrix_quittingSingletonMatrix_of_normal_of_no_uniformPayoff`
   (`UniformEquilibrium/Quitting/Classification/LCP/PunishmentNormalR0.lean`),
   then `singleton_r0Degree_eq_one_of_no_uniformPayoff` and
   `r0Degree_eq_sign_det_of_nonnegative_inverse`
   (`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`). A negative
   determinant and entrywise nonnegative inverse force original UE under that
   normality hypothesis. Alternatively full R0 can be supplied directly and
   normality omitted. The Fin4 theorem already eliminates both extra premises
   through its stronger contrary-source adapter.

4. **A finite signed-count obstruction for counterexample searches.** Combine
   the Fin4 degree-one necessity with
   `r0Degree_eq_sum_admissible_inverse_supports`
   (`MathUE/LinearProgramming/FiniteSupportDegree.lean`). Whenever the finite
   tests apply, original noUE forces the complete support sign sum to equal
   one. Equivalently, since all included determinants are nonzero, the number
   of positive-index admissible supports is one greater than the number of
   negative-index supports. This refines an odd-parity filter and gives an
   exact rejection rule for candidate matrices without identifying the test
   anchor with any actual punishment anchor. The count wrapper is not yet a
   named checked declaration.
