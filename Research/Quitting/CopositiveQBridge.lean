/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.CopositiveQCorollaries
import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses

/-!
# Bridging the generic standard `Q` notion to the production one

`MathUE/LinearProgramming/CopositiveQ.lean` develops the textbook
nonhomogeneous LCP for its own `Prop`-valued solution predicate
`Math.LinearProgramming.IsStandardLCPSolution`, because the generic lane may
not import the game-semantic modules.  The production quitting lane spells out
the same three conditions in the same row convention
`(Mz) i = ∑ j, z j * M i j`, but packages a solution as data
(`GameTheory.QuittingLCPClassification.StandardLCPSolution`).

There is no convention mismatch: no transpose, no sign flip, and no
renormalization.  The two `Q` predicates are equivalent, and the conversion is
field-by-field.  The repository therefore carries three LCP solution notions —
the generic `Prop` structure, the production data structure, and the
simplex-normalized singleton form of `MathUE/LinearProgramming/SingletonLCP.lean`
— of which the first two are now formally identified here.

This file lives in `Research` rather than in either lane: `MathUE` may not
depend on `UniformEquilibrium`, and the production LCP umbrella is not the
place to land unintegrated work.

## Main results

* `isStandardQ_iff_isStandardQMatrix` — the `Q`-predicate bridge
* `isProjectiveQBarMatrix_tournamentSkewMatrix` — for `t > 1`, the
  skew-dominant matrix of an integral tournament is projective `Q̄`, i.e.
  projective `Q` on every nonempty principal submatrix
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The solution-level bridge -/

omit [DecidableEq ι] in
/-- A production solution packet is a generic solution at its weight vector. -/
theorem isStandardLCPSolution_weight {M : ι → ι → ℝ} {q : ι → ℝ}
    (solution : StandardLCPSolution M q) :
    IsStandardLCPSolution M q solution.weight :=
  ⟨solution.weight_nonneg, solution.residual_nonneg, solution.complementary⟩

omit [DecidableEq ι] in
/-- A generic solution packages into a production solution packet. -/
def standardLCPSolutionOfIsStandardLCPSolution {M : ι → ι → ℝ} {q z : ι → ℝ}
    (h : IsStandardLCPSolution M q z) : StandardLCPSolution M q where
  weight := z
  weight_nonneg := h.weight_nonneg
  residual_nonneg := h.residual_nonneg
  complementary := h.complementary

omit [DecidableEq ι] in
/-- The two solvability predicates for a fixed right-hand side agree. -/
theorem standardLCPSolvable_iff_hasStandardLCPSolution (M : ι → ι → ℝ) (q : ι → ℝ) :
    StandardLCPSolvable M q ↔ HasStandardLCPSolution M q := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨standardLCPSolutionOfIsStandardLCPSolution hz⟩
  · rintro ⟨solution⟩
    exact ⟨solution.weight, isStandardLCPSolution_weight solution⟩

omit [DecidableEq ι] in
/-- **The `Q`-predicate bridge.** The generic textbook `Q` predicate of
`CopositiveQ.lean` and the production textbook `Q` predicate of
`MatrixClasses.lean` are the same property.  Both quantify over all right-hand
sides in the row convention `(Mz) i = ∑ j, z j * M i j`; only the packaging of
a solution differs. -/
theorem isStandardQ_iff_isStandardQMatrix (M : ι → ι → ℝ) :
    IsStandardQ M ↔ IsStandardQMatrix M :=
  forall_congr' fun q => standardLCPSolvable_iff_hasStandardLCPSolution M q

/-! ## Family-level projective `Q̄` placement for integral tournaments -/

omit [DecidableEq ι] in
/-- Copositive `R₀` matrices are production standard `Q`, through the bridge. -/
theorem isStandardQMatrix_of_copositive_of_isR0Matrix (M : ι → ι → ℝ)
    (hcop : IsCopositive M) (hR0 : IsR0Matrix M) : IsStandardQMatrix M :=
  (isStandardQ_iff_isStandardQMatrix M).mp (copositive_isR0Matrix_isStandardQ M hcop hR0)

omit [Fintype ι] [DecidableEq ι] in
/-- **Integral tournaments are projective `Q̄`.** Fix `t > 1` and a `0/1`
fractional tournament `A`.  Every nonempty principal submatrix of
`tournamentSkewMatrix t A` is the skew-dominant matrix of the induced
subtournament, which is again a `0/1` fractional tournament.  In the
subtournament either every vertex has a unit out-neighbour, and the submatrix
is standard `Q` by `isStandardQ_tournamentSkewMatrix`, or some vertex loses to
every other member of the subset, and its unit vector is a homogeneous simplex
solution.  Either branch gives projective `Q` through the convention split
`isProjectiveQMatrix_iff_standard_or_homogeneous`.  A singleton subset falls in
the second branch, the diagonal entry being zero.

Integrality is essential: for a genuinely fractional tournament a vertex may
have outgoing weight without a unit out-neighbour, and then neither branch
applies. -/
theorem isProjectiveQBarMatrix_tournamentSkewMatrix (t : ℝ) (A : ι → ι → ℝ)
    (hA : IsIntegralTournament A) (ht : 1 < t) :
    IsProjectiveQBarMatrix (tournamentSkewMatrix t A) := by
  intro players _
  rw [isProjectiveQMatrix_iff_standard_or_homogeneous]
  have hsub := isStandardQ_or_singletonLCPFeasible_comp_of_isIntegralTournament t hA ht
    (Subtype.val : players → ι) Subtype.val_injective
  have hmat : (fun a b : players => tournamentSkewMatrix t A a.1 b.1) =
      principalMatrix (tournamentSkewMatrix t A) players := rfl
  rw [hmat] at hsub
  rcases hsub with h | h
  · exact Or.inl ((isStandardQ_iff_isStandardQMatrix _).mp h)
  · exact Or.inr h

omit [Fintype ι] [DecidableEq ι] in
/-- The same placement for any matrix that is presented as an integral
tournament's skew-dominant matrix, which is the form a quitting table's
`normalizedSoloMatrix` takes once it has been identified. -/
theorem isProjectiveQBarMatrix_of_eq_tournamentSkewMatrix {M : ι → ι → ℝ} (t : ℝ)
    (A : ι → ι → ℝ) (hA : IsIntegralTournament A) (ht : 1 < t)
    (hM : M = tournamentSkewMatrix t A) : IsProjectiveQBarMatrix M := by
  rw [hM]
  exact isProjectiveQBarMatrix_tournamentSkewMatrix t A hA ht

end QuittingLCPClassification
end GameTheory
