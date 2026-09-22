import MathUE.LinearProgramming.LocalAffine
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card

/-!
# Uniqueness by support and finiteness of regular LCP solutions

Every standard LCP solution satisfies its selected-row linear system.
Solutions with the same positive support therefore coincide when that
support's principal matrix is nonsingular. If this nonsingularity holds at
every actual solution, positive support injects the solution set into the
finite set of coordinate subsets.

No strict-complementarity or R0 assumption is needed. Empty support and
dimension zero are included; the selected inactive block is the identity.
-/

noncomputable section

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A standard LCP solution satisfies the actual selected-row linear system. -/
theorem IsStandardLCPSolution.selectedMatrix_mulVec_eq
    {matrix : Matrix ι ι ℝ} {offset root : ι → ℝ}
    (hroot : IsStandardLCPSolution matrix offset root) :
    (lcpSelectedMatrix matrix root).mulVec root =
      fun who => if 0 < root who then -offset who else 0 := by
  classical
  funext who
  rw [lcpSelectedMatrix_mulVec]
  by_cases hactive : 0 < root who
  · simp only [ite_eq_left hactive]
    have hresidual : lcpResidual matrix offset root who = 0 :=
      (mul_eq_zero.mp (hroot.complementary who)).resolve_left hactive.ne'
    have hequal := congrFun (lcpResidual_eq_add_mulVec matrix offset root) who
    simp only [Pi.add_apply] at hequal
    linarith
  · simp only [ite_eq_right hactive]
    exact le_antisymm (le_of_not_gt hactive) (hroot.weight_nonneg who)

/-- Equal positive supports determine equal solutions when their active
principal matrix is nonsingular. No strict inactive slack is required. -/
theorem IsStandardLCPSolution.eq_of_positive_support_eq
    {matrix : Matrix ι ι ℝ} {offset first second : ι → ℝ}
    (hfirst : IsStandardLCPSolution matrix offset first)
    (hsecond : IsStandardLCPSolution matrix offset second)
    (hsupport : ∀ who, 0 < first who ↔ 0 < second who)
    (hnonsingular : (matrix.toSquareBlockProp (fun who => 0 < first who)).det ≠ 0) :
    first = second := by
  classical
  have hmatrix : lcpSelectedMatrix matrix first = lcpSelectedMatrix matrix second := by
    ext who coordinate
    simp only [lcpSelectedMatrix, hsupport who]
  have hvalues : (lcpSelectedMatrix matrix first).mulVec first =
      (lcpSelectedMatrix matrix first).mulVec second := by
    rw [hfirst.selectedMatrix_mulVec_eq, hmatrix, hsecond.selectedMatrix_mulVec_eq]
    funext who
    simp only [hsupport who]
  have hselected : (lcpSelectedMatrix matrix first).det ≠ 0 := by
    intro hzero
    exact hnonsingular ((det_lcpSelectedMatrix matrix first).symm.trans hzero)
  have hinjective : Function.Injective (lcpSelectedMatrix matrix first).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hselected))
  exact hinjective hvalues

private theorem nonsingularStandardLCPSolutions_support_injOn
    (matrix : Matrix ι ι ℝ) (offset : ι → ℝ) :
    Set.InjOn (fun root => Finset.univ.filter (fun who => 0 < root who))
      {root | IsStandardLCPSolution matrix offset root ∧
        (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0} := by
  classical
  intro first hfirst second hsecond hequal
  apply hfirst.1.eq_of_positive_support_eq hsecond.1 _ hfirst.2
  intro who
  have hmem := Finset.ext_iff.mp hequal who
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem

/-- The solutions with nonsingular active principal matrix form a finite set,
without any restriction on the other solutions. -/
theorem finite_nonsingularStandardLCPSolutions
    (matrix : Matrix ι ι ℝ) (offset : ι → ℝ) :
    {root | IsStandardLCPSolution matrix offset root ∧
      (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0}.Finite := by
  classical
  exact Set.Finite.of_injOn (fun _ _ => Set.mem_univ _)
    (nonsingularStandardLCPSolutions_support_injOn matrix offset)
    (Set.toFinite (Set.univ : Set (Finset ι)))

/-- There is at most one nonsingular standard-LCP root per coordinate subset. -/
theorem ncard_nonsingularStandardLCPSolutions_le_two_pow
    (matrix : Matrix ι ι ℝ) (offset : ι → ℝ) :
    {root | IsStandardLCPSolution matrix offset root ∧
      (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0}.ncard ≤
        2 ^ Fintype.card ι := by
  classical
  have hbound := Set.ncard_le_ncard_of_injOn (t := Set.univ)
    _ (fun _ _ => Set.mem_univ _)
    (nonsingularStandardLCPSolutions_support_injOn matrix offset)
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_finset] using hbound

/-- Nonsingularity of every actual solution's active principal matrix makes
the complete standard-LCP solution set finite. -/
theorem finite_standardLCPSolutions_of_nonsingular_active_principals
    (matrix : Matrix ι ι ℝ) (offset : ι → ℝ)
    (hnonsingular : ∀ root, IsStandardLCPSolution matrix offset root →
      (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0) :
    {root | IsStandardLCPSolution matrix offset root}.Finite :=
  (finite_nonsingularStandardLCPSolutions matrix offset).subset
    (fun root hroot => ⟨hroot, hnonsingular root hroot⟩)

/-- The finite solution set has at most one root per coordinate subset. -/
theorem ncard_standardLCPSolutions_le_two_pow
    (matrix : Matrix ι ι ℝ) (offset : ι → ℝ)
    (hnonsingular : ∀ root, IsStandardLCPSolution matrix offset root →
      (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0) :
    {root | IsStandardLCPSolution matrix offset root}.ncard ≤ 2 ^ Fintype.card ι := by
  have hsubset : {root | IsStandardLCPSolution matrix offset root} ⊆
      {root | IsStandardLCPSolution matrix offset root ∧
        (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0} :=
    fun root hroot => ⟨hroot, hnonsingular root hroot⟩
  exact (Set.ncard_le_ncard hsubset
    (finite_nonsingularStandardLCPSolutions matrix offset)).trans
      (ncard_nonsingularStandardLCPSolutions_le_two_pow matrix offset)

end Math.LinearProgramming
