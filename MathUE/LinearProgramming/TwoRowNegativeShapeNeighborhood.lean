import MathUE.LinearProgramming.RowNegativeShape
import Mathlib.Topology.Instances.Matrix

noncomputable section

namespace Math.LinearProgramming

def ZeroDiagonalFourMatrix :=
  {M : Matrix (Fin 4) (Fin 4) ℝ // ∀ i, M i i = 0}

instance : TopologicalSpace ZeroDiagonalFourMatrix :=
  inferInstanceAs (TopologicalSpace
    {M : Matrix (Fin 4) (Fin 4) ℝ // ∀ i, M i i = 0})

def twoRowNegativeShapeGap (M : ZeroDiagonalFourMatrix) : ℝ :=
  (M.1 0 1 + M.1 0 2) ^ 2 * ((M.1 1 2) ^ 2 + (M.1 1 3) ^ 2) -
    (M.1 1 2 + M.1 1 3) ^ 2 * ((M.1 0 1) ^ 2 + (M.1 0 2) ^ 2)

/-- A relative neighborhood where the first two rows retain fixed negative supports
and have distinct scale-invariant negative-entry shapes. -/
def InTwoRowNegativeShapeNeighborhood (M : ZeroDiagonalFourMatrix) : Prop :=
  M.1 0 1 < 0 ∧ M.1 0 2 < 0 ∧ 0 < M.1 0 3 ∧
    0 < M.1 1 0 ∧ M.1 1 2 < 0 ∧ M.1 1 3 < 0 ∧
      twoRowNegativeShapeGap M ≠ 0

theorem inTwoRowNegativeShapeNeighborhood_not_uniform
    {M : ZeroDiagonalFourMatrix} (h : InTwoRowNegativeShapeNeighborhood M) :
    ¬HasUniformNegativeRowShape M.1 := by
  intro huniform
  have h01 := huniform 0 1
  rcases h with ⟨h01n, h02n, h03p, h10p, h12n, h13n, hgap⟩
  have hn0 : negativeColumns M.1 0 = {1, 2} := by
    ext j
    fin_cases j <;> simp [negativeColumns, M.2, h01n, h02n, h03p.le]
  have hn1 : negativeColumns M.1 1 = {2, 3} := by
    ext j
    fin_cases j <;> simp [negativeColumns, M.2, h10p.le, h12n, h13n]
  simp only [negativeRowSum, negativeRowSquareSum, hn0, hn1] at h01
  simp at h01
  exact hgap (sub_eq_zero.mpr h01)

theorem inTwoRowNegativeShapeNeighborhood_not_scaledRelabelingCirculant
    {M : ZeroDiagonalFourMatrix} (h : InTwoRowNegativeShapeNeighborhood M) :
    ¬IsPositiveRowScaledRelabelingRowCirculant M.1 := by
  intro hscaled
  exact inTwoRowNegativeShapeNeighborhood_not_uniform h
    (hasUniformNegativeRowShape_of_positiveRowScaledRelabelingRowCirculant hscaled)

theorem isOpen_inTwoRowNegativeShapeNeighborhood :
    IsOpen {M : ZeroDiagonalFourMatrix | InTwoRowNegativeShapeNeighborhood M} := by
  rw [isOpen_iff_mem_nhds]
  intro M h
  rcases h with ⟨h01, h02, h03, h10, h12, h13, hgap⟩
  have centry (i j : Fin 4) :
      ContinuousAt (fun N : ZeroDiagonalFourMatrix ↦ N.1 i j) M :=
    ((continuous_apply_apply i j).comp continuous_subtype_val).continuousAt
  have cgap : ContinuousAt twoRowNegativeShapeGap M := by
    unfold twoRowNegativeShapeGap
    exact (((centry 0 1).add (centry 0 2)).pow 2).mul
      (((centry 1 2).pow 2).add ((centry 1 3).pow 2)) |>.sub
        ((((centry 1 2).add (centry 1 3)).pow 2).mul
          (((centry 0 1).pow 2).add ((centry 0 2).pow 2)))
  have egap : ∀ᶠ N in nhds M, twoRowNegativeShapeGap N ≠ 0 :=
    cgap.eventually (isOpen_compl_singleton.mem_nhds hgap)
  filter_upwards [(centry 0 1).eventually_lt_const h01,
    (centry 0 2).eventually_lt_const h02,
    (centry 0 3).eventually_const_lt h03,
    (centry 1 0).eventually_const_lt h10,
    (centry 1 2).eventually_lt_const h12,
    (centry 1 3).eventually_lt_const h13, egap] with
      N hn01 hn02 hn03 hn10 hn12 hn13 hngap
  exact ⟨hn01, hn02, hn03, hn10, hn12, hn13, hngap⟩

end Math.LinearProgramming
