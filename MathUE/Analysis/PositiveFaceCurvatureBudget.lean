import MathUE.Analysis.HessianConvexification
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Lattice.Fold

/-! # The exact positive-column curvature budget in face convexification -/

noncomputable section

namespace Math

open Set
open scoped BigOperators RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def positiveFaceCurvatureBudget (matrix : ι → ι → ℝ) : ℝ :=
  (1 / 4) * Finset.univ.sup' Finset.univ_nonempty
    (fun owner => ∑ receiver ∈ Finset.univ.erase owner, (max (matrix receiver owner) 0) ^ 2)

theorem positiveFaceCurvatureBudget_pos_of_positive_entry
    (matrix : ι → ι → ℝ) (hdiagonal : ∀ who, matrix who who = 0)
    (receiver owner : ι) (hentry : 0 < matrix receiver owner) :
    0 < positiveFaceCurvatureBudget matrix := by
  have hne : receiver ≠ owner := by
    intro heq
    subst receiver
    rw [hdiagonal owner] at hentry
    exact (lt_irrefl 0) hentry
  have hsum : 0 < ∑ other ∈ Finset.univ.erase owner,
      (max (matrix other owner) 0) ^ 2 := by
    apply lt_of_lt_of_le (sq_pos_of_pos (lt_of_lt_of_le hentry (le_max_left _ _)))
    exact Finset.single_le_sum
      (f := fun other : ι => (max (matrix other owner) 0) ^ 2)
      (fun _ _ => sq_nonneg _)
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ receiver⟩)
  apply mul_pos (by norm_num)
  exact hsum.trans_le (Finset.le_sup'
    (fun index => ∑ other ∈ Finset.univ.erase index, (max (matrix other index) 0) ^ 2)
    (Finset.mem_univ owner))

theorem positiveFaceCurvatureBudget_le
    (matrix : ι → ι → ℝ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hentry : ∀ receiver owner, matrix receiver owner ≤ 2 * bound) :
    positiveFaceCurvatureBudget matrix ≤ ((Fintype.card ι - 1 : ℕ) : ℝ) * bound ^ 2 := by
  have hcolumn : ∀ owner,
      (∑ receiver ∈ Finset.univ.erase owner, (max (matrix receiver owner) 0) ^ 2) ≤
        ((Fintype.card ι - 1 : ℕ) : ℝ) * (2 * bound) ^ 2 := by
    intro owner
    calc
      _ ≤ ∑ _receiver ∈ Finset.univ.erase owner, (2 * bound) ^ 2 := by
        apply Finset.sum_le_sum
        intro receiver _
        exact (sq_le_sq₀ (le_max_right _ _) (by positivity)).mpr
          (max_le (hentry receiver owner) (by positivity))
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem (Finset.mem_univ owner), Finset.card_univ]
  have hsup := Finset.sup'_le (s := Finset.univ) Finset.univ_nonempty _
    (fun owner _ => hcolumn owner)
  have hscaled := mul_le_mul_of_nonneg_left hsup (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  dsimp [positiveFaceCurvatureBudget]
  nlinarith only [hscaled]

/-- Complete the square on positive matrix entries and use nonnegativity
on nonpositive entries. No bound on an individual coordinate's size is needed. -/
theorem sum_face_quadratic_ge_neg_budget
    (matrix : ι → ι → ℝ) (point : ι → ℝ) (hpoint : ∀ who, 0 ≤ point who)
    (owner : ι) (howner : point owner = 0) :
    -positiveFaceCurvatureBudget matrix ≤
      ∑ receiver, point receiver * (point receiver - matrix receiver owner) := by
  have hterm : ∀ receiver,
      -(max (matrix receiver owner) 0) ^ 2 / 4 ≤
        point receiver * (point receiver - matrix receiver owner) := by
    intro receiver
    by_cases hentry : 0 < matrix receiver owner
    · rw [max_eq_left hentry.le]
      nlinarith [sq_nonneg (point receiver - matrix receiver owner / 2)]
    · rw [max_eq_right (le_of_not_gt hentry)]
      have hproduct := mul_nonneg (hpoint receiver)
        (sub_nonneg.mpr ((le_of_not_gt hentry).trans (hpoint receiver)))
      simpa using hproduct
  have hsum := Finset.sum_le_sum (s := Finset.univ.erase owner) fun receiver _ => hterm receiver
  have hsup := Finset.le_sup'
    (fun index => ∑ receiver ∈ Finset.univ.erase index,
      (max (matrix receiver index) 0) ^ 2) (Finset.mem_univ owner)
  have hown : point owner * (point owner - matrix owner owner) = 0 := by simp [howner]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ owner), hown, add_zero]
  rw [← Finset.sum_div, Finset.sum_neg_distrib] at hsum
  dsimp [positiveFaceCurvatureBudget]
  linarith

/-- The Euclidean squared norm, in the original finite coordinate space. -/
def coordinateShiftedQuadratic (lower : ι → ℝ) (coefficient : ℝ) (point : ι → ℝ) : ℝ :=
  shiftedQuadratic ((EuclideanSpace.equiv ι ℝ).symm lower) coefficient
    ((EuclideanSpace.equiv ι ℝ).symm point)

omit [Nonempty ι] [DecidableEq ι] in
theorem coordinateShiftedQuadratic_contDiff
    (lower : ι → ℝ) (coefficient : ℝ) (order : WithTop ℕ∞) :
    ContDiff ℝ order (coordinateShiftedQuadratic lower coefficient) := by
  have hquadratic :=
    shiftedQuadratic_contDiff ((EuclideanSpace.equiv ι ℝ).symm lower) coefficient order
  exact hquadratic.comp_continuousLinearMap
    (g := (EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap)

omit [Nonempty ι] [DecidableEq ι] in
theorem coordinateShiftedQuadratic_fderiv_apply
    (lower point direction : ι → ℝ) (coefficient : ℝ) :
    fderiv ℝ (coordinateShiftedQuadratic lower coefficient) point direction =
      coefficient * ∑ receiver, (point receiver - lower receiver) * direction receiver := by
  let equiv := EuclideanSpace.equiv ι ℝ
  have hderivative := (shiftedQuadratic_hasFDerivAt (equiv.symm lower) coefficient
    (equiv.symm point)).comp point equiv.symm.hasFDerivAt
  change fderiv ℝ (shiftedQuadratic (equiv.symm lower) coefficient ∘ equiv.symm)
    point direction = _
  rw [hderivative.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul]
  congr 1
  change inner ℝ (equiv.symm point - equiv.symm lower) (equiv.symm direction) = _
  rw [← map_sub, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ receiver, direction receiver * (point receiver - lower receiver)) = _
  apply Finset.sum_congr rfl
  intro receiver _
  ring

end Math
