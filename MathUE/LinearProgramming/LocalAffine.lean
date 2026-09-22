import MathUE.LinearProgramming.CopositiveQ
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Local affine form of the minimum complementarity map

The ambient minimum map uses the existing standard LCP residual and solution
predicate. At a strictly complementary root its rows locally select either
the residual or the coordinate. The resulting matrix has determinant equal
to the active principal determinant, including empty support and dimension
zero. These are algebraic and continuity statements, independent of degree.
-/

noncomputable section

namespace Math.LinearProgramming

open Classical Set Filter
open scoped Topology

variable {ι : Type*} [Fintype ι]

/-- The minimum complementarity map on the entire ambient coordinate space. -/
def lcpMinMap (matrix : Matrix ι ι ℝ) (offset point : ι → ℝ) : ι → ℝ :=
  fun who => min (point who) (lcpResidual matrix offset point who)

/-- The existing row convention agrees with ordinary matrix-vector multiplication. -/
theorem lcpResidual_eq_add_mulVec (matrix : Matrix ι ι ℝ) (offset point : ι → ℝ) :
    lcpResidual matrix offset point = offset + matrix.mulVec point := by
  funext who
  simp only [lcpResidual, Pi.add_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem continuous_lcpResidual (matrix : Matrix ι ι ℝ) (offset : ι → ℝ) :
    Continuous (lcpResidual matrix offset) := by
  have hequal : lcpResidual matrix offset = fun point => offset + matrix.mulVec point :=
    funext fun point => lcpResidual_eq_add_mulVec matrix offset point
  rw [hequal]
  exact continuous_const.add (continuous_const.matrix_mulVec continuous_id)

theorem continuous_lcpMinMap (matrix : Matrix ι ι ℝ) (offset : ι → ℝ) :
    Continuous (lcpMinMap matrix offset) := by
  exact continuous_pi fun who => (continuous_apply who).min
    ((continuous_apply who).comp (continuous_lcpResidual matrix offset))

/-- Ambient zeros are exactly the existing standard LCP solutions. -/
theorem lcpMinMap_eq_zero_iff (matrix : Matrix ι ι ℝ) (offset point : ι → ℝ) :
    lcpMinMap matrix offset point = 0 ↔ IsStandardLCPSolution matrix offset point := by
  constructor
  · intro hzero
    have hmin (who : ι) : min (point who) (lcpResidual matrix offset point who) = 0 :=
      congrFun hzero who
    have hnonneg (who : ι) := le_min_iff.mp (le_of_eq (hmin who).symm)
    refine ⟨fun who => (hnonneg who).1, fun who => (hnonneg who).2, ?_⟩
    intro who
    have hzero := hmin who
    rcases le_total (point who) (lcpResidual matrix offset point who) with hle | hle
    · rw [min_eq_left hle] at hzero
      rw [hzero, zero_mul]
    · rw [min_eq_right hle] at hzero
      rw [hzero, mul_zero]
  · intro hsolution
    funext who
    change min (point who) (lcpResidual matrix offset point who) = 0
    rcases mul_eq_zero.mp (hsolution.complementary who) with hpoint | hresidual
    · rw [hpoint, min_eq_left (hsolution.residual_nonneg who)]
    · rw [hresidual, min_eq_right (hsolution.weight_nonneg who)]

variable [DecidableEq ι]

/-- Active rows select the matrix; inactive rows select the identity. -/
def lcpSelectedMatrix (matrix : Matrix ι ι ℝ) (root : ι → ℝ) : Matrix ι ι ℝ :=
  fun who coordinate => if 0 < root who then matrix who coordinate else
    (1 : Matrix ι ι ℝ) who coordinate

theorem lcpSelectedMatrix_mulVec (matrix : Matrix ι ι ℝ) (root vector : ι → ℝ)
    (who : ι) :
    (lcpSelectedMatrix matrix root).mulVec vector who =
      if 0 < root who then matrix.mulVec vector who else vector who := by
  by_cases hactive : 0 < root who
  · simp [lcpSelectedMatrix, Matrix.mulVec, dotProduct, hactive]
  · simp [lcpSelectedMatrix, Matrix.mulVec, dotProduct, Matrix.one_apply, hactive]

/-- Strict complementarity makes the minimum map literally affine near the root. -/
theorem IsStandardLCPSolution.eventually_lcpMinMap_eq_selectedMatrix
    {matrix : Matrix ι ι ℝ} {offset root : ι → ℝ}
    (hroot : IsStandardLCPSolution matrix offset root)
    (hstrict : ∀ who, root who = 0 → 0 < lcpResidual matrix offset root who) :
    ∀ᶠ point in 𝓝 root,
      lcpMinMap matrix offset point = (lcpSelectedMatrix matrix root).mulVec (point - root) := by
  have hcoordinate (who : ι) : ∀ᶠ point in 𝓝 root,
      lcpMinMap matrix offset point who =
        (lcpSelectedMatrix matrix root).mulVec (point - root) who := by
    have hcontinuous := (continuous_apply who).comp (continuous_lcpResidual matrix offset)
    by_cases hactive : 0 < root who
    · have hzero : lcpResidual matrix offset root who = 0 :=
        (mul_eq_zero.mp (hroot.complementary who)).resolve_left hactive.ne'
      have hnear : ∀ᶠ point in 𝓝 root, lcpResidual matrix offset point who < point who :=
        (hcontinuous.continuousAt : ContinuousAt
          (fun point => lcpResidual matrix offset point who) root).eventually_lt
          (continuous_apply who).continuousAt (by
            change lcpResidual matrix offset root who < root who
            simpa only [hzero] using hactive)
      filter_upwards [hnear] with point hpoint
      rw [lcpMinMap, min_eq_right hpoint.le, lcpSelectedMatrix_mulVec, ite_eq_left hactive,
        Matrix.mulVec_sub]
      have hzero' := congrFun (lcpResidual_eq_add_mulVec matrix offset root) who
      have hpoint' := congrFun (lcpResidual_eq_add_mulVec matrix offset point) who
      simp only [Pi.add_apply, Pi.sub_apply] at hzero' hpoint' ⊢
      linarith
    · have hzero : root who = 0 :=
        le_antisymm (le_of_not_gt hactive) (hroot.weight_nonneg who)
      have hnear : ∀ᶠ point in 𝓝 root, point who < lcpResidual matrix offset point who :=
        ((continuous_apply who).continuousAt : ContinuousAt
          (fun point : ι → ℝ => point who) root).eventually_lt
          hcontinuous.continuousAt (by simpa only [hzero] using hstrict who hzero)
      filter_upwards [hnear] with point hpoint
      rw [lcpMinMap, min_eq_left hpoint.le, lcpSelectedMatrix_mulVec, ite_eq_right hactive]
      simp only [Pi.sub_apply, hzero, sub_zero]
  filter_upwards [Filter.eventually_all.mpr hcoordinate] with point hpoint
  exact funext hpoint

/-- The affine identity holds on an actual positive-radius closed coordinate box. -/
theorem IsStandardLCPSolution.exists_box_lcpMinMap_eq_selectedMatrix
    {matrix : Matrix ι ι ℝ} {offset root : ι → ℝ}
    (hroot : IsStandardLCPSolution matrix offset root)
    (hstrict : ∀ who, root who = 0 → 0 < lcpResidual matrix offset root who) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ point ∈ Icc (fun who => root who - radius) (fun who => root who + radius),
        lcpMinMap matrix offset point =
          (lcpSelectedMatrix matrix root).mulVec (point - root) := by
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp
    (hroot.eventually_lcpMinMap_eq_selectedMatrix hstrict)
  refine ⟨epsilon / 2, half_pos hepsilon, ?_⟩
  intro point hpoint
  apply hball
  rw [Metric.mem_ball, dist_pi_lt_iff hepsilon]
  intro who
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hpoint.1 who, hpoint.2 who]

/-- The selected-row determinant is exactly the active principal determinant.
The identity block contributes one even when either block is empty. -/
theorem det_lcpSelectedMatrix (matrix : Matrix ι ι ℝ) (root : ι → ℝ) :
    (lcpSelectedMatrix matrix root).det =
      (matrix.toSquareBlockProp (fun who => 0 < root who)).det := by
  rw [Matrix.twoBlockTriangular_det _ (fun who => 0 < root who)]
  · have hactive : (lcpSelectedMatrix matrix root).toSquareBlockProp
        (fun who => 0 < root who) = matrix.toSquareBlockProp (fun who => 0 < root who) := by
      ext who coordinate
      simp [Matrix.toSquareBlockProp, lcpSelectedMatrix, who.property]
    have hinactive : (lcpSelectedMatrix matrix root).toSquareBlockProp
        (fun who => ¬0 < root who) = 1 := by
      ext who coordinate
      simp [Matrix.toSquareBlockProp, lcpSelectedMatrix, who.property,
        Matrix.one_apply, Subtype.ext_iff]
    rw [hactive, hinactive, Matrix.det_one, mul_one]
  · intro who hinactive coordinate hactive
    have hne : who ≠ coordinate := by
      intro hequal
      subst coordinate
      exact hinactive hactive
    simp [lcpSelectedMatrix, hinactive, hne]

end Math.LinearProgramming
