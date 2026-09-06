import MathUE.LinearProgramming.PositiveEntries
import Mathlib.Topology.Instances.Matrix

noncomputable section

namespace Math.LinearProgramming

open Filter
open scoped Topology

variable {I : Type} [Fintype I] [DecidableEq I]

/-- An invertible matrix whose inverse is strictly positive entrywise. -/
def HasStrictlyPositiveInverse (M : Matrix I I ℝ) : Prop :=
  M.det ≠ 0 ∧ HasStrictlyPositiveEntries M⁻¹

theorem hasStrictlyPositiveInverse_of_rightInverse
    (M B : Matrix I I ℝ) (hMB : M * B = 1)
    (hB : HasStrictlyPositiveEntries B) : HasStrictlyPositiveInverse M := by
  have hdet : M.det ≠ 0 := by
    intro hzero
    have := congrArg Matrix.det hMB
    simp [Matrix.det_mul, hzero] at this
  refine ⟨hdet, ?_⟩
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hinverse : M⁻¹ = B := by
    calc
      M⁻¹ = M⁻¹ * 1 := by rw [mul_one]
      _ = M⁻¹ * (M * B) := by rw [hMB]
      _ = (M⁻¹ * M) * B := by rw [Matrix.mul_assoc]
      _ = B := by rw [M.nonsing_inv_mul hunit, one_mul]
  rwa [hinverse]

theorem isOpen_hasStrictlyPositiveInverse :
    IsOpen {M : Matrix I I ℝ | HasStrictlyPositiveInverse M} := by
  rw [isOpen_iff_mem_nhds]
  intro M h
  have hdet : ContinuousAt (fun N : Matrix I I ℝ ↦ N.det) M :=
    continuous_id.matrix_det.continuousAt
  have hscalarInv : ContinuousAt Ring.inverse M.det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ h.1
  have hinv : ContinuousAt (fun N : Matrix I I ℝ ↦ N⁻¹) M :=
    continuousAt_matrix_inv M hscalarInv
  have hdetEventually : ∀ᶠ N in nhds M, N.det ≠ 0 :=
    hdet.eventually (isOpen_compl_singleton.mem_nhds h.1)
  have hentryEventually : ∀ᶠ N in nhds M, ∀ i j, 0 < N⁻¹ i j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact ((continuous_apply_apply i j).continuousAt.comp hinv).eventually_const_lt
      (h.2 i j)
  filter_upwards [hdetEventually, hentryEventually] with N hNdet hNentries
  exact ⟨hNdet, hNentries⟩

end Math.LinearProgramming
