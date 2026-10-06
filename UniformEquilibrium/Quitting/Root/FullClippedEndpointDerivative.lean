import UniformEquilibrium.Quitting.Root.FullClippedEndpointMap
import MathUE.LinearAlgebra.IdentityComplementDeterminant
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The full ambient derivative at strict clipping rows

Interior rows retain the derivative of the entire endpoint polynomial.
Strictly lower or upper saturated rows are locally constant under clipping,
so the corresponding displacement derivative is the identity row. Equalities
at clipping thresholds are not asserted differentiable here.
-/

noncomputable section

namespace GameTheory

open Set Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingFullClippedDisplacementDerivative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (active : Finset ι) (point : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun player =>
    if player ∈ active then
      -fderiv ℝ (fun hazard => quittingRealHazardEndpointGap reward tail hazard player) point
    else ContinuousLinearMap.proj player

/-- This derivative is ambient, including signed variations of inactive
coordinates. No Nash or cube-membership premise is needed for linearization. -/
theorem hasFDerivAt_quittingFullClippedDisplacement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (active : Finset ι) (point : ι → ℝ)
    (hinterior : ∀ player ∈ active,
      point player + quittingRealHazardEndpointGap reward tail point player ∈ Ioo (0 : ℝ) 1)
    (hsaturated : ∀ player ∉ active,
      point player + quittingRealHazardEndpointGap reward tail point player < 0 ∨
        1 < point player + quittingRealHazardEndpointGap reward tail point player) :
    HasFDerivAt (fun hazard => hazard - quittingFullClippedEndpointMap reward tail hazard)
      (quittingFullClippedDisplacementDerivative reward tail active point) point := by
  change HasFDerivAt (fun hazard player =>
    hazard player - quittingFullClippedEndpointMap reward tail hazard player)
      (ContinuousLinearMap.pi _) point
  rw [hasFDerivAt_pi]
  intro player
  have hregular := contDiff_quittingRealHazardEndpointGap reward tail 1 player
  have hgap := (hregular.differentiable_one point).hasFDerivAt
  have hinput : Continuous (fun hazard : ι → ℝ =>
      hazard player + quittingRealHazardEndpointGap reward tail hazard player) :=
    (continuous_apply player).add
      (contDiff_quittingRealHazardEndpointGap reward tail 0 player).continuous
  by_cases hactive : player ∈ active
  · simp only [hactive, ite_true]
    apply hgap.neg.congr_of_eventuallyEq
    filter_upwards [hinput.continuousAt.eventually
      (isOpen_Ioo.mem_nhds (hinterior player hactive))] with hazard hhazard
    change hazard player - min 1 (max 0
      (hazard player + quittingRealHazardEndpointGap reward tail hazard player)) = _
    rw [max_eq_right hhazard.1.le, min_eq_right hhazard.2.le]
    change hazard player - (hazard player +
      quittingRealHazardEndpointGap reward tail hazard player) =
        -quittingRealHazardEndpointGap reward tail hazard player
    simp only [sub_add_eq_sub_sub, sub_self, zero_sub]
  · simp only [hactive, ite_false]
    rcases hsaturated player hactive with hlower | hupper
    · apply (hasFDerivAt_apply player point).congr_of_eventuallyEq
      filter_upwards [hinput.continuousAt.eventually
        (isOpen_Iio.mem_nhds hlower)] with hazard hhazard
      change hazard player - min 1 (max 0
        (hazard player + quittingRealHazardEndpointGap reward tail hazard player)) = _
      rw [max_eq_left hhazard.le, min_eq_right zero_le_one, sub_zero]
    · have hrow := (hasFDerivAt_apply (𝕜 := ℝ) player point).sub
        (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) point)
      simp only [sub_zero] at hrow
      apply hrow.congr_of_eventuallyEq
      filter_upwards [hinput.continuousAt.eventually
        (isOpen_Ioi.mem_nhds hupper)] with hazard hhazard
      change hazard player - min 1 (max 0
        (hazard player + quittingRealHazardEndpointGap reward tail hazard player)) = _
      rw [max_eq_right (zero_le_one.trans hhazard.le), min_eq_left hhazard.le]
      rfl

theorem quittingFullClippedDisplacementDerivative_matrix_entry
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (active : Finset ι) (point : ι → ℝ) (row column : ι) :
    LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail active point).toLinearMap
        row column =
      if row ∈ active then
        -fderiv ℝ (fun hazard => quittingRealHazardEndpointGap reward tail hazard row)
          point (Pi.single column 1)
      else if row = column then 1 else 0 := by
  by_cases hrow : row ∈ active
  · simp [LinearMap.toMatrix'_apply, quittingFullClippedDisplacementDerivative, hrow]
  · simp [LinearMap.toMatrix'_apply, quittingFullClippedDisplacementDerivative, hrow,
      Pi.single_apply]

/-- All ambient inactive directions remain present; arbitrary starred
active-to-inactive entries do not affect the determinant. -/
theorem quittingFullClippedDisplacementDerivative_det_eq_active_det
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (active : Finset ι) (point : ι → ℝ) :
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail active point).toLinearMap).det =
      (Matrix.submatrix (LinearMap.toMatrix'
        (quittingFullClippedDisplacementDerivative reward tail active point).toLinearMap)
        (fun row : {row // row ∈ active} => row.val)
        (fun column : {column // column ∈ active} => column.val)).det := by
  apply Math.Matrix.det_eq_active_submatrix_of_identity_complement_rows
  intro row hrow column
  rw [quittingFullClippedDisplacementDerivative_matrix_entry]
  simp only [hrow, ite_false]

end GameTheory
