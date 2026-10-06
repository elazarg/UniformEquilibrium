import UniformEquilibrium.Quitting.Root.FullClippedEndpointMap
import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp
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

theorem quittingRealHazardEndpointGap_update_own
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (point : ι → ℝ) (player : ι) (rate : ℝ) :
    quittingRealHazardEndpointGap reward tail (Function.update point player rate) player =
      quittingRealHazardEndpointGap reward tail point player := by
  unfold quittingRealHazardEndpointGap CoalGame.coordinateDerivative
  apply Finset.sum_congr rfl
  intro coalition _
  by_cases hplayer : player ∈ coalition
  · simp only [hplayer, ite_true]
    congr 1
    apply Finset.prod_congr rfl
    intro who hwho
    exact Function.update_of_ne (Finset.mem_erase.mp hwho).1 rate point
  · simp only [hplayer, ite_false]

theorem quittingRealHazardEndpointGap_own_partial_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (point : ι → ℝ) (player : ι) :
    fderiv ℝ (fun hazard => quittingRealHazardEndpointGap reward tail hazard player)
      point (Pi.single player 1) = 0 := by
  have hregular := contDiff_quittingRealHazardEndpointGap reward tail 1 player
  have hgap := (hregular.differentiable_one point).hasFDerivAt
  have hchain := hgap.comp_hasDerivAt_of_eq (point player)
    (hasDerivAt_update point player (point player)) (by simp)
  have hconstant : HasDerivAt
      (fun rate => quittingRealHazardEndpointGap reward tail
        (Function.update point player rate) player) 0 (point player) := by
    simpa only [quittingRealHazardEndpointGap_update_own] using
      (hasDerivAt_const (point player) (quittingRealHazardEndpointGap reward tail point player))
  exact hchain.unique hconstant

/-- Any proper actual support with strictly inactive gaps has the canonical
full ambient derivative, independently of the support's cardinality. -/
theorem hasFDerivAt_quittingFullClippedDisplacement_of_properSupportNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) (active : Finset ι)
    (hsupport : quittingPositiveHazardSupport root = active)
    (hproper : ∀ player ∈ active, (root player true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hnegative : ∀ player ∉ active, quittingRootEndpointDifference reward tail root player < 0) :
    HasFDerivAt (fun hazard => hazard - quittingFullClippedEndpointMap reward tail hazard)
      (quittingFullClippedDisplacementDerivative reward tail active (hazardOfRoot root))
      (hazardOfRoot root) := by
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash
  apply hasFDerivAt_quittingFullClippedDisplacement
  · intro player hplayer
    have hprobability := hproper player hplayer
    have hfalse : 0 < (root player false).toReal := by
      rw [Math.PMFProduct.pmfBool_false_toReal]
      exact sub_pos.mpr hprobability.2
    have hgap := quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
      reward tail root player hendpoint hfalse hprobability.1
    simpa only [quittingRealHazardEndpointGap_hazardOfRoot, hgap, add_zero, hazardOfRoot]
      using hprobability
  · intro player hplayer
    have hpure := quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport root
      (by rwa [hsupport])
    left
    simpa [quittingRealHazardEndpointGap_hazardOfRoot, hazardOfRoot, hpure]
      using hnegative player hplayer

end GameTheory
