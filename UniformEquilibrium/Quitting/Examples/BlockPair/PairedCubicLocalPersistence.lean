import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCubicActiveJacobian
import UniformEquilibrium.Quitting.Root.RewardTableCoordinates
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! # Full reward-table persistence of the three-active stationary branch

The canonical coordinates range over every raw coalition/recipient entry.
The implicit branch has three independent active hazards and a fixed zero
fourth hazard. Its neighborhood and inactive strict sign are derived from the
actual table, derivative, and algebraic root; none is an input certificate.
-/

noncomputable section

namespace GameTheory.PairedCubicStationaryExample

open scoped Topology ContDiff
open Filter

abbrev RewardParameters :=
  Fin (Fintype.card (QuittingRewardTableVariable (Fin 4))) → ℝ

/-- The full raw parameter domain has fifteen coalition rows and four recipients. -/
theorem rewardTableVariable_card :
    Fintype.card (QuittingRewardTableVariable (Fin 4)) = 60 := by
  have hrows : Fintype.card {S : Finset (Fin 4) // S.Nonempty} = 15 := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr Math.Finset.finFourCoalitionRowEquiv.symm
  change Fintype.card ({S : Finset (Fin 4) // S.Nonempty} × Fin 4) = 60
  rw [Fintype.card_prod, hrows, Fintype.card_fin]

def baseParameters : RewardParameters := quittingRewardTableCoordinates reward

def jointDisplacement (input : RewardParameters × (Fin 3 → ℝ)) (who : Fin 4) : ℝ :=
  quittingDiscountedDisplacement (quittingRewardTableFromCoordinates input.1) 0
    (activeHazard input.2) who

def jointActiveResponse (input : RewardParameters × (Fin 3 → ℝ)) : Fin 3 → ℝ :=
  fun coordinate => jointDisplacement input coordinate.castSucc

@[fun_prop]
private theorem contDiff_joint_hazard (who : Fin 4) :
    ContDiff ℝ 1 (fun input : RewardParameters × (Fin 3 → ℝ) =>
      activeHazard input.2 who) := by
  fin_cases who
  · change ContDiff ℝ 1 (fun input : RewardParameters × (Fin 3 → ℝ) => input.2 0)
    fun_prop
  · change ContDiff ℝ 1 (fun input : RewardParameters × (Fin 3 → ℝ) => input.2 1)
    fun_prop
  · change ContDiff ℝ 1 (fun input : RewardParameters × (Fin 3 → ℝ) => input.2 2)
    fun_prop
  · change ContDiff ℝ 1 (fun _input : RewardParameters × (Fin 3 → ℝ) => (0 : ℝ))
    fun_prop

@[fun_prop]
private theorem contDiff_joint_weight (coalition : Finset (Fin 4)) (who : Fin 4) :
    ContDiff ℝ 1 (fun input : RewardParameters × (Fin 3 → ℝ) =>
      weightOfReward (quittingRewardTableFromCoordinates input.1) coalition who) := by
  unfold weightOfReward
  split_ifs
  · unfold quittingRewardTableFromCoordinates
    fun_prop
  · fun_prop

theorem contDiff_jointDisplacement (who : Fin 4) :
    ContDiff ℝ 1 (fun input => jointDisplacement input who) := by
  unfold jointDisplacement quittingDiscountedDisplacement continueMassExcl
    sigmaValue excludedValue
  fun_prop

theorem contDiff_jointActiveResponse : ContDiff ℝ 1 jointActiveResponse := by
  apply contDiff_pi.mpr
  intro coordinate
  exact contDiff_jointDisplacement coordinate.castSucc

theorem jointActiveResponse_base :
    jointActiveResponse (baseParameters, activeBase) = 0 := by
  change activeResponse (quittingRewardTableFromCoordinates baseParameters) activeBase = 0
  rw [baseParameters, quittingRewardTableFromCoordinates_encode]
  exact activeBase_response_zero

/-- The actual partial derivative in all three independent active coordinates is invertible. -/
theorem jointActiveResponse_partial_invertible :
    (fderiv ℝ jointActiveResponse (baseParameters, activeBase) ∘L
      ContinuousLinearMap.inr ℝ RewardParameters (Fin 3 → ℝ)).IsInvertible := by
  have hderivative : HasFDerivAt jointActiveResponse
      (fderiv ℝ jointActiveResponse (baseParameters, activeBase))
      (baseParameters, activeBase) :=
    (contDiff_jointActiveResponse.contDiffAt.hasStrictFDerivAt
      (by norm_num : (1 : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hchain : HasFDerivAt (fun point => jointActiveResponse (baseParameters, point))
      (fderiv ℝ jointActiveResponse (baseParameters, activeBase) ∘L
        ContinuousLinearMap.inr ℝ RewardParameters (Fin 3 → ℝ)) activeBase :=
    hderivative.comp activeBase (hasFDerivAt_prodMk_right baseParameters activeBase)
  have hrestrict :
      fderiv ℝ (activeResponse reward) activeBase =
        fderiv ℝ jointActiveResponse (baseParameters, activeBase) ∘L
          ContinuousLinearMap.inr ℝ RewardParameters (Fin 3 → ℝ) := by
    have hfunction : (fun point => jointActiveResponse (baseParameters, point)) =
        activeResponse reward := by
      funext point
      change activeResponse (quittingRewardTableFromCoordinates baseParameters) point =
        activeResponse reward point
      rw [baseParameters, quittingRewardTableFromCoordinates_encode]
    rw [hfunction] at hchain
    exact hchain.fderiv
  rw [← hrestrict]
  exact activeBase_derivative_invertible

private theorem inactive_base_negative :
    jointDisplacement (baseParameters, activeBase) 3 < 0 := by
  unfold jointDisplacement baseParameters
  rw [quittingRewardTableFromCoordinates_encode]
  change quittingDiscountedDisplacement reward 0 (hazard firstRoot secondRoot) 3 < 0
  rw [displacement_eq]
  change inactiveResidual firstRoot secondRoot < 0
  have h := inactiveResidual_le firstRoot_spec.1 secondRoot_spec.1
  linarith

/-- Every one of the sixty raw entries may vary independently in this actual open neighborhood. -/
theorem exists_local_active_branch :
    ∃ branch : RewardParameters → (Fin 3 → ℝ),
      ∃ neighborhood : Set RewardParameters,
        IsOpen neighborhood ∧ baseParameters ∈ neighborhood ∧
        ContDiffOn ℝ 1 branch neighborhood ∧ branch baseParameters = activeBase ∧
        ∀ parameters ∈ neighborhood,
          (∀ coordinate, branch parameters coordinate ∈ Set.Ioo (0 : ℝ) 1) ∧
          jointActiveResponse (parameters, branch parameters) = 0 ∧
          jointDisplacement (parameters, branch parameters) 3 < 0 := by
  have cdf : ContDiffAt ℝ 1 jointActiveResponse (baseParameters, activeBase) :=
    contDiff_jointActiveResponse.contDiffAt
  let branch := cdf.implicitFunction (by norm_num : (1 : ℕ∞ω) ≠ 0)
    jointActiveResponse_partial_invertible
  have hbase : branch baseParameters = activeBase :=
    cdf.implicitFunction_apply_self _ _
  have hbranch : ContDiffAt ℝ 1 branch baseParameters :=
    cdf.contDiffAt_implicitFunction _ _
  have hzero : ∀ᶠ parameters in 𝓝 baseParameters,
      jointActiveResponse (parameters, branch parameters) = 0 := by
    simpa only [jointActiveResponse_base] using
      cdf.eventually_apply_implicitFunction
        (by norm_num : (1 : ℕ∞ω) ≠ 0) jointActiveResponse_partial_invertible
  have hinterior : ∀ coordinate, activeBase coordinate ∈ Set.Ioo (0 : ℝ) 1 := by
    intro coordinate
    fin_cases coordinate
    · change 0 < firstRoot ∧ firstRoot < 1
      constructor <;> linarith [firstRoot_spec.1.1, firstRoot_spec.1.2]
    · change 0 < firstRoot ∧ firstRoot < 1
      constructor <;> linarith [firstRoot_spec.1.1, firstRoot_spec.1.2]
    · change 0 < secondRoot ∧ secondRoot < 1
      constructor <;> linarith [secondRoot_spec.1.1, secondRoot_spec.1.2]
  have hunit : ∀ᶠ input : RewardParameters × (Fin 3 → ℝ)
      in 𝓝 (baseParameters, activeBase),
      ∀ coordinate, input.2 coordinate ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [Filter.eventually_all]
    intro coordinate
    exact ((continuous_apply coordinate).comp continuous_snd).continuousAt.tendsto.eventually
      (Ioo_mem_nhds (hinterior coordinate).1 (hinterior coordinate).2)
  have hnegative : ∀ᶠ input in 𝓝 (baseParameters, activeBase),
      jointDisplacement input 3 < 0 :=
    (contDiff_jointDisplacement 3).continuous.continuousAt.tendsto.eventually
      (Iio_mem_nhds inactive_base_negative)
  have hpair : Tendsto (fun parameters => (parameters, branch parameters))
      (𝓝 baseParameters) (𝓝 (baseParameters, activeBase)) := by
    simpa only [hbase, id_eq] using
      (continuous_id.continuousAt.tendsto.prodMk_nhds hbranch.continuousAt.tendsto)
  have hgood := (hpair.eventually (hunit.and hnegative)).and
    (hzero.and (hbranch.eventually (by norm_num : (1 : ℕ∞ω) ≠ ∞)))
  obtain ⟨neighborhood, hsubset, hopen, hmem⟩ := mem_nhds_iff.mp hgood
  refine ⟨branch, neighborhood, hopen, hmem, ?_, hbase, ?_⟩
  · intro parameters hparameters
    exact (hsubset hparameters).2.2.contDiffWithinAt
  · intro parameters hparameters
    have h := hsubset hparameters
    exact ⟨h.1.1, h.2.1, h.1.2⟩

end GameTheory.PairedCubicStationaryExample
