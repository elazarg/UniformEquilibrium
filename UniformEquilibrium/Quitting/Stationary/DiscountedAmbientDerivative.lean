import UniformEquilibrium.Quitting.Stationary.DiscountedQuadraticRemainder
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.TangentCone.Pi
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Ambient derivative of the actual discounted displacement

The existing quadratic estimate determines the derivative within the full
discount-by-hazard cube. Ambient differentiability of the same finite product
formula and the cube's unique-differentiability property identify its ambient
derivative. The probabilistic quadratic inequality itself is not extended to
negative hazards.
-/

noncomputable section

namespace GameTheory

open Filter Set Asymptotics QuittingLCPClassification
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The full singleton linear part of the actual discounted displacement. -/
def quittingDiscountedSingletonLinearization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    (ℝ × (ι → ℝ)) →L[ℝ] ℝ :=
  reward ⟨{who}, Finset.singleton_nonempty who⟩ who • ContinuousLinearMap.fst ℝ ℝ (ι → ℝ) -
    ∑ player, quittingSingletonMatrix reward who player •
      (ContinuousLinearMap.proj player).comp (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ))

omit [DecidableEq ι] in
theorem quittingDiscountedSingletonLinearization_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (point : ℝ × (ι → ℝ)) :
    quittingDiscountedSingletonLinearization reward who point =
      point.1 * reward ⟨{who}, Finset.singleton_nonempty who⟩ who -
        ∑ player, point.2 player * quittingSingletonMatrix reward who player := by
  simp [quittingDiscountedSingletonLinearization, mul_comm]

/-- The literal finite sum/product formula is differentiable on the entire ambient space. -/
theorem differentiable_quittingDiscountedDisplacement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Differentiable ℝ fun point : ℝ × (ι → ℝ) =>
      quittingDiscountedDisplacement reward point.1 point.2 who := by
  unfold quittingDiscountedDisplacement continueMassExcl sigmaValue excludedValue
  fun_prop

theorem quittingDiscountedDisplacement_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingDiscountedDisplacement reward 0 0 who = 0 := by
  have h := abs_quittingDiscountedSingletonRemainder_le reward
    (discount := 0) (by norm_num) (abs_reward_le_quittingRewardBound reward)
    0 (by simp) (by simp) who
  have hzero : |quittingDiscountedDisplacement reward 0 0 who| ≤ 0 := by
    simpa [quittingDiscountedSingletonRemainder] using h
  exact abs_nonpos_iff.mp hzero

/-- The ambient derivative is determined on a full-dimensional cube, using
the actual remainder and uniqueness of derivatives within that cube. -/
theorem hasFDerivAt_quittingDiscountedDisplacement_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    HasFDerivAt (fun point : ℝ × (ι → ℝ) =>
      quittingDiscountedDisplacement reward point.1 point.2 who)
      (quittingDiscountedSingletonLinearization reward who) 0 := by
  let cube : Set (ℝ × (ι → ℝ)) := Icc (0 : ℝ) 1 ×ˢ univ.pi (fun _ : ι => Icc (0 : ℝ) 1)
  let M := quittingRewardBound reward
  let N : ℝ := (Fintype.card ι : ℝ) + 1
  let linear := quittingDiscountedSingletonLinearization reward who
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hN : 0 < N := by dsimp [N]; positivity
  have hcube : UniqueDiffWithinAt ℝ cube (0 : ℝ × (ι → ℝ)) :=
    (uniqueDiffOn_Icc_zero_one (0 : ℝ) (by simp)).prod
      (UniqueDiffWithinAt.univ_pi fun _ => uniqueDiffOn_Icc_zero_one 0 (by simp))
  have hbound : ∀ point ∈ cube,
      ‖quittingDiscountedDisplacement reward point.1 point.2 who - linear point‖ ≤
        (4 * M * N ^ 2) * ‖point‖ ^ 2 := by
    intro point hpoint
    have hzero : ∀ player, 0 ≤ point.2 player := fun player => (hpoint.2 player (mem_univ _)).1
    have hone : ∀ player, point.2 player ≤ 1 := fun player => (hpoint.2 player (mem_univ _)).2
    have h := abs_quittingDiscountedSingletonRemainder_le reward hpoint.1.1
      (abs_reward_le_quittingRewardBound reward) point.2 hzero hone who
    have hsum : (∑ player, point.2 player) ≤ (Fintype.card ι : ℝ) * ‖point‖ := by
      calc
        _ ≤ ∑ _player : ι, ‖point‖ := Finset.sum_le_sum fun player _ =>
          (le_abs_self _).trans ((norm_le_pi_norm point.2 player).trans (norm_snd_le point))
        _ = _ := by simp
    have hfirst : point.1 ≤ ‖point‖ := (le_abs_self _).trans (norm_fst_le point)
    have htotal : point.1 + ∑ player, point.2 player ≤ N * ‖point‖ := by
      dsimp [N]
      linarith
    have htotal0 : 0 ≤ point.1 + ∑ player, point.2 player :=
      add_nonneg hpoint.1.1 (Finset.sum_nonneg fun player _ => hzero player)
    have hsq := (sq_le_sq₀ htotal0 (mul_nonneg hN.le (norm_nonneg point))).mpr htotal
    have hscaled := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * M by positivity)
    rw [Real.norm_eq_abs]
    change |quittingDiscountedDisplacement reward point.1 point.2 who -
      quittingDiscountedSingletonLinearization reward who point| ≤ _
    rw [quittingDiscountedSingletonLinearization_apply]
    have heq : quittingDiscountedDisplacement reward point.1 point.2 who -
        (point.1 * reward ⟨{who}, Finset.singleton_nonempty who⟩ who -
          ∑ player, point.2 player * quittingSingletonMatrix reward who player) =
        quittingDiscountedSingletonRemainder reward point.1 point.2 who := by
      unfold quittingDiscountedSingletonRemainder
      ring
    rw [heq]
    dsimp only [M] at hscaled ⊢
    nlinarith [h, hscaled]
  have hbig : (fun point : ℝ × (ι → ℝ) =>
      quittingDiscountedDisplacement reward point.1 point.2 who - linear point)
      =O[𝓝[cube] 0] (fun point => ‖point‖ ^ 2) := by
    apply IsBigOWith.isBigO (c := 4 * M * N ^ 2)
    apply IsBigOWith.of_bound
    filter_upwards [self_mem_nhdsWithin] with point hpoint
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖point‖)] using hbound point hpoint
  have hlittle := hbig.trans_isLittleO
    ((isLittleO_norm_pow_id (E' := ℝ × (ι → ℝ)) (show 1 < 2 by norm_num)).mono
      nhdsWithin_le_nhds)
  have hwithin : HasFDerivWithinAt (fun point : ℝ × (ι → ℝ) =>
      quittingDiscountedDisplacement reward point.1 point.2 who) linear cube 0 := by
    apply HasFDerivWithinAt.of_isLittleO
    simpa only [Prod.fst_zero, Prod.snd_zero, quittingDiscountedDisplacement_zero,
      sub_zero] using hlittle
  have hambient := (differentiable_quittingDiscountedDisplacement reward who 0).hasFDerivAt
  have heq := hcube.eq hwithin hambient.hasFDerivWithinAt
  change HasFDerivAt _ linear 0
  rw [heq]
  exact hambient

end GameTheory
