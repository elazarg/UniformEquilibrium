import UniformEquilibrium.Quitting.Examples.CrossedMatchingFixtureMatrix
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotient
import UniformEquilibrium.Quitting.Root.PlayerwiseAffineReward
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import Mathlib.Tactic.Ring

/-! # Response-block rigidity of the literal crossed-matching fixture

The all-sure displacement is grand reward minus the reward of the coalition
with the recipient removed, not grand reward minus its own singleton.
Nonzero signed row scales and arbitrary translations preserve this response
screen. No strategic, R0, or degree invariance under signed scaling is asserted.
-/

noncomputable section

namespace GameTheory.CrossedMatchingFixture

open QuittingLCPClassification QuittingFinFourEndpointRows

def responseRowSum : Fin 4 → ℝ := ![169 / 40, 37 / 8, 37 / 8, 37 / 8]

def allSureDisplacement : Fin 4 → ℝ := ![-11, -12, -13, -14]

theorem singleton_rowSum_eq (player : Fin 4) :
      (∑ other, quittingSingletonMatrix reward player other) = responseRowSum player := by
  change (∑ other, quittingProjectiveLCPMatrix reward player other) = responseRowSum player
  rw [projectiveMatrix_eq]
  fin_cases player <;> norm_num [matrix, responseRowSum, Fin.sum_univ_succ]

theorem affine_singletonMatrix (scale shift : Payoff (Fin 4)) (player other : Fin 4) :
    quittingSingletonMatrix (quittingPlayerwiseAffineReward reward scale shift) player other =
      scale player * quittingSingletonMatrix reward player other := by
  unfold quittingSingletonMatrix quittingPlayerwiseAffineReward
  ring

/-- Literal endpoint expansion at the all-one hazard vector. -/
theorem affine_allSure_displacement_eq (scale shift : Payoff (Fin 4)) (player : Fin 4) :
    quittingDiscountedDisplacement
        (quittingPlayerwiseAffineReward reward scale shift) 0 (fun _ => 1) player =
      scale player * allSureDisplacement player := by
  rw [quittingDiscountedDisplacement_one_eq_grand_sub_withdrawal]
  simp only [quittingPlayerwiseAffineReward]
  fin_cases player
  all_goals norm_num [reward, Math.FiniteCoalition.binaryCode_finFour, allSureDisplacement]

theorem allSure_displacement_eq (player : Fin 4) :
    quittingDiscountedDisplacement reward 0 (fun _ => 1) player =
      allSureDisplacement player := by
  have hre : quittingPlayerwiseAffineReward reward (fun _ => 1) (fun _ => 0) = reward := by
    funext terminal who
    simp only [quittingPlayerwiseAffineReward, one_mul, add_zero]
  have h := affine_allSure_displacement_eq (fun _ => 1) (fun _ => 0) player
  rw [hre, one_mul] at h
  exact h

theorem normalized_allSure_ratio_injective :
    Function.Injective (fun player => allSureDisplacement player / responseRowSum player) := by
  intro first second heq
  fin_cases first <;> fin_cases second
  all_goals norm_num [allSureDisplacement, responseRowSum] at heq
  all_goals rfl

/-- A purely response-polynomial screen; signed nonzero scales are sufficient. -/
theorem affine_responseInvariant_injective_of_nonzero_scale
    (scale shift : Payoff (Fin 4)) (hscale : ∀ player, scale player ≠ 0)
    {k : ℕ} (block : Fin 4 → Fin k)
    (hresponse : QuittingResponseInvariantOnUnitCube
      (quittingPlayerwiseAffineReward reward scale shift) block) :
    Function.Injective block := by
  apply injective_block_of_responseInvariant_of_injective_normalized_displacement
    (quittingPlayerwiseAffineReward reward scale shift) block hresponse
  have heq : (fun player =>
      quittingDiscountedDisplacement
          (quittingPlayerwiseAffineReward reward scale shift) 0 (fun _ => 1) player /
        (∑ other, quittingSingletonMatrix
          (quittingPlayerwiseAffineReward reward scale shift) player other)) =
      (fun player => allSureDisplacement player / responseRowSum player) := by
    funext player
    simp only [affine_allSure_displacement_eq, affine_singletonMatrix,
      ← Finset.mul_sum, singleton_rowSum_eq]
    exact mul_div_mul_left _ _ (hscale player)
  rw [heq]
  exact normalized_allSure_ratio_injective

theorem affine_responseInvariant_injective
    (scale shift : Payoff (Fin 4)) (hscale : ∀ player, 0 < scale player)
    {k : ℕ} (block : Fin 4 → Fin k)
    (hresponse : QuittingResponseInvariantOnUnitCube
      (quittingPlayerwiseAffineReward reward scale shift) block) :
    Function.Injective block :=
  affine_responseInvariant_injective_of_nonzero_scale scale shift
    (fun player => (hscale player).ne') block hresponse

theorem responseInvariant_injective {k : ℕ} (block : Fin 4 → Fin k)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block) :
    Function.Injective block := by
  apply injective_block_of_responseInvariant_of_injective_normalized_displacement
    reward block hresponse
  simpa only [allSure_displacement_eq, singleton_rowSum_eq] using
    normalized_allSure_ratio_injective

end GameTheory.CrossedMatchingFixture
