import UniformEquilibrium.Quitting.Examples.BelowSingletonJointPhaseFixture
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantFiniteLabels
import UniformEquilibrium.Quitting.Root.PlayerwiseAffineReward
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import Mathlib.Tactic.Ring

/-! # Discrete response blocks for the below-singleton fixture

The actual singleton row sums are one and the four all-sure displacements
are distinct. The canonical response criterion therefore excludes every
nondiscrete block map, including arbitrary unused labels. Nonzero signed
row scales suffice for this response-only screen; no strategic, R0 or degree
transport under signed scaling is asserted.
-/

noncomputable section

namespace GameTheory.BelowSingletonJointPhaseFixture

open QuittingLCPClassification QuittingFinFourEndpointRows

def allSureDisplacement : Fin 4 → ℝ := ![-101, -102, -103, -104]

theorem singleton_rowSum_eq (player : Fin 4) :
    (∑ other, quittingSingletonMatrix reward player other) = 1 := by
  fin_cases player <;>
    norm_num +decide [quittingSingletonMatrix, reward, Math.FiniteCoalition.binaryCode,
      Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal, Fin.sum_univ_succ]

theorem allSure_displacement_eq (player : Fin 4) :
    quittingDiscountedDisplacement reward 0 (fun _ => 1) player =
      allSureDisplacement player := by
  rw [quittingDiscountedDisplacement_one_eq_grand_sub_withdrawal]
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  fin_cases player <;>
    norm_num +decide [reward, Math.FiniteCoalition.binaryCode_finFour,
      allSureDisplacement, huniv]

theorem affine_singletonMatrix (scale shift : Payoff (Fin 4)) (player other : Fin 4) :
    quittingSingletonMatrix (quittingPlayerwiseAffineReward reward scale shift) player other =
      scale player * quittingSingletonMatrix reward player other := by
  unfold quittingSingletonMatrix quittingPlayerwiseAffineReward
  ring

theorem affine_allSure_displacement_eq (scale shift : Payoff (Fin 4)) (player : Fin 4) :
    quittingDiscountedDisplacement
        (quittingPlayerwiseAffineReward reward scale shift) 0 (fun _ => 1) player =
      scale player * allSureDisplacement player := by
  rw [← allSure_displacement_eq,
    quittingDiscountedDisplacement_one_eq_grand_sub_withdrawal,
    quittingDiscountedDisplacement_one_eq_grand_sub_withdrawal]
  unfold quittingPlayerwiseAffineReward
  ring

theorem allSure_displacement_injective : Function.Injective allSureDisplacement := by
  intro first second heq
  fin_cases first <;> fin_cases second
  all_goals norm_num [allSureDisplacement] at heq
  all_goals rfl

theorem affine_responseInvariant_finite_injective_of_nonzero_scale
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
      allSureDisplacement := by
    funext player
    simp only [affine_allSure_displacement_eq, affine_singletonMatrix,
      ← Finset.mul_sum, singleton_rowSum_eq, mul_one]
    field_simp [hscale player]
  rw [heq]
  exact allSure_displacement_injective

/-- Every actual response-invariant partition is discrete, with arbitrary label type. -/
theorem affine_responseInvariant_injective_of_nonzero_scale
    (scale shift : Payoff (Fin 4)) (hscale : ∀ player, scale player ≠ 0)
    {κ : Type*} (block : Fin 4 → κ)
    (hresponse : QuittingResponseInvariantOnUnitCube
      (quittingPlayerwiseAffineReward reward scale shift) block) :
    Function.Injective block := by
  obtain ⟨compressed, hsame, hinvariant⟩ := exists_responseInvariant_finite_compression
    (quittingPlayerwiseAffineReward reward scale shift) block hresponse
  have hinj := affine_responseInvariant_finite_injective_of_nonzero_scale
    scale shift hscale compressed hinvariant
  intro first second heq
  exact hinj ((hsame first second).mpr heq)

theorem affine_responseInvariant_injective
    (scale shift : Payoff (Fin 4)) (hscale : ∀ player, 0 < scale player)
    {κ : Type*} (block : Fin 4 → κ)
    (hresponse : QuittingResponseInvariantOnUnitCube
      (quittingPlayerwiseAffineReward reward scale shift) block) :
    Function.Injective block :=
  affine_responseInvariant_injective_of_nonzero_scale scale shift
    (fun player => (hscale player).ne') block hresponse

theorem responseInvariant_injective {κ : Type*} (block : Fin 4 → κ)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block) :
    Function.Injective block := by
  have haffine : quittingPlayerwiseAffineReward reward (fun _ => 1) (fun _ => 0) =
      reward := by
    funext terminal player
    simp only [quittingPlayerwiseAffineReward, one_mul, add_zero]
  apply affine_responseInvariant_injective_of_nonzero_scale
    (fun _ => 1) (fun _ => 0) (fun _ => one_ne_zero) block
  rwa [haffine]

end GameTheory.BelowSingletonJointPhaseFixture
