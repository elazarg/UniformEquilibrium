import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponsePartitionSeparation
import UniformEquilibrium.Quitting.Stationary.RewardCoordinatePerturbation

/-! # The literal unit reward ball excludes every nondiscrete response partition -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

/-- At the all-half row, the actual response error is the exact packet factor `7δ/4`. -/
theorem abs_allHalf_displacement_sub_le_of_coordinate_error
    (reward other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (who : Fin 4) :
    |quittingDiscountedDisplacement other 0 (fun _ ↦ 1 / 2) who -
      quittingDiscountedDisplacement reward 0 (fun _ ↦ 1 / 2) who| ≤ 7 * error / 4 := by
  have hmass : continueMassExcl (fun _ : Fin 4 ↦ (1 / 2 : ℝ)) who = 1 / 8 := by
    norm_num [continueMassExcl, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ who)]
  have h := abs_quittingDiscountedDisplacement_sub_le_of_coordinate_error reward other error
    hclose (fun _ ↦ 1 / 2) who (by intro coordinate _; norm_num)
  rw [hmass] at h
  exact h.trans_eq (by ring)

private theorem unitCeiling_allHalf_separation (first second : Fin 4) (hne : first ≠ second) :
    3 / 16 ≤ |quittingDiscountedDisplacement unitCeilingReward 0 (fun _ ↦ 1 / 2) first -
      quittingDiscountedDisplacement unitCeilingReward 0 (fun _ ↦ 1 / 2) second| := by
  rw [unitCeiling_allHalf_displacement, unitCeiling_allHalf_displacement]
  fin_cases first
  all_goals fin_cases second
  all_goals try exact (hne rfl).elim
  all_goals norm_num

/-- No raw response-invariant block can merge distinct players anywhere in the unit ball. -/
theorem unitCeiling_block_injective_of_coordinate_error_responseInvariant {k : ℕ}
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (herror : error < 1 / 1000)
    (hclose : ∀ terminal who, |other terminal who - unitCeilingReward terminal who| ≤ error)
    (block : Fin 4 → Fin k) (hresponse : QuittingResponseInvariantOnUnitCube other block) :
    Function.Injective block := by
  intro first second hblock
  have heq := hresponse (fun _ ↦ 1 / 2) (by intro coordinate; norm_num) first second hblock
  change quittingDiscountedDisplacement other 0 (fun _ ↦ 1 / 2) first =
    quittingDiscountedDisplacement other 0 (fun _ ↦ 1 / 2) second at heq
  by_contra hne
  have hgap := unitCeiling_allHalf_separation first second hne
  have h := Maths.FiniteInequality.abs_sub_differences_le
    (quittingDiscountedDisplacement unitCeilingReward 0 (fun _ ↦ 1 / 2) first)
    (quittingDiscountedDisplacement unitCeilingReward 0 (fun _ ↦ 1 / 2) second)
    (quittingDiscountedDisplacement other 0 (fun _ ↦ 1 / 2) first)
    (quittingDiscountedDisplacement other 0 (fun _ ↦ 1 / 2) second) (7 * error / 4)
    (abs_allHalf_displacement_sub_le_of_coordinate_error unitCeilingReward other
      error hclose first)
    (abs_allHalf_displacement_sub_le_of_coordinate_error unitCeilingReward other
      error hclose second)
  rw [heq, sub_self, zero_sub, abs_neg] at h
  linarith

/-- The literal ordinary Pi-sup ball excludes all nondiscrete response quotients. -/
theorem unitCeiling_block_injective_of_dist_lt_responseInvariant {k : ℕ}
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other unitCeilingReward < 1 / 1000)
    (block : Fin 4 → Fin k) (hresponse : QuittingResponseInvariantOnUnitCube other block) :
    Function.Injective block := by
  apply unitCeiling_block_injective_of_coordinate_error_responseInvariant
    other (dist other unitCeilingReward) hclose _ block hresponse
  intro terminal who
  simpa only [Real.dist_eq] using
    (dist_le_pi_dist (other terminal) (unitCeilingReward terminal) who).trans
      (dist_le_pi_dist other unitCeilingReward terminal)

end GameTheory.GuardedCrossedResponseExamples
