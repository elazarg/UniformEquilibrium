import UniformEquilibrium.Quitting.Examples.StrictDeadlineWithdrawalTable
import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponsePartitionNeighborhood

/-! # Literal and robust response-partition exclusions for the deadline table

The common half-hazard point is block-constant for every partition. Its
actual displacement coordinates have separation at least 11/64. Existing
actual reward-coordinate perturbation bounds preserve this at radius 1/512.
-/

noncomputable section

namespace GameTheory.StrictDeadlineWithdrawal

open GuardedCrossedResponseExamples QuittingFinFourEndpointRows Math.Finset

private theorem allHalf_sigma (who : Fin 4) :
    sigmaValue (weightOfReward reward) (fun _ ↦ 1 / 2) who =
      ![3 / 8, -1 / 16, -1 / 16, -1 / 16] who := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases who
  all_goals simp only [pureQuitEndpointRowSum, Fin.sum_univ_succ]
  all_goals simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ]
  all_goals norm_num +decide [weightOfReward, reward, integerReward, terminalShift, coalitionCode]

private theorem allHalf_excluded (who : Fin 4) :
    excludedValue (weightOfReward reward) (fun _ ↦ 1 / 2) who =
      ![7 / 8, 9 / 128, -23 / 128, 41 / 128] who := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases who
  all_goals simp only [excludedEndpointRowSum, Fin.sum_univ_succ]
  all_goals simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ]
  all_goals norm_num +decide [weightOfReward, reward, integerReward, terminalShift, coalitionCode]

theorem allHalf_displacement (who : Fin 4) :
    quittingDiscountedDisplacement reward 0 (fun _ ↦ 1 / 2) who =
      ![-35 / 64, -1 / 8, 1 / 8, -3 / 8] who := by
  have hmass : continueMassExcl (fun _ : Fin 4 ↦ (1 / 2 : ℝ)) who = 1 / 8 := by
    norm_num [continueMassExcl, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ who)]
  rw [quittingDiscountedDisplacement, allHalf_sigma, allHalf_excluded, hmass]
  fin_cases who <;> norm_num

theorem allHalf_separation (first second : Fin 4) (hne : first ≠ second) :
    11 / 64 ≤ |quittingDiscountedDisplacement reward 0 (fun _ ↦ 1 / 2) first -
      quittingDiscountedDisplacement reward 0 (fun _ ↦ 1 / 2) second| := by
  rw [allHalf_displacement, allHalf_displacement]
  fin_cases first
  all_goals fin_cases second
  all_goals try exact (hne rfl).elim
  all_goals norm_num

/-- All nondiscrete response-invariant partitions are excluded on the exact raw ball. -/
theorem block_injective_of_coordinate_error_responseInvariant {k : ℕ}
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (herror : error < 1 / 512)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (block : Fin 4 → Fin k) (hresponse : QuittingResponseInvariantOnUnitCube other block) :
    Function.Injective block := by
  intro first second hblock
  have heq := hresponse (fun _ ↦ 1 / 2) (by intro coordinate; norm_num) first second hblock
  change quittingDiscountedDisplacement other 0 (fun _ ↦ 1 / 2) first =
    quittingDiscountedDisplacement other 0 (fun _ ↦ 1 / 2) second at heq
  by_contra hne
  have hgap := allHalf_separation first second hne
  have h := Maths.FiniteInequality.abs_sub_differences_le
    (quittingDiscountedDisplacement reward 0 (fun _ ↦ 1 / 2) first)
    (quittingDiscountedDisplacement reward 0 (fun _ ↦ 1 / 2) second)
    (quittingDiscountedDisplacement other 0 (fun _ ↦ 1 / 2) first)
    (quittingDiscountedDisplacement other 0 (fun _ ↦ 1 / 2) second) (7 * error / 4)
    (abs_allHalf_displacement_sub_le_of_coordinate_error reward other error hclose first)
    (abs_allHalf_displacement_sub_le_of_coordinate_error reward other error hclose second)
  rw [heq, sub_self, zero_sub, abs_neg] at h
  linarith

theorem block_injective_of_responseInvariant {k : ℕ}
    (block : Fin 4 → Fin k) (hresponse : QuittingResponseInvariantOnUnitCube reward block) :
    Function.Injective block := by
  apply block_injective_of_coordinate_error_responseInvariant reward 0 (by norm_num) _
    block hresponse
  intro terminal who
  simp only [sub_self, abs_zero, le_refl]

theorem block_injective_of_dist_lt_responseInvariant {k : ℕ}
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512)
    (block : Fin 4 → Fin k) (hresponse : QuittingResponseInvariantOnUnitCube other block) :
    Function.Injective block := by
  apply block_injective_of_coordinate_error_responseInvariant
    other (dist other reward) hclose _ block hresponse
  intro terminal who
  simpa only [Real.dist_eq] using
    (dist_le_pi_dist (other terminal) (reward terminal) who).trans
      (dist_le_pi_dist other reward terminal)

end GameTheory.StrictDeadlineWithdrawal
