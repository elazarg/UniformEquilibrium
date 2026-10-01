import UniformEquilibrium.Quitting.Examples.StrictPatientWithdrawalTable
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotient
import UniformEquilibrium.Quitting.Stationary.RewardCoordinatePerturbation

/-! # Actual residual witnesses exclude every nondiscrete patient response partition

The all-Quit residual separates every pair except zero and one. A second,
block-constant singleton-two row separates that last pair. Both witnesses
remain valid throughout the full sixty-coordinate radius-1/100 reward ball.
-/

noncomputable section

namespace GameTheory.StrictPatientWithdrawal

open GuardedCrossedResponseExamples QuittingFinFourEndpointRows Math.Finset

def singletonTwoHazard (who : Fin 4) : ℝ := if who = 2 then 1 else 0

private theorem allQuit_sigma (who : Fin 4) :
    sigmaValue (weightOfReward reward) (fun _ ↦ 1) who = ![1, 0, -1, 1 / 2] who := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases who
  all_goals
    simp only [pureQuitEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ]
    norm_num +decide [weightOfReward, reward, coalitionCode]

private theorem allQuit_excluded (who : Fin 4) :
    excludedValue (weightOfReward reward) (fun _ ↦ 1) who = ![0, -1, 1, 0] who := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases who
  all_goals
    simp only [excludedEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ]
    norm_num +decide [weightOfReward, reward, coalitionCode]

theorem allQuit_displacement (who : Fin 4) :
    quittingDiscountedDisplacement reward 0 (fun _ ↦ 1) who = ![1, 1, -2, 1 / 2] who := by
  have hmass : continueMassExcl (fun _ : Fin 4 ↦ (1 : ℝ)) who = 0 := by
    norm_num [continueMassExcl, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ who)]
  rw [quittingDiscountedDisplacement, allQuit_sigma, allQuit_excluded, hmass]
  fin_cases who <;> norm_num

private theorem singletonTwo_sigma (who : Fin 4) :
    sigmaValue (weightOfReward reward) singletonTwoHazard who = ![2, -2, 0, 1] who := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases who
  all_goals
    simp only [pureQuitEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ,
      singletonTwoHazard]
    norm_num +decide [weightOfReward, reward, coalitionCode]

private theorem singletonTwo_excluded (who : Fin 4) :
    excludedValue (weightOfReward reward) singletonTwoHazard who = ![0, -1, 0, 3] who := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases who
  all_goals simp only [excludedEndpointRowSum, Fin.sum_univ_succ]
  all_goals simp +decide [opponentCoalitionMass, finFourCoalitionOfRow,
    Fin.prod_univ_succ, singletonTwoHazard]
  all_goals norm_num +decide [weightOfReward, reward, coalitionCode]

theorem singletonTwo_displacement (who : Fin 4) :
    quittingDiscountedDisplacement reward 0 singletonTwoHazard who = ![2, -1, 0, -2] who := by
  have hmass : continueMassExcl singletonTwoHazard who = ![0, 0, 1, 0] who := by
    fin_cases who
    · change continueMassExcl singletonTwoHazard (0 : Fin 4) = 0
      rw [continueMassExcl, show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
      norm_num [singletonTwoHazard]
    · change continueMassExcl singletonTwoHazard (1 : Fin 4) = 0
      rw [continueMassExcl, show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
      norm_num [singletonTwoHazard]
    · change continueMassExcl singletonTwoHazard (2 : Fin 4) = 1
      rw [continueMassExcl, show Finset.univ.erase (2 : Fin 4) = {0, 1, 3} by decide]
      norm_num [singletonTwoHazard]
    · change continueMassExcl singletonTwoHazard (3 : Fin 4) = 0
      rw [continueMassExcl, show Finset.univ.erase (3 : Fin 4) = {0, 1, 2} by decide]
      norm_num [singletonTwoHazard]
  rw [quittingDiscountedDisplacement, singletonTwo_sigma, singletonTwo_excluded, hmass]
  fin_cases who <;> norm_num

/-- The fixed-row error is derived from actual Quit/Continue reward sums. -/
theorem abs_displacement_sub_le_two_mul_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (hazard : Fin 4 → ℝ) (hbox : ∀ who, 0 ≤ hazard who ∧ hazard who ≤ 1) (who : Fin 4) :
    |quittingDiscountedDisplacement other 0 hazard who -
      quittingDiscountedDisplacement reward 0 hazard who| ≤ 2 * error := by
  have herror : 0 ≤ error := (abs_nonneg _).trans
    (hclose ⟨{0}, Finset.singleton_nonempty 0⟩ 0)
  have hmass : 0 ≤ continueMassExcl hazard who :=
    Finset.prod_nonneg (fun coordinate _ => sub_nonneg.mpr (hbox coordinate).2)
  have h := abs_quittingDiscountedDisplacement_sub_le_of_coordinate_error reward other error
    hclose hazard who (fun coordinate _ => hbox coordinate)
  exact h.trans ((mul_le_mul_of_nonneg_left (sub_le_self 1 hmass)
    (mul_nonneg (by norm_num) herror)).trans_eq (mul_one _))

private theorem displacement_ne_of_coordinate_error_gap
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (hazard : Fin 4 → ℝ) (hbox : ∀ who, 0 ≤ hazard who ∧ hazard who ≤ 1)
    (first second : Fin 4)
    (hgap : 4 * error < |quittingDiscountedDisplacement reward 0 hazard first -
      quittingDiscountedDisplacement reward 0 hazard second|) :
    quittingDiscountedDisplacement other 0 hazard first ≠
      quittingDiscountedDisplacement other 0 hazard second := by
  intro hequal
  have h := Maths.FiniteInequality.abs_sub_differences_le
    (quittingDiscountedDisplacement reward 0 hazard first)
    (quittingDiscountedDisplacement reward 0 hazard second)
    (quittingDiscountedDisplacement other 0 hazard first)
    (quittingDiscountedDisplacement other 0 hazard second) (2 * error)
    (abs_displacement_sub_le_two_mul_of_coordinate_error other error hclose hazard hbox first)
    (abs_displacement_sub_le_two_mul_of_coordinate_error other error hclose hazard hbox second)
  rw [hequal, sub_self, zero_sub, abs_neg] at h
  linarith

private theorem allQuit_gap (first second : Fin 4) (hne : first ≠ second)
    (hforward : ¬ (first = 0 ∧ second = 1))
    (hbackward : ¬ (first = 1 ∧ second = 0)) :
    1 / 2 ≤ |quittingDiscountedDisplacement reward 0 (fun _ ↦ 1) first -
      quittingDiscountedDisplacement reward 0 (fun _ ↦ 1) second| := by
  rw [allQuit_displacement, allQuit_displacement]
  fin_cases first
  all_goals fin_cases second
  all_goals norm_num at hne
  all_goals norm_num at hforward
  all_goals norm_num at hbackward
  all_goals norm_num

/-- Every actual response-invariant block map on the stated full reward ball is injective. -/
theorem block_injective_of_coordinate_error_responseInvariant {k : ℕ}
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (herror : error < 1 / 100)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (block : Fin 4 → Fin k) (hresponse : QuittingResponseInvariantOnUnitCube other block) :
    Function.Injective block := by
  have hnotBlock (first second : Fin 4) (hne : first ≠ second)
      (hforward : ¬ (first = 0 ∧ second = 1))
      (hbackward : ¬ (first = 1 ∧ second = 0)) : block first ≠ block second := by
    intro hblock
    have hequal := hresponse (fun _ ↦ 1) (by intro coordinate; norm_num) first second hblock
    change quittingDiscountedDisplacement other 0 (fun _ ↦ 1) first =
      quittingDiscountedDisplacement other 0 (fun _ ↦ 1) second at hequal
    have hgap := allQuit_gap first second hne hforward hbackward
    exact (displacement_ne_of_coordinate_error_gap other error hclose (fun _ ↦ 1)
      (by intro who; norm_num) first second (by linarith)) hequal
  have htwo (who : Fin 4) (hne : who ≠ 2) : block who ≠ block 2 :=
    hnotBlock who 2 hne
      (fun h => (by decide : (2 : Fin 4) ≠ 1) h.2)
      (fun h => (by decide : (2 : Fin 4) ≠ 0) h.2)
  have hfirstPair : block 0 ≠ block 1 := by
    intro hblock
    let point : Fin k → ℝ := fun coordinate => if coordinate = block 2 then 1 else 0
    have hpoint : ∀ coordinate, 0 ≤ point coordinate ∧ point coordinate ≤ 1 := by
      intro coordinate
      dsimp only [point]
      split_ifs <;> norm_num
    have hlift : quittingBlockLift block point = singletonTwoHazard := by
      funext who
      by_cases hequal : who = 2
      · subst who
        simp [quittingBlockLift, point, singletonTwoHazard]
      · simp only [quittingBlockLift, point, singletonTwoHazard, ite_eq_right hequal,
          ite_eq_right (htwo who hequal)]
    have hequal := hresponse point hpoint 0 1 hblock
    rw [hlift] at hequal
    have hbox : ∀ who, 0 ≤ singletonTwoHazard who ∧ singletonTwoHazard who ≤ 1 := by
      intro who
      unfold singletonTwoHazard
      split_ifs <;> norm_num
    apply (displacement_ne_of_coordinate_error_gap other error hclose singletonTwoHazard
      hbox 0 1 ?_) hequal
    rw [singletonTwo_displacement, singletonTwo_displacement]
    norm_num
    linarith
  intro first second hblock
  by_contra hne
  by_cases hforward : first = 0 ∧ second = 1
  · rcases hforward with ⟨rfl, rfl⟩
    exact hfirstPair hblock
  by_cases hbackward : first = 1 ∧ second = 0
  · rcases hbackward with ⟨rfl, rfl⟩
    exact hfirstPair hblock.symm
  exact hnotBlock first second hne hforward hbackward hblock

theorem block_injective_of_responseInvariant {k : ℕ}
    (block : Fin 4 → Fin k) (hresponse : QuittingResponseInvariantOnUnitCube reward block) :
    Function.Injective block :=
  block_injective_of_coordinate_error_responseInvariant reward 0 (by norm_num)
    (fun terminal who => by simp) block hresponse

/-- The metric is the ordinary nested Pi sup metric on all sixty raw reward entries. -/
theorem block_injective_of_dist_lt_responseInvariant {k : ℕ}
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 100)
    (block : Fin 4 → Fin k) (hresponse : QuittingResponseInvariantOnUnitCube other block) :
    Function.Injective block := by
  apply block_injective_of_coordinate_error_responseInvariant
    other (dist other reward) hclose _ block hresponse
  intro terminal who
  simpa only [Real.dist_eq] using
    (dist_le_pi_dist (other terminal) (reward terminal) who).trans
      (dist_le_pi_dist other reward terminal)

end GameTheory.StrictPatientWithdrawal
