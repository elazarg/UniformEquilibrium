import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseTables
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotient

/-! # Literal all-half witnesses exclude every nondiscrete response-invariant block map -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open QuittingFinFourEndpointRows Math.Finset

private theorem half_allHalf_sigma (who : Fin 4) :
    sigmaValue (weightOfReward halfCeilingReward) (fun _ ↦ 1 / 2) who =
      ![-1 / 3, -1009 / 728, 131 / 28, 1 / 4] who := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases who
  all_goals
    simp only [pureQuitEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ]
    norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode]

private theorem half_allHalf_excluded (who : Fin 4) :
    excludedValue (weightOfReward halfCeilingReward) (fun _ ↦ 1 / 2) who =
      ![7 / 8, 0, 283 / 56, 0] who := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases who
  all_goals
    simp only [excludedEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ]
    norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode]

private theorem unit_allHalf_sigma (who : Fin 4) :
    sigmaValue (weightOfReward unitCeilingReward) (fun _ ↦ 1 / 2) who =
      ![-1 / 2, 1 / 4, -1 / 4, 1 / 4] who := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases who
  all_goals
    simp only [pureQuitEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ]
    norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode]

private theorem unit_allHalf_excluded (who : Fin 4) :
    excludedValue (weightOfReward unitCeilingReward) (fun _ ↦ 1 / 2) who =
      ![-1 / 8, 1 / 4, 1 / 2, 3 / 4] who := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases who
  all_goals
    simp only [excludedEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ]
    norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode]

private theorem allHalf_continueMassExcl (who : Fin 4) :
    continueMassExcl (fun _ : Fin 4 ↦ (1 / 2 : ℝ)) who = 1 / 8 := by
  norm_num [continueMassExcl, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ who)]

theorem halfCeiling_allHalf_displacement (who : Fin 4) :
    quittingDiscountedDisplacement halfCeilingReward 0 (fun _ ↦ 1 / 2) who =
      ![-7 / 6, -1009 / 832, -215 / 224, 7 / 32] who := by
  rw [quittingDiscountedDisplacement, half_allHalf_sigma, half_allHalf_excluded,
    allHalf_continueMassExcl]
  fin_cases who <;> norm_num

theorem unitCeiling_allHalf_displacement (who : Fin 4) :
    quittingDiscountedDisplacement unitCeilingReward 0 (fun _ ↦ 1 / 2) who =
      ![-5 / 16, -1 / 32, -23 / 32, -17 / 32] who := by
  rw [quittingDiscountedDisplacement, unit_allHalf_sigma, unit_allHalf_excluded,
    allHalf_continueMassExcl]
  fin_cases who <;> norm_num

/-- The source's merged selected pair already fails invariance at the all-half point. -/
theorem halfCeiling_allHalf_selectedDifference :
    quittingDiscountedDisplacement halfCeilingReward 0 (fun _ ↦ 1 / 2) 1 -
      quittingDiscountedDisplacement halfCeilingReward 0 (fun _ ↦ 1 / 2) 0 =
        -115 / 2496 := by
  rw [halfCeiling_allHalf_displacement, halfCeiling_allHalf_displacement]
  norm_num

/-- Raw response invariance can identify no two distinct players in the half table. -/
theorem halfCeiling_block_injective_of_responseInvariant {k : ℕ}
    (block : Fin 4 → Fin k)
    (hresponse : QuittingResponseInvariantOnUnitCube halfCeilingReward block) :
    Function.Injective block := by
  intro first second hblock
  have heq := hresponse (fun _ ↦ 1 / 2) (by intro coordinate; norm_num)
    first second hblock
  change quittingDiscountedDisplacement halfCeilingReward 0 (fun _ ↦ 1 / 2) first =
    quittingDiscountedDisplacement halfCeilingReward 0 (fun _ ↦ 1 / 2) second at heq
  rw [halfCeiling_allHalf_displacement, halfCeiling_allHalf_displacement] at heq
  fin_cases first <;> fin_cases second
  all_goals first | rfl | norm_num at heq

/-- Raw response invariance can identify no two distinct players in the unit table. -/
theorem unitCeiling_block_injective_of_responseInvariant {k : ℕ}
    (block : Fin 4 → Fin k)
    (hresponse : QuittingResponseInvariantOnUnitCube unitCeilingReward block) :
    Function.Injective block := by
  intro first second hblock
  have heq := hresponse (fun _ ↦ 1 / 2) (by intro coordinate; norm_num)
    first second hblock
  change quittingDiscountedDisplacement unitCeilingReward 0 (fun _ ↦ 1 / 2) first =
    quittingDiscountedDisplacement unitCeilingReward 0 (fun _ ↦ 1 / 2) second at heq
  rw [unitCeiling_allHalf_displacement, unitCeiling_allHalf_displacement] at heq
  fin_cases first <;> fin_cases second
  all_goals first | rfl | norm_num at heq

end GameTheory.GuardedCrossedResponseExamples
