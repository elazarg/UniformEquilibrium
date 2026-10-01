import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponsePartitionSeparation

/-! # Six literal block-constant response-partition witnesses

The exact printed witnesses supplement, rather than replace, the stronger
all-half injectivity theorem. No response-invariance hypothesis is needed
to compute their actual original-game residual differences.
-/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open QuittingFinFourEndpointRows Math.Finset

/-- Rows encode 01/2/3, 12/03, 02/13, 0/1/23, 01/23, and 0123, respectively. -/
def halfCeilingPartitionWitnessBlock (row : Fin 6) : Fin 4 → Fin 3 :=
  ![![0, 0, 1, 2], ![0, 1, 1, 0], ![0, 1, 0, 1],
    ![0, 1, 2, 2], ![0, 0, 1, 1], ![0, 0, 0, 0]] row

def halfCeilingPartitionWitnessPoint (row : Fin 6) : Fin 3 → ℝ :=
  ![![0, 1 / 2, 0], ![1 / 2, 0, 0], ![0, 1 / 2, 0],
    ![0, 0, 1 / 2], ![0, 1 / 2, 0], ![1 / 2, 1 / 2, 1 / 2]] row

def halfCeilingPartitionWitnessHazard (row : Fin 6) : Fin 4 → ℝ :=
  ![![0, 0, 1 / 2, 0], ![1 / 2, 0, 0, 1 / 2], ![0, 1 / 2, 0, 1 / 2],
    ![0, 0, 1 / 2, 1 / 2], ![0, 0, 1 / 2, 1 / 2],
    ![1 / 2, 1 / 2, 1 / 2, 1 / 2]] row

def halfCeilingPartitionWitnessFirst (row : Fin 6) : Fin 4 :=
  ![0, 1, 0, 2, 0, 0] row

def halfCeilingPartitionWitnessSecond (row : Fin 6) : Fin 4 :=
  ![1, 2, 2, 3, 1, 1] row

def halfCeilingPartitionWitnessDifference (row : Fin 6) : ℝ :=
  ![-115 / 1092, 5 / 16, 9 / 8, -3 / 4, -115 / 1456, -115 / 2496] row

theorem halfCeilingPartitionWitness_blockLift (row : Fin 6) :
    quittingBlockLift (halfCeilingPartitionWitnessBlock row)
        (halfCeilingPartitionWitnessPoint row) = halfCeilingPartitionWitnessHazard row := by
  funext who
  fin_cases row <;> fin_cases who <;>
    norm_num [quittingBlockLift, halfCeilingPartitionWitnessBlock,
      halfCeilingPartitionWitnessPoint, halfCeilingPartitionWitnessHazard]

theorem halfCeilingPartitionWitness_point_mem_cube (row : Fin 6) (coordinate : Fin 3) :
    0 ≤ halfCeilingPartitionWitnessPoint row coordinate ∧
      halfCeilingPartitionWitnessPoint row coordinate ≤ 1 := by
  fin_cases row <;> fin_cases coordinate <;> norm_num [halfCeilingPartitionWitnessPoint]

theorem halfCeilingPartitionWitness_same_block (row : Fin 6) :
    halfCeilingPartitionWitnessBlock row (halfCeilingPartitionWitnessFirst row) =
      halfCeilingPartitionWitnessBlock row (halfCeilingPartitionWitnessSecond row) := by
  fin_cases row <;> decide

private theorem witness_zero_difference :
    quittingDiscountedDisplacement halfCeilingReward 0 (![0, 0, 1 / 2, 0]) 1 -
      quittingDiscountedDisplacement halfCeilingReward 0 (![0, 0, 1 / 2, 0]) 0 =
        -115 / 1092 := by
  simp only [quittingDiscountedDisplacement, sigmaValue_eq_pureQuitEndpointRowSum,
    excludedValue_eq_excludedEndpointRowSum, pureQuitEndpointRowSum,
    excludedEndpointRowSum, Fin.sum_univ_succ]
  simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ]
  simp only [continueMassExcl,
    show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide,
    show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
  norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode, Finset.prod_insert]

private theorem witness_one_difference :
    quittingDiscountedDisplacement halfCeilingReward 0 (![1 / 2, 0, 0, 1 / 2]) 2 -
      quittingDiscountedDisplacement halfCeilingReward 0 (![1 / 2, 0, 0, 1 / 2]) 1 =
        5 / 16 := by
  simp only [quittingDiscountedDisplacement, sigmaValue_eq_pureQuitEndpointRowSum,
    excludedValue_eq_excludedEndpointRowSum, pureQuitEndpointRowSum,
    excludedEndpointRowSum, Fin.sum_univ_succ]
  simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ]
  simp only [continueMassExcl,
    show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide,
    show Finset.univ.erase (2 : Fin 4) = {0, 1, 3} by decide]
  norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode, Finset.prod_insert]

private theorem witness_two_difference :
    quittingDiscountedDisplacement halfCeilingReward 0 (![0, 1 / 2, 0, 1 / 2]) 2 -
      quittingDiscountedDisplacement halfCeilingReward 0 (![0, 1 / 2, 0, 1 / 2]) 0 =
        9 / 8 := by
  simp only [quittingDiscountedDisplacement, sigmaValue_eq_pureQuitEndpointRowSum,
    excludedValue_eq_excludedEndpointRowSum, pureQuitEndpointRowSum,
    excludedEndpointRowSum, Fin.sum_univ_succ]
  simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ]
  simp only [continueMassExcl,
    show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide,
    show Finset.univ.erase (2 : Fin 4) = {0, 1, 3} by decide]
  norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode, Finset.prod_insert]

private theorem witness_three_difference :
    quittingDiscountedDisplacement halfCeilingReward 0 (![0, 0, 1 / 2, 1 / 2]) 3 -
      quittingDiscountedDisplacement halfCeilingReward 0 (![0, 0, 1 / 2, 1 / 2]) 2 =
        -3 / 4 := by
  simp only [quittingDiscountedDisplacement, sigmaValue_eq_pureQuitEndpointRowSum,
    excludedValue_eq_excludedEndpointRowSum, pureQuitEndpointRowSum,
    excludedEndpointRowSum, Fin.sum_univ_succ]
  simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ]
  simp only [continueMassExcl,
    show Finset.univ.erase (2 : Fin 4) = {0, 1, 3} by decide,
    show Finset.univ.erase (3 : Fin 4) = {0, 1, 2} by decide]
  norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode, Finset.prod_insert]

private theorem witness_four_difference :
    quittingDiscountedDisplacement halfCeilingReward 0 (![0, 0, 1 / 2, 1 / 2]) 1 -
      quittingDiscountedDisplacement halfCeilingReward 0 (![0, 0, 1 / 2, 1 / 2]) 0 =
        -115 / 1456 := by
  simp only [quittingDiscountedDisplacement, sigmaValue_eq_pureQuitEndpointRowSum,
    excludedValue_eq_excludedEndpointRowSum, pureQuitEndpointRowSum,
    excludedEndpointRowSum, Fin.sum_univ_succ]
  simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ]
  simp only [continueMassExcl,
    show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide,
    show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
  norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode, Finset.prod_insert]

/-- Every printed nonzero difference is an exact evaluation of the actual table. -/
theorem halfCeilingPartitionWitness_displacement_difference (row : Fin 6) :
    quittingDiscountedDisplacement halfCeilingReward 0 (halfCeilingPartitionWitnessHazard row)
        (halfCeilingPartitionWitnessSecond row) -
      quittingDiscountedDisplacement halfCeilingReward 0 (halfCeilingPartitionWitnessHazard row)
        (halfCeilingPartitionWitnessFirst row) = halfCeilingPartitionWitnessDifference row := by
  fin_cases row
  · exact witness_zero_difference
  · exact witness_one_difference
  · exact witness_two_difference
  · exact witness_three_difference
  · exact witness_four_difference
  · exact halfCeiling_allHalf_selectedDifference

theorem halfCeilingPartitionWitness_difference_ne_zero (row : Fin 6) :
    halfCeilingPartitionWitnessDifference row ≠ 0 := by
  fin_cases row <;> norm_num [halfCeilingPartitionWitnessDifference]

/-- Each literal block map fails the canonical raw response-invariance definition. -/
theorem halfCeilingPartitionWitness_not_responseInvariant (row : Fin 6) :
    ¬QuittingResponseInvariantOnUnitCube halfCeilingReward
      (halfCeilingPartitionWitnessBlock row) := by
  intro hinvariant
  have heq := hinvariant (halfCeilingPartitionWitnessPoint row)
    (halfCeilingPartitionWitness_point_mem_cube row)
    (halfCeilingPartitionWitnessFirst row) (halfCeilingPartitionWitnessSecond row)
    (halfCeilingPartitionWitness_same_block row)
  rw [halfCeilingPartitionWitness_blockLift] at heq
  have hdifference := halfCeilingPartitionWitness_displacement_difference row
  rw [heq, sub_self] at hdifference
  exact halfCeilingPartitionWitness_difference_ne_zero row hdifference.symm

end GameTheory.GuardedCrossedResponseExamples
