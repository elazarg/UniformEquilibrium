import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseTables
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawMatrix

/-! # Exact unswapped and crossed singleton indices of the literal tables -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open Math.LinearProgramming QuittingLCPClassification

theorem halfCeiling_singletonDegree_one :
    ∃ hR0 : IsR0Matrix (quittingSingletonMatrix halfCeilingReward),
      r0Degree (quittingSingletonMatrix halfCeilingReward) hR0 = 1 := by
  apply quittingSingletonMatrix_r0_degree_one_of_positiveInverse
  · rw [halfCeiling_singletonMatrix, sourceSingletonMatrix_det]
    norm_num
  · intro row column
    rw [halfCeiling_singletonMatrix]
    exact sourceSingletonMatrix_inverse_pos row column

theorem unitCeiling_singletonDegree_one :
    ∃ hR0 : IsR0Matrix (quittingSingletonMatrix unitCeilingReward),
      r0Degree (quittingSingletonMatrix unitCeilingReward) hR0 = 1 := by
  apply quittingSingletonMatrix_r0_degree_one_of_positiveInverse
  · rw [unitCeiling_singletonMatrix, sourceSingletonMatrix_det]
    norm_num
  · intro row column
    rw [unitCeiling_singletonMatrix]
    exact sourceSingletonMatrix_inverse_pos row column

theorem halfCeiling_crossedDegree_neg_one :
    ∃ hR0 : IsR0Matrix (quittingCrossedSingletonMatrix halfCeilingReward 0 1),
      r0Degree (quittingCrossedSingletonMatrix halfCeilingReward 0 1) hR0 = -1 := by
  apply quittingCrossedSingletonMatrix_r0_degree_neg_one_of_positiveInverse _ _ _ (by decide)
  · rw [halfCeiling_singletonMatrix, sourceSingletonMatrix_det]
    norm_num
  · intro row column
    rw [halfCeiling_singletonMatrix]
    exact sourceSingletonMatrix_inverse_pos row column

theorem unitCeiling_crossedDegree_neg_one :
    ∃ hR0 : IsR0Matrix (quittingCrossedSingletonMatrix unitCeilingReward 0 1),
      r0Degree (quittingCrossedSingletonMatrix unitCeilingReward 0 1) hR0 = -1 := by
  apply quittingCrossedSingletonMatrix_r0_degree_neg_one_of_positiveInverse _ _ _ (by decide)
  · rw [unitCeiling_singletonMatrix, sourceSingletonMatrix_det]
    norm_num
  · intro row column
    rw [unitCeiling_singletonMatrix]
    exact sourceSingletonMatrix_inverse_pos row column

end GameTheory.GuardedCrossedResponseExamples
