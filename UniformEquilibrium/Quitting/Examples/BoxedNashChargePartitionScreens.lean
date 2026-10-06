import MathUE.LinearProgramming.CyclicChildSharedPartitionScreens
import UniformEquilibrium.Quitting.Examples.BoxedNashChargeSharedMatrix
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotient

/-! # Thirteen actual boxed response-quotient exclusions

The full and proper-triple reward tables consume the same thirteen matrix
witnesses through their checked singleton-matrix bindings. The remaining
candidate partition needs the nonlinear full-table response, not this screen.
-/

noncomputable section

namespace GameTheory.BoxedNashChargeSharedMatrix

open Math.CyclicChildJointPhase.SharedFixture

theorem full_singletonPartitionRowSum_eq (entry : Fin 13)
    (receiver coordinate : Fin 4) :
    quittingSingletonBlockRowSum BoxedNashChargeFullCoreFixture.reward
      (excludedPartition entry) receiver coordinate =
        singletonPartitionRowSum (excludedPartition entry) receiver coordinate := by
  unfold quittingSingletonBlockRowSum singletonPartitionRowSum
  rw [full_singletonMatrix_eq]

theorem full_excludedPartition_not_responseInvariant (entry : Fin 13) :
    ¬QuittingResponseInvariantOnUnitCube BoxedNashChargeFullCoreFixture.reward
      (excludedPartition entry) := by
  intro hinvariant
  have heq := quittingSingletonBlockRowSum_eq_of_responseInvariant
    BoxedNashChargeFullCoreFixture.reward (excludedPartition entry) hinvariant
    (partitionFirst entry) (partitionSecond entry) (excludedPartition_same_block entry)
    (partitionColumn entry)
  rw [full_singletonPartitionRowSum_eq, full_singletonPartitionRowSum_eq] at heq
  exact excludedPartition_row_sums_ne entry heq

def tripleExcludedPartition (entry : Fin 13) (player : Fin 4) : Fin 4 :=
  excludedPartition entry (canonicalToTriple.symm player)

theorem triple_singletonPartitionRowSum_eq (entry : Fin 13)
    (receiver coordinate : Fin 4) :
    quittingSingletonBlockRowSum BoxedNashChargeTripleFixture.reward
      (tripleExcludedPartition entry) (canonicalToTriple receiver) coordinate =
        singletonPartitionRowSum (excludedPartition entry) receiver coordinate := by
  unfold quittingSingletonBlockRowSum singletonPartitionRowSum
  rw [← canonicalToTriple.sum_comp (fun owner =>
    if tripleExcludedPartition entry owner = coordinate then
      QuittingLCPClassification.quittingSingletonMatrix BoxedNashChargeTripleFixture.reward
        (canonicalToTriple receiver) owner else 0)]
  simp only [tripleExcludedPartition, Equiv.symm_apply_apply]
  change (∑ owner, if excludedPartition entry owner = coordinate then
    Matrix.submatrix
      (QuittingLCPClassification.quittingSingletonMatrix BoxedNashChargeTripleFixture.reward)
      canonicalToTriple canonicalToTriple receiver owner else 0) = _
  rw [triple_singletonMatrix_relabel_eq]

theorem triple_excludedPartition_not_responseInvariant (entry : Fin 13) :
    ¬QuittingResponseInvariantOnUnitCube BoxedNashChargeTripleFixture.reward
      (tripleExcludedPartition entry) := by
  intro hinvariant
  have hsame : tripleExcludedPartition entry (canonicalToTriple (partitionFirst entry)) =
      tripleExcludedPartition entry (canonicalToTriple (partitionSecond entry)) := by
    simpa only [tripleExcludedPartition, Equiv.symm_apply_apply] using
      excludedPartition_same_block entry
  have heq := quittingSingletonBlockRowSum_eq_of_responseInvariant
    BoxedNashChargeTripleFixture.reward (tripleExcludedPartition entry) hinvariant
    (canonicalToTriple (partitionFirst entry)) (canonicalToTriple (partitionSecond entry))
    hsame (partitionColumn entry)
  rw [triple_singletonPartitionRowSum_eq, triple_singletonPartitionRowSum_eq] at heq
  exact excludedPartition_row_sums_ne entry heq

end GameTheory.BoxedNashChargeSharedMatrix
