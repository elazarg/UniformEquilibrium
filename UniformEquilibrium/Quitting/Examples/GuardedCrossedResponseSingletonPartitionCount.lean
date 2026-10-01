import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseTables
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotient

/-! # The fourteen canonical nondiscrete partitions and their singleton row-sum test

Four triple blocks, six single-pair blocks, three double-pair blocks, and the full block
are encoded explicitly. Exactly eight fail the necessary singleton-matrix test.
Passing this linear test is not asserted to imply response invariance.
-/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

/-- Canonical block maps, in order:
012/3, 013/2, 023/1, 0/123;
01/2/3, 02/1/3, 03/1/2, 0/12/3, 0/13/2, 0/1/23;
01/23, 02/13, 03/12; 0123.
Unused block labels do not change the represented partition. -/
def crossedSourceNondiscretePartitionBlock (row : Fin 14) : Fin 4 → Fin 3 :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 1, 1, 1],
    ![0, 0, 1, 2], ![0, 1, 0, 2], ![0, 1, 2, 0],
    ![0, 1, 1, 2], ![0, 1, 2, 1], ![0, 1, 2, 2],
    ![0, 0, 1, 1], ![0, 1, 0, 1], ![0, 1, 1, 0], ![0, 0, 0, 0]] row

/-- The canonical necessary identity evaluated on the actual half-table singleton matrix. -/
def CrossedSourceSingletonPartitionRowsAgree (row : Fin 14) : Prop :=
  ∀ first second : Fin 4,
    crossedSourceNondiscretePartitionBlock row first =
        crossedSourceNondiscretePartitionBlock row second →
      ∀ coordinate : Fin 3,
        quittingSingletonBlockRowSum halfCeilingReward
            (crossedSourceNondiscretePartitionBlock row) first coordinate =
          quittingSingletonBlockRowSum halfCeilingReward
            (crossedSourceNondiscretePartitionBlock row) second coordinate

/-- The actual finite filter of failures of the canonical necessary row-sum identity. -/
def crossedSourceSingletonPartitionFailedRows : Finset (Fin 14) := by
  classical
  exact Finset.univ.filter (fun row => ¬ CrossedSourceSingletonPartitionRowsAgree row)

/-- The eight rejected rows: four triple blocks followed by the four cross-pair blocks. -/
def crossedSourceSingletonFailureIndex : Fin 8 → Fin 14 :=
  ![0, 1, 2, 3, 5, 6, 7, 8]

def crossedSourceSingletonFailureFirst : Fin 8 → Fin 4 :=
  ![2, 3, 0, 1, 0, 0, 1, 1]

def crossedSourceSingletonFailureSecond : Fin 8 → Fin 4 :=
  ![0, 0, 2, 2, 2, 3, 2, 3]

def crossedSourceSingletonFailureCoordinate : Fin 8 → Fin 3 :=
  ![1, 1, 1, 0, 1, 1, 0, 0]

private theorem singletonFailure_same_block_zero :
    crossedSourceNondiscretePartitionBlock 0 2 =
      crossedSourceNondiscretePartitionBlock 0 0 := by
  norm_num [crossedSourceNondiscretePartitionBlock]

private theorem singletonFailure_same_block_one :
    crossedSourceNondiscretePartitionBlock 1 3 =
      crossedSourceNondiscretePartitionBlock 1 0 := by
  norm_num [crossedSourceNondiscretePartitionBlock]

private theorem singletonFailure_same_block_two :
    crossedSourceNondiscretePartitionBlock 2 0 =
      crossedSourceNondiscretePartitionBlock 2 2 := by
  norm_num [crossedSourceNondiscretePartitionBlock]

private theorem singletonFailure_same_block_three :
    crossedSourceNondiscretePartitionBlock 3 1 =
      crossedSourceNondiscretePartitionBlock 3 2 := by
  norm_num [crossedSourceNondiscretePartitionBlock]

private theorem singletonFailure_same_block_four :
    crossedSourceNondiscretePartitionBlock 5 0 =
      crossedSourceNondiscretePartitionBlock 5 2 := by
  norm_num [crossedSourceNondiscretePartitionBlock]

private theorem singletonFailure_same_block_five :
    crossedSourceNondiscretePartitionBlock 6 0 =
      crossedSourceNondiscretePartitionBlock 6 3 := by
  norm_num [crossedSourceNondiscretePartitionBlock]

private theorem singletonFailure_same_block_six :
    crossedSourceNondiscretePartitionBlock 7 1 =
      crossedSourceNondiscretePartitionBlock 7 2 := by
  norm_num [crossedSourceNondiscretePartitionBlock]

private theorem singletonFailure_same_block_seven :
    crossedSourceNondiscretePartitionBlock 8 1 =
      crossedSourceNondiscretePartitionBlock 8 3 := by
  norm_num [crossedSourceNondiscretePartitionBlock]

theorem crossedSourceSingletonFailure_same_block (entry : Fin 8) :
    crossedSourceNondiscretePartitionBlock (crossedSourceSingletonFailureIndex entry)
        (crossedSourceSingletonFailureFirst entry) =
      crossedSourceNondiscretePartitionBlock (crossedSourceSingletonFailureIndex entry)
        (crossedSourceSingletonFailureSecond entry) := by
  fin_cases entry
  · simpa [crossedSourceSingletonFailureIndex, crossedSourceSingletonFailureFirst,
      crossedSourceSingletonFailureSecond] using singletonFailure_same_block_zero
  · simpa [crossedSourceSingletonFailureIndex, crossedSourceSingletonFailureFirst,
      crossedSourceSingletonFailureSecond] using singletonFailure_same_block_one
  · simpa [crossedSourceSingletonFailureIndex, crossedSourceSingletonFailureFirst,
      crossedSourceSingletonFailureSecond] using singletonFailure_same_block_two
  · simpa [crossedSourceSingletonFailureIndex, crossedSourceSingletonFailureFirst,
      crossedSourceSingletonFailureSecond] using singletonFailure_same_block_three
  · simpa [crossedSourceSingletonFailureIndex, crossedSourceSingletonFailureFirst,
      crossedSourceSingletonFailureSecond] using singletonFailure_same_block_four
  · simpa [crossedSourceSingletonFailureIndex, crossedSourceSingletonFailureFirst,
      crossedSourceSingletonFailureSecond] using singletonFailure_same_block_five
  · simpa [crossedSourceSingletonFailureIndex, crossedSourceSingletonFailureFirst,
      crossedSourceSingletonFailureSecond] using singletonFailure_same_block_six
  · simpa [crossedSourceSingletonFailureIndex, crossedSourceSingletonFailureFirst,
      crossedSourceSingletonFailureSecond] using singletonFailure_same_block_seven

/-- Each actual block-column gap is exactly 3 minus -1. -/
theorem crossedSourceSingletonFailure_rowSum_gap (entry : Fin 8) :
    quittingSingletonBlockRowSum halfCeilingReward
        (crossedSourceNondiscretePartitionBlock (crossedSourceSingletonFailureIndex entry))
        (crossedSourceSingletonFailureFirst entry)
        (crossedSourceSingletonFailureCoordinate entry) -
      quittingSingletonBlockRowSum halfCeilingReward
        (crossedSourceNondiscretePartitionBlock (crossedSourceSingletonFailureIndex entry))
        (crossedSourceSingletonFailureSecond entry)
        (crossedSourceSingletonFailureCoordinate entry) = 4 := by
  simp only [quittingSingletonBlockRowSum, halfCeiling_singletonMatrix]
  fin_cases entry <;>
    norm_num [Fin.sum_univ_succ, sourceSingletonMatrix,
      crossedSourceNondiscretePartitionBlock, crossedSourceSingletonFailureIndex,
      crossedSourceSingletonFailureFirst, crossedSourceSingletonFailureSecond,
      crossedSourceSingletonFailureCoordinate]

theorem crossedSourceSingletonFailure_not_rowsAgree (entry : Fin 8) :
    ¬ CrossedSourceSingletonPartitionRowsAgree (crossedSourceSingletonFailureIndex entry) := by
  intro hagree
  have heq := hagree _ _ (crossedSourceSingletonFailure_same_block entry)
    (crossedSourceSingletonFailureCoordinate entry)
  have hgap := crossedSourceSingletonFailure_rowSum_gap entry
  rw [heq, sub_self] at hgap
  norm_num at hgap

private theorem singletonRowsAgree_singlePairZeroOne :
    CrossedSourceSingletonPartitionRowsAgree 4 := by
  simp only [CrossedSourceSingletonPartitionRowsAgree, quittingSingletonBlockRowSum,
    halfCeiling_singletonMatrix]
  norm_num [crossedSourceNondiscretePartitionBlock, sourceSingletonMatrix,
    Fin.forall_fin_succ, Fin.sum_univ_succ]

private theorem singletonRowsAgree_singlePairTwoThree :
    CrossedSourceSingletonPartitionRowsAgree 9 := by
  simp only [CrossedSourceSingletonPartitionRowsAgree, quittingSingletonBlockRowSum,
    halfCeiling_singletonMatrix]
  norm_num [crossedSourceNondiscretePartitionBlock, sourceSingletonMatrix,
    Fin.forall_fin_succ, Fin.sum_univ_succ]

private theorem singletonRowsAgree_doublePairZeroOneTwoThree :
    CrossedSourceSingletonPartitionRowsAgree 10 := by
  simp only [CrossedSourceSingletonPartitionRowsAgree, quittingSingletonBlockRowSum,
    halfCeiling_singletonMatrix]
  norm_num [crossedSourceNondiscretePartitionBlock, sourceSingletonMatrix,
    Fin.forall_fin_succ, Fin.sum_univ_succ]

private theorem singletonRowsAgree_doublePairZeroTwoOneThree :
    CrossedSourceSingletonPartitionRowsAgree 11 := by
  simp only [CrossedSourceSingletonPartitionRowsAgree, quittingSingletonBlockRowSum,
    halfCeiling_singletonMatrix]
  norm_num [crossedSourceNondiscretePartitionBlock, sourceSingletonMatrix,
    Fin.forall_fin_succ, Fin.sum_univ_succ]

private theorem singletonRowsAgree_doublePairZeroThreeOneTwo :
    CrossedSourceSingletonPartitionRowsAgree 12 := by
  simp only [CrossedSourceSingletonPartitionRowsAgree, quittingSingletonBlockRowSum,
    halfCeiling_singletonMatrix]
  norm_num [crossedSourceNondiscretePartitionBlock, sourceSingletonMatrix,
    Fin.forall_fin_succ, Fin.sum_univ_succ]

private theorem singletonRowsAgree_fullBlock :
    CrossedSourceSingletonPartitionRowsAgree 13 := by
  simp only [CrossedSourceSingletonPartitionRowsAgree, quittingSingletonBlockRowSum,
    halfCeiling_singletonMatrix]
  norm_num [crossedSourceNondiscretePartitionBlock, sourceSingletonMatrix,
    Fin.forall_fin_succ, Fin.sum_univ_succ]

/-- Exactly the six listed rows pass the necessary linear test. -/
theorem crossedSourceSingletonPartition_rowsAgree_iff (row : Fin 14) :
    CrossedSourceSingletonPartitionRowsAgree row ↔
      row ∈ ({4, 9, 10, 11, 12, 13} : Finset (Fin 14)) := by
  fin_cases row
  · simpa [crossedSourceSingletonFailureIndex] using
      crossedSourceSingletonFailure_not_rowsAgree 0
  · simpa [crossedSourceSingletonFailureIndex] using
      crossedSourceSingletonFailure_not_rowsAgree 1
  · simpa [crossedSourceSingletonFailureIndex] using
      crossedSourceSingletonFailure_not_rowsAgree 2
  · simpa [crossedSourceSingletonFailureIndex] using
      crossedSourceSingletonFailure_not_rowsAgree 3
  · simpa using singletonRowsAgree_singlePairZeroOne
  · simpa [crossedSourceSingletonFailureIndex] using
      crossedSourceSingletonFailure_not_rowsAgree 4
  · simpa [crossedSourceSingletonFailureIndex] using
      crossedSourceSingletonFailure_not_rowsAgree 5
  · simpa [crossedSourceSingletonFailureIndex] using
      crossedSourceSingletonFailure_not_rowsAgree 6
  · simpa [crossedSourceSingletonFailureIndex] using
      crossedSourceSingletonFailure_not_rowsAgree 7
  · simpa using singletonRowsAgree_singlePairTwoThree
  · simpa using singletonRowsAgree_doublePairZeroOneTwoThree
  · simpa using singletonRowsAgree_doublePairZeroTwoOneThree
  · simpa using singletonRowsAgree_doublePairZeroThreeOneTwo
  · simpa using singletonRowsAgree_fullBlock

/-- The failed filter is read from actual singleton row sums, not supplied rejection flags. -/
theorem crossedSourceSingletonPartition_failed_rows :
    crossedSourceSingletonPartitionFailedRows = {0, 1, 2, 3, 5, 6, 7, 8} := by
  classical
  unfold crossedSourceSingletonPartitionFailedRows
  ext row
  rw [Finset.mem_filter, crossedSourceSingletonPartition_rowsAgree_iff]
  fin_cases row <;> decide

/-- Precisely eight of these fourteen canonical nondiscrete maps fail the necessary test. -/
theorem crossedSourceSingletonPartition_failed_count :
    crossedSourceSingletonPartitionFailedRows.card = 8 := by
  rw [crossedSourceSingletonPartition_failed_rows]
  decide

/-- The existing necessary derivative identity interprets each rejected row in the actual game. -/
theorem crossedSourceSingletonFailure_not_responseInvariant (entry : Fin 8) :
    ¬ QuittingResponseInvariantOnUnitCube halfCeilingReward
      (crossedSourceNondiscretePartitionBlock (crossedSourceSingletonFailureIndex entry)) := by
  intro hinvariant
  have heq := quittingSingletonBlockRowSum_eq_of_responseInvariant halfCeilingReward
    (crossedSourceNondiscretePartitionBlock (crossedSourceSingletonFailureIndex entry))
    hinvariant (crossedSourceSingletonFailureFirst entry)
    (crossedSourceSingletonFailureSecond entry)
    (crossedSourceSingletonFailure_same_block entry)
    (crossedSourceSingletonFailureCoordinate entry)
  have hgap := crossedSourceSingletonFailure_rowSum_gap entry
  rw [heq, sub_self] at hgap
  norm_num at hgap

end GameTheory.GuardedCrossedResponseExamples
