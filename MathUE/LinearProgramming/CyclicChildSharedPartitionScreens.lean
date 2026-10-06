import MathUE.LinearProgramming.CyclicChildSharedFixture

/-! # Thirteen literal singleton-block row screens

This records the thirteen displayed partition witnesses. The discrete
partition and the partition `0 | 123` are not excluded by these linear tests.
No nonlinear response property or classification of arbitrary partitions is
assumed or concluded by this owner.
-/

noncomputable section

namespace Math.CyclicChildJointPhase.SharedFixture

def excludedPartition (entry : Fin 13) : Fin 4 → Fin 4 :=
  match entry.val with
  | 0 => ![0, 0, 1, 2]
  | 1 => ![0, 1, 0, 2]
  | 2 => ![0, 1, 2, 0]
  | 3 => ![0, 1, 1, 2]
  | 4 => ![0, 1, 2, 1]
  | 5 => ![0, 1, 2, 2]
  | 6 => ![0, 0, 0, 1]
  | 7 => ![0, 0, 1, 0]
  | 8 => ![0, 1, 0, 0]
  | 9 => ![0, 0, 1, 1]
  | 10 => ![0, 1, 0, 1]
  | 11 => ![0, 1, 1, 0]
  | _ => ![0, 0, 0, 0]

def partitionFirst (entry : Fin 13) : Fin 4 :=
  match entry.val with
  | 3 | 4 => 1
  | 5 => 2
  | _ => 0

def partitionSecond (entry : Fin 13) : Fin 4 :=
  match entry.val with
  | 1 | 3 | 8 | 10 => 2
  | 2 | 4 | 5 | 11 => 3
  | _ => 1

def partitionColumn (entry : Fin 13) : Fin 4 :=
  match entry.val with
  | 2 | 3 | 4 | 5 | 11 => 1
  | _ => 0

def partitionFirstSum (entry : Fin 13) : ℝ :=
  match entry.val with
  | 3 => -1
  | 4 | 5 | 6 | 11 => 2
  | 7 | 8 => 0
  | _ => 1

def partitionSecondSum (entry : Fin 13) : ℝ :=
  match entry.val with
  | 3 => 2
  | 6 | 8 => -2
  | 7 | 11 => 1
  | 12 => 0
  | _ => -1

def singletonPartitionRowSum (block : Fin 4 → Fin 4) (receiver coordinate : Fin 4) : ℝ :=
  ∑ owner, if block owner = coordinate then matrix receiver owner else 0

theorem excludedPartition_same_block (entry : Fin 13) :
    excludedPartition entry (partitionFirst entry) =
      excludedPartition entry (partitionSecond entry) := by
  fin_cases entry <;> rfl

theorem excludedPartition_first_sum (entry : Fin 13) :
    singletonPartitionRowSum (excludedPartition entry) (partitionFirst entry)
      (partitionColumn entry) = partitionFirstSum entry := by
  fin_cases entry <;>
    norm_num [singletonPartitionRowSum, excludedPartition, partitionFirst,
      partitionColumn, partitionFirstSum, matrix_eq, Fin.sum_univ_succ]

theorem excludedPartition_second_sum (entry : Fin 13) :
    singletonPartitionRowSum (excludedPartition entry) (partitionSecond entry)
      (partitionColumn entry) = partitionSecondSum entry := by
  fin_cases entry <;>
    norm_num [singletonPartitionRowSum, excludedPartition, partitionSecond,
      partitionColumn, partitionSecondSum, matrix_eq, Fin.sum_univ_succ]

theorem excludedPartition_row_sums_ne (entry : Fin 13) :
    singletonPartitionRowSum (excludedPartition entry) (partitionFirst entry)
      (partitionColumn entry) ≠
    singletonPartitionRowSum (excludedPartition entry) (partitionSecond entry)
      (partitionColumn entry) := by
  rw [excludedPartition_first_sum, excludedPartition_second_sum]
  fin_cases entry <;> norm_num [partitionFirstSum, partitionSecondSum]

end Math.CyclicChildJointPhase.SharedFixture
