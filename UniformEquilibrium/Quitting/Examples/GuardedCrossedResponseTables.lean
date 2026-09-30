import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Two literal four-player crossed-response reward tables -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open QuittingLCPClassification

/-- Coalition bitmask, with player zero in the least significant position. -/
def coalitionCode (coalition : Finset (Fin 4)) : ℕ :=
  (if 0 ∈ coalition then 1 else 0) + (if 1 ∈ coalition then 2 else 0) +
    (if 2 ∈ coalition then 4 else 0) + (if 3 ∈ coalition then 8 else 0)

/-- The half-ceiling table, including its asymmetric nonsingleton coordinates. -/
def halfCeilingReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal => match coalitionCode terminal.val with
    | 1 => ![1, 3, -1, -1]
    | 2 => ![4, 0, -1, -1]
    | 3 => ![5, 4, 178 / 7, 2]
    | 4 => ![0, -1, 0, 3]
    | 5 => ![7 / 3, 0, 8, -1]
    | 6 => ![1, 83 / 91, -2, 2]
    | 7 => ![-5, -6, 199 / 7, -4]
    | 8 => ![0, -1, 3, 0]
    | 9 => ![2, 0, 4, -4]
    | 10 => ![1, 1, 3, 6]
    | 11 => ![-5, -6, 7, 0]
    | 12 => ![0, -1, 3, 0]
    | 13 => ![2, 0, -5, 7]
    | 14 => ![1, 1, 8, -3]
    | 15 => ![-5, -6, -3, -4]
    | _ => 0

/-- The unit-ceiling table; its singleton comparison matrix is unchanged. -/
def unitCeilingReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal => match coalitionCode terminal.val with
    | 1 => ![1, 4, 0, 0]
    | 2 => ![4, 1, 0, 0]
    | 3 => ![-3, -3, 4, 2]
    | 4 => ![0, 0, 1, 4]
    | 5 => ![1, 4, 4, -1]
    | 6 => ![-3, 3, -3, 3]
    | 7 => ![-4, 3, -3, -2]
    | 8 => ![0, 0, 4, 1]
    | 9 => ![3, -1, 2, -1]
    | 10 => ![-2, 3, -2, 1]
    | 11 => ![-3, -3, -4, -1]
    | 12 => ![0, -2, 1, 1]
    | 13 => ![2, -3, 1, 0]
    | 14 => ![0, 3, 1, 1]
    | 15 => ![-1, -5, -4, 0]
    | _ => 0

def sourceSingletonMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 3, -1, -1; 3, 0, -1, -1; -1, -1, 0, 3; -1, -1, 3, 0]

def sourceSingletonInverse : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2 / 15, 7 / 15, 3 / 15, 3 / 15; 7 / 15, 2 / 15, 3 / 15, 3 / 15;
    3 / 15, 3 / 15, 2 / 15, 7 / 15; 3 / 15, 3 / 15, 7 / 15, 2 / 15]

theorem halfCeiling_singletonMatrix :
    quittingSingletonMatrix halfCeilingReward = sourceSingletonMatrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num +decide [quittingSingletonMatrix, halfCeilingReward, coalitionCode,
      sourceSingletonMatrix]

theorem unitCeiling_singletonMatrix :
    quittingSingletonMatrix unitCeilingReward = sourceSingletonMatrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num +decide [quittingSingletonMatrix, unitCeilingReward, coalitionCode,
      sourceSingletonMatrix]

theorem sourceSingletonMatrix_det : sourceSingletonMatrix.det = 45 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, sourceSingletonMatrix,
    Matrix.submatrix, Fin.succAbove]

theorem sourceSingletonMatrix_inverse :
    sourceSingletonMatrix⁻¹ = sourceSingletonInverse := by
  apply Matrix.inv_eq_right_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, sourceSingletonMatrix,
      sourceSingletonInverse, Matrix.one_apply]

theorem sourceSingletonMatrix_inverse_pos (row column : Fin 4) :
    0 < sourceSingletonMatrix⁻¹ row column := by
  rw [sourceSingletonMatrix_inverse]
  fin_cases row <;> fin_cases column <;> norm_num [sourceSingletonInverse]

end GameTheory.GuardedCrossedResponseExamples
