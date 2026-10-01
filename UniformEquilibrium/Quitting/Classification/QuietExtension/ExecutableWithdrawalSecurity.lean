import MathUE.LinearProgramming.ExecutableRationalSelection
import Mathlib.Logic.Equiv.Finset
import UniformEquilibrium.Quitting.Classification.QuietExtension.ExecutableWithdrawalCoefficients
import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalSecurityStandardForm

/-! # Computed exact rational stationary-security values from actual reward rows

The selector enumerates finite rational primal/dual pairs and tests exact zero gap.
The already proved real source feasibility/boundedness are erased termination proofs.
A zero selected hazard is retained without interpreting it as a positive security law.
-/

namespace GameTheory.ExecutableWithdrawal

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def securityRow (reward : Reward ι) (i : ι) (hazard : ℚ) :
    Option {A : Finset ι // A.Nonempty ∧ i ∉ A} → ℚ
  | none => singleton reward i
  | some B =>
      (1 - hazard) * passive reward i B +
        hazard * reward ⟨childCoalition (insert i B.1),
          Finset.map_nonempty.mpr (Finset.insert_nonempty i B.1)⟩ (some i)

omit [Fintype ι] in
theorem securityRow_cast (reward : Reward ι) (i : ι) (hazard : ℚ)
    (row : Option {A : Finset ι // A.Nonempty ∧ i ∉ A}) :
    (securityRow reward i hazard row : ℝ) =
      deadlineWithdrawalSecurityRow (toReal reward) i hazard row := by
  cases row with
  | none => rfl
  | some B =>
      simp only [securityRow, deadlineWithdrawalSecurityRow, Rat.cast_add,
        Rat.cast_mul, Rat.cast_sub, Rat.cast_one, passive, toReal, childCoalition_eq]

def securityMatrix (reward : Reward ι) (i : ι) :
    WithdrawalSecurityStandardForm.Row i → Fin 3 → ℚ
  | none => ![-1, 0, 0]
  | some row => ![securityRow reward i 1 row - securityRow reward i 0 row, -1, 1]

def securityRhs (reward : Reward ι) (i : ι) :
    WithdrawalSecurityStandardForm.Row i → ℚ
  | none => -1
  | some row => -securityRow reward i 0 row

def securityObjective : Fin 3 → ℚ := ![0, -1, 1]

omit [Fintype ι] in
theorem securityMatrix_cast (reward : Reward ι) (i : ι) :
    (fun row coordinate => (securityMatrix reward i row coordinate : ℝ)) =
      WithdrawalSecurityStandardForm.matrix (toReal reward) i := by
  funext row coordinate
  cases row with
  | none => fin_cases coordinate <;> norm_num [securityMatrix,
      WithdrawalSecurityStandardForm.matrix]
  | some row =>
      fin_cases coordinate
      all_goals simp [securityMatrix, WithdrawalSecurityStandardForm.matrix,
        WithdrawalSecurityStandardForm.slope, WithdrawalSecurityStandardForm.base,
        securityRow_cast]

omit [Fintype ι] in
theorem securityRhs_cast (reward : Reward ι) (i : ι) :
    (fun row => (securityRhs reward i row : ℝ)) =
      WithdrawalSecurityStandardForm.rhs (toReal reward) i := by
  funext row
  cases row with
  | none => norm_num [securityRhs, WithdrawalSecurityStandardForm.rhs]
  | some row =>
      simp [securityRhs, WithdrawalSecurityStandardForm.rhs,
        WithdrawalSecurityStandardForm.base, securityRow_cast]

theorem securityObjective_cast :
    (fun coordinate => (securityObjective coordinate : ℝ)) =
      WithdrawalSecurityStandardForm.objective := by
  funext coordinate
  fin_cases coordinate <;> norm_num [securityObjective, WithdrawalSecurityStandardForm.objective]

theorem securityFeasible (reward : Reward ι) (i : ι) :
    ∃ point, Math.LinearProgramming.MinPrimalFeasible
      (fun row coordinate => (securityMatrix reward i row coordinate : ℝ))
      (fun row => (securityRhs reward i row : ℝ)) point := by
  rw [securityMatrix_cast, securityRhs_cast]
  exact WithdrawalSecurityStandardForm.feasible (toReal reward) i

omit [Fintype ι] in
theorem securityBounded (reward : Reward ι) (i : ι) :
    ∃ lower : ℝ, ∀ point, Math.LinearProgramming.MinPrimalFeasible
      (fun row coordinate => (securityMatrix reward i row coordinate : ℝ))
      (fun row => (securityRhs reward i row : ℝ)) point →
        lower ≤ Math.LinearProgramming.minPrimalValue
          (fun coordinate => (securityObjective coordinate : ℝ)) point := by
  rw [securityMatrix_cast, securityRhs_cast, securityObjective_cast]
  exact WithdrawalSecurityStandardForm.bounded (toReal reward) i

def securitySolution [Encodable ι] (reward : Reward ι) (i : ι) :
    (Fin 3 → ℚ) × (WithdrawalSecurityStandardForm.Row i → ℚ) :=
  Math.LinearProgramming.selectRationalPrimalDual
    (securityMatrix reward i) (securityRhs reward i) securityObjective
    (securityFeasible reward i) (securityBounded reward i)

def securityHazard [Encodable ι] (reward : Reward ι) (i : ι) : ℚ :=
  (securitySolution reward i).1 0

def securityValue [Encodable ι] (reward : Reward ι) (i : ι) : ℚ :=
  (securitySolution reward i).1 1 - (securitySolution reward i).1 2

theorem securitySolution_optimal [Encodable ι] (reward : Reward ι) (i : ι) :
    DeadlineWithdrawalSecurityFeasible (toReal reward) i
      (securityHazard reward i) (securityValue reward i) ∧
      ∀ hazard value, DeadlineWithdrawalSecurityFeasible (toReal reward) i hazard value →
        value ≤ (securityValue reward i : ℝ) := by
  have h := Math.LinearProgramming.selectRationalPrimalDual_optimal
    (securityMatrix reward i) (securityRhs reward i) securityObjective
    (securityFeasible reward i) (securityBounded reward i)
  change Math.LinearProgramming.MinPrimalFeasible _ _
      (fun coordinate => ((securitySolution reward i).1 coordinate : ℝ)) ∧ _ at h
  rw [securityMatrix_cast, securityRhs_cast, securityObjective_cast] at h
  refine ⟨?_, ?_⟩
  · have hp := ((WithdrawalSecurityStandardForm.primal_iff (toReal reward) i _).mp h.1).2
    simpa only [securityHazard, securityValue, Rat.cast_sub] using hp
  · intro hazard value hfeasible
    have hoptimal := h.2 (WithdrawalSecurityStandardForm.encode hazard value)
      (WithdrawalSecurityStandardForm.encode_feasible (toReal reward) i hazard value hfeasible)
    rw [WithdrawalSecurityStandardForm.objective_eq,
      WithdrawalSecurityStandardForm.objective_eq] at hoptimal
    change -(((securitySolution reward i).1 1 : ℝ) -
      (securitySolution reward i).1 2) ≤ -(max value 0 - max (-value) 0) at hoptimal
    rw [max_zero_sub_max_neg_zero_eq_self] at hoptimal
    change value ≤ (((securitySolution reward i).1 1 -
      (securitySolution reward i).1 2 : ℚ) : ℝ)
    rw [Rat.cast_sub]
    exact neg_le_neg_iff.mp hoptimal

theorem securityValue_cast [Encodable ι] (reward : Reward ι) (i : ι) :
    (securityValue reward i : ℝ) = deadlineWithdrawalSecurityValue (toReal reward) i := by
  obtain ⟨hazard, hfeasible, hoptimal⟩ := deadlineWithdrawalSecurityValue_spec (toReal reward) i
  exact le_antisymm (hoptimal _ _ (securitySolution_optimal reward i).1)
    ((securitySolution_optimal reward i).2 _ _ hfeasible)

def securityFloor [Encodable ι] (reward : Reward ι) (i : ι) : ℚ :=
  max (zeroFloor reward i) (securityValue reward i)

theorem securityFloor_cast [Encodable ι] (reward : Reward ι) (i : ι) :
    (securityFloor reward i : ℝ) = deadlineWithdrawalSecurityFloor (toReal reward) i := by
  simp only [securityFloor, Rat.cast_max, zeroFloor_cast, securityValue_cast,
    deadlineWithdrawalSecurityFloor]

end GameTheory.ExecutableWithdrawal
