import MathUE.LinearProgramming.Standard
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityLP

/-! # Canonical standard-form encoding of the actual stationary-security LP

The existing rational-optimizer proof delegates to this source encoding.
Computational rational coefficients use the same rows and cast bridge.
-/

noncomputable section

namespace GameTheory.WithdrawalSecurityStandardForm

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev Row (i : ι) := Option (Option {A : Finset ι // A.Nonempty ∧ i ∉ A})

def base (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (i : ι) :=
  deadlineWithdrawalSecurityRow reward i 0

def slope (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (i : ι) :=
  fun row => deadlineWithdrawalSecurityRow reward i 1 row - base reward i row

def matrix (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) : Row i → Fin 3 → ℝ
  | none => ![-1, 0, 0]
  | some row => ![slope reward i row, -1, 1]

def rhs (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) : Row i → ℝ
  | none => -1
  | some row => -base reward i row

def objective : Fin 3 → ℝ := ![0, -1, 1]

def encode (hazard value : ℝ) : Fin 3 → ℝ := ![hazard, max value 0, max (-value) 0]

omit [Fintype ι] in
theorem securityRow_affine
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (hazard : ℝ) (row : Option {A : Finset ι // A.Nonempty ∧ i ∉ A}) :
    deadlineWithdrawalSecurityRow reward i hazard row =
      deadlineWithdrawalSecurityRow reward i 0 row +
        (deadlineWithdrawalSecurityRow reward i 1 row -
          deadlineWithdrawalSecurityRow reward i 0 row) * hazard := by
  cases row <;> dsimp [deadlineWithdrawalSecurityRow] <;> ring

omit [Fintype ι] in
theorem primal_iff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (point : Fin 3 → ℝ) :
    Math.LinearProgramming.MinPrimalFeasible (matrix reward i) (rhs reward i) point ↔
      (∀ coordinate, 0 ≤ point coordinate) ∧
        DeadlineWithdrawalSecurityFeasible reward i (point 0) (point 1 - point 2) := by
  constructor
  · rintro ⟨hnonneg, hrows⟩
    refine ⟨hnonneg, ⟨hnonneg 0, ?_⟩, ?_⟩
    · have h := hrows none
      simp [matrix, rhs, Math.LinearProgramming.rowEval, Fin.sum_univ_succ] at h
      linarith
    · intro row
      have h := hrows (some row)
      simp [matrix, rhs, Math.LinearProgramming.rowEval, Fin.sum_univ_succ] at h
      rw [securityRow_affine]
      change point 1 - point 2 ≤ base reward i row + slope reward i row * point 0
      linarith
  · rintro ⟨hnonneg, hinterval, hrows⟩
    refine ⟨hnonneg, ?_⟩
    intro row
    cases row with
    | none =>
        simp [matrix, rhs, Math.LinearProgramming.rowEval, Fin.sum_univ_succ]
        linarith [hinterval.2]
    | some row =>
        have h := hrows row
        rw [securityRow_affine] at h
        change point 1 - point 2 ≤ base reward i row + slope reward i row * point 0 at h
        simp [matrix, rhs, Math.LinearProgramming.rowEval, Fin.sum_univ_succ]
        linarith

omit [Fintype ι] in
theorem encode_feasible
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (hazard value : ℝ)
    (h : DeadlineWithdrawalSecurityFeasible reward i hazard value) :
    Math.LinearProgramming.MinPrimalFeasible (matrix reward i) (rhs reward i)
      (encode hazard value) := by
  apply (primal_iff reward i _).mpr
  constructor
  · intro coordinate
    fin_cases coordinate
    · exact h.1.1
    · exact le_max_right _ _
    · exact le_max_right _ _
  · simpa [encode, max_zero_sub_max_neg_zero_eq_self] using h

theorem objective_eq (point : Fin 3 → ℝ) :
    Math.LinearProgramming.minPrimalValue objective point = -(point 1 - point 2) := by
  simp [Math.LinearProgramming.minPrimalValue, Math.LinearProgramming.dot,
    objective, Fin.sum_univ_succ, sub_eq_add_neg, add_comm]

theorem feasible
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (i : ι) :
    ∃ point, Math.LinearProgramming.MinPrimalFeasible (matrix reward i) (rhs reward i) point := by
  obtain ⟨hazard, hfeasible, _⟩ := deadlineWithdrawalSecurityValue_spec reward i
  exact ⟨_, encode_feasible reward i _ _ hfeasible⟩

omit [Fintype ι] in
theorem bounded
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (i : ι) :
    ∃ lower : ℝ, ∀ point,
      Math.LinearProgramming.MinPrimalFeasible (matrix reward i) (rhs reward i) point →
        lower ≤ Math.LinearProgramming.minPrimalValue objective point := by
  refine ⟨-deadlineWithdrawalSecurityRow reward i 0 none, ?_⟩
  intro point hpoint
  have h := ((primal_iff reward i point).mp hpoint).2.2 none
  rw [objective_eq]
  simpa [deadlineWithdrawalSecurityRow] using neg_le_neg h

end GameTheory.WithdrawalSecurityStandardForm
