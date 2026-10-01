import MathUE.LinearProgramming.RationalOptimization
import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalSecurityStandardForm

/-!
# Rational stationary-security LPs

Rational reward tables give rational hazard/value optimizers of the actual security LP.
Hazard zero remains admissible. This is an LP optimum, not a claim that a positive terminal
security value is attained by a zero-hazard stopping law.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual finite security LP has a rational optimizer, including boundary hazards. -/
theorem exists_rational_deadlineWithdrawalSecurity_optimizer
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (i : ι) :
    ∃ hazard value : ℚ,
      DeadlineWithdrawalSecurityFeasible reward i hazard value ∧
      ∀ otherHazard otherValue,
        DeadlineWithdrawalSecurityFeasible reward i otherHazard otherValue →
        otherValue ≤ (value : ℝ) := by
  classical
  let base := deadlineWithdrawalSecurityRow reward i 0
  let slope := fun row => deadlineWithdrawalSecurityRow reward i 1 row - base row
  let matrix : Option (Option {A : Finset ι // A.Nonempty ∧ i ∉ A}) → Fin 3 → ℝ
    | none => ![-1, 0, 0]
    | some row => ![slope row, -1, 1]
  let rhs : Option (Option {A : Finset ι // A.Nonempty ∧ i ∉ A}) → ℝ
    | none => -1
    | some row => -base row
  let objective : Fin 3 → ℝ := ![0, -1, 1]
  let encode := fun hazard value : ℝ => ![hazard, max value 0, max (-value) 0]
  have hvalue (value : ℝ) : max value 0 - max (-value) 0 = value :=
    max_zero_sub_max_neg_zero_eq_self value
  have hprimal (point : Fin 3 → ℝ) :
      Math.LinearProgramming.MinPrimalFeasible matrix rhs point ↔
        (∀ coordinate, 0 ≤ point coordinate) ∧
          DeadlineWithdrawalSecurityFeasible reward i (point 0) (point 1 - point 2) :=
    WithdrawalSecurityStandardForm.primal_iff reward i point
  have hencode (hazard value : ℝ)
      (h : DeadlineWithdrawalSecurityFeasible reward i hazard value) :
      Math.LinearProgramming.MinPrimalFeasible matrix rhs (encode hazard value) :=
    WithdrawalSecurityStandardForm.encode_feasible reward i hazard value h
  have hobjective (point : Fin 3 → ℝ) :
      Math.LinearProgramming.minPrimalValue objective point = -(point 1 - point 2) :=
    WithdrawalSecurityStandardForm.objective_eq point
  have hrowRational (hazard : ℝ) (hhazard : hazard = 0 ∨ hazard = 1)
      (row : Option {A : Finset ι // A.Nonempty ∧ i ∉ A}) :
      Math.IsRationalReal (deadlineWithdrawalSecurityRow reward i hazard row) := by
    cases row with
    | none =>
        simpa only [deadlineWithdrawalSecurityRow] using
          hrational ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
    | some coalition =>
        rcases hhazard with rfl | rfl
        · simpa [deadlineWithdrawalSecurityRow] using
            hrational ⟨cappedClockChildCoalition coalition.1,
              cappedClockChildCoalition_nonempty coalition.2.1⟩ (some i)
        · simpa [deadlineWithdrawalSecurityRow] using
            hrational ⟨cappedClockChildCoalition (insert i coalition.1),
              cappedClockChildCoalition_nonempty (Finset.insert_nonempty i coalition.1)⟩
              (some i)
  have hbase : ∀ row, Math.IsRationalReal (base row) :=
    fun row => hrowRational 0 (Or.inl rfl) row
  have hslope : ∀ row, Math.IsRationalReal (slope row) :=
    fun row => (hrowRational 1 (Or.inr rfl) row).sub (hbase row)
  have hminusOne : Math.IsRationalReal (-1 : ℝ) := by
    simpa using Math.IsRationalReal.zero.sub Math.IsRationalReal.one
  have hmatrix : ∀ row coordinate, Math.IsRationalReal (matrix row coordinate) := by
    intro row coordinate
    cases row <;> fin_cases coordinate
    · exact hminusOne
    · exact Math.IsRationalReal.zero
    · exact Math.IsRationalReal.zero
    · exact hslope _
    · exact hminusOne
    · exact Math.IsRationalReal.one
  have hrhs : ∀ row, Math.IsRationalReal (rhs row) := by
    intro row
    cases row with
    | none => exact hminusOne
    | some row => simpa [rhs] using Math.IsRationalReal.zero.sub (hbase row)
  have hobj : ∀ coordinate, Math.IsRationalReal (objective coordinate) := by
    intro coordinate
    fin_cases coordinate
    · exact Math.IsRationalReal.zero
    · exact hminusOne
    · exact Math.IsRationalReal.one
  obtain ⟨hazard, hfeasible, _⟩ := deadlineWithdrawalSecurityValue_spec reward i
  have hbounded : ∃ lower : ℝ,
      ∀ point, Math.LinearProgramming.MinPrimalFeasible matrix rhs point →
        lower ≤ Math.LinearProgramming.minPrimalValue objective point :=
    WithdrawalSecurityStandardForm.bounded reward i
  obtain ⟨point, dual, hpoint, hdual, hgap, hoptimal⟩ :=
    Math.LinearProgramming.exists_rational_minPrimalOptimal matrix rhs objective
      hmatrix hrhs hobj ⟨_, hencode _ _ hfeasible⟩ hbounded
  refine ⟨point 0, point 1 - point 2, ?_, ?_⟩
  · simpa only [Rat.cast_sub] using
      ((hprimal (fun coordinate => (point coordinate : ℝ))).mp hpoint).2
  · intro otherHazard otherValue hother
    have h := hoptimal (encode otherHazard otherValue) (hencode _ _ hother)
    rw [hobjective, hobjective] at h
    change -((point 1 : ℝ) - point 2) ≤ -(max otherValue 0 - max (-otherValue) 0) at h
    rw [hvalue] at h
    simpa only [Rat.cast_sub] using neg_le_neg_iff.mp h

/-- The canonical security value itself is rational; no separately supplied LP value. -/
theorem isRationalReal_deadlineWithdrawalSecurityValue
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (i : ι) : Math.IsRationalReal (deadlineWithdrawalSecurityValue reward i) := by
  obtain ⟨hazard, value, hfeasible, hoptimal⟩ :=
    exists_rational_deadlineWithdrawalSecurity_optimizer reward hrational i
  obtain ⟨canonicalHazard, hcanonical, hcanonicalOptimal⟩ :=
    deadlineWithdrawalSecurityValue_spec reward i
  refine ⟨value, le_antisymm (hoptimal _ _ hcanonical)
    (hcanonicalOptimal _ _ hfeasible)⟩

end GameTheory
