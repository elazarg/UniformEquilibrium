import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityPayoff
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Positive rational private security hazards

Every real reward table and every strictly positive real error produce a
positive rational hazard. The actual finite reward-row envelope supplies
the approximation; rational reward data and an attained positive optimizer
are not required. The consumer uses the same privately sampled geometric
law before every deterministic future opponent tuple. It is not a finite
support construction or an assertion of exact positive-value attainment.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_deadlineWithdrawalSecurity_positive_rational_approximation
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (error : ℝ) (herror : 0 < error) :
    ∃ hazard : ℚ, 0 < (hazard : ℝ) ∧
      DeadlineWithdrawalSecurityFeasible reward i (hazard : ℝ)
        (deadlineWithdrawalSecurityValue reward i - error) := by
  obtain ⟨initial, hpositive, hfeasible⟩ :=
    exists_deadlineWithdrawalSecurity_positive_approximation reward i (error / 2)
      (by positivity)
  have hcontinuous :=
    (continuous_deadlineWithdrawalSecurityEnvelope reward i).continuousAt (x := initial)
  obtain ⟨radius, hradius, hnear⟩ :=
    Metric.continuousAt_iff.mp hcontinuous (error / 2) (by positivity)
  have hinterval : max (initial - radius / 2) (initial / 2) < initial := by
    apply max_lt <;> linarith
  obtain ⟨hazard, hlower, hupper⟩ := exists_rat_btwn hinterval
  have hpos : 0 < (hazard : ℝ) := by
    have := (le_max_right (initial - radius / 2) (initial / 2)).trans_lt hlower
    linarith
  have hsmall : dist (hazard : ℝ) initial < radius := by
    rw [Real.dist_eq, abs_of_neg (by linarith : (hazard : ℝ) - initial < 0)]
    have := (le_max_left (initial - radius / 2) (initial / 2)).trans_lt hlower
    linarith
  have hclose := hnear hsmall
  rw [Real.dist_eq] at hclose
  have hlowerEnvelope := (abs_lt.mp hclose).1
  have hinitial := (deadlineWithdrawalSecurity_le_envelope_iff reward i initial _).mpr
    hfeasible.2
  refine ⟨hazard, hpos, ⟨hpos.le, hupper.le.trans hfeasible.1.2⟩, ?_⟩
  apply (deadlineWithdrawalSecurity_le_envelope_iff reward i (hazard : ℝ) _).mp
  linarith

/-- One actual rational-hazard law, chosen before all future opponent tuples. -/
theorem exists_rational_deadlineWithdrawalSecurityRestartLaw_terminal_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (deadline : ℕ) (error : ℝ) (herror : 0 < error) :
    ∃ (hazard : ℚ) (hpositive : 0 < (hazard : ℝ)) (hle : (hazard : ℝ) ≤ 1),
      let law := deadlineWithdrawalSecurityRestartLaw deadline (hazard : ℝ) hpositive hle
      DeadlineWithdrawalSecurityFeasible reward i (hazard : ℝ)
          (deadlineWithdrawalSecurityValue reward i - error) ∧
        law none = 0 ∧
        (∀ time ≤ deadline, law (some time) = 0) ∧
        (∀ offset, (law (some (deadline + 1 + offset))).toReal =
          ((hazard * (1 - hazard) ^ offset : ℚ) : ℝ)) ∧
        ∀ opponents : ι → Option ℕ, opponents i = none →
          (∀ j, (deadline : WithTop ℕ) < quittingStoppingTimeValue (opponents j)) →
          deadlineWithdrawalSecurityValue reward i - error ≤ expect law
            (fun clock => quittingPureClockTerminalPayoff reward
              (Function.update (quietParentClocks opponents) (some i) clock) (some i)) := by
  obtain ⟨hazard, hpositive, hfeasible⟩ :=
    exists_deadlineWithdrawalSecurity_positive_rational_approximation reward i error herror
  refine ⟨hazard, hpositive, hfeasible.1.2, hfeasible, ?_, ?_, ?_, ?_⟩
  · exact deadlineWithdrawalSecurityRestartLaw_none _ _ _ _
  · intro time htime
    exact deadlineWithdrawalSecurityRestartLaw_before _ _ _ _ time htime
  · intro offset
    rw [deadlineWithdrawalSecurityRestartLaw_mass]
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_sub, Rat.cast_one]
  · intro opponents hown hfuture
    exact deadlineWithdrawalSecurityRestartLaw_terminal_floor reward i (hazard : ℝ) _
      hpositive hfeasible deadline opponents hown hfuture

end GameTheory
