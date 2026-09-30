import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMixedLaw
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityPayoff

/-!
# Actual approximate plans for the untruncated terminal security floor

Positive security values use actual positive-hazard clocks. A possible
zero-hazard LP optimizer is handled by the checked positive approximation.
The exact nonpositive evaluated plan supplies the other branch.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every strictly positive error request produces one private post-deadline
law securing the literal untruncated floor against every deterministic future
opponent tuple. The law is chosen before all hidden opponent clocks. -/
theorem exists_deadlineWithdrawalSecurityTerminalPlan
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (deadline : ℕ) (error : ℝ) (herror : 0 < error) :
    ∃ law : PMF (Option ℕ),
      (∀ time ≤ deadline, law (some time) = 0) ∧
      ∀ (opponents : ι → Option ℕ), opponents i = none →
        (∀ j, (deadline : WithTop ℕ) < quittingStoppingTimeValue (opponents j)) →
        deadlineWithdrawalSecurityFloor reward i - error ≤
          expect law (fun clock => quittingPureClockTerminalPayoff reward
            (Function.update (quietParentClocks opponents) (some i) clock) (some i)) := by
  by_cases hnonpositive : deadlineWithdrawalSecurityFloor reward i ≤ 0
  · refine ⟨deadlineSecurityEvaluatedRestartFamily reward i deadline, ?_, ?_⟩
    · exact fun time htime => deadlineSecurityEvaluatedRestartFamily_before
        reward i deadline time htime
    · intro opponents hown hfuture
      have hplan := deadlineSecurityEvaluatedRestartFamily_floor reward i deadline
        quittingTerminalEvaluation quittingTerminalEvaluation_nonneg
        quittingTerminalEvaluation_antitone opponents hown hfuture
      have hexact : deadlineWithdrawalSecurityFloor reward i ≤
          expect (deadlineSecurityEvaluatedRestartFamily reward i deadline)
            (fun clock => quittingPureClockTerminalPayoff reward
              (Function.update (quietParentClocks opponents) (some i) clock) (some i)) := by
        simpa [quittingTerminalEvaluation, min_eq_left hnonpositive,
          quittingPureClockEvaluatedPayoff_terminalEvaluation] using hplan
      exact (sub_le_self _ herror.le).trans hexact
  · have hpositive : 0 < deadlineWithdrawalSecurityFloor reward i :=
      lt_of_not_ge hnonpositive
    have hfloor : deadlineWithdrawalSecurityFloor reward i =
        deadlineWithdrawalSecurityValue reward i := by
      have hzero := deadlineWithdrawalZeroFloor_le_zero reward i
      unfold deadlineWithdrawalSecurityFloor at hpositive ⊢
      exact max_eq_right (by rcases lt_max_iff.mp hpositive with h | h <;> linarith)
    obtain ⟨hazard, hhazard, hfeasible⟩ :=
      exists_deadlineWithdrawalSecurity_positive_approximation reward i error herror
    refine ⟨deadlineWithdrawalSecurityRestartLaw deadline hazard hhazard hfeasible.1.2,
      ?_, ?_⟩
    · exact fun time htime => deadlineWithdrawalSecurityRestartLaw_before
        deadline hazard hhazard hfeasible.1.2 time htime
    · intro opponents hown hfuture
      rw [hfloor]
      exact deadlineWithdrawalSecurityRestartLaw_terminal_floor reward i hazard _
        hhazard hfeasible deadline opponents hown hfuture

/-- The terminal source family selected from raw rewards and a requested
positive error. It never observes an opponent's future private clock. -/
def deadlineSecurityTerminalRestartFamily
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (error : ℝ) (herror : 0 < error) (deadline : ℕ) : PMF (Option ℕ) :=
  Classical.choose (exists_deadlineWithdrawalSecurityTerminalPlan
    reward i deadline error herror)

theorem deadlineSecurityTerminalRestartFamily_before
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (error : ℝ) (herror : 0 < error)
    (deadline time : ℕ) (htime : time ≤ deadline) :
    deadlineSecurityTerminalRestartFamily reward i error herror deadline (some time) = 0 :=
  (Classical.choose_spec (exists_deadlineWithdrawalSecurityTerminalPlan
    reward i deadline error herror)).1 time htime

theorem deadlineSecurityTerminalRestartFamily_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (error : ℝ) (herror : 0 < error) (deadline : ℕ)
    (opponents : ι → Option ℕ) (hown : opponents i = none)
    (hfuture : ∀ j, (deadline : WithTop ℕ) < quittingStoppingTimeValue (opponents j)) :
    deadlineWithdrawalSecurityFloor reward i - error ≤
      expect (deadlineSecurityTerminalRestartFamily reward i error herror deadline)
        (fun clock => quittingPureClockTerminalPayoff reward
          (Function.update (quietParentClocks opponents) (some i) clock) (some i)) :=
  (Classical.choose_spec (exists_deadlineWithdrawalSecurityTerminalPlan
    reward i deadline error herror)).2 opponents hown hfuture

end GameTheory
