import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityEvaluated
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalPointwise

/-!
# Reward-table production of exact nonpositive security plans

One private law, selected from the reward table and deadline alone, secures
the truncated improved floor simultaneously for all decreasing evaluations
and all deterministic future opponent tuples.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem security_never_evaluated_floor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (i : ι) (deadline : ℕ) (opponents : ι → Option ℕ)
    (hfuture : ∀ j, (deadline : WithTop ℕ) < quittingStoppingTimeValue (opponents j)) :
    evaluation deadline * deadlineWithdrawalZeroFloor reward i ≤
      quittingPureClockEvaluatedPayoff reward evaluation
        (Function.update (quietParentClocks opponents) (some i) none) (some i) := by
  let : Nonempty ι := ⟨i⟩
  let times := Function.update opponents i (some deadline)
  have hclock : times i = some deadline := by simp [times]
  have hfirst : quittingEarliestStoppingValue times = (deadline : WithTop ℕ) := by
    apply le_antisymm
    · have h : quittingEarliestStoppingValue times ≤ quittingStoppingTimeValue (times i) :=
        Finset.inf_le (Finset.mem_univ i)
      simpa [hclock, quittingStoppingTimeValue] using h
    · apply Finset.le_inf
      intro j _
      by_cases hj : j = i
      · subst j
        simp [hclock, quittingStoppingTimeValue]
      · exact (by simpa [times, hj] using (hfuture j).le)
  have hwithdraw : withdrawnChildParentClocks times (some deadline) i =
      Function.update (quietParentClocks opponents) (some i) none := by
    rw [withdrawnChildParentClocks_eq_quiet_update_none times deadline i hclock]
    funext player
    cases player with
    | none => simp [quietParentClocks]
    | some j =>
        by_cases hj : j = i <;> simp [quietParentClocks, times, hj]
  simpa only [hwithdraw] using deadlineWithdrawal_singleton_future_payoff_floor
    reward evaluation hnonneg hantitone times deadline i hfirst hclock

/-- The exact Section 5.2 floor is produced from raw rewards. The chosen law
and its strict post-deadline support do not depend on the evaluation or on
hidden opponent clocks. -/
theorem exists_deadlineWithdrawalSecurityEvaluatedPlan
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (deadline : ℕ) :
    ∃ law : PMF (Option ℕ),
      (∀ time ≤ deadline, law (some time) = 0) ∧
      ∀ (evaluation : WithTop ℕ → ℝ),
        (∀ time, 0 ≤ evaluation time) → Antitone evaluation →
        ∀ (opponents : ι → Option ℕ), opponents i = none →
          (∀ j, (deadline : WithTop ℕ) < quittingStoppingTimeValue (opponents j)) →
          evaluation deadline * min (deadlineWithdrawalSecurityFloor reward i) 0 ≤
            expect law (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
              (Function.update (quietParentClocks opponents) (some i) clock) (some i)) := by
  rcases deadlineWithdrawalSecurity_nonpositive_witness reward i with hnever | hpositive
  · refine ⟨PMF.pure none, ?_, ?_⟩
    · intro time _
      simp
    · intro evaluation hnonneg hantitone opponents hown hfuture
      simp only [expect_pure]
      exact (mul_le_mul_of_nonneg_left hnever (hnonneg _)).trans
        (security_never_evaluated_floor reward evaluation hnonneg hantitone
          i deadline opponents hfuture)
  · obtain ⟨hazard, hpositive, hfeasible⟩ := hpositive
    refine ⟨deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hfeasible.1.2,
      ?_, ?_⟩
    · exact fun time htime => deadlineWithdrawalSecurityRestartLaw_before
        deadline hazard hpositive hfeasible.1.2 time htime
    · intro evaluation hnonneg hantitone opponents hown hfuture
      exact deadlineWithdrawalSecurityRestartLaw_evaluated_floor reward evaluation
        hnonneg hantitone i hazard _ hpositive (min_le_right _ _) hfeasible deadline
        opponents hown hfuture

end GameTheory
