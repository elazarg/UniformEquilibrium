import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalPayoffLimit

/-!
# Expected terminal payoff limit of actual patient responses

Dominated convergence is applied on the fixed original-clock/outsider-replica
sample. Every integrand is the payoff of an actual finite-delay response,
uniformly bounded by the finite reward table. No deviation supremum is
interchanged with a limit.
-/

noncomputable section

namespace GameTheory

open Filter Topology _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem patient_terminalPayoff_abs_le
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (clocks : Option ι → Option ℕ) (i : ι) :
    |quittingPureClockTerminalPayoff reward clocks (some i)| ≤
      quittingRewardBound reward := by
  simpa only [quittingPureClockEvaluatedPayoff_terminalEvaluation,
    quittingTerminalEvaluation_zero, one_mul] using
    abs_quittingPureClockEvaluatedPayoff_le reward quittingTerminalEvaluation
      quittingTerminalEvaluation_nonneg quittingTerminalEvaluation_antitone clocks (some i)

/-- The patient payoff limit obeys the same finite reward-table bound as
every actual finite-delay response. -/
theorem abs_patientWithdrawalTerminalPayoffLimit_le
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) :
    |patientWithdrawalTerminalPayoffLimit reward times deadline i| ≤
      quittingRewardBound reward := by
  exact le_of_tendsto'
    (patientWithdrawal_terminalPayoff_tendsto reward times deadline i).abs
    (fun delay => patient_terminalPayoff_abs_le reward
      (patientWithdrawalParentClocks reward times deadline delay i) i)

/-- On any fixed coupled source law, the actual finite-delay expected
terminal payoffs converge to the expectation of the literal patient limit. -/
theorem patientWithdrawal_expectedTerminalPayoff_tendsto
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (source : PMF ((ι → Option ℕ) × Option ℕ)) (i : ι) :
    Tendsto (fun delay : ℕ => expect source fun sample =>
        quittingPureClockTerminalPayoff reward
          (patientWithdrawalParentClocks reward sample.1 sample.2 delay i) (some i))
      atTop (𝓝 (expect source fun sample =>
        patientWithdrawalTerminalPayoffLimit reward sample.1 sample.2 i)) := by
  have hsum : Summable (fun sample =>
      (source sample).toReal * quittingRewardBound reward) :=
    (pmf_toReal_summable source).mul_right (quittingRewardBound reward)
  have hpoint (sample : (ι → Option ℕ) × Option ℕ) :
      Tendsto (fun delay : ℕ => (source sample).toReal *
          quittingPureClockTerminalPayoff reward
            (patientWithdrawalParentClocks reward sample.1 sample.2 delay i) (some i))
        atTop (𝓝 ((source sample).toReal *
          patientWithdrawalTerminalPayoffLimit reward sample.1 sample.2 i)) :=
    (patientWithdrawal_terminalPayoff_tendsto reward sample.1 sample.2 i).const_mul _
  have hbound : ∀ delay : ℕ, ∀ sample : (ι → Option ℕ) × Option ℕ,
      ‖(source sample).toReal * quittingPureClockTerminalPayoff reward
          (patientWithdrawalParentClocks reward sample.1 sample.2 delay i) (some i)‖ ≤
        (source sample).toReal * quittingRewardBound reward := by
    intro delay sample
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left
      (patient_terminalPayoff_abs_le reward
        (patientWithdrawalParentClocks reward sample.1 sample.2 delay i) i)
      ENNReal.toReal_nonneg
  exact tendsto_tsum_of_dominated_convergence hsum hpoint
    (Eventually.of_forall hbound)

end GameTheory
