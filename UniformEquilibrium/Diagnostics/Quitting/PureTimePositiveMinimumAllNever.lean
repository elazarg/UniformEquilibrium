import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# The all-Never profile is not a positive global semantic-debt minimum
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal all-Never cannot realize a positive global minimum of total
terminal semantic debt. -/
theorem not_allNever_positiveMinimumTerminalSemanticDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingAlwaysContinueProfile reward)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingAlwaysContinueProfile reward))) : False := by
  let pair := quittingTerminalSemanticPair reward
    (quittingAlwaysContinueProfile reward)
  have hpair : pair ∈ quittingTerminalSemanticCarrier reward := by
    apply subset_closure
    exact ⟨_, rfl⟩
  by_cases hexists : ∃ who,
      0 ≤ reward (quittingSingletonTerminal who) who
  · obtain ⟨who, hsolo⟩ := hexists
    have hmargin := minimumTerminalSemantic_singletonMargin
      pair hpair hminimum hpositive who
    have hpayoff : pair.1 who = 0 := by
      exact quittingTerminalPayoff_quittingAlwaysContinue reward who
    have hcap : pair.2 who =
        max 0 (reward (quittingSingletonTerminal who) who) :=
      quittingContinuationBestResponseValue_quittingAlwaysContinueProfile
        reward who
    rw [hcap, max_eq_right hsolo] at hmargin
    linarith
  · push Not at hexists
    have hdebtZero : ∀ who, quittingTerminalSemanticDebt pair who = 0 := by
      intro who
      unfold quittingTerminalSemanticDebt
      change quittingContinuationBestResponseValue reward
          (quittingAlwaysContinueProfile reward) who -
        quittingTerminalPayoff reward
          (quittingAlwaysContinueProfile reward) who = 0
      rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
        quittingTerminalPayoff_quittingAlwaysContinue,
        max_eq_left (le_of_lt (hexists who))]
      ring
    have hsum : quittingTerminalSemanticDebtSum pair = 0 := by
      unfold quittingTerminalSemanticDebtSum
      simp [hdebtZero]
    exact hpositive.ne' hsum

end GameTheory
