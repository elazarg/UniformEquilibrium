import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityTerminalDebt

/-! # Actual quiet-lift terminal debt from untruncated security rows -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance deadlineSecurityTerminalQuietChildNonempty :
    Nonempty {who : Option ι // ¬ who = none} :=
  Nonempty.map (fun who => ⟨some who, Option.some_ne_none who⟩)
    (inferInstance : Nonempty ι)

/-- Literal untruncated gamma rows bound the actual outsider's full terminal
debt for the Never lift of every actual child behavioral profile. The private
security plans and their vanishing approximation error are already produced
by the stopping-law theorem, with no plan or cap supplied here. -/
theorem deadlineSecurityTerminal_quietLift_outsideBehaviorDebt_le_weighted_childDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : DeadlineSecurityTerminalRewardCertificate reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorDeviationPayoffCap reward lifted none -
        quittingTerminalPayoff reward lifted none ≤
      ∑ i, certificate.debtWeight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩) := by
  have h :=
    quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_const_of_canonical
      reward certificate.debtWeight quittingTerminalEvaluation childProfile 0
      (by
        simpa only [quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation,
          quittingBehaviorEvaluatedPayoff_terminalEvaluation, add_zero] using
            deadlineSecurityTerminal_outsideBehaviorDebt_le_weighted_childDebt
              reward certificate (quietOutsiderChildLaws reward childProfile))
  simpa only [quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation,
    quittingBehaviorEvaluatedPayoff_terminalEvaluation, add_zero] using h

end GameTheory
