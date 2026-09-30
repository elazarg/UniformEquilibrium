import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityTerminalFixedTarget
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalFinFourExistence

/-! # Literal untruncated security rows produce four-player uniform equilibrium -/

noncomputable section

namespace GameTheory

open StochasticGame

/-- For every nonempty proper child of the literal four-player reward table,
untruncated stationary-security deadline certificates for all outsiders imply
existence. The existing low-cardinality theorem supplies the actual child UE
target; no strategy, continuation, cap, or favorable target is a premise. -/
theorem quittingGame_exists_uniformPayoffWitnesses_of_finFour_deadlineSecurityTerminalFamily
    (deleted : Fin 4 → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : Fin 4 // deleted who}]
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (certificate : ∀ outside : {who : Fin 4 // deleted who},
      DeadlineSecurityTerminalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside)) :
    ∃ payoff : Payoff (Fin 4),
      ∀ ε : ℝ, 0 < ε →
        ∃ (profile : (quittingGame
            (quittingDeleteReward reward deleted)).BehaviorProfile) (threshold : ℕ),
          ∀ horizon, threshold ≤ horizon →
            (quittingGame reward).IsεHorizonNash none horizon ε
                (quittingLiftDeletedProfile reward deleted profile) ∧
              ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
                (quittingLiftDeletedProfile reward deleted profile) who - payoff who| ≤ ε := by
  obtain ⟨target, htarget⟩ :=
    quittingDeleteReward_finFour_exists_uniformEquilibriumPayoff deleted reward
  obtain ⟨payoff, _, hpayoff⟩ :=
    exists_uniformPayoffWitnesses_eq_on_child_of_deadlineSecurityTerminalFamily
      deleted reward certificate target htarget
  exact ⟨payoff, hpayoff⟩

/-- Project source-produced actual quiet witnesses to four-player UE existence. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_finFour_deadlineSecurityTerminalFamily
    (deleted : Fin 4 → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : Fin 4 // deleted who}]
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (certificate : ∀ outside : {who : Fin 4 // deleted who},
      DeadlineSecurityTerminalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside)) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨payoff, hwitnesses⟩ :=
    quittingGame_exists_uniformPayoffWitnesses_of_finFour_deadlineSecurityTerminalFamily
      deleted reward certificate
  refine ⟨payoff, fun ε hε => ?_⟩
  obtain ⟨profile, threshold, hwitness⟩ := hwitnesses ε hε
  exact ⟨quittingLiftDeletedProfile reward deleted profile, threshold, hwitness⟩

end GameTheory
