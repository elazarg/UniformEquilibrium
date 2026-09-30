import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityFixedTarget
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalFinFourExistence

/-!
# Four-player existence from literal security-enhanced deadline rows

The security LP and private restart plans are selected from the literal reward
table by the imported comparison. The child equilibrium target is produced by
the existing low-cardinality declarations, including children of size one or two.
-/

noncomputable section

namespace GameTheory

open StochasticGame

/-- Security-enhanced N/F/J rows for every quiet outsider imply existence
in the literal four-player game, for any nonempty proper child. The singleton
floor is `min(gamma,0)`, so the imported comparison holds at every evaluation.
No strategy, security plan, child target, or cap is supplied as a premise. -/
theorem quittingGame_exists_uniformPayoffWitnesses_of_finFour_deadlineSecurityFamily
    (deleted : Fin 4 → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : Fin 4 // deleted who}]
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (certificate : ∀ outside : {who : Fin 4 // deleted who},
      DeadlineSecurityRewardCertificate
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
    exists_uniformPayoffWitnesses_eq_on_child_of_deadlineSecurityFamily
      deleted reward certificate target htarget
  exact ⟨payoff, hpayoff⟩

/-- Project source-produced actual quiet witnesses to four-player UE existence. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_finFour_deadlineSecurityFamily
    (deleted : Fin 4 → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : Fin 4 // deleted who}]
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (certificate : ∀ outside : {who : Fin 4 // deleted who},
      DeadlineSecurityRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside)) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨payoff, hwitnesses⟩ :=
    quittingGame_exists_uniformPayoffWitnesses_of_finFour_deadlineSecurityFamily
      deleted reward certificate
  refine ⟨payoff, fun ε hε => ?_⟩
  obtain ⟨profile, threshold, hwitness⟩ := hwitnesses ε hε
  exact ⟨quittingLiftDeletedProfile reward deleted profile, threshold, hwitness⟩

end GameTheory
