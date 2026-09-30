import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalFixedTarget
import UniformEquilibrium.Quitting.Classification.SmallPlayerExistence

/-!
# Raw deadline-withdrawal production in four-player games

The actual restricted reward table supplies the child target by the existing
one-, two-, or three-player existence theorem. The raw certificate family
then supplies the parent target through the fixed-target quiet lift.
-/

noncomputable section

namespace GameTheory

open StochasticGame

/-- Any nonempty proper child of a four-player game has an actual
uniform-equilibrium target for its restricted signed reward table. -/
theorem quittingDeleteReward_finFour_exists_uniformEquilibriumPayoff
    (deleted : Fin 4 → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : Fin 4 // deleted who}]
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    ∃ target : Payoff (QuittingChildPlayer deleted),
      (quittingGame (quittingDeleteReward reward deleted)).IsUniformEquilibriumPayoff
        none target := by
  obtain ⟨⟨outside, houtside⟩⟩ :=
    (inferInstance : Nonempty {who : Fin 4 // deleted who})
  have hlt : Fintype.card (QuittingChildPlayer deleted) < 4 := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_subtype_lt (p := fun who : Fin 4 => ¬ deleted who)
        (x := outside) (not_not.mpr houtside))
  exact quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three
    (Nat.le_of_lt_succ hlt) (quittingDeleteReward reward deleted)

/-- The literal deadline N/F/J rows for every outsider imply four-player
existence for every nonempty proper child. No favorable child target,
strategy, continuation, or deviation cap is an additional hypothesis. -/
theorem quittingGame_exists_uniformPayoffWitnesses_of_finFour_deadlineWithdrawalFamily
    (deleted : Fin 4 → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : Fin 4 // deleted who}]
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (certificate : ∀ outside : {who : Fin 4 // deleted who},
      DeadlineWithdrawalRewardCertificate
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
    exists_uniformPayoffWitnesses_eq_on_child_of_deadlineWithdrawalFamily
      deleted reward certificate target htarget
  exact ⟨payoff, hpayoff⟩

/-- Project source-produced actual quiet witnesses to four-player UE existence. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_finFour_deadlineWithdrawalFamily
    (deleted : Fin 4 → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : Fin 4 // deleted who}]
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (certificate : ∀ outside : {who : Fin 4 // deleted who},
      DeadlineWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside)) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨payoff, hwitnesses⟩ :=
    quittingGame_exists_uniformPayoffWitnesses_of_finFour_deadlineWithdrawalFamily
      deleted reward certificate
  refine ⟨payoff, fun ε hε => ?_⟩
  obtain ⟨profile, threshold, hwitness⟩ := hwitnesses ε hε
  exact ⟨quittingLiftDeletedProfile reward deleted profile, threshold, hwitness⟩

end GameTheory
