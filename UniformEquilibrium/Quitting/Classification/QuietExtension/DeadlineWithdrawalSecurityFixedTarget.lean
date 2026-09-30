import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMultipleOutsiderFamily
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalNashLift
import UniformEquilibrium.Quitting.Classification.QuietExtension.TerminalWeightedDebtLift

/-!
# Fixed-target quiet extension from security-enhanced deadline-withdrawal rows

The terminal evaluation of the simultaneous all-evaluation debt comparison
provides a fixed-multiplier terminal Nash lift. The existing target-tail
consumer then preserves every specified child uniform-equilibrium target.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

omit [Nonempty α] in
/-- A displayed raw security-enhanced deadline-withdrawal outsider weight is below the family
maximum, which also includes the unchanged child-coordinate factor one. -/
theorem deadlineSecurityOutsiderWeight_le_maxWeight
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineSecurityRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (outside : {who : α // deleted who}) :
    deadlineSecurityOutsiderWeight deleted reward certificate outside ≤
      deadlineSecurityOutsiderMaxWeight deleted reward certificate := by
  apply le_trans (Finset.le_sup'
    (f := deadlineSecurityOutsiderWeight deleted reward certificate)
    (Finset.mem_univ outside))
  exact le_max_right _ _

/-- Every child terminal approximate equilibrium lifts at the finite fixed
factor from the raw D certificates, for the same quiet lifted profile. -/
theorem isεAsymptoticNash_liftDeletedProfile_of_deadlineSecurityFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineSecurityRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    {error : ℝ} (herror : 0 ≤ error)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (hnash : (quittingGame
      (quittingDeleteReward reward deleted)).IsεAsymptoticNash
        (quittingTerminalPayoff (quittingDeleteReward reward deleted))
        error profile) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (deadlineSecurityOutsiderMaxWeight deleted reward certificate * error)
      (quittingLiftDeletedProfile reward deleted profile) := by
  exact isεAsymptoticNash_quietLift_of_outsideTerminalDebtBounds
    deleted reward (fun outside => (certificate outside).debtWeight)
    (fun outside child => (certificate outside).debtWeight_nonneg child)
    (deadlineSecurityOutsiderMaxWeight deleted reward certificate)
    (le_max_left _ _)
    (fun outside => deadlineSecurityOutsiderWeight_le_maxWeight
      deleted reward certificate outside)
    herror profile
    (fun outside => by
      have h := quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_deadlineSecurity
        deleted reward outside (certificate outside) quittingTerminalEvaluation
        quittingTerminalEvaluation_nonneg quittingTerminalEvaluation_antitone profile
      simpa only [quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation,
        quittingBehaviorEvaluatedPayoff_terminalEvaluation] using h)
    hnash

/-- Every specified child uniform-equilibrium target extends under raw
security-enhanced deadline-withdrawal certificates for all outsiders, with no favorable child
profile supplied beyond the target's actual uniform-equilibrium property. -/
theorem exists_uniformPayoffWitnesses_eq_on_child_of_deadlineSecurityFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineSecurityRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (target : Payoff (QuittingChildPlayer deleted))
    (htarget : (quittingGame
      (quittingDeleteReward reward deleted)).IsUniformEquilibriumPayoff
        none target) :
    ∃ payoff : Payoff α,
      (∀ who : QuittingChildPlayer deleted, payoff who.1 = target who) ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ (profile : (quittingGame
              (quittingDeleteReward reward deleted)).BehaviorProfile) (threshold : ℕ),
            ∀ horizon, threshold ≤ horizon →
              (quittingGame reward).IsεHorizonNash none horizon ε
                  (quittingLiftDeletedProfile reward deleted profile) ∧
                ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
                  (quittingLiftDeletedProfile reward deleted profile) who - payoff who| ≤ ε := by
  exact exists_uniformPayoffWitnesses_eq_on_image_of_terminalNash_lift
    reward (quittingDeleteReward reward deleted) (fun who => who.1)
    (quittingLiftDeletedProfile reward deleted)
    (deadlineSecurityOutsiderMaxWeight deleted reward certificate)
    (fun profile who =>
      quittingTerminalPayoff_liftDeletedProfile reward deleted profile who)
    (fun herror profile hnash =>
      isεAsymptoticNash_liftDeletedProfile_of_deadlineSecurityFamily
        deleted reward certificate herror profile hnash)
    target htarget

/-- Project the actual quiet witnesses to the usual fixed-target UE conclusion. -/
theorem exists_uniformEquilibriumPayoff_eq_on_child_of_deadlineSecurityFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineSecurityRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (target : Payoff (QuittingChildPlayer deleted))
    (htarget : (quittingGame
      (quittingDeleteReward reward deleted)).IsUniformEquilibriumPayoff
        none target) :
    ∃ payoff : Payoff α,
      (∀ who : QuittingChildPlayer deleted, payoff who.1 = target who) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨payoff, hcoordinates, hwitnesses⟩ :=
    exists_uniformPayoffWitnesses_eq_on_child_of_deadlineSecurityFamily
      deleted reward certificate target htarget
  refine ⟨payoff, hcoordinates, fun ε hε => ?_⟩
  obtain ⟨profile, threshold, hwitness⟩ := hwitnesses ε hε
  exact ⟨quittingLiftDeletedProfile reward deleted profile, threshold, hwitness⟩

end GameTheory
