import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalFullBehavioralDebt
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedMultipleOutsiderFamily

/-!
# Simultaneous deadline-withdrawal certificates for quiet outsiders

Each outsider is tested in its own child-plus-one-outsider experiment while
all other outsiders prescribe Never. The same actual full quiet lift is used
for every experiment; child debt coordinates are preserved exactly.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

local instance deadlineWithdrawalFamilyOptionChildNonempty
    {β : Type} [Nonempty β] :
    Nonempty {who : Option β // ¬ who = none} :=
  Nonempty.map (fun who => ⟨some who, Option.some_ne_none who⟩)
    (inferInstance : Nonempty β)

/-- Total maximum-mix coefficient for one outsider. -/
def deadlineWithdrawalOutsiderWeight
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (outside : {who : α // deleted who}) : ℝ :=
  ∑ who, (certificate outside).debtWeight who

/-- Finite maximum of one and all outsider coefficient totals. -/
def deadlineWithdrawalOutsiderMaxWeight
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside)) : ℝ :=
  max 1 (Finset.univ.sup' Finset.univ_nonempty
    (deadlineWithdrawalOutsiderWeight deleted reward certificate))

/-- A displayed outsider's actual full-game evaluated debt is bounded by
literal child debts under its own raw deadline-withdrawal certificate. -/
theorem quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_deadlineWithdrawal
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (outside : {who : α // deleted who})
    (certificate : DeadlineWithdrawalRewardCertificate
      (quittingChildWithOutsiderReward reward deleted outside))
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
          (quittingLiftDeletedProfile reward deleted profile) outside.1 -
        quittingBehaviorEvaluatedPayoff reward evaluation
          (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
      ∑ who, certificate.debtWeight who *
        (quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward reward deleted) evaluation profile who -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward reward deleted) evaluation profile who) := by
  exact quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_oneOutsiderBound
    deleted reward outside certificate.debtWeight evaluation
    (fun childProfile =>
      deadlineWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt
        (quittingChildWithOutsiderReward reward deleted outside) certificate
        evaluation evaluation_nonneg evaluation_antitone childProfile) profile

/-- Every child debt is unchanged, and all outsider debts satisfy their own
deadline-withdrawal weighted bound simultaneously for the same full lift. -/
theorem quittingLiftDeletedProfile_evaluatedDebt_of_deadlineWithdrawalFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    (∀ who : QuittingChildPlayer deleted,
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
            (quittingLiftDeletedProfile reward deleted profile) who.1 -
          quittingBehaviorEvaluatedPayoff reward evaluation
            (quittingLiftDeletedProfile reward deleted profile) who.1 =
        quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward reward deleted) evaluation profile who -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward reward deleted) evaluation profile who) ∧
    ∀ outside : {who : α // deleted who},
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
            (quittingLiftDeletedProfile reward deleted profile) outside.1 -
          quittingBehaviorEvaluatedPayoff reward evaluation
            (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
        ∑ who, (certificate outside).debtWeight who *
          (quittingBehaviorEvaluatedDeviationPayoffCap
              (quittingDeleteReward reward deleted) evaluation profile who -
            quittingBehaviorEvaluatedPayoff
              (quittingDeleteReward reward deleted) evaluation profile who) := by
  constructor
  · exact fun who => quittingBehaviorEvaluatedDeviationDebt_liftDeletedProfile
      deleted reward evaluation profile who
  · exact fun outside =>
      quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_deadlineWithdrawal
        deleted reward outside (certificate outside) evaluation
        evaluation_nonneg evaluation_antitone profile

end GameTheory
