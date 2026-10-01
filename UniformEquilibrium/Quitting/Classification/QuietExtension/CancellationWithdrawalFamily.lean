import UniformEquilibrium.Quitting.Classification.QuietExtension.CancellationWithdrawalFullBehavioralDebt
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedMultipleOutsiderFamily

/-!
# Simultaneous evaluated-cancellation certificates for quiet outsiders

Each outsider is tested in its own child-plus-one-outsider experiment while
all other outsiders prescribe Never. The same actual full quiet lift is used
for every experiment; child debt coordinates are preserved exactly.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Total summed advance/cancellation coefficient for one outsider. -/
def cancellationWithdrawalOutsiderWeight
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      CancellationWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (outside : {who : α // deleted who}) : ℝ :=
  ∑ who, (certificate outside).debtWeight who

/-- Finite maximum of one and all outsider coefficient totals. -/
def cancellationWithdrawalOutsiderMaxWeight
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      CancellationWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside)) : ℝ :=
  max 1 (Finset.univ.sup' Finset.univ_nonempty
    (cancellationWithdrawalOutsiderWeight deleted reward certificate))

section Child

variable (deleted : α → Prop) [DecidablePred deleted]
variable [Nonempty (QuittingChildPlayer deleted)]

variable [Nonempty α]

/-- A displayed outsider's actual full-game evaluated debt is bounded by
literal lambda-plus-mu child debts under its own raw cancellation certificate. -/
theorem quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_cancellationWithdrawal
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (outside : {who : α // deleted who})
    (certificate : CancellationWithdrawalRewardCertificate
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
      cancellationWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt
        (quittingChildWithOutsiderReward reward deleted outside) certificate
        evaluation evaluation_nonneg evaluation_antitone childProfile) profile

/-- Every child debt is unchanged, and all outsider debts satisfy their own
evaluated-cancellation weighted bound simultaneously for the same full lift. -/
theorem quittingLiftDeletedProfile_evaluatedDebt_of_cancellationWithdrawalFamily
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      CancellationWithdrawalRewardCertificate
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
      quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_cancellationWithdrawal
        deleted reward outside (certificate outside) evaluation
        evaluation_nonneg evaluation_antitone profile

end Child

/-- Every outsider's lambda-plus-mu sum is below the fixed family factor. -/
theorem cancellationWithdrawalOutsiderWeight_le_maxWeight
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      CancellationWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (outside : {who : α // deleted who}) :
    cancellationWithdrawalOutsiderWeight deleted reward certificate outside ≤
      cancellationWithdrawalOutsiderMaxWeight deleted reward certificate := by
  exact (Finset.le_sup'
    (f := cancellationWithdrawalOutsiderWeight deleted reward certificate)
    (Finset.mem_univ outside)).trans (le_max_right _ _)

end GameTheory
