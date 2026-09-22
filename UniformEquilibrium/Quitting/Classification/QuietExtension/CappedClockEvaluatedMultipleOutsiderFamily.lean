import UniformEquilibrium.Quitting.Classification.PlayerReindexEvaluatedPayoff
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedChildDeletionAdapter
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockMultipleOutsiderFamily

/-! # Simultaneous evaluated debt bounds for quiet outsider families -/

noncomputable section

namespace GameTheory

open StochasticGame

local instance evaluatedOptionChildNonempty {β : Type} [Nonempty β] :
    Nonempty {who : Option β // ¬ who = none} :=
  Nonempty.map (fun who => ⟨some who, Option.some_ne_none who⟩)
    (inferInstance : Nonempty β)

section ChildProfile

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The displayed one-outsider child profile has the literal child's
evaluated payoff. -/
theorem quittingBehaviorEvaluatedPayoff_childWithOutsiderChildProfile
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (outside : {who : α // deleted who})
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (who : QuittingChildPlayer deleted) :
    quittingBehaviorEvaluatedPayoff
        (quittingDeleteReward
          (quittingChildWithOutsiderReward reward deleted outside) (· = none))
        evaluation
        (quittingChildWithOutsiderChildProfile reward deleted outside profile)
        (quittingChildSomeEquiv deleted who) =
      quittingBehaviorEvaluatedPayoff
        (quittingDeleteReward reward deleted) evaluation profile who := by
  rw [quittingChildWithOutsiderChildProfile,
    quittingBehaviorEvaluatedPayoff_profileOfRewardEq]
  exact quittingBehaviorEvaluatedPayoff_profilePushforward
    (quittingChildSomeEquiv deleted)
    (quittingDeleteReward reward deleted) evaluation profile who

/-- The displayed one-outsider child profile preserves each full evaluated cap. -/
theorem quittingBehaviorEvaluatedDeviationPayoffCap_childWithOutsiderChildProfile
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (outside : {who : α // deleted who})
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (who : QuittingChildPlayer deleted) :
    quittingBehaviorEvaluatedDeviationPayoffCap
        (quittingDeleteReward
          (quittingChildWithOutsiderReward reward deleted outside) (· = none))
        evaluation
        (quittingChildWithOutsiderChildProfile reward deleted outside profile)
        (quittingChildSomeEquiv deleted who) =
      quittingBehaviorEvaluatedDeviationPayoffCap
        (quittingDeleteReward reward deleted) evaluation profile who := by
  rw [quittingChildWithOutsiderChildProfile,
    quittingBehaviorEvaluatedDeviationPayoffCap_profileOfRewardEq]
  exact quittingBehaviorEvaluatedDeviationPayoffCap_profilePushforward
    (quittingChildSomeEquiv deleted)
    (quittingDeleteReward reward deleted) evaluation profile who

end ChildProfile

section OutsiderFamily

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The two-stage restriction and the direct full lift have equal evaluated
debts, since their complete stopping-law tuples coincide. -/
theorem quittingBehaviorEvaluatedDeviationDebt_childWithOutsiderFullProfile
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (outside : {who : α // deleted who})
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (who : α) :
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
          (quittingChildWithOutsiderFullProfile reward deleted outside profile) who -
        quittingBehaviorEvaluatedPayoff reward evaluation
          (quittingChildWithOutsiderFullProfile reward deleted outside profile) who =
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
          (quittingLiftDeletedProfile reward deleted profile) who -
        quittingBehaviorEvaluatedPayoff reward evaluation
          (quittingLiftDeletedProfile reward deleted profile) who := by
  rw [quittingBehaviorEvaluatedDeviationPayoffCap_eq_of_behaviorStoppingLaws_eq
      reward evaluation _ _
      (quittingBehaviorStoppingLaws_childWithOutsiderFullProfile
        reward deleted outside profile) who,
    quittingBehaviorEvaluatedPayoff_eq_of_behaviorStoppingLaws_eq
      reward evaluation _ _
      (quittingBehaviorStoppingLaws_childWithOutsiderFullProfile
        reward deleted outside profile) who]

/-- The displayed outsider's evaluated debt is its debt in the full
child-plus-one-outsider lift. -/
theorem quittingBehaviorEvaluatedDeviationDebt_childWithOutsider_none
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (outside : {who : α // deleted who})
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    let optionReward := quittingChildWithOutsiderReward reward deleted outside
    let optionProfile := quittingLiftDeletedProfile optionReward (· = none)
      (quittingChildWithOutsiderChildProfile reward deleted outside profile)
    quittingBehaviorEvaluatedDeviationPayoffCap optionReward evaluation
          optionProfile none -
        quittingBehaviorEvaluatedPayoff optionReward evaluation
          optionProfile none =
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
          (quittingChildWithOutsiderFullProfile reward deleted outside profile)
          outside.1 -
        quittingBehaviorEvaluatedPayoff reward evaluation
          (quittingChildWithOutsiderFullProfile reward deleted outside profile)
          outside.1 := by
  dsimp only
  let pairDeleted := fun who : α => deleted who ∧ who ≠ outside.1
  let pairReward := quittingDeleteReward reward pairDeleted
  let optionReward := quittingChildWithOutsiderReward reward deleted outside
  let optionProfile := quittingLiftDeletedProfile optionReward (· = none)
    (quittingChildWithOutsiderChildProfile reward deleted outside profile)
  let pairPlayer : {who : α // ¬ pairDeleted who} :=
    ⟨outside.1, fun h => h.2 rfl⟩
  let : Nonempty (QuittingChildWithOutsiderPlayer deleted outside.1) :=
    ⟨⟨outside.1, fun h => h.2 rfl⟩⟩
  have hequiv : quittingChildWithOutsiderEquiv deleted outside pairPlayer = none := by
    simp [quittingChildWithOutsiderEquiv, pairPlayer, outside.2]
  have hcapPull := (quittingBehaviorEvaluatedDeviationPayoffCap_profilePullback
    (quittingChildWithOutsiderEquiv deleted outside) pairReward evaluation
    optionProfile pairPlayer).symm
  have hpayoffPull := quittingBehaviorEvaluatedPayoff_profilePullback
    (quittingChildWithOutsiderEquiv deleted outside) pairReward evaluation
    optionProfile pairPlayer
  rw [hequiv] at hcapPull hpayoffPull
  have hcapLift := quittingBehaviorEvaluatedDeviationPayoffCap_liftDeletedProfile
    pairDeleted reward evaluation
    (quittingChildWithOutsiderPairProfile reward deleted outside profile)
    pairPlayer
  have hpayoffLift := quittingBehaviorEvaluatedPayoff_liftDeletedProfile
    pairDeleted reward evaluation
    (quittingChildWithOutsiderPairProfile reward deleted outside profile)
    pairPlayer
  change quittingBehaviorEvaluatedDeviationPayoffCap pairReward evaluation
      (quittingChildWithOutsiderPairProfile reward deleted outside profile)
        pairPlayer =
    quittingBehaviorEvaluatedDeviationPayoffCap optionReward evaluation
      optionProfile none at hcapPull
  change quittingBehaviorEvaluatedPayoff optionReward evaluation
      optionProfile none =
    quittingBehaviorEvaluatedPayoff pairReward evaluation
      (quittingChildWithOutsiderPairProfile reward deleted outside profile)
        pairPlayer at hpayoffPull
  change quittingBehaviorEvaluatedDeviationPayoffCap optionReward evaluation
      optionProfile none -
    quittingBehaviorEvaluatedPayoff optionReward evaluation optionProfile none = _
  change _ = quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
      (quittingLiftDeletedProfile reward pairDeleted
        (quittingChildWithOutsiderPairProfile reward deleted outside profile))
        pairPlayer.1 -
    quittingBehaviorEvaluatedPayoff reward evaluation
      (quittingLiftDeletedProfile reward pairDeleted
        (quittingChildWithOutsiderPairProfile reward deleted outside profile))
        pairPlayer.1
  rw [hcapLift, hpayoffLift, ← hcapPull, ← hpayoffPull]

/-- One member of an exact certificate family bounds its actual full-game
evaluated debt by literal child debts. -/
theorem quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_cappedClockCertificate
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (outside : {who : α // deleted who})
    (certificate : CappedClockParentRewardCertificate
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
      ∑ who, certificate.weight who *
        (quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward reward deleted) evaluation profile who -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward reward deleted) evaluation profile who) := by
  let optionReward := quittingChildWithOutsiderReward reward deleted outside
  let childProfile :=
    quittingChildWithOutsiderChildProfile reward deleted outside profile
  let optionProfile := quittingLiftDeletedProfile optionReward (· = none) childProfile
  have hoption := quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt
    optionReward certificate evaluation evaluation_nonneg evaluation_antitone
    childProfile
  have hnone := quittingBehaviorEvaluatedDeviationDebt_childWithOutsider_none
    deleted reward outside evaluation profile
  have hsame := quittingBehaviorEvaluatedDeviationDebt_childWithOutsiderFullProfile
    deleted reward outside evaluation profile outside.1
  rw [← hsame, ← hnone]
  calc
    quittingBehaviorEvaluatedDeviationPayoffCap optionReward evaluation
          optionProfile none -
        quittingBehaviorEvaluatedPayoff optionReward evaluation
          optionProfile none ≤
      ∑ who, certificate.weight who *
        (quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward optionReward (· = none)) evaluation
              childProfile ⟨some who, Option.some_ne_none who⟩ -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward optionReward (· = none)) evaluation
              childProfile ⟨some who, Option.some_ne_none who⟩) := by
      simpa only [optionReward, optionProfile, childProfile] using hoption
    _ = _ := by
      apply Finset.sum_congr rfl
      intro who _
      dsimp only [optionReward, childProfile]
      change certificate.weight who *
        (quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward
              (quittingChildWithOutsiderReward reward deleted outside) (· = none))
            evaluation
            (quittingChildWithOutsiderChildProfile
              reward deleted outside profile)
            (quittingChildSomeEquiv deleted who) -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward
              (quittingChildWithOutsiderReward reward deleted outside) (· = none))
            evaluation
            (quittingChildWithOutsiderChildProfile
              reward deleted outside profile)
            (quittingChildSomeEquiv deleted who)) = _
      rw [quittingBehaviorEvaluatedDeviationPayoffCap_childWithOutsiderChildProfile,
        quittingBehaviorEvaluatedPayoff_childWithOutsiderChildProfile]

/-- Simultaneously, every child debt is preserved and each outsider's debt
is bounded by its own exact certificate weights. -/
theorem quittingLiftDeletedProfile_evaluatedDebt_of_cappedClockCertificateFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      CappedClockParentRewardCertificate
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
        ∑ who, (certificate outside).weight who *
          (quittingBehaviorEvaluatedDeviationPayoffCap
              (quittingDeleteReward reward deleted) evaluation profile who -
            quittingBehaviorEvaluatedPayoff
              (quittingDeleteReward reward deleted) evaluation profile who) := by
  constructor
  · exact fun who => quittingBehaviorEvaluatedDeviationDebt_liftDeletedProfile
      deleted reward evaluation profile who
  · exact fun outside =>
      quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_cappedClockCertificate
        deleted reward outside (certificate outside) evaluation
        evaluation_nonneg evaluation_antitone profile

/-- The maximum unrestricted evaluated behavioral debt across all players. -/
def quittingBehaviorEvaluatedMaxDebt
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun who =>
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation profile who -
      quittingBehaviorEvaluatedPayoff reward evaluation profile who

/-- The sum of unrestricted evaluated behavioral debts across all players. -/
def quittingBehaviorEvaluatedTotalDebt
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  ∑ who, (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation profile who -
    quittingBehaviorEvaluatedPayoff reward evaluation profile who)

/-- Each actual evaluated behavioral debt is nonnegative. -/
private theorem quittingBehaviorEvaluatedDebt_nonneg
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (profile : (quittingGame reward).BehaviorProfile) (who : α) :
    0 ≤ quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation profile who -
      quittingBehaviorEvaluatedPayoff reward evaluation profile who := by
  apply sub_nonneg.mpr
  unfold quittingBehaviorEvaluatedDeviationPayoffCap
  apply le_csSup
    (bddAbove_range_quittingBehaviorEvaluatedPayoff_update
      reward evaluation evaluation_nonneg evaluation_antitone profile who)
  exact ⟨profile who, by simp⟩

/-- Equation (6), maximum form: the same quiet lift obeys the bound for
every nonnegative nonincreasing clock evaluation. -/
theorem quittingBehaviorEvaluatedMaxDebt_liftDeletedProfile_le
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      CappedClockParentRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorEvaluatedMaxDebt reward evaluation
        (quittingLiftDeletedProfile reward deleted profile) ≤
      cappedClockOutsiderMaxWeight deleted reward certificate *
        quittingBehaviorEvaluatedMaxDebt
          (quittingDeleteReward reward deleted) evaluation profile := by
  let factor := cappedClockOutsiderMaxWeight deleted reward certificate
  let childReward := quittingDeleteReward reward deleted
  let lifted := quittingLiftDeletedProfile reward deleted profile
  let childDebt := fun who : QuittingChildPlayer deleted =>
    quittingBehaviorEvaluatedDeviationPayoffCap childReward evaluation profile who -
      quittingBehaviorEvaluatedPayoff childReward evaluation profile who
  let childMax := quittingBehaviorEvaluatedMaxDebt childReward evaluation profile
  have hchildLe (who : QuittingChildPlayer deleted) : childDebt who ≤ childMax :=
    Finset.le_sup' (f := childDebt) (Finset.mem_univ who)
  have hchildMaxNonneg : 0 ≤ childMax := by
    obtain ⟨who⟩ := (inferInstance : Nonempty (QuittingChildPlayer deleted))
    exact (quittingBehaviorEvaluatedDebt_nonneg childReward evaluation
      evaluation_nonneg evaluation_antitone profile who).trans (hchildLe who)
  have hfamily :=
    quittingLiftDeletedProfile_evaluatedDebt_of_cappedClockCertificateFamily
      deleted reward certificate evaluation evaluation_nonneg evaluation_antitone
      profile
  unfold quittingBehaviorEvaluatedMaxDebt
  apply Finset.sup'_le
  intro who _
  by_cases hdeleted : deleted who
  · let outside : {who : α // deleted who} := ⟨who, hdeleted⟩
    calc
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted who -
          quittingBehaviorEvaluatedPayoff reward evaluation lifted who ≤
        ∑ child, (certificate outside).weight child * childDebt child :=
        hfamily.2 outside
      _ ≤ ∑ child, (certificate outside).weight child * childMax := by
        apply Finset.sum_le_sum
        intro child _
        exact mul_le_mul_of_nonneg_left (hchildLe child)
          ((certificate outside).weight_nonneg child)
      _ = cappedClockOutsiderWeight deleted reward certificate outside *
          childMax := by
        rw [← Finset.sum_mul]
        rfl
      _ ≤ factor * childMax :=
        mul_le_mul_of_nonneg_right
          (cappedClockOutsiderWeight_le_maxWeight
            deleted reward certificate outside) hchildMaxNonneg
  · let child : QuittingChildPlayer deleted := ⟨who, hdeleted⟩
    calc
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted who -
          quittingBehaviorEvaluatedPayoff reward evaluation lifted who =
        childDebt child := hfamily.1 child
      _ ≤ childMax := hchildLe child
      _ ≤ factor * childMax := by
        have hone : 1 ≤ factor := le_max_left _ _
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hone hchildMaxNonneg

/-- Equation (6), sum form: outsider weights accumulate on each literal
child debt, with one copy for that child's preserved parent coordinate. -/
theorem quittingBehaviorEvaluatedTotalDebt_liftDeletedProfile_le
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      CappedClockParentRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorEvaluatedTotalDebt reward evaluation
        (quittingLiftDeletedProfile reward deleted profile) ≤
      ∑ child : QuittingChildPlayer deleted,
        (1 + ∑ outside : {who : α // deleted who},
          (certificate outside).weight child) *
          (quittingBehaviorEvaluatedDeviationPayoffCap
              (quittingDeleteReward reward deleted) evaluation profile child -
            quittingBehaviorEvaluatedPayoff
              (quittingDeleteReward reward deleted) evaluation profile child) := by
  let lifted := quittingLiftDeletedProfile reward deleted profile
  let childReward := quittingDeleteReward reward deleted
  let parentDebt := fun who : α =>
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted who -
      quittingBehaviorEvaluatedPayoff reward evaluation lifted who
  let childDebt := fun who : QuittingChildPlayer deleted =>
    quittingBehaviorEvaluatedDeviationPayoffCap childReward evaluation profile who -
      quittingBehaviorEvaluatedPayoff childReward evaluation profile who
  have hfamily :=
    quittingLiftDeletedProfile_evaluatedDebt_of_cappedClockCertificateFamily
      deleted reward certificate evaluation evaluation_nonneg evaluation_antitone
      profile
  change (∑ who, parentDebt who) ≤
    ∑ child, (1 + ∑ outside : {who : α // deleted who},
      (certificate outside).weight child) * childDebt child
  calc
    (∑ who, parentDebt who) =
        (∑ outside : {who : α // deleted who}, parentDebt outside.1) +
          ∑ child : QuittingChildPlayer deleted, parentDebt child.1 := by
      exact (Fintype.sum_subtype_add_sum_subtype deleted parentDebt).symm
    _ ≤ (∑ outside : {who : α // deleted who},
          ∑ child, (certificate outside).weight child * childDebt child) +
        ∑ child : QuittingChildPlayer deleted, childDebt child := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro outside _
        exact hfamily.2 outside
      · apply Finset.sum_le_sum
        intro child _
        exact le_of_eq (hfamily.1 child)
    _ = ∑ child, (1 + ∑ outside : {who : α // deleted who},
          (certificate outside).weight child) * childDebt child := by
      simp only [add_mul, one_mul, Finset.sum_add_distrib, Finset.sum_mul]
      rw [Finset.sum_comm]
      ac_rfl

end OutsiderFamily

end GameTheory
