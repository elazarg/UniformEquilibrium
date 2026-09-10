import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockMultipleOutsiderRestriction
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPositiveSingletonQuietExtension

/-! # Playerwise capped-clock debt bounds for a family of outsiders -/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- A child own singleton in the retained Option table is literally the
corresponding singleton reward in the original table. -/
theorem quittingChildWithOutsiderReward_singleton_some
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (outside : {who : ι // deleted who})
    (who : QuittingChildPlayer deleted) :
    quittingChildWithOutsiderReward reward deleted outside
        (quittingSingletonTerminal (some who)) (some who) =
      reward (quittingSingletonTerminal who.1) who.1 := by
  change reward _ _ = reward _ _
  congr 1

/-! ## Actual debt transport -/

/-- The two-stage child-plus-one-outsider profile has the same terminal debt
as the direct full quiet lift, player by player. -/
theorem quittingBehaviorDeviationDebt_childWithOutsiderFullProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (outside : {who : ι // deleted who})
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (who : ι) :
    quittingBehaviorDeviationPayoffCap reward
          (quittingChildWithOutsiderFullProfile reward deleted outside profile) who -
        quittingTerminalPayoff reward
          (quittingChildWithOutsiderFullProfile reward deleted outside profile) who =
      quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward deleted profile) who -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) who := by
  rw [quittingBehaviorDeviationPayoffCap_eq_of_behaviorStoppingLaws_eq
      reward _ _
      (quittingBehaviorStoppingLaws_childWithOutsiderFullProfile
        reward deleted outside profile) who,
    quittingTerminalPayoff_eq_of_behaviorStoppingLaws_eq reward _ _
      (quittingBehaviorStoppingLaws_childWithOutsiderFullProfile
        reward deleted outside profile) who]

/-- The displayed Option outsider debt is exactly the corresponding debt in
the actual full child-plus-one-outsider profile. -/
theorem quittingBehaviorDeviationDebt_childWithOutsider_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (outside : {who : ι // deleted who})
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    let optionReward := quittingChildWithOutsiderReward reward deleted outside
    let optionProfile := quittingLiftDeletedProfile optionReward (· = none)
      (quittingChildWithOutsiderChildProfile reward deleted outside profile)
    quittingBehaviorDeviationPayoffCap optionReward optionProfile none -
        quittingTerminalPayoff optionReward optionProfile none =
      quittingBehaviorDeviationPayoffCap reward
          (quittingChildWithOutsiderFullProfile reward deleted outside profile)
          outside.1 -
        quittingTerminalPayoff reward
          (quittingChildWithOutsiderFullProfile reward deleted outside profile)
          outside.1 := by
  dsimp only
  let pairDeleted := fun who : ι => deleted who ∧ who ≠ outside.1
  let pairReward := quittingDeleteReward reward pairDeleted
  let optionReward := quittingChildWithOutsiderReward reward deleted outside
  let optionProfile := quittingLiftDeletedProfile optionReward (· = none)
    (quittingChildWithOutsiderChildProfile reward deleted outside profile)
  let pairPlayer : {who : ι // ¬ pairDeleted who} :=
    ⟨outside.1, fun h => h.2 rfl⟩
  have hequiv : quittingChildWithOutsiderEquiv deleted outside pairPlayer = none := by
    simp [quittingChildWithOutsiderEquiv, pairPlayer, outside.2]
  have hcapPull := quittingBehaviorDeviationPayoffCap_profilePullback
    (quittingChildWithOutsiderEquiv deleted outside) pairReward optionProfile
    pairPlayer
  have hpayoffPull := quittingTerminalPayoff_profilePullback
    (quittingChildWithOutsiderEquiv deleted outside) pairReward optionProfile
    pairPlayer
  rw [hequiv] at hcapPull hpayoffPull
  have hcapLift := quittingBehaviorDeviationPayoffCap_liftDeletedProfile
    reward pairDeleted
    (quittingChildWithOutsiderPairProfile reward deleted outside profile)
    pairPlayer
  have hpayoffLift := quittingTerminalPayoff_liftDeletedProfile
    reward pairDeleted
    (quittingChildWithOutsiderPairProfile reward deleted outside profile)
    pairPlayer
  change quittingBehaviorDeviationPayoffCap pairReward
      (quittingChildWithOutsiderPairProfile reward deleted outside profile)
        pairPlayer =
    quittingBehaviorDeviationPayoffCap optionReward optionProfile none at hcapPull
  change quittingTerminalPayoff optionReward optionProfile none =
    quittingTerminalPayoff pairReward
      (quittingChildWithOutsiderPairProfile reward deleted outside profile)
        pairPlayer at hpayoffPull
  change quittingBehaviorDeviationPayoffCap optionReward optionProfile none -
      quittingTerminalPayoff optionReward optionProfile none = _
  change _ = quittingBehaviorDeviationPayoffCap reward
      (quittingLiftDeletedProfile reward pairDeleted
        (quittingChildWithOutsiderPairProfile reward deleted outside profile))
        pairPlayer.1 -
    quittingTerminalPayoff reward
      (quittingLiftDeletedProfile reward pairDeleted
        (quittingChildWithOutsiderPairProfile reward deleted outside profile))
        pairPlayer.1
  rw [hcapLift, hpayoffLift, ← hcapPull, ← hpayoffPull]

/-- Exact Never/future/joining bounds the actual full-game debt of one outsider by the
weighted actual child debts. -/
theorem quittingLiftDeletedProfile_outsideDebt_le_of_cappedClockCertificate
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (outside : {who : ι // deleted who})
    (certificate : CappedClockParentRewardCertificate
      (quittingChildWithOutsiderReward reward deleted outside))
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
      ∑ who, certificate.weight who *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff
            (quittingDeleteReward reward deleted) profile who) := by
  let optionReward := quittingChildWithOutsiderReward reward deleted outside
  let childProfile :=
    quittingChildWithOutsiderChildProfile reward deleted outside profile
  let optionProfile := quittingLiftDeletedProfile optionReward (· = none) childProfile
  have hoption := quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt
    optionReward certificate childProfile
  have hnone := quittingBehaviorDeviationDebt_childWithOutsider_none
    reward deleted outside profile
  have hsame := quittingBehaviorDeviationDebt_childWithOutsiderFullProfile
    reward deleted outside profile outside.1
  rw [← hsame, ← hnone]
  calc
    quittingBehaviorDeviationPayoffCap optionReward optionProfile none -
        quittingTerminalPayoff optionReward optionProfile none ≤
      ∑ who, certificate.weight who *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward optionReward (· = none)) childProfile
              ⟨some who, Option.some_ne_none who⟩ -
          quittingTerminalPayoff
            (quittingDeleteReward optionReward (· = none)) childProfile
              ⟨some who, Option.some_ne_none who⟩) := by
      simpa [optionReward, optionProfile, childProfile] using hoption
    _ = _ := by
      apply Finset.sum_congr rfl
      intro who _
      dsimp only [optionReward, childProfile]
      change certificate.weight who *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward
              (quittingChildWithOutsiderReward reward deleted outside) (· = none))
            (quittingChildWithOutsiderChildProfile
              reward deleted outside profile)
            (quittingChildSomeEquiv deleted who) -
          quittingTerminalPayoff
            (quittingDeleteReward
              (quittingChildWithOutsiderReward reward deleted outside) (· = none))
            (quittingChildWithOutsiderChildProfile
              reward deleted outside profile)
            (quittingChildSomeEquiv deleted who)) = _
      rw [quittingBehaviorDeviationPayoffCap_childWithOutsiderChildProfile,
        quittingTerminalPayoff_childWithOutsiderChildProfile]

/-- Future and joining rows bound one outsider's actual terminal debt by
weighted child debts plus its Never-row excess times the actual child
joint-Never mass. -/
theorem quittingLiftDeletedProfile_outsideDebt_le_of_cappedClockFutureJoin
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (outside : {who : ι // deleted who})
    (certificate : CappedClockParentFutureJoinCertificate
      (quittingChildWithOutsiderReward reward deleted outside))
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
      (∑ who, certificate.weight who *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff
            (quittingDeleteReward reward deleted) profile who)) +
      cappedClockNeverExcess
          (quittingChildWithOutsiderReward reward deleted outside) certificate *
        ∏ who, (quittingBehaviorStoppingLaw
          (quittingDeleteReward reward deleted) (profile who) none).toReal := by
  let optionReward := quittingChildWithOutsiderReward reward deleted outside
  let childProfile :=
    quittingChildWithOutsiderChildProfile reward deleted outside profile
  let optionProfile := quittingLiftDeletedProfile optionReward (· = none) childProfile
  have hoption :=
    quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_neverExcess
      optionReward certificate childProfile
  have hnone := quittingBehaviorDeviationDebt_childWithOutsider_none
    reward deleted outside profile
  have hsame := quittingBehaviorDeviationDebt_childWithOutsiderFullProfile
    reward deleted outside profile outside.1
  rw [← hsame, ← hnone]
  calc
    quittingBehaviorDeviationPayoffCap optionReward optionProfile none -
        quittingTerminalPayoff optionReward optionProfile none ≤
      (∑ who, certificate.weight who *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward optionReward (· = none)) childProfile
              ⟨some who, Option.some_ne_none who⟩ -
          quittingTerminalPayoff
            (quittingDeleteReward optionReward (· = none)) childProfile
              ⟨some who, Option.some_ne_none who⟩)) +
      cappedClockNeverExcess optionReward certificate *
        ∏ who, (quietOutsiderChildLaws optionReward childProfile who none).toReal := by
      simpa [optionReward, optionProfile, childProfile,
        CappedClockParentFutureJoinCertificate.toSlack] using hoption
    _ = _ := by
      congr 1
      · apply Finset.sum_congr rfl
        intro who _
        change certificate.weight who *
          (quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward
                (quittingChildWithOutsiderReward reward deleted outside)
                  (· = none))
              (quittingChildWithOutsiderChildProfile
                reward deleted outside profile)
              (quittingChildSomeEquiv deleted who) -
            quittingTerminalPayoff
              (quittingDeleteReward
                (quittingChildWithOutsiderReward reward deleted outside)
                  (· = none))
              (quittingChildWithOutsiderChildProfile
                reward deleted outside profile)
              (quittingChildSomeEquiv deleted who)) = _
        rw [quittingBehaviorDeviationPayoffCap_childWithOutsiderChildProfile,
          quittingTerminalPayoff_childWithOutsiderChildProfile]

/-- Future/joining plus a positive child singleton bounds one outsider's actual debt by
the weighted child debts and the singleton correction. -/
theorem quittingLiftDeletedProfile_outsideDebt_le_of_cappedClockPositiveSingleton
    (deleted : ι → Prop) [DecidablePred deleted]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (outside : {who : ι // deleted who})
    (certificate : CappedClockParentFutureJoinCertificate
      (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot.1) pivot.1)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
      (∑ who, certificate.weight who *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff
            (quittingDeleteReward reward deleted) profile who)) +
      (cappedClockNeverExcess
          (quittingChildWithOutsiderReward reward deleted outside) certificate /
        reward (quittingSingletonTerminal pivot.1) pivot.1) *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile pivot -
          quittingTerminalPayoff
            (quittingDeleteReward reward deleted) profile pivot) := by
  letI : Nonempty (QuittingChildPlayer deleted) := ⟨pivot⟩
  let childReward := quittingDeleteReward reward deleted
  let jointNever := ∏ who, (quittingBehaviorStoppingLaw
    childReward (profile who) none).toReal
  let singleton := reward (quittingSingletonTerminal pivot.1) pivot.1
  let pivotDebt := quittingBehaviorDeviationPayoffCap childReward profile pivot -
    quittingTerminalPayoff childReward profile pivot
  have hrelaxed :=
    quittingLiftDeletedProfile_outsideDebt_le_of_cappedClockFutureJoin
      deleted reward outside certificate profile
  have hcharge : jointNever * singleton ≤ pivotDebt := by
    have h := prod_stoppingLaw_none_mul_singleton_le_terminalDebt
      childReward profile pivot
    have hsingletonChild :
        childReward (quittingSingletonTerminal pivot) pivot = singleton := by
      change reward _ _ = reward _ _
      congr 1
    rw [hsingletonChild] at h
    simpa [childReward, jointNever, singleton, pivotDebt,
      quittingTerminalDeviationDebt,
      quittingContinuationBestResponseValue,
      quittingBehaviorDeviationPayoffCap] using h
  have hcoefficient : 0 ≤ cappedClockNeverExcess
        (quittingChildWithOutsiderReward reward deleted outside) certificate /
      singleton :=
    div_nonneg
      (cappedClockNeverExcess_nonneg
        (quittingChildWithOutsiderReward reward deleted outside) certificate)
      hpivot.le
  have hcorrection : cappedClockNeverExcess
        (quittingChildWithOutsiderReward reward deleted outside) certificate *
          jointNever ≤
      (cappedClockNeverExcess
          (quittingChildWithOutsiderReward reward deleted outside) certificate /
        singleton) * pivotDebt := by
    calc
      cappedClockNeverExcess
            (quittingChildWithOutsiderReward reward deleted outside) certificate *
          jointNever =
        (cappedClockNeverExcess
            (quittingChildWithOutsiderReward reward deleted outside) certificate /
          singleton) * (jointNever * singleton) := by
            field_simp [singleton, ne_of_gt hpivot]
      _ ≤ (cappedClockNeverExcess
            (quittingChildWithOutsiderReward reward deleted outside) certificate /
          singleton) * pivotDebt :=
        mul_le_mul_of_nonneg_left hcharge hcoefficient
  exact hrelaxed.trans (by
    simpa only [childReward, jointNever, singleton, pivotDebt, add_comm] using
      add_le_add_right hcorrection
        (∑ who, certificate.weight who *
          (quittingBehaviorDeviationPayoffCap childReward profile who -
            quittingTerminalPayoff childReward profile who)))

end GameTheory
