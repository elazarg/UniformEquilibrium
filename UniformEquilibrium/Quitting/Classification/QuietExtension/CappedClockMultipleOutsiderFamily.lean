import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockMultipleOutsiderDebt

/-! # Capped-clock quiet extension for every outsider -/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The total exact Never/future/joining weight assigned to one outsider. -/
def cappedClockOutsiderWeight
    (deleted : ι → Prop) [DecidablePred deleted]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (certificate : ∀ outside : {who : ι // deleted who},
      CappedClockParentRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (outside : {who : ι // deleted who}) : ℝ :=
  ∑ who, (certificate outside).weight who

/-- The finite maximum of one and all exact outsider weight totals. -/
def cappedClockOutsiderMaxWeight
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty {who : ι // deleted who}]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (certificate : ∀ outside : {who : ι // deleted who},
      CappedClockParentRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside)) : ℝ :=
  max 1 (Finset.univ.sup' Finset.univ_nonempty
    (cappedClockOutsiderWeight deleted reward certificate))

/-- The future/joining weight total for one outsider, including its positive-singleton
Never-row correction. -/
def cappedClockPositiveSingletonOutsiderWeight
    (deleted : ι → Prop) [DecidablePred deleted]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (certificate : ∀ outside : {who : ι // deleted who},
      CappedClockParentFutureJoinCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : {who : ι // deleted who} → QuittingChildPlayer deleted)
    (outside : {who : ι // deleted who}) : ℝ :=
  (∑ who, (certificate outside).weight who) +
    cappedClockNeverExcess
        (quittingChildWithOutsiderReward reward deleted outside)
        (certificate outside) /
      reward (quittingSingletonTerminal (pivot outside).1) (pivot outside).1

/-- The finite maximum of one and all corrected future/joining outsider weights. -/
def cappedClockPositiveSingletonOutsiderMaxWeight
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty {who : ι // deleted who}]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (certificate : ∀ outside : {who : ι // deleted who},
      CappedClockParentFutureJoinCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : {who : ι // deleted who} → QuittingChildPlayer deleted) : ℝ :=
  max 1 (Finset.univ.sup' Finset.univ_nonempty
    (cappedClockPositiveSingletonOutsiderWeight
      deleted reward certificate pivot))

/-! ## Playerwise debt packages -/

/-- Exact Never/future/joining gives the survivor debt identities and every outsider's
weighted actual debt bound in one playerwise package. -/
theorem quittingLiftDeletedProfile_debt_of_cappedClockCertificateFamily
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (certificate : ∀ outside : {who : ι // deleted who},
      CappedClockParentRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    (∀ who : QuittingChildPlayer deleted,
      quittingBehaviorDeviationPayoffCap reward
            (quittingLiftDeletedProfile reward deleted profile) who.1 -
          quittingTerminalPayoff reward
            (quittingLiftDeletedProfile reward deleted profile) who.1 =
        quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff
            (quittingDeleteReward reward deleted) profile who) ∧
    ∀ outside : {who : ι // deleted who},
      quittingBehaviorDeviationPayoffCap reward
            (quittingLiftDeletedProfile reward deleted profile) outside.1 -
          quittingTerminalPayoff reward
            (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
        ∑ who, (certificate outside).weight who *
          (quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward reward deleted) profile who -
            quittingTerminalPayoff
              (quittingDeleteReward reward deleted) profile who) := by
  constructor
  · exact fun who => quittingBehaviorDeviationDebt_liftDeletedProfile
      reward deleted profile who
  · exact fun outside =>
      quittingLiftDeletedProfile_outsideDebt_le_of_cappedClockCertificate
        deleted reward outside (certificate outside) profile

/-- Future and joining rows give survivor debt identities and every
outsider's joint-Never-corrected debt bound in one playerwise package. -/
theorem quittingLiftDeletedProfile_debt_of_cappedClockFutureJoinFamily
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (certificate : ∀ outside : {who : ι // deleted who},
      CappedClockParentFutureJoinCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    (∀ who : QuittingChildPlayer deleted,
      quittingBehaviorDeviationPayoffCap reward
            (quittingLiftDeletedProfile reward deleted profile) who.1 -
          quittingTerminalPayoff reward
            (quittingLiftDeletedProfile reward deleted profile) who.1 =
        quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff
            (quittingDeleteReward reward deleted) profile who) ∧
    ∀ outside : {who : ι // deleted who},
      quittingBehaviorDeviationPayoffCap reward
            (quittingLiftDeletedProfile reward deleted profile) outside.1 -
          quittingTerminalPayoff reward
            (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
        (∑ who, (certificate outside).weight who *
          (quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward reward deleted) profile who -
            quittingTerminalPayoff
              (quittingDeleteReward reward deleted) profile who)) +
        cappedClockNeverExcess
            (quittingChildWithOutsiderReward reward deleted outside)
            (certificate outside) *
          ∏ who, (quittingBehaviorStoppingLaw
            (quittingDeleteReward reward deleted) (profile who) none).toReal := by
  constructor
  · exact fun who => quittingBehaviorDeviationDebt_liftDeletedProfile
      reward deleted profile who
  · exact fun outside =>
      quittingLiftDeletedProfile_outsideDebt_le_of_cappedClockFutureJoin
        deleted reward outside (certificate outside) profile

/-- Future/joining plus one positive child singleton per outsider gives the survivor
identities and all corrected outsider debt bounds. -/
theorem quittingLiftDeletedProfile_debt_of_cappedClockPositiveSingletonFamily
    (deleted : ι → Prop) [DecidablePred deleted]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (certificate : ∀ outside : {who : ι // deleted who},
      CappedClockParentFutureJoinCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : {who : ι // deleted who} → QuittingChildPlayer deleted)
    (hpivot : ∀ outside, 0 <
      reward (quittingSingletonTerminal (pivot outside).1) (pivot outside).1)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    (∀ who : QuittingChildPlayer deleted,
      quittingBehaviorDeviationPayoffCap reward
            (quittingLiftDeletedProfile reward deleted profile) who.1 -
          quittingTerminalPayoff reward
            (quittingLiftDeletedProfile reward deleted profile) who.1 =
        quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff
            (quittingDeleteReward reward deleted) profile who) ∧
    ∀ outside : {who : ι // deleted who},
      quittingBehaviorDeviationPayoffCap reward
            (quittingLiftDeletedProfile reward deleted profile) outside.1 -
          quittingTerminalPayoff reward
            (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
        (∑ who, (certificate outside).weight who *
          (quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward reward deleted) profile who -
            quittingTerminalPayoff
              (quittingDeleteReward reward deleted) profile who)) +
        (cappedClockNeverExcess
            (quittingChildWithOutsiderReward reward deleted outside)
              (certificate outside) /
          reward (quittingSingletonTerminal (pivot outside).1)
            (pivot outside).1) *
          (quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward reward deleted) profile (pivot outside) -
            quittingTerminalPayoff
              (quittingDeleteReward reward deleted) profile
                (pivot outside)) := by
  constructor
  · exact fun who => quittingBehaviorDeviationDebt_liftDeletedProfile
      reward deleted profile who
  · exact fun outside =>
      quittingLiftDeletedProfile_outsideDebt_le_of_cappedClockPositiveSingleton
        deleted reward outside (certificate outside) (pivot outside)
          (hpivot outside) profile

/-! ## Maximum-regret and fixed-target consumers -/

/-- Every displayed exact outsider weight is below the family maximum. -/
theorem cappedClockOutsiderWeight_le_maxWeight
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty {who : ι // deleted who}]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (certificate : ∀ outside : {who : ι // deleted who},
      CappedClockParentRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (outside : {who : ι // deleted who}) :
    cappedClockOutsiderWeight deleted reward certificate outside ≤
      cappedClockOutsiderMaxWeight deleted reward certificate := by
  apply le_trans (Finset.le_sup'
    (f := cappedClockOutsiderWeight deleted reward certificate)
    (Finset.mem_univ outside))
  exact le_max_right _ _

/-- Exact Never/future/joining for every outsider lifts each child terminal approximate
equilibrium with the maximum outsider weight, not a sum over outsiders. -/
theorem isεAsymptoticNash_liftDeletedProfile_of_cappedClockCertificateFamily
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : ι // deleted who}]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (certificate : ∀ outside : {who : ι // deleted who},
      CappedClockParentRewardCertificate
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
      (cappedClockOutsiderMaxWeight deleted reward certificate * error)
      (quittingLiftDeletedProfile reward deleted profile) := by
  let factor := cappedClockOutsiderMaxWeight deleted reward certificate
  let lifted := quittingLiftDeletedProfile reward deleted profile
  have hchildDebt (who : QuittingChildPlayer deleted) :
      quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff
            (quittingDeleteReward reward deleted) profile who ≤ error := by
    rw [quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
    apply sub_le_iff_le_add.mpr
    apply quittingBestReplyValue_le
    intro deviation
    have h := hnash who deviation
    linarith
  have hfamily :=
    quittingLiftDeletedProfile_debt_of_cappedClockCertificateFamily
      deleted reward certificate profile
  have hdebt (who : ι) :
      quittingBehaviorDeviationPayoffCap reward lifted who -
          quittingTerminalPayoff reward lifted who ≤ factor * error := by
    by_cases hdeleted : deleted who
    · let outside : {who : ι // deleted who} := ⟨who, hdeleted⟩
      calc
        quittingBehaviorDeviationPayoffCap reward lifted who -
            quittingTerminalPayoff reward lifted who ≤
          ∑ child, (certificate outside).weight child *
            (quittingBehaviorDeviationPayoffCap
                (quittingDeleteReward reward deleted) profile child -
              quittingTerminalPayoff
                (quittingDeleteReward reward deleted) profile child) :=
          hfamily.2 outside
        _ ≤ ∑ child, (certificate outside).weight child * error := by
          apply Finset.sum_le_sum
          intro child _
          exact mul_le_mul_of_nonneg_left
            (hchildDebt child) ((certificate outside).weight_nonneg child)
        _ = cappedClockOutsiderWeight deleted reward certificate outside *
            error := by
          rw [← Finset.sum_mul]
          rfl
        _ ≤ factor * error := by
          exact mul_le_mul_of_nonneg_right
            (cappedClockOutsiderWeight_le_maxWeight
              deleted reward certificate outside) herror
    · let child : QuittingChildPlayer deleted := ⟨who, hdeleted⟩
      calc
        quittingBehaviorDeviationPayoffCap reward lifted who -
            quittingTerminalPayoff reward lifted who =
          quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward reward deleted) profile child -
            quittingTerminalPayoff
              (quittingDeleteReward reward deleted) profile child :=
          hfamily.1 child
        _ ≤ error := hchildDebt child
        _ ≤ factor * error := by
          have hone : 1 ≤ factor := le_max_left _ _
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hone herror
  intro who deviation
  have hdeviation := le_quittingBestReplyValue reward lifted who deviation
  rw [← quittingBehaviorDeviationPayoffCap_eq_bestReplyValue] at hdeviation
  change quittingTerminalPayoff reward lifted who + factor * error ≥ _
  linarith [hdebt who]

/-- Every specified child uniform-equilibrium target extends under an exact
Never/future/joining certificate for each outsider. -/
theorem exists_uniformEquilibriumPayoff_eq_on_child_of_cappedClockCertificateFamily
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : ι // deleted who}]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (certificate : ∀ outside : {who : ι // deleted who},
      CappedClockParentRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (target : Payoff (QuittingChildPlayer deleted))
    (htarget : (quittingGame
      (quittingDeleteReward reward deleted)).IsUniformEquilibriumPayoff
        none target) :
    ∃ payoff : Payoff ι,
      (∀ who : QuittingChildPlayer deleted, payoff who.1 = target who) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact exists_uniformEquilibriumPayoff_eq_on_image_of_terminalNash_lift
    reward (quittingDeleteReward reward deleted) (fun who => who.1)
    (quittingLiftDeletedProfile reward deleted)
    (cappedClockOutsiderMaxWeight deleted reward certificate)
    (fun profile who =>
      quittingTerminalPayoff_liftDeletedProfile reward deleted profile who)
    (fun herror profile hnash =>
      isεAsymptoticNash_liftDeletedProfile_of_cappedClockCertificateFamily
        deleted reward certificate herror profile hnash)
    target htarget

/-- Every corrected future/joining outsider weight is below its family maximum. -/
theorem cappedClockPositiveSingletonOutsiderWeight_le_maxWeight
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty {who : ι // deleted who}]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (certificate : ∀ outside : {who : ι // deleted who},
      CappedClockParentFutureJoinCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : {who : ι // deleted who} → QuittingChildPlayer deleted)
    (outside : {who : ι // deleted who}) :
    cappedClockPositiveSingletonOutsiderWeight
        deleted reward certificate pivot outside ≤
      cappedClockPositiveSingletonOutsiderMaxWeight
        deleted reward certificate pivot := by
  apply le_trans (Finset.le_sup'
    (f := cappedClockPositiveSingletonOutsiderWeight
      deleted reward certificate pivot)
    (Finset.mem_univ outside))
  exact le_max_right _ _

/-- Future/joining and one positive child singleton per outsider lift every child
terminal approximate equilibrium with the maximum corrected outsider weight. -/
theorem isεAsymptoticNash_liftDeletedProfile_of_cappedClockPositiveSingletonFamily
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty {who : ι // deleted who}]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (certificate : ∀ outside : {who : ι // deleted who},
      CappedClockParentFutureJoinCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : {who : ι // deleted who} → QuittingChildPlayer deleted)
    (hpivot : ∀ outside, 0 <
      reward (quittingSingletonTerminal (pivot outside).1) (pivot outside).1)
    {error : ℝ} (herror : 0 ≤ error)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (hnash : (quittingGame
      (quittingDeleteReward reward deleted)).IsεAsymptoticNash
        (quittingTerminalPayoff (quittingDeleteReward reward deleted))
        error profile) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (cappedClockPositiveSingletonOutsiderMaxWeight
        deleted reward certificate pivot * error)
      (quittingLiftDeletedProfile reward deleted profile) := by
  let factor := cappedClockPositiveSingletonOutsiderMaxWeight
    deleted reward certificate pivot
  let lifted := quittingLiftDeletedProfile reward deleted profile
  have hchildDebt (who : QuittingChildPlayer deleted) :
      quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff
            (quittingDeleteReward reward deleted) profile who ≤ error := by
    rw [quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
    apply sub_le_iff_le_add.mpr
    apply quittingBestReplyValue_le
    intro deviation
    have h := hnash who deviation
    linarith
  have hfamily :=
    quittingLiftDeletedProfile_debt_of_cappedClockPositiveSingletonFamily
      deleted reward certificate pivot hpivot profile
  have hdebt (who : ι) :
      quittingBehaviorDeviationPayoffCap reward lifted who -
          quittingTerminalPayoff reward lifted who ≤ factor * error := by
    by_cases hdeleted : deleted who
    · let outside : {who : ι // deleted who} := ⟨who, hdeleted⟩
      let correction := cappedClockNeverExcess
          (quittingChildWithOutsiderReward reward deleted outside)
            (certificate outside) /
        reward (quittingSingletonTerminal (pivot outside).1) (pivot outside).1
      have hcorrection : 0 ≤ correction :=
        div_nonneg
          (cappedClockNeverExcess_nonneg
            (quittingChildWithOutsiderReward reward deleted outside)
              (certificate outside))
          (hpivot outside).le
      calc
        quittingBehaviorDeviationPayoffCap reward lifted who -
            quittingTerminalPayoff reward lifted who ≤
          (∑ child, (certificate outside).weight child *
            (quittingBehaviorDeviationPayoffCap
                (quittingDeleteReward reward deleted) profile child -
              quittingTerminalPayoff
                (quittingDeleteReward reward deleted) profile child)) +
          correction *
            (quittingBehaviorDeviationPayoffCap
                (quittingDeleteReward reward deleted) profile (pivot outside) -
              quittingTerminalPayoff
                (quittingDeleteReward reward deleted) profile
                  (pivot outside)) := hfamily.2 outside
        _ ≤ (∑ child, (certificate outside).weight child * error) +
            correction * error := by
          apply add_le_add
          · apply Finset.sum_le_sum
            intro child _
            exact mul_le_mul_of_nonneg_left
              (hchildDebt child) ((certificate outside).weight_nonneg child)
          · exact mul_le_mul_of_nonneg_left
              (hchildDebt (pivot outside)) hcorrection
        _ = cappedClockPositiveSingletonOutsiderWeight
              deleted reward certificate pivot outside * error := by
          rw [← Finset.sum_mul]
          dsimp [cappedClockPositiveSingletonOutsiderWeight, correction]
          ring
        _ ≤ factor * error := by
          exact mul_le_mul_of_nonneg_right
            (cappedClockPositiveSingletonOutsiderWeight_le_maxWeight
              deleted reward certificate pivot outside) herror
    · let child : QuittingChildPlayer deleted := ⟨who, hdeleted⟩
      calc
        quittingBehaviorDeviationPayoffCap reward lifted who -
            quittingTerminalPayoff reward lifted who =
          quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward reward deleted) profile child -
            quittingTerminalPayoff
              (quittingDeleteReward reward deleted) profile child :=
          hfamily.1 child
        _ ≤ error := hchildDebt child
        _ ≤ factor * error := by
          have hone : 1 ≤ factor := le_max_left _ _
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hone herror
  intro who deviation
  have hdeviation := le_quittingBestReplyValue reward lifted who deviation
  rw [← quittingBehaviorDeviationPayoffCap_eq_bestReplyValue] at hdeviation
  change quittingTerminalPayoff reward lifted who + factor * error ≥ _
  linarith [hdebt who]

/-- Every specified child uniform-equilibrium target extends under future/joining and a
positive child singleton chosen separately for each outsider. -/
theorem
    exists_uniformEquilibriumPayoff_eq_on_child_of_cappedClockPositiveSingletonFamily
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty {who : ι // deleted who}]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (certificate : ∀ outside : {who : ι // deleted who},
      CappedClockParentFutureJoinCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : {who : ι // deleted who} → QuittingChildPlayer deleted)
    (hpivot : ∀ outside, 0 <
      reward (quittingSingletonTerminal (pivot outside).1) (pivot outside).1)
    (target : Payoff (QuittingChildPlayer deleted))
    (htarget : (quittingGame
      (quittingDeleteReward reward deleted)).IsUniformEquilibriumPayoff
        none target) :
    ∃ payoff : Payoff ι,
      (∀ who : QuittingChildPlayer deleted, payoff who.1 = target who) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact exists_uniformEquilibriumPayoff_eq_on_image_of_terminalNash_lift
    reward (quittingDeleteReward reward deleted) (fun who => who.1)
    (quittingLiftDeletedProfile reward deleted)
    (cappedClockPositiveSingletonOutsiderMaxWeight
      deleted reward certificate pivot)
    (fun profile who =>
      quittingTerminalPayoff_liftDeletedProfile reward deleted profile who)
    (fun herror profile hnash =>
      isεAsymptoticNash_liftDeletedProfile_of_cappedClockPositiveSingletonFamily
        deleted reward certificate pivot hpivot herror profile hnash)
    target htarget

end GameTheory
