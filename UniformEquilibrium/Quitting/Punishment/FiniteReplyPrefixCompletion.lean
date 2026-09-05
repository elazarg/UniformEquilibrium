import UniformEquilibrium.Quitting.Punishment.FinitePureReplyValue
import UniformEquilibrium.Quitting.Debt.Ledger.OpponentLedgerRemainder
import UniformEquilibrium.Quitting.Root.StationaryTailSplice
import UniformEquilibrium.Quitting.Root.FiniteRootWordCapTailBound
import UniformEquilibrium.Quitting.Root.CorrectedNeverPrefixPayoff
import UniformEquilibrium.Quitting.Paths.LiveRootSurvival
import UniformEquilibrium.Quitting.Punishment.InstantPunishment
import UniformEquilibrium.Quitting.Terminal.TargetTail.DiagonalTargetTailSelection

/-! # Complete opponent-prefix completion from finite-date response bounds -/

noncomputable section

namespace GameTheory

open Set Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual source's deleted survival converges to the opponents' Never
product extracted from that same source, including zero-probability histories. -/
theorem quittingOpponentSurvivalWeight_profileLiveRoot_tendsto_neverProduct
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    Tendsto (quittingOpponentSurvivalWeight (quittingProfileLiveRoot reward profile) who 0)
      atTop (nhds (quittingOpponentNeverProduct
        (quittingCompactStoppingLawsOfProfile reward profile) who)) := by
  have hproduct : quittingOpponentNeverProduct
      (quittingCompactStoppingLawsOfProfile reward profile) who =
      ∏ opponent ∈ Finset.univ.erase who,
        quittingHazardNeverMass (quittingBehaviorLiveHazard reward (profile opponent)) := by
    unfold quittingOpponentNeverProduct quittingCompactStoppingLawsOfProfile
    apply Finset.prod_congr rfl
    intro opponent _
    change (((_root_.Math.Probability.CompactStoppingLaw.ofPMF
      (quittingBehaviorStoppingLaw reward (profile opponent))).toPMF ⊤)).toReal = _
    rw [_root_.Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    exact quittingBehaviorStoppingLaw_none_toReal reward (profile opponent)
  rw [hproduct]
  have h := tendsto_finsetProd (Finset.univ.erase who) fun opponent _ ↦
    tendsto_quittingHazardSurvival_neverMass
      (quittingBehaviorLiveHazard reward (profile opponent))
  convert h using 1
  funext time
  rw [quittingOpponentSurvivalWeight_eq_prod_hazardSurvival]
  rfl

/-- The same source's finite-date bound controls all early responses; its
actual Never ledger controls every response entering the selected tail. -/
theorem quittingCap_stationaryTailSplice_le_finiteReply_and_lateLedger
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (cutoff : ℕ)
    (root : ι → PMF Bool) {bound : ℝ}
    (hreward : ∀ terminal, |reward terminal who| ≤ bound) :
    quittingContinuationBestResponseValue reward
        (quittingStationaryTailSpliceProfile reward profile cutoff root) who ≤
      max (quittingFinitePureReplyValue reward profile who)
        (quittingTerminalPayoff reward (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who none)) who +
          bound * (quittingOpponentSurvivalWeight
              (quittingProfileLiveRoot reward profile) who 0 cutoff -
            quittingOpponentNeverProduct (quittingCompactStoppingLawsOfProfile reward profile)
              who) +
          quittingOpponentSurvivalWeight (quittingProfileLiveRoot reward profile) who 0 cutoff *
            quittingStationaryUnilateralCap reward root who) := by
  let roots := quittingProfileLiveRoot reward profile
  rw [quittingContinuationBestResponseValue_congr_profileLiveRoot reward _ _
      (quittingProfileLiveRoot_stationaryTailSplice_eq_literalRootStack
        reward profile cutoff root) who,
    quittingContinuationBestResponseValue_literalRootStack_eq_capFold]
  change quittingFiniteRootWordCap reward
      (List.ofFn fun time : Fin cutoff ↦ roots time.val) who
      (quittingBestReplyValue reward (quittingStationaryProfile reward root) who) ≤ _
  rw [quittingBestReplyValue_stationary]
  have henvelope := quittingFiniteRootWordCap_le_max_pureTime_and_tail reward roots who cutoff
    (quittingStationaryUnilateralCap reward root who)
    (quittingFinitePureReplyValue reward profile who) (fun time _ ↦ by
      simpa only [quittingTerminalPayoff_update_pureTimeBehaviorStrategy] using
        quittingTerminalPayoff_finiteTime_le_finitePureReplyValue reward profile who time)
  apply henvelope.trans
  apply max_le_max le_rfl
  have hrem := abs_quittingNeverValue_sub_ledger_le_survival_remainder
    reward roots who cutoff hreward
    (quittingOpponentSurvivalWeight_profileLiveRoot_tendsto_neverProduct reward profile who)
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  have h := neg_le_of_abs_le hrem
  linarith

theorem quittingOpponentNeverProduct_le_profileSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (cutoff : ℕ) :
    quittingOpponentNeverProduct (quittingCompactStoppingLawsOfProfile reward profile) who ≤
      quittingOpponentSurvivalWeight (quittingProfileLiveRoot reward profile) who 0 cutoff := by
  apply le_of_tendsto
    (quittingOpponentSurvivalWeight_profileLiveRoot_tendsto_neverProduct reward profile who)
  filter_upwards [eventually_ge_atTop cutoff] with time htime
  exact antitone_quittingOpponentSurvivalWeight _ who 0 htime

/-- An arbitrary stationary tail costs at most the small deleted reach plus
the source's late finite opponent-absorption remainder. -/
theorem quittingCap_stationaryTailSplice_le_finiteReply_add_clockError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (cutoff : ℕ)
    (root : ι → PMF Bool) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingContinuationBestResponseValue reward
        (quittingStationaryTailSpliceProfile reward profile cutoff root) who ≤
      quittingFinitePureReplyValue reward profile who +
        2 * bound * quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward profile) who 0 cutoff +
        bound * (quittingOpponentSurvivalWeight (quittingProfileLiveRoot reward profile)
            who 0 cutoff - quittingOpponentNeverProduct
              (quittingCompactStoppingLawsOfProfile reward profile) who) := by
  let roots := quittingProfileLiveRoot reward profile
  let deleted := quittingOpponentNeverProduct (quittingCompactStoppingLawsOfProfile reward profile)
    who
  have hbound : 0 ≤ bound := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who) who)
  have hsurv := quittingOpponentSurvivalWeight_nonneg roots who 0 cutoff
  have hdeleted : 0 ≤ deleted := ge_of_tendsto
    (quittingOpponentSurvivalWeight_profileLiveRoot_tendsto_neverProduct reward profile who)
    (Eventually.of_forall fun time ↦ quittingOpponentSurvivalWeight_nonneg roots who 0 time)
  have hle := quittingOpponentNeverProduct_le_profileSurvival reward profile who cutoff
  have hlate := neverPayoff_add_opponentNever_mul_solo_le_finitePureReplyValue
    reward profile who
  have hroot : quittingStationaryUnilateralCap reward root who ≤ bound := by
    rw [← quittingBestReplyValue_stationary reward root who]
    exact le_of_abs_le (abs_quittingContinuationBestResponseValue_le reward
      (quittingStationaryProfile reward root) who hreward)
  apply (quittingCap_stationaryTailSplice_le_finiteReply_and_lateLedger
    reward profile who cutoff root (fun terminal ↦ hreward terminal who)).trans
  apply max_le
  · have hrem := mul_nonneg hbound (sub_nonneg.mpr hle)
    have hclock := mul_nonneg hbound hsurv
    linarith
  · have htail := mul_le_mul_of_nonneg_left hroot hsurv
    have hsolo := mul_le_mul_of_nonneg_left
      (neg_le_of_abs_le (hreward (quittingSingletonTerminal who) who)) hdeleted
    have hclock := mul_le_mul_of_nonneg_left hle hbound
    change 0 ≤ deleted at hdeleted
    dsimp only [deleted, roots] at hsurv htail hsolo
    nlinarith

/-- A preselected approximate punishment tail replaces the deleted-reach
cost by a vanishing late-absorption error, using original punishment normality. -/
theorem quittingCap_stationaryTailSplice_le_finiteReply_of_punishment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (cutoff : ℕ)
    (root : ι → PMF Bool) {bound slack : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hslack : 0 ≤ slack)
    (hnormal : quittingPunishmentValue reward who ≤ quittingSoloReward reward who who)
    (hroot : quittingStationaryUnilateralCap reward root who ≤
      quittingPunishmentValue reward who + slack) :
    quittingContinuationBestResponseValue reward
        (quittingStationaryTailSpliceProfile reward profile cutoff root) who ≤
      quittingFinitePureReplyValue reward profile who +
        2 * bound * (quittingOpponentSurvivalWeight (quittingProfileLiveRoot reward profile)
            who 0 cutoff - quittingOpponentNeverProduct
              (quittingCompactStoppingLawsOfProfile reward profile) who) + slack := by
  let roots := quittingProfileLiveRoot reward profile
  have hbound : 0 ≤ bound := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who) who)
  have hsurv := quittingOpponentSurvivalWeight_nonneg roots who 0 cutoff
  have hone := quittingOpponentSurvivalWeight_le_one roots who 0 cutoff
  have hle := quittingOpponentNeverProduct_le_profileSurvival reward profile who cutoff
  have hlate := neverPayoff_add_opponentNever_mul_solo_le_finitePureReplyValue
    reward profile who
  have htail := mul_le_mul_of_nonneg_left hroot hsurv
  have hnormal' := mul_le_mul_of_nonneg_left hnormal hsurv
  have hslack' := mul_le_mul_of_nonneg_right hone hslack
  have hsolo := mul_le_mul_of_nonneg_left
    (le_of_abs_le (hreward (quittingSingletonTerminal who) who)) (sub_nonneg.mpr hle)
  apply (quittingCap_stationaryTailSplice_le_finiteReply_and_lateLedger
    reward profile who cutoff root (fun terminal ↦ hreward terminal who)).trans
  apply max_le
  · have hrem := mul_nonneg hbound (sub_nonneg.mpr hle)
    linarith
  · change quittingPunishmentValue reward who ≤ reward (quittingSingletonTerminal who) who
      at hnormal
    change quittingOpponentSurvivalWeight roots who 0 cutoff * quittingPunishmentValue reward who ≤
      quittingOpponentSurvivalWeight roots who 0 cutoff * reward (quittingSingletonTerminal who) who
      at hnormal'
    dsimp only [roots] at htail hnormal' hslack'
    nlinarith

omit [DecidableEq ι] in
theorem quittingJointSurvivalLimit_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingJointSurvivalLimit (quittingProfileLiveRoot reward profile) 0 =
      quittingLiveMassLimit reward profile := by
  apply tendsto_nhds_unique (tendsto_quittingJointSurvivalLimit _ 0)
  convert tendsto_quittingLiveMass reward profile using 1
  funext time
  exact (quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot reward profile time).symm

omit [DecidableEq ι] in
/-- The payoff estimate applies to the original profile, with every source
history retained before the cutoff and any bounded alternative Never reward. -/
theorem abs_quittingStationaryTailSplicePayoff_sub_corrected_source_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ)
    (root : ι → PMF Bool) (who : ι) {bound correction : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hcorrection : |correction| ≤ bound) :
    |quittingTerminalPayoff reward
        (quittingStationaryTailSpliceProfile reward profile cutoff root) who -
      (quittingTerminalPayoff reward profile who +
        correction * quittingLiveMassLimit reward profile)| ≤
      2 * bound * quittingLiveMass reward profile cutoff := by
  rw [quittingTerminalPayoff_congr_profileLiveRoot reward _ _
      (quittingProfileLiveRoot_stationaryTailSplice_eq_literalRootStack
        reward profile cutoff root) who,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot reward profile,
    ← quittingJointSurvivalLimit_profileLiveRoot reward profile,
    quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
  exact abs_quittingLiteralRootStackPayoff_sub_corrected_rootSequence_le reward
    (quittingProfileLiveRoot reward profile) cutoff (quittingStationaryProfile reward root)
    who hreward hcorrection

/-- Source-derived completion: one actual cutoff, one fixed target, and one
stationary punishment root work simultaneously for every player. The finite
reply bound always refers to the original complete source profile. -/
theorem exists_stationaryTailSplice_finiteReply_completion [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {bound reach tolerance slack : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤ quittingSoloReward reward who who)
    (hreach : quittingLiveMassLimit reward profile < reach)
    (htolerance : 0 < tolerance) (hslack : 0 < slack) :
    ∃ cutoff : ℕ, ∃ target : ι, ∃ root : ι → PMF Bool,
      quittingStationaryUnilateralCap reward root target <
        quittingPunishmentValue reward target + slack ∧
      quittingLiveMass reward profile cutoff < reach ∧
      (∀ time < cutoff, ∀ who (history : (quittingGame reward).Hist time),
        quittingStationaryTailSpliceProfile reward profile cutoff root who time history =
          profile who time history) ∧
      (∀ who, quittingContinuationBestResponseValue reward
          (quittingStationaryTailSpliceProfile reward profile cutoff root) who ≤
        quittingFinitePureReplyValue reward profile who +
          2 * bound * Real.sqrt reach + 2 * bound * tolerance + slack) ∧
      (∀ who correction, |correction| ≤ bound →
        |quittingTerminalPayoff reward
            (quittingStationaryTailSpliceProfile reward profile cutoff root) who -
          (quittingTerminalPayoff reward profile who +
            correction * quittingLiveMassLimit reward profile)| ≤ 2 * bound * reach) := by
  let witness : ι := Classical.choice inferInstance
  let roots := quittingProfileLiveRoot reward profile
  have hbound : 0 ≤ bound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal witness) witness)
  have hreachpos : 0 < reach :=
    (quittingLiveMassLimit_nonneg reward profile).trans_lt hreach
  have hearly := (tendsto_quittingLiveMass reward profile).eventually (gt_mem_nhds hreach)
  have hlate (who : ι) : ∀ᶠ cutoff in atTop,
      quittingOpponentSurvivalWeight roots who 0 cutoff -
        quittingOpponentNeverProduct (quittingCompactStoppingLawsOfProfile reward profile) who <
      tolerance := by
    have h : Tendsto (fun cutoff ↦ quittingOpponentSurvivalWeight roots who 0 cutoff -
        quittingOpponentNeverProduct (quittingCompactStoppingLawsOfProfile reward profile) who)
        atTop (nhds 0) := by
      simpa only [sub_self] using
        (quittingOpponentSurvivalWeight_profileLiveRoot_tendsto_neverProduct
          reward profile who).sub_const
          (quittingOpponentNeverProduct (quittingCompactStoppingLawsOfProfile reward profile) who)
    exact h.eventually (gt_mem_nhds htolerance)
  obtain ⟨cutoff, hcutoff, hlate⟩ := (hearly.and (Filter.eventually_all.mpr hlate)).exists
  obtain ⟨target, htarget⟩ :=
    exists_target_forall_opponentSurvivalWeight_le_of_joint_le_sq roots cutoff
      (Real.sqrt_nonneg reach) (by
        rw [Real.sq_sqrt hreachpos.le]
        simpa only [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot] using hcutoff.le)
  obtain ⟨root, hroot⟩ := exists_quittingStationaryPunishmentRoot_lt_add reward target hslack
  refine ⟨cutoff, target, root, hroot, hcutoff, ?_, ?_, ?_⟩
  · intro time htime who history
    exact quittingStationaryTailSpliceProfile_of_lt reward profile cutoff root htime who history
  · intro who
    by_cases hwho : who = target
    · subst who
      have h := quittingCap_stationaryTailSplice_le_finiteReply_of_punishment
        reward profile target cutoff root hreward hslack.le (hnormal target) hroot.le
      have hsmall := mul_le_mul_of_nonneg_left (hlate target).le (by positivity : 0 ≤ 2 * bound)
      have hrootReach := mul_nonneg hbound (Real.sqrt_nonneg reach)
      linarith
    · have h := quittingCap_stationaryTailSplice_le_finiteReply_add_clockError
        reward profile who cutoff root hreward
      have hsmall := mul_le_mul_of_nonneg_left (hlate who).le hbound
      have hclock := mul_le_mul_of_nonneg_left (htarget who hwho) (by positivity : 0 ≤ 2 * bound)
      have htol := mul_nonneg hbound htolerance.le
      dsimp only [roots] at hsmall hclock
      linarith
  · intro who correction hcorrection
    exact (abs_quittingStationaryTailSplicePayoff_sub_corrected_source_le
      reward profile cutoff root who hreward hcorrection).trans
        (mul_le_mul_of_nonneg_left hcutoff.le (by positivity))

end GameTheory
