/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreement
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticForcedOwnerRefusalCollector
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect

/-!
# Temporal orientation of a paid first disagreement

If the receiving witness is later, its positive edge is already one legal
owner deviation from the earlier pure-time profile.  If it is earlier, the
receiving witness Quits surely at the reached row.  Its approximate
optimality bounds the live-mass-weighted forced-owner refusal at that row.
Combining this bound with the atomic blocker barrier forces a legal outsider
endpoint whenever the approximation error is below the quantitative
threshold.

This is an orientation result, not a claim that the resulting outsider row
has been re-entered into any reset cube or chronological producer.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A player who deterministically Continues before `stop` makes joint live
mass at `stop` equal the opponents' deleted survival to that date. -/
theorem quittingLiveMass_update_pureTime_some_eq_opponentSurvivalWeight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (stop : ℕ) :
    quittingLiveMass reward
        (Function.update profile owner
          (quittingPureTimeBehaviorStrategy reward owner (some stop))) stop =
      quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) owner 0 stop := by
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    quittingJointSurvivalWeight_eq_prod]
  unfold quittingOpponentSurvivalWeight
  simp only [Nat.zero_add]
  apply Finset.prod_congr rfl
  intro offset hoffset
  have hoffsetLt : offset < stop := Finset.mem_range.mp hoffset
  change quittingStationaryContinueMass
      (quittingProfileLiveRoot reward
        (Function.update profile owner
          (quittingPureTimeBehaviorStrategy reward owner (some stop)))
        offset) =
    quittingFixedOpponentsContinueMass
      (quittingProfileLiveRoot reward profile) owner offset
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingBehaviorLiveHazard_pureTimeBehaviorStrategy]
  unfold quittingRootSequenceUpdate quittingFixedOpponentsContinueMass
  rw [quittingPureTimeHazard_some_of_ne (ne_of_lt hoffsetLt)]

/-- In the later-receiving orientation, the receiving edge is a legal owner
deviation from the earlier pure-time profile, with the full source-unit
gain. -/
theorem QuittingPaidFirstDisagreementRow.exists_ownerDeviation_of_receivingLater
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {receiving : (quittingGame reward).BehaviorProfile}
    {observer : ι} {gain : ℝ}
    (row : QuittingPaidFirstDisagreementRow reward receiving observer gain)
    (_hlater : row.receivingEarlier = false) :
    let earlierProfile := Function.update receiving observer
      (quittingPureTimeBehaviorStrategy reward observer row.sourceWitness)
    ∃ deviation : (quittingGame reward).BehaviorStrategy observer,
      quittingTerminalPayoff reward earlierProfile observer + gain ≤
        quittingTerminalPayoff reward
          (Function.update earlierProfile observer deviation) observer := by
  dsimp only
  refine ⟨quittingPureTimeBehaviorStrategy reward observer
    row.receivingWitness, ?_⟩
  rw [Function.update_idem]
  have hedge := row.gain_le_paid.trans_eq row.edge_identity.symm
  unfold quittingPureTimeDeviationPayoff at hedge
  linarith

/-- Approximate optimality of the earlier receiving witness bounds its
literal semantic debt after the owner is replaced by that witness. -/
theorem QuittingPaidFirstDisagreementRow.receivingProfile_debt_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {receiving : (quittingGame reward).BehaviorProfile}
    {observer : ι} {gain eta : ℝ}
    (row : QuittingPaidFirstDisagreementRow reward receiving observer gain)
    (happrox :
      quittingContinuationBestResponseValue reward receiving observer - eta ≤
        quittingPureTimeDeviationPayoff reward receiving observer
          row.receivingWitness) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update receiving observer
            (quittingPureTimeBehaviorStrategy reward observer
              row.receivingWitness))) observer ≤ eta := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change quittingContinuationBestResponseValue reward
        (Function.update receiving observer
          (quittingPureTimeBehaviorStrategy reward observer
            row.receivingWitness)) observer -
      quittingTerminalPayoff reward
        (Function.update receiving observer
          (quittingPureTimeBehaviorStrategy reward observer
            row.receivingWitness)) observer ≤ eta
  rw [quittingContinuationBestResponseValue_update_self]
  unfold quittingPureTimeDeviationPayoff at happrox
  linarith

/-- In the earlier-receiving orientation, the reached forced-owner refusal,
weighted by the exact first-disagreement live mass, is at most the receiving
witness's approximation error.  This is the literal one-row refusal/debt
collector, not a reset-cube curvature estimate. -/
theorem QuittingPaidFirstDisagreementRow.liveMass_mul_forcedRefusal_le_eta
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {receiving : (quittingGame reward).BehaviorProfile}
    {observer : ι} {gain eta : ℝ}
    (row : QuittingPaidFirstDisagreementRow reward receiving observer gain)
    (hearlier : row.receivingEarlier = true)
    (happrox :
      quittingContinuationBestResponseValue reward receiving observer - eta ≤
        quittingPureTimeDeviationPayoff reward receiving observer
          row.receivingWitness) :
    let profile := Function.update receiving observer
      (quittingPureTimeBehaviorStrategy reward observer row.receivingWitness)
    let root := quittingProfileLiveRoot reward profile row.start
    row.liveMass *
        max 0 (-quittingAtomicBlockerBalance reward root observer) ≤ eta := by
  dsimp only
  have hchronology := row.chronology
  rw [hearlier] at hchronology
  simp only [if_true] at hchronology
  let profile := Function.update receiving observer
    (quittingPureTimeBehaviorStrategy reward observer row.receivingWitness)
  let root := quittingProfileLiveRoot reward profile row.start
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (row.start + 1))
  let current := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile row.start)
  let refusal := max 0
    (-quittingAtomicBlockerBalance reward root observer)
  have howner : root observer = PMF.pure true := by
    dsimp only [root, profile]
    rw [hchronology.1, quittingProfileLiveRoot_update_pureTime_self,
      quittingPureTimeHazard_some_self]
  have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have htailDebt : 0 ≤ quittingTerminalSemanticDebt tail observer :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward htailCarrier observer
  have hfloor : quittingPunishmentValue reward observer ≤ tail.2 observer := by
    have h := quittingPunishmentValue_le reward observer
      (quittingAllContinueProfileSpine reward profile (row.start + 1))
    change quittingPunishmentValue reward observer ≤
      quittingContinuationBestResponseValue reward
        (quittingAllContinueProfileSpine reward profile (row.start + 1)) observer
    simpa [quittingBestReplyValue, quittingContinuationBestResponseValue,
      iSup] using h
  have hrow :=
    quittingOwnerQuitProbability_mul_forcedRefusal_add_transport_le_prefixDebt
      reward tail root observer htailDebt hfloor
  have hforced : Function.update root observer (PMF.pure true) = root := by
    rw [← howner]
    exact Function.update_eq_self observer root
  have hprefix : current = quittingTerminalSemanticPrefix reward root tail :=
    quittingTerminalSemanticPair_spine_eq_prefix reward profile row.start
  have hrefusalCurrent : refusal ≤
      quittingTerminalSemanticDebt current observer := by
    dsimp only [refusal]
    rw [hforced] at hrow
    have hquit : (root observer true).toReal = 1 := by rw [howner]; simp
    have hcontinue : quittingStationaryContinueMass root = 0 :=
      quittingStationaryContinueMass_eq_zero_of_owner_eq_pure howner
    rw [hquit, one_mul, hcontinue, zero_mul] at hrow
    simpa [hprefix] using hrow
  have hliveCurrent :=
    quittingLiveMass_mul_spineDebt_le_initialDebt_of_prior_pureContinue
      reward profile observer row.start (by
        intro stage hstage
        dsimp only [profile]
        rw [hchronology.1]
        exact quittingProfileLiveRoot_update_pureTime_some_eq_pureContinue_of_lt
          reward receiving observer hstage)
  have hlive0 : 0 ≤ quittingLiveMass reward profile row.start :=
    quittingLiveMass_nonneg reward profile row.start
  have hrefusalWeighted :
      quittingLiveMass reward profile row.start * refusal ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer := by
    calc
      _ ≤ quittingLiveMass reward profile row.start *
          quittingTerminalSemanticDebt current observer :=
        mul_le_mul_of_nonneg_left hrefusalCurrent hlive0
      _ ≤ _ := by simpa [current] using hliveCurrent
  have hdebt := row.receivingProfile_debt_le happrox
  have hlive : quittingLiveMass reward profile row.start = row.liveMass := by
    dsimp only [profile]
    rw [hchronology.1,
      quittingLiveMass_update_pureTime_some_eq_opponentSurvivalWeight]
    exact row.liveMass_eq.symm
  rw [← hlive]
  exact hrefusalWeighted.trans hdebt

/-- A positive lower bound on the forced-owner outsider defect is attained
by one outsider's pure Boolean endpoint. -/
theorem exists_outsider_pureEndpoint_gain_ge_of_le_forcedOwnerOutsiderDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) {lower : ℝ}
    (hlower : 0 < lower)
    (hdefect : lower ≤ quittingForcedOwnerOutsiderDefect reward root owner) :
    ∃ who, who ≠ owner ∧ ∃ action : Bool,
      quittingRootExpectedPayoff reward 0 root who + lower ≤
        quittingRootExpectedPayoff reward 0
          (Function.update root who (PMF.pure action)) who := by
  letI : Nonempty ι := ⟨owner⟩
  obtain ⟨who, _hwhoMem, hsup⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (quittingForcedOwnerOutsiderCoordinateDefect reward root owner)
  have hcoordinate : lower ≤
      quittingForcedOwnerOutsiderCoordinateDefect reward root owner who := by
    rw [← hsup]
    exact hdefect
  have hwho : who ≠ owner := by
    intro heq
    subst who
    simp [quittingForcedOwnerOutsiderCoordinateDefect] at hcoordinate
    linarith
  let quitValue := quittingStationaryFixedOpponentsQuitValue reward root who
  let continueValue :=
    quittingStationaryFixedOpponentsContinueReward reward root who
  let obeyValue := quittingRootAbsorbingContribution reward root who
  have hrawPos : 0 < max quitValue continueValue - obeyValue := by
    by_contra hnot
    have hnonpos : max quitValue continueValue - obeyValue ≤ 0 :=
      le_of_not_gt hnot
    have hzero :
        quittingForcedOwnerOutsiderCoordinateDefect reward root owner who = 0 := by
      simp [quittingForcedOwnerOutsiderCoordinateDefect, hwho,
        quitValue, continueValue, obeyValue, max_eq_left hnonpos]
    rw [hzero] at hcoordinate
    linarith
  have hgain : obeyValue + lower ≤ max quitValue continueValue := by
    have hraw : lower ≤ max quitValue continueValue - obeyValue := by
      simpa [quittingForcedOwnerOutsiderCoordinateDefect, hwho,
        quitValue, continueValue, obeyValue, max_eq_right hrawPos.le] using
        hcoordinate
    linarith
  have hrootPayoff :
      quittingRootExpectedPayoff reward 0 root who = obeyValue := by rfl
  have hquitPayoff :
      quittingRootExpectedPayoff reward 0
          (Function.update root who (PMF.pure true)) who = quitValue := by rfl
  have hcontinuePayoff :
      quittingRootExpectedPayoff reward 0
          (Function.update root who (PMF.pure false)) who = continueValue := by rfl
  rcases le_total quitValue continueValue with hquitLe | hcontinueLe
  · refine ⟨who, hwho, false, ?_⟩
    rw [hrootPayoff, hcontinuePayoff]
    rwa [max_eq_right hquitLe] at hgain
  · refine ⟨who, hwho, true, ?_⟩
    rw [hrootPayoff, hquitPayoff]
    rwa [max_eq_left hcontinueLe] at hgain

/-- **Earlier-receiving temporal dispatch.**  Let `gain` be the paid
receiving edge and let `gamma` be the terminal exploitability floor.  If the
receiving witness is `eta`-optimal and

`eta < gamma * gain / (2 * quittingRewardBound reward)`,

then one fixed outsider has a legal pure endpoint deviation at the reached
row whose source-unit gain is at least that threshold.  The conclusion also
returns the full behavior deviation obtained by pasting that endpoint at the
reached public history.

This theorem reaches the live atomic outsider leaf.  It does not identify
that leaf with a reset-chord endpoint or otherwise eliminate it. -/
theorem QuittingPaidFirstDisagreementRow.exists_outsiderDeviation_of_receivingEarlier
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {receiving : (quittingGame reward).BehaviorProfile}
    {observer : ι} {gain eta gamma : ℝ}
    (row : QuittingPaidFirstDisagreementRow reward receiving observer gain)
    (hearlier : row.receivingEarlier = true)
    (hgain : 0 < gain) (hgamma : 0 < gamma)
    (hgap : HasTerminalExploitabilityGap reward gamma)
    (happrox :
      quittingContinuationBestResponseValue reward receiving observer - eta ≤
        quittingPureTimeDeviationPayoff reward receiving observer
          row.receivingWitness)
    (hsmall : eta < gamma * gain /
      (2 * quittingRewardBound reward)) :
    let profile := Function.update receiving observer
      (quittingPureTimeBehaviorStrategy reward observer row.receivingWitness)
    ∃ who, who ≠ observer ∧ ∃ action : Bool,
      let deviation := quittingStagePureEndpointBehaviorDeviation
        reward profile who row.start action
      gamma * gain / (2 * quittingRewardBound reward) ≤
          row.liveMass *
            (quittingRootExpectedPayoff reward 0
                (Function.update
                  (quittingProfileLiveRoot reward profile row.start) who
                  (PMF.pure action)) who -
              quittingRootExpectedPayoff reward 0
                (quittingProfileLiveRoot reward profile row.start) who) ∧
        gamma * gain / (2 * quittingRewardBound reward) ≤
          quittingTerminalPayoff reward
              (Function.update profile who deviation) who -
            quittingTerminalPayoff reward profile who := by
  dsimp only
  have hchronology := row.chronology
  rw [hearlier] at hchronology
  simp only [if_true] at hchronology
  let profile := Function.update receiving observer
    (quittingPureTimeBehaviorStrategy reward observer row.receivingWitness)
  let root := quittingProfileLiveRoot reward profile row.start
  let refusal := max 0 (-quittingAtomicBlockerBalance reward root observer)
  let defect := quittingForcedOwnerOutsiderDefect reward root observer
  let bound := quittingRewardBound reward
  have howner : root observer = PMF.pure true := by
    dsimp only [root, profile]
    rw [hchronology.1, quittingProfileLiveRoot_update_pureTime_self,
      quittingPureTimeHazard_some_self]
  have hbound0 : 0 < bound := by
    have hlive0 : 0 ≤ row.liveMass := by
      rw [row.liveMass_eq]
      exact quittingOpponentSurvivalWeight_nonneg _ _ _ _
    dsimp only [bound]
    nlinarith [row.gain_le_liveMass]
  have hbarrier : gamma ≤ max defect refusal := by
    simpa only [defect, refusal] using
      terminalExploitabilityGap_le_atomicBlockerBarrier howner hgamma hgap
  have hrefusalWeighted : row.liveMass * refusal ≤ eta := by
    simpa only [profile, root, refusal] using
      row.liveMass_mul_forcedRefusal_le_eta hearlier happrox
  have hlive0 : 0 ≤ row.liveMass := by
    rw [row.liveMass_eq]
    exact quittingOpponentSurvivalWeight_nonneg _ _ _ _
  have hthresholdLeLive :
      gamma * gain / (2 * bound) ≤ gamma * row.liveMass := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * bound)).2
    nlinarith [row.gain_le_liveMass]
  have hdefect : gamma ≤ defect := by
    by_contra hnot
    have hdefectLt : defect < gamma := lt_of_not_ge hnot
    have hrefusalGe : gamma ≤ refusal := by
      by_contra hrefusalNot
      have hrefusalLt : refusal < gamma := lt_of_not_ge hrefusalNot
      exact (not_lt_of_ge hbarrier) (max_lt hdefectLt hrefusalLt)
    have hweightedGe : gamma * row.liveMass ≤ row.liveMass * refusal := by
      nlinarith
    have hsmallLive : eta < gamma * row.liveMass :=
      hsmall.trans_le hthresholdLeLive
    linarith
  obtain ⟨who, hwho, action, hendpoint⟩ :=
    exists_outsider_pureEndpoint_gain_ge_of_le_forcedOwnerOutsiderDefect
      reward root observer hgamma hdefect
  refine ⟨who, hwho, action, ?_, ?_⟩
  · have hscaled := mul_le_mul_of_nonneg_left hendpoint hlive0
    dsimp only [bound] at hthresholdLeLive ⊢
    linarith
  · let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (row.start + 1))
    have hglobal :=
      quittingTerminalPayoff_stagePureEndpointDeviation_sub_eq_liveMass_mul
        reward profile who row.start action
    have hrootZero : quittingRootSuccessorPayoff reward tail.1 root who =
        quittingRootExpectedPayoff reward 0 root who := by
      unfold quittingRootSuccessorPayoff
      rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
        quittingRootExpectedPayoff_eq_absorbingContribution_add]
      rw [quittingStationaryContinueMass_eq_zero_of_owner_eq_pure howner]
      simp
    have hownerUpdated :
        Function.update root who (PMF.pure action) observer = PMF.pure true := by
      rw [Function.update_of_ne (Ne.symm hwho)]
      exact howner
    have hupdatedZero :
        quittingRootSuccessorPayoff reward tail.1
            (Function.update root who (PMF.pure action)) who =
          quittingRootExpectedPayoff reward 0
            (Function.update root who (PMF.pure action)) who := by
      unfold quittingRootSuccessorPayoff
      rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
        quittingRootExpectedPayoff_eq_absorbingContribution_add]
      rw [quittingStationaryContinueMass_eq_zero_of_owner_eq_pure hownerUpdated]
      simp
    have hscaled := mul_le_mul_of_nonneg_left hendpoint hlive0
    have hlive : quittingLiveMass reward profile row.start = row.liveMass := by
      dsimp only [profile]
      rw [hchronology.1,
        quittingLiveMass_update_pureTime_some_eq_opponentSurvivalWeight]
      exact row.liveMass_eq.symm
    dsimp only [bound] at hthresholdLeLive ⊢
    dsimp only at hglobal
    rw [hrootZero, hupdatedZero] at hglobal
    rw [hlive] at hglobal
    linarith

end GameTheory
