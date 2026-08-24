/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseConcreteGap
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.StrictToggleLargeBasePaidChain
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreement
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness

/-!
# Stationary semantic handoff from a reselected singleton base

The large-base deletion route reselects one persistent label as a singleton
sure quitter and lets every other player enter the induced binary game.  A
positive singleton owner-floor excess then has a direct semantic meaning:
the sure owner has positive unrestricted best-response debt.  Replacing that
owner by Always Continue attains its cap and transfers the terminal gap to a
different player.  The latter debt is decoded into a literal paid
first-disagreement row between immediate Quit and Never.

The statements below are semantic adapters.  They do not assert that the
reselected stationary profile is reached from the earlier large-base face,
or that the repair is a Nash--Bellman edge.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The stationary profile obtained by extending an induced singleton-base
mixed point to the quitting game. -/
def quittingSingletonBaseStationaryProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) :
    (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward
    (quittingPersistentBaseRoot {owner} free point)

/-- The repaired row removes the singleton owner's sure Quit action. -/
def quittingSingletonBaseRepairedRoot
    (owner : ι) (free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) : ι → PMF Bool :=
  Function.update (quittingPersistentBaseRoot {owner} free point) owner
    (PMF.pure false)

/-- The stationary profile after the singleton owner is repaired by Always
Continue. -/
def quittingSingletonBaseRepairedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) :
    (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward
    (quittingSingletonBaseRepairedRoot owner free point)

/-- The named repaired profile is literally the unilateral Always-Continue
replacement of the singleton owner. -/
theorem update_quittingSingletonBaseStationaryProfile_owner_alwaysContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) :
    Function.update
        (quittingSingletonBaseStationaryProfile reward owner free point)
        owner (quittingAlwaysContinueStrategy reward owner) =
      quittingSingletonBaseRepairedProfile reward owner free point := by
  exact update_quittingStationaryProfile_alwaysContinue reward
    (quittingPersistentBaseRoot {owner} free point) owner

private theorem stationary_prescribed_between_quitNow_and_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    let profile := quittingStationaryProfile reward root
    let prescribed := quittingTerminalPayoff reward profile who
    let quitNow := quittingPureTimeDeviationPayoff reward profile who (some 0)
    let never := quittingPureTimeDeviationPayoff reward profile who none
    (quitNow ≤ never → quitNow ≤ prescribed ∧ prescribed ≤ never) ∧
      (never ≤ quitNow → never ≤ prescribed ∧ prescribed ≤ quitNow) := by
  dsimp only
  let profile := quittingStationaryProfile reward root
  let prescribed := quittingTerminalPayoff reward profile who
  let quitNow := quittingPureTimeDeviationPayoff reward profile who (some 0)
  let never := quittingPureTimeDeviationPayoff reward profile who none
  let opponentMass := quittingStationaryFixedOpponentsContinueMass root who
  let continueReward :=
    quittingStationaryFixedOpponentsContinueReward reward root who
  let absorptionMass := quittingRootAbsorptionMass root
  let quitProbability := (root who true).toReal
  change (quitNow ≤ never → quitNow ≤ prescribed ∧ prescribed ≤ never) ∧
    (never ≤ quitNow → never ≤ prescribed ∧ prescribed ≤ quitNow)
  have hopponentMass0 : 0 ≤ opponentMass :=
    quittingStationaryFixedOpponentsContinueMass_nonneg root who
  have hopponentMass1 : opponentMass ≤ 1 :=
    quittingStationaryFixedOpponentsContinueMass_le_one root who
  have hquitProbability0 : 0 ≤ quitProbability := ENNReal.toReal_nonneg
  have hquitProbability1 : quitProbability ≤ 1 := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    dsimp only [quitProbability]
    have hcontinue0 : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
    linarith
  have hquitNow : quitNow =
      quittingStationaryFixedOpponentsQuitValue reward root who := by
    dsimp only [quitNow, quittingPureTimeDeviationPayoff, profile]
    rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
    simp
  by_cases hopponent : opponentMass < 1
  · have habsorptionIdentity : absorptionMass =
        1 - (1 - quitProbability) * opponentMass := by
      dsimp only [absorptionMass, quitProbability, opponentMass]
      rw [quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul]
      have hsum := quittingRoot_continueProbability_add_quitProbability root who
      congr 2
      linarith
    have habsorptionPos : 0 < absorptionMass := by
      rw [habsorptionIdentity]
      have hproduct :
          (1 - quitProbability) * opponentMass < 1 := by
        calc
          (1 - quitProbability) * opponentMass ≤ 1 * opponentMass :=
            mul_le_mul_of_nonneg_right (by linarith) hopponentMass0
          _ < 1 := by simpa using hopponent
      linarith
    have hnever : never =
        quittingStationaryNeverValue continueReward opponentMass := by
      dsimp only [never, quittingPureTimeDeviationPayoff, profile,
        continueReward, opponentMass]
      rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
        quittingProfileLiveRoot_stationary,
        quittingRootSequencePureTimeTerminalValue_const_none]
      exact hopponent
    have hbalance := quittingRootAbsorptionMass_mul_stationaryTerminalValue
      reward root who
    have habsorptionIdentity' :=
      quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul root who
    have hneverBalance := quittingStationaryNeverValue_balance
      continueReward opponentMass hopponent
    have hcontinueProbability : (root who false).toReal =
        1 - quitProbability := by
      have hsum := quittingRoot_continueProbability_add_quitProbability root who
      dsimp only [quitProbability]
      linarith
    rw [hcontinueProbability] at hbalance habsorptionIdentity'
    change absorptionMass * prescribed =
      quitProbability * quittingStationaryFixedOpponentsQuitValue reward root who +
        (1 - quitProbability) * continueReward at hbalance
    change absorptionMass =
      1 - (1 - quitProbability) * opponentMass at habsorptionIdentity'
    rw [← hquitNow] at hbalance
    rw [← hnever] at hneverBalance
    have hlowerIdentity : absorptionMass * (prescribed - quitNow) =
        (1 - quitProbability) * (1 - opponentMass) * (never - quitNow) := by
      linear_combination hbalance - quitNow * habsorptionIdentity' +
        (1 - quitProbability) * hneverBalance
    have hupperIdentity : absorptionMass * (never - prescribed) =
        quitProbability * (never - quitNow) := by
      linear_combination never * habsorptionIdentity' - hbalance -
        (1 - quitProbability) * hneverBalance
    constructor
    · intro horder
      have hlower0 : 0 ≤ absorptionMass * (prescribed - quitNow) := by
        rw [hlowerIdentity]
        positivity
      have hupper0 : 0 ≤ absorptionMass * (never - prescribed) := by
        rw [hupperIdentity]
        positivity
      constructor
      · exact sub_nonneg.mp
          (nonneg_of_mul_nonneg_right hlower0 habsorptionPos)
      · exact sub_nonneg.mp
          (nonneg_of_mul_nonneg_right hupper0 habsorptionPos)
    · intro horder
      have hlower0 : 0 ≤ absorptionMass * (prescribed - never) := by
        rw [show absorptionMass * (prescribed - never) =
            -(absorptionMass * (never - prescribed)) by ring,
          hupperIdentity]
        exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
          hquitProbability0 (sub_nonpos.mpr horder))
      have hupper0 : 0 ≤ absorptionMass * (quitNow - prescribed) := by
        rw [show absorptionMass * (quitNow - prescribed) =
            -(absorptionMass * (prescribed - quitNow)) by ring,
          hlowerIdentity]
        exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (by linarith : 0 ≤ 1 - quitProbability)
            (by linarith : 0 ≤ 1 - opponentMass))
          (sub_nonpos.mpr horder))
      constructor
      · exact sub_nonneg.mp
          (nonneg_of_mul_nonneg_right hlower0 habsorptionPos)
      · exact sub_nonneg.mp
          (nonneg_of_mul_nonneg_right hupper0 habsorptionPos)
  · have hopponentEq : opponentMass = 1 := le_antisymm hopponentMass1
        (not_lt.mp hopponent)
    have hcontinueReward : continueReward = 0 := by
      exact quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
        reward hopponentEq
    have hnever : never = 0 := by
      dsimp only [never, quittingPureTimeDeviationPayoff, profile]
      rw [quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
        update_quittingStationaryProfile_alwaysContinue]
      have hall := eq_pureSetRoot_empty_of_fixedOpponentsContinueMass_eq_one
        (root := root) (who := who) hopponentEq
      have hallUpdated : Function.update root who (PMF.pure false) =
          fun _ : ι => PMF.pure false := by
        funext player
        by_cases hplayer : player = who
        · subst player
          simp
        · rw [Function.update_of_ne hplayer, hall player hplayer]
          rfl
      rw [hallUpdated]
      exact quittingTerminalPayoff_quittingAlwaysContinue reward who
    by_cases hquitProbability : quitProbability = 0
    · have hwho : root who = PMF.pure false :=
        Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
          (root who) hquitProbability
      have hall : root = fun _ : ι => PMF.pure false := by
        have hopponents :=
          eq_pureSetRoot_empty_of_fixedOpponentsContinueMass_eq_one
            (root := root) (who := who) hopponentEq
        funext player
        by_cases hplayer : player = who
        · subst player
          exact hwho
        · exact hopponents player hplayer
      have hprescribed : prescribed = 0 := by
        dsimp only [prescribed, profile]
        rw [hall]
        exact quittingTerminalPayoff_quittingAlwaysContinue reward who
      rw [hnever, hprescribed]
      constructor <;> intro horder <;> constructor <;> linarith
    · have hquitProbabilityPos : 0 < quitProbability :=
        lt_of_le_of_ne hquitProbability0 (Ne.symm hquitProbability)
      have hbalance := quittingRootAbsorptionMass_mul_stationaryTerminalValue
        reward root who
      have habsorptionIdentity :=
        quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul root who
      have hcontinueProbability : (root who false).toReal =
          1 - quitProbability := by
        have hsum := quittingRoot_continueProbability_add_quitProbability root who
        dsimp only [quitProbability]
        linarith
      rw [hcontinueProbability] at hbalance habsorptionIdentity
      change quittingRootAbsorptionMass root * prescribed =
        quitProbability * quittingStationaryFixedOpponentsQuitValue reward root who +
          (1 - quitProbability) * continueReward at hbalance
      change quittingRootAbsorptionMass root =
        1 - (1 - quitProbability) * opponentMass at habsorptionIdentity
      rw [hcontinueReward, ← hquitNow] at hbalance
      rw [hopponentEq] at habsorptionIdentity
      rw [habsorptionIdentity] at hbalance
      norm_num at hbalance
      have hprescribed : prescribed = quitNow := by
        rcases hbalance with hbalance | hzero
        · exact hbalance
        · exact (ne_of_gt hquitProbabilityPos hzero).elim
      rw [hnever, hprescribed]
      constructor <;> intro horder <;> constructor <;> linarith

/-- At every stationary row, including the degenerate all-opponents-Continue
boundary, the unrestricted behavioral cap is the larger of immediate Quit
and Never. -/
theorem quittingStationaryUnilateralCap_eq_max_quitNow_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryUnilateralCap reward root who =
      max
        (quittingPureTimeDeviationPayoff reward
          (quittingStationaryProfile reward root) who (some 0))
        (quittingPureTimeDeviationPayoff reward
          (quittingStationaryProfile reward root) who none) := by
  rw [quittingStationaryUnilateralCap_eq_max_div]
  have hquitNow : quittingPureTimeDeviationPayoff reward
        (quittingStationaryProfile reward root) who (some 0) =
      quittingStationaryFixedOpponentsQuitValue reward root who := by
    dsimp only [quittingPureTimeDeviationPayoff]
    rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
    simp
  by_cases hopponent :
      quittingStationaryFixedOpponentsContinueMass root who < 1
  · have hnever : quittingPureTimeDeviationPayoff reward
        (quittingStationaryProfile reward root) who none =
      quittingStationaryFixedOpponentsContinueReward reward root who /
        (1 - quittingStationaryFixedOpponentsContinueMass root who) := by
      dsimp only [quittingPureTimeDeviationPayoff]
      rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
        quittingProfileLiveRoot_stationary,
        quittingRootSequencePureTimeTerminalValue_const_none reward root who
          hopponent]
      rfl
    rw [hquitNow, hnever]
  · have hmass : quittingStationaryFixedOpponentsContinueMass root who = 1 :=
      le_antisymm
        (quittingStationaryFixedOpponentsContinueMass_le_one root who)
        (not_lt.mp hopponent)
    have hnever : quittingPureTimeDeviationPayoff reward
        (quittingStationaryProfile reward root) who none = 0 := by
      dsimp only [quittingPureTimeDeviationPayoff]
      rw [quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
        update_quittingStationaryProfile_alwaysContinue]
      have hall := eq_pureSetRoot_empty_of_fixedOpponentsContinueMass_eq_one
        (root := root) (who := who) hmass
      have hallUpdated : Function.update root who (PMF.pure false) =
          fun _ : ι => PMF.pure false := by
        funext player
        by_cases hplayer : player = who
        · subst player
          simp
        · rw [Function.update_of_ne hplayer, hall player hplayer]
          rfl
      rw [hallUpdated]
      exact quittingTerminalPayoff_quittingAlwaysContinue reward who
    rw [hquitNow, hnever, hmass]
    simp

/-- A positive stationary cap debt is witnessed by an oriented difference
between immediate Quit and Never, including the all-opponents-Continue
boundary. -/
theorem exists_oriented_quitNow_never_gap_of_stationary_cap_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {gap : ℝ}
    (hgap : gap ≤ quittingStationaryUnilateralCap reward root who -
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who) :
    gap ≤ quittingPureTimeDeviationPayoff reward
          (quittingStationaryProfile reward root) who (some 0) -
        quittingPureTimeDeviationPayoff reward
          (quittingStationaryProfile reward root) who none ∨
      gap ≤ quittingPureTimeDeviationPayoff reward
          (quittingStationaryProfile reward root) who none -
        quittingPureTimeDeviationPayoff reward
          (quittingStationaryProfile reward root) who (some 0) := by
  let profile := quittingStationaryProfile reward root
  let prescribed := quittingTerminalPayoff reward profile who
  let quitNow := quittingPureTimeDeviationPayoff reward profile who (some 0)
  let never := quittingPureTimeDeviationPayoff reward profile who none
  have hbetween := stationary_prescribed_between_quitNow_and_never
    reward root who
  have hcap : quittingStationaryUnilateralCap reward root who =
      max quitNow never :=
    quittingStationaryUnilateralCap_eq_max_quitNow_never reward root who
  by_cases horder : quitNow ≤ never
  · right
    have hsegment := hbetween.1 horder
    rw [hcap, max_eq_right horder] at hgap
    dsimp only [profile, prescribed, quitNow, never] at hgap hsegment ⊢
    linarith
  · left
    have horder' : never ≤ quitNow := le_of_not_ge horder
    have hsegment := hbetween.2 horder'
    rw [hcap, max_eq_left horder'] at hgap
    dsimp only [profile, prescribed, quitNow, never] at hgap hsegment ⊢
    linarith

/-- **One-debtor stationary source.**  At an induced Nash point on a
singleton-base face, every free coordinate realizes its unrestricted
behavioral cap and lies above punishment.  A positive owner-floor excess is
bounded by the sure owner's actual behavioral debt. -/
theorem singletonBase_inducedNash_floorExcess_semantics
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι) (howner : owner ∉ free)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet reward {owner} free)
    {delta : ℝ}
    (hdelta : delta ≤ quittingSingletonBaseOwnerFloorExcess reward owner
      (quittingPersistentBaseRoot {owner} free point)) :
    (∀ who ∈ free,
      quittingTerminalPayoff reward
          (quittingSingletonBaseStationaryProfile reward owner free point) who =
        quittingStationaryUnilateralCap reward
          (quittingPersistentBaseRoot {owner} free point) who ∧
      quittingPunishmentValue reward who ≤
        quittingTerminalPayoff reward
          (quittingSingletonBaseStationaryProfile reward owner free point) who) ∧
    quittingPunishmentValue reward owner ≤
        quittingStationaryUnilateralCap reward
          (quittingPersistentBaseRoot {owner} free point) owner ∧
      delta ≤ quittingStationaryUnilateralCap reward
          (quittingPersistentBaseRoot {owner} free point) owner -
        quittingTerminalPayoff reward
          (quittingSingletonBaseStationaryProfile reward owner free point) owner := by
  let root := quittingPersistentBaseRoot {owner} free point
  let profile := quittingSingletonBaseStationaryProfile reward owner free point
  have hownerRoot : root owner = PMF.pure true := by
    exact quittingPersistentBaseRoot_apply_of_mem_base
      {owner} free point (by simp)
  have hcontinueMass : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hownerRoot
  have hprofile : profile = quittingStationaryProfile reward root := rfl
  constructor
  · intro who hwho
    have hne : who ≠ owner := by
      intro heq
      subst who
      exact howner hwho
    have hopponentMass :
        quittingStationaryFixedOpponentsContinueMass root who = 0 :=
      quittingStationaryContinueMass_update_of_sureQuitter
        hne hownerRoot (PMF.pure false)
    have hpure := quittingPersistentBaseRoot_free_purePayoff_le
      reward {owner} free (by simp)
        (Finset.disjoint_singleton_left.mpr howner) point hpoint who hwho
    have htarget : quittingTerminalPayoff reward profile who =
        quittingRootAbsorbingContribution reward root who := by
      rw [hprofile,
        quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
      · rw [hcontinueMass]
        norm_num
      · rw [hcontinueMass]
        norm_num
    have hsuccessor : quittingRootSuccessorPayoff reward 0 root who =
        quittingRootAbsorbingContribution reward root who := by
      unfold quittingRootSuccessorPayoff
      rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
        hcontinueMass]
      simp
    have hquit : quittingStationaryFixedOpponentsQuitValue reward root who ≤
        quittingTerminalPayoff reward profile who := by
      have hquitEq : quittingRootQuitPayoff reward 0 root who =
          quittingStationaryFixedOpponentsQuitValue reward root who := by
        simpa [quittingStationaryFixedOpponentsQuitValue] using
          (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
            reward (fun _ => root) who 0 0)
      calc
        quittingStationaryFixedOpponentsQuitValue reward root who =
            quittingRootQuitPayoff reward 0 root who := hquitEq.symm
        _ ≤ quittingRootSuccessorPayoff reward 0 root who := hpure.1
        _ = quittingRootAbsorbingContribution reward root who := hsuccessor
        _ = quittingTerminalPayoff reward profile who := htarget.symm
    have hcontinue :
        quittingStationaryFixedOpponentsContinueReward reward root who ≤
          quittingTerminalPayoff reward profile who := by
      have hcontinueEq : quittingRootContinuePayoff reward 0 root who =
          quittingStationaryFixedOpponentsContinueReward reward root who := by
        have hraw := quittingRootContinuePayoff_eq_fixedOpponents
          reward (fun _ => root) who 0 0
        simpa [quittingStationaryFixedOpponentsContinueReward] using hraw
      calc
        quittingStationaryFixedOpponentsContinueReward reward root who =
            quittingRootContinuePayoff reward 0 root who := hcontinueEq.symm
        _ ≤ quittingRootSuccessorPayoff reward 0 root who := hpure.2
        _ = quittingRootAbsorbingContribution reward root who := hsuccessor
        _ = quittingTerminalPayoff reward profile who := htarget.symm
    have hcapUpper : quittingStationaryUnilateralCap reward root who ≤
        quittingTerminalPayoff reward profile who := by
      rw [quittingStationaryUnilateralCap_eq_max_div, hopponentMass]
      norm_num
      exact ⟨hquit, hcontinue⟩
    have hpayoffLower : quittingTerminalPayoff reward profile who ≤
        quittingStationaryUnilateralCap reward root who := by
      rw [← quittingBestReplyValue_stationary]
      have hself := le_quittingBestReplyValue reward profile who (profile who)
      rw [← hprofile]
      simpa only [Function.update_eq_self] using hself
    have heq := le_antisymm hpayoffLower hcapUpper
    refine ⟨heq, ?_⟩
    rw [heq]
    exact quittingPunishmentValue_le_stationaryUnilateralCap reward who root
  · have hpunishment :=
      quittingPunishmentValue_le_stationaryUnilateralCap reward owner root
    refine ⟨hpunishment, hdelta.trans ?_⟩
    have htarget : quittingTerminalPayoff reward profile owner =
        quittingRootAbsorbingContribution reward root owner := by
      rw [hprofile,
        quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
      · rw [hcontinueMass]
        norm_num
      · rw [hcontinueMass]
        norm_num
    have hfloor : quittingSingletonBaseOwnerFloorExcess reward owner root =
        quittingStationaryFixedOpponentsContinueReward reward root owner +
          quittingStationaryFixedOpponentsContinueMass root owner *
            quittingPunishmentValue reward owner -
          quittingTerminalPayoff reward profile owner := by
      unfold quittingSingletonBaseOwnerFloorExcess
      have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents
        reward (fun _ => root) owner
          (fun _ => quittingPunishmentValue reward owner) 0
      have hrootTarget := quittingRootExpectedPayoff_eq_absorbingContribution_add
        reward 0 root owner
      rw [hcontinue, hrootTarget, hcontinueMass, htarget]
      simp [quittingStationaryFixedOpponentsContinueReward,
        quittingStationaryFixedOpponentsContinueMass,
        quittingFixedOpponentsContinueReward,
        quittingFixedOpponentsContinueMass]
    rw [hfloor]
    let mass := quittingStationaryFixedOpponentsContinueMass root owner
    let absorb := quittingStationaryFixedOpponentsContinueReward reward root owner
    let cap := quittingStationaryUnilateralCap reward root owner
    have hmass0 : 0 ≤ mass :=
      quittingStationaryFixedOpponentsContinueMass_nonneg root owner
    have hmass1 : mass ≤ 1 :=
      quittingStationaryFixedOpponentsContinueMass_le_one root owner
    by_cases hcontracts : mass < 1
    · have hbellman := quittingStationaryUnilateralCap_bellman
        reward root owner hcontracts
      have hcontinueCap : absorb + mass * cap ≤ cap := by
        dsimp only [absorb, mass, cap]
        calc
          _ ≤ max (quittingStationaryFixedOpponentsQuitValue reward root owner)
              (quittingStationaryFixedOpponentsContinueReward reward root owner +
                quittingStationaryFixedOpponentsContinueMass root owner *
                  quittingStationaryUnilateralCap reward root owner) :=
            le_max_right _ _
          _ = quittingStationaryUnilateralCap reward root owner := hbellman.symm
      have hscaled := mul_le_mul_of_nonneg_left hpunishment hmass0
      dsimp only [absorb, mass, cap] at hcontinueCap hscaled
      linarith
    · have hmassEq : mass = 1 := le_antisymm hmass1 (not_lt.mp hcontracts)
      have habsorb : absorb = 0 := by
        exact quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
          reward hmassEq
      dsimp only [absorb, mass, cap] at habsorb hmassEq ⊢
      rw [habsorb, hmassEq]
      linarith

/-- When the free set is the full complement of a singleton owner, the
terminal witness forces a uniformly positive owner-floor excess on the whole
compact induced Nash carrier.  This is the compact re-selection step; it
does not choose or connect a path through that carrier. -/
theorem QuittingTerminalExploitabilityWitness.exists_pos_ownerFloorExcess_gap
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (owner : ι) (free : Finset ι)
    (hfree : free = Finset.univ.erase owner) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ point ∈ quittingPersistentBaseNashSet reward {owner} free,
        delta ≤ quittingSingletonBaseOwnerFloorExcess reward owner
          (quittingPersistentBaseRoot {owner} free point) := by
  rcases exists_persistentBaseNash_nonpos_or_pos_gap reward {owner} free
      (fun point => quittingSingletonBaseOwnerFloorExcess reward owner
        (quittingPersistentBaseRoot {owner} free point))
      (continuous_quittingSingletonBaseOwnerFloorExcess reward owner free) with
    haccepted | hgap
  · obtain ⟨point, hpoint, hfloor⟩ := haccepted
    have howner : owner ∉ free := by
      rw [hfree]
      simp
    have hjoin : ∀ who ∉ ({owner} : Finset ι) ∪ free,
        quittingRootEndpointDifference reward 0
          (quittingPersistentBaseRoot {owner} free point) who ≤ 0 := by
      intro who houtside
      exfalso
      apply houtside
      rw [hfree]
      simp
    obtain ⟨certificate⟩ :=
      nonempty_quittingSingletonBaseCertificate_of_inducedNash
        reward owner free howner point hpoint hfloor hjoin
    exact (witness.not_exists_uniformEquilibriumPayoff
      ⟨quittingRootAbsorbingContribution reward
        (quittingPersistentBaseRoot {owner} free point),
        certificate.isUniformEquilibriumPayoff⟩).elim
  · exact hgap

/-- Both arms of the support-two paid-chain residual retain an ordered paid
base label and the other base label as owner. -/
theorem HasSupportTwoNormalPaidChainResidual.exists_paid_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseFirst baseSecond first second : ι) (gamma : ℝ)
    (residual : HasSupportTwoNormalPaidChainResidual reward
      baseFirst baseSecond first second gamma) :
    ∃ paid owner,
      (paid = baseFirst ∧ owner = baseSecond) ∨
        (paid = baseSecond ∧ owner = baseFirst) := by
  rcases residual with hpure | hmixed
  · obtain ⟨paid, owner, -, -, hpair, -⟩ := hpure
    exact ⟨paid, owner, hpair⟩
  · dsimp [HasActualPaidMixedNormalFiniteResidual] at hmixed
    obtain ⟨paid, owner, hpair, -⟩ := hmixed
    exact ⟨paid, owner, hpair⟩

/-- Data retained by the complete singleton-owner repair handoff.  The
`outsideDebtor` is selected by the unrestricted terminal exploitability gap,
not by a stationary-only verifier. -/
structure QuittingSingletonBaseStationaryHandoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (delta terminalGap : ℝ) where
  outsideDebtor : ι
  outsideDebtor_mem_free : outsideDebtor ∈ free
  outsideDebtor_ne_owner : outsideDebtor ≠ owner
  source_free_semantics : ∀ who ∈ free,
    quittingTerminalPayoff reward
          (quittingSingletonBaseStationaryProfile reward owner free point) who =
        quittingStationaryUnilateralCap reward
          (quittingPersistentBaseRoot {owner} free point) who ∧
      quittingPunishmentValue reward who ≤
        quittingTerminalPayoff reward
          (quittingSingletonBaseStationaryProfile reward owner free point) who
  source_owner_floor_cap : quittingPunishmentValue reward owner ≤
    quittingStationaryUnilateralCap reward
      (quittingPersistentBaseRoot {owner} free point) owner
  source_owner_debt : delta ≤
    quittingStationaryUnilateralCap reward
        (quittingPersistentBaseRoot {owner} free point) owner -
      quittingTerminalPayoff reward
        (quittingSingletonBaseStationaryProfile reward owner free point) owner
  repaired_owner_payoff_eq_source_cap :
    quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point) owner =
      quittingStationaryUnilateralCap reward
        (quittingPersistentBaseRoot {owner} free point) owner
  repaired_owner_cap_eq_payoff :
    quittingStationaryUnilateralCap reward
        (quittingSingletonBaseRepairedRoot owner free point) owner =
      quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point) owner
  repaired_owner_gain : delta ≤
    quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point) owner -
      quittingTerminalPayoff reward
        (quittingSingletonBaseStationaryProfile reward owner free point) owner
  repaired_owner_floor : quittingPunishmentValue reward owner ≤
    quittingTerminalPayoff reward
      (quittingSingletonBaseRepairedProfile reward owner free point) owner
  outside_debt : terminalGap ≤
    quittingStationaryUnilateralCap reward
        (quittingSingletonBaseRepairedRoot owner free point) outsideDebtor -
      quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point)
          outsideDebtor
  floor_dispatch :
    (∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point) who) ∨
    ∃ who ∈ free,
      quittingTerminalPayoff reward
          (quittingSingletonBaseRepairedProfile reward owner free point) who <
        quittingPunishmentValue reward who
  paid_row : Nonempty (QuittingPaidFirstDisagreementRow reward
    (quittingSingletonBaseRepairedProfile reward owner free point)
    outsideDebtor terminalGap)

/-- **Owner repair and paid-row transfer.**  Suppose the induced free set is
the full complement of the singleton owner.  A positive lower bound on the
owner-floor excess makes the owner the unique debtor of the sure-Quit source.
Always Continue attains that owner's cap.  The terminal exploitability gap
then selects a distinct free debtor and compiles its debt to a literal paid
first-disagreement row between immediate Quit and Never.

The repaired profile is an actual unilateral strategy replacement and keeps
the same fixed stationary payoff throughout the statement.  No claim is made
that it is a Nash--Bellman edge or is reached from the earlier large-base
face. -/
theorem exists_singletonBaseStationaryHandoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (free : Finset ι)
    (hfree : free = Finset.univ.erase owner)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet reward {owner} free)
    (witness : QuittingTerminalExploitabilityWitness reward)
    {delta : ℝ} (hdeltaPos : 0 < delta)
    (hdelta : delta ≤ quittingSingletonBaseOwnerFloorExcess reward owner
      (quittingPersistentBaseRoot {owner} free point)) :
    Nonempty (QuittingSingletonBaseStationaryHandoff reward owner free point
      delta witness.terminalGap) := by
  let root := quittingPersistentBaseRoot {owner} free point
  let source := quittingSingletonBaseStationaryProfile reward owner free point
  let repairedRoot := quittingSingletonBaseRepairedRoot owner free point
  let repaired := quittingSingletonBaseRepairedProfile reward owner free point
  have howner : owner ∉ free := by
    rw [hfree]
    simp
  obtain ⟨hfreeSemantics, hownerFloorCap, hownerDebt⟩ :=
    singletonBase_inducedNash_floorExcess_semantics
      reward owner free howner point hpoint hdelta
  have hownerRoot : root owner = PMF.pure true := by
    exact quittingPersistentBaseRoot_apply_of_mem_base
      {owner} free point (by simp)
  have hsource : source = quittingStationaryProfile reward root := rfl
  have hrepaired : repaired =
      quittingStationaryProfile reward repairedRoot := rfl
  have hsourceTarget : quittingTerminalPayoff reward source owner =
      quittingRootAbsorbingContribution reward root owner := by
    have hcontinueMass : quittingStationaryContinueMass root = 0 :=
      quittingStationaryContinueMass_of_sureQuitter hownerRoot
    rw [hsource,
      quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
    · rw [hcontinueMass]
      norm_num
    · rw [hcontinueMass]
      norm_num
  have hsourceImmediate :
      quittingPureTimeDeviationPayoff reward source owner (some 0) =
        quittingTerminalPayoff reward source owner := by
    have hquit : quittingPureTimeDeviationPayoff reward source owner (some 0) =
        quittingStationaryFixedOpponentsQuitValue reward root owner := by
      rw [hsource]
      dsimp only [quittingPureTimeDeviationPayoff]
      rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
      simp
    have hquitTarget :
        quittingStationaryFixedOpponentsQuitValue reward root owner =
          quittingRootAbsorbingContribution reward root owner := by
      change quittingRootAbsorbingContribution reward
          (Function.update root owner (PMF.pure true)) owner = _
      rw [← hownerRoot, Function.update_eq_self]
    rw [hquit, hquitTarget, hsourceTarget]
  have hrepairedNever :
      quittingPureTimeDeviationPayoff reward source owner none =
        quittingTerminalPayoff reward repaired owner := by
    dsimp only [quittingPureTimeDeviationPayoff]
    rw [quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
      update_quittingSingletonBaseStationaryProfile_owner_alwaysContinue]
  have hsourceCapMax :
      quittingStationaryUnilateralCap reward root owner =
        max
          (quittingPureTimeDeviationPayoff reward source owner (some 0))
          (quittingPureTimeDeviationPayoff reward source owner none) := by
    rw [hsource]
    exact quittingStationaryUnilateralCap_eq_max_quitNow_never
      reward root owner
  have hsourceStrict : quittingTerminalPayoff reward source owner <
      quittingStationaryUnilateralCap reward root owner := by
    linarith
  have himmediateNever :
      quittingPureTimeDeviationPayoff reward source owner (some 0) ≤
        quittingPureTimeDeviationPayoff reward source owner none := by
    by_contra hnot
    have hreverse : quittingPureTimeDeviationPayoff reward source owner none ≤
        quittingPureTimeDeviationPayoff reward source owner (some 0) :=
      le_of_not_ge hnot
    have hcapImmediate := max_eq_left hreverse
    rw [hsourceCapMax, hcapImmediate, hsourceImmediate] at hsourceStrict
    exact (lt_irrefl _ hsourceStrict)
  have hrepairedOwner : quittingTerminalPayoff reward repaired owner =
      quittingStationaryUnilateralCap reward root owner := by
    calc
      quittingTerminalPayoff reward repaired owner =
          quittingPureTimeDeviationPayoff reward source owner none :=
        hrepairedNever.symm
      _ = max (quittingPureTimeDeviationPayoff reward source owner (some 0))
          (quittingPureTimeDeviationPayoff reward source owner none) :=
        (max_eq_right himmediateNever).symm
      _ = quittingStationaryUnilateralCap reward root owner :=
        hsourceCapMax.symm
  have hcaps : quittingStationaryUnilateralCap reward repairedRoot owner =
      quittingStationaryUnilateralCap reward root owner := by
    symm
    apply quittingStationaryUnilateralCap_congr_of_opponents reward owner
    intro player hplayer
    dsimp only [repairedRoot, quittingSingletonBaseRepairedRoot]
    rw [Function.update_of_ne hplayer]
  have hrepairedOwnerCap :
      quittingStationaryUnilateralCap reward repairedRoot owner =
        quittingTerminalPayoff reward repaired owner := by
    rw [hcaps, hrepairedOwner]
  have hrepairedGain : delta ≤
      quittingTerminalPayoff reward repaired owner -
        quittingTerminalPayoff reward source owner := by
    rw [hrepairedOwner]
    exact hownerDebt
  have hrepairedFloor : quittingPunishmentValue reward owner ≤
      quittingTerminalPayoff reward repaired owner := by
    rw [hrepairedOwner]
    exact hownerFloorCap
  obtain ⟨outsideDebtor, deviation, hexploit⟩ :=
    witness.terminalExploitability repaired
  have hdeviationCap := quittingTerminalPayoff_update_stationary_le_cap
    reward repairedRoot outsideDebtor deviation
  rw [← hrepaired] at hdeviationCap
  have houtsideDebt : witness.terminalGap ≤
      quittingStationaryUnilateralCap reward repairedRoot outsideDebtor -
        quittingTerminalPayoff reward repaired outsideDebtor := by
    linarith
  have houtsideNe : outsideDebtor ≠ owner := by
    intro heq
    subst outsideDebtor
    rw [hrepairedOwnerCap] at houtsideDebt
    linarith [witness.terminalGap_pos]
  have houtsideMem : outsideDebtor ∈ free := by
    rw [hfree]
    simp [houtsideNe]
  have hpaid : Nonempty (QuittingPaidFirstDisagreementRow reward repaired
      outsideDebtor witness.terminalGap) := by
    rcases exists_oriented_quitNow_never_gap_of_stationary_cap_debt
      reward repairedRoot outsideDebtor houtsideDebt with hquit | hnever
    · obtain ⟨row, -, -⟩ :=
        exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
          reward repaired outsideDebtor none (some 0) witness.terminalGap
            witness.terminalGap_pos hquit
      exact ⟨row⟩
    · obtain ⟨row, -, -⟩ :=
        exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
          reward repaired outsideDebtor (some 0) none witness.terminalGap
            witness.terminalGap_pos hnever
      exact ⟨row⟩
  have hfloorDispatch :
      (∀ who, quittingPunishmentValue reward who ≤
        quittingTerminalPayoff reward repaired who) ∨
      ∃ who ∈ free,
        quittingTerminalPayoff reward repaired who <
          quittingPunishmentValue reward who := by
    classical
    by_cases hall : ∀ who, quittingPunishmentValue reward who ≤
        quittingTerminalPayoff reward repaired who
    · exact Or.inl hall
    · right
      push Not at hall
      obtain ⟨who, hwho⟩ := hall
      have hne : who ≠ owner := by
        intro heq
        subst who
        exact (not_lt_of_ge hrepairedFloor hwho)
      refine ⟨who, ?_, hwho⟩
      rw [hfree]
      simp [hne]
  exact ⟨{
    outsideDebtor := outsideDebtor
    outsideDebtor_mem_free := houtsideMem
    outsideDebtor_ne_owner := houtsideNe
    source_free_semantics := hfreeSemantics
    source_owner_floor_cap := hownerFloorCap
    source_owner_debt := hownerDebt
    repaired_owner_payoff_eq_source_cap := hrepairedOwner
    repaired_owner_cap_eq_payoff := hrepairedOwnerCap
    repaired_owner_gain := hrepairedGain
    repaired_owner_floor := hrepairedFloor
    outside_debt := houtsideDebt
    floor_dispatch := hfloorDispatch
    paid_row := hpaid }⟩

namespace QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {witness : QuittingTerminalExploitabilityWitness reward}
variable {seed : Finset ι}

/-- The actual large-base paid residual together with its reselected
singleton-owner Nash point and complete stationary semantic handoff.  The
original paid-chain residual is retained verbatim; no chronological connector
from its boundary source to the reselected point is asserted. -/
structure LargeBasePaidStationaryHandoff
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) where
  baseFirst : ι
  baseSecond : ι
  first : ι
  second : ι
  paid : ι
  owner : ι
  gamma : ℝ
  delta : ℝ
  baseFirst_ne_baseSecond : baseFirst ≠ baseSecond
  first_ne_second : first ≠ second
  persistentBase_eq : cycle.persistentBase = {baseFirst, baseSecond}
  freePlayers_eq : cycle.freePlayers = {first, second}
  gamma_pos : 0 < gamma
  paid_owner_pair :
    (paid = baseFirst ∧ owner = baseSecond) ∨
      (paid = baseSecond ∧ owner = baseFirst)
  paidChainResidual : HasSupportTwoNormalPaidChainResidual reward
    baseFirst baseSecond first second gamma
  reselectedFree_eq : ({paid, first, second} : Finset ι) =
    Finset.univ.erase owner
  delta_pos : 0 < delta
  point : mixedPolytope (quittingBinaryForm
    ({paid, first, second} : Finset ι)).sig
  point_mem : point ∈ quittingPersistentBaseNashSet reward {owner}
    {paid, first, second}
  delta_le_ownerFloorExcess : delta ≤
    quittingSingletonBaseOwnerFloorExcess reward owner
      (quittingPersistentBaseRoot {owner} {paid, first, second} point)
  semanticHandoff : Nonempty (QuittingSingletonBaseStationaryHandoff reward
    owner {paid, first, second} point delta witness.terminalGap)

/-- **Actual large-base source-to-consumer adapter.**  On four players, the
checked support-two paid-chain residual chooses a paid base label.  Moving
that label into the two-player free face leaves the other base label as the
singleton owner.  Compact Nash re-selection supplies a positive owner-floor
gap and any selected Nash point enters the complete stationary repair and
paid-row handoff above. -/
theorem exists_largeBasePaidStationaryHandoff
    (cycle : witness.ReachableStrictToggleSimpleCycle seed)
    (hfour : Fintype.card ι = 4)
    (residual : cycle.HasLargeBasePaidChainResidual) :
    Nonempty cycle.LargeBasePaidStationaryHandoff := by
  obtain ⟨baseFirst, baseSecond, first, second, gamma,
    hbaseNe, hfirstNe, hbase, hfree, hgamma, hpaidResidual⟩ := residual
  have hdisjoint : Disjoint ({baseFirst, baseSecond} : Finset ι)
      {first, second} := by
    rw [← hbase, ← hfree]
    exact cycle.disjoint_persistentBase_freePlayers
  have hunionCard :
      (({baseFirst, baseSecond} : Finset ι) ∪ {first, second}).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisjoint,
      Finset.card_pair hbaseNe, Finset.card_pair hfirstNe]
  have hunion : ({baseFirst, baseSecond} : Finset ι) ∪ {first, second} =
      Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hunionCard]
    exact hfour.symm
  obtain ⟨paid, owner, hpair⟩ :=
    hpaidResidual.exists_paid_owner reward baseFirst baseSecond first second gamma
  have hpairSet : ({paid, owner} : Finset ι) = {baseFirst, baseSecond} := by
    rcases hpair with hpair | hpair
    · simp [hpair.1, hpair.2]
    · simp [hpair.1, hpair.2, Finset.pair_comm]
  have hpaidOwner : paid ≠ owner := by
    rcases hpair with hpair | hpair
    · simpa [hpair.1, hpair.2] using hbaseNe
    · simpa [hpair.1, hpair.2] using hbaseNe.symm
  have hownerMem : owner ∈ ({baseFirst, baseSecond} : Finset ι) := by
    rw [← hpairSet]
    simp
  have hownerFirst : owner ≠ first := by
    intro heq
    apply Finset.disjoint_left.mp hdisjoint hownerMem
    simp [heq]
  have hownerSecond : owner ≠ second := by
    intro heq
    apply Finset.disjoint_left.mp hdisjoint hownerMem
    simp [heq]
  have hpartition : ({paid, owner} : Finset ι) ∪ {first, second} =
      Finset.univ := by
    rw [hpairSet]
    exact hunion
  have hreselected : ({paid, first, second} : Finset ι) =
      Finset.univ.erase owner := by
    have herase := congrArg (fun set : Finset ι => set.erase owner) hpartition
    have herase' : ({second, paid, first} : Finset ι) =
        Finset.univ.erase owner := by
      simpa [hpaidOwner, hpaidOwner.symm, hownerFirst, hownerFirst.symm,
        hownerSecond, hownerSecond.symm, Finset.pair_comm,
        Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
          herase
    calc
      ({paid, first, second} : Finset ι) = {second, paid, first} := by
        ext player
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      _ = Finset.univ.erase owner := herase'
  obtain ⟨delta, hdelta, hgap⟩ :=
    witness.exists_pos_ownerFloorExcess_gap owner {paid, first, second}
      hreselected
  obtain ⟨point, hpoint⟩ := quittingPersistentBaseNashSet_nonempty reward
    ({owner} : Finset ι) {paid, first, second}
  have hhandoff := exists_singletonBaseStationaryHandoff reward owner
    {paid, first, second} hreselected point hpoint witness hdelta
      (hgap point hpoint)
  exact ⟨{
    baseFirst := baseFirst
    baseSecond := baseSecond
    first := first
    second := second
    paid := paid
    owner := owner
    gamma := gamma
    delta := delta
    baseFirst_ne_baseSecond := hbaseNe
    first_ne_second := hfirstNe
    persistentBase_eq := hbase
    freePlayers_eq := hfree
    gamma_pos := hgamma
    paid_owner_pair := hpair
    paidChainResidual := hpaidResidual
    reselectedFree_eq := hreselected
    delta_pos := hdelta
    point := point
    point_mem := hpoint
    delta_le_ownerFloorExcess := hgap point hpoint
    semanticHandoff := hhandoff }⟩

end QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

end GameTheory
