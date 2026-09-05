/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Cycles.PeriodOneStationarySubsetLimits
import UniformEquilibrium.Quitting.Stationary.StrictEndpointSelection
import UniformEquilibrium.Quitting.Root.ImmediateQuitCapDisplacement
import UniformEquilibrium.Quitting.Classification.LCP.FourPlayerSingletonColumnBlockers
import UniformEquilibrium.Diagnostics.Quitting.CompleteCapSingletonLimitCollar
import MathUE.LinearProgramming.TwoPointHomogeneousObstruction

/-! # Chronological stationary descent to an off-minimum paid Quit-now port -/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open QuittingLCPClassification Math.LinearProgramming
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- An actual stationary source at which one fixed Quit-now response attains
the unrestricted cap, pays uniformly, and stays outside the minimum fiber. -/
structure StationaryOffMinimumQuitNowPort
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ℕ → ι → PMF Bool) where
  payer : ι
  gain : ℝ
  gain_pos : 0 < gain
  cap_tendsto : Tendsto (fun index ↦ quittingContinuationBestResponseValue reward
    (quittingStationaryProfile reward (root index)) payer) atTop
    (nhds (quittingSoloReward reward payer payer))
  minimum : QuittingTerminalSemanticPair ι
  minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward
  minimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤ quittingTerminalSemanticDebtSum candidate
  minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum
  collar : ℝ
  collar_pos : 0 < collar
  eventually_paid : ∀ᶠ index in atTop,
    stationaryQuitNowPayoff reward (root index) payer =
      quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward (root index)) payer ∧
    gain ≤ stationaryQuitNowPayoff reward (root index) payer -
      quittingTerminalPayoff reward (quittingStationaryProfile reward (root index)) payer ∧
    quittingTerminalSemanticDebtSum minimum + collar ≤
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (quittingStationaryProfile reward (root index))) ∧
    1 / 2 ≤ quittingStationaryContinueMass (root index) ∧
    1 / 2 ≤ (root index payer false).toReal ∧
    1 / 2 ≤ quittingRootOpponentContinueMass (root index) payer

omit [Nontrivial ι] in
/-- The final paid decision is the actual date-zero row, reached with
probability one. Continue has positive source support, its continuation is
the same stationary profile, and the local Quit-minus-Continue gap is paid. -/
theorem StationaryOffMinimumQuitNowPort.eventually_paid_initialRow
    {root : ℕ → ι → PMF Bool} (port : StationaryOffMinimumQuitNowPort reward root) :
    ∀ᶠ index in atTop,
      quittingLiveMass reward (quittingStationaryProfile reward (root index)) 0 = 1 ∧
      quittingProfileLiveRoot reward (quittingStationaryProfile reward (root index)) 0 =
        root index ∧
      quittingRootThenContinuationProfile reward (root index)
        (quittingStationaryProfile reward (root index)) =
          quittingStationaryProfile reward (root index) ∧
      0 < (root index port.payer false).toReal ∧
      port.gain ≤ quittingRootEndpointDifference reward
        (fun who ↦ quittingTerminalPayoff reward
          (quittingStationaryProfile reward (root index)) who) (root index) port.payer := by
  filter_upwards [port.eventually_paid] with index hp
  have hcap : quittingTerminalPayoff reward
      (Function.update (quittingRootThenContinuationProfile reward (root index)
        (quittingStationaryProfile reward (root index))) port.payer
        (quittingPureTimeBehaviorStrategy reward port.payer (some 0))) port.payer =
      quittingContinuationBestResponseValue reward
        (quittingRootThenContinuationProfile reward (root index)
          (quittingStationaryProfile reward (root index))) port.payer := by
    simpa only [quittingRootThenContinuationProfile_stationary, stationaryQuitNowPayoff] using hp.1
  have hid :=
    quittingTerminalDeviationDebt_rootThen_eq_continue_mul_endpointDifference_of_quitZeroCap
      reward (root index) (quittingStationaryProfile reward (root index)) port.payer hcap
  simp only [quittingRootThenContinuationProfile_stationary, quittingTerminalDeviationDebt,
    ← hp.1] at hid
  have hgain : port.gain ≤ (root index port.payer false).toReal *
      quittingRootEndpointDifference reward
        (fun who ↦ quittingTerminalPayoff reward
          (quittingStationaryProfile reward (root index)) who) (root index) port.payer := by
    rw [← hid]
    exact hp.2.1
  have hnonneg : 0 ≤ quittingRootEndpointDifference reward
      (fun who ↦ quittingTerminalPayoff reward
        (quittingStationaryProfile reward (root index)) who) (root index) port.payer := by
    by_contra hnot
    have hmul := mul_nonpos_of_nonneg_of_nonpos
      (ENNReal.toReal_nonneg (a := root index port.payer false)) (le_of_lt (lt_of_not_ge hnot))
    linarith [port.gain_pos]
  have hupper : (root index port.payer false).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top ((root index port.payer).coe_le_one false)
  refine ⟨quittingLiveMass_zero _ _, by simp, by simp, ?_, ?_⟩
  · linarith [hp.2.2.2.2.1]
  · exact hgain.trans (by nlinarith)

namespace PeriodOneNormalizedSourceLimit

variable {error : ℕ → ℝ} {source : PeriodOneVanishingHazardSource reward error}

/-- A finite actual chronology: each Never edge starts at the preceding
literal child, and the last counted move is the paid Quit-now response. -/
inductive StationarySubsetPaidDescent (limit : PeriodOneNormalizedSourceLimit source) :
    Finset ι → ℕ → Prop
  | paid (retained : Finset ι)
      (port : Nonempty (StationaryOffMinimumQuitNowPort reward (limit.subsetRoot retained))) :
      StationarySubsetPaidDescent limit retained 1
  | never (retained : Finset ι) (owner : ι) (gain : ℝ) (gain_pos : 0 < gain)
      (edge : ∀ᶠ index in atTop,
        IsExactNeverCapEdge reward (limit.subsetProfile retained index)
          (limit.subsetProfile (retained.erase owner) index) owner gain)
      {steps : ℕ} (tail : StationarySubsetPaidDescent limit (retained.erase owner) steps) :
      StationarySubsetPaidDescent limit retained (steps + 1)

/-- One fixed finite update chain, realized on one common eventual tail.
Only the final response is Quit-now; every preceding response is Never. -/
structure LiteralStationaryPaidCapChain
    (start : ℕ → (quittingGame reward).BehaviorProfile) (steps : ℕ) where
  steps_pos : 0 < steps
  profile : ℕ → ℕ → (quittingGame reward).BehaviorProfile
  mover : ℕ → ι
  gain : ℝ
  gain_pos : 0 < gain
  source_eq : ∀ index, profile 0 index = start index
  lastRoot : ℕ → ι → PMF Bool
  lastRoot_continue_tendsto : ∀ who,
    Tendsto (fun index ↦ (lastRoot index who false).toReal) atTop (nhds 1)
  port : StationaryOffMinimumQuitNowPort reward lastRoot
  last_source_eq : ∀ index, profile (steps - 1) index =
    quittingStationaryProfile reward (lastRoot index)
  last_mover_eq : mover (steps - 1) = port.payer
  eventually_chain : ∀ᶠ index in atTop, ∀ step < steps,
    profile (step + 1) index = Function.update (profile step index) (mover step)
      (quittingPureTimeBehaviorStrategy reward (mover step)
        (if step + 1 = steps then some 0 else none)) ∧
    quittingTerminalPayoff reward (profile (step + 1) index) (mover step) =
      quittingContinuationBestResponseValue reward (profile step index) (mover step) ∧
    gain ≤ quittingTerminalPayoff reward (profile (step + 1) index) (mover step) -
      quittingTerminalPayoff reward (profile step index) (mover step)

theorem StationarySubsetPaidDescent.exists_literalChain
    {limit : PeriodOneNormalizedSourceLimit source} {retained : Finset ι} {steps : ℕ}
    (descent : StationarySubsetPaidDescent limit retained steps) :
    Nonempty (LiteralStationaryPaidCapChain (limit.subsetProfile retained) steps) := by
  induction descent with
  | paid retained hport =>
      obtain ⟨port⟩ := hport
      let profiles := fun step index ↦ if step = 0 then limit.subsetProfile retained index else
        Function.update (limit.subsetProfile retained index) port.payer
          (quittingPureTimeBehaviorStrategy reward port.payer (some 0))
      refine ⟨{
        steps_pos := by norm_num
        profile := profiles
        mover := fun _ ↦ port.payer
        gain := port.gain
        gain_pos := port.gain_pos
        source_eq := by intro index; simp [profiles]
        lastRoot := limit.subsetRoot retained
        lastRoot_continue_tendsto := fun who ↦
          (limit.subsetRoot_continueLimits retained who).2.1
        port := port
        last_source_eq := by intro index; simp [profiles, subsetProfile]
        last_mover_eq := rfl
        eventually_chain := ?_ }⟩
      filter_upwards [port.eventually_paid] with index hpaid
      intro step hstep
      have : step = 0 := by omega
      subst step
      exact ⟨by simp [profiles], hpaid.1, hpaid.2.1⟩
  | @never retained owner gain hgain hedge steps tail ih =>
      obtain ⟨chain⟩ := ih
      let profiles := fun step index ↦ if step = 0 then limit.subsetProfile retained index else
        chain.profile (step - 1) index
      let movers := fun step ↦ if step = 0 then owner else chain.mover (step - 1)
      refine ⟨{
        steps_pos := Nat.succ_pos steps
        profile := profiles
        mover := movers
        gain := min gain chain.gain
        gain_pos := lt_min hgain chain.gain_pos
        source_eq := by intro index; simp [profiles]
        lastRoot := chain.lastRoot
        lastRoot_continue_tendsto := chain.lastRoot_continue_tendsto
        port := chain.port
        last_source_eq := ?_
        last_mover_eq := ?_
        eventually_chain := ?_ }⟩
      · intro index
        simpa [profiles, Nat.ne_of_gt chain.steps_pos] using chain.last_source_eq index
      · simpa [movers, Nat.ne_of_gt chain.steps_pos] using chain.last_mover_eq
      · filter_upwards [hedge, chain.eventually_chain] with index hedgeIndex hchainIndex
        intro step hstep
        cases step with
        | zero =>
            have hsource := chain.source_eq index
            refine ⟨?_, ?_, ?_⟩
            · simpa [profiles, movers, Nat.ne_of_gt chain.steps_pos, hsource] using hedgeIndex.1
            · simpa [profiles, movers, hsource] using hedgeIndex.2.1
            · exact (min_le_left gain chain.gain).trans
                (by simpa [profiles, movers, hsource] using hedgeIndex.2.2)
        | succ step =>
            have h := hchainIndex step (by omega)
            refine ⟨?_, ?_, ?_⟩
            · simpa [profiles, movers, Nat.succ_eq_add_one] using h.1
            · simpa [profiles, movers, Nat.succ_eq_add_one] using h.2.1
            · exact (min_le_right gain chain.gain).trans
                (by simpa [profiles, movers, Nat.succ_eq_add_one] using h.2.2)

omit [Nontrivial ι] in
/-- All fixed-label updates, the final source collar, and the actual paid
date-zero row hold on one common eventual tail of the original sequence. -/
theorem LiteralStationaryPaidCapChain.eventually_chain_and_paidRow
    {start : ℕ → (quittingGame reward).BehaviorProfile} {steps : ℕ}
    (chain : LiteralStationaryPaidCapChain start steps) :
    ∀ᶠ index in atTop,
      (∀ step < steps,
        chain.profile (step + 1) index =
          Function.update (chain.profile step index) (chain.mover step)
            (quittingPureTimeBehaviorStrategy reward (chain.mover step)
              (if step + 1 = steps then some 0 else none)) ∧
        quittingTerminalPayoff reward (chain.profile (step + 1) index) (chain.mover step) =
          quittingContinuationBestResponseValue reward
            (chain.profile step index) (chain.mover step) ∧
        chain.gain ≤
          quittingTerminalPayoff reward (chain.profile (step + 1) index) (chain.mover step) -
            quittingTerminalPayoff reward (chain.profile step index) (chain.mover step)) ∧
      quittingTerminalSemanticDebtSum chain.port.minimum + chain.port.collar ≤
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (chain.profile (steps - 1) index)) ∧
      quittingLiveMass reward (chain.profile (steps - 1) index) 0 = 1 ∧
      0 < (chain.lastRoot index chain.port.payer false).toReal ∧
      chain.port.gain ≤ quittingRootEndpointDifference reward
        (fun who ↦ quittingTerminalPayoff reward (chain.profile (steps - 1) index) who)
        (chain.lastRoot index) chain.port.payer := by
  filter_upwards [chain.eventually_chain, chain.port.eventually_paid,
    chain.port.eventually_paid_initialRow] with index hchain hport hrow
  rw [chain.last_source_eq index]
  exact ⟨hchain, hport.2.2.1, hrow.1, hrow.2.2.2.1, hrow.2.2.2.2⟩

/-- Strict limiting endpoint separation produces a full paid port at the
literal subset source. No cap limit or off-minimum conclusion is assumed. -/
theorem exists_subsetPaidPort_of_strict_endpointLimits
    (limit : PeriodOneNormalizedSourceLimit source)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (retained : Finset ι) (payer : ι)
    (hmass : 0 < limit.subsetMass retained)
    (hrest : 0 < limit.subsetMass (retained.erase payer))
    (hstrict : limit.subsetValue (retained.erase payer) payer <
      quittingSoloReward reward payer payer)
    (hgain : 0 < quittingSoloReward reward payer payer - limit.subsetValue retained payer) :
    ∃ port : StationaryOffMinimumQuitNowPort reward (limit.subsetRoot retained),
      port.payer = payer ∧ port.gain =
        (quittingSoloReward reward payer payer - limit.subsetValue retained payer) / 2 := by
  have hquit := limit.subsetProfile_quitNow_tendsto retained payer
  have hnever := limit.subsetProfile_anyNever_tendsto retained payer hrest
  have hpayoff := limit.subsetProfile_payoff_tendsto retained hmass payer
  have hpaid := eventually_quitNow_eq_completeCap_and_gain_ge_of_tendsto reward
    (limit.subsetRoot retained) payer (quittingSoloReward reward payer payer)
    (limit.subsetValue (retained.erase payer) payer) (limit.subsetValue retained payer)
    hquit hnever hpayoff hstrict hgain
  have hcap : Tendsto (fun index ↦ quittingContinuationBestResponseValue reward
      (quittingStationaryProfile reward (limit.subsetRoot retained index)) payer) atTop
      (nhds (quittingSoloReward reward payer payer)) :=
    hquit.congr' (hpaid.mono fun _ h ↦ h.1)
  obtain ⟨minimum, hminimumMem, hminimum, hminimumPos, collar, hcollar, heventCollar⟩ :=
    exists_eventual_offMinimum_collar_of_completeCap_tendsto_singleton reward hno
      (limit.subsetProfile retained) payer hcap
  refine ⟨{
    payer := payer
    gain := (quittingSoloReward reward payer payer - limit.subsetValue retained payer) / 2
    gain_pos := half_pos hgain
    cap_tendsto := hcap
    minimum := minimum
    minimum_mem := hminimumMem
    minimum_le := hminimum
    minimum_pos := hminimumPos
    collar := collar
    collar_pos := hcollar
    eventually_paid := ?_ }, rfl, rfl⟩
  filter_upwards [hpaid, heventCollar,
    (limit.subsetRoot_continueLimits retained payer).2.2.2] with index hp hc hl
  exact ⟨hp.1, hp.2, hc, hl⟩

/-- A negative singleton margin makes Quit-now strictly better than both
the prescribed payoff and Never at the same subset source. -/
theorem exists_subsetPaidPort_of_negative_margin
    (limit : PeriodOneNormalizedSourceLimit source)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (retained : Finset ι) (payer : ι)
    (hmass : 0 < limit.subsetMass retained)
    (hrest : 0 < limit.subsetMass (retained.erase payer))
    (hmargin : (∑ owner ∈ retained, limit.direction.val owner *
      (quittingSoloReward reward owner payer - quittingSoloReward reward payer payer)) < 0) :
    Nonempty (StationaryOffMinimumQuitNowPort reward (limit.subsetRoot retained)) := by
  have hsame : (∑ owner ∈ retained.erase payer, limit.direction.val owner *
      (quittingSoloReward reward owner payer - quittingSoloReward reward payer payer)) =
      ∑ owner ∈ retained, limit.direction.val owner *
        (quittingSoloReward reward owner payer - quittingSoloReward reward payer payer) := by
    by_cases hmem : payer ∈ retained
    · have h := Finset.sum_erase_add retained
        (fun owner ↦ limit.direction.val owner *
          (quittingSoloReward reward owner payer - quittingSoloReward reward payer payer)) hmem
      simpa using h
    · simp [Finset.erase_eq_of_notMem hmem]
  have hprescribed : limit.subsetValue retained payer -
      quittingSoloReward reward payer payer < 0 := by
    rw [limit.subsetValue_sub_solo retained hmass]
    exact div_neg_of_neg_of_pos hmargin hmass
  have hnever : limit.subsetValue (retained.erase payer) payer -
      quittingSoloReward reward payer payer < 0 := by
    rw [limit.subsetValue_sub_solo (retained.erase payer) hrest, hsame]
    exact div_neg_of_neg_of_pos hmargin hrest
  obtain ⟨port, _, _⟩ := limit.exists_subsetPaidPort_of_strict_endpointLimits
    hno retained payer hmass hrest (by linarith) (by linarith)
  exact ⟨port⟩

/-- A fixed column blocker yields a paid off-minimum port at every literal
singleton descendant, including original zero-share outsider hazards. -/
theorem exists_singletonSubsetPaidPort_with_blocker
    (limit : PeriodOneNormalizedSourceLimit source)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (blockers : SingletonColumnBlockerCertificate reward)
    {owner : ι} (hpositive : 0 < limit.direction.val owner) :
    ∃ port : StationaryOffMinimumQuitNowPort reward (limit.subsetRoot {owner}),
      port.payer = blockers.blocker owner ∧ blockers.gap / 2 ≤ port.gain := by
  have hmass : 0 < limit.subsetMass {owner} := by simpa [subsetMass] using hpositive
  have herase : ({owner} : Finset ι).erase (blockers.blocker owner) = {owner} := by
    simp [blockers.blocker_ne owner]
  have hgap := blockers.gap_pos.trans_le (blockers.gap_le owner)
  obtain ⟨port, hpayer, hgain⟩ := limit.exists_subsetPaidPort_of_strict_endpointLimits hno {owner}
    (blockers.blocker owner) hmass (by rwa [herase])
    (by rw [herase, limit.subsetValue_singleton hpositive]; linarith)
    (by rw [limit.subsetValue_singleton hpositive]; exact hgap)
  refine ⟨port, hpayer, ?_⟩
  rw [hgain, limit.subsetValue_singleton hpositive]
  linarith [blockers.gap_le owner]

theorem exists_singletonSubsetPaidPort
    (limit : PeriodOneNormalizedSourceLimit source)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (blockers : SingletonColumnBlockerCertificate reward)
    {owner : ι} (hpositive : 0 < limit.direction.val owner) :
    Nonempty (StationaryOffMinimumQuitNowPort reward (limit.subsetRoot {owner})) := by
  obtain ⟨port, _, _⟩ := limit.exists_singletonSubsetPaidPort_with_blocker hno blockers hpositive
  exact ⟨port⟩

/-- A strictly positive cross entry pays a Never move at the two-owner source,
followed by the fixed singleton blocker's paid Quit-now move. -/
theorem pairSubset_paidDescent_of_positive_cross
    (limit : PeriodOneNormalizedSourceLimit source)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (blockers : SingletonColumnBlockerCertificate reward)
    {first second : ι} (hne : first ≠ second)
    (hfirst : 0 < limit.direction.val first) (hsecond : 0 < limit.direction.val second)
    (hcross : 0 < quittingSoloReward reward second first - quittingSoloReward reward first first) :
    StationarySubsetPaidDescent limit {first, second} 2 := by
  have herase : ({first, second} : Finset ι).erase first = {second} := by simp [hne]
  have hrest : 0 < limit.subsetMass (({first, second} : Finset ι).erase first) := by
    simpa [herase, subsetMass] using hsecond
  have hmargin : 0 < ∑ owner ∈ ({first, second} : Finset ι).erase first,
      limit.direction.val owner *
        (quittingSoloReward reward owner first - quittingSoloReward reward first first) := by
    simpa [herase] using mul_pos hsecond hcross
  obtain ⟨gain, hgain, hedge⟩ := limit.eventually_subsetNever_edge
    {first, second} (by simp) hfirst hrest hmargin
  have hport := limit.exists_singletonSubsetPaidPort hno blockers hsecond
  apply StationarySubsetPaidDescent.never _ first gain hgain hedge
  rw [herase]
  exact .paid _ hport

/-- A strictly negative cross entry makes the corresponding owner's Quit-now
response a paid off-minimum port directly at the two-owner source. -/
theorem pairSubset_paidDescent_of_negative_cross
    (limit : PeriodOneNormalizedSourceLimit source)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    {first second : ι} (hne : first ≠ second)
    (hfirst : 0 < limit.direction.val first) (hsecond : 0 < limit.direction.val second)
    (hcross : quittingSoloReward reward second first - quittingSoloReward reward first first < 0) :
    StationarySubsetPaidDescent limit {first, second} 1 := by
  have herase : ({first, second} : Finset ι).erase first = {second} := by simp [hne]
  have hmass : 0 < limit.subsetMass {first, second} := by
    simpa [subsetMass, Finset.sum_pair hne] using add_pos hfirst hsecond
  have hrest : 0 < limit.subsetMass (({first, second} : Finset ι).erase first) := by
    simpa [herase, subsetMass] using hsecond
  have hmargin : (∑ owner ∈ ({first, second} : Finset ι), limit.direction.val owner *
      (quittingSoloReward reward owner first - quittingSoloReward reward first first)) < 0 := by
    simpa [Finset.sum_pair hne] using mul_neg_of_pos_of_neg hsecond hcross
  exact .paid _ (limit.exists_subsetPaidPort_of_negative_margin
    hno {first, second} first hmass hrest hmargin)

/-- The full homogeneous obstruction supplies the missing removed-coordinate
blocker in the zero-cross case; no negative outsider is an input. -/
theorem exists_pairSubset_paidDescent
    (limit : PeriodOneNormalizedSourceLimit source)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (blockers : SingletonColumnBlockerCertificate reward)
    (hhom : ¬ SingletonLCPFeasible (normalizedSoloMatrix reward))
    {first second : ι} (hne : first ≠ second)
    (hfirst : 0 < limit.direction.val first) (hsecond : 0 < limit.direction.val second) :
    ∃ steps ∈ ({1, 2} : Finset ℕ), StationarySubsetPaidDescent limit {first, second} steps := by
  let mass := limit.direction.val first + limit.direction.val second
  have hmass : 0 < mass := add_pos hfirst hsecond
  have hmatrix (who owner : ι) : normalizedSoloMatrix reward who owner =
      quittingSoloReward reward owner who - quittingSoloReward reward who who := by
    rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
    rfl
  have hexit := twoPointMatrixExit_of_noHomogeneous (normalizedSoloMatrix reward) first second
    (limit.direction.val first / mass) (limit.direction.val second / mass)
    (div_nonneg hfirst.le hmass.le) (div_nonneg hsecond.le hmass.le)
    (by rw [← add_div]; exact div_self hmass.ne')
    (normalizedSoloMatrix_diagonal reward) hhom
  cases hexit with
  | firstPositive hcross =>
      exact ⟨2, by simp, limit.pairSubset_paidDescent_of_positive_cross hno blockers hne
        hfirst hsecond (by rwa [hmatrix] at hcross)⟩
  | firstNegative hcross =>
      exact ⟨1, by simp, limit.pairSubset_paidDescent_of_negative_cross hno hne
        hfirst hsecond (by rwa [hmatrix] at hcross)⟩
  | secondPositive hcross =>
      refine ⟨2, by simp, ?_⟩
      simpa only [Finset.pair_comm] using
        limit.pairSubset_paidDescent_of_positive_cross hno blockers hne.symm
          hsecond hfirst (by rwa [hmatrix] at hcross)
  | secondNegative hcross =>
      refine ⟨1, by simp, ?_⟩
      simpa only [Finset.pair_comm] using
        limit.pairSubset_paidDescent_of_negative_cross hno hne.symm
          hsecond hfirst (by rwa [hmatrix] at hcross)
  | outsiderNegative outsider houtside hresidual =>
      have hres : (normalizedSoloMatrix reward outsider first * limit.direction.val first +
          normalizedSoloMatrix reward outsider second * limit.direction.val second) / mass < 0 := by
        simpa only [← mul_div_assoc, ← add_div] using hresidual
      have hnegative := (div_neg_iff.mp hres).resolve_left
        (fun h ↦ (not_lt_of_ge hmass.le) h.2) |>.1
      have herase : ({first, second} : Finset ι).erase outsider = {first, second} :=
        Finset.erase_eq_of_notMem houtside
      have hsubsetMass : 0 < limit.subsetMass {first, second} := by
        simpa [subsetMass, Finset.sum_pair hne] using hmass
      have hmargin : (∑ owner ∈ ({first, second} : Finset ι), limit.direction.val owner *
          (quittingSoloReward reward owner outsider -
            quittingSoloReward reward outsider outsider)) < 0 := by
        simpa only [Finset.sum_pair hne, hmatrix, mul_comm] using hnegative
      refine ⟨1, by simp, .paid _ ?_⟩
      exact limit.exists_subsetPaidPort_of_negative_margin hno {first, second} outsider
        hsubsetMass (by rwa [herase]) hmargin

/-- The exact move counts: two moves from support two, three from support
three, and three or four from support four. -/
def StationarySupportDescentLength (support steps : ℕ) : Prop :=
  (support = 2 ∧ steps = 2) ∨ (support = 3 ∧ steps = 3) ∨
    (support = 4 ∧ (steps = 3 ∨ steps = 4))

/-- The common positive tropical margin yields a chronological finite descent
on the original source selector, ending at a produced off-minimum paid port. -/
theorem exists_support_paidDescent
    (limit : PeriodOneNormalizedSourceLimit source)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (blockers : SingletonColumnBlockerCertificate reward)
    (hhom : ¬ SingletonLCPFeasible (normalizedSoloMatrix reward))
    {minimum : ℝ} (hminimum : 0 < minimum)
    (hcommon : ∀ who ∈ limit.positiveSupport, limit.limitingSingletonMargin who = minimum)
    (hcard : limit.positiveSupport.card ∈ ({2, 3, 4} : Finset ℕ)) :
    ∃ steps, StationarySupportDescentLength limit.positiveSupport.card steps ∧
      StationarySubsetPaidDescent limit limit.positiveSupport steps := by
  have hpositive {who : ι} (hwho : who ∈ limit.positiveSupport) :
      0 < limit.direction.val who := (Finset.mem_filter.mp hwho).2
  by_cases htwo : limit.positiveSupport.card = 2
  · obtain ⟨first, hfirst, last, gain, hgain, herase, hedge⟩ :=
      limit.exists_chronological_Never_singletonDescent hminimum hcommon htwo
    have hlast : last ∈ limit.positiveSupport :=
      (Finset.erase_subset first limit.positiveSupport)
        (by rw [herase]; simp)
    have hport := limit.exists_singletonSubsetPaidPort hno blockers (hpositive hlast)
    refine ⟨2, Or.inl ⟨htwo, rfl⟩, ?_⟩
    apply StationarySubsetPaidDescent.never _ first gain hgain
    · simpa only [subsetProfile_positiveSupport, herase] using hedge
    · rw [herase]
      exact .paid _ hport
  · have hthree : 3 ≤ limit.positiveSupport.card := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcard
      omega
    obtain ⟨first, hfirst, second, hsecond, firstGain, secondGain,
      hfirstGain, hsecondGain, hlastCard, hedge⟩ :=
      limit.exists_chronological_twoNever_supportDescent hminimum hcommon hthree
    let last := (limit.positiveSupport.erase first).erase second
    have hlastSubset : last ⊆ limit.positiveSupport :=
      (Finset.erase_subset second (limit.positiveSupport.erase first)).trans
        (Finset.erase_subset first limit.positiveSupport)
    have hprefix (steps : ℕ) (htail : StationarySubsetPaidDescent limit last steps) :
        StationarySubsetPaidDescent limit limit.positiveSupport (steps + 2) := by
      apply StationarySubsetPaidDescent.never _ first firstGain hfirstGain
      · simpa only [subsetProfile_positiveSupport] using hedge.mono (fun _ h ↦ h.1)
      · exact .never _ second secondGain hsecondGain (hedge.mono fun _ h ↦ h.2) htail
    by_cases hsupportThree : limit.positiveSupport.card = 3
    · have hlastOne : last.card = 1 := by dsimp [last]; omega
      obtain ⟨owner, howner⟩ := Finset.card_eq_one.mp hlastOne
      have hownerSupport : owner ∈ limit.positiveSupport :=
        hlastSubset (by rw [howner]; simp)
      have htail : StationarySubsetPaidDescent limit last 1 := by
        rw [howner]
        exact .paid _ (limit.exists_singletonSubsetPaidPort hno blockers (hpositive hownerSupport))
      exact ⟨3, Or.inr (Or.inl ⟨hsupportThree, rfl⟩), hprefix 1 htail⟩
    · have hsupportFour : limit.positiveSupport.card = 4 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcard
        omega
      have hlastTwo : last.card = 2 := by dsimp [last]; omega
      obtain ⟨owner, other, hne, howners⟩ := Finset.card_eq_two.mp hlastTwo
      have hownerSupport : owner ∈ limit.positiveSupport :=
        hlastSubset (by rw [howners]; simp)
      have hotherSupport : other ∈ limit.positiveSupport :=
        hlastSubset (by rw [howners]; simp)
      obtain ⟨steps, hsteps, htail⟩ := limit.exists_pairSubset_paidDescent hno blockers hhom hne
        (hpositive hownerSupport) (hpositive hotherSupport)
      refine ⟨steps + 2, Or.inr (Or.inr ⟨hsupportFour, ?_⟩), ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hsteps
        omega
      · exact hprefix steps (by rwa [howners])

end PeriodOneNormalizedSourceLimit

/-- A four-player counterexample produces one actual period-one source,
one selected subsequence, and a literal two-to-four-move full-cap chronology
ending in a paid Quit-now response at an off-minimum stationary source. -/
theorem exists_periodOne_literalPaidCapChain_of_fourPlayer_noUniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hplayers : Fintype.card ι = 4)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (error : ℕ → ℝ) (herrorPos : ∀ index, 0 < error index)
    (herror : Tendsto error atTop (nhds 0)) :
    ∃ source : PeriodOneVanishingHazardSource reward error,
      ∃ limit : PeriodOneNormalizedSourceLimit source, ∃ steps ∈ ({2, 3, 4} : Finset ℕ),
        PeriodOneNormalizedSourceLimit.StationarySupportDescentLength
          limit.positiveSupport.card steps ∧
        Nonempty (PeriodOneNormalizedSourceLimit.LiteralStationaryPaidCapChain
          (fun index ↦ source.profile (limit.select index)) steps) := by
  obtain ⟨source, ⟨limit⟩⟩ := exists_periodOneNormalizedSourceLimit_of_fourPlayer_noUniformPayoff
    reward hplayers hno error herrorPos herror
  obtain ⟨minimum, hminimum, _, hcommon⟩ :=
    limit.exists_positive_commonMinimum_limitingSingletonMargin hplayers hno herrorPos herror
  obtain ⟨hhom, ⟨blockers⟩⟩ :=
    exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform reward hplayers hno
  have hcard := limit.positiveDirectionSupport_card hplayers
    (limit.exists_two_distinct_direction_positive hplayers hno herrorPos herror)
  obtain ⟨steps, hlength, hdescent⟩ := limit.exists_support_paidDescent hno blockers hhom hminimum
    (fun who hwho ↦ hcommon who (Finset.mem_filter.mp hwho).2) hcard
  have hchain := hdescent.exists_literalChain
  have hsource : limit.subsetProfile limit.positiveSupport =
      fun index ↦ source.profile (limit.select index) :=
    funext limit.subsetProfile_positiveSupport
  rw [hsource] at hchain
  refine ⟨source, limit, steps, ?_, hlength, hchain⟩
  rcases hlength with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl | rfl⟩ <;> simp

end GameTheory
