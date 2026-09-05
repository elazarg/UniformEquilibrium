/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FirstExactRootSurvivalResponses
import UniformEquilibrium.Quitting.Stationary.CompleteEndpointChoices

/-! # First exact roots at an actual stationary Quit-now cap pin

The source retains actual stationary profiles. Compactification and endpoint
choices are produced, not source assumptions. Stationary opponents may all
Continue surely. Neither surviving branch claims a renewed cap pin or source.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]


/-- The stationary repetition of the supplied sure-owner exact root has
zero outsider debt and a complete Never cap paid by the fixed terminal gap. -/
theorem stationaryNeverReset_of_sure_exactRoot
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (tail : Payoff ι) (root : ι → PMF Bool) (owner : ι)
    (hsure : root owner = PMF.pure true)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    (∀ other, other ≠ owner →
      quittingTerminalDeviationDebt reward (quittingStationaryProfile reward root) other = 0) ∧
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) owner
          (quittingPureTimeBehaviorStrategy reward owner none)) owner =
      quittingContinuationBestResponseValue reward (quittingStationaryProfile reward root) owner ∧
    witness.terminalGap ≤ quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) owner
          (quittingPureTimeBehaviorStrategy reward owner none)) owner -
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) owner := by
  obtain ⟨delta, _, ⟨handoff⟩⟩ :=
    witness.exists_samePoint_stationaryHandoff_of_sure_exactNash tail root owner hsure hnash
  have hsource := quittingSingletonBaseStationaryProfile_rootFreeMixedPoint_eq
    reward root owner hsure
  have hrepair := quittingSingletonBaseRepairedProfile_rootFreeMixedPoint_eq_update
    reward root owner hsure
  have hroot := quittingPersistentBaseRoot_rootFreeMixedPoint_eq root owner hsure
  refine ⟨?_, ?_, ?_⟩
  · intro other hne
    have h := (handoff.source_free_semantics other (by simp [hne])).1
    rw [hsource, hroot] at h
    rw [quittingTerminalDeviationDebt, quittingCompleteCap_stationary_eq_unilateralCap, ← h]
    exact sub_self _
  · have h := handoff.repaired_owner_payoff_eq_source_cap
    rw [hrepair, hroot] at h
    rw [quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
      quittingCompleteCap_stationary_eq_unilateralCap]
    exact h
  · have h := handoff.terminalGap_le_ownerNeverGain witness
    rw [hsource, hrepair] at h
    simpa only [quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue] using h

/-- Actual stationary source data before any new root is chosen. -/
structure StationaryQuitNowCapPinSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  tailRoot : ℕ → ι → PMF Bool
  player : ι
  gamma : ℝ
  bound : ℝ
  gamma_pos : 0 < gamma
  bound_pos : 0 < bound
  reward_bound : ∀ terminal who, |reward terminal who| ≤ bound
  pin : ∀ᶠ index in atTop,
    gamma ≤ quittingTerminalDeviationDebt reward
      (quittingStationaryProfile reward (tailRoot index)) player ∧
    quittingTerminalPayoff reward
      (Function.update (quittingStationaryProfile reward (tailRoot index)) player
        (quittingPureTimeBehaviorStrategy reward player (some 0))) player =
      quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward (tailRoot index)) player
  cap_limit : Tendsto (fun index ↦ quittingContinuationBestResponseValue reward
    (quittingStationaryProfile reward (tailRoot index)) player) atTop
    (nhds (reward (quittingSingletonTerminal player) player))

namespace StationaryQuitNowCapPinSource

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

def profile (source : StationaryQuitNowCapPinSource reward) (index : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (source.tailRoot index)

def pair (source : StationaryQuitNowCapPinSource reward) (index : ℕ) :
    QuittingTerminalSemanticPair ι := quittingTerminalSemanticPair reward (source.profile index)

def absorptionFloor (source : StationaryQuitNowCapPinSource reward) : ℝ :=
  min 1 (source.gamma / (16 * source.bound))

def debtDrop (source : StationaryQuitNowCapPinSource reward) : ℝ :=
  min (source.gamma / 2) (source.gamma ^ 2 / (16 * source.bound))

theorem absorptionFloor_pos (source : StationaryQuitNowCapPinSource reward) :
    0 < source.absorptionFloor := by
  exact lt_min (by norm_num) (div_pos source.gamma_pos (by nlinarith [source.bound_pos]))

theorem debtDrop_pos (source : StationaryQuitNowCapPinSource reward) : 0 < source.debtDrop := by
  exact fixedCapPinDebtDropBound_pos source.bound_pos source.gamma_pos

/-- Both strict expenditures hold eventually and uniformly over every
exact root at the literal prescribed payoff of the same source. -/
theorem eventually_all_exactRoot_bounds (source : StationaryQuitNowCapPinSource reward) :
    ∀ᶠ index in atTop, ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward (source.pair index).1 0 root →
      source.absorptionFloor ≤ quittingRootAbsorptionMass root ∧
      source.debtDrop ≤ quittingTerminalSemanticDebt (source.pair index) source.player -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root (source.pair index)) source.player ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root (source.pair index)) ≤
        quittingTerminalSemanticDebtSum (source.pair index) - source.debtDrop := by
  have hnear : ∀ᶠ index in atTop, |(source.pair index).2 source.player -
      reward (quittingSingletonTerminal source.player) source.player| ≤ source.gamma / 4 := by
    exact source.cap_limit.eventually (by
      filter_upwards [Metric.closedBall_mem_nhds
        (reward (quittingSingletonTerminal source.player) source.player)
        (div_pos source.gamma_pos (by norm_num : (0 : ℝ) < 4))] with value hvalue
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hvalue)
  filter_upwards [source.pin, hnear] with index hpin hnear
  intro root hnash
  have hvalue := abs_quittingTerminalPayoff_le reward (source.profile index)
    source.player source.reward_bound
  have hnneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt (source.pair index) who :=
    fun who ↦ quittingTerminalDeviationDebt_nonneg reward (source.profile index) who
  refine ⟨fixedCapPin_exactRoot_absorptionMass_lowerBound reward (source.pair index) root
    source.player source.bound_pos source.gamma_pos source.reward_bound hvalue hpin.1 hnear hnash,
    fixedCapPin_coordinateDebtDrop reward (source.pair index) root source.player
      source.bound_pos source.gamma_pos source.reward_bound hvalue hpin.1 hnear hnash, ?_⟩
  have htotal := fixedCapPin_totalDebtDrop reward (source.pair index) root source.player
    source.bound_pos source.gamma_pos source.reward_bound hvalue hnneg hpin.1 hnear hnash
  change source.debtDrop ≤ _ at htotal
  linarith

end StationaryQuitNowCapPinSource

/-- One common selector for the actual source pairs and selected product
roots, with exact Nash passed to their common limit. -/
structure FirstStationaryRootLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : StationaryQuitNowCapPinSource reward) (root : ℕ → ι → PMF Bool) where
  select : ℕ → ℕ
  strictMono : StrictMono select
  sourceLimit : QuittingTerminalSemanticPair ι
  rootLimit : ι → PMF Bool
  source_tendsto : Tendsto (source.pair ∘ select) atTop (nhds sourceLimit)
  root_tendsto : Tendsto (fun index ↦ quittingSimplexOfRoot (root (select index)))
    atTop (nhds (quittingSimplexOfRoot rootLimit))
  source_mem : sourceLimit ∈ quittingTerminalSemanticCarrier reward
  exactNash : IsεQuittingRootNash reward sourceLimit.1 0 rootLimit

private theorem exists_firstStationaryRootLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : StationaryQuitNowCapPinSource reward) (root : ℕ → ι → PMF Bool)
    (hnash : ∀ index, IsεQuittingRootNash reward (source.pair index).1 0 (root index)) :
    Nonempty (FirstStationaryRootLimit source root) := by
  let data := fun index ↦ (quittingSimplexOfRoot (root index), source.pair index)
  have hdata : ∀ index, data index ∈
      (Set.univ : Set (QuittingRootSimplex ι)) ×ˢ quittingTerminalSemanticCarrier reward :=
    fun index ↦ ⟨Set.mem_univ _, subset_closure (Set.mem_range_self (source.profile index))⟩
  obtain ⟨limit, hmem, select, hmono, hlimit⟩ :=
    (isCompact_univ.prod (quittingTerminalSemanticCarrier_isCompact reward)).tendsto_subseq hdata
  let limitRoot := quittingRootOfSimplex limit.1
  have hsource := (continuous_snd.tendsto limit).comp hlimit
  have hroot := (continuous_fst.tendsto limit).comp hlimit
  have hnashLimit : IsεQuittingRootNash reward limit.2.1 0 limitRoot := by
    rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
    apply (isClosed_isZeroQuittingRootEndpointNash_simplex reward).mem_of_tendsto
      (continuous_snd.fst.tendsto limit |>.prodMk_nhds
        (continuous_fst.tendsto limit) |>.comp hlimit)
    filter_upwards [] with index
    simpa [data] using (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward
      (source.pair (select index)).1 (root (select index))).2 (hnash (select index))
  refine ⟨⟨select, hmono, limit.2, limitRoot, hsource, ?_, hmem.2, hnashLimit⟩⟩
  simpa [data, limitRoot, Function.comp_def] using hroot

/-- The positive-reach branch retains an executable copied-root Quit-now
response. It is not claimed to attain the new complete cap. -/
structure FirstStationaryRootPositiveBranch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : StationaryQuitNowCapPinSource reward) (root : ℕ → ι → PMF Bool)
    extends FirstStationaryRootLimit source root where
  reach : ℝ
  reach_pos : 0 < reach
  paid : ∀ᶠ index in atTop,
    reach ≤ quittingStationaryContinueMass (root (select index)) ∧
    quittingStationaryContinueMass (root (select index)) ≤ 1 - source.absorptionFloor ∧
    let profile := quittingRootThenContinuationProfile reward (root (select index))
      (source.profile (select index))
    let response := quittingRootAndContinuationDeviation reward (root (select index) source.player)
      (quittingPureTimeBehaviorStrategy reward source.player (some 0))
    let gain := quittingTerminalPayoff reward (Function.update profile source.player response)
      source.player - quittingTerminalPayoff reward profile source.player
    gain = quittingStationaryContinueMass (root (select index)) *
      quittingTerminalDeviationDebt reward (source.profile (select index)) source.player ∧
    reach * source.gamma ≤ gain ∧
    reach * source.gamma ≤ quittingTerminalDeviationDebt reward profile source.player

/-- The zero-reach branch distinguishes its actual finite prefixed sources
and shifted cap responses from the stationary repetition of the limiting root. -/
structure FirstStationaryRootZeroBranch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : StationaryQuitNowCapPinSource reward) (root : ℕ → ι → PMF Bool)
    (minimum gap : ℝ) extends FirstStationaryRootLimit source root where
  survival_zero : Tendsto (fun index ↦ quittingStationaryContinueMass (root (select index)))
    atTop (nhds 0)
  owner : ι
  owner_sure : rootLimit owner = PMF.pure true
  owner_unique : ∀ other, other ≠ owner → rootLimit other ≠ PMF.pure true
  outsider_debt_zero : ∀ other, other ≠ owner → Tendsto (fun index ↦
    quittingTerminalDeviationDebt reward (quittingRootThenContinuationProfile reward
      (root (select index)) (source.profile (select index))) other) atTop (nhds 0)
  owner_debt_floor : ∀ᶠ index in atTop, minimum / 2 ≤
    quittingTerminalDeviationDebt reward (quittingRootThenContinuationProfile reward
      (root (select index)) (source.profile (select index))) owner
  endpoint : Option ℕ
  endpoint_kind : endpoint = none ∨ endpoint = some 0
  tail_cap : ∀ index, quittingTerminalPayoff reward
    (Function.update (source.profile (select index)) owner
      (quittingPureTimeBehaviorStrategy reward owner endpoint)) owner =
    quittingContinuationBestResponseValue reward (source.profile (select index)) owner
  opponent_reach_pos : 0 < quittingRootOpponentContinueMass rootLimit owner
  opponent_reach_tendsto : Tendsto (fun index ↦
    quittingRootOpponentContinueMass (root (select index)) owner) atTop
    (nhds (quittingRootOpponentContinueMass rootLimit owner))
  finite_cap : ∀ᶠ index in atTop,
    quittingRootOpponentContinueMass rootLimit owner / 2 ≤
      quittingRootOpponentContinueMass (root (select index)) owner ∧
    quittingTerminalPayoff reward
      (Function.update (quittingRootThenContinuationProfile reward
        (root (select index)) (source.profile (select index))) owner
        (quittingPureTimeBehaviorStrategy reward owner (endpoint.map Nat.succ))) owner =
      quittingContinuationBestResponseValue reward (quittingRootThenContinuationProfile reward
        (root (select index)) (source.profile (select index))) owner
  stationary_outsider_debt : ∀ other, other ≠ owner →
    quittingTerminalDeviationDebt reward (quittingStationaryProfile reward rootLimit) other = 0
  stationary_never_cap : quittingTerminalPayoff reward
    (Function.update (quittingStationaryProfile reward rootLimit) owner
      (quittingPureTimeBehaviorStrategy reward owner none)) owner =
    quittingContinuationBestResponseValue reward (quittingStationaryProfile reward rootLimit) owner
  stationary_never_gain : gap ≤ quittingTerminalPayoff reward
    (Function.update (quittingStationaryProfile reward rootLimit) owner
      (quittingPureTimeBehaviorStrategy reward owner none)) owner -
    quittingTerminalPayoff reward (quittingStationaryProfile reward rootLimit) owner

private theorem positiveBranch_of_commonLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : StationaryQuitNowCapPinSource reward} {root : ℕ → ι → PMF Bool}
    (limit : FirstStationaryRootLimit source root)
    (hnash : ∀ index, IsεQuittingRootNash reward (source.pair index).1 0 (root index))
    (hpositive : 0 < quittingStationaryContinueMass limit.rootLimit) :
    Nonempty (FirstStationaryRootPositiveBranch source root) := by
  have hsurvival : Tendsto (fun index ↦ quittingStationaryContinueMass (root (limit.select index)))
      atTop (nhds (quittingStationaryContinueMass limit.rootLimit)) := by
    simpa [Function.comp_def] using (continuous_quittingStationaryContinueMass_simplex.tendsto
      (quittingSimplexOfRoot limit.rootLimit)).comp limit.root_tendsto
  let reach := quittingStationaryContinueMass limit.rootLimit / 2
  have hreach : 0 < reach := half_pos hpositive
  have hreachEvent : ∀ᶠ index in atTop,
      reach ≤ quittingStationaryContinueMass (root (limit.select index)) := by
    exact (hsurvival.eventually (lt_mem_nhds (by dsimp [reach]; linarith))).mono fun _ h ↦ h.le
  refine ⟨{ toFirstStationaryRootLimit := limit, reach := reach, reach_pos := hreach, paid := ?_ }⟩
  filter_upwards [hreachEvent, limit.strictMono.tendsto_atTop.eventually source.pin,
    limit.strictMono.tendsto_atTop.eventually source.eventually_all_exactRoot_bounds]
    with index hreachIndex hpin hbounds
  have habs := (hbounds (root (limit.select index)) (hnash (limit.select index))).1
  have hupper : quittingStationaryContinueMass (root (limit.select index)) ≤
      1 - source.absorptionFloor := by
    unfold quittingRootAbsorptionMass at habs
    linarith
  refine ⟨hreachIndex, hupper, ?_⟩
  dsimp only
  have heq := copiedRootAttachedTailCapDeviation_gain_eq reward (root (limit.select index))
    (source.profile (limit.select index)) source.player
    (quittingPureTimeBehaviorStrategy reward source.player (some 0)) hpin.2
  have hgain := copiedRootAttachedTailDeviation_gain_ge reward (root (limit.select index))
    (source.profile (limit.select index)) source.player
    (quittingPureTimeBehaviorStrategy reward source.player (some 0)) hreachIndex
    (by dsimp only [StationaryQuitNowCapPinSource.profile]
        rw [hpin.2]
        exact hpin.1) source.gamma_pos.le
  refine ⟨heq, hgain, ?_⟩
  have hcap := quittingTerminalPayoff_update_le_continuationBestResponseValue reward
    (quittingRootThenContinuationProfile reward (root (limit.select index))
      (source.profile (limit.select index))) source.player
    (quittingRootAndContinuationDeviation reward (root (limit.select index) source.player)
      (quittingPureTimeBehaviorStrategy reward source.player (some 0)))
  unfold quittingTerminalDeviationDebt
  linarith

private theorem zeroBranch_of_survival_subsequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : StationaryQuitNowCapPinSource reward) (root : ℕ → ι → PMF Bool)
    (witness : QuittingTerminalExploitabilityWitness reward)
    {minimum : ℝ} (hminimumPos : 0 < minimum)
    (hminimum : ∀ profile : (quittingGame reward).BehaviorProfile,
      minimum ≤ quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile))
    (hnash : ∀ index, IsεQuittingRootNash reward (source.pair index).1 0 (root index))
    (start : ℕ → ℕ) (hstart : StrictMono start)
    (hzero : Tendsto (fun index ↦ quittingStationaryContinueMass (root (start index)))
      atTop (nhds 0)) :
    Nonempty (FirstStationaryRootZeroBranch source root minimum witness.terminalGap) := by
  have htotal : ∀ index, minimum ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPrefix reward (root (start index)) (source.pair (start index))) := by
    intro index
    unfold StationaryQuitNowCapPinSource.pair
    rw [← quittingTerminalSemanticPair_rootThenContinuation]
    exact hminimum _
  obtain ⟨limitSource, limitRoot, select, hselect, hsourceLimit, hrootLimit, hsourceMem,
      hnashLimit, _, owner, howner, hunique, houtside, hownerDebt⟩ :=
    exists_uniqueSureLimit_of_firstExactRoots reward (source.pair ∘ start) (root ∘ start)
      hminimumPos (fun index ↦ subset_closure (Set.mem_range_self (source.profile (start index))))
      (fun index ↦ hnash (start index)) htotal hzero
  let base := start ∘ select
  have hbaseMono : StrictMono base := hstart.comp hselect
  have hbaseRoot : Tendsto (fun index ↦ quittingSimplexOfRoot (root (base index)))
      atTop (nhds (quittingSimplexOfRoot limitRoot)) := hrootLimit
  choose choice hkind hcap using fun index ↦ exists_stationary_quitNow_or_never_completeCap
    reward (source.tailRoot (base index)) owner
  have hbaseNash : ∀ index, IsεQuittingRootNash reward
      (fun player ↦ quittingTerminalPayoff reward (source.profile (base index)) player)
      0 (root (base index)) := fun index ↦ hnash (base index)
  simp only [Function.comp_apply, StationaryQuitNowCapPinSource.pair,
    ← quittingTerminalSemanticPair_rootThenContinuation] at houtside hownerDebt
  obtain ⟨fixed, hfixed, final, hfinal, hchoiceFixed, hfinalRoot, hfinalOutside,
      hfinalFloor, hreachPos, hreachLimit, hfinite⟩ :=
    exists_fixed_shiftedCap_subsequence_of_uniqueSureLimit reward (root ∘ base)
      (source.profile ∘ base) limitRoot owner choice hbaseRoot howner hunique hbaseNash
      hcap hkind hownerDebt (half_pos hminimumPos) houtside
  obtain ⟨hresetOutside, hresetCap, hresetGain⟩ :=
    stationaryNeverReset_of_sure_exactRoot witness limitSource.1 limitRoot owner howner hnashLimit
  refine ⟨{
    select := base ∘ final
    strictMono := hbaseMono.comp hfinal
    sourceLimit := limitSource
    rootLimit := limitRoot
    source_tendsto := hsourceLimit.comp hfinal.tendsto_atTop
    root_tendsto := hfinalRoot
    source_mem := hsourceMem
    exactNash := hnashLimit
    survival_zero := hzero.comp (hselect.comp hfinal).tendsto_atTop
    owner := owner
    owner_sure := howner
    owner_unique := hunique
    outsider_debt_zero := hfinalOutside
    owner_debt_floor := hfinalFloor
    endpoint := fixed
    endpoint_kind := hfixed
    tail_cap := ?_
    opponent_reach_pos := hreachPos
    opponent_reach_tendsto := hreachLimit
    finite_cap := ?_
    stationary_outsider_debt := hresetOutside
    stationary_never_cap := hresetCap
    stationary_never_gain := hresetGain
  }⟩
  · intro index
    simpa only [Function.comp_apply, StationaryQuitNowCapPinSource.profile,
      ← hchoiceFixed index] using hcap (final index)
  · filter_upwards [hfinite] with index hindex
    simpa only [Function.comp_apply, hchoiceFixed index] using hindex

/-- Source-facing assembly. The minimizer, fixed terminal gap, common limit,
survival branch, and executable responses are all produced from one source
and the caller's arbitrary exact-root selection. -/
structure FirstStationaryRootDichotomy
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : StationaryQuitNowCapPinSource reward) (root : ℕ → ι → PMF Bool) where
  minimum : QuittingTerminalSemanticPair ι
  minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward
  minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum
  minimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤ quittingTerminalSemanticDebtSum candidate
  witness : QuittingTerminalExploitabilityWitness reward
  prefix_floor : ∀ index, quittingTerminalSemanticDebtSum minimum ≤
    quittingTerminalSemanticDebtSum (quittingTerminalSemanticPrefix reward
      (root index) (source.pair index))
  uniform_expenditure : ∀ᶠ index in atTop, ∀ candidateRoot : ι → PMF Bool,
    IsεQuittingRootNash reward (source.pair index).1 0 candidateRoot →
    source.absorptionFloor ≤ quittingRootAbsorptionMass candidateRoot ∧
    source.debtDrop ≤ quittingTerminalSemanticDebt (source.pair index) source.player -
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward candidateRoot (source.pair index)) source.player ∧
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward candidateRoot (source.pair index)) ≤
      quittingTerminalSemanticDebtSum (source.pair index) - source.debtDrop
  branch : Nonempty (FirstStationaryRootPositiveBranch source root) ∨
    Nonempty (FirstStationaryRootZeroBranch source root
      (quittingTerminalSemanticDebtSum minimum) witness.terminalGap)

/-- Every exact-root selection at the actual stationary cap-pinned source
has the delayed paid-fork or unique-sure stationary Never-reset alternative.
No stationary-interiority hypothesis or independently selected cap is needed. -/
theorem StationaryQuitNowCapPinSource.firstExactRoot_dichotomy
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : StationaryQuitNowCapPinSource reward)
    (hno : ¬ ∃ payoff : Payoff ι, (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (root : ℕ → ι → PMF Bool)
    (hnash : ∀ index, IsεQuittingRootNash reward (source.pair index).1 0 (root index)) :
    Nonempty (FirstStationaryRootDichotomy source root) := by
  letI : Nonempty ι := ⟨source.player⟩
  obtain ⟨minimum, _, hminimumMem, _, hminimum, ⟨player, hplayer⟩, _⟩ :=
    exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff reward hno
  have hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum :=
    hplayer.trans_le (Finset.single_le_sum (fun who _ ↦
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hminimumMem who)
        (Finset.mem_univ player))
  obtain ⟨witness⟩ :=
    nonempty_terminalExploitabilityWitness_of_not_exists_uniformEquilibriumPayoff reward hno
  have hactualMin : ∀ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) :=
    fun profile ↦ hminimum _ (subset_closure (Set.mem_range_self profile))
  refine ⟨{
    minimum := minimum
    minimum_mem := hminimumMem
    minimum_pos := hminimumPos
    minimum_le := hminimum
    witness := witness
    prefix_floor := ?_
    uniform_expenditure := source.eventually_all_exactRoot_bounds
    branch := ?_
  }⟩
  · intro index
    unfold StationaryQuitNowCapPinSource.pair
    rw [← quittingTerminalSemanticPair_rootThenContinuation]
    exact hactualMin _
  · obtain ⟨limit⟩ := exists_firstStationaryRootLimit source root hnash
    by_cases hzero : quittingStationaryContinueMass limit.rootLimit = 0
    · right
      have hsurvival : Tendsto
          (fun index ↦ quittingStationaryContinueMass (root (limit.select index)))
          atTop (nhds 0) := by
        have h := (continuous_quittingStationaryContinueMass_simplex.tendsto
          (quittingSimplexOfRoot limit.rootLimit)).comp limit.root_tendsto
        simpa [hzero, Function.comp_def] using h
      exact zeroBranch_of_survival_subsequence source root witness hminimumPos hactualMin
        hnash limit.select limit.strictMono hsurvival
    · left
      exact positiveBranch_of_commonLimit limit hnash
        (lt_of_le_of_ne (quittingStationaryContinueMass_nonneg limit.rootLimit) (Ne.symm hzero))

end GameTheory
