/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FiniteClockPolynomialCenter
import Research.Quitting.FiniteClockTerminalSemantics
import UniformEquilibrium.Diagnostics.Quitting.PureTimeDeadlineSemantics
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap
import Mathlib.Topology.Connected.Clopen

/-!
# A finite-clock double full-gap co-source

A positive unrestricted terminal exploitability gap forces two distinct
full-gap debtors at one literal finite-clock behavioral source.  The proof
uses the connected one-date semantic center.  At all-Never, some player has a
positive singleton response.  Moving that player to Sure Quit stays in the
one-date center and makes its own unrestricted debt exactly zero.  A finite
closed debt cover of the connected center must therefore overlap.

This replaces the longer density/watchdog route in the source packet by a
strictly local connectedness argument.  It does not assert any chronology,
Nash--Bellman spine, or compatibility between the two returned responses.
-/

noncomputable section

namespace GameTheory

open Function Set
open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal finite-clock source with two distinct full-gap debtors.  The two
displayed pure date-or-Never candidates attain their respective unrestricted
behavioral caps. -/
structure QuittingFiniteClockDoubleFullGapCosource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ) where
  clockBound : ℕ
  clockBound_pos : 0 < clockBound
  weight : ι → FiniteClockAtom clockBound → ℝ
  weight_simplex : ∀ player,
    weight player ∈ stdSimplex ℝ (FiniteClockAtom clockBound)
  auxiliary_eq_zero : ∀ player,
    weight player (finiteClockAuxAtom clockBound) = 0
  first : ι
  second : ι
  distinct : first ≠ second
  firstCandidate : FiniteClockAtom clockBound
  secondCandidate : FiniteClockAtom clockBound
  first_attains_cap :
    quittingTerminalPayoff reward
        (Function.update
          (finiteClockDecodedProfile reward clockBound weight weight_simplex)
          first
          (quittingPureTimeBehaviorStrategy reward first
            (finiteClockAtomToStoppingTime clockBound firstCandidate))) first =
      quittingContinuationBestResponseValue reward
        (finiteClockDecodedProfile reward clockBound weight weight_simplex)
        first
  second_attains_cap :
    quittingTerminalPayoff reward
        (Function.update
          (finiteClockDecodedProfile reward clockBound weight weight_simplex)
          second
          (quittingPureTimeBehaviorStrategy reward second
            (finiteClockAtomToStoppingTime clockBound secondCandidate))) second =
      quittingContinuationBestResponseValue reward
        (finiteClockDecodedProfile reward clockBound weight weight_simplex)
        second
  first_gain :
    quittingTerminalPayoff reward
          (finiteClockDecodedProfile reward clockBound weight weight_simplex)
          first + gap ≤
      quittingTerminalPayoff reward
        (Function.update
          (finiteClockDecodedProfile reward clockBound weight weight_simplex)
          first
          (quittingPureTimeBehaviorStrategy reward first
            (finiteClockAtomToStoppingTime clockBound firstCandidate))) first
  second_gain :
    quittingTerminalPayoff reward
          (finiteClockDecodedProfile reward clockBound weight weight_simplex)
          second + gap ≤
      quittingTerminalPayoff reward
        (Function.update
          (finiteClockDecodedProfile reward clockBound weight weight_simplex)
          second
          (quittingPureTimeBehaviorStrategy reward second
            (finiteClockAtomToStoppingTime clockBound secondCandidate))) second

namespace QuittingFiniteClockDoubleFullGapCosource

/-- The actual behavioral profile decoded from the source marginals. -/
def sourceProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {gap : ℝ}
    (source : QuittingFiniteClockDoubleFullGapCosource reward gap) :
    (quittingGame reward).BehaviorProfile :=
  finiteClockDecodedProfile reward source.clockBound source.weight
    source.weight_simplex

/-- Every source marginal is supported strictly before the displayed clock
bound, with the Never atom retained literally. -/
theorem sourceStoppingLaw_isFiniteClock
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {gap : ℝ}
    (source : QuittingFiniteClockDoubleFullGapCosource reward gap)
    (player : ι) :
    IsFiniteClockStoppingLaw source.clockBound
      (finiteClockDecodedLaws source.clockBound source.weight
        source.weight_simplex player) := by
  exact finiteClockDecodeLaw_support source.clockBound
    (source.weight player) (source.weight_simplex player)
    (source.auxiliary_eq_zero player)

/-- Both returned players have their full unrestricted semantic debt at least
the displayed gap. -/
theorem debts
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {gap : ℝ}
    (source : QuittingFiniteClockDoubleFullGapCosource reward gap) :
    gap ≤ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source.sourceProfile)
        source.first ∧
      gap ≤ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source.sourceProfile)
        source.second := by
  constructor
  · change gap ≤ quittingContinuationBestResponseValue reward
        (finiteClockDecodedProfile reward source.clockBound source.weight
          source.weight_simplex) source.first -
      quittingTerminalPayoff reward
        (finiteClockDecodedProfile reward source.clockBound source.weight
          source.weight_simplex) source.first
    rw [← source.first_attains_cap]
    linarith [source.first_gain]
  · change gap ≤ quittingContinuationBestResponseValue reward
        (finiteClockDecodedProfile reward source.clockBound source.weight
          source.weight_simplex) source.second -
      quittingTerminalPayoff reward
        (finiteClockDecodedProfile reward source.clockBound source.weight
          source.weight_simplex) source.second
    rw [← source.second_attains_cap]
    linarith [source.second_gain]

end QuittingFiniteClockDoubleFullGapCosource

/-- A positive global terminal gap forces some positive singleton reward at
the all-Never profile.  This is the exact SureQuit endpoint used below. -/
theorem HasTerminalExploitabilityGap.exists_singletonReward_ge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    ∃ player : ι,
      gap ≤ reward (quittingSingletonTerminal player) player := by
  obtain ⟨player, deviation, hgain⟩ :=
    hexploit (quittingAlwaysContinueProfile reward)
  have hpayoff : quittingTerminalPayoff reward
      (quittingAlwaysContinueProfile reward) player = 0 :=
    quittingTerminalPayoff_quittingAlwaysContinue reward player
  have hupper := quittingTerminalPayoff_update_quittingAlwaysContinue_le_max
    reward player deviation
  have hmax : gap ≤
      max 0 (reward (quittingSingletonTerminal player) player) := by
    linarith
  have hsingletonNonneg :
      0 ≤ reward (quittingSingletonTerminal player) player := by
    by_contra hnegative
    rw [max_eq_left (le_of_not_ge hnegative)] at hmax
    linarith
  exact ⟨player, by simpa [max_eq_right hsingletonNonneg] using hmax⟩

private def quittingClockOneSureQuitTimes (player : ι) : ι → Option ℕ :=
  Function.update (fun _ ↦ none) player (some 0)

private def quittingClockOneSureQuitRoot (player : ι) :
    QuittingRootSimplex ι :=
  quittingSimplexOfRoot
    (Function.update quittingAllContinueRoot player (PMF.pure true))

private def quittingClockOneSureQuitWord (player : ι) :
    Fin 1 → QuittingRootSimplex ι :=
  fun _ ↦ quittingClockOneSureQuitRoot player

private def quittingClockOneAllContinueWord :
    Fin 1 → QuittingRootSimplex ι :=
  fun _ ↦ quittingSimplexOfRoot quittingAllContinueRoot

omit [DecidableEq ι] in
private theorem quittingFiniteClockWordProfile_clockOneAllContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingFiniteClockWordProfile reward 1
        (quittingClockOneAllContinueWord (ι := ι)) =
      quittingAlwaysContinueProfile reward := by
  funext player time history
  by_cases htime : time < 1
  · have hzero : time = 0 := by omega
    subst time
    simp [quittingFiniteClockWordProfile, quittingRootSequenceProfile,
      quittingFiniteClockRoots, quittingClockOneAllContinueWord,
      quittingAlwaysContinueProfile,
      StochasticGame.stationaryBehaviorProfile, quittingAllContinueRoot] ;
      rfl
  · simp [quittingFiniteClockWordProfile, quittingRootSequenceProfile,
      quittingFiniteClockRoots, htime, quittingAlwaysContinueProfile,
      StochasticGame.stationaryBehaviorProfile, quittingAllContinueRoot] ;
      rfl

private theorem quittingFiniteClockWordProfile_clockOneSureQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) :
    quittingFiniteClockWordProfile reward 1
        (quittingClockOneSureQuitWord player) =
      quittingPureTimeProfileBehavior reward
        (quittingClockOneSureQuitTimes player) := by
  funext who time history
  by_cases htime : time < 1
  · have hzero : time = 0 := by omega
    subst time
    by_cases hwho : who = player
    · subst who
      simp [quittingFiniteClockWordProfile, quittingRootSequenceProfile,
        quittingFiniteClockRoots, quittingClockOneSureQuitWord,
        quittingClockOneSureQuitRoot, quittingClockOneSureQuitTimes,
        quittingPureTimeProfileBehavior, quittingPureTimeBehaviorStrategy,
        quittingPureTimeHazard]
    · simp [quittingFiniteClockWordProfile, quittingRootSequenceProfile,
        quittingFiniteClockRoots, quittingClockOneSureQuitWord,
        quittingClockOneSureQuitRoot, quittingClockOneSureQuitTimes,
        quittingPureTimeProfileBehavior, quittingPureTimeBehaviorStrategy,
        quittingPureTimeHazard, hwho, quittingAllContinueRoot]
  · have htimeZero : time ≠ 0 := by omega
    by_cases hwho : who = player
    · subst who
      simp [quittingFiniteClockWordProfile, quittingRootSequenceProfile,
        quittingFiniteClockRoots, htime, quittingClockOneSureQuitTimes,
        quittingPureTimeProfileBehavior, quittingPureTimeBehaviorStrategy,
        quittingPureTimeHazard, htimeZero, quittingAllContinueRoot]
    · simp [quittingFiniteClockWordProfile, quittingRootSequenceProfile,
        quittingFiniteClockRoots, htime, quittingClockOneSureQuitTimes,
        quittingPureTimeProfileBehavior, quittingPureTimeBehaviorStrategy,
        quittingPureTimeHazard, hwho, quittingAllContinueRoot]

private theorem quittingClockOneSureQuit_debt_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι)
    (hsingleton : 0 ≤ reward (quittingSingletonTerminal player) player) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingFiniteClockWordProfile reward 1
            (quittingClockOneSureQuitWord player))) player = 0 := by
  let times := quittingClockOneSureQuitTimes player
  have hcoalition : quittingPureTimeCoalitionAt times 0 = {player} := by
    ext who
    by_cases hwho : who = player
    · subst who
      simp [times, quittingClockOneSureQuitTimes,
        quittingPureTimeCoalitionAt]
    · simp [times, quittingClockOneSureQuitTimes,
        quittingPureTimeCoalitionAt, hwho]
  have hnonempty : (quittingPureTimeCoalitionAt times 0).Nonempty := by
    rw [hcoalition]
    simp
  have hpayoffVector := quittingTerminalPayoff_pureTimeProfileBehavior_eq
    reward times 0 (by omega) hnonempty
  have hpayoff : quittingTerminalPayoff reward
      (quittingPureTimeProfileBehavior reward times) player =
        reward (quittingSingletonTerminal player) player := by
    have := congrFun hpayoffVector player
    have hterminal :
        (⟨quittingPureTimeCoalitionAt times 0, hnonempty⟩ :
          {S : Finset ι // S.Nonempty}) =
          quittingSingletonTerminal player := by
      apply Subtype.ext
      exact hcoalition
    rw [hterminal] at this
    exact this
  have hprofile : quittingPureTimeProfileBehavior reward times =
      Function.update (quittingAlwaysContinueProfile reward) player
        (quittingPureTimeBehaviorStrategy reward player (some 0)) := by
    funext who time history
    by_cases hwho : who = player
    · subst who
      simp [times, quittingClockOneSureQuitTimes,
        quittingPureTimeProfileBehavior]
    · simp [times, quittingClockOneSureQuitTimes,
        quittingPureTimeProfileBehavior, quittingAlwaysContinueProfile,
        quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
        StochasticGame.stationaryBehaviorProfile, hwho] ;
        rfl
  have hcap : quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward times) player =
        reward (quittingSingletonTerminal player) player := by
    rw [hprofile, quittingContinuationBestResponseValue_update_self,
      quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
      max_eq_right hsingleton]
  rw [quittingFiniteClockWordProfile_clockOneSureQuit]
  change quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward times) player -
    quittingTerminalPayoff reward
      (quittingPureTimeProfileBehavior reward times) player = 0
  rw [hpayoff, hcap, sub_self]

/-- The connected one-date center contains a semantic pair with two distinct
unrestricted debts at least `gap`. -/
theorem exists_pair_mem_quittingFiniteClockSemanticReachable_one_and_two_debts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    ∃ pair ∈ quittingFiniteClockSemanticReachable reward 1,
      ∃ first second : ι,
        first ≠ second ∧
          gap ≤ quittingTerminalSemanticDebt pair first ∧
          gap ≤ quittingTerminalSemanticDebt pair second := by
  classical
  let carrier := quittingFiniteClockSemanticReachable reward 1
  let region : ι → Set (QuittingTerminalSemanticPair ι) :=
    fun player ↦ {pair | gap ≤ quittingTerminalSemanticDebt pair player}
  have hregionClosed : ∀ player, IsClosed (region player) := by
    intro player
    exact isClosed_le continuous_const
      (continuous_quittingTerminalSemanticDebt player)
  have hcover : carrier ⊆ ⋃ player, region player := by
    intro pair hpair
    rcases hpair with ⟨laws, hlaws, rfl⟩
    obtain ⟨player, deviation, hgain⟩ :=
      hexploit (quittingStoppingLawProfile reward laws)
    have hbest :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward (quittingStoppingLawProfile reward laws) player deviation
    exact Set.mem_iUnion.mpr ⟨player, by
      change gap ≤ quittingContinuationBestResponseValue reward
          (quittingStoppingLawProfile reward laws) player -
        quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward laws) player
      linarith⟩
  obtain ⟨anchor, hanchorSingleton⟩ :=
    hexploit.exists_singletonReward_ge hgap
  have hsingletonNonneg :
      0 ≤ reward (quittingSingletonTerminal anchor) anchor :=
    hgap.le.trans hanchorSingleton
  let allNeverPair := quittingTerminalSemanticPair reward
    (quittingAlwaysContinueProfile reward)
  let sureQuitPair := quittingTerminalSemanticPair reward
    (quittingFiniteClockWordProfile reward 1
      (quittingClockOneSureQuitWord anchor))
  have hallNeverMem : allNeverPair ∈ carrier := by
    rw [show carrier = quittingFiniteClockSemanticReachable reward 1 by rfl,
      quittingFiniteClockSemanticReachable_eq_range_fold]
    refine ⟨quittingClockOneAllContinueWord, ?_⟩
    rw [← quittingTerminalSemanticPair_finiteClockWordProfile_eq_fold,
      quittingFiniteClockWordProfile_clockOneAllContinue]
  have hallNeverRegion : allNeverPair ∈ region anchor := by
    change gap ≤ quittingContinuationBestResponseValue reward
        (quittingAlwaysContinueProfile reward) anchor -
      quittingTerminalPayoff reward
        (quittingAlwaysContinueProfile reward) anchor
    rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
      quittingTerminalPayoff_quittingAlwaysContinue,
      max_eq_right hsingletonNonneg]
    linarith
  have hsureQuitMem : sureQuitPair ∈ carrier := by
    rw [show carrier = quittingFiniteClockSemanticReachable reward 1 by rfl,
      quittingFiniteClockSemanticReachable_eq_range_fold]
    refine ⟨quittingClockOneSureQuitWord anchor, ?_⟩
    rw [← quittingTerminalSemanticPair_finiteClockWordProfile_eq_fold]
  have hsureQuitNotRegion : sureQuitPair ∉ region anchor := by
    change ¬gap ≤ quittingTerminalSemanticDebt sureQuitPair anchor
    rw [show quittingTerminalSemanticDebt sureQuitPair anchor = 0 by
      exact quittingClockOneSureQuit_debt_eq_zero reward anchor
        hsingletonNonneg]
    linarith
  by_contra hnoOverlap
  push Not at hnoOverlap
  let subtypeCarrier := {pair // pair ∈ carrier}
  let anchorRegion : Set subtypeCarrier :=
    {pair | pair.1 ∈ region anchor}
  have hanchorClosed : IsClosed anchorRegion := by
    exact (hregionClosed anchor).preimage continuous_subtype_val
  have hanchorOpen : IsOpen anchorRegion := by
    rw [← isClosed_compl_iff]
    let otherRegion : {player : ι // player ≠ anchor} →
        Set subtypeCarrier :=
      fun player ↦ {pair | pair.1 ∈ region player.1}
    have hcompl : anchorRegionᶜ = ⋃ player, otherRegion player := by
      ext pair
      constructor
      · intro hnotAnchor
        have hcovered := hcover pair.2
        rcases Set.mem_iUnion.mp hcovered with ⟨player, hplayer⟩
        have hne : player ≠ anchor := by
          intro heq
          subst player
          exact hnotAnchor hplayer
        exact Set.mem_iUnion.mpr ⟨⟨player, hne⟩, hplayer⟩
      · intro hother hanchor
        rcases Set.mem_iUnion.mp hother with ⟨player, hplayer⟩
        exact (not_lt_of_ge hplayer)
          (hnoOverlap pair.1 pair.2 anchor player.1 player.2.symm hanchor)
    rw [hcompl]
    exact isClosed_iUnion_of_finite fun player ↦
      (hregionClosed player.1).preimage continuous_subtype_val
  letI : ConnectedSpace subtypeCarrier :=
    Subtype.connectedSpace
      (quittingFiniteClockSemanticReachable_isConnected reward 1)
  have hanchorUniv : anchorRegion = Set.univ :=
    IsClopen.eq_univ ⟨hanchorClosed, hanchorOpen⟩
      ⟨⟨allNeverPair, hallNeverMem⟩, hallNeverRegion⟩
  have hsureAnchor :
      (⟨sureQuitPair, hsureQuitMem⟩ : subtypeCarrier) ∈ anchorRegion := by
    rw [hanchorUniv]
    trivial
  exact hsureQuitNotRegion hsureAnchor

/-- A positive global terminal gap produces a literal finite-clock source
with two distinct co-realized full debts and two cap-attaining pure
date-or-Never responses.  The construction in fact uses clock bound one. -/
theorem exists_quittingFiniteClockDoubleFullGapCosource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    Nonempty (QuittingFiniteClockDoubleFullGapCosource reward gap) := by
  classical
  obtain ⟨pair, hpair, first, second, hne, hfirst, hsecond⟩ :=
    exists_pair_mem_quittingFiniteClockSemanticReachable_one_and_two_debts
      reward hgap hexploit
  rcases hpair with ⟨laws, hlaws, hpairEq⟩
  let weight : ι → FiniteClockAtom 1 → ℝ := fun player ↦
    finiteClockLawCoordinates 1 (laws player)
  have hweight : ∀ player,
      weight player ∈ stdSimplex ℝ (FiniteClockAtom 1) := fun player ↦
    finiteClockLawCoordinates_mem_stdSimplex 1 (laws player)
  have haux : ∀ player,
      weight player (finiteClockAuxAtom 1) = 0 := fun player ↦
    finiteClockLawCoordinates_aux_eq_zero 1 (laws player) (hlaws player)
  have hdecoded : finiteClockDecodedProfile reward 1 weight hweight =
      quittingStoppingLawProfile reward laws := by
    unfold finiteClockDecodedProfile finiteClockDecodedLaws weight
    congr 1
    funext player
    exact finiteClockDecodeLaw_coordinates 1 (laws player) (hlaws player)
  obtain ⟨firstCandidate, hfirstCap⟩ :=
    exists_finiteClockCandidate_payoff_eq_continuationBestResponseValue
      reward 1 weight hweight haux first
  obtain ⟨secondCandidate, hsecondCap⟩ :=
    exists_finiteClockCandidate_payoff_eq_continuationBestResponseValue
      reward 1 weight hweight haux second
  refine ⟨{
    clockBound := 1
    clockBound_pos := by omega
    weight := weight
    weight_simplex := hweight
    auxiliary_eq_zero := haux
    first := first
    second := second
    distinct := hne
    firstCandidate := firstCandidate
    secondCandidate := secondCandidate
    first_attains_cap := hfirstCap
    second_attains_cap := hsecondCap
    first_gain := ?_
    second_gain := ?_ }⟩
  · rw [hfirstCap, hdecoded]
    rw [hpairEq] at hfirst
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair at hfirst
    linarith
  · rw [hsecondCap, hdecoded]
    rw [hpairEq] at hsecond
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair at hsecond
    linarith

/-- Failure of a uniform-equilibrium payoff supplies a positive gap and then
the corresponding finite-clock double full-gap co-source. -/
theorem exists_positive_quittingFiniteClockDoubleFullGapCosource_of_no_uniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ gap : ℝ, 0 < gap ∧
      Nonempty (QuittingFiniteClockDoubleFullGapCosource reward gap) := by
  obtain ⟨gap, hgap, hexploit⟩ :=
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).mp hno
  exact ⟨gap, hgap,
    exists_quittingFiniteClockDoubleFullGapCosource reward hgap hexploit⟩

end GameTheory
