/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FirstExactRootCompactification
import UniformEquilibrium.Quitting.Root.PureTimeCapPrefixSelection
import UniformEquilibrium.Quitting.Stationary.BestResponse
import UniformEquilibrium.Quitting.Stationary.CompleteBehavioralCap
import UniformEquilibrium.Quitting.Stationary.CompleteEndpointChoices

/-!
# Behavioral responses in the two first-root survival regimes

The positive-survival response copies the player's current root law and
changes only the attached tail strategy.  The vanishing-survival finite
response forces the limiting owner to Continue and then uses one of the two
stationary cap endpoints in the unchanged opponent tail.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Along a root subsequence converging to a unique-sure limit, the owner's
Quit probability tends to one and the probability that all opponents
Continue tends to a strictly positive value.  Hence both the owner's finite
Quit probability and half of the limiting opponent reach hold eventually. -/
theorem uniqueSureLimit_ownerQuit_and_opponentReach
    (root : ℕ → ι → PMF Bool) (limitRoot : ι → PMF Bool)
    (owner : ι)
    (hroot : Tendsto (fun index => quittingSimplexOfRoot (root index))
      atTop (nhds (quittingSimplexOfRoot limitRoot)))
    (howner : limitRoot owner = PMF.pure true)
    (hunique : ∀ other, other ≠ owner →
      limitRoot other ≠ PMF.pure true) :
    Tendsto (fun index => (root index owner true).toReal) atTop (nhds 1) ∧
      0 < quittingRootOpponentContinueMass limitRoot owner ∧
      Tendsto (fun index => quittingRootOpponentContinueMass (root index) owner)
        atTop (nhds (quittingRootOpponentContinueMass limitRoot owner)) ∧
      Filter.Eventually (fun index =>
        0 < (root index owner true).toReal ∧
          quittingRootOpponentContinueMass limitRoot owner / 2 ≤
            quittingRootOpponentContinueMass (root index) owner) atTop := by
  have hownerLimit : Tendsto (fun index => (root index owner true).toReal)
      atTop (nhds ((limitRoot owner true).toReal)) := by
    have h : Continuous (fun simplex : QuittingRootSimplex ι =>
        ((quittingRootOfSimplex simplex owner) true).toReal) := by
      simp only [quittingRootOfSimplex_apply_toReal]
      exact (continuous_apply true).comp
        (continuous_subtype_val.comp (continuous_apply owner))
    have ht := h.tendsto (quittingSimplexOfRoot limitRoot) |>.comp hroot
    change Tendsto (fun index =>
      ((quittingRootOfSimplex (quittingSimplexOfRoot (root index)) owner)
        true).toReal) atTop
      (nhds ((quittingRootOfSimplex (quittingSimplexOfRoot limitRoot) owner)
        true).toReal) at ht
    simpa only [quittingRootOfSimplex_simplexOfRoot] using ht
  have hownerOne : (limitRoot owner true).toReal = 1 := by simp [howner]
  have hownerTendsto : Tendsto (fun index => (root index owner true).toReal)
      atTop (nhds 1) := by simpa [hownerOne] using hownerLimit
  have hopponentPos : 0 < quittingRootOpponentContinueMass limitRoot owner := by
    unfold quittingRootOpponentContinueMass
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    apply Finset.prod_pos
    intro other _
    by_cases hne : other = owner
    · subst other
      simp
    · rw [Function.update_of_ne hne]
      have hnonneg : 0 ≤ (limitRoot other false).toReal := ENNReal.toReal_nonneg
      refine lt_of_le_of_ne hnonneg ?_
      intro hzero
      have hsum := quittingRoot_continueProbability_add_quitProbability limitRoot other
      have htrue : (limitRoot other true).toReal = 1 := by linarith
      exact hunique other hne
        (Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one _ htrue)
  have hcontinuous : Continuous (fun simplex : QuittingRootSimplex ι =>
      quittingRootOpponentContinueMass (quittingRootOfSimplex simplex) owner) := by
    unfold quittingRootOpponentContinueMass
    simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    apply continuous_finsetProd
    intro other _
    by_cases hne : other = owner
    · subst other
      simp
      exact continuous_const
    · simp only [Function.update_of_ne hne]
      have hother : Continuous (fun root : QuittingRootSimplex ι =>
          (root other : Bool → ℝ)) :=
        continuous_subtype_val.comp (continuous_apply other)
      apply Continuous.congr ((continuous_apply false).comp hother)
      intro simplex
      exact (quittingRootOfSimplex_apply_toReal simplex other false).symm
  have hopponentTendsto : Tendsto
      (fun index => quittingRootOpponentContinueMass (root index) owner) atTop
      (nhds (quittingRootOpponentContinueMass limitRoot owner)) := by
    have h := (hcontinuous.tendsto (quittingSimplexOfRoot limitRoot)).comp hroot
    change Tendsto (fun index => quittingRootOpponentContinueMass
      (quittingRootOfSimplex (quittingSimplexOfRoot (root index))) owner) atTop
      (nhds (quittingRootOpponentContinueMass
        (quittingRootOfSimplex (quittingSimplexOfRoot limitRoot)) owner)) at h
    simpa only [quittingRootOfSimplex_simplexOfRoot] using h
  refine ⟨hownerTendsto, hopponentPos, hopponentTendsto, ?_⟩
  filter_upwards
    [(tendsto_order.1 hownerTendsto).1 0 (by norm_num),
      (tendsto_order.1 hopponentTendsto).1
        (quittingRootOpponentContinueMass limitRoot owner / 2) (by linarith)]
    with index hquit hreach
  exact ⟨hquit, hreach.le⟩

/-- A positive joint-survival lower bound transports any fixed attached-tail
gain to the literal root-and-tail source with the product lower bound. -/
theorem copiedRootAttachedTailDeviation_gain_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (player : ι)
    (tailDeviation : (quittingGame reward).BehaviorStrategy player)
    {reach gain : ℝ}
    (hsurvival : reach ≤ quittingStationaryContinueMass root)
    (hgain : gain ≤ quittingTerminalPayoff reward
        (Function.update continuation player tailDeviation) player -
      quittingTerminalPayoff reward continuation player)
    (hgainNonneg : 0 ≤ gain) :
    reach * gain ≤
      quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            player
            (quittingRootAndContinuationDeviation reward (root player)
              tailDeviation)) player -
        quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward root continuation) player := by
  rw [quittingTerminalPayoff_copiedRootAttachedTailDeviation_sub_eq_continueMass_mul]
  calc
    reach * gain ≤ quittingStationaryContinueMass root * gain :=
      mul_le_mul_of_nonneg_right hsurvival hgainNonneg
    _ ≤ quittingStationaryContinueMass root *
        (quittingTerminalPayoff reward
            (Function.update continuation player tailDeviation) player -
          quittingTerminalPayoff reward continuation player) :=
      mul_le_mul_of_nonneg_left hgain
        (quittingStationaryContinueMass_nonneg root)

/-- When the attached-tail response attains the source cap, the copied-root
gain equals the source debt times joint survival. -/
theorem copiedRootAttachedTailCapDeviation_gain_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (player : ι)
    (tailDeviation : (quittingGame reward).BehaviorStrategy player)
    (hcap : quittingTerminalPayoff reward
        (Function.update continuation player tailDeviation) player =
      quittingContinuationBestResponseValue reward continuation player) :
    quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            player
            (quittingRootAndContinuationDeviation reward (root player)
              tailDeviation)) player -
        quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward root continuation) player =
      quittingStationaryContinueMass root *
        quittingTerminalDeviationDebt reward continuation player := by
  rw [quittingTerminalPayoff_copiedRootAttachedTailDeviation_sub_eq_continueMass_mul,
    hcap]
  rfl

/-- If a player has positive debt after an exact root and uses Quit with
positive probability at that root, a supplied pure-time suffix cap cannot
extend as immediate Quit.  Its shifted suffix time is the actual cap attainer
of the prefixed profile. -/
theorem shifted_pureTimeCap_attains_prefixCap_of_positiveDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (owner : ι) (choice : Option ℕ)
    (hchoice : quittingTerminalPayoff reward
        (Function.update continuation owner
          (quittingPureTimeBehaviorStrategy reward owner choice)) owner =
      quittingContinuationBestResponseValue reward continuation owner)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player)
      0 root)
    (hquit : 0 < (root owner true).toReal)
    (hdebt : 0 < quittingTerminalDeviationDebt reward
      (quittingRootThenContinuationProfile reward root continuation) owner) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingRootThenContinuationProfile reward root continuation)
          owner
          (quittingPureTimeBehaviorStrategy reward owner
            (choice.map Nat.succ))) owner =
      quittingContinuationBestResponseValue reward
        (quittingRootThenContinuationProfile reward root continuation) owner := by
  obtain ⟨nextChoice, hnext, hattains⟩ :=
    exists_pureTimeCap_zero_or_map_succ_of_suffixAttainer
      reward root continuation owner choice hchoice
  rcases hnext with hzero | hshift
  · subst nextChoice
    have hendpoint :=
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward
        (fun player => quittingTerminalPayoff reward continuation player) root).2
        hnash owner
    have hdiffNonneg : 0 ≤ quittingRootEndpointDifference reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root owner := by
      nlinarith [hendpoint.2]
    have hquitGe : quittingRootSuccessorPayoff reward
          (fun player => quittingTerminalPayoff reward continuation player)
          root owner ≤
        quittingRootQuitPayoff reward
          (fun player => quittingTerminalPayoff reward continuation player)
          root owner := by
      rw [quittingRootSuccessorPayoff_eq_endpointMix]
      have hfalse : 0 ≤ (root owner false).toReal := ENNReal.toReal_nonneg
      have hsum := quittingRoot_continueProbability_add_quitProbability root owner
      have hscaled := mul_nonneg hfalse hdiffNonneg
      unfold quittingRootEndpointDifference at hscaled
      have hmix :
          (root owner true).toReal *
                quittingRootQuitPayoff reward
                  (fun player => quittingTerminalPayoff reward continuation player)
                  root owner +
              (root owner false).toReal *
                quittingRootContinuePayoff reward
                  (fun player => quittingTerminalPayoff reward continuation player)
                  root owner =
            quittingRootQuitPayoff reward
                (fun player => quittingTerminalPayoff reward continuation player)
                root owner -
              (root owner false).toReal *
                (quittingRootQuitPayoff reward
                    (fun player => quittingTerminalPayoff reward continuation player)
                    root owner -
                  quittingRootContinuePayoff reward
                    (fun player => quittingTerminalPayoff reward continuation player)
                    root owner) := by
        linear_combination
          (quittingRootQuitPayoff reward
            (fun player => quittingTerminalPayoff reward continuation player)
            root owner) * hsum
      rw [hmix]
      linarith
    have hquitLe := quittingRootQuitPayoff_le_successor_of_isZeroNash
      reward (fun player => quittingTerminalPayoff reward continuation player)
        root owner hnash
    have hquitEq := le_antisymm hquitLe hquitGe
    have hsourcePayoff : quittingTerminalPayoff reward
        (quittingRootThenContinuationProfile reward root continuation) owner =
      quittingRootSuccessorPayoff reward
        (fun player => quittingTerminalPayoff reward continuation player)
          root owner := quittingTerminalPayoff_rootThenContinuation_eq
            reward root continuation owner
    have hquitPayoff := quittingTerminalPayoff_rootThen_pureTime_zero_eq_quitPayoff
      reward root continuation owner
    unfold quittingTerminalDeviationDebt at hdebt
    rw [← hattains, hquitPayoff, hquitEq, hsourcePayoff] at hdebt
    linarith
  · simpa [hshift] using hattains

/-- A sequence of stationary cap endpoints, each either `Never` or `Quit0`,
has a subsequence on which the literal endpoint is fixed. -/
theorem exists_fixed_quitNow_or_never_subsequence
    (choice : ℕ → Option ℕ)
    (hchoice : ∀ index, choice index = none ∨ choice index = some 0) :
    ∃ fixed : Option ℕ, (fixed = none ∨ fixed = some 0) ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        ∀ index, choice (subsequence index) = fixed := by
  let label : ℕ → Bool := fun index => choice index = none
  obtain ⟨selected, subsequence, hsubsequence, hselected⟩ :=
    exists_fixedPlayer_strictMono_subsequence label
  cases selected with
  | false =>
      refine ⟨some 0, Or.inr rfl, subsequence, hsubsequence, ?_⟩
      intro index
      have hnotNone : choice (subsequence index) ≠ none := by
        intro hnone
        have : label (subsequence index) = true := by simp [label, hnone]
        rw [hselected index] at this
        contradiction
      rcases hchoice (subsequence index) with hnone | hzero
      · exact (hnotNone hnone).elim
      · exact hzero
  | true =>
      refine ⟨none, Or.inl rfl, subsequence, hsubsequence, ?_⟩
      intro index
      have : label (subsequence index) = true := hselected index
      simpa [label] using this

/-- Arbitrary stationary opponents supply the two-valued cap
choices required by the finite unique-sure response, rather than requiring
those choices as additional source data. -/
theorem exists_stationary_quitNow_or_never_completeCapChoices
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ℕ → ι → PMF Bool) (owner : ι) :
    ∃ choice : ℕ → Option ℕ,
      (∀ index, choice index = none ∨ choice index = some 0) ∧
      ∀ index, quittingTerminalPayoff reward
          (Function.update (quittingStationaryProfile reward (root index)) owner
            (quittingPureTimeBehaviorStrategy reward owner (choice index))) owner =
        quittingContinuationBestResponseValue reward
          (quittingStationaryProfile reward (root index)) owner := by
  choose choice hkind hcap using fun index =>
    exists_stationary_quitNow_or_never_completeCap reward (root index) owner
  exact ⟨choice, hkind, hcap⟩

/-- On the same compact unique-sure chronology, finite exact cap responses
eventually pass through the new root and use the old stationary endpoint.
A further two-valued selection fixes that endpoint while preserving root
convergence, outsider concentration, the owner's debt floor, and opponent
tail reach. -/
theorem exists_fixed_shiftedCap_subsequence_of_uniqueSureLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ℕ → ι → PMF Bool)
    (continuation : ℕ → (quittingGame reward).BehaviorProfile)
    (limitRoot : ι → PMF Bool) (owner : ι)
    (choice : ℕ → Option ℕ) {floor : ℝ}
    (hroot : Tendsto (fun index => quittingSimplexOfRoot (root index))
      atTop (nhds (quittingSimplexOfRoot limitRoot)))
    (howner : limitRoot owner = PMF.pure true)
    (hunique : ∀ other, other ≠ owner →
      limitRoot other ≠ PMF.pure true)
    (hnash : ∀ index, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (continuation index) player)
      0 (root index))
    (hchoice : ∀ index, quittingTerminalPayoff reward
        (Function.update (continuation index) owner
          (quittingPureTimeBehaviorStrategy reward owner (choice index))) owner =
      quittingContinuationBestResponseValue reward (continuation index) owner)
    (hendpoint : ∀ index, choice index = none ∨ choice index = some 0)
    (hownerDebt : ∀ᶠ index in atTop, floor ≤
      quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward (root index)
          (continuation index)) owner)
    (hfloor : 0 < floor)
    (houtside : ∀ other, other ≠ owner → Tendsto (fun index =>
      quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward (root index)
          (continuation index)) other) atTop (nhds 0)) :
    ∃ fixed : Option ℕ, (fixed = none ∨ fixed = some 0) ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        (∀ index, choice (subsequence index) = fixed) ∧
        Tendsto (fun index => quittingSimplexOfRoot
          (root (subsequence index))) atTop
          (nhds (quittingSimplexOfRoot limitRoot)) ∧
        (∀ other, other ≠ owner → Tendsto (fun index =>
          quittingTerminalDeviationDebt reward
            (quittingRootThenContinuationProfile reward
              (root (subsequence index)) (continuation (subsequence index))) other)
          atTop (nhds 0)) ∧
        (∀ᶠ index in atTop, floor ≤
          quittingTerminalDeviationDebt reward
            (quittingRootThenContinuationProfile reward
              (root (subsequence index)) (continuation (subsequence index))) owner) ∧
        0 < quittingRootOpponentContinueMass limitRoot owner ∧
        Tendsto (fun index => quittingRootOpponentContinueMass
          (root (subsequence index)) owner) atTop
          (nhds (quittingRootOpponentContinueMass limitRoot owner)) ∧
        (∀ᶠ index in atTop,
          quittingRootOpponentContinueMass limitRoot owner / 2 ≤
            quittingRootOpponentContinueMass (root (subsequence index)) owner ∧
          quittingTerminalPayoff reward
              (Function.update
                (quittingRootThenContinuationProfile reward
                  (root (subsequence index)) (continuation (subsequence index)))
                owner
                (quittingPureTimeBehaviorStrategy reward owner
                  ((choice (subsequence index)).map Nat.succ))) owner =
            quittingContinuationBestResponseValue reward
              (quittingRootThenContinuationProfile reward
                (root (subsequence index)) (continuation (subsequence index)))
              owner) := by
  obtain ⟨hownerTendsto, hopponentPos, hopponentTendsto, heventualRoot⟩ :=
    uniqueSureLimit_ownerQuit_and_opponentReach root limitRoot owner hroot
      howner hunique
  have hpositiveDebt : ∀ᶠ index in atTop, 0 <
      quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward (root index)
          (continuation index)) owner :=
    hownerDebt.mono fun _ h => hfloor.trans_le h
  have hshifted : ∀ᶠ index in atTop,
      quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward (root index)
              (continuation index)) owner
            (quittingPureTimeBehaviorStrategy reward owner
              ((choice index).map Nat.succ))) owner =
        quittingContinuationBestResponseValue reward
          (quittingRootThenContinuationProfile reward (root index)
            (continuation index)) owner := by
    filter_upwards [heventualRoot, hpositiveDebt] with index hfinite hdebt
    exact shifted_pureTimeCap_attains_prefixCap_of_positiveDebt reward
      (root index) (continuation index) owner (choice index) (hchoice index)
      (hnash index) hfinite.1 hdebt
  obtain ⟨fixed, hfixed, subsequence, hsubsequence, hchoiceFixed⟩ :=
    exists_fixed_quitNow_or_never_subsequence choice hendpoint
  refine ⟨fixed, hfixed, subsequence, hsubsequence, hchoiceFixed,
    hroot.comp hsubsequence.tendsto_atTop, ?_,
    hsubsequence.tendsto_atTop.eventually hownerDebt, hopponentPos,
    hopponentTendsto.comp hsubsequence.tendsto_atTop, ?_⟩
  · intro other hne
    exact (houtside other hne).comp hsubsequence.tendsto_atTop
  · filter_upwards
      [hsubsequence.tendsto_atTop.eventually heventualRoot,
        hsubsequence.tendsto_atTop.eventually hshifted]
      with index hfinite hcap
    exact ⟨hfinite.2, hcap⟩

/-- At the unique-sure stationary source, every free coordinate already
attains its complete stationary cap.  The terminal exploitability witness is
therefore paid entirely by the owner's literal Always-Continue (`Never`)
repair. -/
theorem QuittingSingletonBaseStationaryHandoff.terminalGap_le_ownerNeverGain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {owner : ι}
    {point : mixedPolytope (quittingBinaryForm (Finset.univ.erase owner)).sig}
    {delta : ℝ}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (handoff : QuittingSingletonBaseStationaryHandoff reward owner
      (Finset.univ.erase owner) point delta witness.terminalGap) :
    witness.terminalGap ≤
      quittingTerminalPayoff reward
          (quittingSingletonBaseRepairedProfile reward owner
            (Finset.univ.erase owner) point) owner -
        quittingTerminalPayoff reward
          (quittingSingletonBaseStationaryProfile reward owner
            (Finset.univ.erase owner) point) owner := by
  let root := quittingPersistentBaseRoot {owner} (Finset.univ.erase owner) point
  obtain ⟨who, hwho⟩ := witness.exists_stationaryCap_gain root
  have hwhoOwner : who = owner := by
    by_contra hne
    have hfree : who ∈ Finset.univ.erase owner := by simp [hne]
    have hzero := (handoff.source_free_semantics who hfree).1
    change quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who =
      quittingStationaryUnilateralCap reward root who at hzero
    linarith [witness.terminalGap_pos]
  subst who
  rw [handoff.repaired_owner_payoff_eq_source_cap]
  change quittingTerminalPayoff reward
      (quittingSingletonBaseStationaryProfile reward owner
        (Finset.univ.erase owner) point) owner + witness.terminalGap ≤
    quittingStationaryUnilateralCap reward
      (quittingPersistentBaseRoot {owner} (Finset.univ.erase owner) point) owner at hwho
  linarith

end GameTheory
