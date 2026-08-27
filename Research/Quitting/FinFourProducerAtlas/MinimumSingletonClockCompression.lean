/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.AnchoredSingletonClockCompression
import Research.Quitting.FinFourProducerAtlas.Source

/-!
# Clock compression of a Fin4 minimum-law singleton

This module retains one causal chronology from a minimum-law singleton source
and attaches literal one-date owner-compressed endpoints to cofinally deep
members of that same chronology.  Exact cap--Nash stack data remains attached
to the unmodified source suffix.  No target-side Nash, near-minimum, low-tail,
return, or regeneration property is asserted.
-/

noncomputable section

namespace GameTheory

open Filter
open QuittingNonsingletonMinimumLawTransfer

/-! ## One retained causal chronology -/

/-- The single source chronology unpacked from a minimum-law causal atom.
The final field is retained as the original eventual conjunction rather than
being regenerated from independently selected rows. -/
structure FinFourMinimumAtomChronology
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  profiles : ℕ → (quittingGame reward).BehaviorProfile
  cutoff : ℕ → ℕ
  mark : ℕ → ℕ
  roots : ℕ → List (Fin 4 → PMF Bool)
  profiles_tendsto : Tendsto (fun n ↦
    (quittingTerminalSemanticPair reward (profiles n),
      quittingTerminalOutcomeMass reward (profiles n)))
    atTop (nhds source.point)
  roots_length : ∀ n, (roots n).length = n + 1
  roots_nash : ∀ n, IsQuittingCapNashRootStack reward (roots n) (profiles n)
  prefix_debt_tendsto : Tendsto (fun n ↦ quittingTerminalDebtSum reward
    (prefixedProfile reward profiles roots n))
    atTop (nhds (quittingTerminalDebtSumInf reward))
  causal : ∀ᶠ n in atTop,
    source.point.2 (some source.atom.terminal) / 2 <
        ∑ time ∈ Finset.range (cutoff n),
          quittingStageCoalitionMass reward (profiles n) time source.atom.terminal ∧
      mark n < cutoff n ∧
      0 < quittingStageCoalitionMass reward
        (profiles n) (mark n) source.atom.terminal ∧
      0 < quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward (roots n) (profiles n))
        (n + 1 + mark n) source.atom.terminal

namespace FinFourMinimumAtomChronology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The terminal mass retained strictly on the suffix side of the source root
word, expressed on the actual literally prefixed profile. -/
def prefixedTailMass
    (chronology : FinFourMinimumAtomChronology source) (rank : ℕ) : ℝ :=
  ∑' time, quittingStageCoalitionMass reward
    (prefixedProfile reward chronology.profiles chronology.roots rank)
    ((chronology.roots rank).length + time) source.atom.terminal

/-- Exact transport of the complete suffix terminal atom through the retained
literal root word. -/
theorem prefixedTailMass_eq_continueProduct_mul_terminalMass
    (chronology : FinFourMinimumAtomChronology source) (rank : ℕ) :
    chronology.prefixedTailMass rank =
      quittingCapNashStackContinueProduct (chronology.roots rank) *
        quittingTerminalOutcomeMass reward (chronology.profiles rank)
          (some source.atom.terminal) := by
  unfold prefixedTailMass
  calc
    (∑' time, quittingStageCoalitionMass reward
        (prefixedProfile reward chronology.profiles chronology.roots rank)
        ((chronology.roots rank).length + time) source.atom.terminal) =
        ∑' time, quittingCapNashStackContinueProduct (chronology.roots rank) *
          quittingStageCoalitionMass reward (chronology.profiles rank)
            time source.atom.terminal := by
      apply tsum_congr
      intro time
      exact quittingStageCoalitionMass_literalRootStack_add_length
        reward (chronology.roots rank) (chronology.profiles rank)
          time source.atom.terminal
    _ = quittingCapNashStackContinueProduct (chronology.roots rank) *
        ∑' time, quittingStageCoalitionMass reward
          (chronology.profiles rank) time source.atom.terminal := by
      rw [tsum_mul_left]
    _ = quittingCapNashStackContinueProduct (chronology.roots rank) *
        quittingTerminalOutcomeMass reward (chronology.profiles rank)
          (some source.atom.terminal) := by
      rw [quittingTerminalOutcomeMass_eq_timeDisintegration]

/-- The after-prefix mass of the retained atom converges to its selected
minimum-law coordinate. -/
theorem tendsto_prefixedTailMass
    (chronology : FinFourMinimumAtomChronology source) :
    Tendsto chronology.prefixedTailMass atTop
      (nhds (source.point.2 (some source.atom.terminal))) := by
  have hproduct :=
    QuittingNonsingletonMinimumLawTransfer.tendsto_capNashStackContinueProduct_one
      reward source.point chronology.profiles chronology.roots source.point_mem
        source.minimum source.minimumDebt_pos chronology.profiles_tendsto
        chronology.roots_nash chronology.prefix_debt_tendsto
  have hmass : Tendsto (fun rank ↦
      quittingTerminalOutcomeMass reward (chronology.profiles rank)
        (some source.atom.terminal)) atTop
      (nhds (source.point.2 (some source.atom.terminal))) :=
    ((continuous_apply (some source.atom.terminal)).comp continuous_snd).tendsto
      source.point |>.comp chronology.profiles_tendsto
  have hmul := hproduct.mul hmass
  have hfun : chronology.prefixedTailMass = fun rank ↦
      quittingCapNashStackContinueProduct (chronology.roots rank) *
        quittingTerminalOutcomeMass reward (chronology.profiles rank)
          (some source.atom.terminal) := by
    funext rank
    exact chronology.prefixedTailMass_eq_continueProduct_mul_terminalMass rank
  rw [hfun]
  simpa only [one_mul] using hmul

end FinFourMinimumAtomChronology

namespace FinFourMinimumAtomProducer

/-- The canonical clock-compression scale shared with the existing reached
singleton endpoints. -/
def minimumSingletonClockResolution
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) : ℝ :=
  source.point.2 (some source.atom.terminal) ^ 2 / 8

/-- The canonical clock-compression scale is strictly positive. -/
theorem minimumSingletonClockResolution_pos
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) :
    0 < source.minimumSingletonClockResolution := by
  exact div_pos (pow_pos source.atom.terminalMass_pos 2) (by norm_num)

/-- The canonical scale is strictly below the selected singleton law mass. -/
theorem minimumSingletonClockResolution_lt_terminalMass
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) :
    source.minimumSingletonClockResolution <
      source.point.2 (some source.atom.terminal) := by
  let mass := source.point.2 (some source.atom.terminal)
  have hmassPos : 0 < mass := source.atom.terminalMass_pos
  have hsimplex := terminalSemanticLawCarrier_mass_mem_stdSimplex
    source.point source.point_mem
  have hmassLeOne : mass ≤ 1 := by
    have hle : source.point.2 (some source.atom.terminal) ≤
        ∑ outcome, source.point.2 outcome := by
      exact Finset.single_le_sum
        (fun outcome _ ↦ hsimplex.1 outcome) (Finset.mem_univ _)
    simpa only [mass, hsimplex.2] using hle
  have hmassSquareLe : mass ^ 2 ≤ mass := by
    nlinarith [mul_nonneg hmassPos.le (sub_nonneg.mpr hmassLeOne)]
  dsimp only [minimumSingletonClockResolution, mass]
  nlinarith

/-- Unpack exactly one chronology already stored by the source atom. -/
theorem nonempty_chronology
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) :
    Nonempty (FinFourMinimumAtomChronology source) := by
  obtain ⟨profiles, cutoff, mark, roots, hprofiles, hlength, hnash,
      hprefix, hcausal⟩ := source.atom.chronology
  exact ⟨{
    profiles := profiles
    cutoff := cutoff
    mark := mark
    roots := roots
    profiles_tendsto := hprofiles
    roots_length := hlength
    roots_nash := hnash
    prefix_debt_tendsto := hprefix
    causal := hcausal
  }⟩

end FinFourMinimumAtomProducer

/-! ## Literal owner-compressed endpoints -/

/-- One cofinally deep literal owner-compressed endpoint.  The retained root
stack is certified only over `chronology.profiles rank`; the target profile is
not asserted to preserve that cap--Nash certificate. -/
structure FinFourOwnerCompressedSingletonEndpoint
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (chronology : FinFourMinimumAtomChronology source)
    (owner : Fin 4) (lambda : ℝ) (depth : ℕ) where
  terminal_eq : source.atom.terminal.val = {owner}
  rank : ℕ
  depth_le_rank : depth ≤ rank
  stage : ℕ
  anchor_le_stage : (chronology.roots rank).length ≤ stage
  owner_continue_before : ∀ time,
    (chronology.roots rank).length ≤ time → time < stage →
      quittingProfileLiveRoot reward
          (prefixedProfile reward chronology.profiles chronology.roots rank)
          time owner = PMF.pure false
  stageMass_gt : lambda <
    quittingStageCoalitionMass reward
      (quittingLiteralOneDateProfile reward
        (prefixedProfile reward chronology.profiles chronology.roots rank)
        owner stage true)
      stage source.atom.terminal

namespace FinFourOwnerCompressedSingletonEndpoint

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {chronology : FinFourMinimumAtomChronology source}
  {owner : Fin 4} {lambda : ℝ} {depth : ℕ}

/-- The unmodified suffix over which the retained root stack is cap--Nash. -/
def suffixProfile
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) :
    (quittingGame reward).BehaviorProfile :=
  chronology.profiles endpoint.rank

/-- The retained cap-root stack at the endpoint's selected source rank. -/
def rootStack
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) : List (Fin 4 → PMF Bool) :=
  chronology.roots endpoint.rank

/-- The literal source profile obtained by prefixing the retained suffix. -/
def referenceProfile
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) :
    (quittingGame reward).BehaviorProfile :=
  prefixedProfile reward chronology.profiles chronology.roots endpoint.rank

/-- The actual target changes only `owner` at the selected date. -/
def targetProfile
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralOneDateProfile reward endpoint.referenceProfile
    owner endpoint.stage true

/-- The anchor is the exact length of the retained source root word. -/
def anchor
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) : ℕ :=
  endpoint.rootStack.length

/-- The reference profile is definitionally the original literal prefix. -/
theorem referenceProfile_eq_prefixedProfile
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) :
    endpoint.referenceProfile =
      prefixedProfile reward chronology.profiles chronology.roots endpoint.rank := rfl

/-- The target is definitionally a single literal pure-Quit override. -/
theorem targetProfile_eq_literalOneDateProfile
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) :
    endpoint.targetProfile =
      quittingLiteralOneDateProfile reward endpoint.referenceProfile
        owner endpoint.stage true := rfl

/-- The retained root word has exactly the causal source length `rank + 1`. -/
theorem rootStack_length
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) :
    endpoint.rootStack.length = endpoint.rank + 1 :=
  chronology.roots_length endpoint.rank

/-- The selected anchor is exactly `rank + 1`. -/
theorem anchor_eq_rank_add_one
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) :
    endpoint.anchor = endpoint.rank + 1 :=
  endpoint.rootStack_length

/-- The retained stack remains exactly cap--Nash over the unmodified suffix. -/
theorem rootStack_nash
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) :
    IsQuittingCapNashRootStack reward endpoint.rootStack
      endpoint.suffixProfile :=
  chronology.roots_nash endpoint.rank

/-- The selected date occurs after the complete retained root word. -/
theorem anchor_le_selectedStage
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) :
    endpoint.anchor ≤ endpoint.stage :=
  endpoint.anchor_le_stage

/-- The selected rank is at least the requested depth. -/
theorem requestedDepth_le_rank
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) :
    depth ≤ endpoint.rank :=
  endpoint.depth_le_rank

/-- The original minimum-law atom is literally the selected owner's singleton. -/
theorem terminal_eq_singleton
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) :
    source.atom.terminal.val = {owner} :=
  endpoint.terminal_eq

/-- The actual target has the advertised strict singleton stage-mass floor. -/
theorem target_stageMass_gt
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) :
    lambda < quittingStageCoalitionMass reward endpoint.targetProfile
      endpoint.stage source.atom.terminal :=
  endpoint.stageMass_gt

/-- The source owner already Continues on every intervening live row. -/
theorem referenceProfile_owner_continue_before
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth)
    (time : ℕ) (hanchor : endpoint.anchor ≤ time)
    (hstage : time < endpoint.stage) :
    quittingProfileLiveRoot reward endpoint.referenceProfile time owner =
      PMF.pure false :=
  endpoint.owner_continue_before time hanchor hstage

/-- Every opponent's complete behavioral strategy is literally unchanged. -/
theorem targetProfile_other_eq
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth)
    (other : Fin 4) (hne : other ≠ owner) :
    endpoint.targetProfile other = endpoint.referenceProfile other := by
  simp [targetProfile, quittingLiteralOneDateProfile, hne]

/-- The owner's complete strategy is unchanged at every other date. -/
theorem targetProfile_owner_of_ne
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth)
    (time : ℕ) (hne : time ≠ endpoint.stage) :
    endpoint.targetProfile owner time = endpoint.referenceProfile owner time := by
  simpa [targetProfile, quittingLiteralOneDateProfile] using
    quittingLiteralOneDateOverride_of_ne
      (endpoint.referenceProfile owner) endpoint.stage time true hne

/-- Every complete live root except the selected one is unchanged. -/
theorem targetProfile_liveRoot_eq_of_ne
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth)
    (time : ℕ) (hne : time ≠ endpoint.stage) :
    quittingProfileLiveRoot reward endpoint.targetProfile time =
      quittingProfileLiveRoot reward endpoint.referenceProfile time := by
  unfold quittingProfileLiveRoot
  funext player
  by_cases hplayer : player = owner
  · subst player
    exact congrFun (endpoint.targetProfile_owner_of_ne time hne)
      (quittingLiveHist reward time)
  · exact congrFun
      (congrFun (endpoint.targetProfile_other_eq player hplayer) time)
      (quittingLiveHist reward time)

/-- In particular, the complete retained prefix before the anchor is literal. -/
theorem targetProfile_prefix_liveRoot_eq
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth)
    (time : ℕ) (htime : time < endpoint.anchor) :
    quittingProfileLiveRoot reward endpoint.targetProfile time =
      quittingProfileLiveRoot reward endpoint.referenceProfile time := by
  apply endpoint.targetProfile_liveRoot_eq_of_ne
  exact Nat.ne_of_lt (htime.trans_le endpoint.anchor_le_selectedStage)

/-- The complete post-date live-root tail is literally the source tail. -/
theorem targetProfile_postDate_liveRoot_eq
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) (offset : ℕ) :
    quittingProfileLiveRoot reward endpoint.targetProfile
        (endpoint.stage + 1 + offset) =
      quittingProfileLiveRoot reward endpoint.referenceProfile
        (endpoint.stage + 1 + offset) :=
  quittingProfileLiveRoot_literalOneDateProfile_tail_eq
    endpoint.referenceProfile owner endpoint.stage offset true

/-- The owner's unrestricted behavioral best-response cap is unchanged. -/
theorem targetProfile_ownerCap_eq
    (endpoint : FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) :
    quittingContinuationBestResponseValue reward endpoint.targetProfile owner =
      quittingContinuationBestResponseValue reward endpoint.referenceProfile owner :=
  quittingContinuationBestResponseValue_literalOneDateProfile_self_eq
    reward endpoint.referenceProfile owner endpoint.stage true

end FinFourOwnerCompressedSingletonEndpoint

/-! ## Cofinal compression on one retained chronology -/

namespace FinFourMinimumAtomChronology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Every positive scale below the selected singleton law mass occurs at an
owner-compressed endpoint beyond the requested source rank, using this fixed
chronology's profiles and roots. -/
theorem nonempty_ownerCompressedSingleton
    (chronology : FinFourMinimumAtomChronology source)
    (owner : Fin 4) (hterminal : source.atom.terminal.val = {owner})
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (hlambda_lt : lambda <
      source.point.2 (some source.atom.terminal)) (depth : ℕ) :
    Nonempty (FinFourOwnerCompressedSingletonEndpoint
      source chronology owner lambda depth) := by
  have hevent : ∀ᶠ rank in atTop,
      lambda < chronology.prefixedTailMass rank :=
    chronology.tendsto_prefixedTailMass.eventually (Ioi_mem_nhds hlambda_lt)
  have hdepth : ∀ᶠ rank in atTop, depth ≤ rank :=
    eventually_ge_atTop depth
  obtain ⟨rank, hrankDepth, hrankMass⟩ := (hdepth.and hevent).exists
  let reference :=
    prefixedProfile reward chronology.profiles chronology.roots rank
  let anchor := (chronology.roots rank).length
  have hterminalSubtype :
      source.atom.terminal = quittingSingletonTerminal owner := by
    apply Subtype.ext
    exact hterminal
  have htailEq :
      quittingAnchoredSingletonTailMass reference owner anchor =
        chronology.prefixedTailMass rank := by
    unfold quittingAnchoredSingletonTailMass
      FinFourMinimumAtomChronology.prefixedTailMass reference anchor
    rw [← hterminalSubtype]
  have htailPositive :
      0 < quittingAnchoredSingletonTailMass reference owner anchor :=
    hlambda_pos.trans (by rw [htailEq]; exact hrankMass)
  obtain ⟨offset, _hstop, _hzero, hcontinue, _hstageExact, _hdiv,
      htailLe⟩ :=
    exists_quittingAnchoredSingletonClockCompression
      reference owner anchor htailPositive
  refine ⟨{
    terminal_eq := hterminal
    rank := rank
    depth_le_rank := hrankDepth
    stage := anchor + offset
    anchor_le_stage := Nat.le_add_right anchor offset
    owner_continue_before := ?_
    stageMass_gt := ?_
  }⟩
  · intro time hanchor hstage
    obtain ⟨earlier, rfl⟩ := Nat.exists_eq_add_of_le hanchor
    exact hcontinue earlier (by omega)
  · have htailGt : lambda <
        quittingAnchoredSingletonTailMass reference owner anchor := by
      rw [htailEq]
      exact hrankMass
    have hstageGt := htailGt.trans_le htailLe
    simpa only [reference, anchor, quittingAnchoredSingletonQuitProfile,
      hterminalSubtype] using hstageGt

end FinFourMinimumAtomChronology

namespace FinFourMinimumAtomProducer

/-- Unpack one source chronology before choosing either the fixed positive
resolution or the requested depth.  All resulting endpoints use that same
profile/root family. -/
theorem exists_commonChronology_cofinal_ownerCompressedSingleton
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (owner : Fin 4) (hterminal : source.atom.terminal.val = {owner}) :
    ∃ chronology : FinFourMinimumAtomChronology source,
      ∀ lambda, 0 < lambda →
        lambda < source.point.2 (some source.atom.terminal) →
          ∀ depth, Nonempty (FinFourOwnerCompressedSingletonEndpoint
            source chronology owner lambda depth) := by
  obtain ⟨chronology⟩ := source.nonempty_chronology
  exact ⟨chronology, fun lambda hlambdaPos hlambdaLt depth ↦
    chronology.nonempty_ownerCompressedSingleton owner hterminal lambda
      hlambdaPos hlambdaLt depth⟩

end FinFourMinimumAtomProducer

/-- Canonical `mu^2 / 8` owner-compression data for a minimum-law singleton.
The same retained chronology serves every requested depth. -/
structure FinFourOwnerCompressedSingletonProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  owner : Fin 4
  terminal_eq : source.atom.terminal.val = {owner}
  chronology : FinFourMinimumAtomChronology source
  cofinal_endpoint : ∀ depth, Nonempty
    (FinFourOwnerCompressedSingletonEndpoint source chronology owner
      source.minimumSingletonClockResolution depth)

namespace FinFourOwnerCompressedSingletonProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The producer's original minimum-law terminal is literally a singleton. -/
theorem terminal_card
    (producer : FinFourOwnerCompressedSingletonProducer source) :
    source.atom.terminal.val.card = 1 := by
  rw [producer.terminal_eq]
  simp

/-- The common clock-compression resolution is strictly positive. -/
theorem resolution_pos
    (_producer : FinFourOwnerCompressedSingletonProducer source) :
    0 < source.minimumSingletonClockResolution :=
  source.minimumSingletonClockResolution_pos

/-- An actual compressed endpoint is available beyond every requested rank. -/
theorem nonempty_endpoint
    (producer : FinFourOwnerCompressedSingletonProducer source) (depth : ℕ) :
    Nonempty (FinFourOwnerCompressedSingletonEndpoint source
      producer.chronology producer.owner
      source.minimumSingletonClockResolution depth) :=
  producer.cofinal_endpoint depth

/-- In particular, the producer exposes one literal base endpoint. -/
theorem nonempty_baseEndpoint
    (producer : FinFourOwnerCompressedSingletonProducer source) :
    Nonempty (FinFourOwnerCompressedSingletonEndpoint source
      producer.chronology producer.owner
      source.minimumSingletonClockResolution 0) :=
  producer.nonempty_endpoint 0

end FinFourOwnerCompressedSingletonProducer

namespace FinFourMinimumAtomProducer

/-- A singleton minimum atom canonically yields the cofinal `mu^2 / 8`
owner-compression producer. -/
theorem nonempty_ownerCompressedSingletonProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (terminal_card : source.atom.terminal.val.card = 1) :
    Nonempty (FinFourOwnerCompressedSingletonProducer source) := by
  obtain ⟨owner, hterminal⟩ := Finset.card_eq_one.mp terminal_card
  obtain ⟨chronology, hall⟩ :=
    source.exists_commonChronology_cofinal_ownerCompressedSingleton
      owner hterminal
  exact ⟨{
    owner := owner
    terminal_eq := hterminal
    chronology := chronology
    cofinal_endpoint := hall source.minimumSingletonClockResolution
      source.minimumSingletonClockResolution_pos
      source.minimumSingletonClockResolution_lt_terminalMass
  }⟩

end FinFourMinimumAtomProducer

end GameTheory
