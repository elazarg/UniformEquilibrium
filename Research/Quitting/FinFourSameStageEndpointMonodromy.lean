/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.SameStageEndpointPurification
import MathUE.FinFourOrderedCoalitionCycle

/-!
# Finite-four adapter for same-stage endpoint cycles

This Research module translates a dispatched closed segment of the quitting
endpoint family into the ordered Boolean-cycle interface on `Fin 4`.  The
translation is literal: code vertices are obtained through
`coalitionCodeEquiv.symm`, and the cyclic edge at the closing offset uses the
closed-segment equality.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open MathUE.FinFourCoalitionCycle
open MathUE.FiniteBooleanEndpointOrbit

private abbrev FinFourCoalition := QuittingNonsingletonCoalition (Fin 4)

private theorem oneCoordinateAdjacent_of_toggle
    (source target : FinFourCoalition) (who : Fin 4) (action : Bool)
    (htoggle :
      (source.1.erase who = target.1 ∧ action = false ∧ who ∈ source.1) ∨
        (insert who source.1 = target.1 ∧ action = true ∧ who ∉ source.1)) :
    oneCoordinateAdjacent (coalitionCodeEquiv.symm source)
      (coalitionCodeEquiv.symm target) := by
  rcases htoggle with hdrop | hjoin
  · rcases hdrop with ⟨htarget, hfalse, hmem⟩
    unfold oneCoordinateAdjacent
    have hsource := coalitionSet_equiv_symm source
    have htarget' := coalitionSet_equiv_symm target
    rw [hsource, htarget']
    rw [← htarget]
    have hleft : source.1 \ source.1.erase who = {who} := by
      ext player
      by_cases hplayer : player = who
      · subst player
        simp [hmem]
      · simp [hplayer]
    have hright : source.1.erase who \ source.1 = ∅ :=
      Finset.sdiff_eq_empty_iff_subset.mpr (Finset.erase_subset _ _)
    rw [hleft, hright]
    simp
  · rcases hjoin with ⟨htarget, htrue, hmem⟩
    unfold oneCoordinateAdjacent
    have hsource := coalitionSet_equiv_symm source
    have htarget' := coalitionSet_equiv_symm target
    rw [hsource, htarget']
    rw [← htarget]
    have hleft : source.1 \ insert who source.1 = ∅ :=
      Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_insert _ _)
    have hright : insert who source.1 \ source.1 = {who} := by
      ext player
      by_cases hplayer : player = who
      · subst player
        simp [hmem]
      · simp [hplayer]
    rw [hleft, hright]
    simp

private def finCycleNext (period : ℕ) (period_pos : 0 < period) (offset : Fin period) :
    Fin period :=
  ⟨(offset.val + 1) % period, Nat.mod_lt _ period_pos⟩

private theorem finFourTrace_orbit_next_eq
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (offset : Fin trace.segment.segment.period) :
    trace.orbit (trace.segment.segment.start +
        (finCycleNext trace.segment.segment.period
          trace.segment.segment.period_pos offset : Fin _)) =
      trace.orbit (trace.segment.segment.start + offset + 1) := by
  dsimp [finCycleNext]
  by_cases hlt : offset.val + 1 < trace.segment.segment.period
  · rw [Nat.mod_eq_of_lt hlt]
    congr 1
  · have heq : offset.val + 1 = trace.segment.segment.period := by omega
    rw [heq, Nat.mod_self]
    have hsum : trace.segment.segment.start + offset + 1 =
        trace.segment.segment.start + trace.segment.segment.period := by omega
    rw [hsum]
    simpa using trace.segment.segment.closes.symm

def finFourTraceCode
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (offset : Fin trace.segment.segment.period) : MathUE.FinFourCoalitionCycle.CoalitionCode :=
  coalitionCodeEquiv.symm (trace.orbit (trace.segment.segment.start + offset))

theorem finFourTraceCode_injective
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start) :
    Function.Injective (finFourTraceCode trace) := by
  intro left right hcode
  apply trace.segment.offset_injective
  have hcoal := congrArg coalitionCodeEquiv hcode
  simpa [finFourTraceCode] using hcoal

theorem finFourTraceCode_adjacent
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (offset : Fin trace.segment.segment.period) :
    oneCoordinateAdjacent (finFourTraceCode trace offset)
      (finFourTraceCode trace
        (finCycleNext trace.segment.segment.period trace.segment.segment.period_pos offset)) := by
  obtain ⟨edge⟩ := trace.offset_edge offset
  have hnext := finFourTrace_orbit_next_eq trace offset
  have htoggle := edge.target_eq_singlePlayer_toggle
  have hnext' :
      (trace.orbit (trace.segment.segment.start + offset + 1)).1 =
      (trace.orbit (trace.segment.segment.start +
          (finCycleNext trace.segment.segment.period
            trace.segment.segment.period_pos offset : Fin _))).1 :=
    congrArg Subtype.val hnext.symm
  rcases htoggle with hdrop | hjoin
  · have htoggle' :
        ((trace.orbit (trace.segment.segment.start + offset)).1.erase edge.who =
            (trace.orbit (trace.segment.segment.start +
              (finCycleNext trace.segment.segment.period
                trace.segment.segment.period_pos offset : Fin _))).1 ∧
          edge.action = false ∧ edge.who ∈
            (trace.orbit (trace.segment.segment.start + offset)).1) :=
      ⟨hdrop.1.trans hnext', hdrop.2.1, hdrop.2.2⟩
    have htoggle'' :
        ((trace.orbit (trace.segment.segment.start + offset)).1.erase edge.who =
            (trace.orbit (trace.segment.segment.start +
              (finCycleNext trace.segment.segment.period
                trace.segment.segment.period_pos offset : Fin _))).1 ∧
          edge.action = false ∧ edge.who ∈
            (trace.orbit (trace.segment.segment.start + offset)).1) ∨
        (insert edge.who (trace.orbit (trace.segment.segment.start + offset)).1 =
            (trace.orbit (trace.segment.segment.start +
              (finCycleNext trace.segment.segment.period
                trace.segment.segment.period_pos offset : Fin _))).1 ∧
          edge.action = true ∧ edge.who ∉
            (trace.orbit (trace.segment.segment.start + offset)).1) := Or.inl htoggle'
    simpa [finFourTraceCode] using oneCoordinateAdjacent_of_toggle
      (trace.orbit (trace.segment.segment.start + offset))
      (trace.orbit (trace.segment.segment.start +
        (finCycleNext trace.segment.segment.period
          trace.segment.segment.period_pos offset : Fin _)))
      edge.who edge.action htoggle''
  · have htoggle' :
        (insert edge.who (trace.orbit (trace.segment.segment.start + offset)).1 =
            (trace.orbit (trace.segment.segment.start +
              (finCycleNext trace.segment.segment.period
                trace.segment.segment.period_pos offset : Fin _))).1 ∧
          edge.action = true ∧ edge.who ∉
            (trace.orbit (trace.segment.segment.start + offset)).1) :=
      ⟨hjoin.1.trans hnext', hjoin.2.1, hjoin.2.2⟩
    have htoggle'' :
        ((trace.orbit (trace.segment.segment.start + offset)).1.erase edge.who =
            (trace.orbit (trace.segment.segment.start +
              (finCycleNext trace.segment.segment.period
                trace.segment.segment.period_pos offset : Fin _))).1 ∧
          edge.action = false ∧ edge.who ∈
            (trace.orbit (trace.segment.segment.start + offset)).1) ∨
        (insert edge.who (trace.orbit (trace.segment.segment.start + offset)).1 =
            (trace.orbit (trace.segment.segment.start +
              (finCycleNext trace.segment.segment.period
                trace.segment.segment.period_pos offset : Fin _))).1 ∧
          edge.action = true ∧ edge.who ∉
            (trace.orbit (trace.segment.segment.start + offset)).1) := Or.inr htoggle'
    simpa [finFourTraceCode] using oneCoordinateAdjacent_of_toggle
      (trace.orbit (trace.segment.segment.start + offset))
      (trace.orbit (trace.segment.segment.start +
        (finCycleNext trace.segment.segment.period
          trace.segment.segment.period_pos offset : Fin _)))
      edge.who edge.action htoggle''

def finFourTraceCodeSupport
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start) : Finset MathUE.FinFourCoalitionCycle.CoalitionCode :=
  (Finset.univ : Finset (Fin trace.segment.segment.period)).image (finFourTraceCode trace)

def finFourTraceCoalitionSupport
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start) : Finset FinFourCoalition :=
  (Finset.univ : Finset (Fin trace.segment.segment.period)).image (fun offset :
    Fin trace.segment.segment.period =>
    trace.orbit (trace.segment.segment.start + offset))

theorem finFourTraceCodeSupport_mem_iff
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (offset : Fin trace.segment.segment.period) :
    finFourTraceCode trace offset ∈ finFourTraceCodeSupport trace := by
  exact Finset.mem_image.mpr ⟨offset, Finset.mem_univ _, rfl⟩

theorem finFourTraceCoalitionSupport_mem_iff
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (offset : Fin trace.segment.segment.period) :
    trace.orbit (trace.segment.segment.start + offset) ∈ finFourTraceCoalitionSupport trace := by
  exact Finset.mem_image.mpr ⟨offset, Finset.mem_univ _, rfl⟩

theorem finFourTraceCodeSupport_card_eq_period
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start) :
    (finFourTraceCodeSupport trace).card = trace.segment.segment.period := by
  rw [finFourTraceCodeSupport, Finset.card_image_of_injective _
    (finFourTraceCode_injective trace)]
  simp

theorem finFourTraceCodeSupport_coalitionCodeEquiv_image
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start) :
    (finFourTraceCodeSupport trace).image
        coalitionCodeEquiv = finFourTraceCoalitionSupport trace := by
  ext coalition
  constructor
  · intro hmem
    obtain ⟨code, hcode, hcoal⟩ := Finset.mem_image.mp hmem
    obtain ⟨offset, hoffset, rfl⟩ := Finset.mem_image.mp hcode
    refine Finset.mem_image.mpr ⟨offset, hoffset, ?_⟩
    simpa [finFourTraceCode] using hcoal
  · intro hmem
    obtain ⟨offset, hoffset, hcoal⟩ := Finset.mem_image.mp hmem
    refine Finset.mem_image.mpr ⟨finFourTraceCode trace offset, ?_, ?_⟩
    · exact finFourTraceCodeSupport_mem_iff trace offset
    · simpa [finFourTraceCode] using hcoal

def finFourTraceOrderedBooleanCycle
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start) : OrderedBooleanCycle := by
  refine {
    period := trace.segment.segment.period
    period_pos := trace.segment.segment.period_pos
    vertex := finFourTraceCode trace
    vertex_injective := finFourTraceCode_injective trace
    adjacent := ?_
  }
  intro offset
  simpa [finCycleNext, cycleNext'] using finFourTraceCode_adjacent trace offset

theorem finFourTrace_period_le_eight
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start) : trace.segment.segment.period ≤ 8 := by
  exact orderedBooleanCycle_card_le_eight (finFourTraceOrderedBooleanCycle trace)

theorem finFourTrace_common_or_complementary
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start) :
    (∃ player : Fin 4, ∀ offset : Fin trace.segment.segment.period,
      player ∈ (trace.orbit (trace.segment.segment.start + offset)).1) ∨
    (∃ offset₁ offset₂ : Fin trace.segment.segment.period,
      (trace.orbit (trace.segment.segment.start + offset₁)).1.card = 2 ∧
      (trace.orbit (trace.segment.segment.start + offset₂)).1.card = 2 ∧
      Disjoint (trace.orbit (trace.segment.segment.start + offset₁)).1
        (trace.orbit (trace.segment.segment.start + offset₂)).1) := by
  obtain ⟨_, hgeometry⟩ :=
    orderedBooleanCycle_card_le_eight_and_geometry (finFourTraceOrderedBooleanCycle trace)
  rcases hgeometry with hcommon | hcomplementary
  · left
    obtain ⟨player, hplayer⟩ := hcommon
    refine ⟨player, ?_⟩
    intro offset
    have hmem := hplayer (finFourTraceCode trace offset)
      (finFourTraceCodeSupport_mem_iff trace offset)
    unfold finFourTraceCode at hmem
    rw [coalitionSet_equiv_symm] at hmem
    exact hmem
  · right
    obtain ⟨code₁, hcode₁, code₂, hcode₂, hcard₁, hcard₂, hdisjoint⟩ :=
      hcomplementary
    obtain ⟨offset₁, -, hoffset₁⟩ := Finset.mem_image.mp hcode₁
    obtain ⟨offset₂, -, hoffset₂⟩ := Finset.mem_image.mp hcode₂
    have hset₁ : coalitionSet code₁ =
        (trace.orbit (trace.segment.segment.start + offset₁)).1 := by
      rw [← hoffset₁]
      exact coalitionSet_equiv_symm _
    have hset₂ : coalitionSet code₂ =
        (trace.orbit (trace.segment.segment.start + offset₂)).1 := by
      rw [← hoffset₂]
      exact coalitionSet_equiv_symm _
    refine ⟨offset₁, offset₂, ?_, ?_, ?_⟩
    · rw [← hset₁]
      exact hcard₁
    · rw [← hset₂]
      exact hcard₂
    · rw [← hset₁, ← hset₂]
      exact hdisjoint

theorem finFour_disjoint_card_two_eq_complement
    (s t : Finset (Fin 4))
    (hs : s.card = 2) (ht : t.card = 2) (hdisjoint : Disjoint s t) :
    t = sᶜ := by
  have hunion : s ∪ t = (Finset.univ : Finset (Fin 4)) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, Finset.card_union_of_disjoint hdisjoint, hs, ht]
    norm_num
  ext player
  constructor
  · intro hplayer
    simp only [Finset.mem_compl]
    intro hsource
    exact Finset.disjoint_left.1 hdisjoint hsource hplayer
  · intro hplayer
    simp only [Finset.mem_compl] at hplayer
    have hmem : player ∈ s ∪ t := by
      rw [hunion]
      simp
    rcases Finset.mem_union.mp hmem with hsource | htarget
    · exact False.elim (hplayer hsource)
    · exact htarget

theorem finFourTrace_common_or_complementary_exact
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start) :
    (∃ player : Fin 4, ∀ offset : Fin trace.segment.segment.period,
      player ∈ (trace.orbit (trace.segment.segment.start + offset)).1) ∨
    (∃ offset₁ offset₂ : Fin trace.segment.segment.period,
      (trace.orbit (trace.segment.segment.start + offset₁)).1.card = 2 ∧
      (trace.orbit (trace.segment.segment.start + offset₂)).1.card = 2 ∧
      Disjoint (trace.orbit (trace.segment.segment.start + offset₁)).1
        (trace.orbit (trace.segment.segment.start + offset₂)).1 ∧
      (trace.orbit (trace.segment.segment.start + offset₂)).1 =
        (trace.orbit (trace.segment.segment.start + offset₁)).1ᶜ) := by
  obtain hcommon | ⟨offset₁, offset₂, hcard₁, hcard₂, hdisjoint⟩ :=
    finFourTrace_common_or_complementary trace
  · exact Or.inl hcommon
  · right
    refine ⟨offset₁, offset₂, hcard₁, hcard₂, hdisjoint, ?_⟩
    exact finFour_disjoint_card_two_eq_complement _ _ hcard₁ hcard₂ hdisjoint

theorem finFourTrace_period_le_eight_and_geometry
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start) :
    trace.segment.segment.period ≤ 8 ∧
      ((∃ player : Fin 4, ∀ offset : Fin trace.segment.segment.period,
          player ∈ (trace.orbit (trace.segment.segment.start + offset)).1) ∨
        (∃ offset₁ offset₂ : Fin trace.segment.segment.period,
          (trace.orbit (trace.segment.segment.start + offset₁)).1.card = 2 ∧
          (trace.orbit (trace.segment.segment.start + offset₂)).1.card = 2 ∧
          Disjoint (trace.orbit (trace.segment.segment.start + offset₁)).1
            (trace.orbit (trace.segment.segment.start + offset₂)).1 ∧
          (trace.orbit (trace.segment.segment.start + offset₂)).1 =
            (trace.orbit (trace.segment.segment.start + offset₁)).1ᶜ)) := by
  exact ⟨finFourTrace_period_le_eight trace,
    finFourTrace_common_or_complementary_exact trace⟩

theorem finFourTrace_offset_gain_certificate
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (offset : Fin trace.segment.segment.period) :
    ∃ edge : QuittingSameStageEndpointEdge reward profile stage minimum lambda
        (trace.orbit (trace.segment.segment.start + offset))
        (trace.orbit (trace.segment.segment.start + offset + 1)),
      edge.action = quittingRootBestEndpointAction reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (quittingLiteralPureRootCoalitionProfile reward profile
                stage (trace.orbit (trace.segment.segment.start + offset)))
              (stage + 1))).1
          (quittingProfileLiveRoot reward
            (quittingLiteralPureRootCoalitionProfile reward profile
              stage (trace.orbit (trace.segment.segment.start + offset))) stage)
          edge.who ∧
        0 < quittingSameStageCoalitionGain reward profile stage
          (trace.orbit (trace.segment.segment.start + offset)) edge.who edge.action ∧
        lambda * quittingTerminalSemanticDebtSum minimum / 8 ≤
          quittingSameStageCoalitionGain reward profile stage
            (trace.orbit (trace.segment.segment.start + offset)) edge.who edge.action := by
  let edge := dispatchedClosedSegmentEdge trace offset
  refine ⟨edge, edge.action_eq_best, edge.gain_pos, ?_⟩
  have hfloor := edge.gain_floor
  norm_num [Fintype.card_fin] at hfloor ⊢
  exact hfloor

theorem finFourTrace_stageMass_ge_liveMass
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : FinFourCoalition}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (hlive : lambda ≤ quittingLiveMass reward profile stage) :
    ∀ offset : Fin trace.segment.segment.period,
      lambda ≤ quittingStageCoalitionMass reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage
          (trace.orbit (trace.segment.segment.start + offset))) stage
        (quittingTerminalOfNonsingletonCoalition
          (trace.orbit (trace.segment.segment.start + offset))) := by
  intro offset
  rw [quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass]
  exact hlive

theorem quittingPartialPurification_then_finFourSameStage_dispatch
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (coalition : QuittingNonsingletonCoalition (Fin 4))
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hlambda : 0 < lambda)
    (hmass : lambda ≤ quittingStageCoalitionMass reward baseProfile stage
      (quittingTerminalOfNonsingletonCoalition coalition))
    (hlowTail : quittingSpineDebtExcess reward baseProfile
          (quittingTerminalSemanticDebtSum minimum) (stage + 1) <
        lambda * quittingTerminalSemanticDebtSum minimum / 2) :
    (∃ state steps,
      Nonempty (QuittingPartialPurificationSingleton reward baseProfile stage lambda state) ∧
        QuittingPartialPurificationPath reward baseProfile stage lambda
          (quittingPartialPurificationInitialState reward baseProfile stage lambda coalition hmass)
          state steps ∧
        steps ≤ Fintype.card (Fin 4)) ∨
      ∃ finalState steps,
        QuittingPartialPurificationPath reward baseProfile stage lambda
            (quittingPartialPurificationInitialState reward baseProfile stage lambda
              coalition hmass)
            finalState steps ∧
        steps ≤ Fintype.card (Fin 4) ∧
        (∀ who, finalState.assignment who ≠ none) ∧
        ((Nonempty (DispatchedOrbit
          (QuittingSameStageSingletonRoute
            reward (quittingPartialPurificationStateProfile reward baseProfile stage lambda
              finalState) stage)
          (fun source target => Nonempty
            (QuittingSameStageEndpointEdge
              reward (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                finalState) stage minimum lambda source target))
          finalState.coalition)) ∨
          ∃ trace : DispatchedClosedSegment
              (QuittingSameStageSingletonRoute
                reward (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                  finalState) stage)
              (fun source target => Nonempty
                (QuittingSameStageEndpointEdge
                  reward (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                    finalState) stage minimum lambda source target))
              finalState.coalition,
            trace.segment.segment.period ≤ 8 ∧
            ((∃ player : Fin 4, ∀ offset : Fin trace.segment.segment.period,
                player ∈ (trace.orbit (trace.segment.segment.start + offset)).1) ∨
              (∃ offset₁ offset₂ : Fin trace.segment.segment.period,
                (trace.orbit (trace.segment.segment.start + offset₁)).1.card = 2 ∧
                (trace.orbit (trace.segment.segment.start + offset₂)).1.card = 2 ∧
                Disjoint (trace.orbit (trace.segment.segment.start + offset₁)).1
                  (trace.orbit (trace.segment.segment.start + offset₂)).1 ∧
                (trace.orbit (trace.segment.segment.start + offset₂)).1 =
                  (trace.orbit (trace.segment.segment.start + offset₁)).1ᶜ)) ∧
            (∀ offset : Fin trace.segment.segment.period,
              lambda ≤ quittingStageCoalitionMass reward
                (quittingLiteralPureRootCoalitionProfile reward
                  (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                    finalState) stage
                  (trace.orbit (trace.segment.segment.start + offset))) stage
                (quittingTerminalOfNonsingletonCoalition
                  (trace.orbit (trace.segment.segment.start + offset)))) ∧
            (∀ offset : Fin trace.segment.segment.period,
              ∃ edge : QuittingSameStageEndpointEdge reward
                  (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                    finalState)
                  stage minimum lambda
                  (trace.orbit (trace.segment.segment.start + offset))
                  (trace.orbit (trace.segment.segment.start + offset + 1)),
                edge.action = quittingRootBestEndpointAction reward
                    (quittingTerminalSemanticPair reward
                      (quittingAllContinueProfileSpine reward
                        (quittingLiteralPureRootCoalitionProfile reward
                          (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                            finalState) stage
                          (trace.orbit (trace.segment.segment.start + offset)))
                        (stage + 1))).1
                    (quittingProfileLiveRoot reward
                      (quittingLiteralPureRootCoalitionProfile reward
                        (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                          finalState) stage
                        (trace.orbit (trace.segment.segment.start + offset))) stage)
                    edge.who ∧
                  0 < quittingSameStageCoalitionGain reward
                    (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                      finalState) stage
                    (trace.orbit (trace.segment.segment.start + offset)) edge.who edge.action ∧
                  lambda * quittingTerminalSemanticDebtSum minimum / 8 ≤
                    quittingSameStageCoalitionGain reward
                      (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                        finalState) stage
                      (trace.orbit (trace.segment.segment.start + offset))
                      edge.who edge.action)) := by
  rcases quittingPartialPurification_then_sameStage_dispatch
      reward minimum baseProfile stage lambda coalition hminimumCarrier hminimum
      hminimumDebt hlambda hmass hlowTail with hstop |
        ⟨finalState, steps, hpath, hsteps, hcomplete, hdispatch⟩
  · exact Or.inl hstop
  · right
    refine ⟨finalState, steps, hpath, hsteps, hcomplete, ?_⟩
    rcases hdispatch with hterminal | ⟨trace, _hperiod, _hclosure⟩
    · exact Or.inl hterminal
    · right
      have hlive : lambda ≤ quittingLiveMass reward
          (quittingPartialPurificationStateProfile reward baseProfile stage lambda finalState)
          stage := by
        exact finalState.mass_floor.trans
          (quittingStageCoalitionMass_le_liveMass reward
            (quittingPartialPurificationStateProfile reward baseProfile stage lambda finalState)
            stage (quittingTerminalOfNonsingletonCoalition finalState.coalition))
      obtain ⟨hperiod, hgeometry⟩ := finFourTrace_period_le_eight_and_geometry trace
      exact ⟨trace, hperiod, hgeometry,
        finFourTrace_stageMass_ge_liveMass trace hlive,
        fun offset => finFourTrace_offset_gain_certificate trace offset⟩

end GameTheory
