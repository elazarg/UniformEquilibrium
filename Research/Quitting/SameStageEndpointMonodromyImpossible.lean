/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import MathUE.FinFourOrderedCoalitionCycle
import Research.Quitting.SameStageEndpointMonodromy

/-!
# Impossibility of four-supported same-stage endpoint monodromy

A two-player vertex is already a terminal singleton route.  Consequently, a
closed dispatched segment supported on at most four players visits only
triples and the full effective support, forcing period two.  Exact positive
mover-debt subtraction rules out the resulting reverse pair of edges.

This module is independent of the Fin4 producer atlas.  Its reusable theorem
allows any finite ambient player type whose visited support has cardinality at
most four; thin Fin4 and producer-specific wrappers live downstream.
-/

noncomputable section

namespace GameTheory

open MathUE.FiniteBooleanEndpointOrbit
open MathUE.FinFourCoalitionCycle

variable {iota : Type} [Fintype iota] [DecidableEq iota]

private theorem sameStageTrace_orbit_next_eq
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair iota} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition iota}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda
          source target)) start)
    (offset : Fin trace.segment.segment.period) :
    trace.orbit (trace.segment.segment.start +
        (cycleNext' trace.segment.segment.period
          trace.segment.segment.period_pos offset : Fin _)) =
      trace.orbit (trace.segment.segment.start + offset + 1) := by
  dsimp [cycleNext']
  by_cases hlt : offset.val + 1 < trace.segment.segment.period
  · rw [Nat.mod_eq_of_lt hlt]
    congr 1
  · have heq : offset.val + 1 = trace.segment.segment.period := by omega
    rw [heq, Nat.mod_self]
    have hsum : trace.segment.segment.start + offset + 1 =
        trace.segment.segment.start + trace.segment.segment.period := by omega
    rw [hsum]
    simpa using trace.segment.segment.closes.symm

/-- The union of the coalitions visited at the distinct offsets of one simple
same-stage period. -/
def sameStageEndpointTraceVisitedSupport
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair iota} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition iota}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda
          source target)) start) : Finset iota :=
  Finset.univ.biUnion fun offset : Fin trace.segment.segment.period =>
    (trace.orbit (trace.segment.segment.start + offset)).1

/-- An effective-support bound of four forces a same-stage dispatched segment
to have period two.  The ambient finite player type may be larger. -/
theorem sameStageEndpointTrace_period_eq_two_of_effectiveSupport_card_le_four
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair iota} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition iota}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda
          source target)) start)
    (support : Finset iota)
    (hcontained : ∀ offset : Fin trace.segment.segment.period,
      (trace.orbit (trace.segment.segment.start + offset)).1 ⊆ support)
    (hsupport : support.card ≤ 4) :
    trace.segment.segment.period = 2 := by
  let next := cycleNext' trace.segment.segment.period
    trace.segment.segment.period_pos
  have hcard_ge_three : ∀ offset : Fin trace.segment.segment.period,
      3 ≤ (trace.orbit (trace.segment.segment.start + offset)).1.card := by
    intro offset
    have hnonsingleton :=
      (trace.orbit (trace.segment.segment.start + offset)).2
    have hne :
        (trace.orbit (trace.segment.segment.start + offset)).1.card ≠ 2 := by
      intro hcard
      exact trace.offset_not_terminal offset
        (quittingSameStageSingletonRoute_of_card_eq_two
          reward profile stage _ hcard)
    omega
  have hcard_le_four : ∀ offset : Fin trace.segment.segment.period,
      (trace.orbit (trace.segment.segment.start + offset)).1.card ≤ 4 := by
    intro offset
    exact (Finset.card_le_card (hcontained offset)).trans hsupport
  have hstep : ∀ offset : Fin trace.segment.segment.period,
      ((trace.orbit (trace.segment.segment.start + offset)).1.card = 3 ∧
        (trace.orbit (trace.segment.segment.start + next offset)).1.card = 4) ∨
      ((trace.orbit (trace.segment.segment.start + offset)).1.card = 4 ∧
        (trace.orbit (trace.segment.segment.start + next offset)).1.card = 3) := by
    intro offset
    obtain ⟨edge⟩ := trace.offset_edge offset
    have hnext := sameStageTrace_orbit_next_eq trace offset
    have hsourceGe := hcard_ge_three offset
    have hsourceLe := hcard_le_four offset
    have htargetGe := hcard_ge_three (next offset)
    have htargetLe := hcard_le_four (next offset)
    rcases edge.target_eq_singlePlayer_toggle with hdrop | hjoin
    · have hcard :
          (trace.orbit (trace.segment.segment.start + next offset)).1.card =
            (trace.orbit (trace.segment.segment.start + offset)).1.card - 1 := by
        rw [congrArg (fun coalition => coalition.1.card) hnext]
        rw [← hdrop.1, Finset.card_erase_of_mem hdrop.2.2]
      exact Or.inr ⟨by omega, by omega⟩
    · have hcard :
          (trace.orbit (trace.segment.segment.start + next offset)).1.card =
            (trace.orbit (trace.segment.segment.start + offset)).1.card + 1 := by
        rw [congrArg (fun coalition => coalition.1.card) hnext]
        rw [← hjoin.1, Finset.card_insert_of_notMem hjoin.2.2]
      exact Or.inl ⟨by omega, by omega⟩
  have hperiod_ge_two := dispatchedClosedSegment_period_two_or_more trace
  by_contra hne
  have hperiod_ge_three : 3 ≤ trace.segment.segment.period := by omega
  let zero : Fin trace.segment.segment.period :=
    ⟨0, trace.segment.segment.period_pos⟩
  let tripleOffset : Fin trace.segment.segment.period :=
    if (trace.orbit (trace.segment.segment.start + zero)).1.card = 3 then
      zero
    else next zero
  have htriple :
      (trace.orbit (trace.segment.segment.start + tripleOffset)).1.card = 3 := by
    dsimp only [tripleOffset]
    split_ifs with hzero
    · exact hzero
    · rcases hstep zero with hthree | hfour
      · exact False.elim (hzero hthree.1)
      · exact hfour.2
  have hnextFour :
      (trace.orbit (trace.segment.segment.start + next tripleOffset)).1.card = 4 :=
    (hstep tripleOffset).resolve_right (fun hfour => by omega) |>.2
  have htwoThree :
      (trace.orbit
        (trace.segment.segment.start + next (next tripleOffset))).1.card = 3 :=
    (hstep (next tripleOffset)).resolve_left (fun hthree => by omega) |>.2
  have hthreeFour :
      (trace.orbit
        (trace.segment.segment.start + next (next (next tripleOffset)))).1.card = 4 :=
    (hstep (next (next tripleOffset))).resolve_right (fun hfour => by omega) |>.2
  have hnext_eq_support :
      (trace.orbit (trace.segment.segment.start + next tripleOffset)).1 = support := by
    apply Finset.eq_of_subset_of_card_le (hcontained (next tripleOffset))
    omega
  have hthree_eq_support :
      (trace.orbit
        (trace.segment.segment.start + next (next (next tripleOffset)))).1 = support := by
    apply Finset.eq_of_subset_of_card_le
      (hcontained (next (next (next tripleOffset))))
    omega
  have hoffset : next tripleOffset = next (next (next tripleOffset)) := by
    apply trace.segment.offset_injective
    apply Subtype.ext
    rw [hnext_eq_support, hthree_eq_support]
  have htwo : tripleOffset = next (next tripleOffset) :=
    (cycleNext'_injective trace.segment.segment.period
      trace.segment.segment.period_pos) hoffset
  exact cycleNext'_two_step_ne trace.segment.segment.period
    hperiod_ge_three tripleOffset htwo.symm

/-- Exact positive mover-debt subtraction rules out a period-two same-stage
endpoint segment on every finite player type. -/
theorem sameStageEndpointTrace_period_ne_two
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair iota} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition iota}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda
          source target)) start) :
    trace.segment.segment.period ≠ 2 := by
  intro hperiod
  let offsetZero : Fin trace.segment.segment.period :=
    ⟨0, trace.segment.segment.period_pos⟩
  let offsetOne : Fin trace.segment.segment.period := ⟨1, by omega⟩
  obtain ⟨first⟩ := trace.offset_edge offsetZero
  obtain ⟨second⟩ := trace.offset_edge offsetOne
  have hclose : trace.orbit (trace.segment.segment.start + 2) =
      trace.orbit trace.segment.segment.start := by
    simpa [hperiod] using trace.segment.segment.closes
  have first' : QuittingSameStageEndpointEdge reward profile stage minimum lambda
      (trace.orbit trace.segment.segment.start)
      (trace.orbit (trace.segment.segment.start + 1)) := by
    simpa [offsetZero] using first
  have second' : QuittingSameStageEndpointEdge reward profile stage minimum lambda
      (trace.orbit (trace.segment.segment.start + 1))
      (trace.orbit trace.segment.segment.start) := by
    rw [← hclose]
    simpa [offsetOne] using second
  exact first'.not_reverse second'

/-- No same-stage dispatched endpoint segment can stay inside an effective
support of at most four players. -/
theorem sameStageEndpointTrace_false_of_effectiveSupport_card_le_four
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair iota} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition iota}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda
          source target)) start)
    (support : Finset iota)
    (hcontained : ∀ offset : Fin trace.segment.segment.period,
      (trace.orbit (trace.segment.segment.start + offset)).1 ⊆ support)
    (hsupport : support.card ≤ 4) : False := by
  exact sameStageEndpointTrace_period_ne_two trace
    (sameStageEndpointTrace_period_eq_two_of_effectiveSupport_card_le_four
      trace support hcontained hsupport)

/-- In particular, cardinality at most four of the literal union of visited
coalitions is impossible. -/
theorem sameStageEndpointTrace_false_of_visitedSupport_card_le_four
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair iota} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition iota}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda
          source target)) start)
    (hsupport : (sameStageEndpointTraceVisitedSupport trace).card ≤ 4) : False := by
  apply sameStageEndpointTrace_false_of_effectiveSupport_card_le_four trace
    (sameStageEndpointTraceVisitedSupport trace) _ hsupport
  intro offset player hplayer
  exact Finset.mem_biUnion.mpr ⟨offset, Finset.mem_univ _, hplayer⟩

/-- Every Fin4 same-stage dispatched segment would have period two.  This is a
thin specialization of the effective-support theorem. -/
theorem finFourSameStageEndpointTrace_period_eq_two
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition (Fin 4)}
    (trace : DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda
          source target)) start) :
    trace.segment.segment.period = 2 := by
  apply sameStageEndpointTrace_period_eq_two_of_effectiveSupport_card_le_four
    trace Finset.univ
  · intro offset
    exact Finset.subset_univ _
  · simp

/-- No Fin4 same-stage endpoint dispatch can form a closed segment while its
terminal predicate is the mass-preserving singleton route. -/
theorem not_nonempty_finFourSameStageEndpointClosedSegment
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition (Fin 4)} :
    ¬Nonempty (DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda
          source target)) start) := by
  rintro ⟨trace⟩
  have hperiod := finFourSameStageEndpointTrace_period_eq_two trace
  exact sameStageEndpointTrace_period_ne_two trace hperiod

end GameTheory
