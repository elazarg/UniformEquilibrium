/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.Coverage

/-!
# Impossibility of the Fin4 same-stage monodromy leaf

A two-player vertex is already a terminal singleton route: removing either
member leaves a singleton and the checked pure-endpoint mass inequality is
exactly the terminal predicate.  Consequently, a closed dispatched segment
on four players can visit only triples and the universal coalition.  Its
injective cyclic word then has period two.  The two reverse edges have the
same mover, so their exact positive debt decreases contradict one another.

The reusable theorem below applies on any finite ambient player type whenever
the union of visited coalitions has cardinality at most four.  It does not
assume a minimum-atom source or any of the atlas scale bounds.
-/

noncomputable section

namespace GameTheory

open MathUE.FiniteBooleanEndpointOrbit
open MathUE.FinFourCoalitionCycle
open QuittingNonsingletonMinimumLawTransfer

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- A two-player same-stage vertex already has a mass-preserving route to a
singleton, independently of the minimum law and gain dispatch. -/
theorem quittingSameStageSingletonRoute_of_card_eq_two
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (source : QuittingNonsingletonCoalition iota)
    (hcard : source.1.card = 2) :
    QuittingSameStageSingletonRoute reward profile stage source := by
  have hcard_pos : 0 < source.1.card := by rw [hcard]; omega
  have hnonempty : source.1.Nonempty := Finset.card_pos.mp hcard_pos
  obtain ⟨who, hwho⟩ := hnonempty
  let routed := quittingPureEndpointRoutedCoalition source.1 who false
  have hrouted : routed.Nonempty :=
    quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
      source.1 who false source.2
  let singleton : {S : Finset iota // S.Nonempty} := ⟨routed, hrouted⟩
  refine ⟨who, false, singleton, ?_, rfl, ?_⟩
  · dsimp only [singleton, routed]
    rw [quittingPureEndpointRoutedCoalition_false,
      Finset.card_erase_of_mem hwho, hcard]
  · rw [quittingStageCoalitionMass_literalOneDateProfile_eq_canonical]
    obtain ⟨hrouted', hmass⟩ := quittingStageCoalitionMass_le_stagePureEndpointRouted
      reward
      (quittingLiteralPureRootCoalitionProfile reward profile stage source)
      who stage (quittingTerminalOfNonsingletonCoalition source) false source.2
    simpa only [singleton, routed, quittingTerminalOfNonsingletonCoalition] using hmass

private theorem QuittingSameStageEndpointEdge.target_eq_toggle
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair iota} {lambda : ℝ}
    {source target : QuittingNonsingletonCoalition iota}
    (edge : QuittingSameStageEndpointEdge reward profile stage minimum lambda
      source target) :
    target.1 = quittingToggleCoalition source.1 edge.who := by
  rcases edge.target_eq_singlePlayer_toggle with hdrop | hjoin
  · rw [quittingToggleCoalition_of_mem hdrop.2.2]
    exact hdrop.1.symm
  · rw [quittingToggleCoalition_of_notMem hjoin.2.2]
    exact hjoin.1.symm

omit [Fintype iota] in
private theorem eq_of_toggle_toggle_eq
    (coalition : Finset iota) (first second : iota)
    (hreturn : quittingToggleCoalition
      (quittingToggleCoalition coalition first) second = coalition) :
    second = first := by
  by_contra hne
  have hmembership := congrArg (fun target => first ∈ target) hreturn
  by_cases hfirst : first ∈ coalition
  · by_cases hsecond : second ∈ coalition
    · simp [quittingToggleCoalition, hfirst, hsecond, hne] at hmembership
    · simp [quittingToggleCoalition, hfirst, hsecond, hne] at hmembership
      exact hne hmembership.symm
  · by_cases hsecond : second ∈ coalition
    · simp [quittingToggleCoalition, hfirst, hsecond, hne] at hmembership
      exact hne hmembership.symm
    · simp [quittingToggleCoalition, hfirst, hsecond, hne] at hmembership

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
  have hfirstToggle :
      (trace.orbit (trace.segment.segment.start + 1)).1 =
        quittingToggleCoalition
          (trace.orbit trace.segment.segment.start).1 first.who := by
    simpa [offsetZero] using first.target_eq_toggle
  have hsecondToggle :
      (trace.orbit (trace.segment.segment.start + 2)).1 =
        quittingToggleCoalition
          (trace.orbit (trace.segment.segment.start + 1)).1 second.who := by
    simpa [offsetOne] using second.target_eq_toggle
  have hreturn : quittingToggleCoalition
        (quittingToggleCoalition
          (trace.orbit trace.segment.segment.start).1 first.who)
        second.who =
      (trace.orbit trace.segment.segment.start).1 := by
    rw [← hfirstToggle, ← hsecondToggle]
    exact congrArg Subtype.val hclose
  have hwho : second.who = first.who :=
    eq_of_toggle_toggle_eq _ first.who second.who hreturn
  let debtAt (time : ℕ) := quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward
      (quittingLiteralPureRootCoalitionProfile reward profile stage
        (trace.orbit (trace.segment.segment.start + time)))) first.who
  have hfirstDebt : debtAt 1 = debtAt 0 -
      quittingSameStageCoalitionGain reward profile stage
        (trace.orbit trace.segment.segment.start) first.who first.action := by
    simpa [debtAt, offsetZero] using first.mover_debt
  have hsecondDebt : debtAt 2 = debtAt 1 -
      quittingSameStageCoalitionGain reward profile stage
        (trace.orbit (trace.segment.segment.start + 1)) first.who second.action := by
    simpa [debtAt, offsetOne, hwho] using second.mover_debt
  have hcloseDebt : debtAt 2 = debtAt 0 := by
    dsimp only [debtAt]
    exact congrArg (fun coalition => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage coalition))
      first.who) (by simpa using hclose)
  have hfirstGainPos : 0 < quittingSameStageCoalitionGain reward profile stage
      (trace.orbit trace.segment.segment.start) first.who first.action := by
    simpa [offsetZero] using first.gain_pos
  have hsecondGainPos : 0 < quittingSameStageCoalitionGain reward profile stage
      (trace.orbit (trace.segment.segment.start + 1)) first.who second.action := by
    simpa [offsetOne, hwho] using second.gain_pos
  linarith

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

namespace FinFourMonodromyProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The dispatched trace stored by a Fin4 monodromy producer is internally
inconsistent.  No source property or quantitative scale field is used. -/
theorem false (producer : FinFourMonodromyProducer source) : False :=
  not_nonempty_finFourSameStageEndpointClosedSegment ⟨producer.trace⟩

end FinFourMonodromyProducer

/-- The exact source-indexed monodromy leaf is empty for arbitrary reward and
bound data. -/
theorem not_nonempty_finFourMonodromyProducer
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) (source : FinFourMinimumAtomProducer reward bound) :
    ¬Nonempty (FinFourMonodromyProducer source) := by
  rintro ⟨producer⟩
  exact producer.false

/-- The common-host refinement is empty by projection to its monodromy
producer. -/
theorem not_nonempty_finFourCommonHostMonodromyProducer
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) (source : FinFourMinimumAtomProducer reward bound) :
    ¬Nonempty (FinFourCommonHostMonodromyProducer source) := by
  rintro ⟨producer⟩
  exact producer.monodromy.false

/-- The complementary-pair refinement is empty by projection to its monodromy
producer. -/
theorem not_nonempty_finFourComplementaryPairMonodromyProducer
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) (source : FinFourMinimumAtomProducer reward bound) :
    ¬Nonempty (FinFourComplementaryPairMonodromyProducer source) := by
  rintro ⟨producer⟩
  exact producer.monodromy.false

namespace FinFourLowTailRow

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Eliminating both impossible monodromy refinements contracts the low-row
dispatch to its two genuine singleton outputs. -/
theorem nonempty_singleton_leaf (low : FinFourLowTailRow source) :
    Nonempty (FinFourPurifiedSingletonProducer source) ∨
      Nonempty (FinFourTerminalSingletonProducer source) := by
  rcases low.nonempty_leaf with purified | terminal | common | complementary
  · exact Or.inl purified
  · exact Or.inr terminal
  · exact False.elim
      (not_nonempty_finFourCommonHostMonodromyProducer reward bound source common)
  · exact False.elim
      (not_nonempty_finFourComplementaryPairMonodromyProducer
        reward bound source complementary)

end FinFourLowTailRow

/-- The four atlas modes left after eliminating both monodromy constructors.
This retains each original source and producer without identifying the three
ways of reaching singleton data. -/
inductive FinFourProducerResidualWithoutMonodromy
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) : Type
  | minimumSingleton
      (source : FinFourMinimumAtomProducer reward bound)
      (terminal_card : source.atom.terminal.val.card = 1)
  | purifiedSingleton
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : FinFourPurifiedSingletonProducer source)
  | terminalSingleton
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : FinFourTerminalSingletonProducer source)
  | tailEscape
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : TailEscapeSubsequence reward source.point source.atom)

/-- Eliminate the impossible constructors of an existing six-tag residual,
without reselecting its source or changing any surviving witness. -/
def FinFourProducerResidual.withoutMonodromy
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} : FinFourProducerResidual reward bound →
      FinFourProducerResidualWithoutMonodromy reward bound
  | .minimumSingleton source terminalCard =>
      .minimumSingleton source terminalCard
  | .purifiedSingleton source producer => .purifiedSingleton source producer
  | .terminalSingleton source producer => .terminalSingleton source producer
  | .tailEscape source producer => .tailEscape source producer
  | .commonHostMonodromy _ producer => False.elim producer.monodromy.false
  | .complementaryPairMonodromy _ producer =>
      False.elim producer.monodromy.false

/-- A hard residual therefore produces one of the four monodromy-free tagged
leaves. -/
theorem nonempty_finFourProducerResidualWithoutMonodromy_of_hardResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    Nonempty (FinFourProducerResidualWithoutMonodromy reward bound) := by
  obtain ⟨producer⟩ :=
    nonempty_finFourProducerResidual_of_hardResidual reward bound residual
  exact ⟨producer.withoutMonodromy⟩

/-- Global bounded-data coverage with the two impossible monodromy tags
removed.  The uniform-payoff arm is unchanged. -/
theorem uniformPayoff_or_nonempty_finFourProducerResidualWithoutMonodromy
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      Nonempty (FinFourProducerResidualWithoutMonodromy reward bound) := by
  rcases uniformPayoff_or_nonempty_finFourProducerResidual reward hreward with
    hpayoff | hresidual
  · exact Or.inl hpayoff
  · obtain ⟨residual⟩ := hresidual
    exact Or.inr ⟨residual.withoutMonodromy⟩

end GameTheory
