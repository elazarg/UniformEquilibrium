/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.MinimumResponseChordRegeneration
import Research.Quitting.FinFourProducerAtlas.NormalizedReturn
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.VanishingDebtAtomAlternative
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawFiniteSpliceMarkedLaw

/-!
# Actual Fin4 decoder for minimum response chords

The normalized-return equality arm supplies an actual fixed pure pair and an
actual three-role endpoint-law sequence.  On the same ranks this module uses
the endpoint recipient's stopping-law decoder.  It keeps the genuine exits
separate: a routed singleton, a prescribed atom, or a response limit strictly
above the minimum.  Only the nonsingleton rectangle whose response limit is
on the minimum fibre is passed to the response-chord compiler.

No branch is discarded and no response endpoint is assumed to be minimal.
The regenerated chronology is not asserted to contain the displayed edge.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Source-attached finite rows immediately before the stopping-law branch.
Unlike `FinFourMinimumResponseRectanglePacket`, this record contains no atom,
response, or compact response endpoint. -/
structure FinFourMinimumResponseEndpointRiseOrigin
    (source : FinFourMinimumAtomProducer reward bound) where
  sourceProfile : ℕ → (quittingGame reward).BehaviorProfile
  mover : Fin 4
  observer : Fin 4
  mover_ne_observer : mover ≠ observer
  replacement : ℕ → (quittingGame reward).BehaviorStrategy mover
  endpointProfile : ℕ → (quittingGame reward).BehaviorProfile
  endpointProfile_eq_update : ∀ rank,
    endpointProfile rank =
      Function.update (sourceProfile rank) mover (replacement rank)
  mark : ℕ → ℕ
  markedCoalition : QuittingNonsingletonCoalition (Fin 4)
  endpointProfile_eq_literalPureRoot : ∀ rank,
    endpointProfile rank = quittingLiteralPureRootCoalitionProfile reward
      (sourceProfile rank) (mark rank) markedCoalition
  liveRoot_eq_of_ne : ∀ rank time, time ≠ mark rank →
    quittingProfileLiveRoot reward (sourceProfile rank) time =
      quittingProfileLiveRoot reward (endpointProfile rank) time
  lambda : ℝ
  lambda_pos : 0 < lambda
  markedStageMass_floor : ∀ rank,
    lambda ≤ quittingStageCoalitionMass reward (endpointProfile rank)
      (mark rank) (quittingTerminalOfNonsingletonCoalition markedCoalition)
  moverGap : ℝ
  moverGap_pos : 0 < moverGap
  moverGain_floor : ∀ rank,
    moverGap ≤ quittingTerminalPayoff reward (endpointProfile rank) mover -
      quittingTerminalPayoff reward (sourceProfile rank) mover
  charge : ℝ
  charge_pos : 0 < charge
  endpointDebtRise : ∀ rank,
    charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (endpointProfile rank)) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (sourceProfile rank)) observer
  endpointPoint : QuittingTerminalSemanticLawPoint (Fin 4)
  endpoint_mem : endpointPoint ∈ quittingTerminalSemanticLawCarrier reward
  endpoint_tendsto : Tendsto (fun rank =>
    (quittingTerminalSemanticPair reward (endpointProfile rank),
      quittingTerminalOutcomeMass reward (endpointProfile rank)))
    atTop (nhds endpointPoint)
  endpoint_debtSum_eq_source :
    quittingTerminalSemanticDebtSum endpointPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1
  rewardBound : ∀ terminal who, |reward terminal who| ≤ bound
  bound_nonneg : 0 ≤ bound

/-- The prescribed-atom exit of the actual stopping-law decoder. -/
structure FinFourMinimumResponsePrescribedAtomExit
    (origin : FinFourMinimumResponseEndpointRiseOrigin source) where
  rank : ℕ → ℕ
  rank_strictMono : StrictMono rank
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  atom_bound : ∀ n,
    (7 * origin.charge / 8) / 2 ≤
      (Fintype.card (QuittingTerminalOutcome (Fin 4)) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (origin.sourceProfile (rank n))
          (origin.endpointProfile (rank n)) origin.observer (some terminal)

/-- The fixed-label rectangle exit before compactifying its response law. -/
structure FinFourMinimumResponseRectangleSequence
    (origin : FinFourMinimumResponseEndpointRiseOrigin source) where
  rank : ℕ → ℕ
  rank_strictMono : StrictMono rank
  quitTime : ℕ → Option ℕ
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  atom_bound : ∀ n,
    (7 * origin.charge / 8) / 4 ≤
      (Fintype.card (QuittingTerminalOutcome (Fin 4)) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (Function.update (origin.endpointProfile (rank n)) origin.observer
            (quittingPureTimeBehaviorStrategy reward origin.observer
              (quitTime n)))
          (Function.update (origin.sourceProfile (rank n)) origin.observer
            (quittingPureTimeBehaviorStrategy reward origin.observer
              (quitTime n))) origin.observer (some terminal)
  observer_debt_bound : ∀ n,
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update (origin.endpointProfile (rank n)) origin.observer
          (quittingPureTimeBehaviorStrategy reward origin.observer
            (quitTime n)))) origin.observer ≤
      quittingStoppingLawAtomDecoderError origin.charge (rank n)
  observer_debt_tendsto_zero : Tendsto (fun n =>
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update (origin.endpointProfile (rank n)) origin.observer
          (quittingPureTimeBehaviorStrategy reward origin.observer
            (quitTime n)))) origin.observer) atTop (nhds 0)

namespace FinFourMinimumResponseEndpointRiseOrigin

variable (origin : FinFourMinimumResponseEndpointRiseOrigin source)

/-- The endpoint observer already has positive debt at the compact endpoint.
This is forced by the per-row rise and nonnegativity of source debt; no
convergence of the source siblings is needed. -/
theorem charge_le_endpointPoint_observerDebt :
    origin.charge ≤ quittingTerminalSemanticDebt origin.endpointPoint.1
      origin.observer := by
  have hlimit : Tendsto (fun rank ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (origin.endpointProfile rank))
          origin.observer) atTop
      (nhds (quittingTerminalSemanticDebt origin.endpointPoint.1
        origin.observer)) :=
    ((continuous_quittingTerminalSemanticDebt origin.observer).comp
      continuous_fst).tendsto origin.endpointPoint |>.comp
        origin.endpoint_tendsto
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlimit
  intro rank
  have hsource : 0 ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (origin.sourceProfile rank))
        origin.observer :=
    quittingTerminalDeviationDebt_nonneg reward
      (origin.sourceProfile rank) origin.observer
  linarith [origin.endpointDebtRise rank]

theorem endpointPoint_observerDebt_pos :
    0 < quittingTerminalSemanticDebt origin.endpointPoint.1 origin.observer :=
  origin.charge_pos.trans_le origin.charge_le_endpointPoint_observerDebt

/-- The endpoint-rise rows are decoded without assuming the rectangle arm.
The fixed terminal label is selected only after deciding which alternative
occurs frequently. -/
theorem prescribedAtom_or_rectangleSequence :
    Nonempty (FinFourMinimumResponsePrescribedAtomExit origin) ∨
      Nonempty (FinFourMinimumResponseRectangleSequence origin) := by
  classical
  let Prescribed : ℕ → Prop := fun rank =>
    ∃ terminal : {S : Finset (Fin 4) // S.Nonempty},
      (7 * origin.charge / 8) / 2 ≤
        (Fintype.card (QuittingTerminalOutcome (Fin 4)) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (origin.sourceProfile rank) (origin.endpointProfile rank)
              origin.observer (some terminal)
  let Rectangle : ℕ → Prop := fun rank =>
    ∃ quitTime : Option ℕ, ∃ terminal : {S : Finset (Fin 4) // S.Nonempty},
      (7 * origin.charge / 8) / 4 ≤
        (Fintype.card (QuittingTerminalOutcome (Fin 4)) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (Function.update (origin.endpointProfile rank) origin.observer
              (quittingPureTimeBehaviorStrategy reward origin.observer quitTime))
            (Function.update (origin.sourceProfile rank) origin.observer
              (quittingPureTimeBehaviorStrategy reward origin.observer quitTime))
            origin.observer (some terminal) ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update (origin.endpointProfile rank) origin.observer
              (quittingPureTimeBehaviorStrategy reward origin.observer quitTime)))
          origin.observer ≤
        quittingStoppingLawAtomDecoderError origin.charge rank
  have halternative : ∀ rank, Prescribed rank ∨ Rectangle rank := by
    intro rank
    have hrise : origin.charge ≤
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update (origin.sourceProfile rank) origin.mover
                (origin.replacement rank))) origin.observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (origin.sourceProfile rank))
              origin.observer := by
      rw [← origin.endpointProfile_eq_update rank]
      exact origin.endpointDebtRise rank
    have h := hasVanishingDebtAtomAlternative_of_endpointDebtRise reward
      (origin.sourceProfile rank) origin.mover origin.observer
      (origin.replacement rank) origin.charge
      (quittingStoppingLawAtomDecoderError origin.charge rank)
      origin.charge_pos
      (quittingStoppingLawAtomDecoderError_pos origin.charge_pos rank)
      (quittingStoppingLawAtomDecoderError_le origin.charge_pos.le rank)
      hrise
    rcases h with hprescribed | ⟨quitTime, terminal, hatom, hdebt⟩
    · left
      rcases hprescribed with ⟨terminal, hatom⟩
      refine ⟨terminal, ?_⟩
      simpa only [origin.endpointProfile_eq_update rank] using hatom
    · right
      refine ⟨quitTime, terminal, ?_, ?_⟩
      · simpa only [origin.endpointProfile_eq_update rank,
          Function.update_eq_self] using hatom
      · simpa only [origin.endpointProfile_eq_update rank] using hdebt
  by_cases hprescribed : ∃ᶠ rank in atTop, Prescribed rank
  · obtain ⟨rank, hrank, hatom⟩ := extraction_of_frequently_atTop hprescribed
    choose terminalAt hterminalAt using hatom
    obtain ⟨terminal, hterminal⟩ := Finite.exists_infinite_fiber terminalAt
    have hfrequent : ∃ᶠ n in atTop, terminalAt n = terminal := by
      rw [Nat.frequently_atTop_iff_infinite]
      exact Set.infinite_coe_iff.mp hterminal
    obtain ⟨fixed, hfixed, hlabel⟩ := extraction_of_frequently_atTop hfrequent
    refine Or.inl ⟨{
      rank := rank ∘ fixed
      rank_strictMono := hrank.comp hfixed
      terminal := terminal
      atom_bound := ?_ }⟩
    intro n
    have h := hterminalAt (fixed n)
    rw [hlabel n] at h
    exact h
  · have hrectangle : ∀ᶠ rank in atTop, Rectangle rank := by
      filter_upwards [Filter.not_frequently.mp hprescribed] with rank hnot
      exact (halternative rank).resolve_left hnot
    obtain ⟨start, hstart⟩ := eventually_atTop.1 hrectangle
    have hchoice : ∀ n, Rectangle (n + start) := by
      intro n
      exact hstart (n + start) (Nat.le_add_left start n)
    choose quitTimeAt terminalAt hatomAt hdebtAt using hchoice
    obtain ⟨terminal, hterminalInfinite⟩ :=
      Finite.exists_infinite_fiber terminalAt
    have hfrequent : ∃ᶠ n in atTop, terminalAt n = terminal := by
      rw [Nat.frequently_atTop_iff_infinite]
      exact Set.infinite_coe_iff.mp hterminalInfinite
    obtain ⟨fixed, hfixed, hlabel⟩ := extraction_of_frequently_atTop hfrequent
    let rank : ℕ → ℕ := fun n => fixed n + start
    let quitTime : ℕ → Option ℕ := fun n => quitTimeAt (fixed n)
    have hrank : StrictMono rank := fun _ _ hlt =>
      Nat.add_lt_add_right (hfixed hlt) start
    have herror : Tendsto
        (fun n => quittingStoppingLawAtomDecoderError origin.charge (rank n))
        atTop (nhds 0) :=
      (tendsto_quittingStoppingLawAtomDecoderError origin.charge).comp
        hrank.tendsto_atTop
    have hdebt : Tendsto (fun n =>
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update (origin.endpointProfile (rank n)) origin.observer
              (quittingPureTimeBehaviorStrategy reward origin.observer
                (quitTime n)))) origin.observer) atTop (nhds 0) := by
      apply squeeze_zero
      · intro n
        exact quittingTerminalDeviationDebt_nonneg reward _ origin.observer
      · intro n
        simpa only [rank, quitTime] using hdebtAt (fixed n)
      · exact herror
    refine Or.inr ⟨{
      rank := rank
      rank_strictMono := hrank
      quitTime := quitTime
      terminal := terminal
      atom_bound := ?_
      observer_debt_bound := ?_
      observer_debt_tendsto_zero := hdebt }⟩
    intro n
    have h := hatomAt (fixed n)
    rw [hlabel n] at h
    simpa only [rank, quitTime] using h
    intro n
    simpa only [rank, quitTime] using hdebtAt (fixed n)

end FinFourMinimumResponseEndpointRiseOrigin

/-- A rectangle whose actual response compactifies strictly above the global
minimum.  The exact response profiles and common subsequence are retained. -/
structure FinFourMinimumResponseStrictResponseAscent
    {origin : FinFourMinimumResponseEndpointRiseOrigin source}
    (sequence : FinFourMinimumResponseRectangleSequence origin) where
  refinement : ℕ → ℕ
  refinement_strictMono : StrictMono refinement
  responsePoint : QuittingTerminalSemanticLawPoint (Fin 4)
  response_mem : responsePoint ∈ quittingTerminalSemanticLawCarrier reward
  response_tendsto : Tendsto (fun rank =>
    let index := refinement rank
    let profile := Function.update
      (origin.endpointProfile (sequence.rank index)) origin.observer
      (quittingPureTimeBehaviorStrategy reward origin.observer
        (sequence.quitTime index))
    (quittingTerminalSemanticPair reward profile,
      quittingTerminalOutcomeMass reward profile)) atTop (nhds responsePoint)
  response_observerDebt_eq_zero :
    quittingTerminalSemanticDebt responsePoint.1 origin.observer = 0
  debtSum_gt_source :
    quittingTerminalSemanticDebtSum source.point.1 <
      quittingTerminalSemanticDebtSum responsePoint.1

/-- The minimum-fibre rectangle produced from actual endpoint-rise data.
The stored rectangle is already the output of the committed route-mode
compiler, so all response-chord consumers apply directly. -/
structure FinFourMinimumResponseCompiledRectangle
    {origin : FinFourMinimumResponseEndpointRiseOrigin source}
    (sequence : FinFourMinimumResponseRectangleSequence origin) where
  packet : FinFourMinimumResponseRectanglePacket source
  packet_mover : packet.mover = origin.mover
  packet_observer : packet.observer = origin.observer
  packet_markedCoalition : packet.markedCoalition = origin.markedCoalition
  packet_lambda : packet.lambda = origin.lambda
  packet_moverGap : packet.moverGap = origin.moverGap
  packet_endpointPoint : packet.endpointPoint = origin.endpointPoint
  packet_mark : ∀ rank,
    packet.mark rank = origin.mark (sequence.rank rank)
  packet_sourceProfile : ∀ rank,
    packet.sourceProfile rank = origin.sourceProfile (sequence.rank rank)
  packet_endpointProfile : ∀ rank,
    packet.endpointProfile rank = origin.endpointProfile (sequence.rank rank)
  packet_responseChoice : ∀ rank,
    packet.responseChoice rank = sequence.quitTime rank
  packet_responseAtom : packet.responseAtom = sequence.terminal
  packet_eta : packet.eta =
    (7 * origin.charge / 8) /
      (4 * (Fintype.card (QuittingTerminalOutcome (Fin 4)) : ℝ))
  packet_crossFloor : packet.crossFloor = 7 * origin.charge / 8
  response_observerDebt_eq_zero :
    quittingTerminalSemanticDebt packet.responsePoint.1 origin.observer = 0
  rectangle : FinFourMinimumResponseRectangle source
  rectangle_toPacket :
    rectangle.toFinFourMinimumResponseRectanglePacket = packet

namespace FinFourMinimumResponseCompiledRectangle

variable
  {origin : FinFourMinimumResponseEndpointRiseOrigin source}
  {sequence : FinFourMinimumResponseRectangleSequence origin}

/-- Every proper chord parameter is consumed by the committed response-chord
compiler without selecting a new source packet. -/
theorem nonempty_chord
    (compiled : FinFourMinimumResponseCompiledRectangle sequence)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    Nonempty (FinFourMinimumResponseChord source compiled.rectangle theta
      htheta0 htheta1) :=
  compiled.rectangle.nonempty_minimumResponseChord theta htheta0 htheta1

theorem endpointPoint_observerDebt_pos
    (compiled : FinFourMinimumResponseCompiledRectangle sequence) :
    0 < quittingTerminalSemanticDebt compiled.packet.endpointPoint.1
      compiled.packet.observer := by
  rw [compiled.packet_endpointPoint, compiled.packet_observer]
  exact origin.endpointPoint_observerDebt_pos

theorem responsePoint_observerDebt_eq_zero
    (compiled : FinFourMinimumResponseCompiledRectangle sequence) :
    quittingTerminalSemanticDebt compiled.packet.responsePoint.1
      compiled.packet.observer = 0 := by
  rw [compiled.packet_observer]
  exact compiled.response_observerDebt_eq_zero

/-- The response law retains the full actual packet resolution, not the
pigeonholed response-atom scale. -/
theorem lambda_le_responsePoint_terminalMass
    (compiled : FinFourMinimumResponseCompiledRectangle sequence) :
    origin.lambda ≤ compiled.packet.responsePoint.2
      (some compiled.rectangle.routedTerminal) := by
  rw [← compiled.packet_lambda, ← compiled.rectangle_toPacket]
  exact compiled.rectangle.lambda_le_responsePoint_terminalMass

/-- The actual endpoint rise and vanishing-debt response make the response
support strictly smaller than every proper chord support.  Unlike the generic
response-chord theorem, no extra killed-coordinate hypotheses are required. -/
theorem nonempty_chord_with_responseSupportDrop
    (compiled : FinFourMinimumResponseCompiledRectangle sequence)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    ∃ chord : FinFourMinimumResponseChord source compiled.rectangle theta
        htheta0 htheta1,
      quittingPositiveDebtSupport compiled.rectangle.responsePoint.1 ⊂
        quittingPositiveDebtSupport chord.chordPoint.1 := by
  obtain ⟨chord⟩ := compiled.nonempty_chord theta htheta0 htheta1
  refine ⟨chord, chord.response_support_ssubset_chord_of_killed ?_ ?_⟩
  · rw [compiled.rectangle_toPacket]
    exact compiled.endpointPoint_observerDebt_pos
  · rw [compiled.rectangle_toPacket]
    exact compiled.responsePoint_observerDebt_eq_zero

end FinFourMinimumResponseCompiledRectangle

namespace FinFourMinimumResponseRectangleSequence

variable
  {origin : FinFourMinimumResponseEndpointRiseOrigin source}
  (sequence : FinFourMinimumResponseRectangleSequence origin)

/-- The fixed rectangle label has a genuinely positive signed complete-law
atom on every retained row. -/
theorem responseAtom_pos (rank : ℕ) :
    0 < quittingTerminalPayoffDifferenceAtom reward
      (Function.update (origin.endpointProfile (sequence.rank rank))
        origin.observer
        (quittingPureTimeBehaviorStrategy reward origin.observer
          (sequence.quitTime rank)))
      (Function.update (origin.sourceProfile (sequence.rank rank))
        origin.observer
        (quittingPureTimeBehaviorStrategy reward origin.observer
          (sequence.quitTime rank))) origin.observer (some sequence.terminal) := by
  have hlower : 0 < (7 * origin.charge / 8) / 4 :=
    div_pos (div_pos (mul_pos (by norm_num) origin.charge_pos) (by norm_num))
      (by norm_num)
  have hproduct := hlower.trans_le (sequence.atom_bound rank)
  rcases mul_pos_iff.mp hproduct with hpositive | hnegative
  · exact hpositive.2
  · have hcard : 0 <
        (Fintype.card (QuittingTerminalOutcome (Fin 4)) : ℝ) := by positivity
    exact (not_lt_of_ge hcard.le hnegative.1).elim

/-- Positivity of the actual response atom forces every finite response to be
at or after the retained marked date, even in the strict response-ascent arm. -/
theorem quitTime_ge_mark (rank stop : ℕ)
    (hchoice : sequence.quitTime rank = some stop) :
    origin.mark (sequence.rank rank) ≤ stop := by
  let atomValue := quittingTerminalPayoffDifferenceAtom reward
    (Function.update (origin.endpointProfile (sequence.rank rank))
      origin.observer
      (quittingPureTimeBehaviorStrategy reward origin.observer
        (sequence.quitTime rank)))
    (Function.update (origin.sourceProfile (sequence.rank rank))
      origin.observer
      (quittingPureTimeBehaviorStrategy reward origin.observer
        (sequence.quitTime rank))) origin.observer (some sequence.terminal)
  apply responseAtom_pos_imp_pureTime_ge_mark reward
    (origin.sourceProfile (sequence.rank rank))
    (origin.endpointProfile (sequence.rank rank)) origin.observer
    (sequence.quitTime rank) (origin.mark (sequence.rank rank))
    sequence.terminal atomValue (sequence.responseAtom_pos rank)
  · intro time htime
    exact origin.liveRoot_eq_of_ne (sequence.rank rank) time
      (Nat.ne_of_lt htime)
  · exact le_rfl
  · exact hchoice

private theorem exists_rectangle_eq_packet
    (packet : FinFourMinimumResponseRectanglePacket source) :
    ∃ rectangle : FinFourMinimumResponseRectangle source,
      rectangle.toFinFourMinimumResponseRectanglePacket = packet := by
  let label : ℕ → Bool := fun rank =>
    packet.responseModeAt (packet.commonSubsequence rank)
  obtain ⟨fixed, hfixedInfinite⟩ := Finite.exists_infinite_fiber label
  have hfrequent : ∃ᶠ rank in atTop, label rank = fixed := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact Set.infinite_coe_iff.mp hfixedInfinite
  obtain ⟨refine, hrefine, hfixed⟩ :=
    extraction_of_frequently_atTop hfrequent
  let routed : {S : Finset (Fin 4) // S.Nonempty} :=
    ⟨quittingPureEndpointRoutedCoalition packet.markedCoalition.1
        packet.observer fixed,
      quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
        packet.markedCoalition.1 packet.observer fixed
        packet.markedCoalition.2⟩
  let rectangle : FinFourMinimumResponseRectangle source := {
    toFinFourMinimumResponseRectanglePacket := packet
    routeRefinement := refine
    routeRefinement_strictMono := hrefine
    routedAction := fixed
    routedTerminal := routed
    routedTerminal_eq := rfl
    responseMode_eq := by
      intro rank
      have hmode := (hfixed rank).symm
      change fixed = packet.responseModeAt
        (packet.commonSubsequence (refine rank)) at hmode
      cases hchoice : packet.responseChoice
          (packet.commonSubsequence (refine rank)) with
      | none => simpa only [FinFourMinimumResponseRectanglePacket.responseModeAt,
          hchoice] using hmode
      | some stop =>
          simpa only [FinFourMinimumResponseRectanglePacket.responseModeAt,
            hchoice] using hmode
  }
  exact ⟨rectangle, rfl⟩

/-- The actual rectangle response either remains strictly above the minimum
or compiles, at its exact minimum law, to the committed response rectangle. -/
theorem strictResponseAscent_or_compiledRectangle :
    Nonempty (FinFourMinimumResponseStrictResponseAscent sequence) ∨
      Nonempty (FinFourMinimumResponseCompiledRectangle sequence) := by
  let responseProfile : ℕ → (quittingGame reward).BehaviorProfile := fun rank =>
    Function.update (origin.endpointProfile (sequence.rank rank))
      origin.observer
      (quittingPureTimeBehaviorStrategy reward origin.observer
        (sequence.quitTime rank))
  let responsePointSeq : ℕ → QuittingTerminalSemanticLawPoint (Fin 4) :=
    fun rank =>
      (quittingTerminalSemanticPair reward (responseProfile rank),
        quittingTerminalOutcomeMass reward (responseProfile rank))
  have hmem : ∀ rank, responsePointSeq rank ∈
      quittingTerminalSemanticLawCarrier reward := fun rank =>
    quittingTerminalSemanticLawPoint_mem_carrier reward (responseProfile rank)
  obtain ⟨responsePoint, hresponseMem, refine, hrefine, hresponse⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq hmem
  have hresponseObserverDebt :
      quittingTerminalSemanticDebt responsePoint.1 origin.observer = 0 := by
    have hselected := sequence.observer_debt_tendsto_zero.comp
      hrefine.tendsto_atTop
    have hpoint := ((continuous_quittingTerminalSemanticDebt
      origin.observer).comp continuous_fst).tendsto responsePoint |>.comp
        hresponse
    exact tendsto_nhds_unique hpoint hselected
  have hminimum : quittingTerminalSemanticDebtSum source.point.1 ≤
      quittingTerminalSemanticDebtSum responsePoint.1 :=
    source.minimum responsePoint.1
      (terminalSemanticLawCarrier_fst_mem_carrier responsePoint hresponseMem)
  rcases hminimum.eq_or_lt with heq | hstrict
  · right
    have hendpointTendsto : Tendsto (fun rank =>
        (quittingTerminalSemanticPair reward
            (origin.endpointProfile (sequence.rank (refine rank))),
          quittingTerminalOutcomeMass reward
            (origin.endpointProfile (sequence.rank (refine rank)))))
        atTop (nhds origin.endpointPoint) :=
      origin.endpoint_tendsto.comp
        (sequence.rank_strictMono.comp hrefine).tendsto_atTop
    let outcomeCard : ℝ :=
      Fintype.card (QuittingTerminalOutcome (Fin 4))
    let eta : ℝ := (7 * origin.charge / 8) / (4 * outcomeCard)
    have houtcomeCard : 0 < outcomeCard := by
      dsimp only [outcomeCard]
      positivity
    have heta : 0 < eta := by
      dsimp only [eta]
      exact div_pos (div_pos (mul_pos (by norm_num) origin.charge_pos)
        (by norm_num)) (mul_pos (by norm_num) houtcomeCard)
    have hatomFloor : ∀ rank, eta ≤
        (quittingTerminalOutcomeMass reward
            (Function.update
              (origin.endpointProfile (sequence.rank rank)) origin.observer
              (quittingPureTimeBehaviorStrategy reward origin.observer
                (sequence.quitTime rank))) (some sequence.terminal) -
          quittingTerminalOutcomeMass reward
            (Function.update
              (origin.sourceProfile (sequence.rank rank)) origin.observer
              (quittingPureTimeBehaviorStrategy reward origin.observer
                (sequence.quitTime rank))) (some sequence.terminal)) *
          reward sequence.terminal origin.observer := by
      intro rank
      have hatom := sequence.atom_bound rank
      unfold quittingTerminalPayoffDifferenceAtom at hatom
      simp only [quittingTerminalOutcomeReward] at hatom
      calc
        (7 * origin.charge / 8) / (4 * outcomeCard) =
            ((7 * origin.charge / 8) / 4) / outcomeCard := by ring
        _ ≤ _ := (div_le_iff₀ houtcomeCard).2 (by
          simpa only [outcomeCard, mul_comm] using hatom)
    have hcross : ∀ rank, 7 * origin.charge / 8 ≤
        (quittingTerminalPayoff reward
            (Function.update
              (origin.endpointProfile (sequence.rank rank)) origin.observer
              (quittingPureTimeBehaviorStrategy reward origin.observer
                (sequence.quitTime rank))) origin.observer -
          quittingTerminalPayoff reward
            (origin.endpointProfile (sequence.rank rank)) origin.observer) -
        (quittingTerminalPayoff reward
            (Function.update
              (origin.sourceProfile (sequence.rank rank)) origin.observer
              (quittingPureTimeBehaviorStrategy reward origin.observer
                (sequence.quitTime rank))) origin.observer -
          quittingTerminalPayoff reward
            (origin.sourceProfile (sequence.rank rank)) origin.observer) := by
      intro rank
      let response := quittingPureTimeBehaviorStrategy reward origin.observer
        (sequence.quitTime rank)
      have hendpoint :=
        quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain reward
          (origin.endpointProfile (sequence.rank rank)) origin.observer response
      have hsource :=
        quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain reward
          (origin.sourceProfile (sequence.rank rank)) origin.observer response
      have hsourceNonneg := quittingTerminalDeviationDebt_nonneg reward
        (Function.update (origin.sourceProfile (sequence.rank rank))
          origin.observer response) origin.observer
      have herror := sequence.observer_debt_bound rank
      have herrorLe := quittingStoppingLawAtomDecoderError_le
        origin.charge_pos.le (sequence.rank rank)
      have hrise := origin.endpointDebtRise (sequence.rank rank)
      change 0 ≤ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update (origin.sourceProfile (sequence.rank rank))
            origin.observer response)) origin.observer at hsourceNonneg
      dsimp only [response] at hendpoint hsource hsourceNonneg herror ⊢
      nlinarith
    let packet : FinFourMinimumResponseRectanglePacket source := {
      sourceProfile := origin.sourceProfile ∘ sequence.rank
      mover := origin.mover
      observer := origin.observer
      mover_ne_observer := origin.mover_ne_observer
      replacement := origin.replacement ∘ sequence.rank
      responseChoice := sequence.quitTime
      mark := origin.mark ∘ sequence.rank
      markedCoalition := origin.markedCoalition
      endpointProfile := origin.endpointProfile ∘ sequence.rank
      endpointProfile_eq_update := fun rank =>
        origin.endpointProfile_eq_update (sequence.rank rank)
      endpointProfile_eq_literalPureRoot := fun rank =>
        origin.endpointProfile_eq_literalPureRoot (sequence.rank rank)
      liveRoot_eq_of_ne := fun rank time htime =>
        origin.liveRoot_eq_of_ne (sequence.rank rank) time htime
      responseAtom := sequence.terminal
      eta := eta
      eta_pos := heta
      responseAtom_floor := hatomFloor
      lambda := origin.lambda
      lambda_pos := origin.lambda_pos
      markedStageMass_floor := fun rank =>
        origin.markedStageMass_floor (sequence.rank rank)
      moverGap := origin.moverGap
      moverGap_pos := origin.moverGap_pos
      moverGain_floor := fun rank => origin.moverGain_floor (sequence.rank rank)
      crossFloor := 7 * origin.charge / 8
      crossFloor_pos := div_pos
        (mul_pos (by norm_num) origin.charge_pos) (by norm_num)
      responseCross_floor := hcross
      rewardBound := origin.rewardBound
      bound_nonneg := origin.bound_nonneg
      commonSubsequence := refine
      commonSubsequence_strictMono := hrefine
      endpointPoint := origin.endpointPoint
      responsePoint := responsePoint
      endpoint_tendsto := hendpointTendsto
      response_tendsto := by
        change Tendsto (responsePointSeq ∘ refine) atTop (nhds responsePoint)
        exact hresponse
      endpoint_mem := origin.endpoint_mem
      response_mem := hresponseMem
      endpoint_debtSum_eq_source := origin.endpoint_debtSum_eq_source
      response_debtSum_eq_source := heq.symm
    }
    obtain ⟨rectangle, hrectangle⟩ := exists_rectangle_eq_packet packet
    exact ⟨{
      packet := packet
      packet_mover := rfl
      packet_observer := rfl
      packet_markedCoalition := rfl
      packet_lambda := rfl
      packet_moverGap := rfl
      packet_endpointPoint := rfl
      packet_mark := fun _ => rfl
      packet_sourceProfile := fun _ => rfl
      packet_endpointProfile := fun _ => rfl
      packet_responseChoice := fun _ => rfl
      packet_responseAtom := rfl
      packet_eta := rfl
      packet_crossFloor := rfl
      response_observerDebt_eq_zero := hresponseObserverDebt
      rectangle := rectangle
      rectangle_toPacket := hrectangle }⟩
  · left
    exact ⟨{
      refinement := refine
      refinement_strictMono := hrefine
      responsePoint := responsePoint
      response_mem := hresponseMem
      response_tendsto := by
        change Tendsto (responsePointSeq ∘ refine) atTop (nhds responsePoint)
        exact hresponse
      response_observerDebt_eq_zero := hresponseObserverDebt
      debtSum_gt_source := hstrict }⟩

end FinFourMinimumResponseRectangleSequence

namespace QuittingMarkedPairMinimumReturnActualizer

variable
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}
  {selection : FinFourNormalizedReturnSelection packet}
  {point : QuittingMarkedPairDecoration (Fin 4)}

/-- The actualized marked root is still the fixed pure pair produced by the
Fin4 forced-pair source.  Arbitrary literal prefixes only shift its date. -/
theorem finFour_markedRoot_eq_pureTerminal
    (actualizer : QuittingMarkedPairMinimumReturnActualizer selection.family
      source.point.1 selection.massDensity selection.gainDensity point)
    (rank : ℕ) :
    quittingProfileLiveRoot reward (actualizer.profiles rank)
        (actualizer.mark rank) =
      fun who => PMF.pure
        (quittingCoalitionAction selection.family.terminal.val who) := by
  rw [QuittingMarkedPairMinimumReturnActualizer.profiles,
    QuittingMarkedPairMinimumReturnActualizer.mark,
    selection.family.descendant_markedRoot_eq]
  rw [selection.profile_eq (actualizer.originRank rank),
    selection.mark_eq (actualizer.originRank rank)]
  let index := packet.subsequence
    (selection.packetIndex (actualizer.originRank rank))
  let adapter := packet.base.forcedAdapter index
  change quittingProfileLiveRoot reward adapter.targetProfile
      (packet.base.endpoint index).stage = _
  rw [adapter.targetProfile_eq_literalOneDateProfile,
    quittingProfileLiveRoot_literalOneDateProfile]
  have hsourceRoot : adapter.sourceRoot =
      fun who => PMF.pure
        (quittingCoalitionAction source.atom.terminal.val who) := by
    change quittingProfileLiveRoot reward
      (packet.base.pureSingletonProfile index)
        (packet.base.endpoint index).stage = _
    simp only [FinFourOwnerCompressedMinimumReturnForcedPairBase.pureSingletonProfile,
      quittingProfileLiveRoot_literalPureRootProfile_self]
  change Function.update adapter.sourceRoot packet.base.forcedOwner
    (PMF.pure adapter.action) = _
  rw [hsourceRoot]
  have hterminal : selection.family.terminal = adapter.routedTerminal := by
    rw [selection.terminal_eq]
    exact (packet.forcedTerminal_eq_movingTerminal
      (selection.packetIndex (actualizer.originRank rank))).symm
  rw [hterminal]
  funext who
  rw [QuittingStageAtomConcentratedPacketAdapter.routedTerminal_val]
  unfold QuittingStageAtomConcentratedPacketAdapter.routedCoalition
  rw [quittingCoalitionAction_routed]
  simp only [Function.update_apply]
  split <;> rfl

end QuittingMarkedPairMinimumReturnActualizer

/-- Reapplying the same pure root to a profile already purified at that date
does not change any complete behavioral rule. -/
theorem quittingLiteralPureRootProfile_idem
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (root : ι → Bool) :
    quittingLiteralPureRootProfile reward
        (quittingLiteralPureRootProfile reward profile stage root) stage root =
      quittingLiteralPureRootProfile reward profile stage root := by
  funext who
  exact quittingLiteralOneDateOverride_idem (profile who) stage (root who)

/-- A second literal root at the same date overwrites the first one.  This is
the profile-level form needed when a source row is purified before routing its
marked coalition. -/
theorem quittingLiteralPureRootProfile_absorb
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (firstRoot secondRoot : ι → Bool) :
    quittingLiteralPureRootProfile reward
        (quittingLiteralPureRootProfile reward profile stage firstRoot)
        stage secondRoot =
      quittingLiteralPureRootProfile reward profile stage secondRoot := by
  funext who time history
  by_cases htime : time = stage
  · subst time
    simp [quittingLiteralPureRootProfile, quittingLiteralOneDateOverride]
  · simp [quittingLiteralPureRootProfile, quittingLiteralOneDateOverride,
      htime]

/-- Exact provenance of the endpoint-rise origin decoded from one actual
normalized-return endpoint.  The retained rank is a strict refinement of the
endpoint-law ranks, and both displayed profiles are literal pure roots over
the same upstream packet row. -/
structure FinFourMinimumResponseCanonicalEndpointRiseOrigin
    {returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source}
    {lambda : ℝ}
    {sourcePacket : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    {selection : FinFourNormalizedReturnSelection sourcePacket}
    {point : QuittingMarkedPairDecoration (Fin 4)}
    {actualizer : QuittingMarkedPairMinimumReturnActualizer selection.family
      source.point.1 selection.massDensity selection.gainDensity point}
    {mover observer : Fin 4}
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1
      actualizer.packet mover observer) where
  origin : FinFourMinimumResponseEndpointRiseOrigin source
  endpointRank : ℕ → ℕ
  endpointRank_strictMono : StrictMono endpointRank
  initialCoalition : QuittingNonsingletonCoalition (Fin 4)
  initialCoalition_val_eq :
    initialCoalition.val = selection.family.terminal.val
  sourceProfile_eq : ∀ rank,
    origin.sourceProfile rank =
      quittingLiteralPureRootCoalitionProfile reward
        (ConcentratedCollisionFourRole.packetProfile actualizer.packet
          (endpointRank rank))
        (actualizer.packet.mark (endpointRank rank)) initialCoalition
  endpointProfile_eq : ∀ rank,
    origin.endpointProfile rank =
      quittingLiteralPureRootCoalitionProfile reward
        (ConcentratedCollisionFourRole.packetProfile actualizer.packet
          (endpointRank rank))
        (actualizer.packet.mark (endpointRank rank)) origin.markedCoalition
  mark_eq : ∀ rank,
    origin.mark rank = actualizer.packet.mark (endpointRank rank)
  mover_eq : origin.mover = mover
  observer_eq : origin.observer = observer
  markedCoalition_val_eq :
    origin.markedCoalition.val = endpoint.routedTerminal.val
  lambda_eq : origin.lambda = actualizer.packet.resolution
  moverGap_eq : origin.moverGap = actualizer.packet.resolution ^ 2 *
    quittingTerminalSemanticDebtSum source.point.1 / 8
  charge_eq : origin.charge = actualizer.packet.resolution ^ 2 *
    quittingTerminalSemanticDebtSum source.point.1 / 128
  endpointPoint_eq : origin.endpointPoint = endpoint.targetPoint
  sourceSemantic_tendsto : Tendsto (fun rank ↦
    quittingTerminalSemanticPair reward (origin.sourceProfile rank)) atTop
      (nhds endpoint.sourceLimit)

namespace FinFourMinimumResponseCanonicalEndpointRiseOrigin

variable
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}
  {sourcePacket : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}
  {selection : FinFourNormalizedReturnSelection sourcePacket}
  {point : QuittingMarkedPairDecoration (Fin 4)}
  {actualizer : QuittingMarkedPairMinimumReturnActualizer selection.family
    source.point.1 selection.massDensity selection.gainDensity point}
  {mover observer : Fin 4}
  {endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1
    actualizer.packet mover observer}

/-- The actual three-role endpoint gives twice the decoder charge: its
observer debt change has the sharper `rho² D_*/64` floor. -/
theorem two_mul_charge_le_endpointDebtChange
    (canonical : FinFourMinimumResponseCanonicalEndpointRiseOrigin endpoint) :
    2 * canonical.origin.charge ≤
      quittingTerminalSemanticDebtChange endpoint.sourceLimit
        endpoint.targetPoint.1 observer := by
  rw [canonical.charge_eq]
  convert endpoint.finFour_recipient_rise using 1
  all_goals ring

/-- The endpoint observer itself has the full `rho² D_*/64` debt floor,
which is stronger than positivity by the decoder's half-sized charge. -/
theorem endpointObserverDebt_floor
    (_canonical : FinFourMinimumResponseCanonicalEndpointRiseOrigin endpoint) :
    actualizer.packet.resolution ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 64 ≤
      quittingTerminalSemanticDebt endpoint.targetPoint.1 observer := by
  have hsource : 0 ≤
      quittingTerminalSemanticDebt endpoint.sourceLimit observer :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      endpoint.source_mem observer
  have hrise := endpoint.finFour_recipient_rise
  unfold quittingTerminalSemanticDebtChange at hrise
  linarith

/-- The exact marked mass scale is the packet resolution. -/
theorem resolution_le_markedStageMass
    (canonical : FinFourMinimumResponseCanonicalEndpointRiseOrigin endpoint)
    (rank : ℕ) :
    actualizer.packet.resolution ≤
      quittingStageCoalitionMass reward (canonical.origin.endpointProfile rank)
        (canonical.origin.mark rank)
        (quittingTerminalOfNonsingletonCoalition
          canonical.origin.markedCoalition) := by
  rw [← canonical.lambda_eq]
  exact canonical.origin.markedStageMass_floor rank

/-- The compiled rectangle keeps the exact resolution selected by the actual
normalized-return packet. -/
theorem compiled_lambda_eq_resolution
    (canonical : FinFourMinimumResponseCanonicalEndpointRiseOrigin endpoint)
    {sequence : FinFourMinimumResponseRectangleSequence canonical.origin}
    (compiled : FinFourMinimumResponseCompiledRectangle sequence) :
    compiled.packet.lambda = actualizer.packet.resolution := by
  rw [compiled.packet_lambda, canonical.lambda_eq]

/-- The horizontal paid edge has the actual endpoint-law floor
`rho² D_*/8`. -/
theorem compiled_moverGap_eq
    (canonical : FinFourMinimumResponseCanonicalEndpointRiseOrigin endpoint)
    {sequence : FinFourMinimumResponseRectangleSequence canonical.origin}
    (compiled : FinFourMinimumResponseCompiledRectangle sequence) :
    compiled.packet.moverGap = actualizer.packet.resolution ^ 2 *
      quittingTerminalSemanticDebtSum source.point.1 / 8 := by
  rw [compiled.packet_moverGap, canonical.moverGap_eq]

/-- The executable vertical response square has the explicit actual-source
floor `7 rho² D_*/1024`. -/
theorem compiled_crossFloor_eq
    (canonical : FinFourMinimumResponseCanonicalEndpointRiseOrigin endpoint)
    {sequence : FinFourMinimumResponseRectangleSequence canonical.origin}
    (compiled : FinFourMinimumResponseCompiledRectangle sequence) :
    compiled.packet.crossFloor =
      7 * actualizer.packet.resolution ^ 2 *
        quittingTerminalSemanticDebtSum source.point.1 / 1024 := by
  rw [compiled.packet_crossFloor, canonical.charge_eq]
  ring

end FinFourMinimumResponseCanonicalEndpointRiseOrigin

namespace ConcentratedCollisionThreeRoleEndpointLaw

variable
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}
  {sourcePacket : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}
  {selection : FinFourNormalizedReturnSelection sourcePacket}
  {point : QuittingMarkedPairDecoration (Fin 4)}
  {actualizer : QuittingMarkedPairMinimumReturnActualizer selection.family
    source.point.1 selection.massDensity selection.gainDensity point}
  {mover observer : Fin 4}
  (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1
    actualizer.packet mover observer)

/-- Actual endpoint-law minimum regeneration supplies a stopping-law
endpoint-rise origin whenever the routed endpoint remains nonsingleton.  The
only extra argument is the table bound already used to build the hard
residual; no row, response, atom, or compact point is supplied. -/
theorem nonempty_canonicalMinimumResponseEndpointRiseOrigin
    (regeneration : FinFourThreeRoleMinimumTargetRegeneration source endpoint)
    (hroutedCard : 1 < endpoint.routedTerminal.val.card)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    Nonempty (FinFourMinimumResponseCanonicalEndpointRiseOrigin endpoint) := by
  classical
  have hmarkedCard : selection.family.terminal.val.card = 2 := by
    change sourcePacket.movingTerminal.val.card = 2
    exact sourcePacket.movingTerminal_card
  let marked : QuittingNonsingletonCoalition (Fin 4) :=
    ⟨selection.family.terminal.val, by omega⟩
  let routed : QuittingNonsingletonCoalition (Fin 4) :=
    ⟨endpoint.routedTerminal.val, hroutedCard⟩
  let rawProfile : ℕ → (quittingGame reward).BehaviorProfile := fun rank =>
    ConcentratedCollisionFourRole.packetProfile actualizer.packet
      (endpoint.ranks rank)
  let stage : ℕ → ℕ := fun rank =>
    actualizer.packet.mark (endpoint.ranks rank)
  have hrawRoot : ∀ rank,
      quittingProfileLiveRoot reward (rawProfile rank) (stage rank) =
        fun who => PMF.pure
          (quittingCoalitionAction selection.family.terminal.val who) := by
    intro rank
    simpa only [rawProfile, stage,
      ConcentratedCollisionFourRole.packetProfile,
      QuittingMarkedPairMinimumReturnActualizer.packet, id_eq] using
        actualizer.finFour_markedRoot_eq_pureTerminal (endpoint.ranks rank)
  let pureSource : ℕ → (quittingGame reward).BehaviorProfile := fun rank =>
    quittingLiteralPureRootCoalitionProfile reward (rawProfile rank)
      (stage rank) marked
  have hpureSourceRoot : ∀ rank,
      quittingProfileLiveRoot reward (pureSource rank) =
        quittingProfileLiveRoot reward (rawProfile rank) := by
    intro rank
    funext time
    by_cases htime : time = stage rank
    · subst time
      rw [show quittingProfileLiveRoot reward (pureSource rank) (stage rank) =
          fun who => PMF.pure
            (quittingCoalitionAction selection.family.terminal.val who) by
        exact quittingProfileLiveRoot_literalPureRootProfile_self reward
          (rawProfile rank) (stage rank) _]
      exact (hrawRoot rank).symm
    · exact quittingProfileLiveRoot_literalPureRootProfile_of_ne reward
        (rawProfile rank) (stage rank) time _ htime
  have hpureSourceSem : ∀ rank,
      quittingTerminalSemanticPair reward (pureSource rank) =
        quittingTerminalSemanticPair reward (rawProfile rank) := fun rank =>
    quittingTerminalSemanticPair_eq_of_liveRoot_eq reward _ _
      (hpureSourceRoot rank)
  have hpureSourceLaw : ∀ rank,
      quittingTerminalOutcomeMass reward (pureSource rank) =
        quittingTerminalOutcomeMass reward (rawProfile rank) := fun rank =>
    funext fun outcome =>
      quittingTerminalOutcomeMass_eq_of_profileLiveRoot_eq reward reward _ _
        (hpureSourceRoot rank) outcome
  let replacement : ℕ → (quittingGame reward).BehaviorStrategy mover :=
    fun rank => quittingLiteralOneDateOverride (pureSource rank mover)
      (stage rank) endpoint.endpointAction
  let literalEndpoint : ℕ → (quittingGame reward).BehaviorProfile := fun rank =>
    Function.update (pureSource rank) mover (replacement rank)
  have hliteralEndpoint : ∀ rank,
      literalEndpoint rank = quittingLiteralPureRootCoalitionProfile reward
        (pureSource rank) (stage rank) routed := by
    intro rank
    calc
      literalEndpoint rank =
          quittingLiteralPureRootCoalitionProfile reward (rawProfile rank)
            (stage rank) routed := by
        exact quittingLiteralPureRootCoalitionProfile_update_eq_routed reward
          (rawProfile rank) (stage rank) marked mover endpoint.endpointAction
            routed endpoint.routedTerminal_eq
      _ = quittingLiteralPureRootCoalitionProfile reward (pureSource rank)
          (stage rank) routed := by
        exact (quittingLiteralPureRootProfile_absorb (rawProfile rank)
          (stage rank) (quittingCoalitionAction marked.1)
            (quittingCoalitionAction routed.1)).symm
  have hliteralCanonicalRoot : ∀ rank,
      quittingProfileLiveRoot reward (literalEndpoint rank) =
        quittingProfileLiveRoot reward
          (ConcentratedCollisionFourRole.targetProfile reward (rawProfile rank)
            (stage rank) mover) := by
    intro rank
    rw [show literalEndpoint rank =
        quittingLiteralOneDateProfile reward (pureSource rank) mover
          (stage rank) endpoint.endpointAction by rfl]
    rw [quittingProfileLiveRoot_literalOneDateProfile_eq_canonical]
    have haction : ConcentratedCollisionFourRole.action reward
        (rawProfile rank) (stage rank) mover = endpoint.endpointAction := by
      exact endpoint.endpointAction_eq rank
    rw [ConcentratedCollisionFourRole.targetProfile, haction]
    rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
      quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
      quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation,
      quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation,
      hpureSourceRoot rank]
  have hliteralCanonicalSem : ∀ rank,
      quittingTerminalSemanticPair reward (literalEndpoint rank) =
        quittingTerminalSemanticPair reward
          (ConcentratedCollisionFourRole.targetProfile reward (rawProfile rank)
            (stage rank) mover) := fun rank =>
    quittingTerminalSemanticPair_eq_of_liveRoot_eq reward _ _
      (hliteralCanonicalRoot rank)
  have hliteralCanonicalLaw : ∀ rank,
      quittingTerminalOutcomeMass reward (literalEndpoint rank) =
        quittingTerminalOutcomeMass reward
          (ConcentratedCollisionFourRole.targetProfile reward (rawProfile rank)
            (stage rank) mover) := fun rank =>
    funext fun outcome =>
      quittingTerminalOutcomeMass_eq_of_profileLiveRoot_eq reward reward _ _
        (hliteralCanonicalRoot rank) outcome
  have hsourceDebt : Tendsto (fun rank =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (rawProfile rank)) observer)
      atTop (nhds (quittingTerminalSemanticDebt endpoint.sourceLimit observer)) := by
    exact (continuous_quittingTerminalSemanticDebt observer).tendsto
      endpoint.sourceLimit |>.comp endpoint.source_tendsto
  have htargetDebt : Tendsto (fun rank =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (ConcentratedCollisionFourRole.targetProfile reward (rawProfile rank)
            (stage rank) mover)) observer) atTop
      (nhds (quittingTerminalSemanticDebt endpoint.targetPoint.1 observer)) := by
    have hprojection : Continuous
        (fun point : QuittingTerminalSemanticLawPoint (Fin 4) =>
          quittingTerminalSemanticDebt point.1 observer) :=
      (continuous_quittingTerminalSemanticDebt observer).comp continuous_fst
    exact hprojection.tendsto endpoint.targetPoint |>.comp
      endpoint.target_joint_tendsto
  have hchange : Tendsto (fun rank =>
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (ConcentratedCollisionFourRole.targetProfile reward (rawProfile rank)
              (stage rank) mover)) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (rawProfile rank)) observer)
      atTop (nhds (quittingTerminalSemanticDebtChange endpoint.sourceLimit
        endpoint.targetPoint.1 observer)) := by
    simpa only [quittingTerminalSemanticDebtChange] using
      htargetDebt.sub hsourceDebt
  let riseFloor := actualizer.packet.resolution ^ 2 *
    quittingTerminalSemanticDebtSum source.point.1 / 64
  let charge := riseFloor / 2
  have hriseFloorPos : 0 < riseFloor := by
    dsimp only [riseFloor]
    exact div_pos
      (mul_pos (sq_pos_of_pos actualizer.packet.resolution_pos)
        source.minimumDebt_pos) (by norm_num)
  have hchargePos : 0 < charge := half_pos hriseFloorPos
  have hchargeLt : charge <
      quittingTerminalSemanticDebtChange endpoint.sourceLimit
        endpoint.targetPoint.1 observer := by
    exact (half_lt_self hriseFloorPos).trans_le endpoint.finFour_recipient_rise
  have heventually : ∀ᶠ rank in atTop, charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (ConcentratedCollisionFourRole.targetProfile reward (rawProfile rank)
              (stage rank) mover)) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (rawProfile rank)) observer :=
    (hchange.eventually_const_lt hchargeLt).mono fun _ h => h.le
  obtain ⟨start, hstart⟩ := eventually_atTop.1 heventually
  let select : ℕ → ℕ := fun rank => rank + start
  have hselect : StrictMono select := by
    intro first second hlt
    exact Nat.add_lt_add_right hlt start
  have hstageMass : ∀ rank,
      actualizer.packet.resolution ≤
        quittingStageCoalitionMass reward (literalEndpoint (select rank))
          (stage (select rank)) (quittingTerminalOfNonsingletonCoalition routed) := by
    intro rank
    calc
      actualizer.packet.resolution ≤
          quittingStageCoalitionMass reward (rawProfile (select rank))
            (stage (select rank)) selection.family.terminal :=
        endpoint.resolution_le_sourceMarkedStageMass (select rank)
      _ ≤ quittingLiveMass reward (rawProfile (select rank))
            (stage (select rank)) :=
        quittingStageCoalitionMass_le_liveMass reward _ _ _
      _ = quittingLiveMass reward (pureSource (select rank))
            (stage (select rank)) := by
        exact (quittingLiveMass_literalPureRootProfile_eq reward
          (rawProfile (select rank)) (stage (select rank)) _).symm
      _ = quittingStageCoalitionMass reward (literalEndpoint (select rank))
            (stage (select rank))
            (quittingTerminalOfNonsingletonCoalition routed) := by
        rw [hliteralEndpoint]
        exact (quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass
          reward (pureSource (select rank)) (stage (select rank)) routed).symm
  have hmoverGain : ∀ rank,
      actualizer.packet.resolution ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 8 ≤
        quittingTerminalPayoff reward (literalEndpoint (select rank)) mover -
          quittingTerminalPayoff reward (pureSource (select rank)) mover := by
    intro rank
    have hgain := (endpoint.transfer (select rank)).gain_globalFloor
    have hcanonical : actualizer.packet.resolution ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 8 ≤
        ConcentratedCollisionFourRole.gain reward (rawProfile (select rank))
          (stage (select rank)) mover := by
      rw [show (endpoint.transfer (select rank)).mover = mover from
        endpoint.transfer_mover_eq (select rank)] at hgain
      convert hgain using 1
      all_goals norm_num
    unfold ConcentratedCollisionFourRole.gain at hcanonical
    rw [show quittingTerminalPayoff reward (literalEndpoint (select rank)) mover =
        quittingTerminalPayoff reward
          (ConcentratedCollisionFourRole.targetProfile reward
            (rawProfile (select rank)) (stage (select rank)) mover) mover by
      exact congrArg (fun pair : QuittingTerminalSemanticPair (Fin 4) => pair.1 mover)
        (hliteralCanonicalSem (select rank))]
    rw [show quittingTerminalPayoff reward (pureSource (select rank)) mover =
        quittingTerminalPayoff reward (rawProfile (select rank)) mover by
      exact congrArg (fun pair : QuittingTerminalSemanticPair (Fin 4) => pair.1 mover)
        (hpureSourceSem (select rank))]
    exact hcanonical
  have hendpointTendsto : Tendsto (fun rank =>
      (quittingTerminalSemanticPair reward (literalEndpoint (select rank)),
        quittingTerminalOutcomeMass reward (literalEndpoint (select rank))))
      atTop (nhds endpoint.targetPoint) := by
    have hcanonical := endpoint.target_joint_tendsto.comp hselect.tendsto_atTop
    apply hcanonical.congr'
    filter_upwards [] with rank
    apply Prod.ext
    · exact (hliteralCanonicalSem (select rank)).symm
    · exact (hliteralCanonicalLaw (select rank)).symm
  have hendpointDebt : ∀ rank, charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (literalEndpoint (select rank)))
          observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (pureSource (select rank)))
          observer := by
    intro rank
    rw [hliteralCanonicalSem, hpureSourceSem]
    exact hstart (select rank) (Nat.le_add_left start rank)
  have hdebtEq : quittingTerminalSemanticDebtSum endpoint.targetPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1 := by
    calc
      quittingTerminalSemanticDebtSum endpoint.targetPoint.1 =
          quittingTerminalSemanticDebtSum regeneration.next.point.1 := by
        rw [regeneration.next_point_eq]
      _ = quittingTerminalDebtSumInf reward := regeneration.next.debt_eq_inf
      _ = quittingTerminalSemanticDebtSum source.point.1 := source.debt_eq_inf.symm
  have hboundNonneg : 0 ≤ bound := by
    exact (abs_nonneg (reward source.atom.terminal 0)).trans
      (hreward source.atom.terminal 0)
  let origin : FinFourMinimumResponseEndpointRiseOrigin source := {
    sourceProfile := pureSource ∘ select
    mover := mover
    observer := observer
    mover_ne_observer := endpoint.recipient_ne_mover.symm
    replacement := replacement ∘ select
    endpointProfile := literalEndpoint ∘ select
    endpointProfile_eq_update := fun _ => rfl
    mark := stage ∘ select
    markedCoalition := routed
    endpointProfile_eq_literalPureRoot := fun rank =>
      hliteralEndpoint (select rank)
    liveRoot_eq_of_ne := by
      intro rank time htime
      change quittingProfileLiveRoot reward (pureSource (select rank)) time =
        quittingProfileLiveRoot reward (literalEndpoint (select rank)) time
      rw [hliteralEndpoint]
      symm
      exact quittingProfileLiveRoot_literalPureRootProfile_of_ne reward
        (pureSource (select rank)) (stage (select rank)) time _ htime
    lambda := actualizer.packet.resolution
    lambda_pos := actualizer.packet.resolution_pos
    markedStageMass_floor := hstageMass
    moverGap := actualizer.packet.resolution ^ 2 *
      quittingTerminalSemanticDebtSum source.point.1 / 8
    moverGap_pos := div_pos
      (mul_pos (sq_pos_of_pos actualizer.packet.resolution_pos)
        source.minimumDebt_pos) (by norm_num)
    moverGain_floor := hmoverGain
    charge := charge
    charge_pos := hchargePos
    endpointDebtRise := hendpointDebt
    endpointPoint := endpoint.targetPoint
    endpoint_mem := endpoint.target_mem
    endpoint_tendsto := hendpointTendsto
    endpoint_debtSum_eq_source := hdebtEq
    rewardBound := hreward
    bound_nonneg := hboundNonneg
  }
  let endpointRank : ℕ → ℕ := endpoint.ranks ∘ select
  have hsourceSemantic : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward
        (origin.sourceProfile rank)) atTop (nhds endpoint.sourceLimit) := by
    have hraw := endpoint.source_tendsto.comp hselect.tendsto_atTop
    apply hraw.congr'
    filter_upwards [] with rank
    change ConcentratedCollisionFourRole.source reward
        (rawProfile (select rank)) =
      quittingTerminalSemanticPair reward (pureSource (select rank))
    exact (hpureSourceSem (select rank)).symm
  refine ⟨{
    origin := origin
    endpointRank := endpointRank
    endpointRank_strictMono := endpoint.ranks_strictMono.comp hselect
    initialCoalition := marked
    initialCoalition_val_eq := rfl
    sourceProfile_eq := fun _ => rfl
    endpointProfile_eq := ?_
    mark_eq := fun _ => rfl
    mover_eq := rfl
    observer_eq := rfl
    markedCoalition_val_eq := rfl
    lambda_eq := rfl
    moverGap_eq := rfl
    charge_eq := by
      dsimp only [origin, charge, riseFloor]
      ring
    endpointPoint_eq := rfl
    sourceSemantic_tendsto := hsourceSemantic }⟩
  intro rank
  change literalEndpoint (select rank) =
    quittingLiteralPureRootCoalitionProfile reward (rawProfile (select rank))
      (stage (select rank)) routed
  calc
    literalEndpoint (select rank) =
        quittingLiteralPureRootCoalitionProfile reward
          (pureSource (select rank)) (stage (select rank)) routed :=
      hliteralEndpoint (select rank)
    _ = quittingLiteralPureRootCoalitionProfile reward
          (rawProfile (select rank)) (stage (select rank)) routed :=
      quittingLiteralPureRootProfile_absorb (rawProfile (select rank))
        (stage (select rank)) (quittingCoalitionAction marked.1)
          (quittingCoalitionAction routed.1)

/-- Forgetful compatibility view of the canonical endpoint-rise decoder. -/
theorem nonempty_minimumResponseEndpointRiseOrigin
    (regeneration : FinFourThreeRoleMinimumTargetRegeneration source endpoint)
    (hroutedCard : 1 < endpoint.routedTerminal.val.card)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    Nonempty (FinFourMinimumResponseEndpointRiseOrigin source) := by
  obtain ⟨canonical⟩ := endpoint.nonempty_canonicalMinimumResponseEndpointRiseOrigin
    regeneration hroutedCard hreward
  exact ⟨canonical.origin⟩

end ConcentratedCollisionThreeRoleEndpointLaw

/-- Exhaustive actual endpoint decoding.  The rectangle compiler is reached
only after ruling out endpoint ascent, routed singleton, prescribed atom, and
strict response ascent.  Every constructor retains the exact endpoint result
from which its additional data was produced. -/
inductive FinFourMinimumResponseActualEndpointOutcome
    {returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source}
    {lambda : ℝ}
    {sourcePacket : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    {selection : FinFourNormalizedReturnSelection sourcePacket}
    {point : QuittingMarkedPairDecoration (Fin 4)}
    {actualizer : QuittingMarkedPairMinimumReturnActualizer selection.family
      source.point.1 selection.massDensity selection.gainDensity point}
    (result : FinFourThreeRoleRegenerationOrAscent source actualizer.packet) :
    Type where
  | endpointAscent
      (hdebt : quittingTerminalSemanticDebtSum source.point.1 <
        quittingTerminalSemanticDebtSum result.endpoint.targetPoint.1)
  | routedSingleton
      (regeneration : FinFourThreeRoleMinimumTargetRegeneration source
        result.endpoint)
      (hcard : result.endpoint.routedTerminal.val.card = 1)
  | prescribedAtom
      (regeneration : FinFourThreeRoleMinimumTargetRegeneration source
        result.endpoint)
      (canonical : FinFourMinimumResponseCanonicalEndpointRiseOrigin
        result.endpoint)
      (exit : FinFourMinimumResponsePrescribedAtomExit canonical.origin)
  | responseAscent
      (regeneration : FinFourThreeRoleMinimumTargetRegeneration source
        result.endpoint)
      (canonical : FinFourMinimumResponseCanonicalEndpointRiseOrigin
        result.endpoint)
      (sequence : FinFourMinimumResponseRectangleSequence canonical.origin)
      (ascent : FinFourMinimumResponseStrictResponseAscent sequence)
  | compiledRectangle
      (regeneration : FinFourThreeRoleMinimumTargetRegeneration source
        result.endpoint)
      (canonical : FinFourMinimumResponseCanonicalEndpointRiseOrigin
        result.endpoint)
      (sequence : FinFourMinimumResponseRectangleSequence canonical.origin)
      (compiled : FinFourMinimumResponseCompiledRectangle sequence)

namespace FinFourThreeRoleRegenerationOrAscent

variable
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}
  {sourcePacket : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}
  {selection : FinFourNormalizedReturnSelection sourcePacket}
  {point : QuittingMarkedPairDecoration (Fin 4)}
  {actualizer : QuittingMarkedPairMinimumReturnActualizer selection.family
    source.point.1 selection.massDensity selection.gainDensity point}

/-- Decode one actual equality-arm endpoint without supplying a leaf
certificate.  The card-one route is returned before the stopping-law
decoder; in the remaining route, the prescribed-atom and response-ascent
exits stay public. -/
theorem nonempty_minimumResponseActualEndpointOutcome
    (result : FinFourThreeRoleRegenerationOrAscent source actualizer.packet)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    Nonempty (FinFourMinimumResponseActualEndpointOutcome result) := by
  rcases result.outcome with hascent | hregeneration
  · exact ⟨FinFourMinimumResponseActualEndpointOutcome.endpointAscent
      hascent⟩
  · obtain ⟨regeneration⟩ := hregeneration
    have hcardPos : 0 < result.endpoint.routedTerminal.val.card :=
      Finset.card_pos.mpr result.endpoint.routedTerminal.property
    by_cases hcard : result.endpoint.routedTerminal.val.card = 1
    · exact ⟨FinFourMinimumResponseActualEndpointOutcome.routedSingleton
        regeneration hcard⟩
    · have hcardTwo : 1 < result.endpoint.routedTerminal.val.card := by omega
      obtain ⟨canonical⟩ :=
        result.endpoint.nonempty_canonicalMinimumResponseEndpointRiseOrigin
          regeneration hcardTwo hreward
      rcases canonical.origin.prescribedAtom_or_rectangleSequence with
        ⟨⟨exit⟩⟩ | ⟨⟨sequence⟩⟩
      · exact ⟨FinFourMinimumResponseActualEndpointOutcome.prescribedAtom
          regeneration canonical exit⟩
      · rcases sequence.strictResponseAscent_or_compiledRectangle with
          ⟨⟨ascent⟩⟩ | ⟨⟨compiled⟩⟩
        · exact ⟨FinFourMinimumResponseActualEndpointOutcome.responseAscent
            regeneration canonical sequence ascent⟩
        · exact
            ⟨FinFourMinimumResponseActualEndpointOutcome.compiledRectangle
              regeneration canonical sequence compiled⟩

end FinFourThreeRoleRegenerationOrAscent

/-- Exhaustive source-attached output of the normalized-return capstone.  The
strict inert branch remains unchanged.  The equality branch retains its
actualizer, the exact minimum identity, its endpoint result, and the full
endpoint decoder outcome. -/
inductive FinFourMinimumResponseActualSourceOutcome
    {returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source}
    {lambda : ℝ}
    (capstone : FinFourNormalizedReturnSourceCapstone returnSource lambda) :
    Type where
  | strictInert
      (hdebt : quittingTerminalSemanticDebtSum source.point.1 <
        capstone.normalized.point.wholeDebt)
      (hroot : ∀ root : Fin 4 → PMF Bool,
        IsεQuittingRootNash reward capstone.normalized.point.whole.1.2 0 root ↔
          root = (quittingAllContinueRoot : Fin 4 → PMF Bool))
  | decoded
      (actualizer : QuittingMarkedPairMinimumReturnActualizer
        capstone.normalized.selection.family source.point.1
          capstone.normalized.selection.massDensity
            capstone.normalized.selection.gainDensity
              capstone.normalized.point)
      (hminimum : capstone.normalized.point.wholeDebt =
        quittingTerminalSemanticDebtSum source.point.1)
      (result : FinFourThreeRoleRegenerationOrAscent source actualizer.packet)
      (outcome : FinFourMinimumResponseActualEndpointOutcome result)

namespace FinFourNormalizedReturnSourceCapstone

/-- Actual atlas decoder from the normalized-return capstone.  It constructs
all finite labels, stopping-law choices, compact response points, and route
refinements internally. -/
theorem nonempty_minimumResponseActualSourceOutcome
    {returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source}
    {lambda : ℝ}
    (capstone : FinFourNormalizedReturnSourceCapstone returnSource lambda)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    Nonempty (FinFourMinimumResponseActualSourceOutcome capstone) := by
  rcases capstone.regenerationOrAscent_or_strictInert with
      ⟨actualizer, hminimum, ⟨result⟩⟩ | ⟨hdebt, hroot⟩
  · obtain ⟨outcome⟩ :=
      result.nonempty_minimumResponseActualEndpointOutcome hreward
    exact ⟨FinFourMinimumResponseActualSourceOutcome.decoded actualizer
      hminimum result outcome⟩
  · exact ⟨FinFourMinimumResponseActualSourceOutcome.strictInert
      hdebt hroot⟩

end FinFourNormalizedReturnSourceCapstone

end GameTheory
