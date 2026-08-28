/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.Source
import Research.Quitting.MinimumResponseChordLaw
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPureTimeRectangleDisintegration

/-!
# Source-attached Fin4 minimum response chords

This module packages a fixed response rectangle over one
`FinFourMinimumAtomProducer`, extracts every proper executable response chord
on literal further subsequences, and regenerates same-law minimum sources at
the response endpoint and chord point.

The pre-route packet retains the actual marked-row floor and positive
complete-law rectangle atom.  The construction itself freezes the finite
response mode and routed terminal, then derives the post-response row floor
from literal at-or-after-mark no-loss routing.  It does not assert renewable
support rank, near-minimality of the displayed rows, or a uniform-equilibrium
payoff.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Actual response-rectangle data before the finite response mode is frozen.
This is precisely the source-facing passport: it retains the literal marked
row, its positive mass floor, the positive complete-law rectangle atom, and
one common endpoint/response joint-law subsequence.  It assumes no routed row
certificate. -/
structure FinFourMinimumResponseRectanglePacket
    (source : FinFourMinimumAtomProducer reward bound) where
  sourceProfile : ℕ → (quittingGame reward).BehaviorProfile
  mover : Fin 4
  observer : Fin 4
  mover_ne_observer : mover ≠ observer
  replacement : ℕ → (quittingGame reward).BehaviorStrategy mover
  responseChoice : ℕ → Option ℕ
  mark : ℕ → ℕ
  markedCoalition : QuittingNonsingletonCoalition (Fin 4)
  endpointProfile : ℕ → (quittingGame reward).BehaviorProfile
  endpointProfile_eq_update : ∀ rank,
    endpointProfile rank =
      Function.update (sourceProfile rank) mover (replacement rank)
  endpointProfile_eq_literalPureRoot : ∀ rank,
    endpointProfile rank = quittingLiteralPureRootCoalitionProfile reward
      (sourceProfile rank) (mark rank) markedCoalition
  liveRoot_eq_of_ne : ∀ rank time, time ≠ mark rank →
    quittingProfileLiveRoot reward (sourceProfile rank) time =
      quittingProfileLiveRoot reward (endpointProfile rank) time
  responseAtom : {S : Finset (Fin 4) // S.Nonempty}
  eta : ℝ
  eta_pos : 0 < eta
  responseAtom_floor : ∀ rank,
    eta ≤
      (quittingTerminalOutcomeMass reward
          (Function.update (endpointProfile rank) observer
            (quittingPureTimeBehaviorStrategy reward observer
              (responseChoice rank))) (some responseAtom) -
        quittingTerminalOutcomeMass reward
          (Function.update (sourceProfile rank) observer
            (quittingPureTimeBehaviorStrategy reward observer
              (responseChoice rank))) (some responseAtom)) *
        reward responseAtom observer
  lambda : ℝ
  lambda_pos : 0 < lambda
  markedStageMass_floor : ∀ rank,
    lambda ≤ quittingStageCoalitionMass reward (endpointProfile rank)
      (mark rank) (quittingTerminalOfNonsingletonCoalition markedCoalition)
  moverGap : ℝ
  moverGap_pos : 0 < moverGap
  moverGain_floor : ∀ rank,
    moverGap ≤
      quittingTerminalPayoff reward (endpointProfile rank) mover -
        quittingTerminalPayoff reward (sourceProfile rank) mover
  crossFloor : ℝ
  crossFloor_pos : 0 < crossFloor
  responseCross_floor : ∀ rank,
    crossFloor ≤
      (quittingTerminalPayoff reward
          (Function.update (endpointProfile rank) observer
            (quittingPureTimeBehaviorStrategy reward observer
              (responseChoice rank))) observer -
        quittingTerminalPayoff reward (endpointProfile rank) observer) -
      (quittingTerminalPayoff reward
          (Function.update (sourceProfile rank) observer
            (quittingPureTimeBehaviorStrategy reward observer
              (responseChoice rank))) observer -
        quittingTerminalPayoff reward (sourceProfile rank) observer)
  rewardBound : ∀ terminal who, |reward terminal who| ≤ bound
  bound_nonneg : 0 ≤ bound
  commonSubsequence : ℕ → ℕ
  commonSubsequence_strictMono : StrictMono commonSubsequence
  endpointPoint : QuittingTerminalSemanticLawPoint (Fin 4)
  responsePoint : QuittingTerminalSemanticLawPoint (Fin 4)
  endpoint_tendsto : Tendsto (fun rank =>
    let index := commonSubsequence rank
    (quittingTerminalSemanticPair reward (endpointProfile index),
      quittingTerminalOutcomeMass reward (endpointProfile index)))
    atTop (nhds endpointPoint)
  response_tendsto : Tendsto (fun rank =>
    let index := commonSubsequence rank
    let profile := Function.update (endpointProfile index) observer
      (quittingPureTimeBehaviorStrategy reward observer (responseChoice index))
    (quittingTerminalSemanticPair reward profile,
      quittingTerminalOutcomeMass reward profile))
    atTop (nhds responsePoint)
  endpoint_mem : endpointPoint ∈ quittingTerminalSemanticLawCarrier reward
  response_mem : responsePoint ∈ quittingTerminalSemanticLawCarrier reward
  endpoint_debtSum_eq_source :
    quittingTerminalSemanticDebtSum endpointPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1
  response_debtSum_eq_source :
    quittingTerminalSemanticDebtSum responsePoint.1 =
      quittingTerminalSemanticDebtSum source.point.1

/-- A pre-route packet after internally freezing the finite response mode.
The routed terminal is the corresponding no-loss toggle of the same marked
coalition. -/
structure FinFourMinimumResponseRectangle
    (source : FinFourMinimumAtomProducer reward bound)
    extends FinFourMinimumResponseRectanglePacket source where
  routeRefinement : ℕ → ℕ
  routeRefinement_strictMono : StrictMono routeRefinement
  routedAction : Bool
  routedTerminal : {S : Finset (Fin 4) // S.Nonempty}
  routedTerminal_eq : routedTerminal.val =
    quittingPureEndpointRoutedCoalition markedCoalition.1 observer routedAction
  responseMode_eq : ∀ rank,
    match responseChoice (commonSubsequence (routeRefinement rank)) with
    | some stop =>
        routedAction = decide
          (stop = mark (commonSubsequence (routeRefinement rank)))
    | none => routedAction = false

namespace FinFourMinimumResponseRectanglePacket

variable (packet : FinFourMinimumResponseRectanglePacket source)

/-- The deterministic action taken by the decoded pure-time response at the
marked row. -/
def responseModeAt (rank : ℕ) : Bool :=
  match packet.responseChoice rank with
  | some stop => decide (stop = packet.mark rank)
  | none => false

/-- The marked coalition routed through the decoded response action. -/
def routedTerminalAt (rank : ℕ) :
    {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨quittingPureEndpointRoutedCoalition packet.markedCoalition.1
      packet.observer (packet.responseModeAt rank),
    quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
      packet.markedCoalition.1 packet.observer (packet.responseModeAt rank)
      packet.markedCoalition.2⟩

/-- Every actual pre-route packet yields a routed rectangle.  Only the finite
Boolean response mode is selected: the selected ranks are a literal strict
refinement of the packet's common joint-law subsequence, and the terminal is
the corresponding toggle of the same marked coalition. -/
theorem nonempty_minimumResponseRectangle
    (packet : FinFourMinimumResponseRectanglePacket source) :
    Nonempty (FinFourMinimumResponseRectangle source) := by
  let label : ℕ → Bool := fun rank =>
    packet.responseModeAt (packet.commonSubsequence rank)
  obtain ⟨fixed, hfixedInfinite⟩ := Finite.exists_infinite_fiber label
  have hfrequent : ∃ᶠ rank in atTop, label rank = fixed := by
    rw [Nat.frequently_atTop_iff_infinite]
    have hinfinite : (label ⁻¹' ({fixed} : Set Bool)).Infinite :=
      Set.infinite_coe_iff.mp hfixedInfinite
    convert hinfinite using 1
    ext rank
    simp
  obtain ⟨refine, hrefine, hfixed⟩ :=
    extraction_of_frequently_atTop hfrequent
  let routed : {S : Finset (Fin 4) // S.Nonempty} :=
    ⟨quittingPureEndpointRoutedCoalition packet.markedCoalition.1
        packet.observer fixed,
      quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
        packet.markedCoalition.1 packet.observer fixed
        packet.markedCoalition.2⟩
  refine ⟨{
    toFinFourMinimumResponseRectanglePacket := packet
    routeRefinement := refine
    routeRefinement_strictMono := hrefine
    routedAction := fixed
    routedTerminal := routed
    routedTerminal_eq := rfl
    responseMode_eq := ?_ }⟩
  intro rank
  have hmode := (hfixed rank).symm
  change fixed = packet.responseModeAt
    (packet.commonSubsequence (refine rank)) at hmode
  cases hchoice : packet.responseChoice
      (packet.commonSubsequence (refine rank)) with
  | none => simpa only [responseModeAt, hchoice] using hmode
  | some stop => simpa only [responseModeAt, hchoice] using hmode

end FinFourMinimumResponseRectanglePacket

/-- Repackage any same-fibre positive-law point as a new minimum source while
retaining the exact hard residual and displayed law coordinate. -/
def FinFourMinimumAtomProducer.regeneratedAtLawPoint
    (source : FinFourMinimumAtomProducer reward bound)
    (point : QuittingTerminalSemanticLawPoint (Fin 4))
    (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hdebt : quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalSemanticDebtSum source.point.1)
    (hmass : 0 < point.2 (some terminal)) :
    FinFourMinimumAtomProducer reward bound := by
  let atom : QuittingMinimumLawCausalSuffixAtom reward point := {
    terminal := terminal
    terminalMass_pos := hmass
    chronology :=
      exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom
        reward point terminal hpoint hmass source.inf_pos
          (hdebt.trans source.debt_eq_inf)
  }
  exact {
    residual := source.residual
    point := point
    point_mem := hpoint
    semantic_mem := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
    minimum := by
      intro candidate hcandidate
      rw [hdebt]
      exact source.minimum candidate hcandidate
    inf_pos := source.inf_pos
    debt_eq_inf := hdebt.trans source.debt_eq_inf
    atom := atom
  }

namespace FinFourMinimumResponseRectangle

variable (rectangle : FinFourMinimumResponseRectangle source)

/-- The lower-left response endpoint. -/
def sourceResponseProfile (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  Function.update (rectangle.sourceProfile rank) rectangle.observer
    (quittingPureTimeBehaviorStrategy reward rectangle.observer
      (rectangle.responseChoice rank))

/-- The upper-right response endpoint. -/
def endpointResponseProfile (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  Function.update (rectangle.endpointProfile rank) rectangle.observer
    (quittingPureTimeBehaviorStrategy reward rectangle.observer
      (rectangle.responseChoice rank))

/-- The common subsequence after the finite routed label and response mode have
also been frozen. -/
def routedSubsequence (rank : ℕ) : ℕ :=
  rectangle.commonSubsequence (rectangle.routeRefinement rank)

theorem routedSubsequence_strictMono : StrictMono rectangle.routedSubsequence :=
  rectangle.commonSubsequence_strictMono.comp
    rectangle.routeRefinement_strictMono

/-- The positive response-law atom forces every finite response to occur at or
after the marked date. -/
theorem responseChoice_ge_mark (rank stop : ℕ)
    (hchoice : rectangle.responseChoice rank = some stop) :
    rectangle.mark rank ≤ stop := by
  apply responseAtom_pos_imp_pureTime_ge_mark reward
    (rectangle.sourceProfile rank) (rectangle.endpointProfile rank)
    rectangle.observer (rectangle.responseChoice rank) (rectangle.mark rank)
    rectangle.responseAtom rectangle.eta rectangle.eta_pos
  · intro time htime
    exact rectangle.liveRoot_eq_of_ne rank time (Nat.ne_of_lt htime)
  · exact rectangle.responseAtom_floor rank
  · exact hchoice

/-- The selected pure-time response has exactly the frozen Boolean action at
the marked row. -/
theorem responseHazard_eq_routedAction (rank : ℕ) :
    quittingPureTimeHazard
        (rectangle.responseChoice (rectangle.routedSubsequence rank))
        (rectangle.mark (rectangle.routedSubsequence rank)) =
      PMF.pure rectangle.routedAction := by
  rw [quittingPureTimeHazard_eq_pure_responseMode]
  cases hchoice : rectangle.responseChoice
      (rectangle.routedSubsequence rank) with
  | none =>
      have hmode := rectangle.responseMode_eq rank
      simp only [routedSubsequence] at hchoice ⊢
      rw [hchoice] at hmode
      rw [hmode]
  | some stop =>
      have hmode := rectangle.responseMode_eq rank
      simp only [routedSubsequence] at hchoice ⊢
      rw [hchoice] at hmode
      rw [hmode]
      rfl

/-- The post-response routed row retains the actual pre-response marked mass
floor.  This is derived from the positive rectangle atom's at-or-after-mark
chronology and one-coordinate no-loss routing; it is not a stored route
certificate. -/
theorem routedStageMass_floor (rank : ℕ) :
    rectangle.lambda ≤ quittingStageCoalitionMass reward
      (rectangle.endpointResponseProfile (rectangle.routedSubsequence rank))
      (rectangle.mark (rectangle.routedSubsequence rank))
      rectangle.routedTerminal := by
  let index := rectangle.routedSubsequence rank
  let sourceTerminal :=
    quittingTerminalOfNonsingletonCoalition rectangle.markedCoalition
  have hrouted :
      (quittingPureEndpointRoutedCoalition sourceTerminal.val
        rectangle.observer rectangle.routedAction).Nonempty :=
    quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
      rectangle.markedCoalition.1 rectangle.observer rectangle.routedAction
      rectangle.markedCoalition.2
  have hnoLoss := quittingStageCoalitionMass_le_update_pureTime_routed
    reward (rectangle.endpointProfile index) rectangle.observer
    (rectangle.responseChoice index) (rectangle.mark index) sourceTerminal
    rectangle.routedAction
    (fun stop hstop ↦ rectangle.responseChoice_ge_mark index stop hstop)
    (rectangle.responseHazard_eq_routedAction rank) hrouted
  have hterminal :
      (⟨quittingPureEndpointRoutedCoalition sourceTerminal.val
          rectangle.observer rectangle.routedAction, hrouted⟩ :
        {S : Finset (Fin 4) // S.Nonempty}) = rectangle.routedTerminal := by
    apply Subtype.ext
    exact rectangle.routedTerminal_eq.symm
  rw [hterminal] at hnoLoss
  exact (rectangle.markedStageMass_floor index).trans hnoLoss

/-- The endpoint response changes only the fixed observer. -/
theorem endpointResponseProfile_eq_of_ne (rank : ℕ) (other : Fin 4)
    (hne : other ≠ rectangle.observer) :
    rectangle.endpointResponseProfile rank other =
      rectangle.endpointProfile rank other := by
  simp [endpointResponseProfile, Function.update_of_ne hne]

/-- The source response changes only the same fixed observer. -/
theorem sourceResponseProfile_eq_of_ne (rank : ℕ) (other : Fin 4)
    (hne : other ≠ rectangle.observer) :
    rectangle.sourceResponseProfile rank other =
      rectangle.sourceProfile rank other := by
  simp [sourceResponseProfile, Function.update_of_ne hne]

/-- The upper response point keeps the frozen routed terminal with at least
the original unconditional marked mass. -/
theorem lambda_le_responsePoint_terminalMass :
    rectangle.lambda ≤ rectangle.responsePoint.2 (some rectangle.routedTerminal) := by
  have hlimit : Tendsto (fun rank =>
      quittingTerminalOutcomeMass reward
        (rectangle.endpointResponseProfile (rectangle.routedSubsequence rank))
        (some rectangle.routedTerminal)) atTop
      (nhds (rectangle.responsePoint.2 (some rectangle.routedTerminal))) := by
    have hresponse := rectangle.response_tendsto.comp
      rectangle.routeRefinement_strictMono.tendsto_atTop
    exact (((continuous_apply (some rectangle.routedTerminal)).comp
      continuous_snd).tendsto rectangle.responsePoint).comp hresponse
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlimit
  intro rank
  have hrow := (rectangle.routedStageMass_floor rank).trans
    (quittingStageCoalitionMass_le_terminalOutcomeMass reward
      (rectangle.endpointResponseProfile (rectangle.routedSubsequence rank))
      (rectangle.mark (rectangle.routedSubsequence rank))
      rectangle.routedTerminal)
  simpa only [endpointResponseProfile, routedSubsequence] using hrow

theorem responsePoint_terminalMass_pos :
    0 < rectangle.responsePoint.2 (some rectangle.routedTerminal) :=
  rectangle.lambda_pos.trans_le rectangle.lambda_le_responsePoint_terminalMass

/-- The response endpoint remains on the exact incoming global-minimum fibre. -/
theorem responsePoint_minimum :
    ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum rectangle.responsePoint.1 ≤
        quittingTerminalSemanticDebtSum candidate := by
  intro candidate hcandidate
  rw [rectangle.response_debtSum_eq_source]
  exact source.minimum candidate hcandidate

/-- Same-law source regenerated at the fixed response endpoint. -/
def responseSource : FinFourMinimumAtomProducer reward bound :=
  source.regeneratedAtLawPoint rectangle.responsePoint rectangle.routedTerminal
    rectangle.response_mem rectangle.response_debtSum_eq_source
    rectangle.responsePoint_terminalMass_pos

theorem responseSource_residual_eq :
    rectangle.responseSource.residual = source.residual := rfl

theorem responseSource_point_eq :
    rectangle.responseSource.point = rectangle.responsePoint := rfl

theorem responseSource_terminal_eq :
    rectangle.responseSource.atom.terminal = rectangle.routedTerminal := rfl

end FinFourMinimumResponseRectangle

/-! ## Proper chord extraction and regeneration -/

/-- One proper response chord on a literal further subsequence of the fixed
routed subsequence.  The generic geometry and both regenerated sources retain
the same input producer and hard residual. -/
structure FinFourMinimumResponseChord
    (source : FinFourMinimumAtomProducer reward bound)
    (rectangle : FinFourMinimumResponseRectangle source)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) where
  chordRefinement : ℕ → ℕ
  chordRefinement_strictMono : StrictMono chordRefinement
  chordPoint : QuittingTerminalSemanticLawPoint (Fin 4)
  chord_tendsto : Tendsto (fun rank =>
    let index := rectangle.routedSubsequence (chordRefinement rank)
    let profile := quittingResponseChordProfile reward
      (rectangle.endpointProfile index)
      (rectangle.endpointResponseProfile index) rectangle.observer theta
      htheta0.le htheta1.le
    (quittingTerminalSemanticPair reward profile,
      quittingTerminalOutcomeMass reward profile)) atTop (nhds chordPoint)
  geometry : QuittingMinimumResponseChordLaw reward
  geometry_endpoint_eq : geometry.endpoint = rectangle.endpointPoint
  geometry_response_eq : geometry.response = rectangle.responsePoint
  geometry_chord_eq : geometry.chord = chordPoint
  geometry_theta_eq : geometry.theta = theta
  chordSource : FinFourMinimumAtomProducer reward bound
  chordSource_residual_eq : chordSource.residual = source.residual
  chordSource_point_eq : chordSource.point = chordPoint
  chordSource_terminal_eq : chordSource.atom.terminal = rectangle.routedTerminal

namespace FinFourMinimumResponseChord

variable {theta : ℝ} {htheta0 : 0 < theta} {htheta1 : theta < 1}
  {rectangle : FinFourMinimumResponseRectangle source}
  (chord : FinFourMinimumResponseChord source rectangle theta htheta0 htheta1)

/-- The response source is determined by the rectangle and is not reselected
when a proper chord is extracted. -/
def responseSource
    (_chord : FinFourMinimumResponseChord source rectangle theta htheta0 htheta1) :
    FinFourMinimumAtomProducer reward bound :=
  rectangle.responseSource

theorem responseSource_eq : chord.responseSource = rectangle.responseSource :=
  rfl

/-- The complete selected rank map, exposing both finite refinements. -/
def fullSubsequence (rank : ℕ) : ℕ :=
  rectangle.commonSubsequence
    (rectangle.routeRefinement (chord.chordRefinement rank))

theorem fullSubsequence_eq : chord.fullSubsequence =
    rectangle.commonSubsequence ∘ rectangle.routeRefinement ∘
      chord.chordRefinement := rfl

theorem fullSubsequence_strictMono : StrictMono chord.fullSubsequence :=
  rectangle.commonSubsequence_strictMono.comp
    (rectangle.routeRefinement_strictMono.comp chord.chordRefinement_strictMono)

theorem debtSum_eq_source :
    quittingTerminalSemanticDebtSum chord.chordPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1 := by
  rw [← chord.geometry_chord_eq, chord.geometry.chord_debtSum_eq_endpoint,
    chord.geometry_endpoint_eq, rectangle.endpoint_debtSum_eq_source]

theorem debt_eq_affine (who : Fin 4) :
    quittingTerminalSemanticDebt chord.chordPoint.1 who =
      (1 - theta) *
          quittingTerminalSemanticDebt rectangle.endpointPoint.1 who +
        theta * quittingTerminalSemanticDebt rectangle.responsePoint.1 who := by
  simpa [chord.geometry_endpoint_eq, chord.geometry_response_eq,
    chord.geometry_chord_eq, chord.geometry_theta_eq] using
      chord.geometry.chord_debt_eq_affine who

/-- The chord's complete terminal law is the exact affine combination of the
two retained endpoint laws. -/
theorem terminalLaw_eq_affine (outcome : QuittingTerminalOutcome (Fin 4)) :
    chord.chordPoint.2 outcome =
      (1 - theta) * rectangle.endpointPoint.2 outcome +
        theta * rectangle.responsePoint.2 outcome := by
  simpa [chord.geometry_endpoint_eq, chord.geometry_response_eq,
    chord.geometry_chord_eq, chord.geometry_theta_eq] using
      chord.geometry.chord_law_eq_affine outcome

theorem support_eq_union :
    quittingPositiveDebtSupport chord.chordPoint.1 =
      quittingPositiveDebtSupport rectangle.endpointPoint.1 ∪
        quittingPositiveDebtSupport rectangle.responsePoint.1 := by
  simpa [chord.geometry_endpoint_eq, chord.geometry_response_eq,
    chord.geometry_chord_eq] using chord.geometry.chord_support_eq_union

theorem theta_mul_lambda_le_terminalMass :
    theta * rectangle.lambda ≤
      chord.chordPoint.2 (some rectangle.routedTerminal) := by
  have hresponseFloor : rectangle.lambda ≤
      chord.geometry.response.2 (some rectangle.routedTerminal) := by
    rw [chord.geometry_response_eq]
    exact rectangle.lambda_le_responsePoint_terminalMass
  have hfloor := chord.geometry.theta_mul_le_chord_terminalMass
    rectangle.routedTerminal rectangle.lambda hresponseFloor
  rw [chord.geometry_chord_eq, chord.geometry_theta_eq] at hfloor
  exact hfloor

theorem chord_terminalMass_pos :
    0 < chord.chordPoint.2 (some rectangle.routedTerminal) := by
  exact (mul_pos htheta0 rectangle.lambda_pos).trans_le
    chord.theta_mul_lambda_le_terminalMass

theorem response_support_ssubset_chord_of_killed
    (hendpoint : 0 < quittingTerminalSemanticDebt
      rectangle.endpointPoint.1 rectangle.observer)
    (hresponse : quittingTerminalSemanticDebt
      rectangle.responsePoint.1 rectangle.observer = 0) :
    quittingPositiveDebtSupport rectangle.responsePoint.1 ⊂
      quittingPositiveDebtSupport chord.chordPoint.1 := by
  have hendpoint' : 0 < quittingTerminalSemanticDebt
      chord.geometry.endpoint.1 rectangle.observer := by
    rw [chord.geometry_endpoint_eq]
    exact hendpoint
  have hresponse' : quittingTerminalSemanticDebt
      chord.geometry.response.1 rectangle.observer = 0 := by
    rw [chord.geometry_response_eq]
    exact hresponse
  have hstrict := chord.geometry.response_support_ssubset_chord_of_killed
    rectangle.observer hendpoint' hresponse'
  rw [chord.geometry_response_eq, chord.geometry_chord_eq] at hstrict
  exact hstrict

include chord in
/-- The oriented endpoint comparison is available only when the actual
mover-reset endpoint is maximal in the positive-atom minimum class. -/
theorem response_support_ssubset_endpoint_of_endpoint_maximal
    (hmaximal : IsMaximumSupportMinimumAtomEndpoint reward
      rectangle.endpointPoint)
    (hendpoint : 0 < quittingTerminalSemanticDebt
      rectangle.endpointPoint.1 rectangle.observer)
    (hresponse : quittingTerminalSemanticDebt
      rectangle.responsePoint.1 rectangle.observer = 0) :
    quittingPositiveDebtSupport rectangle.responsePoint.1 ⊂
      quittingPositiveDebtSupport rectangle.endpointPoint.1 := by
  have hmaximal' : IsMaximumSupportMinimumAtomEndpoint reward
      chord.geometry.endpoint := by
    rw [chord.geometry_endpoint_eq]
    exact hmaximal
  have hendpoint' : 0 < quittingTerminalSemanticDebt
      chord.geometry.endpoint.1 rectangle.observer := by
    rw [chord.geometry_endpoint_eq]
    exact hendpoint
  have hresponse' : quittingTerminalSemanticDebt
      chord.geometry.response.1 rectangle.observer = 0 := by
    rw [chord.geometry_response_eq]
    exact hresponse
  have hmass : 0 < chord.geometry.chord.2
      (some rectangle.routedTerminal) := by
    rw [chord.geometry_chord_eq]
    exact chord.chord_terminalMass_pos
  have hstrict :=
    chord.geometry.response_support_ssubset_endpoint_of_endpoint_maximal
      rectangle.routedTerminal hmass hmaximal' rectangle.observer
        hendpoint' hresponse'
  rw [chord.geometry_response_eq, chord.geometry_endpoint_eq] at hstrict
  exact hstrict

theorem chordSource_same_source :
    chord.chordSource.residual = source.residual ∧
      chord.chordSource.point = chord.chordPoint ∧
      chord.chordSource.atom.terminal = rectangle.routedTerminal :=
  ⟨chord.chordSource_residual_eq, chord.chordSource_point_eq,
    chord.chordSource_terminal_eq⟩

/-- Both regenerated objects use the exact incoming hard residual and the
displayed response/chord joint laws. -/
theorem regeneratedSources_same_source :
    chord.responseSource.residual = source.residual ∧
      chord.responseSource.point = rectangle.responsePoint ∧
      chord.responseSource.atom.terminal = rectangle.routedTerminal ∧
      chord.chordSource.residual = source.residual ∧
      chord.chordSource.point = chord.chordPoint ∧
      chord.chordSource.atom.terminal = rectangle.routedTerminal := by
  exact ⟨rectangle.responseSource_residual_eq,
    rectangle.responseSource_point_eq, rectangle.responseSource_terminal_eq,
    chord.chordSource_residual_eq, chord.chordSource_point_eq,
    chord.chordSource_terminal_eq⟩

end FinFourMinimumResponseChord

namespace FinFourMinimumResponseRectangle

variable (rectangle : FinFourMinimumResponseRectangle source)

/-- Every proper parameter produces an actual compact chord cluster on one
further literal refinement, together with exact same-law source regeneration
at the response endpoint and at that chord. -/
theorem nonempty_minimumResponseChord
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    Nonempty
      (FinFourMinimumResponseChord source rectangle theta htheta0 htheta1) := by
  let chordProfile : ℕ → (quittingGame reward).BehaviorProfile := fun rank =>
    let index := rectangle.routedSubsequence rank
    quittingResponseChordProfile reward (rectangle.endpointProfile index)
      (rectangle.endpointResponseProfile index) rectangle.observer theta
        htheta0.le htheta1.le
  let chordPointSeq : ℕ → QuittingTerminalSemanticLawPoint (Fin 4) := fun rank =>
    (quittingTerminalSemanticPair reward (chordProfile rank),
      quittingTerminalOutcomeMass reward (chordProfile rank))
  have hmem : ∀ rank, chordPointSeq rank ∈
      quittingTerminalSemanticLawCarrier reward := fun rank =>
    quittingTerminalSemanticLawPoint_mem_carrier reward (chordProfile rank)
  obtain ⟨chordPoint, hchordMem, refine, hrefine, hchordTendsto⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq hmem
  have hendpointTendsto : Tendsto (fun rank =>
      (quittingTerminalSemanticPair reward
          (rectangle.endpointProfile
            (rectangle.routedSubsequence (refine rank))),
        quittingTerminalOutcomeMass reward
          (rectangle.endpointProfile
            (rectangle.routedSubsequence (refine rank))))) atTop
      (nhds rectangle.endpointPoint) :=
    rectangle.endpoint_tendsto.comp
      (rectangle.routeRefinement_strictMono.comp hrefine).tendsto_atTop
  have hresponseTendsto : Tendsto (fun rank =>
      (quittingTerminalSemanticPair reward
          (rectangle.endpointResponseProfile
            (rectangle.routedSubsequence (refine rank))),
        quittingTerminalOutcomeMass reward
          (rectangle.endpointResponseProfile
            (rectangle.routedSubsequence (refine rank))))) atTop
      (nhds rectangle.responsePoint) :=
    rectangle.response_tendsto.comp
      (rectangle.routeRefinement_strictMono.comp hrefine).tendsto_atTop
  have hdebtLe : ∀ who,
      quittingTerminalSemanticDebt chordPoint.1 who ≤
        (1 - theta) *
            quittingTerminalSemanticDebt rectangle.endpointPoint.1 who +
          theta * quittingTerminalSemanticDebt rectangle.responsePoint.1 who := by
    intro who
    have hleft := ((continuous_quittingTerminalSemanticDebt who).comp
      continuous_fst).tendsto chordPoint |>.comp hchordTendsto
    have hendpointDebt := ((continuous_quittingTerminalSemanticDebt who).comp
      continuous_fst).tendsto rectangle.endpointPoint |>.comp hendpointTendsto
    have hresponseDebt := ((continuous_quittingTerminalSemanticDebt who).comp
      continuous_fst).tendsto rectangle.responsePoint |>.comp hresponseTendsto
    have hright := (hendpointDebt.const_mul (1 - theta)).add
      (hresponseDebt.const_mul theta)
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [] with rank
    exact quittingTerminalSemanticDebt_responseChord_le reward
      (rectangle.endpointProfile (rectangle.routedSubsequence (refine rank)))
      (rectangle.endpointResponseProfile
        (rectangle.routedSubsequence (refine rank)))
      rectangle.observer who theta htheta0.le htheta1.le
      (rectangle.endpointResponseProfile_eq_of_ne _)
  have hlaw : ∀ outcome,
      chordPoint.2 outcome =
        (1 - theta) * rectangle.endpointPoint.2 outcome +
          theta * rectangle.responsePoint.2 outcome := by
    intro outcome
    have hleft := (((continuous_apply outcome).comp continuous_snd).tendsto
      chordPoint).comp hchordTendsto
    have hendpointLaw := (((continuous_apply outcome).comp continuous_snd).tendsto
      rectangle.endpointPoint).comp hendpointTendsto
    have hresponseLaw := (((continuous_apply outcome).comp continuous_snd).tendsto
      rectangle.responsePoint).comp hresponseTendsto
    have hright := (hendpointLaw.const_mul (1 - theta)).add
      (hresponseLaw.const_mul theta)
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [] with rank
    symm
    exact quittingTerminalOutcomeMass_responseChord_eq reward
      (rectangle.endpointProfile (rectangle.routedSubsequence (refine rank)))
      (rectangle.endpointResponseProfile
        (rectangle.routedSubsequence (refine rank)))
      rectangle.observer theta htheta0.le htheta1.le
      (rectangle.endpointResponseProfile_eq_of_ne _) outcome
  let geometry : QuittingMinimumResponseChordLaw reward := {
    endpoint := rectangle.endpointPoint
    response := rectangle.responsePoint
    chord := chordPoint
    theta := theta
    theta_pos := htheta0
    theta_lt_one := htheta1
    endpoint_mem := rectangle.endpoint_mem
    response_mem := rectangle.response_mem
    chord_mem := hchordMem
    endpoint_minimum := by
      intro candidate hcandidate
      rw [rectangle.endpoint_debtSum_eq_source]
      exact source.minimum candidate hcandidate
    response_debtSum_eq_endpoint := by
      rw [rectangle.response_debtSum_eq_source,
        rectangle.endpoint_debtSum_eq_source]
    chord_debt_le_affine := hdebtLe
    chord_law_eq_affine := hlaw
  }
  have hchordMass : 0 < chordPoint.2 (some rectangle.routedTerminal) := by
    have hfloor := geometry.theta_mul_le_chord_terminalMass
      rectangle.routedTerminal rectangle.lambda
        rectangle.lambda_le_responsePoint_terminalMass
    exact (mul_pos htheta0 rectangle.lambda_pos).trans_le hfloor
  let chordSource := source.regeneratedAtLawPoint chordPoint
    rectangle.routedTerminal hchordMem
      (geometry.chord_debtSum_eq_endpoint.trans
        rectangle.endpoint_debtSum_eq_source) hchordMass
  refine ⟨{
    chordRefinement := refine
    chordRefinement_strictMono := hrefine
    chordPoint := chordPoint
    chord_tendsto := ?_
    geometry := geometry
    geometry_endpoint_eq := rfl
    geometry_response_eq := rfl
    geometry_chord_eq := rfl
    geometry_theta_eq := rfl
    chordSource := chordSource
    chordSource_residual_eq := rfl
    chordSource_point_eq := rfl
    chordSource_terminal_eq := rfl
  }⟩
  simpa only [chordPointSeq, chordProfile, Function.comp_def] using hchordTendsto

/-- The two chord siblings differ literally only by the original mover
replacement; no profile or response law is reselected. -/
theorem endpointChord_eq_update_sourceChord
    (rank : ℕ) (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    quittingResponseChordProfile reward (rectangle.endpointProfile rank)
        (rectangle.endpointResponseProfile rank) rectangle.observer theta
        htheta0 htheta1 =
      Function.update
        (quittingResponseChordProfile reward (rectangle.sourceProfile rank)
          (rectangle.sourceResponseProfile rank) rectangle.observer theta
          htheta0 htheta1)
        rectangle.mover (rectangle.replacement rank) := by
  unfold quittingResponseChordProfile endpointResponseProfile
    sourceResponseProfile
  rw [rectangle.endpointProfile_eq_update rank]
  have hne : rectangle.observer ≠ rectangle.mover :=
    rectangle.mover_ne_observer.symm
  simp only [Function.update_of_ne hne, Function.update_self]
  exact Function.update_comm rectangle.mover_ne_observer _ _ _

/-- Exact scaling of the response gain on the upper vertical chord edge. -/
theorem responseGain_eq_scale
    (rank : ℕ) (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    quittingTerminalPayoff reward (rectangle.endpointResponseProfile rank)
        rectangle.observer -
      quittingTerminalPayoff reward
        (quittingResponseChordProfile reward (rectangle.endpointProfile rank)
          (rectangle.endpointResponseProfile rank) rectangle.observer theta
          htheta0 htheta1) rectangle.observer =
      (1 - theta) *
        (quittingTerminalPayoff reward (rectangle.endpointResponseProfile rank)
            rectangle.observer -
          quittingTerminalPayoff reward (rectangle.endpointProfile rank)
            rectangle.observer) :=
  quittingResponseChord_fullResponseGain_eq_scale reward
    (rectangle.endpointProfile rank) (rectangle.endpointResponseProfile rank)
    rectangle.observer rectangle.observer theta htheta0 htheta1
    (rectangle.endpointResponseProfile_eq_of_ne rank)

/-- Exact scaling of the positive response-square cross-difference. -/
theorem responseCross_eq_scale
    (rank : ℕ) (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    (quittingTerminalPayoff reward (rectangle.endpointResponseProfile rank)
        rectangle.observer -
      quittingTerminalPayoff reward
        (quittingResponseChordProfile reward (rectangle.endpointProfile rank)
          (rectangle.endpointResponseProfile rank) rectangle.observer theta
          htheta0 htheta1) rectangle.observer) -
      (quittingTerminalPayoff reward (rectangle.sourceResponseProfile rank)
          rectangle.observer -
        quittingTerminalPayoff reward
          (quittingResponseChordProfile reward (rectangle.sourceProfile rank)
            (rectangle.sourceResponseProfile rank) rectangle.observer theta
            htheta0 htheta1) rectangle.observer) =
      (1 - theta) *
        ((quittingTerminalPayoff reward (rectangle.endpointResponseProfile rank)
            rectangle.observer -
          quittingTerminalPayoff reward (rectangle.endpointProfile rank)
            rectangle.observer) -
        (quittingTerminalPayoff reward (rectangle.sourceResponseProfile rank)
            rectangle.observer -
          quittingTerminalPayoff reward (rectangle.sourceProfile rank)
            rectangle.observer)) :=
  quittingResponseChord_crossDifference_eq_scale reward
    (rectangle.sourceProfile rank) (rectangle.endpointProfile rank)
    (rectangle.sourceResponseProfile rank)
    (rectangle.endpointResponseProfile rank) rectangle.observer theta
    htheta0 htheta1 (rectangle.sourceResponseProfile_eq_of_ne rank)
    (rectangle.endpointResponseProfile_eq_of_ne rank)

/-- The response rectangle keeps the quantitative floor
`(1 - theta) * crossFloor`. -/
theorem one_sub_mul_crossFloor_le_responseCross
    (rank : ℕ) (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    (1 - theta) * rectangle.crossFloor ≤
      (quittingTerminalPayoff reward (rectangle.endpointResponseProfile rank)
          rectangle.observer -
        quittingTerminalPayoff reward
          (quittingResponseChordProfile reward (rectangle.endpointProfile rank)
            (rectangle.endpointResponseProfile rank) rectangle.observer theta
            htheta0 htheta1) rectangle.observer) -
      (quittingTerminalPayoff reward (rectangle.sourceResponseProfile rank)
          rectangle.observer -
        quittingTerminalPayoff reward
          (quittingResponseChordProfile reward (rectangle.sourceProfile rank)
            (rectangle.sourceResponseProfile rank) rectangle.observer theta
            htheta0 htheta1) rectangle.observer) := by
  rw [rectangle.responseCross_eq_scale rank theta htheta0 htheta1]
  exact mul_le_mul_of_nonneg_left (rectangle.responseCross_floor rank)
    (sub_nonneg.mpr htheta1)

/-- Every proper chord keeps a strictly positive response-square charge. -/
theorem responseCross_pos
    (rank : ℕ) (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) :
    0 <
      (quittingTerminalPayoff reward (rectangle.endpointResponseProfile rank)
          rectangle.observer -
        quittingTerminalPayoff reward
          (quittingResponseChordProfile reward (rectangle.endpointProfile rank)
            (rectangle.endpointResponseProfile rank) rectangle.observer theta
            htheta0 htheta1.le) rectangle.observer) -
      (quittingTerminalPayoff reward (rectangle.sourceResponseProfile rank)
          rectangle.observer -
        quittingTerminalPayoff reward
          (quittingResponseChordProfile reward (rectangle.sourceProfile rank)
            (rectangle.sourceResponseProfile rank) rectangle.observer theta
            htheta0 htheta1.le) rectangle.observer) := by
  have hlower := rectangle.one_sub_mul_crossFloor_le_responseCross rank theta
    htheta0 htheta1.le
  exact (mul_pos (sub_pos.mpr htheta1) rectangle.crossFloor_pos).trans_le hlower

/-- Under the packet's sharp small-parameter condition, every literal chord
row retains at least half of the mover's paid edge. -/
theorem theta_le_one_of_le_moverGap_ratio
    (theta : ℝ)
    (htheta : theta ≤ rectangle.moverGap /
      (2 * (rectangle.moverGap + 2 * bound))) :
    theta ≤ 1 := by
  apply htheta.trans
  have hdenom : 0 < 2 * (rectangle.moverGap + 2 * bound) := by
    nlinarith [rectangle.moverGap_pos, rectangle.bound_nonneg]
  apply (div_le_one hdenom).2
  nlinarith [rectangle.moverGap_pos, rectangle.bound_nonneg]

/-- Under the packet's sharp small-parameter condition, every literal chord
row retains at least half of the mover's paid edge. -/
theorem moverGap_div_two_le_chordGain
    (rank : ℕ) (theta : ℝ) (htheta0 : 0 ≤ theta)
    (htheta : theta ≤ rectangle.moverGap /
      (2 * (rectangle.moverGap + 2 * bound))) :
    rectangle.moverGap / 2 ≤
      quittingTerminalPayoff reward
          (quittingResponseChordProfile reward (rectangle.endpointProfile rank)
            (rectangle.endpointResponseProfile rank) rectangle.observer theta
            htheta0 (rectangle.theta_le_one_of_le_moverGap_ratio theta htheta))
          rectangle.mover -
        quittingTerminalPayoff reward
          (quittingResponseChordProfile reward (rectangle.sourceProfile rank)
            (rectangle.sourceResponseProfile rank) rectangle.observer theta
            htheta0 (rectangle.theta_le_one_of_le_moverGap_ratio theta htheta))
          rectangle.mover := by
  have htheta1 := rectangle.theta_le_one_of_le_moverGap_ratio theta htheta
  rw [quittingResponseChord_moverGain_eq reward
    (rectangle.sourceProfile rank) (rectangle.endpointProfile rank)
    (rectangle.sourceResponseProfile rank)
    (rectangle.endpointResponseProfile rank) rectangle.observer rectangle.mover
    theta htheta0 htheta1 (rectangle.sourceResponseProfile_eq_of_ne rank)
    (rectangle.endpointResponseProfile_eq_of_ne rank)]
  apply quittingResponseChord_moverGain_ge_half reward
    (rectangle.sourceProfile rank) (rectangle.endpointProfile rank)
    (rectangle.sourceResponseProfile rank)
    (rectangle.endpointResponseProfile rank) rectangle.mover theta
    rectangle.moverGap bound htheta0 (rectangle.moverGain_floor rank)
    rectangle.moverGap_pos rectangle.bound_nonneg
  · exact abs_quittingTerminalPayoff_le reward _ rectangle.mover
      rectangle.rewardBound
  · exact abs_quittingTerminalPayoff_le reward _ rectangle.mover
      rectangle.rewardBound
  · exact htheta

end FinFourMinimumResponseRectangle

end GameTheory
