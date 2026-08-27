/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.Source
import Research.Quitting.FinFourSameStageEndpointMonodromy

/-!
# Finite source-distinct leaves of the exhaustive Fin4 atlas

One low-tail source row dispatches to a bounded purification singleton, a
terminal singleton in the subsequent pure-root orbit, or one of the two exact
Fin4 cycle geometries.  Every output remains indexed by the common minimum-law
source.  The terminal-orbit record deliberately makes no claim about transient
edge certificates before its terminal vertex.
-/

noncomputable section

namespace GameTheory

open MathUE.FiniteBooleanEndpointOrbit
open QuittingNonsingletonMinimumLawTransfer

/-! ## Bounded partial purification -/

/-- A singleton reached during the bounded preliminary purification. -/
structure FinFourPurifiedSingletonProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  low : FinFourLowTailRow source
  state : QuittingPartialPurificationState reward low.profile low.stage low.lambda
  steps : ℕ
  singleton :
    QuittingPartialPurificationSingleton reward low.profile low.stage low.lambda state
  path : QuittingPartialPurificationPath reward low.profile low.stage low.lambda
    low.initialState state steps
  steps_le : steps ≤ Fintype.card (Fin 4)

/-- A completed bounded purification, before the finite endpoint orbit is
classified as terminal or cyclic. -/
structure FinFourTotalPurificationProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  low : FinFourLowTailRow source
  finalState :
    QuittingPartialPurificationState reward low.profile low.stage low.lambda
  steps : ℕ
  path : QuittingPartialPurificationPath reward low.profile low.stage low.lambda
    low.initialState finalState steps
  steps_le : steps ≤ Fintype.card (Fin 4)
  complete : ∀ who, finalState.assignment who ≠ none

namespace FinFourPurifiedSingletonProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The preliminary source-to-singleton path has at most four edges. -/
theorem steps_le_four (producer : FinFourPurifiedSingletonProducer source) :
    producer.steps ≤ 4 := by
  simpa using producer.steps_le

/-- The routed singleton retains the fixed low-row mass floor. -/
theorem singleton_stageMass_floor
    (producer : FinFourPurifiedSingletonProducer source) :
    producer.low.lambda ≤
      quittingStageCoalitionMass reward
        (quittingLiteralOneDateProfile reward
          (quittingPartialPurificationStateProfile reward producer.low.profile
            producer.low.stage producer.low.lambda producer.state)
          producer.singleton.who producer.low.stage producer.singleton.action)
        producer.low.stage producer.singleton.singleton := by
  exact producer.state.mass_floor.trans producer.singleton.mass_le

/-- The pre-terminal purification state has the original literal tail strictly
after the selected date. -/
theorem state_postDate_liveRoot_eq
    (producer : FinFourPurifiedSingletonProducer source) (offset : ℕ) :
    quittingProfileLiveRoot reward
        (quittingPartialPurificationStateProfile reward producer.low.profile
          producer.low.stage producer.low.lambda producer.state)
        (producer.low.stage + 1 + offset) =
      quittingProfileLiveRoot reward producer.low.profile
        (producer.low.stage + 1 + offset) := by
  unfold quittingPartialPurificationStateProfile quittingLiteralPartialRootProfile
    quittingProfileLiveRoot
  funext who
  cases hassignment : producer.state.assignment who with
  | none => simp [hassignment]
  | some action =>
      simp [hassignment, quittingLiteralOneDateOverride,
        show producer.low.stage + 1 + offset ≠ producer.low.stage by omega]

/-- Semantic form of the pre-terminal state's post-date tail provenance. -/
theorem state_postDateTail_eq
    (producer : FinFourPurifiedSingletonProducer source) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (quittingPartialPurificationStateProfile reward producer.low.profile
            producer.low.stage producer.low.lambda producer.state)
          (producer.low.stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward producer.low.profile
          (producer.low.stage + 1)) := by
  apply quittingTerminalSemanticPair_eq_of_liveRoot_eq
  funext offset player
  change (quittingAllContinueProfileSpine reward
      (quittingPartialPurificationStateProfile reward producer.low.profile
        producer.low.stage producer.low.lambda producer.state)
      (producer.low.stage + 1)) player offset (quittingLiveHist reward offset) =
    (quittingAllContinueProfileSpine reward producer.low.profile
      (producer.low.stage + 1)) player offset (quittingLiveHist reward offset)
  rw [quittingAllContinueProfileSpine_apply_liveHist,
    quittingAllContinueProfileSpine_apply_liveHist]
  exact congrFun (producer.state_postDate_liveRoot_eq offset) player

/-- The actual routed singleton target profile. -/
def singletonTargetProfile (producer : FinFourPurifiedSingletonProducer source) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralOneDateProfile reward
    (quittingPartialPurificationStateProfile reward producer.low.profile
      producer.low.stage producer.low.lambda producer.state)
    producer.singleton.who producer.low.stage producer.singleton.action

/-- The actual singleton target, including its terminal update, retains the
original literal live-root tail after the selected date. -/
theorem singletonTarget_postDate_liveRoot_eq
    (producer : FinFourPurifiedSingletonProducer source) (offset : ℕ) :
    quittingProfileLiveRoot reward producer.singletonTargetProfile
        (producer.low.stage + 1 + offset) =
      quittingProfileLiveRoot reward producer.low.profile
        (producer.low.stage + 1 + offset) := by
  calc
    quittingProfileLiveRoot reward producer.singletonTargetProfile
          (producer.low.stage + 1 + offset) =
        quittingProfileLiveRoot reward
          (quittingPartialPurificationStateProfile reward producer.low.profile
            producer.low.stage producer.low.lambda producer.state)
          (producer.low.stage + 1 + offset) :=
      quittingProfileLiveRoot_literalOneDateProfile_tail_eq
        (quittingPartialPurificationStateProfile reward producer.low.profile
          producer.low.stage producer.low.lambda producer.state)
        producer.singleton.who producer.low.stage offset producer.singleton.action
    _ = quittingProfileLiveRoot reward producer.low.profile
          (producer.low.stage + 1 + offset) :=
      producer.state_postDate_liveRoot_eq offset

/-- Semantic tail equality for the actual routed singleton target profile. -/
theorem singletonTarget_postDateTail_eq
    (producer : FinFourPurifiedSingletonProducer source) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward producer.singletonTargetProfile
          (producer.low.stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward producer.low.profile
          (producer.low.stage + 1)) := by
  apply quittingTerminalSemanticPair_eq_of_liveRoot_eq
  funext offset player
  change (quittingAllContinueProfileSpine reward producer.singletonTargetProfile
      (producer.low.stage + 1)) player offset (quittingLiveHist reward offset) =
    (quittingAllContinueProfileSpine reward producer.low.profile
      (producer.low.stage + 1)) player offset (quittingLiveHist reward offset)
  rw [quittingAllContinueProfileSpine_apply_liveHist,
    quittingAllContinueProfileSpine_apply_liveHist]
  exact congrFun (producer.singletonTarget_postDate_liveRoot_eq offset) player

end FinFourPurifiedSingletonProducer

namespace FinFourTotalPurificationProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The exact source profile of the finite endpoint orbit. -/
def profile (producer : FinFourTotalPurificationProducer source) :
    (quittingGame reward).BehaviorProfile :=
  quittingPartialPurificationStateProfile reward producer.low.profile
    producer.low.stage producer.low.lambda producer.finalState

/-- Total purification also takes at most four literal one-date updates. -/
theorem steps_le_four (producer : FinFourTotalPurificationProducer source) :
    producer.steps ≤ 4 := by
  simpa using producer.steps_le

/-- Completeness identifies the orbit source with a literal total pure root. -/
theorem profile_eq_literalPureRoot
    (producer : FinFourTotalPurificationProducer source) :
    producer.profile =
      quittingLiteralPureRootProfile reward producer.low.profile producer.low.stage
        (fun who => (producer.finalState.assignment who).getD false) := by
  exact quittingLiteralPartialRootProfile_eq_total_of_complete
    reward producer.low.profile producer.low.stage producer.finalState.assignment
    (fun who => Option.ne_none_iff_exists'.mp (producer.complete who))

/-- The total pure-root orbit source retains the original literal tail after
the selected date. -/
theorem postDate_liveRoot_eq
    (producer : FinFourTotalPurificationProducer source) (offset : ℕ) :
    quittingProfileLiveRoot reward producer.profile
        (producer.low.stage + 1 + offset) =
      quittingProfileLiveRoot reward producer.low.profile
        (producer.low.stage + 1 + offset) := by
  rw [producer.profile_eq_literalPureRoot]
  exact quittingLiteralPureRootProfile_tail_eq reward producer.low.profile
    producer.low.stage _ offset

/-- Semantic form of total-purification tail provenance. -/
theorem postDateTail_eq
    (producer : FinFourTotalPurificationProducer source) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward producer.profile
          (producer.low.stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward producer.low.profile
          (producer.low.stage + 1)) := by
  apply quittingTerminalSemanticPair_eq_of_liveRoot_eq
  funext offset player
  change (quittingAllContinueProfileSpine reward producer.profile
      (producer.low.stage + 1)) player offset (quittingLiveHist reward offset) =
    (quittingAllContinueProfileSpine reward producer.low.profile
      (producer.low.stage + 1)) player offset (quittingLiveHist reward offset)
  rw [quittingAllContinueProfileSpine_apply_liveHist,
    quittingAllContinueProfileSpine_apply_liveHist]
  exact congrFun (producer.postDate_liveRoot_eq offset) player

/-- The low-row floor also bounds the common live mass of the pure-root orbit. -/
theorem lambda_le_liveMass
    (producer : FinFourTotalPurificationProducer source) :
    producer.low.lambda ≤
      quittingLiveMass reward producer.profile producer.low.stage := by
  exact producer.finalState.mass_floor.trans
    (quittingStageCoalitionMass_le_liveMass reward producer.profile
      producer.low.stage
      (quittingTerminalOfNonsingletonCoalition producer.finalState.coalition))

end FinFourTotalPurificationProducer

/-! ## Terminal and cyclic pure-root outputs -/

/-- A singleton reached at a terminal vertex of the finite endpoint orbit.
The public orbit stores the terminal vertex, but not certified transient edges. -/
structure FinFourTerminalSingletonProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  purification : FinFourTotalPurificationProducer source
  orbit : DispatchedOrbit
    (QuittingSameStageSingletonRoute reward purification.profile
      purification.low.stage)
    (fun start target => Nonempty
      (QuittingSameStageEndpointEdge reward purification.profile
        purification.low.stage source.point.1 purification.low.lambda start target))
    purification.finalState.coalition

namespace FinFourTerminalSingletonProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- A literal one-date target profile at the orbit's terminal vertex.  It is a
singleton target when `who` and `action` come from `producer.orbit.terminal_at`. -/
def terminalVertexTargetProfile (producer : FinFourTerminalSingletonProducer source)
    (who : Fin 4) (action : Bool) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralOneDateProfile reward
    (quittingLiteralPureRootCoalitionProfile reward producer.purification.profile
      producer.purification.low.stage
      (producer.orbit.orbit producer.orbit.terminal_time))
    who producer.purification.low.stage action

/-- Every literal target at the stored terminal orbit vertex retains the
original selected row's live-root tail after the marked date. -/
theorem terminalVertexTarget_postDate_liveRoot_eq
    (producer : FinFourTerminalSingletonProducer source)
    (who : Fin 4) (action : Bool) (offset : ℕ) :
    quittingProfileLiveRoot reward (producer.terminalVertexTargetProfile who action)
        (producer.purification.low.stage + 1 + offset) =
      quittingProfileLiveRoot reward producer.purification.low.profile
        (producer.purification.low.stage + 1 + offset) := by
  calc
    quittingProfileLiveRoot reward (producer.terminalVertexTargetProfile who action)
          (producer.purification.low.stage + 1 + offset) =
        quittingProfileLiveRoot reward
          (quittingLiteralPureRootCoalitionProfile reward
            producer.purification.profile producer.purification.low.stage
            (producer.orbit.orbit producer.orbit.terminal_time))
          (producer.purification.low.stage + 1 + offset) :=
      quittingProfileLiveRoot_literalOneDateProfile_tail_eq
        (quittingLiteralPureRootCoalitionProfile reward producer.purification.profile
          producer.purification.low.stage
          (producer.orbit.orbit producer.orbit.terminal_time))
        who producer.purification.low.stage offset action
    _ = quittingProfileLiveRoot reward producer.purification.profile
          (producer.purification.low.stage + 1 + offset) :=
      quittingLiteralPureRootProfile_tail_eq reward producer.purification.profile
        producer.purification.low.stage _ offset
    _ = quittingProfileLiveRoot reward producer.purification.low.profile
          (producer.purification.low.stage + 1 + offset) :=
      producer.purification.postDate_liveRoot_eq offset

/-- Semantic tail equality for a literal target at the stored terminal orbit
vertex.  This does not assert transient orbit edges. -/
theorem terminalVertexTarget_postDateTail_eq
    (producer : FinFourTerminalSingletonProducer source)
    (who : Fin 4) (action : Bool) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (producer.terminalVertexTargetProfile who action)
          (producer.purification.low.stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward producer.purification.low.profile
          (producer.purification.low.stage + 1)) := by
  apply quittingTerminalSemanticPair_eq_of_liveRoot_eq
  funext offset player
  change (quittingAllContinueProfileSpine reward
      (producer.terminalVertexTargetProfile who action)
      (producer.purification.low.stage + 1)) player offset
        (quittingLiveHist reward offset) =
    (quittingAllContinueProfileSpine reward producer.purification.low.profile
      (producer.purification.low.stage + 1)) player offset
        (quittingLiveHist reward offset)
  rw [quittingAllContinueProfileSpine_apply_liveHist,
    quittingAllContinueProfileSpine_apply_liveHist]
  exact congrFun
    (producer.terminalVertexTarget_postDate_liveRoot_eq who action offset) player

/-- The orbit terminal predicate yields an actual routed singleton with the
fixed mass floor.  No transient edge certificate is used or returned. -/
theorem exists_singleton_with_stageMass_floor
    (producer : FinFourTerminalSingletonProducer source) :
    ∃ (who : Fin 4) (action : Bool)
        (singleton : {S : Finset (Fin 4) // S.Nonempty}),
      singleton.val.card = 1 ∧
        singleton.val = quittingPureEndpointRoutedCoalition
          (producer.orbit.orbit producer.orbit.terminal_time).1 who action ∧
        producer.purification.low.lambda ≤
          quittingStageCoalitionMass reward
            (quittingLiteralOneDateProfile reward
              (quittingLiteralPureRootCoalitionProfile reward
                producer.purification.profile producer.purification.low.stage
                (producer.orbit.orbit producer.orbit.terminal_time))
              who producer.purification.low.stage action)
            producer.purification.low.stage singleton := by
  obtain ⟨who, action, singleton, hcard, hrouted, hmass⟩ :=
    producer.orbit.terminal_at
  refine ⟨who, action, singleton, hcard, hrouted, ?_⟩
  apply producer.purification.lambda_le_liveMass.trans
  rw [← quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass
    reward producer.purification.profile producer.purification.low.stage
    (producer.orbit.orbit producer.orbit.terminal_time)]
  exact hmass

/-- The stored terminal predicate supplies an actual singleton target with
both the fixed mass floor and the original selected row's semantic tail.  No
transient orbit edge is used or returned. -/
theorem exists_singleton_with_stageMass_floor_and_postDateTail_eq
    (producer : FinFourTerminalSingletonProducer source) :
    ∃ (who : Fin 4) (action : Bool)
        (singleton : {S : Finset (Fin 4) // S.Nonempty}),
      singleton.val.card = 1 ∧
        singleton.val = quittingPureEndpointRoutedCoalition
          (producer.orbit.orbit producer.orbit.terminal_time).1 who action ∧
        producer.purification.low.lambda ≤
          quittingStageCoalitionMass reward
            (producer.terminalVertexTargetProfile who action)
            producer.purification.low.stage singleton ∧
        quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (producer.terminalVertexTargetProfile who action)
              (producer.purification.low.stage + 1)) =
          quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              producer.purification.low.profile
              (producer.purification.low.stage + 1)) := by
  obtain ⟨who, action, singleton, hcard, hrouted, hmass⟩ :=
    producer.exists_singleton_with_stageMass_floor
  exact ⟨who, action, singleton, hcard, hrouted, hmass,
    producer.terminalVertexTarget_postDateTail_eq who action⟩

end FinFourTerminalSingletonProducer

/-- The complete literal source of a simple same-stage endpoint cycle. -/
structure FinFourMonodromyProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  purification : FinFourTotalPurificationProducer source
  trace : DispatchedClosedSegment
    (QuittingSameStageSingletonRoute reward purification.profile
      purification.low.stage)
    (fun start target => Nonempty
      (QuittingSameStageEndpointEdge reward purification.profile
        purification.low.stage source.point.1 purification.low.lambda start target))
    purification.finalState.coalition
  period_le_eight : trace.segment.segment.period ≤ 8
  stage_mass_floor : ∀ offset : Fin trace.segment.segment.period,
    purification.low.lambda ≤ quittingStageCoalitionMass reward
      (quittingLiteralPureRootCoalitionProfile reward purification.profile
        purification.low.stage
        (trace.orbit (trace.segment.segment.start + offset)))
      purification.low.stage
      (quittingTerminalOfNonsingletonCoalition
        (trace.orbit (trace.segment.segment.start + offset)))
  edge_certificate : ∀ offset : Fin trace.segment.segment.period,
    ∃ edge : QuittingSameStageEndpointEdge reward purification.profile
        purification.low.stage source.point.1 purification.low.lambda
        (trace.orbit (trace.segment.segment.start + offset))
        (trace.orbit (trace.segment.segment.start + offset + 1)),
      edge.action = quittingRootBestEndpointAction reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (quittingLiteralPureRootCoalitionProfile reward purification.profile
                purification.low.stage
                (trace.orbit (trace.segment.segment.start + offset)))
              (purification.low.stage + 1))).1
          (quittingProfileLiveRoot reward
            (quittingLiteralPureRootCoalitionProfile reward purification.profile
              purification.low.stage
              (trace.orbit (trace.segment.segment.start + offset)))
            purification.low.stage)
          edge.who ∧
        0 < quittingSameStageCoalitionGain reward purification.profile
          purification.low.stage
          (trace.orbit (trace.segment.segment.start + offset))
          edge.who edge.action ∧
        purification.low.lambda *
              quittingTerminalSemanticDebtSum source.point.1 / 8 ≤
          quittingSameStageCoalitionGain reward purification.profile
            purification.low.stage
            (trace.orbit (trace.segment.segment.start + offset))
            edge.who edge.action

namespace FinFourMonodromyProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The canonical certified edge at a cycle offset. -/
def edge (producer : FinFourMonodromyProducer source)
    (offset : Fin producer.trace.segment.segment.period) :
    QuittingSameStageEndpointEdge reward producer.purification.profile
      producer.purification.low.stage source.point.1 producer.purification.low.lambda
      (producer.trace.orbit (producer.trace.segment.segment.start + offset))
      (producer.trace.orbit (producer.trace.segment.segment.start + offset + 1)) :=
  dispatchedClosedSegmentEdge producer.trace offset

/-- Each cycle step is the literal routed membership toggle recorded by its
edge certificate. -/
theorem edge_target_eq_routed (producer : FinFourMonodromyProducer source)
    (offset : Fin producer.trace.segment.segment.period) :
    (producer.trace.orbit
        (producer.trace.segment.segment.start + offset + 1)).1 =
      quittingPureEndpointRoutedCoalition
        (producer.trace.orbit
          (producer.trace.segment.segment.start + offset)).1
        (producer.edge offset).who (producer.edge offset).action :=
  (producer.edge offset).target_eq_routed

/-- Every cycle edge has the exact Fin4 gain floor. -/
theorem edge_gain_floor (producer : FinFourMonodromyProducer source)
    (offset : Fin producer.trace.segment.segment.period) :
    producer.purification.low.lambda *
          quittingTerminalSemanticDebtSum source.point.1 / 8 ≤
      quittingSameStageCoalitionGain reward producer.purification.profile
        producer.purification.low.stage
        (producer.trace.orbit (producer.trace.segment.segment.start + offset))
        (producer.edge offset).who (producer.edge offset).action := by
  have hfloor := (producer.edge offset).gain_floor
  norm_num [Fintype.card_fin] at hfloor ⊢
  exact hfloor

/-- The gain floor in the packet's explicit `mu^2 * D_* / 64` normalization. -/
theorem edge_gain_floor_mu_square_div_sixty_four
    (producer : FinFourMonodromyProducer source)
    (offset : Fin producer.trace.segment.segment.period) :
    source.point.2 (some source.atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 64 ≤
      quittingSameStageCoalitionGain reward producer.purification.profile
        producer.purification.low.stage
        (producer.trace.orbit (producer.trace.segment.segment.start + offset))
        (producer.edge offset).who (producer.edge offset).action := by
  calc
    source.point.2 (some source.atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 64 =
        producer.purification.low.lambda *
          quittingTerminalSemanticDebtSum source.point.1 / 8 := by
      dsimp only [FinFourLowTailRow.lambda]
      ring
    _ ≤ _ := producer.edge_gain_floor offset

/-- Every cycle edge has strictly positive literal payoff gain. -/
theorem edge_gain_pos (producer : FinFourMonodromyProducer source)
    (offset : Fin producer.trace.segment.segment.period) :
    0 < quittingSameStageCoalitionGain reward producer.purification.profile
      producer.purification.low.stage
      (producer.trace.orbit (producer.trace.segment.segment.start + offset))
      (producer.edge offset).who (producer.edge offset).action :=
  (producer.edge offset).gain_pos

/-- The mover's semantic debt decreases by exactly the displayed edge gain. -/
theorem edge_mover_debt
    (producer : FinFourMonodromyProducer source)
    (offset : Fin producer.trace.segment.segment.period) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingLiteralPureRootCoalitionProfile reward
            producer.purification.profile producer.purification.low.stage
            (producer.trace.orbit
              (producer.trace.segment.segment.start + offset + 1))))
        (producer.edge offset).who =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingLiteralPureRootCoalitionProfile reward
              producer.purification.profile producer.purification.low.stage
              (producer.trace.orbit
                (producer.trace.segment.segment.start + offset))))
          (producer.edge offset).who -
        quittingSameStageCoalitionGain reward producer.purification.profile
          producer.purification.low.stage
          (producer.trace.orbit
            (producer.trace.segment.segment.start + offset))
          (producer.edge offset).who (producer.edge offset).action :=
  (producer.edge offset).mover_debt

/-- Routing a cycle edge does not decrease the marked stage mass. -/
theorem edge_stageMass_noLoss
    (producer : FinFourMonodromyProducer source)
    (offset : Fin producer.trace.segment.segment.period) :
    quittingStageCoalitionMass reward
        (quittingLiteralPureRootCoalitionProfile reward
          producer.purification.profile producer.purification.low.stage
          (producer.trace.orbit
            (producer.trace.segment.segment.start + offset)))
        producer.purification.low.stage
        (quittingTerminalOfNonsingletonCoalition
          (producer.trace.orbit
            (producer.trace.segment.segment.start + offset))) ≤
      quittingStageCoalitionMass reward
        (quittingLiteralPureRootCoalitionProfile reward
          producer.purification.profile producer.purification.low.stage
          (producer.trace.orbit
            (producer.trace.segment.segment.start + offset + 1)))
        producer.purification.low.stage
        (quittingTerminalOfNonsingletonCoalition
          (producer.trace.orbit
            (producer.trace.segment.segment.start + offset + 1))) :=
  (producer.edge offset).stage_mass_le

end FinFourMonodromyProducer

/-- Common-host geometry for a literal simple endpoint cycle. -/
structure FinFourCommonHostMonodromyProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  monodromy : FinFourMonodromyProducer source
  host : Fin 4
  host_mem : ∀ offset : Fin monodromy.trace.segment.segment.period,
    host ∈ (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + offset)).1

namespace FinFourCommonHostMonodromyProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Exact common-host geometry, stated independently of any exclusivity claim. -/
theorem exact_geometry (producer : FinFourCommonHostMonodromyProducer source) :
    ∃ host : Fin 4,
      ∀ offset : Fin producer.monodromy.trace.segment.segment.period,
        host ∈ (producer.monodromy.trace.orbit
          (producer.monodromy.trace.segment.segment.start + offset)).1 :=
  ⟨producer.host, producer.host_mem⟩

end FinFourCommonHostMonodromyProducer

/-- Complementary-pair geometry for a literal simple endpoint cycle. -/
structure FinFourComplementaryPairMonodromyProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  monodromy : FinFourMonodromyProducer source
  first : Fin monodromy.trace.segment.segment.period
  second : Fin monodromy.trace.segment.segment.period
  first_card :
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + first)).1.card = 2
  second_card :
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + second)).1.card = 2
  disjoint : Disjoint
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + first)).1
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + second)).1
  complementary :
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + second)).1 =
      (monodromy.trace.orbit
        (monodromy.trace.segment.segment.start + first)).1ᶜ

namespace FinFourComplementaryPairMonodromyProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The two displayed pair vertices are disjoint exact complements. -/
theorem exact_geometry
    (producer : FinFourComplementaryPairMonodromyProducer source) :
    let firstCoalition := (producer.monodromy.trace.orbit
      (producer.monodromy.trace.segment.segment.start + producer.first)).1
    let secondCoalition := (producer.monodromy.trace.orbit
      (producer.monodromy.trace.segment.segment.start + producer.second)).1
    firstCoalition.card = 2 ∧ secondCoalition.card = 2 ∧
      Disjoint firstCoalition secondCoalition ∧
      secondCoalition = firstCoalitionᶜ := by
  exact ⟨producer.first_card, producer.second_card, producer.disjoint,
    producer.complementary⟩

end FinFourComplementaryPairMonodromyProducer

/-! ## Exhaustive low-row dispatch and leaf family -/

namespace FinFourLowTailRow

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- One actual low-tail row produces one of the four downstream source forms.
The two cycle geometries need not be mutually exclusive. -/
theorem nonempty_leaf (low : FinFourLowTailRow source) :
    Nonempty (FinFourPurifiedSingletonProducer source) ∨
      Nonempty (FinFourTerminalSingletonProducer source) ∨
      Nonempty (FinFourCommonHostMonodromyProducer source) ∨
      Nonempty (FinFourComplementaryPairMonodromyProducer source) := by
  have hdispatch := quittingPartialPurification_then_finFourSameStage_dispatch
    reward source.point.1 low.profile low.stage low.lambda low.coalition
    source.semantic_mem source.minimum source.minimumDebt_pos low.lambda_pos
    low.lambda_le_stageMass low.lowTail
  rcases hdispatch with hsingleton |
      ⟨finalState, steps, hpath, hsteps, hcomplete, hterminalOrCycle⟩
  · obtain ⟨state, steps, ⟨singleton⟩, hpath, hsteps⟩ := hsingleton
    exact Or.inl ⟨{
      low := low
      state := state
      steps := steps
      singleton := singleton
      path := hpath
      steps_le := hsteps
    }⟩
  · let purification : FinFourTotalPurificationProducer source := {
      low := low
      finalState := finalState
      steps := steps
      path := hpath
      steps_le := hsteps
      complete := hcomplete
    }
    rcases hterminalOrCycle with horbit |
        ⟨trace, hperiod, hgeometry, hmass, hedge⟩
    · obtain ⟨orbit⟩ := horbit
      exact Or.inr (Or.inl ⟨{
        purification := purification
        orbit := orbit
      }⟩)
    · let monodromy : FinFourMonodromyProducer source := {
        purification := purification
        trace := trace
        period_le_eight := hperiod
        stage_mass_floor := hmass
        edge_certificate := hedge
      }
      rcases hgeometry with ⟨host, hhost⟩ |
          ⟨first, second, hfirst, hsecond, hdisjoint, hcomplementary⟩
      · exact Or.inr (Or.inr (Or.inl ⟨{
          monodromy := monodromy
          host := host
          host_mem := hhost
        }⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨{
          monodromy := monodromy
          first := first
          second := second
          first_card := hfirst
          second_card := hsecond
          disjoint := hdisjoint
          complementary := hcomplementary
        }⟩))

end FinFourLowTailRow

/-- The six natural producer modes.  The three ways of reaching a singleton
remain separate constructors so their literal sources are not identified. -/
inductive FinFourProducerResidual
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
  | commonHostMonodromy
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : FinFourCommonHostMonodromyProducer source)
  | complementaryPairMonodromy
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : FinFourComplementaryPairMonodromyProducer source)

/-- Names for the four remaining completion obligations.  This type is only a
classifier and supplies no downstream consumer. -/
inductive FinFourProducerCompletionContract
  | singletonTerminalApproximationOrRegeneration
  | escapedTailChargeOrRegeneration
  | commonHostNonlocalReturnOrRegeneration
  | complementaryPairNonlocalReturnOrRegeneration
  deriving DecidableEq

/-- Classify each leaf by its remaining obligation; this is not a consumer. -/
def FinFourProducerResidual.completionContract
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} : FinFourProducerResidual reward bound →
      FinFourProducerCompletionContract
  | .minimumSingleton .. => .singletonTerminalApproximationOrRegeneration
  | .purifiedSingleton .. => .singletonTerminalApproximationOrRegeneration
  | .terminalSingleton .. => .singletonTerminalApproximationOrRegeneration
  | .tailEscape .. => .escapedTailChargeOrRegeneration
  | .commonHostMonodromy .. => .commonHostNonlocalReturnOrRegeneration
  | .complementaryPairMonodromy .. =>
      .complementaryPairNonlocalReturnOrRegeneration

end GameTheory
