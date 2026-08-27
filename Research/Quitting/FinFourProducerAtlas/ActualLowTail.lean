/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.Source
import Research.Quitting.FinFourSameStageEndpointMonodromy

/-!
# Actual low-tail rows for the Fin4 producer atlas

This module isolates the exact hypotheses consumed by the raw same-stage
purification dispatch.  An actual row need not belong to `SelectedRows` and
does not claim that any copied root remains cap-Nash after its continuation is
changed.  Its dependent `source` index retains the fixed minimum semantic
point used by the dispatch.
-/

noncomputable section

namespace GameTheory

open MathUE.FiniteBooleanEndpointOrbit

private theorem allContinueSpine_succ_eq
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingAllContinueProfileSpine reward profile (time + 1) =
      quittingAllContinueProfileSpine reward
        (quittingProfileAllContinueContinuation reward profile) time := by
  induction time with
  | zero => rfl
  | succ time ih =>
      simpa only [quittingAllContinueProfileSpine] using
        congrArg (quittingProfileAllContinueContinuation reward) ih

private theorem allContinueSpine_eq_of_eq_from
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (first second : (quittingGame reward).BehaviorProfile) (start : ℕ)
    (heq : ∀ who time history, start ≤ time →
      first who time history = second who time history) :
    quittingAllContinueProfileSpine reward first start =
      quittingAllContinueProfileSpine reward second start := by
  induction start generalizing first second with
  | zero =>
      funext who time history
      exact heq who time history (Nat.zero_le time)
  | succ start ih =>
      rw [allContinueSpine_succ_eq, allContinueSpine_succ_eq]
      apply ih
      intro who time history htime
      unfold quittingProfileAllContinueContinuation StochasticGame.shiftProfile
      exact heq who (time + 1) _ (by omega)

/-- The minimal actual-profile passport for the raw Fin4 same-stage dispatch.
It records no selected-row, cap-root-stack, or chronology assertion. -/
structure FinFourActualLowTailRow
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  profile : (quittingGame reward).BehaviorProfile
  stage : ℕ
  lambda : ℝ
  coalition : QuittingNonsingletonCoalition (Fin 4)
  lambda_pos : 0 < lambda
  lambda_le_stageMass :
    lambda ≤ quittingStageCoalitionMass reward profile stage
      (quittingTerminalOfNonsingletonCoalition coalition)
  lowTail :
    quittingSpineDebtExcess reward profile
        (quittingTerminalSemanticDebtSum source.point.1) (stage + 1) <
      lambda * quittingTerminalSemanticDebtSum source.point.1 / 2

namespace FinFourActualLowTailRow

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The initial partial-purification state attached to the actual row. -/
def initialState (row : FinFourActualLowTailRow source) :
    QuittingPartialPurificationState reward row.profile row.stage row.lambda :=
  quittingPartialPurificationInitialState reward row.profile row.stage row.lambda
    row.coalition row.lambda_le_stageMass

/-- Every partial one-date assignment retains the actual row's live roots
strictly after its selected date. -/
theorem state_postDate_liveRoot_eq
    (row : FinFourActualLowTailRow source)
    (state : QuittingPartialPurificationState
      reward row.profile row.stage row.lambda)
    (offset : ℕ) :
    quittingProfileLiveRoot reward
        (quittingPartialPurificationStateProfile reward row.profile row.stage
          row.lambda state)
        (row.stage + 1 + offset) =
      quittingProfileLiveRoot reward row.profile
        (row.stage + 1 + offset) := by
  unfold quittingPartialPurificationStateProfile
    quittingLiteralPartialRootProfile quittingProfileLiveRoot
  funext who
  cases hassignment : state.assignment who with
  | none => simp [hassignment]
  | some action =>
      simp [hassignment, quittingLiteralOneDateOverride,
        show row.stage + 1 + offset ≠ row.stage by omega]

end FinFourActualLowTailRow

namespace FinFourLowTailRow

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Forget the selected-row and exact-root data, retaining precisely the
actual-profile hypotheses consumed by same-stage dispatch. -/
def toActualLowTailRow (row : FinFourLowTailRow source) :
    FinFourActualLowTailRow source where
  profile := row.profile
  stage := row.stage
  lambda := row.lambda
  coalition := row.coalition
  lambda_pos := row.lambda_pos
  lambda_le_stageMass := row.lambda_le_stageMass
  lowTail := row.lowTail

end FinFourLowTailRow

/-- Complete provenance for either terminating arm of the raw dispatch.  The
dependent indices identify the normalized target profile and singleton with
the literal data produced by that arm.

The partial constructor retains its pre-terminal state, bounded path, and
best-endpoint singleton witness.  The terminal-orbit constructor retains the
completed state and bounded path, the actual orbit, and exactly the terminal
route witness supplied at the orbit's stored terminal time. -/
inductive FinFourActualLowTailSingletonOrigin
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (row : FinFourActualLowTailRow source) :
    (quittingGame reward).BehaviorProfile →
      {S : Finset (Fin 4) // S.Nonempty} → Type
  | partialSingleton
      (state : QuittingPartialPurificationState
        reward row.profile row.stage row.lambda)
      (steps : ℕ)
      (path : QuittingPartialPurificationPath reward row.profile row.stage
        row.lambda row.initialState state steps)
      (steps_le : steps ≤ Fintype.card (Fin 4))
      (exit : QuittingPartialPurificationSingleton reward row.profile row.stage
        row.lambda state) :
      FinFourActualLowTailSingletonOrigin row
        (quittingLiteralOneDateProfile reward
          (quittingPartialPurificationStateProfile reward row.profile row.stage
            row.lambda state)
          exit.who row.stage exit.action)
        exit.singleton
  | terminalOrbit
      (finalState : QuittingPartialPurificationState
        reward row.profile row.stage row.lambda)
      (steps : ℕ)
      (path : QuittingPartialPurificationPath reward row.profile row.stage
        row.lambda row.initialState finalState steps)
      (steps_le : steps ≤ Fintype.card (Fin 4))
      (complete : ∀ who, finalState.assignment who ≠ none)
      (orbit : DispatchedOrbit
        (QuittingSameStageSingletonRoute reward
          (quittingPartialPurificationStateProfile reward row.profile row.stage
            row.lambda finalState) row.stage)
        (fun start target => Nonempty
          (QuittingSameStageEndpointEdge reward
            (quittingPartialPurificationStateProfile reward row.profile row.stage
              row.lambda finalState)
            row.stage source.point.1 row.lambda start target))
        finalState.coalition)
      (who : Fin 4) (action : Bool)
      (singleton : {S : Finset (Fin 4) // S.Nonempty})
      (singleton_card : singleton.val.card = 1)
      (routed : singleton.val = quittingPureEndpointRoutedCoalition
        (orbit.orbit orbit.terminal_time).1 who action)
      (mass_le : quittingStageCoalitionMass reward
          (quittingLiteralPureRootCoalitionProfile reward
            (quittingPartialPurificationStateProfile reward row.profile row.stage
              row.lambda finalState)
            row.stage (orbit.orbit orbit.terminal_time))
          row.stage
          (quittingTerminalOfNonsingletonCoalition
            (orbit.orbit orbit.terminal_time)) ≤
        quittingStageCoalitionMass reward
          (quittingLiteralOneDateProfile reward
            (quittingLiteralPureRootCoalitionProfile reward
              (quittingPartialPurificationStateProfile reward row.profile
                row.stage row.lambda finalState)
              row.stage (orbit.orbit orbit.terminal_time))
            who row.stage action)
          row.stage singleton) :
      FinFourActualLowTailSingletonOrigin row
        (quittingLiteralOneDateProfile reward
          (quittingLiteralPureRootCoalitionProfile reward
            (quittingPartialPurificationStateProfile reward row.profile row.stage
              row.lambda finalState)
            row.stage (orbit.orbit orbit.terminal_time))
          who row.stage action)
        singleton

namespace FinFourActualLowTailSingletonOrigin

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {row : FinFourActualLowTailRow source}
  {targetProfile : (quittingGame reward).BehaviorProfile}
  {singleton : {S : Finset (Fin 4) // S.Nonempty}}

/-- The pre-terminal or completed partial-purification state retained by the
terminating mechanism. -/
def state
    (origin : FinFourActualLowTailSingletonOrigin row targetProfile singleton) :
    QuittingPartialPurificationState reward row.profile row.stage row.lambda :=
  match origin with
  | .partialSingleton state .. => state
  | .terminalOrbit finalState .. => finalState

/-- Number of partial-purification edges before the terminating mechanism. -/
def steps
    (origin : FinFourActualLowTailSingletonOrigin row targetProfile singleton) :
    ℕ :=
  match origin with
  | .partialSingleton _ steps .. => steps
  | .terminalOrbit _ steps .. => steps

/-- The retained path starts at the exact initial state of the indexed row. -/
theorem path
    (origin : FinFourActualLowTailSingletonOrigin row targetProfile singleton) :
    QuittingPartialPurificationPath reward row.profile row.stage row.lambda
      row.initialState origin.state origin.steps := by
  cases origin with
  | partialSingleton state steps path stepsLe exit =>
      exact path
  | terminalOrbit finalState steps path stepsLe complete orbit who action
      singleton singletonCard routed massLe =>
      exact path

/-- Either terminating mechanism occurs after at most four partial updates. -/
theorem steps_le_four
    (origin : FinFourActualLowTailSingletonOrigin row targetProfile singleton) :
    origin.steps ≤ 4 := by
  cases origin with
  | partialSingleton state steps path stepsLe exit =>
      change steps ≤ 4
      simpa using stepsLe
  | terminalOrbit finalState steps path stepsLe complete orbit who action
      singleton singletonCard routed massLe =>
      change steps ≤ 4
      simpa using stepsLe

/-- The player whose endpoint action supplies the terminal singleton route. -/
def mover
    (origin : FinFourActualLowTailSingletonOrigin row targetProfile singleton) :
    Fin 4 :=
  match origin with
  | .partialSingleton _ _ _ _ exit => exit.who
  | .terminalOrbit _ _ _ _ _ _ who .. => who

/-- The pure endpoint action used by the terminating singleton route. -/
def action
    (origin : FinFourActualLowTailSingletonOrigin row targetProfile singleton) :
    Bool :=
  match origin with
  | .partialSingleton _ _ _ _ exit => exit.action
  | .terminalOrbit _ _ _ _ _ _ _ action .. => action

/-- The exact nonsingleton coalition immediately before the terminal route. -/
def sourceCoalition
    (origin : FinFourActualLowTailSingletonOrigin row targetProfile singleton) :
    QuittingNonsingletonCoalition (Fin 4) :=
  match origin with
  | .partialSingleton state .. => state.coalition
  | .terminalOrbit _ _ _ _ _ orbit .. => orbit.orbit orbit.terminal_time

/-- The literal profile carrying the nonsingleton atom immediately before the
terminal route. -/
def routeSourceProfile
    (origin : FinFourActualLowTailSingletonOrigin row targetProfile singleton) :
    (quittingGame reward).BehaviorProfile :=
  match origin with
  | .partialSingleton state .. =>
      quittingPartialPurificationStateProfile reward row.profile row.stage
        row.lambda state
  | .terminalOrbit finalState _ _ _ _ orbit .. =>
      quittingLiteralPureRootCoalitionProfile reward
        (quittingPartialPurificationStateProfile reward row.profile row.stage
          row.lambda finalState)
        row.stage (orbit.orbit orbit.terminal_time)

/-- The returned singleton is exactly the routed coalition from the retained
pre-terminal coalition, mover, and action. -/
theorem singleton_eq_routed
    (origin : FinFourActualLowTailSingletonOrigin row targetProfile singleton) :
    singleton.val = quittingPureEndpointRoutedCoalition
      origin.sourceCoalition.1 origin.mover origin.action := by
  cases origin with
  | partialSingleton state steps path stepsLe exit =>
      exact exit.routed
  | terminalOrbit finalState steps path stepsLe complete orbit who action
      singleton singletonCard routed massLe =>
      exact routed

/-- The exact terminal route does not lose unconditional stage mass. -/
theorem route_mass_le
    (origin : FinFourActualLowTailSingletonOrigin row targetProfile singleton) :
    quittingStageCoalitionMass reward origin.routeSourceProfile row.stage
        (quittingTerminalOfNonsingletonCoalition origin.sourceCoalition) ≤
      quittingStageCoalitionMass reward targetProfile row.stage singleton := by
  cases origin with
  | partialSingleton state steps path stepsLe exit =>
      exact exit.mass_le
  | terminalOrbit finalState steps path stepsLe complete orbit who action
      singleton singletonCard routed massLe =>
      exact massLe

/-- Both terminating mechanisms retain an actual singleton. -/
theorem singleton_card
    (origin : FinFourActualLowTailSingletonOrigin row targetProfile singleton) :
    singleton.val.card = 1 := by
  cases origin with
  | partialSingleton state steps path stepsLe exit =>
      exact exit.singleton_card
  | terminalOrbit finalState steps path stepsLe complete orbit who action
      singleton singletonCard routed massLe =>
      exact singletonCard

end FinFourActualLowTailSingletonOrigin

/-- An actual singleton endpoint returned by either terminating arm of the
raw dispatch.  Indexing by `row` preserves its exact source profile, date,
scale, coalition, and fixed minimum point; `origin` retains the complete
terminating mechanism. -/
structure FinFourActualLowTailSingletonEndpoint
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (row : FinFourActualLowTailRow source) where
  targetProfile : (quittingGame reward).BehaviorProfile
  singleton : {S : Finset (Fin 4) // S.Nonempty}
  origin : FinFourActualLowTailSingletonOrigin row targetProfile singleton
  singleton_card : singleton.val.card = 1
  lambda_le_stageMass :
    row.lambda ≤ quittingStageCoalitionMass reward targetProfile row.stage singleton
  postDateSpine_eq :
    quittingAllContinueProfileSpine reward targetProfile (row.stage + 1) =
      quittingAllContinueProfileSpine reward row.profile (row.stage + 1)

namespace FinFourActualLowTailSingletonEndpoint

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {row : FinFourActualLowTailRow source}

/-- The endpoint's date is the exact date stored by its actual source row. -/
def stage (_endpoint : FinFourActualLowTailSingletonEndpoint row) : ℕ :=
  row.stage

/-- The endpoint's mass scale is the exact scale stored by its actual row. -/
def lambda (_endpoint : FinFourActualLowTailSingletonEndpoint row) : ℝ :=
  row.lambda

/-- The complete post-date behavioral spine is preserved, hence so is every
actual live root after the selected date. -/
theorem postDate_liveRoot_eq
    (endpoint : FinFourActualLowTailSingletonEndpoint row) (offset : ℕ) :
    quittingProfileLiveRoot reward endpoint.targetProfile
        (row.stage + 1 + offset) =
      quittingProfileLiveRoot reward row.profile
        (row.stage + 1 + offset) := by
  funext player
  have heq := congrFun (congrFun (congrFun endpoint.postDateSpine_eq player)
    offset) (quittingLiveHist reward offset)
  rw [quittingAllContinueProfileSpine_apply_liveHist,
    quittingAllContinueProfileSpine_apply_liveHist] at heq
  exact heq

/-- Semantic-tail form of the endpoint's exact post-date live-root
provenance. -/
theorem postDateTail_eq
    (endpoint : FinFourActualLowTailSingletonEndpoint row) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward endpoint.targetProfile
          (row.stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward row.profile (row.stage + 1)) := by
  rw [endpoint.postDateSpine_eq]

end FinFourActualLowTailSingletonEndpoint

/-- The raw cyclic output of the same-stage dispatch.  The stored trace is
definitionally based at the row's actual profile, date, scale, and fixed
minimum point, so the generic Fin4 closed-segment obstruction applies without
reselecting any of them. -/
structure FinFourActualLowTailClosedSegment
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (row : FinFourActualLowTailRow source) where
  finalState :
    QuittingPartialPurificationState reward row.profile row.stage row.lambda
  steps : ℕ
  path : QuittingPartialPurificationPath reward row.profile row.stage row.lambda
    row.initialState finalState steps
  steps_le : steps ≤ Fintype.card (Fin 4)
  complete : ∀ who, finalState.assignment who ≠ none
  trace : DispatchedClosedSegment
    (QuittingSameStageSingletonRoute reward
      (quittingPartialPurificationStateProfile reward row.profile row.stage
        row.lambda finalState) row.stage)
    (fun start target => Nonempty
      (QuittingSameStageEndpointEdge reward
        (quittingPartialPurificationStateProfile reward row.profile row.stage
          row.lambda finalState)
        row.stage source.point.1 row.lambda start target))
    finalState.coalition

namespace FinFourActualLowTailRow

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Raw Fin4 dispatch from exactly the data in an actual low-tail passport.
The two terminal mechanisms are normalized to one actual singleton endpoint;
the only other output is the unaltered dispatched closed segment. -/
theorem nonempty_singletonEndpoint_or_closedSegment
    (row : FinFourActualLowTailRow source) :
    Nonempty (FinFourActualLowTailSingletonEndpoint row) ∨
      Nonempty (FinFourActualLowTailClosedSegment row) := by
  rcases quittingPartialPurification_then_finFourSameStage_dispatch
      reward source.point.1 row.profile row.stage row.lambda row.coalition
      source.semantic_mem source.minimum source.minimumDebt_pos row.lambda_pos
      row.lambda_le_stageMass row.lowTail with
    ⟨state, steps, ⟨singleton⟩, path, steps_le⟩ |
      ⟨finalState, steps, path, steps_le, complete, dispatched⟩
  · left
    refine ⟨{
      targetProfile := quittingLiteralOneDateProfile reward
        (quittingPartialPurificationStateProfile reward row.profile row.stage
          row.lambda state)
        singleton.who row.stage singleton.action
      singleton := singleton.singleton
      origin := .partialSingleton state steps path steps_le singleton
      singleton_card := singleton.singleton_card
      lambda_le_stageMass := state.mass_floor.trans singleton.mass_le
      postDateSpine_eq := ?_
    }⟩
    apply allContinueSpine_eq_of_eq_from
    intro who time history htime
    unfold quittingLiteralOneDateProfile
      quittingPartialPurificationStateProfile quittingLiteralPartialRootProfile
    by_cases hwho : who = singleton.who
    · subst who
      simp only [Function.update_self]
      cases hassignment : state.assignment singleton.who with
      | none =>
          simp [quittingLiteralOneDateOverride,
            show time ≠ row.stage by omega]
      | some assigned =>
          simp [quittingLiteralOneDateOverride,
            show time ≠ row.stage by omega]
    · simp only [Function.update_of_ne hwho]
      cases hassignment : state.assignment who with
      | none => simp
      | some assigned =>
          simp [quittingLiteralOneDateOverride,
            show time ≠ row.stage by omega]
  · rcases dispatched with terminal | closed
    · obtain ⟨orbit⟩ := terminal
      obtain ⟨who, action, singleton, singleton_card, routed, mass_le⟩ :=
        orbit.terminal_at
      left
      refine ⟨{
        targetProfile := quittingLiteralOneDateProfile reward
          (quittingLiteralPureRootCoalitionProfile reward
            (quittingPartialPurificationStateProfile reward row.profile row.stage
              row.lambda finalState)
            row.stage (orbit.orbit orbit.terminal_time))
          who row.stage action
        singleton := singleton
        origin := .terminalOrbit finalState steps path steps_le complete orbit
          who action singleton singleton_card routed mass_le
        singleton_card := singleton_card
        lambda_le_stageMass := ?_
        postDateSpine_eq := ?_
      }⟩
      · have liveMass_floor : row.lambda ≤ quittingLiveMass reward
            (quittingPartialPurificationStateProfile reward row.profile row.stage
              row.lambda finalState)
            row.stage :=
          finalState.mass_floor.trans
            (quittingStageCoalitionMass_le_liveMass reward
              (quittingPartialPurificationStateProfile reward row.profile row.stage
                row.lambda finalState)
              row.stage
              (quittingTerminalOfNonsingletonCoalition finalState.coalition))
        apply liveMass_floor.trans
        rw [← quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass
          reward
          (quittingPartialPurificationStateProfile reward row.profile row.stage
            row.lambda finalState)
          row.stage (orbit.orbit orbit.terminal_time)]
        exact mass_le
      · apply allContinueSpine_eq_of_eq_from
        intro player time history htime
        unfold quittingLiteralOneDateProfile
          quittingLiteralPureRootCoalitionProfile quittingLiteralPureRootProfile
          quittingPartialPurificationStateProfile quittingLiteralPartialRootProfile
        by_cases hplayer : player = who
        · subst player
          simp only [Function.update_self]
          cases hassignment : finalState.assignment who with
          | none =>
              simp [quittingLiteralOneDateOverride,
                show time ≠ row.stage by omega]
          | some assigned =>
              simp [quittingLiteralOneDateOverride,
                show time ≠ row.stage by omega]
        · simp only [Function.update_of_ne hplayer]
          cases hassignment : finalState.assignment player with
          | none =>
              simp [quittingLiteralOneDateOverride,
                show time ≠ row.stage by omega]
          | some assigned =>
              simp [quittingLiteralOneDateOverride,
                show time ≠ row.stage by omega]
    · obtain ⟨trace, _period, _geometry, _mass, _edges⟩ := closed
      right
      exact ⟨{
        finalState := finalState
        steps := steps
        path := path
        steps_le := steps_le
        complete := complete
        trace := trace
      }⟩

end FinFourActualLowTailRow

end GameTheory
