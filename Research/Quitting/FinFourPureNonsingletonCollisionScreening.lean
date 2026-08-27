/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.PureNonsingletonCollisionScreening
import Research.Quitting.SameStageEndpointMonodromyImpossible

/-!
# Fin4 pure nonsingleton collision screening

The continuation-screened local dispatch cannot close on four players.  Its
first-terminal orbit therefore reaches a literal pair-to-singleton route in
at most three strict best-endpoint edges.  The result keeps the original
profile, pure sibling, complete certified orbit, final route, and singleton
target.  The simultaneous initial pure overwrite and the final route are not
asserted to be profitable.
-/

noncomputable section

namespace GameTheory

open MathUE.FiniteBooleanEndpointOrbit

/-- The literal singleton endpoint of one Fin4 pure nonsingleton screening.
The stored orbit carries every strict preterminal edge and its first-terminal
property; the remaining fields unpack the actual final no-loss route. -/
structure FinFourPureNonsingletonScreenedEndpoint
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (source : QuittingNonsingletonCoalition (Fin 4))
    (lambda : ℝ) where
  lambda_pos : 0 < lambda
  lambda_le_sourceStageMass :
    lambda ≤ quittingStageCoalitionMass reward profile stage
      (quittingTerminalOfNonsingletonCoalition source)
  orbit : DispatchedOrbit
    (QuittingSameStageSingletonRoute reward profile stage)
    (fun left right => Nonempty
      (QuittingPureNonsingletonScreenedEdge reward profile stage minimum
        lambda left right)) source
  who : Fin 4
  action : Bool
  singleton : {S : Finset (Fin 4) // S.Nonempty}
  singleton_card : singleton.val.card = 1
  singleton_eq_routed : singleton.val =
    quittingPureEndpointRoutedCoalition
      (orbit.orbit orbit.terminal_time).1 who action
  terminalStageMass_le :
    quittingStageCoalitionMass reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage
          (orbit.orbit orbit.terminal_time)) stage
        (quittingTerminalOfNonsingletonCoalition
          (orbit.orbit orbit.terminal_time)) ≤
      quittingStageCoalitionMass reward
        (quittingLiteralOneDateProfile reward
          (quittingLiteralPureRootCoalitionProfile reward profile stage
            (orbit.orbit orbit.terminal_time)) who stage action)
        stage singleton

namespace FinFourPureNonsingletonScreenedEndpoint

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {minimum : QuittingTerminalSemanticPair (Fin 4)}
  {profile : (quittingGame reward).BehaviorProfile}
  {stage : ℕ} {source : QuittingNonsingletonCoalition (Fin 4)}
  {lambda : ℝ}

/-- The initial simultaneous overwrite is the literal pure sibling of the
supplied actual profile at the marked date. -/
def sourcePureProfile
    (_endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralPureRootCoalitionProfile reward profile stage source

/-- The actual pure profile at a vertex of the retained orbit. -/
def orbitProfile
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) (time : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralPureRootCoalitionProfile reward profile stage
    (endpoint.orbit.orbit time)

/-- Every pure profile in the finite orbit is literally the supplied profile
away from the marked date, at every history. -/
theorem orbitProfile_eq_of_time_ne
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda)
    (orbitTime : ℕ) (player : Fin 4) (time : ℕ)
    (history : (quittingGame reward).Hist time) (htime : time ≠ stage) :
    endpoint.orbitProfile orbitTime player time history =
      profile player time history := by
  unfold orbitProfile quittingLiteralPureRootCoalitionProfile
    quittingLiteralPureRootProfile
  exact congrFun
    (quittingLiteralOneDateOverride_of_ne (profile player) stage time _ htime)
    history

/-- The literal final pair-to-singleton target profile. -/
def targetProfile
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralOneDateProfile reward
    (endpoint.orbitProfile endpoint.orbit.terminal_time)
    endpoint.who stage endpoint.action

/-- The final update is literally the pure root of the routed singleton, not
merely a profile with a lower-bounded singleton mass. -/
theorem targetProfile_eq_pureSingleton
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) :
    endpoint.targetProfile =
      quittingLiteralPureRootProfile reward profile stage
        (quittingCoalitionAction endpoint.singleton.val) := by
  simpa only [targetProfile, orbitProfile, quittingLiteralOneDateProfile,
    quittingLiteralPureRootCoalitionProfile, quittingPureRootOfCoalition] using
      quittingLiteralPureRootProfile_update_eq_routed reward profile stage
        (endpoint.orbit.orbit endpoint.orbit.terminal_time).1 endpoint.who
        endpoint.action endpoint.singleton.val endpoint.singleton_eq_routed

/-- The source pure sibling assigns exactly the reached live mass to the
marked coalition. -/
theorem sourcePure_stageMass_eq_liveMass
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) :
    quittingStageCoalitionMass reward endpoint.sourcePureProfile stage
        (quittingTerminalOfNonsingletonCoalition source) =
      quittingLiveMass reward profile stage :=
  quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass
    reward profile stage source

/-- The supplied source stage-mass floor is also a reached-live-mass floor. -/
theorem lambda_le_liveMass
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) :
    lambda ≤ quittingLiveMass reward profile stage :=
  endpoint.lambda_le_sourceStageMass.trans
    (quittingStageCoalitionMass_le_liveMass reward profile stage
      (quittingTerminalOfNonsingletonCoalition source))

/-- The orbit starts at the supplied nonsingleton coalition. -/
theorem orbit_zero
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) :
    endpoint.orbit.orbit 0 = source :=
  endpoint.orbit.orbit_zero

/-- Every step before the first terminal time retains its complete screened
best-endpoint certificate. -/
theorem nonempty_screenedEdge
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda)
    (time : ℕ) (htime : time < endpoint.orbit.terminal_time) :
    Nonempty (QuittingPureNonsingletonScreenedEdge reward profile stage
      minimum lambda (endpoint.orbit.orbit time)
        (endpoint.orbit.orbit (time + 1))) :=
  endpoint.orbit.edge_before time htime

/-- The canonical selected certificate for one preterminal orbit edge.  All
quantitative accessors below use this single definition. -/
def screenedEdge
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda)
    (time : ℕ) (htime : time < endpoint.orbit.terminal_time) :
    QuittingPureNonsingletonScreenedEdge reward profile stage minimum lambda
      (endpoint.orbit.orbit time) (endpoint.orbit.orbit (time + 1)) :=
  Classical.choice (endpoint.nonempty_screenedEdge time htime)

/-- A certified orbit edge is literally the one-date update from its source
pure profile to its target pure profile. -/
theorem edge_targetProfile_eq
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda)
    (time : ℕ) (htime : time < endpoint.orbit.terminal_time) :
    let screened := endpoint.screenedEdge time htime
    quittingLiteralOneDateProfile reward (endpoint.orbitProfile time)
        screened.edge.who stage screened.edge.action =
      endpoint.orbitProfile (time + 1) := by
  dsimp only
  simpa only [orbitProfile, quittingLiteralOneDateProfile] using
    quittingLiteralPureRootCoalitionProfile_update_eq_routed reward profile
      stage (endpoint.orbit.orbit time)
      (endpoint.screenedEdge time htime).edge.who
      (endpoint.screenedEdge time htime).edge.action
      (endpoint.orbit.orbit (time + 1))
      (endpoint.screenedEdge time htime).edge.target_eq_routed

/-- Every strict preterminal edge has the sharp reached-live-mass floor
`L * D_* / 4`. -/
theorem edge_gain_floor_live
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda)
    (time : ℕ) (htime : time < endpoint.orbit.terminal_time) :
    let screened := endpoint.screenedEdge time htime
    quittingLiveMass reward profile stage *
          quittingTerminalSemanticDebtSum minimum / 4 ≤
      quittingSameStageCoalitionGain reward profile stage
        (endpoint.orbit.orbit time) screened.edge.who screened.edge.action := by
  dsimp only
  simpa using (endpoint.screenedEdge time htime).gain_floor_live

/-- Every strict preterminal edge has the resulting selected-scale Fin4 paid
floor `lambda * D_* / 4`. -/
theorem edge_gain_floor
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda)
    (hminimumDebt : 0 ≤ quittingTerminalSemanticDebtSum minimum)
    (time : ℕ) (htime : time < endpoint.orbit.terminal_time) :
    let screened := endpoint.screenedEdge time htime
    lambda * quittingTerminalSemanticDebtSum minimum / 4 ≤
      quittingSameStageCoalitionGain reward profile stage
        (endpoint.orbit.orbit time) screened.edge.who screened.edge.action := by
  dsimp only
  simpa using (endpoint.screenedEdge time htime).gain_floor
    endpoint.lambda_le_liveMass hminimumDebt

/-- Every certified orbit edge is strictly profitable for its mover. -/
theorem edge_gain_pos
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda)
    (time : ℕ) (htime : time < endpoint.orbit.terminal_time) :
    let screened := endpoint.screenedEdge time htime
    0 < quittingSameStageCoalitionGain reward profile stage
      (endpoint.orbit.orbit time) screened.edge.who screened.edge.action := by
  dsimp only
  exact (endpoint.screenedEdge time htime).edge.gain_pos

/-- The mover's unrestricted behavioral debt decreases by exactly the actual
payoff gain on each retained strict edge. -/
theorem edge_mover_debt
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda)
    (time : ℕ) (htime : time < endpoint.orbit.terminal_time) :
    let screened := endpoint.screenedEdge time htime
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (endpoint.orbitProfile (time + 1))) screened.edge.who =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (endpoint.orbitProfile time)) screened.edge.who -
        quittingSameStageCoalitionGain reward profile stage
          (endpoint.orbit.orbit time) screened.edge.who screened.edge.action := by
  dsimp only
  exact (endpoint.screenedEdge time htime).edge.mover_debt

/-- Every retained strict edge routes the marked pure-coalition mass without
loss. -/
theorem edge_stageMass_le
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda)
    (time : ℕ) (htime : time < endpoint.orbit.terminal_time) :
    quittingStageCoalitionMass reward (endpoint.orbitProfile time) stage
        (quittingTerminalOfNonsingletonCoalition
          (endpoint.orbit.orbit time)) ≤
      quittingStageCoalitionMass reward
        (endpoint.orbitProfile (time + 1)) stage
        (quittingTerminalOfNonsingletonCoalition
          (endpoint.orbit.orbit (time + 1))) := by
  exact (endpoint.screenedEdge time htime).edge.stage_mass_le

/-- Consecutive retained strict edges cannot reverse one another. -/
theorem no_immediate_reverse
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda)
    (time : ℕ) (htime : time + 1 < endpoint.orbit.terminal_time) :
    endpoint.orbit.orbit (time + 2) ≠ endpoint.orbit.orbit time := by
  intro hreverse
  let first := endpoint.screenedEdge time (by omega)
  let second := endpoint.screenedEdge (time + 1) htime
  rw [hreverse] at second
  exact first.not_reverse second

/-- The final singleton route is exactly a Continue move from a two-player
source.  No payoff sign is attached to that last route. -/
theorem terminal_action_and_card
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) :
    endpoint.action = false ∧
      (endpoint.orbit.orbit endpoint.orbit.terminal_time).1.card = 2 := by
  have hcardRouted :
      (quittingPureEndpointRoutedCoalition
        (endpoint.orbit.orbit endpoint.orbit.terminal_time).1
        endpoint.who endpoint.action).card = 1 := by
    calc
      _ = endpoint.singleton.val.card :=
        congrArg Finset.card endpoint.singleton_eq_routed.symm
      _ = 1 := endpoint.singleton_card
  exact quittingPureEndpointRoutedCoalition_card_eq_one_of_nonsingleton
    (endpoint.orbit.orbit endpoint.orbit.terminal_time) endpoint.who
    endpoint.action hcardRouted

/-- The first terminal coalition is a pair. -/
theorem terminal_card_eq_two
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) :
    (endpoint.orbit.orbit endpoint.orbit.terminal_time).1.card = 2 :=
  endpoint.terminal_action_and_card.2

/-- The terminal route necessarily makes one member Continue.  It is not
asserted to be payoff-improving. -/
theorem terminal_action_eq_false
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) :
    endpoint.action = false :=
  endpoint.terminal_action_and_card.1

/-- The retained Fin4 orbit has at most three strict profitable edges. -/
theorem edge_count_le_three
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) :
    endpoint.orbit.terminal_time.val ≤ 3 := by
  apply pureNonsingletonScreenedOrbit_terminal_time_le_three endpoint.orbit
    Finset.univ
  · intro time _htime
    exact Finset.subset_univ _
  · simp

/-- Exact no-loss routing along every strict edge and the final route carries
the original positive scale into the singleton target. -/
theorem lambda_le_targetStageMass
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) :
    lambda ≤ quittingStageCoalitionMass reward endpoint.targetProfile stage
      endpoint.singleton := by
  have hstart : lambda ≤
      quittingStageCoalitionMass reward (endpoint.orbitProfile 0) stage
        (quittingTerminalOfNonsingletonCoalition
          (endpoint.orbit.orbit 0)) := by
    calc
      lambda ≤ quittingLiveMass reward profile stage :=
        endpoint.lambda_le_liveMass
      _ = quittingStageCoalitionMass reward (endpoint.orbitProfile 0) stage
          (quittingTerminalOfNonsingletonCoalition
            (endpoint.orbit.orbit 0)) := by
        exact
          (quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass
            reward profile stage (endpoint.orbit.orbit 0)).symm
  have horbit := pureNonsingletonScreenedOrbit_stageMass_zero_le
    endpoint.orbit endpoint.orbit.terminal_time (le_rfl)
  exact hstart.trans (horbit.trans endpoint.terminalStageMass_le)

/-- The final singleton mass is exactly the original reached live mass.  The
last pair-to-singleton route needs no profitability assertion. -/
theorem targetStageMass_eq_liveMass
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) :
    quittingStageCoalitionMass reward endpoint.targetProfile stage
        endpoint.singleton =
      quittingLiveMass reward profile stage := by
  rw [endpoint.targetProfile_eq_pureSingleton,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_literalPureRootProfile_eq,
    quittingProfileLiveRoot_literalPureRootProfile_self,
    quittingRootCoalitionMass_pureCoalitionAction_eq_one, mul_one]

/-- At every date other than the marked row, the singleton target is exactly
the originally supplied behavioral profile, at every history. -/
theorem targetProfile_eq_of_time_ne
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda)
    (player : Fin 4) (time : ℕ) (history : (quittingGame reward).Hist time)
    (htime : time ≠ stage) :
    endpoint.targetProfile player time history =
      profile player time history := by
  rw [endpoint.targetProfile_eq_pureSingleton]
  unfold quittingLiteralPureRootProfile
  exact congrFun
    (quittingLiteralOneDateOverride_of_ne (profile player) stage time _ htime)
    history

/-- The singleton target retains the original complete behavioral tail after
the marked date. -/
theorem target_postDate_liveRoot_eq
    (endpoint : FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) (offset : ℕ) :
    quittingProfileLiveRoot reward endpoint.targetProfile
        (stage + 1 + offset) =
      quittingProfileLiveRoot reward profile (stage + 1 + offset) := by
  calc
    quittingProfileLiveRoot reward endpoint.targetProfile
          (stage + 1 + offset) =
        quittingProfileLiveRoot reward
          (endpoint.orbitProfile endpoint.orbit.terminal_time)
          (stage + 1 + offset) := by
      exact quittingProfileLiveRoot_literalOneDateProfile_tail_eq
        (endpoint.orbitProfile endpoint.orbit.terminal_time)
        endpoint.who stage offset endpoint.action
    _ = quittingProfileLiveRoot reward profile (stage + 1 + offset) := by
      exact quittingLiteralPureRootProfile_tail_eq reward profile stage _ offset

end FinFourPureNonsingletonScreenedEndpoint

/-- Arbitrary Fin4 data satisfying the positive source-stage-mass floor
produces a certified singleton endpoint without a tail-debt hypothesis. -/
theorem quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (source : QuittingNonsingletonCoalition (Fin 4))
    (lambda : ℝ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hlambda : 0 < lambda)
    (hmass : lambda ≤ quittingStageCoalitionMass reward profile stage
      (quittingTerminalOfNonsingletonCoalition source)) :
    Nonempty (FinFourPureNonsingletonScreenedEndpoint reward minimum
      profile stage source lambda) := by
  have hlive := hmass.trans
    (quittingStageCoalitionMass_le_liveMass reward profile stage
      (quittingTerminalOfNonsingletonCoalition source))
  rcases exists_pureNonsingletonScreened_terminalOrbit_or_closedSegment
      reward minimum profile stage source lambda hminimum hminimumDebt
        hlambda hlive with horbit | hclosed
  · obtain ⟨orbit⟩ := horbit
    obtain ⟨who, action, singleton, hcard, hrouted, hstageMass⟩ :=
      orbit.terminal_at
    exact ⟨{
      lambda_pos := hlambda
      lambda_le_sourceStageMass := hmass
      orbit := orbit
      who := who
      action := action
      singleton := singleton
      singleton_card := hcard
      singleton_eq_routed := hrouted
      terminalStageMass_le := hstageMass
    }⟩
  · obtain ⟨closed⟩ := hclosed
    let base := closed.mapEdge fun _left _right hedge =>
      let screened := Classical.choice hedge
      Nonempty.intro screened.edge
    exact False.elim
      (not_nonempty_finFourSameStageEndpointClosedSegment ⟨base⟩)

end GameTheory
