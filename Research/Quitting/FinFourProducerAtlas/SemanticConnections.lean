/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.Leaves
import Research.Quitting.FinFourProducerAtlas.MinimumSingletonClockCompression

/-!
# Semantic connections between the source-distinct Fin4 atlas leaves

The two reached-singleton leaves expose one common literal endpoint while an
origin tag retains their distinct purification-path and terminal-orbit data.
Likewise, the two monodromy leaves share all dynamic data and differ only in
their exact cycle geometry.  Additively, owner-clock compression places the
minimum-singleton leaf and the existing reached endpoints behind a weaker
common core, reducing the directed residual classes from four to three.
These adapters normalize producer data; they do not discharge a residual or
produce a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open QuittingNonsingletonMinimumLawTransfer

/-! ## Common reached-singleton endpoint -/

/-- The complete origin of a concentrated singleton endpoint.  In the terminal
orbit case the selected singleton route is retained because it is existential
data not stored directly by the orbit producer. -/
inductive FinFourAtlasConcentratedSingletonOrigin
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) : Type
  | purified (producer : FinFourPurifiedSingletonProducer source)
  | terminalOrbit
      (producer : FinFourTerminalSingletonProducer source)
      (who : Fin 4)
      (action : Bool)
      (singleton : {S : Finset (Fin 4) // S.Nonempty})
      (singleton_card : singleton.val.card = 1)
      (routed : singleton.val = quittingPureEndpointRoutedCoalition
        (producer.orbit.orbit producer.orbit.terminal_time).1 who action)
      (stageMass_floor : producer.purification.low.lambda ≤
        quittingStageCoalitionMass reward
          (producer.terminalVertexTargetProfile who action)
          producer.purification.low.stage singleton)

namespace FinFourAtlasConcentratedSingletonOrigin

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The literal low row underlying either reached-singleton origin. -/
def low (origin : FinFourAtlasConcentratedSingletonOrigin source) :
    FinFourLowTailRow source :=
  match origin with
  | .purified producer => producer.low
  | .terminalOrbit producer .. => producer.purification.low

/-- The literal marked date selected by the retained low row. -/
def stage (origin : FinFourAtlasConcentratedSingletonOrigin source) : ℕ :=
  origin.low.stage

/-- The actual behavioral profile realizing the routed singleton. -/
def profile (origin : FinFourAtlasConcentratedSingletonOrigin source) :
    (quittingGame reward).BehaviorProfile :=
  match origin with
  | .purified producer => producer.singletonTargetProfile
  | .terminalOrbit producer who action .. =>
      producer.terminalVertexTargetProfile who action

/-- The actual singleton terminal coalition at the marked date. -/
def terminal (origin : FinFourAtlasConcentratedSingletonOrigin source) :
    {S : Finset (Fin 4) // S.Nonempty} :=
  match origin with
  | .purified producer => producer.singleton.singleton
  | .terminalOrbit _ _ _ singleton .. => singleton

/-- Both origins retain a literal singleton rather than only a law label. -/
theorem terminal_card (origin : FinFourAtlasConcentratedSingletonOrigin source) :
    origin.terminal.val.card = 1 := by
  cases origin with
  | purified producer => exact producer.singleton.singleton_card
  | terminalOrbit _ _ _ _ singletonCard _ _ => exact singletonCard

/-- Both actual target profiles carry the fixed low-row stage-mass floor. -/
theorem stageMass_floor
    (origin : FinFourAtlasConcentratedSingletonOrigin source) :
    origin.low.lambda ≤ quittingStageCoalitionMass reward origin.profile
      origin.stage origin.terminal := by
  cases origin with
  | purified producer => exact producer.singleton_stageMass_floor
  | terminalOrbit _ _ _ _ _ _ massFloor => exact massFloor

/-- Both actual target profiles retain the complete literal post-date live-root
tail of their own selected low row. -/
theorem postDate_liveRoot_eq
    (origin : FinFourAtlasConcentratedSingletonOrigin source) (offset : ℕ) :
    quittingProfileLiveRoot reward origin.profile
        (origin.stage + 1 + offset) =
      quittingProfileLiveRoot reward origin.low.profile
        (origin.stage + 1 + offset) := by
  cases origin with
  | purified producer => exact producer.singletonTarget_postDate_liveRoot_eq offset
  | terminalOrbit producer who action _ _ _ _ =>
      exact producer.terminalVertexTarget_postDate_liveRoot_eq who action offset

end FinFourAtlasConcentratedSingletonOrigin

/-- Common semantic endpoint data for both literal routes to a reached
singleton.  The origin field retains the full route-specific producer. -/
structure FinFourAtlasConcentratedSingletonEndpoint
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  origin : FinFourAtlasConcentratedSingletonOrigin source

namespace FinFourAtlasConcentratedSingletonEndpoint

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The literal selected low row, with its original source chronology. -/
def low (endpoint : FinFourAtlasConcentratedSingletonEndpoint source) :
    FinFourLowTailRow source :=
  endpoint.origin.low

/-- The literal marked date selected by the endpoint's retained low row. -/
def stage (endpoint : FinFourAtlasConcentratedSingletonEndpoint source) : ℕ :=
  endpoint.origin.stage

/-- The actual target profile at the reached singleton. -/
def profile (endpoint : FinFourAtlasConcentratedSingletonEndpoint source) :
    (quittingGame reward).BehaviorProfile :=
  endpoint.origin.profile

/-- The actual singleton terminal at the selected date. -/
def terminal (endpoint : FinFourAtlasConcentratedSingletonEndpoint source) :
    {S : Finset (Fin 4) // S.Nonempty} :=
  endpoint.origin.terminal

/-- The endpoint terminal is literally a singleton. -/
theorem terminal_card (endpoint : FinFourAtlasConcentratedSingletonEndpoint source) :
    endpoint.terminal.val.card = 1 :=
  endpoint.origin.terminal_card

/-- The actual target profile retains the fixed low-row stage-mass floor. -/
theorem stageMass_floor
    (endpoint : FinFourAtlasConcentratedSingletonEndpoint source) :
    endpoint.low.lambda ≤ quittingStageCoalitionMass reward endpoint.profile
      endpoint.stage endpoint.terminal :=
  endpoint.origin.stageMass_floor

/-- Literal equality of the complete post-date live-root tail. -/
theorem postDate_liveRoot_eq
    (endpoint : FinFourAtlasConcentratedSingletonEndpoint source) (offset : ℕ) :
    quittingProfileLiveRoot reward endpoint.profile
        (endpoint.stage + 1 + offset) =
      quittingProfileLiveRoot reward endpoint.low.profile
        (endpoint.stage + 1 + offset) :=
  endpoint.origin.postDate_liveRoot_eq offset

/-- Semantic tail equality derived from the stronger literal live-root tail
equality. -/
theorem postDateTail_eq
    (endpoint : FinFourAtlasConcentratedSingletonEndpoint source) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward endpoint.profile
          (endpoint.stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward endpoint.low.profile
          (endpoint.stage + 1)) := by
  apply quittingTerminalSemanticPair_eq_of_liveRoot_eq
  funext offset player
  change (quittingAllContinueProfileSpine reward endpoint.profile
      (endpoint.stage + 1)) player offset (quittingLiveHist reward offset) =
    (quittingAllContinueProfileSpine reward endpoint.low.profile
      (endpoint.stage + 1)) player offset (quittingLiveHist reward offset)
  rw [quittingAllContinueProfileSpine_apply_liveHist,
    quittingAllContinueProfileSpine_apply_liveHist]
  exact congrFun (endpoint.postDate_liveRoot_eq offset) player

end FinFourAtlasConcentratedSingletonEndpoint

namespace FinFourPurifiedSingletonProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Package a bounded-purification singleton without discarding its certified
finite path. -/
def toConcentratedEndpoint (producer : FinFourPurifiedSingletonProducer source) :
    FinFourAtlasConcentratedSingletonEndpoint source :=
  ⟨.purified producer⟩

end FinFourPurifiedSingletonProducer

namespace FinFourTerminalSingletonProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Select the terminal-orbit singleton while retaining both the original orbit
producer and the exact routed terminal witness. -/
theorem nonempty_concentratedEndpoint
    (producer : FinFourTerminalSingletonProducer source) :
    Nonempty (FinFourAtlasConcentratedSingletonEndpoint source) := by
  obtain ⟨who, action, singleton, hcard, hrouted, hmass⟩ :=
    producer.exists_singleton_with_stageMass_floor
  exact ⟨⟨.terminalOrbit producer who action singleton hcard hrouted hmass⟩⟩

end FinFourTerminalSingletonProducer

/-! ## Common monodromy endpoint and exact geometry -/

namespace FinFourMonodromyProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The literal coalition at one offset of the stored simple closed trace. -/
def cycleCoalition (producer : FinFourMonodromyProducer source)
    (offset : Fin producer.trace.segment.segment.period) : Finset (Fin 4) :=
  (producer.trace.orbit (producer.trace.segment.segment.start + offset)).1

end FinFourMonodromyProducer

/-- The two exact Fin4 geometries over one fixed monodromy trace. -/
inductive FinFourAtlasMonodromyGeometry
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (monodromy : FinFourMonodromyProducer source) : Type
  | commonHost
      (host : Fin 4)
      (host_mem : ∀ offset, host ∈ monodromy.cycleCoalition offset)
  | complementaryPair
      (first second : Fin monodromy.trace.segment.segment.period)
      (first_card : (monodromy.cycleCoalition first).card = 2)
      (second_card : (monodromy.cycleCoalition second).card = 2)
      (disjoint : Disjoint (monodromy.cycleCoalition first)
        (monodromy.cycleCoalition second))
      (complementary : monodromy.cycleCoalition second =
        (monodromy.cycleCoalition first)ᶜ)

/-- One common monodromy carrying all shared dynamic data and one exact Fin4
geometry witness. -/
structure FinFourAtlasMonodromyNode
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  monodromy : FinFourMonodromyProducer source
  geometry : FinFourAtlasMonodromyGeometry monodromy

namespace FinFourCommonHostMonodromyProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Repackage a common-host leaf without copying or reselecting its monodromy. -/
def toAtlasMonodromyNode (producer : FinFourCommonHostMonodromyProducer source) :
    FinFourAtlasMonodromyNode source :=
  ⟨producer.monodromy, .commonHost producer.host producer.host_mem⟩

end FinFourCommonHostMonodromyProducer

namespace FinFourComplementaryPairMonodromyProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Repackage a complementary-pair leaf while retaining every geometry field. -/
def toAtlasMonodromyNode
    (producer : FinFourComplementaryPairMonodromyProducer source) :
    FinFourAtlasMonodromyNode source :=
  ⟨producer.monodromy, .complementaryPair producer.first producer.second
    producer.first_card producer.second_card producer.disjoint
    producer.complementary⟩

end FinFourComplementaryPairMonodromyProducer

/-- Common-host geometry as a proposition on one fixed trace. -/
def FinFourMonodromyHasCommonHost
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (monodromy : FinFourMonodromyProducer source) : Prop :=
  ∃ host : Fin 4, ∀ offset, host ∈ monodromy.cycleCoalition offset

/-- Complementary-pair geometry as a proposition on one fixed trace. -/
def FinFourMonodromyHasComplementaryPair
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (monodromy : FinFourMonodromyProducer source) : Prop :=
  ∃ first second : Fin monodromy.trace.segment.segment.period,
    (monodromy.cycleCoalition first).card = 2 ∧
      (monodromy.cycleCoalition second).card = 2 ∧
      Disjoint (monodromy.cycleCoalition first)
        (monodromy.cycleCoalition second) ∧
      monodromy.cycleCoalition second = (monodromy.cycleCoalition first)ᶜ

/-- A common host cannot lie in both members of an exact complementary pair on
the same monodromy trace.  This does not compare independently selected traces. -/
theorem not_commonHost_and_complementaryPair_sameTrace
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (monodromy : FinFourMonodromyProducer source) :
    ¬ (FinFourMonodromyHasCommonHost monodromy ∧
      FinFourMonodromyHasComplementaryPair monodromy) := by
  rintro ⟨⟨host, hhost⟩, ⟨first, second, _hfirst, _hsecond, _hdisjoint, hcomp⟩⟩
  have hfirst := hhost first
  have hsecond := hhost second
  have hnot : host ∉ monodromy.cycleCoalition first := by
    simpa [hcomp] using hsecond
  exact hnot hfirst

/-! ## Four semantically directed residual nodes -/

/-- Four data-carrying residual classes after normalizing the two reached
singletons and the two geometries.  No constructor is a completion theorem. -/
inductive FinFourAtlasDirectedNode
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) : Type
  | minimumLawSingleton
      (source : FinFourMinimumAtomProducer reward bound)
      (terminal_card : source.atom.terminal.val.card = 1)
  | concentratedSingleton
      (source : FinFourMinimumAtomProducer reward bound)
      (endpoint : FinFourAtlasConcentratedSingletonEndpoint source)
  | tailEscape
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : TailEscapeSubsequence reward source.point source.atom)
  | monodromy
      (source : FinFourMinimumAtomProducer reward bound)
      (node : FinFourAtlasMonodromyNode source)

/-- Normalize every source-distinct atlas residual without discharging it.  The
terminal-orbit branch remains propositionally existential, avoiding a public
choice of its routed singleton. -/
theorem FinFourProducerResidual.nonempty_directedNode
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (residual : FinFourProducerResidual reward bound) :
    Nonempty (FinFourAtlasDirectedNode reward bound) := by
  cases residual with
  | minimumSingleton source terminalCard =>
      exact ⟨.minimumLawSingleton source terminalCard⟩
  | purifiedSingleton source producer =>
      exact ⟨.concentratedSingleton source producer.toConcentratedEndpoint⟩
  | terminalSingleton source producer =>
      obtain ⟨endpoint⟩ := producer.nonempty_concentratedEndpoint
      exact ⟨.concentratedSingleton source endpoint⟩
  | tailEscape source producer =>
      exact ⟨.tailEscape source producer⟩
  | commonHostMonodromy source producer =>
      exact ⟨.monodromy source producer.toAtlasMonodromyNode⟩
  | complementaryPairMonodromy source producer =>
      exact ⟨.monodromy source producer.toAtlasMonodromyNode⟩

/-! ## Three clock-compressed residual obligations -/

/-- Provenance for the weak concentrated-singleton core.  The reached case
retains the existing stronger low-row endpoint unchanged.  The owner-clock
case retains both the cofinal compression producer and one literal depth-zero
endpoint selected from it. -/
inductive FinFourAtlasWeakConcentratedSingletonOrigin
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) : Type
  | reached (endpoint : FinFourAtlasConcentratedSingletonEndpoint source)
  | ownerClock
      (producer : FinFourOwnerCompressedSingletonProducer source)
      (baseEndpoint : FinFourOwnerCompressedSingletonEndpoint source
        producer.chronology producer.owner
        source.minimumSingletonClockResolution 0)

/-- The common literal data exposed by both concentrated-singleton routes.
The origin retains stronger route-specific data, but this core makes no
target-side Nash, reprojection, return, regeneration, or consumer claim. -/
structure FinFourAtlasWeakConcentratedSingletonCore
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  origin : FinFourAtlasWeakConcentratedSingletonOrigin source

namespace FinFourAtlasWeakConcentratedSingletonCore

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The actual source-side profile from which the one-date target is read. -/
def referenceProfile (core : FinFourAtlasWeakConcentratedSingletonCore source) :
    (quittingGame reward).BehaviorProfile :=
  match core.origin with
  | .reached endpoint => endpoint.low.profile
  | .ownerClock _ endpoint => endpoint.referenceProfile

/-- The actual concentrated-singleton target profile. -/
def targetProfile (core : FinFourAtlasWeakConcentratedSingletonCore source) :
    (quittingGame reward).BehaviorProfile :=
  match core.origin with
  | .reached endpoint => endpoint.profile
  | .ownerClock _ endpoint => endpoint.targetProfile

/-- The literal date carrying the concentrated singleton. -/
def stage (core : FinFourAtlasWeakConcentratedSingletonCore source) : ℕ :=
  match core.origin with
  | .reached endpoint => endpoint.stage
  | .ownerClock _ endpoint => endpoint.stage

/-- The literal singleton terminal at the concentrated date. -/
def singleton (core : FinFourAtlasWeakConcentratedSingletonCore source) :
    {S : Finset (Fin 4) // S.Nonempty} :=
  match core.origin with
  | .reached endpoint => endpoint.terminal
  | .ownerClock _ _ => source.atom.terminal

/-- The scale shared by low-row concentration and owner-clock compression. -/
def resolution (_core : FinFourAtlasWeakConcentratedSingletonCore source) : ℝ :=
  source.minimumSingletonClockResolution

/-- Both routes retain an actual singleton, not merely a law coordinate. -/
theorem singleton_card (core : FinFourAtlasWeakConcentratedSingletonCore source) :
    core.singleton.val.card = 1 := by
  rcases core with ⟨origin⟩
  cases origin with
  | reached endpoint => exact endpoint.terminal_card
  | ownerClock producer _ => exact producer.terminal_card

/-- Both routes carry the canonical `mu^2 / 8` stage-mass floor.  The
owner-clock route actually proves the strict version and is weakened only at
this common interface. -/
theorem resolution_le_stageMass
    (core : FinFourAtlasWeakConcentratedSingletonCore source) :
    core.resolution ≤ quittingStageCoalitionMass reward core.targetProfile
      core.stage core.singleton := by
  rcases core with ⟨origin⟩
  cases origin with
  | reached endpoint =>
      simpa [resolution, targetProfile, stage, singleton,
        FinFourLowTailRow.lambda,
        FinFourMinimumAtomProducer.minimumSingletonClockResolution] using
        endpoint.stageMass_floor
  | ownerClock _ endpoint =>
      simpa [resolution, targetProfile, stage, singleton] using
        endpoint.target_stageMass_gt.le

/-- Both target profiles retain the complete literal live-root tail of their
own reference profile strictly after the selected date. -/
theorem postDate_liveRoot_eq
    (core : FinFourAtlasWeakConcentratedSingletonCore source) (offset : ℕ) :
    quittingProfileLiveRoot reward core.targetProfile
        (core.stage + 1 + offset) =
      quittingProfileLiveRoot reward core.referenceProfile
        (core.stage + 1 + offset) := by
  rcases core with ⟨origin⟩
  cases origin with
  | reached endpoint =>
      simpa [targetProfile, referenceProfile, stage] using
        endpoint.postDate_liveRoot_eq offset
  | ownerClock _ endpoint =>
      simpa [targetProfile, referenceProfile, stage] using
        endpoint.targetProfile_postDate_liveRoot_eq offset

/-- Semantic tail equality derived from the common literal tail equality. -/
theorem postDateTail_eq
    (core : FinFourAtlasWeakConcentratedSingletonCore source) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward core.targetProfile
          (core.stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward core.referenceProfile
          (core.stage + 1)) := by
  apply quittingTerminalSemanticPair_eq_of_liveRoot_eq
  funext offset player
  change (quittingAllContinueProfileSpine reward core.targetProfile
      (core.stage + 1)) player offset (quittingLiveHist reward offset) =
    (quittingAllContinueProfileSpine reward core.referenceProfile
      (core.stage + 1)) player offset (quittingLiveHist reward offset)
  rw [quittingAllContinueProfileSpine_apply_liveHist,
    quittingAllContinueProfileSpine_apply_liveHist]
  exact congrFun (core.postDate_liveRoot_eq offset) player

end FinFourAtlasWeakConcentratedSingletonCore

/-- The three remaining directed obligations after compressing a diffuse
minimum-law singleton into the common weak concentrated-singleton core.  No
constructor is a completion theorem. -/
inductive FinFourAtlasClockCompressedDirectedNode
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) : Type
  | concentratedSingleton
      (source : FinFourMinimumAtomProducer reward bound)
      (core : FinFourAtlasWeakConcentratedSingletonCore source)
  | tailEscape
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : TailEscapeSubsequence reward source.point source.atom)
  | monodromy
      (source : FinFourMinimumAtomProducer reward bound)
      (node : FinFourAtlasMonodromyNode source)

/-- Normalize every six-leaf residual to one of the three clock-compressed
obligations.  The minimum-singleton branch retains the full cofinal producer
and one selected depth-zero endpoint; it does not regenerate semantic source
data or invoke a concentrated-singleton consumer. -/
theorem FinFourProducerResidual.nonempty_clockCompressedDirectedNode
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (residual : FinFourProducerResidual reward bound) :
    Nonempty (FinFourAtlasClockCompressedDirectedNode reward bound) := by
  cases residual with
  | minimumSingleton source terminalCard =>
      obtain ⟨producer⟩ :=
        source.nonempty_ownerCompressedSingletonProducer terminalCard
      obtain ⟨baseEndpoint⟩ := producer.nonempty_baseEndpoint
      exact ⟨.concentratedSingleton source
        ⟨.ownerClock producer baseEndpoint⟩⟩
  | purifiedSingleton source producer =>
      exact ⟨.concentratedSingleton source
        ⟨.reached producer.toConcentratedEndpoint⟩⟩
  | terminalSingleton source producer =>
      obtain ⟨endpoint⟩ := producer.nonempty_concentratedEndpoint
      exact ⟨.concentratedSingleton source ⟨.reached endpoint⟩⟩
  | tailEscape source producer =>
      exact ⟨.tailEscape source producer⟩
  | commonHostMonodromy source producer =>
      exact ⟨.monodromy source producer.toAtlasMonodromyNode⟩
  | complementaryPairMonodromy source producer =>
      exact ⟨.monodromy source producer.toAtlasMonodromyNode⟩

end GameTheory
