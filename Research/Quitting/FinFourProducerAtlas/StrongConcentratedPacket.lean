/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.SemanticConnections
import Research.Quitting.PositiveStageAtomConcentratedPacket

/-!
# Strong concentrated packets from the Fin4 singleton routes

A positive singleton stage atom admits a distinct packet owner.  Updating that
owner to its exact best endpoint routes the source atom without loss and gives
the existing concentrated reprojection packet at the same resolution.  The
original singleton owner remains in the routed terminal, but the terminal has
cardinality one in Continue mode and two in Quit mode.

The weak atlas core supplies the canonical `mu^2 / 8` instance.  The retained
minimum-atom chronology also supplies an instance for every requested
`0 < lambda < mu` and depth without selecting another chronology.  No
target-side Nash, near-minimum, low-tail, return, regeneration, or downstream
consumer conclusion is asserted.
-/

noncomputable section

namespace GameTheory

open Filter

/-! ## A Fin4 singleton-stage payload -/

/-- A positive singleton source atom together with a distinct packet owner and
the resulting exact best-endpoint concentrated-packet adapter. -/
structure FinFourSingletonStageStrongConcentratedPacket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (sourceProfile : (quittingGame reward).BehaviorProfile)
    (sourceTerminal : {S : Finset (Fin 4) // S.Nonempty})
    (stage : ℕ) (resolution : ℝ) where
  singletonOwner : Fin 4
  sourceTerminal_eq : sourceTerminal.val = {singletonOwner}
  packetOwner : Fin 4
  packetOwner_ne_singletonOwner : packetOwner ≠ singletonOwner
  adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
    sourceTerminal packetOwner stage resolution

namespace FinFourSingletonStageStrongConcentratedPacket

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {sourceProfile : (quittingGame reward).BehaviorProfile}
  {sourceTerminal : {S : Finset (Fin 4) // S.Nonempty}}
  {stage : ℕ} {resolution : ℝ}

/-- The source singleton is not the singleton of the distinct packet owner. -/
theorem sourceTerminal_ne_packetOwner
    (strong : FinFourSingletonStageStrongConcentratedPacket reward
      sourceProfile sourceTerminal stage resolution) :
    sourceTerminal.val ≠ {strong.packetOwner} :=
  strong.adapter.sourceTerminal_ne_owner

/-- The original singleton owner survives either endpoint-routing mode. -/
theorem singletonOwner_mem_routedTerminal
    (strong : FinFourSingletonStageStrongConcentratedPacket reward
      sourceProfile sourceTerminal stage resolution) :
    strong.singletonOwner ∈ strong.adapter.routedTerminal.val := by
  rw [strong.adapter.routedTerminal_val]
  unfold QuittingStageAtomConcentratedPacketAdapter.routedCoalition
  cases haction : strong.adapter.action with
  | false =>
      simp [strong.sourceTerminal_eq,
        strong.packetOwner_ne_singletonOwner]
  | true =>
      simp [strong.sourceTerminal_eq]

/-- Routing is exactly singleton-preserving in Continue mode and exactly a
two-player terminal in Quit mode.  In particular, no unconditional routed
singleton assertion is made. -/
theorem routedTerminal_mode_and_card
    (strong : FinFourSingletonStageStrongConcentratedPacket reward
      sourceProfile sourceTerminal stage resolution) :
    (strong.adapter.action = false ∧
        strong.adapter.routedTerminal.val = {strong.singletonOwner} ∧
        strong.adapter.routedTerminal.val.card = 1) ∨
      (strong.adapter.action = true ∧
        strong.adapter.routedTerminal.val =
          {strong.packetOwner, strong.singletonOwner} ∧
        strong.adapter.routedTerminal.val.card = 2) := by
  cases haction : strong.adapter.action with
  | false =>
      left
      refine ⟨rfl, ?_, ?_⟩
      · simp [QuittingStageAtomConcentratedPacketAdapter.routedTerminal,
          QuittingStageAtomConcentratedPacketAdapter.routedCoalition,
          haction, strong.sourceTerminal_eq,
          strong.packetOwner_ne_singletonOwner]
      · simp [QuittingStageAtomConcentratedPacketAdapter.routedTerminal,
          QuittingStageAtomConcentratedPacketAdapter.routedCoalition,
          haction, strong.sourceTerminal_eq,
          strong.packetOwner_ne_singletonOwner]
  | true =>
      right
      refine ⟨rfl, ?_, ?_⟩
      · simp [QuittingStageAtomConcentratedPacketAdapter.routedTerminal,
          QuittingStageAtomConcentratedPacketAdapter.routedCoalition,
          haction, strong.sourceTerminal_eq]
      · simp [QuittingStageAtomConcentratedPacketAdapter.routedTerminal,
          QuittingStageAtomConcentratedPacketAdapter.routedCoalition,
          haction, strong.sourceTerminal_eq,
          strong.packetOwner_ne_singletonOwner]

/-- The generic packet's canonical scale is pointwise positive. -/
theorem scale_pos
    (strong : FinFourSingletonStageStrongConcentratedPacket reward
      sourceProfile sourceTerminal stage resolution) (rank : ℕ) :
    0 < strong.adapter.scale rank :=
  strong.adapter.scale_pos rank

/-- The generic packet's canonical scale tends to zero. -/
theorem scale_tendsto_zero
    (strong : FinFourSingletonStageStrongConcentratedPacket reward
      sourceProfile sourceTerminal stage resolution) :
    Tendsto strong.adapter.scale atTop (nhds 0) :=
  strong.adapter.scale_tendsto_zero

/-- Construct the Fin4 payload from a positive singleton stage atom. -/
theorem nonempty_of_singleton_stageMass
    (sourceProfile : (quittingGame reward).BehaviorProfile)
    (sourceTerminal : {S : Finset (Fin 4) // S.Nonempty})
    (stage : ℕ) (resolution : ℝ)
    (hcard : sourceTerminal.val.card = 1)
    (hresolution : 0 < resolution)
    (hmass : resolution ≤
      quittingStageCoalitionMass reward sourceProfile stage sourceTerminal) :
    Nonempty (FinFourSingletonStageStrongConcentratedPacket reward
      sourceProfile sourceTerminal stage resolution) := by
  obtain ⟨singletonOwner, hsingleton⟩ := Finset.card_eq_one.mp hcard
  obtain ⟨packetOwner, hpacketOwner⟩ :=
    Fintype.exists_ne_of_one_lt_card (by decide) singletonOwner
  have hterminal : sourceTerminal.val ≠ {packetOwner} := by
    intro heq
    have howners : singletonOwner = packetOwner := by
      simpa only [hsingleton, Finset.singleton_inj] using heq
    exact hpacketOwner howners.symm
  obtain ⟨adapter⟩ :=
    QuittingStageAtomConcentratedPacketAdapter.nonempty_of_stageMass
      sourceProfile sourceTerminal packetOwner stage resolution hterminal
        hresolution hmass
  exact ⟨{
    singletonOwner := singletonOwner
    sourceTerminal_eq := hsingleton
    packetOwner := packetOwner
    packetOwner_ne_singletonOwner := hpacketOwner
    adapter := adapter
  }⟩

end FinFourSingletonStageStrongConcentratedPacket

/-! ## The weak atlas core at the canonical resolution -/

/-- The strong packet attached to the exact weak concentrated-singleton core.
The dependent index retains the core's origin and all source provenance. -/
structure FinFourAtlasWeakStrongConcentratedPacket
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (core : FinFourAtlasWeakConcentratedSingletonCore source) where
  strong : FinFourSingletonStageStrongConcentratedPacket reward
    core.targetProfile core.singleton core.stage core.resolution

namespace FinFourAtlasWeakStrongConcentratedPacket

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {core : FinFourAtlasWeakConcentratedSingletonCore source}

/-- The actual best-endpoint adapter, at the same canonical resolution as the
weak core. -/
theorem adapter (packet : FinFourAtlasWeakStrongConcentratedPacket core) :
    QuittingStageAtomConcentratedPacketAdapter reward core.targetProfile
      core.singleton packet.strong.packetOwner core.stage core.resolution :=
  packet.strong.adapter

/-- The packet keeps the core's canonical `mu^2 / 8` resolution exactly. -/
theorem packet_resolution_eq
    (packet : FinFourAtlasWeakStrongConcentratedPacket core) :
    packet.adapter.packet.resolution =
      source.minimumSingletonClockResolution := rfl

/-- The original singleton owner remains in the routed target terminal. -/
theorem singletonOwner_mem_routedTerminal
    (packet : FinFourAtlasWeakStrongConcentratedPacket core) :
    packet.strong.singletonOwner ∈ packet.adapter.routedTerminal.val :=
  packet.strong.singletonOwner_mem_routedTerminal

/-- The routed target is a singleton in Continue mode and a pair in Quit
mode. -/
theorem routedTerminal_mode_and_card
    (packet : FinFourAtlasWeakStrongConcentratedPacket core) :
    (packet.adapter.action = false ∧
        packet.adapter.routedTerminal.val =
          {packet.strong.singletonOwner} ∧
        packet.adapter.routedTerminal.val.card = 1) ∨
      (packet.adapter.action = true ∧
        packet.adapter.routedTerminal.val =
          {packet.strong.packetOwner, packet.strong.singletonOwner} ∧
        packet.adapter.routedTerminal.val.card = 2) :=
  packet.strong.routedTerminal_mode_and_card

/-- The returned packet scale is pointwise positive. -/
theorem scale_pos (packet : FinFourAtlasWeakStrongConcentratedPacket core)
    (rank : ℕ) : 0 < packet.adapter.scale rank :=
  packet.strong.scale_pos rank

/-- The returned packet scale tends to zero. -/
theorem scale_tendsto_zero
    (packet : FinFourAtlasWeakStrongConcentratedPacket core) :
    Tendsto packet.adapter.scale atTop (nhds 0) :=
  packet.strong.scale_tendsto_zero

end FinFourAtlasWeakStrongConcentratedPacket

namespace FinFourAtlasWeakConcentratedSingletonCore

/-- Every weak atlas concentrated-singleton core yields the strong generic
packet at the same canonical `mu^2 / 8` resolution. -/
theorem nonempty_strongConcentratedPacket
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (core : FinFourAtlasWeakConcentratedSingletonCore source) :
    Nonempty (FinFourAtlasWeakStrongConcentratedPacket core) := by
  obtain ⟨strong⟩ :=
    FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass
      core.targetProfile core.singleton core.stage core.resolution
        core.singleton_card source.minimumSingletonClockResolution_pos
          core.resolution_le_stageMass
  exact ⟨⟨strong⟩⟩

end FinFourAtlasWeakConcentratedSingletonCore

/-! ## Arbitrary scales on the producer's fixed chronology -/

/-- A strong packet at an arbitrary admissible resolution and depth on the
producer's already retained common chronology. -/
structure FinFourOwnerCompressedStrongConcentratedPacket
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (producer : FinFourOwnerCompressedSingletonProducer source)
    (lambda : ℝ) (depth : ℕ) where
  lambda_pos : 0 < lambda
  lambda_lt_terminalMass :
    lambda < source.point.2 (some source.atom.terminal)
  endpoint : FinFourOwnerCompressedSingletonEndpoint source
    producer.chronology producer.owner lambda depth
  strong : FinFourSingletonStageStrongConcentratedPacket reward
    endpoint.targetProfile source.atom.terminal endpoint.stage lambda

namespace FinFourOwnerCompressedStrongConcentratedPacket

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {producer : FinFourOwnerCompressedSingletonProducer source}
  {lambda : ℝ} {depth : ℕ}

/-- The actual best-endpoint adapter at the requested scale and depth. -/
theorem adapter
    (packet : FinFourOwnerCompressedStrongConcentratedPacket producer
      lambda depth) :
    QuittingStageAtomConcentratedPacketAdapter reward
      packet.endpoint.targetProfile source.atom.terminal
      packet.strong.packetOwner packet.endpoint.stage lambda :=
  packet.strong.adapter

/-- The packet keeps the requested resolution exactly. -/
theorem packet_resolution_eq
    (packet : FinFourOwnerCompressedStrongConcentratedPacket producer
      lambda depth) :
    packet.adapter.packet.resolution = lambda := rfl

/-- The payload's singleton owner is the producer's original atom owner. -/
theorem singletonOwner_eq_owner
    (packet : FinFourOwnerCompressedStrongConcentratedPacket producer
      lambda depth) :
    packet.strong.singletonOwner = producer.owner := by
  have hsource := packet.strong.sourceTerminal_eq
  rw [producer.terminal_eq] at hsource
  simpa only [Finset.singleton_inj] using hsource.symm

/-- The original minimum-singleton owner remains in the routed terminal. -/
theorem owner_mem_routedTerminal
    (packet : FinFourOwnerCompressedStrongConcentratedPacket producer
      lambda depth) :
    producer.owner ∈ packet.adapter.routedTerminal.val := by
  have hmem := packet.strong.singletonOwner_mem_routedTerminal
  change producer.owner ∈ packet.strong.adapter.routedTerminal.val
  simpa only [packet.singletonOwner_eq_owner] using hmem

/-- The routed terminal has the exact one-or-two cardinality dictated by the
selected Boolean endpoint. -/
theorem routedTerminal_mode_and_card
    (packet : FinFourOwnerCompressedStrongConcentratedPacket producer
      lambda depth) :
    (packet.adapter.action = false ∧
        packet.adapter.routedTerminal.val =
          {producer.owner} ∧
        packet.adapter.routedTerminal.val.card = 1) ∨
      (packet.adapter.action = true ∧
        packet.adapter.routedTerminal.val =
          {packet.strong.packetOwner, producer.owner} ∧
        packet.adapter.routedTerminal.val.card = 2) :=
  packet.strong.routedTerminal_mode_and_card
    |>.imp (fun h ↦ by simpa only [packet.singletonOwner_eq_owner] using h)
      (fun h ↦ by simpa only [packet.singletonOwner_eq_owner] using h)

/-- The returned packet scale is pointwise positive. -/
theorem scale_pos
    (packet : FinFourOwnerCompressedStrongConcentratedPacket producer
      lambda depth) (rank : ℕ) :
    0 < packet.adapter.scale rank :=
  packet.strong.scale_pos rank

/-- The returned packet scale tends to zero. -/
theorem scale_tendsto_zero
    (packet : FinFourOwnerCompressedStrongConcentratedPacket producer
      lambda depth) :
    Tendsto packet.adapter.scale atTop (nhds 0) :=
  packet.strong.scale_tendsto_zero

end FinFourOwnerCompressedStrongConcentratedPacket

namespace FinFourOwnerCompressedSingletonProducer

/-- For every admissible resolution and depth, construct a strong packet from
an endpoint of this producer's fixed chronology.  The chronology is not
reselected inside either quantifier. -/
theorem nonempty_strongConcentratedPacket
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (producer : FinFourOwnerCompressedSingletonProducer source)
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (hlambda_lt : lambda < source.point.2 (some source.atom.terminal))
    (depth : ℕ) :
    Nonempty (FinFourOwnerCompressedStrongConcentratedPacket producer
      lambda depth) := by
  obtain ⟨endpoint⟩ :=
    producer.chronology.nonempty_ownerCompressedSingleton producer.owner
      producer.terminal_eq lambda hlambda_pos hlambda_lt depth
  obtain ⟨strong⟩ :=
    FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass
      endpoint.targetProfile source.atom.terminal endpoint.stage lambda
        producer.terminal_card hlambda_pos endpoint.target_stageMass_gt.le
  exact ⟨{
    lambda_pos := hlambda_pos
    lambda_lt_terminalMass := hlambda_lt
    endpoint := endpoint
    strong := strong
  }⟩

end FinFourOwnerCompressedSingletonProducer

end GameTheory
