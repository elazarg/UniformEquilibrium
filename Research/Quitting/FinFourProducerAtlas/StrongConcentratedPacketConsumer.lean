/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.ConcentratedSingleton.Compression
import Research.Quitting.FinFourProducerAtlas.StrongConcentratedPacket

/-!
# Consuming the strong Fin4 concentrated packet

The strong singleton-stage adapter supplies exactly the packet, distinct
packet owner, retained singleton member, and vanishing scale required by the
existing concentrated minimum-fiber consumer.  This file composes those
interfaces without changing the atlas source or the literal adapter.

The table-level atomic handoff is already universal under the retained
terminal witness.  Consequently the strategic arm is exactly Continue mode,
while Quit mode forces the collision-minimum residual on the same packet.
This action normal form does not consume either mode or assert that a
collision residual is absent in Continue mode.
-/

noncomputable section

namespace GameTheory

/-! ## The exact consumer output on one produced payload -/

/-- The named left arm of the strong-packet consumer.  Its atomic handoff is
table-level data; the concentrated dispatch retains the actual packet. -/
def FinFourStrongConcentratedPacketStrategicArm
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    {sourceProfile : (quittingGame reward).BehaviorProfile}
    {sourceTerminal : {S : Finset (Fin 4) // S.Nonempty}}
    {stage : ℕ} {resolution : ℝ}
    (strong : FinFourSingletonStageStrongConcentratedPacket reward
      sourceProfile sourceTerminal stage resolution) : Prop :=
  HasQuittingConcentratedSingletonStrategicDispatch source.residual.witness
      strong.adapter.packet strong.singletonOwner ∧
    (HasQuittingStaticAtomicToggleHandoff reward ∨
      HasQuittingExactPlayerDeletionAtGap reward strong.singletonOwner
        source.residual.witness.terminalGap)

/-- The exact output of applying the retained minimum source to one strong
singleton-stage packet.  The collision branch remains an unresolved residual
on the same literal packet. -/
def FinFourStrongConcentratedPacketConsumerResult
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    {sourceProfile : (quittingGame reward).BehaviorProfile}
    {sourceTerminal : {S : Finset (Fin 4) // S.Nonempty}}
    {stage : ℕ} {resolution : ℝ}
    (strong : FinFourSingletonStageStrongConcentratedPacket reward
      sourceProfile sourceTerminal stage resolution) : Prop :=
  FinFourStrongConcentratedPacketStrategicArm source strong ∨
    Nonempty (QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 strong.packetOwner strong.adapter.routedTerminal
        strong.adapter.packet)

namespace FinFourSingletonStageStrongConcentratedPacket

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {sourceProfile : (quittingGame reward).BehaviorProfile}
  {sourceTerminal : {S : Finset (Fin 4) // S.Nonempty}}
  {stage : ℕ} {resolution : ℝ}

/-- Consume exactly the packet produced from one singleton stage atom against
the retained atlas minimum.  The original singleton owner is the distinct
routed member required by the existing consumer. -/
theorem consumerResult
    (strong : FinFourSingletonStageStrongConcentratedPacket reward
      sourceProfile sourceTerminal stage resolution) :
    FinFourStrongConcentratedPacketConsumerResult source strong := by
  have hdispatch :=
    source.residual.witness.concentratedPacket_singletonStrategic_or_collisionMinimumResidual
      source.point.1 strong.adapter.packet strong.singletonOwner
        strong.packetOwner_ne_singletonOwner.symm
        strong.singletonOwner_mem_routedTerminal source.semantic_mem
        source.minimum source.minimumDebt_pos strong.scale_pos
        strong.scale_tendsto_zero
  rcases hdispatch with hstrategic | hcollision
  · left
    exact ⟨hstrategic,
      Or.inl source.residual.witness.hasStaticAtomicToggleHandoff⟩
  · exact Or.inr hcollision

/-- For a strong Fin4 packet, the concentrated strategic dispatch is exactly
the Continue routing mode. -/
theorem hasStrategicDispatch_iff_action_eq_false
    (strong : FinFourSingletonStageStrongConcentratedPacket reward
      sourceProfile sourceTerminal stage resolution) :
    HasQuittingConcentratedSingletonStrategicDispatch source.residual.witness
        strong.adapter.packet strong.singletonOwner ↔
      strong.adapter.action = false := by
  rw [hasQuittingConcentratedSingletonStrategicDispatch_iff_terminal_eq
    source.residual.witness strong.adapter.packet strong.singletonOwner
      strong.packetOwner_ne_singletonOwner.symm strong.scale_pos
      strong.scale_tendsto_zero]
  constructor
  · intro hterminal
    rcases strong.routedTerminal_mode_and_card with hcontinue | hquit
    · exact hcontinue.1
    · have hcard : strong.adapter.routedTerminal.val.card = 1 := by
        rw [hterminal]
        simp
      omega
  · intro haction
    rcases strong.routedTerminal_mode_and_card with hcontinue | hquit
    · exact hcontinue.2.1
    · simp [haction] at hquit

/-- The complete named strategic arm is exactly Continue mode.  Its static
handoff conjunct is discharged by the source witness before the packet is
selected. -/
theorem strategicArm_iff_action_eq_false
    (strong : FinFourSingletonStageStrongConcentratedPacket reward
      sourceProfile sourceTerminal stage resolution) :
    FinFourStrongConcentratedPacketStrategicArm source strong ↔
      strong.adapter.action = false := by
  constructor
  · intro hstrategic
    exact strong.hasStrategicDispatch_iff_action_eq_false.mp hstrategic.1
  · intro haction
    exact ⟨strong.hasStrategicDispatch_iff_action_eq_false.mpr haction,
      Or.inl source.residual.witness.hasStaticAtomicToggleHandoff⟩

/-- Quit mode rules out the strategic arm and therefore forces the existing
collision-minimum residual on the same source, minimum, owner, terminal, and
packet. -/
theorem collisionMinimumResidual_of_action_eq_true
    (strong : FinFourSingletonStageStrongConcentratedPacket reward
      sourceProfile sourceTerminal stage resolution)
    (haction : strong.adapter.action = true) :
    Nonempty (QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 strong.packetOwner strong.adapter.routedTerminal
        strong.adapter.packet) := by
  rcases strong.consumerResult (source := source) with hstrategic | hcollision
  · have hfalse := strong.strategicArm_iff_action_eq_false.mp hstrategic
    simp [haction] at hfalse
  · exact hcollision

/-- Select the checked consumer output by the adapter's exact Boolean mode.
The alternatives are action-exclusive, but no absence of a collision residual
in Continue mode is asserted. -/
theorem actionIndexedConsumerResult
    (strong : FinFourSingletonStageStrongConcentratedPacket reward
      sourceProfile sourceTerminal stage resolution) :
    (strong.adapter.action = false ∧
        FinFourStrongConcentratedPacketStrategicArm source strong) ∨
      (strong.adapter.action = true ∧
        Nonempty (QuittingConcentratedCollisionMinimumResidual reward
          source.point.1 strong.packetOwner strong.adapter.routedTerminal
            strong.adapter.packet)) := by
  by_cases haction : strong.adapter.action = false
  · exact Or.inl ⟨haction,
      strong.strategicArm_iff_action_eq_false.mpr haction⟩
  · have htrue : strong.adapter.action = true := by
      cases hmode : strong.adapter.action <;> simp_all
    exact Or.inr ⟨htrue,
      strong.collisionMinimumResidual_of_action_eq_true htrue⟩

end FinFourSingletonStageStrongConcentratedPacket

/-! ## Weak-core provenance -/

/-- Consumer data indexed by the exact weak atlas core.  The produced strong
packet retains the core origin and its actual adapter; the result field refers
to that same adapter rather than an independently selected packet. -/
structure FinFourAtlasWeakStrongConcentratedPacketConsumption
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (core : FinFourAtlasWeakConcentratedSingletonCore source) where
  produced : FinFourAtlasWeakStrongConcentratedPacket core
  result : FinFourStrongConcentratedPacketConsumerResult source produced.strong

namespace FinFourAtlasWeakStrongConcentratedPacketConsumption

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {core : FinFourAtlasWeakConcentratedSingletonCore source}

/-- The literal best-endpoint adapter stored by the produced packet. -/
theorem adapter
    (consumption : FinFourAtlasWeakStrongConcentratedPacketConsumption core) :
    QuittingStageAtomConcentratedPacketAdapter reward core.targetProfile
      core.singleton consumption.produced.strong.packetOwner core.stage
        core.resolution :=
  consumption.produced.adapter

/-- The consumer's exact strategic-versus-collision split on the same source,
core, and adapter. -/
theorem strategic_or_collisionMinimumResidual
    (consumption : FinFourAtlasWeakStrongConcentratedPacketConsumption core) :
    (HasQuittingConcentratedSingletonStrategicDispatch source.residual.witness
          consumption.adapter.packet
          consumption.produced.strong.singletonOwner ∧
        (HasQuittingStaticAtomicToggleHandoff reward ∨
          HasQuittingExactPlayerDeletionAtGap reward
            consumption.produced.strong.singletonOwner
            source.residual.witness.terminalGap)) ∨
      Nonempty (QuittingConcentratedCollisionMinimumResidual reward
        source.point.1 consumption.produced.strong.packetOwner
          consumption.adapter.routedTerminal consumption.adapter.packet) :=
  consumption.result

end FinFourAtlasWeakStrongConcentratedPacketConsumption

namespace FinFourAtlasWeakConcentratedSingletonCore

/-- Construct and consume the strong packet without discarding the supplied
weak core or its origin. -/
theorem nonempty_strongConcentratedPacketConsumption
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (core : FinFourAtlasWeakConcentratedSingletonCore source) :
    Nonempty (FinFourAtlasWeakStrongConcentratedPacketConsumption core) := by
  obtain ⟨produced⟩ := core.nonempty_strongConcentratedPacket
  exact ⟨{
    produced := produced
    result := produced.strong.consumerResult
  }⟩

end FinFourAtlasWeakConcentratedSingletonCore

/-! ## Arbitrary-resolution owner-clock provenance -/

/-- Consumer data for one requested resolution and depth on a producer's
already retained chronology.  The endpoint and strong adapter remain stored
inside `produced`. -/
structure FinFourOwnerCompressedStrongConcentratedPacketConsumption
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (producer : FinFourOwnerCompressedSingletonProducer source)
    (lambda : ℝ) (depth : ℕ) where
  produced : FinFourOwnerCompressedStrongConcentratedPacket producer
    lambda depth
  result : FinFourStrongConcentratedPacketConsumerResult source produced.strong

namespace FinFourOwnerCompressedStrongConcentratedPacketConsumption

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {producer : FinFourOwnerCompressedSingletonProducer source}
  {lambda : ℝ} {depth : ℕ}

/-- The literal adapter at the requested resolution and depth. -/
theorem adapter
    (consumption :
      FinFourOwnerCompressedStrongConcentratedPacketConsumption producer
        lambda depth) :
    QuittingStageAtomConcentratedPacketAdapter reward
      consumption.produced.endpoint.targetProfile source.atom.terminal
      consumption.produced.strong.packetOwner
      consumption.produced.endpoint.stage lambda :=
  consumption.produced.adapter

/-- The same exact consumer split for an arbitrary admissible owner-clock
resolution and depth. -/
theorem strategic_or_collisionMinimumResidual
    (consumption :
      FinFourOwnerCompressedStrongConcentratedPacketConsumption producer
        lambda depth) :
    (HasQuittingConcentratedSingletonStrategicDispatch source.residual.witness
          consumption.adapter.packet
          consumption.produced.strong.singletonOwner ∧
        (HasQuittingStaticAtomicToggleHandoff reward ∨
          HasQuittingExactPlayerDeletionAtGap reward
            consumption.produced.strong.singletonOwner
            source.residual.witness.terminalGap)) ∨
      Nonempty (QuittingConcentratedCollisionMinimumResidual reward
        source.point.1 consumption.produced.strong.packetOwner
          consumption.adapter.routedTerminal consumption.adapter.packet) :=
  consumption.result

end FinFourOwnerCompressedStrongConcentratedPacketConsumption

namespace FinFourOwnerCompressedSingletonProducer

/-- At every admissible scale and depth, construct and consume a packet from
this producer's one fixed chronology. -/
theorem nonempty_strongConcentratedPacketConsumption
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (producer : FinFourOwnerCompressedSingletonProducer source)
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (hlambda_lt : lambda < source.point.2 (some source.atom.terminal))
    (depth : ℕ) :
    Nonempty
      (FinFourOwnerCompressedStrongConcentratedPacketConsumption producer
        lambda depth) := by
  obtain ⟨produced⟩ := producer.nonempty_strongConcentratedPacket
    lambda hlambda_pos hlambda_lt depth
  exact ⟨{
    produced := produced
    result := produced.strong.consumerResult
  }⟩

end FinFourOwnerCompressedSingletonProducer

end GameTheory
