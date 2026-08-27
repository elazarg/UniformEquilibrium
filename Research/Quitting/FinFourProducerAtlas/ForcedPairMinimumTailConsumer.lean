/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.ConcentratedSingleton.NonSingletonResidual
import Research.Quitting.FinFourProducerAtlas.ForcedPair

/-!
# Minimum-tail consumption of an arbitrary weak-core forced pair

The forced pair has a nonsingleton routed terminal, so the generic
concentrated compiler cannot return its singleton arm.  Its residual cluster
is the literal post-date semantic tail of the supplied weak core.  Global
minimality then gives the exact tail-escape versus minimum-tail split, while
the already selected paid endpoint supplies the quantitative minimum-tail
arm.
-/

noncomputable section

namespace GameTheory

open Filter

namespace FinFourWeakCoreForcedPairPacket

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {core : FinFourAtlasWeakConcentratedSingletonCore source}

/-- The actual semantic tail inherited from the supplied weak core. -/
def referenceTail (_packet : FinFourWeakCoreForcedPairPacket core) :
    QuittingTerminalSemanticPair (Fin 4) :=
  quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward core.referenceProfile
      (core.stage + 1))

/-- Named semantic identity for the forced target tail. -/
theorem forcedTargetTail_eq_referenceTail
    (packet : FinFourWeakCoreForcedPairPacket core) :
    packet.forcedAdapter.targetTail = packet.referenceTail := by
  unfold QuittingStageAtomConcentratedPacketAdapter.targetTail referenceTail
  exact packet.forcedPair_postDateTail_eq_reference

/-- Named semantic identity for the paid target tail. -/
theorem payerTargetTail_eq_referenceTail
    (packet : FinFourWeakCoreForcedPairPacket core) :
    packet.payerAdapter.targetTail = packet.referenceTail := by
  unfold QuittingStageAtomConcentratedPacketAdapter.targetTail referenceTail
  exact packet.payerTarget_postDateTail_eq_reference

/-- Named total-debt identity for the forced target tail. -/
theorem forcedTargetTailDebtSum_eq_reference
    (packet : FinFourWeakCoreForcedPairPacket core) :
    quittingTerminalSemanticDebtSum packet.forcedAdapter.targetTail =
      quittingTerminalSemanticDebtSum packet.referenceTail := by
  rw [packet.forcedTargetTail_eq_referenceTail]

/-- Named total-debt identity for the paid target tail. -/
theorem payerTargetTailDebtSum_eq_reference
    (packet : FinFourWeakCoreForcedPairPacket core) :
    quittingTerminalSemanticDebtSum packet.payerAdapter.targetTail =
      quittingTerminalSemanticDebtSum packet.referenceTail := by
  rw [packet.payerTargetTail_eq_referenceTail]

/-- The fixed pair enters the collision-minimum residual without a strategic
singleton alternative. -/
theorem nonempty_collisionMinimumResidual
    (packet : FinFourWeakCoreForcedPairPacket core) :
    Nonempty (QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 packet.forcedOwner packet.forcedAdapter.routedTerminal
        packet.forcedAdapter.packet) := by
  apply packet.forcedAdapter.packet
    |>.nonempty_collisionMinimumResidual_of_terminal_card_ne_one
  · rw [packet.forcedTerminal_card]
    norm_num
  · exact source.semantic_mem
  · exact source.minimum
  · exact source.minimumDebt_pos
  · exact packet.forcedAdapter.scale_pos
  · exact packet.forcedAdapter.scale_tendsto_zero

/-- Every residual cluster of the constant pair packet is exactly the actual
post-date semantic tail of the supplied weak core. -/
theorem collisionCluster_eq_postDateTail
    (packet : FinFourWeakCoreForcedPairPacket core)
    (residual : QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 packet.forcedOwner packet.forcedAdapter.routedTerminal
        packet.forcedAdapter.packet) :
    residual.cluster = packet.referenceTail := by
  have htail := residual.tail_tendsto
  have heq : (fun rank ↦
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (packet.forcedAdapter.profiles
            (packet.forcedAdapter.packet.subseq (residual.subseq rank)))
          (packet.forcedAdapter.packet.mark (residual.subseq rank) + 1))) =
      fun _rank ↦ packet.referenceTail := by
    funext rank
    simpa only [QuittingStageAtomConcentratedPacketAdapter.profiles,
      QuittingStageAtomConcentratedPacketAdapter.packet,
      QuittingStageAtomConcentratedPacketAdapter.packetWithScale,
      QuittingStageAtomConcentratedPacketAdapter.subseq,
      QuittingStageAtomConcentratedPacketAdapter.mark, id_eq,
      referenceTail] using packet.forcedPair_postDateTail_eq_reference
  rw [heq] at htail
  exact tendsto_nhds_unique htail tendsto_const_nhds

/-- Export-facing form of the cluster identity: the cluster is the semantic
pair of the actual all-Continue spine of `core.targetProfile`. -/
theorem collisionCluster_eq_corePostDateTail
    (packet : FinFourWeakCoreForcedPairPacket core)
    (residual : QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 packet.forcedOwner packet.forcedAdapter.routedTerminal
        packet.forcedAdapter.packet) :
    residual.cluster =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward core.targetProfile
          (core.stage + 1)) := by
  rw [packet.collisionCluster_eq_postDateTail residual, core.postDateTail_eq]
  rfl

/-- The weak-core resolution is at most one. -/
theorem resolution_le_one
    (_packet : FinFourWeakCoreForcedPairPacket core) :
    core.resolution ≤ 1 := by
  have hsimplex := terminalSemanticLawCarrier_mass_mem_stdSimplex
    source.point source.point_mem
  have hmassLeOne : source.point.2 (some source.atom.terminal) ≤ 1 := by
    have hle : source.point.2 (some source.atom.terminal) ≤
        ∑ outcome, source.point.2 outcome :=
      Finset.single_le_sum (fun outcome _ ↦ hsimplex.1 outcome)
        (Finset.mem_univ _)
    simpa only [hsimplex.2] using hle
  exact source.minimumSingletonClockResolution_lt_terminalMass.le.trans
    hmassLeOne

/-- Verbatim weak-core defect floor `resolution * D_* / 6`. -/
theorem resolution_mul_minimumDebt_div_six_le_payerDefect
    (packet : FinFourWeakCoreForcedPairPacket core) :
    core.resolution * quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
      quittingRootCoordinateNashDefect reward
        packet.payerAdapter.sourceTail.1 packet.payerAdapter.sourceRoot
          packet.payer := by
  have hdebt : 0 ≤ quittingTerminalSemanticDebtSum source.point.1 :=
    source.minimumDebt_pos.le
  have hmul : core.resolution *
      quittingTerminalSemanticDebtSum source.point.1 ≤
        quittingTerminalSemanticDebtSum source.point.1 :=
    mul_le_of_le_one_left hdebt packet.resolution_le_one
  calc
    core.resolution * quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
        quittingTerminalSemanticDebtSum source.point.1 / 3 := by linarith
    _ ≤ _ := packet.payerDefect_floor

/-- Verbatim weak-core gain floor `resolution^2 * D_* / 6`. -/
theorem resolution_sq_mul_minimumDebt_div_six_le_payerGain
    (packet : FinFourWeakCoreForcedPairPacket core) :
    core.resolution ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
      packet.payerGain := by
  have hsquare : core.resolution ^ 2 ≤ core.resolution := by
    have hpos : 0 ≤ core.resolution :=
      source.minimumSingletonClockResolution_pos.le
    have hproduct : 0 ≤ core.resolution * (1 - core.resolution) :=
      mul_nonneg hpos (sub_nonneg.mpr packet.resolution_le_one)
    nlinarith
  have hdebt : 0 ≤ quittingTerminalSemanticDebtSum source.point.1 :=
    source.minimumDebt_pos.le
  have hscaled := mul_le_mul_of_nonneg_right hsquare hdebt
  have hproduct : 0 ≤ core.resolution *
      quittingTerminalSemanticDebtSum source.point.1 :=
    mul_nonneg source.minimumSingletonClockResolution_pos.le hdebt
  calc
    core.resolution ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
        core.resolution *
          quittingTerminalSemanticDebtSum source.point.1 / 3 := by linarith
    _ ≤ packet.payerGain := packet.payerGain_floor

/-- Literal Part A consumer split: the residual tail is either strictly
off-minimum, or it is minimum-tail and carries the advertised fixed paid
endpoint.  The alternatives are exclusive by their displayed debt tests. -/
theorem tailEscape_or_minimumTail_fixedGain
    (packet : FinFourWeakCoreForcedPairPacket core)
    (residual : QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 packet.forcedOwner packet.forcedAdapter.routedTerminal
        packet.forcedAdapter.packet) :
    quittingTerminalSemanticDebtSum source.point.1 <
        quittingTerminalSemanticDebtSum residual.cluster ∨
      quittingTerminalSemanticDebtSum residual.cluster =
          quittingTerminalSemanticDebtSum source.point.1 ∧
        packet.payer ≠ packet.forcedOwner ∧
        core.resolution *
              quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
            quittingRootCoordinateNashDefect reward
              packet.payerAdapter.sourceTail.1
              packet.payerAdapter.sourceRoot packet.payer ∧
        core.resolution ^ 2 *
              quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
            packet.payerGain := by
  have hminimum := source.minimum residual.cluster residual.cluster_mem
  rcases hminimum.lt_or_eq with hescape | hfiber
  · exact Or.inl hescape
  · exact Or.inr ⟨hfiber.symm, packet.payer_ne_forcedOwner,
      packet.resolution_mul_minimumDebt_div_six_le_payerDefect,
      packet.resolution_sq_mul_minimumDebt_div_six_le_payerGain⟩

/-- Typed consumer outcome for one weak-core residual. -/
inductive TailOutcome
    (packet : FinFourWeakCoreForcedPairPacket core)
    (residual : QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 packet.forcedOwner packet.forcedAdapter.routedTerminal
        packet.forcedAdapter.packet) : Type
  | tailEscape
      (strict : quittingTerminalSemanticDebtSum source.point.1 <
        quittingTerminalSemanticDebtSum residual.cluster)
  | minimumTail
      (clusterDebt_eq : quittingTerminalSemanticDebtSum residual.cluster =
        quittingTerminalSemanticDebtSum source.point.1)
      (payer_ne : packet.payer ≠ packet.forcedOwner)
      (defect_floor : core.resolution *
            quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
          quittingRootCoordinateNashDefect reward
            packet.payerAdapter.sourceTail.1 packet.payerAdapter.sourceRoot
              packet.payer)
      (gain_floor : core.resolution ^ 2 *
            quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
          packet.payerGain)

/-- One-shot Part A capstone retaining the supplied core, selected literal
packet, exact residual, cluster provenance, and typed consumer outcome. -/
structure ResidualCapstone
    (core : FinFourAtlasWeakConcentratedSingletonCore source) where
  packet : FinFourWeakCoreForcedPairPacket core
  residual : QuittingConcentratedCollisionMinimumResidual reward
    source.point.1 packet.forcedOwner packet.forcedAdapter.routedTerminal
      packet.forcedAdapter.packet
  cluster_eq_corePostDateTail : residual.cluster =
    quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward core.targetProfile
        (core.stage + 1))
  outcome : TailOutcome packet residual

end FinFourWeakCoreForcedPairPacket

namespace FinFourAtlasWeakConcentratedSingletonCore

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Construct and consume the selected weak-core forced pair in one call. -/
theorem nonempty_forcedPairResidualCapstone
    (core : FinFourAtlasWeakConcentratedSingletonCore source) :
    Nonempty (FinFourWeakCoreForcedPairPacket.ResidualCapstone core) := by
  obtain ⟨packet⟩ := core.nonempty_forcedPairPacket
  obtain ⟨residual⟩ := packet.nonempty_collisionMinimumResidual
  have hcluster := packet.collisionCluster_eq_corePostDateTail residual
  rcases packet.tailEscape_or_minimumTail_fixedGain residual with
      hescape | hminimum
  · exact ⟨⟨packet, residual, hcluster,
      .tailEscape hescape⟩⟩
  · exact ⟨⟨packet, residual, hcluster,
      .minimumTail hminimum.1 hminimum.2.1 hminimum.2.2.1
        hminimum.2.2.2⟩⟩

end FinFourAtlasWeakConcentratedSingletonCore

end GameTheory
