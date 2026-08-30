/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.SingletonFrameForcedPair
import Research.Quitting.FinFourProducerAtlas.SourcePreservingSingletonFrames

/-!
# Forced pairs from source-preserving singleton frames

This module factors the paid forced-pair construction through the neutral
singleton-frame interface.  The packet is indexed by the exact entrance and
frame, rather than by the older two-constructor weak-core origin.  It therefore
retains the one source chronology selected by the source-preserving atlas.

The construction uses only the frame's singleton card and positive stage-mass
floor.  Its root-stack Nash and convergence fields remain available through
the frame and enclosing cofinal packet, but are not hypotheses of this local
compiler.  No target-side Nash, near-minimality, total-debt descent, return,
regeneration, or uniform-equilibrium conclusion is asserted.
-/

noncomputable section

namespace GameTheory

open QuittingNonsingletonMinimumLawTransfer
open QuittingSureSetOwnerRepair

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {entrance : FinFourSourcePreservingSingletonEntrance source}

namespace FinFourSourcePreservingSingletonFrame

/-- Forget the source-preserving entrance while retaining the exact local
singleton frame and its canonical resolution. -/
def toSingletonFrame
    (frame : FinFourSourcePreservingSingletonFrame entrance) :
    FinFourSingletonFrame source where
  referenceProfile := frame.referenceProfile
  targetProfile := frame.targetProfile
  stage := frame.stage
  singleton := frame.singleton
  resolution := source.minimumSingletonClockResolution
  resolution_pos := source.minimumSingletonClockResolution_pos
  singleton_card := frame.singleton_card
  resolution_le_stageMass := frame.resolution_le_stageMass
  postDateSpine_eq_reference := frame.postDateSpine_eq_reference

/-- The literal pure-singleton sibling at the frame's marked date. -/
def pureSingletonProfile
    (frame : FinFourSourcePreservingSingletonFrame entrance) :
    (quittingGame reward).BehaviorProfile :=
  frame.toSingletonFrame.pureSingletonProfile

/-- Pureification puts the complete reached mass on the singleton. -/
theorem pureSingleton_stageMass_eq_liveMass
    (frame : FinFourSourcePreservingSingletonFrame entrance) :
    quittingStageCoalitionMass reward frame.pureSingletonProfile frame.stage
        frame.singleton =
      quittingLiveMass reward frame.targetProfile frame.stage := by
  exact frame.toSingletonFrame.pureSingleton_stageMass_eq_liveMass

/-- The canonical frame resolution survives pureification. -/
theorem resolution_le_pureSingletonStageMass
    (frame : FinFourSourcePreservingSingletonFrame entrance) :
    source.minimumSingletonClockResolution ≤
      quittingStageCoalitionMass reward frame.pureSingletonProfile frame.stage
        frame.singleton := by
  exact frame.toSingletonFrame.resolution_le_pureSingletonStageMass

/-- Pureification changes no complete behavior away from the marked date. -/
theorem pureSingletonProfile_eq_of_time_ne
    (frame : FinFourSourcePreservingSingletonFrame entrance)
    (player : Fin 4) (time : ℕ)
    (history : (quittingGame reward).Hist time)
    (htime : time ≠ frame.stage) :
    frame.pureSingletonProfile player time history =
      frame.targetProfile player time history := by
  exact congrFun
    (frame.toSingletonFrame.pureSingletonProfile_at_of_ne time htime player)
    history

/-- Pureification retains the frame's complete post-date source spine. -/
theorem pureSingleton_postDateSpine_eq_reference
    (frame : FinFourSourcePreservingSingletonFrame entrance) :
    quittingAllContinueProfileSpine reward frame.pureSingletonProfile
        (frame.stage + 1) =
      quittingAllContinueProfileSpine reward frame.referenceProfile
        (frame.stage + 1) := by
  exact frame.toSingletonFrame.pureSingleton_postDateSpine_eq_reference

end FinFourSourcePreservingSingletonFrame

/-- A full-gap forced pair and paid endpoint attached to one exact
source-preserving singleton frame. -/
structure FinFourSourcePreservingForcedPairPacket
    (frame : FinFourSourcePreservingSingletonFrame entrance) where
  singletonOwner : Fin 4
  singleton_eq : frame.singleton.val = {singletonOwner}
  forcedOwner : Fin 4
  forcedOwner_ne_singletonOwner : forcedOwner ≠ singletonOwner
  terminalGap_join :
    quittingSetReward reward {singletonOwner} forcedOwner +
          source.residual.witness.terminalGap ≤
      quittingSetReward reward {singletonOwner, forcedOwner} forcedOwner
  forcedAdapter : QuittingStageAtomConcentratedPacketAdapter reward
    frame.pureSingletonProfile frame.singleton forcedOwner frame.stage
      source.minimumSingletonClockResolution
  forcedAction_eq_true : forcedAdapter.action = true
  payer : Fin 4
  payer_ne_forcedOwner : payer ≠ forcedOwner
  payerAdapter : QuittingStageAtomConcentratedPacketAdapter reward
    forcedAdapter.targetProfile forcedAdapter.routedTerminal payer frame.stage
      source.minimumSingletonClockResolution
  payerDefect_floor :
    quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      quittingRootCoordinateNashDefect reward payerAdapter.sourceTail.1
        payerAdapter.sourceRoot payer

namespace FinFourSourcePreservingForcedPairPacket

variable {frame : FinFourSourcePreservingSingletonFrame entrance}

/-- Forget the source-preserving wrapper while retaining the complete common
forced-pair packet. -/
def toSingletonFrameForcedPairPacket
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    FinFourSingletonFrameForcedPairPacket frame.toSingletonFrame where
  singletonOwner := packet.singletonOwner
  singleton_eq := packet.singleton_eq
  forcedOwner := packet.forcedOwner
  forcedOwner_ne_singletonOwner := packet.forcedOwner_ne_singletonOwner
  terminalGap_join := packet.terminalGap_join
  forcedAdapter := packet.forcedAdapter
  forcedAction_eq_true := packet.forcedAction_eq_true
  payer := packet.payer
  payer_ne_forcedOwner := packet.payer_ne_forcedOwner
  payerAdapter := packet.payerAdapter
  payerDefect_floor := packet.payerDefect_floor

/-- Restore the source-preserving wrapper around one common packet. -/
def ofSingletonFrameForcedPairPacket
    (packet : FinFourSingletonFrameForcedPairPacket frame.toSingletonFrame) :
    FinFourSourcePreservingForcedPairPacket frame where
  singletonOwner := packet.singletonOwner
  singleton_eq := packet.singleton_eq
  forcedOwner := packet.forcedOwner
  forcedOwner_ne_singletonOwner := packet.forcedOwner_ne_singletonOwner
  terminalGap_join := packet.terminalGap_join
  forcedAdapter := packet.forcedAdapter
  forcedAction_eq_true := packet.forcedAction_eq_true
  payer := packet.payer
  payer_ne_forcedOwner := packet.payer_ne_forcedOwner
  payerAdapter := packet.payerAdapter
  payerDefect_floor := packet.payerDefect_floor

/-- The exact monodromy-free residual retained by the entrance. -/
def residual
    (_packet : FinFourSourcePreservingForcedPairPacket frame) :
    FinFourProducerResidualWithoutMonodromy reward bound :=
  entrance.toResidual

/-- The routed forced terminal is the displayed pair. -/
theorem forcedTerminal_val
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    packet.forcedAdapter.routedTerminal.val =
      {packet.singletonOwner, packet.forcedOwner} :=
  packet.toSingletonFrameForcedPairPacket.forcedTerminal_val

/-- The routed forced terminal is genuinely a pair. -/
theorem forcedTerminal_card
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    packet.forcedAdapter.routedTerminal.val.card = 2 :=
  packet.toSingletonFrameForcedPairPacket.forcedTerminal_card

/-- The first adapter, exposed as the standard strong concentrated packet. -/
def strong (packet : FinFourSourcePreservingForcedPairPacket frame) :
    FinFourSingletonStageStrongConcentratedPacket reward
      frame.pureSingletonProfile frame.singleton frame.stage
        source.minimumSingletonClockResolution where
  singletonOwner := packet.singletonOwner
  sourceTerminal_eq := packet.singleton_eq
  packetOwner := packet.forcedOwner
  packetOwner_ne_singletonOwner := packet.forcedOwner_ne_singletonOwner
  adapter := packet.forcedAdapter

/-- The forced target is literally the pure displayed pair over the frame. -/
theorem pairProfile_eq_purePair
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    packet.forcedAdapter.targetProfile =
      quittingLiteralPureRootProfile reward frame.targetProfile frame.stage
        (quittingCoalitionAction
          packet.forcedAdapter.routedTerminal.val) := by
  rw [QuittingStageAtomConcentratedPacketAdapter.targetProfile_eq_literalOneDateProfile]
  exact quittingLiteralPureRootProfile_update_eq_routed reward
    frame.targetProfile frame.stage frame.singleton.val packet.forcedOwner
      packet.forcedAdapter.action packet.forcedAdapter.routedTerminal.val rfl

/-- The forced pair retains the complete live mass reaching the frame. -/
theorem forcedPair_stageMass_eq_liveMass
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    quittingStageCoalitionMass reward packet.forcedAdapter.targetProfile
        frame.stage packet.forcedAdapter.routedTerminal =
      quittingLiveMass reward frame.targetProfile frame.stage := by
  rw [packet.pairProfile_eq_purePair,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_literalPureRootProfile_eq,
    quittingProfileLiveRoot_literalPureRootProfile_self,
    quittingRootCoalitionMass_pureCoalitionAction_eq_one, mul_one]

/-- The forced pair retains the canonical source resolution. -/
theorem resolution_le_forcedPairStageMass
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    source.minimumSingletonClockResolution ≤
      quittingStageCoalitionMass reward packet.forcedAdapter.targetProfile
        frame.stage packet.forcedAdapter.routedTerminal := by
  rw [packet.forcedPair_stageMass_eq_liveMass]
  exact frame.resolution_le_stageMass.trans
    (quittingStageCoalitionMass_le_liveMass reward frame.targetProfile
      frame.stage frame.singleton)

/-- The forced owner has zero marked defect at the displayed pair. -/
theorem forcedOwnerDefect_eq_zero
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    quittingRootCoordinateNashDefect reward
        packet.payerAdapter.sourceTail.1 packet.payerAdapter.sourceRoot
        packet.forcedOwner = 0 :=
  packet.toSingletonFrameForcedPairPacket.forcedOwnerDefect_eq_zero

/-- The table-selected forced owner's actual source-to-pair gain. -/
def forcedOwnerGain
    (packet : FinFourSourcePreservingForcedPairPacket frame) : ℝ :=
  packet.forcedAdapter.sourceToTargetGain

/-- The full terminal gap lower-bounds the forced owner's marked defect. -/
theorem terminalGap_le_forcedOwnerDefect
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    source.residual.witness.terminalGap ≤
      quittingRootCoordinateNashDefect reward
        packet.forcedAdapter.sourceTail.1 packet.forcedAdapter.sourceRoot
          packet.forcedOwner := by
  have hsourceRoot : packet.forcedAdapter.sourceRoot =
      quittingPureSetRoot ({packet.singletonOwner} : Finset (Fin 4)) := by
    funext who
    simp only [QuittingStageAtomConcentratedPacketAdapter.sourceRoot,
      FinFourSourcePreservingSingletonFrame.pureSingletonProfile,
      FinFourSingletonFrame.pureSingletonProfile,
      FinFourSourcePreservingSingletonFrame.toSingletonFrame,
      quittingProfileLiveRoot_literalPureRootProfile_self,
      packet.singleton_eq]
    simp [quittingPureSetRoot, quittingSetAction, quittingCoalitionAction]
  have herase : (({packet.singletonOwner} : Finset (Fin 4)).erase
      packet.forcedOwner).Nonempty := by
    simp [packet.forcedOwner_ne_singletonOwner]
  have hcontinue : quittingRootContinuePayoff reward
        packet.forcedAdapter.sourceTail.1 packet.forcedAdapter.sourceRoot
        packet.forcedOwner =
      quittingSetReward reward {packet.singletonOwner} packet.forcedOwner := by
    rw [hsourceRoot,
      quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
        packet.forcedAdapter.sourceTail.1 {packet.singletonOwner}
          packet.forcedOwner herase]
    simp [packet.forcedOwner_ne_singletonOwner]
  have hquit : quittingRootQuitPayoff reward
        packet.forcedAdapter.sourceTail.1 packet.forcedAdapter.sourceRoot
        packet.forcedOwner =
      quittingSetReward reward
        {packet.singletonOwner, packet.forcedOwner} packet.forcedOwner := by
    rw [hsourceRoot, quittingRootQuitPayoff_pureSetRoot_eq_insert]
    simp [Finset.pair_comm]
  have hfalse :
      (packet.forcedAdapter.sourceRoot packet.forcedOwner false).toReal = 1 := by
    rw [hsourceRoot]
    simp [quittingPureSetRoot, quittingSetAction,
      packet.forcedOwner_ne_singletonOwner]
  have htrue :
      (packet.forcedAdapter.sourceRoot packet.forcedOwner true).toReal = 0 := by
    rw [hsourceRoot]
    simp [quittingPureSetRoot, quittingSetAction,
      packet.forcedOwner_ne_singletonOwner]
  have hgapDifference : source.residual.witness.terminalGap ≤
      quittingRootEndpointDifference reward packet.forcedAdapter.sourceTail.1
        packet.forcedAdapter.sourceRoot packet.forcedOwner := by
    simp only [quittingRootEndpointDifference, hcontinue, hquit]
    linarith [packet.terminalGap_join]
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart,
    hfalse, htrue, one_mul, zero_mul, add_zero,
    max_eq_left (source.residual.witness.terminalGap_pos.le.trans
      hgapDifference)]
  exact hgapDifference

/-- The forced owner's actual gain has the resolution-times-gap floor. -/
theorem resolution_mul_terminalGap_le_forcedOwnerGain
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    source.minimumSingletonClockResolution *
        source.residual.witness.terminalGap ≤ packet.forcedOwnerGain := by
  exact packet.forcedAdapter.sourceToTargetGain_lowerBound
    source.minimumSingletonClockResolution
      source.residual.witness.terminalGap
      (frame.resolution_le_pureSingletonStageMass.trans
        (quittingStageCoalitionMass_le_liveMass reward
          frame.pureSingletonProfile frame.stage frame.singleton))
      source.residual.witness.terminalGap_pos.le
      packet.terminalGap_le_forcedOwnerDefect

/-- The selected payer's actual best-endpoint gain. -/
def payerGain (packet : FinFourSourcePreservingForcedPairPacket frame) : ℝ :=
  packet.toSingletonFrameForcedPairPacket.payerGain

/-- Exact live-mass-times-defect identity for the paid endpoint. -/
theorem payerGain_eq_liveMass_mul_defect
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    packet.payerGain =
      quittingLiveMass reward packet.forcedAdapter.targetProfile frame.stage *
        quittingRootCoordinateNashDefect reward
          packet.payerAdapter.sourceTail.1 packet.payerAdapter.sourceRoot
            packet.payer :=
  packet.payerAdapter.sourceToTargetGain_eq_liveMass_mul_defect

/-- The payer gain has the exact canonical `lambda * D_* / 3` floor. -/
theorem payerGain_floor
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    source.minimumSingletonClockResolution *
          quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      packet.payerGain :=
  packet.toSingletonFrameForcedPairPacket.payerGain_floor

/-- The selected payer's actual gain is strictly positive. -/
theorem payerGain_pos
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    0 < packet.payerGain :=
  packet.toSingletonFrameForcedPairPacket.payerGain_pos

/-- Canonical `mu^2 * D_* / 24` form of the payer-gain floor. -/
theorem canonical_payerGain_floor
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    source.point.2 (some source.atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 24 ≤
      packet.payerGain := by
  calc
    source.point.2 (some source.atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 24 =
        source.minimumSingletonClockResolution *
          quittingTerminalSemanticDebtSum source.point.1 / 3 := by
      simp only [FinFourMinimumAtomProducer.minimumSingletonClockResolution]
      ring
    _ ≤ packet.payerGain := packet.payerGain_floor

/-- The payer's unrestricted debt falls by exactly its actual gain. -/
theorem payerTargetDebt_eq_sourceDebt_sub_gain
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          packet.payerAdapter.targetProfile) packet.payer =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            packet.forcedAdapter.targetProfile) packet.payer -
        packet.payerGain :=
  packet.toSingletonFrameForcedPairPacket.payerTargetDebt_eq_sourceDebt_sub_gain

/-- The payer target is a pure routed coalition over the original frame. -/
theorem payerTargetProfile_eq_pureRouted
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    packet.payerAdapter.targetProfile =
      quittingLiteralPureRootProfile reward frame.targetProfile frame.stage
        (quittingCoalitionAction packet.payerAdapter.routedTerminal.val) := by
  calc
    packet.payerAdapter.targetProfile =
        quittingLiteralOneDateProfile reward
          packet.forcedAdapter.targetProfile packet.payer frame.stage
            packet.payerAdapter.action := rfl
    _ = quittingLiteralOneDateProfile reward
          (quittingLiteralPureRootProfile reward frame.targetProfile frame.stage
            (quittingCoalitionAction
              packet.forcedAdapter.routedTerminal.val))
          packet.payer frame.stage packet.payerAdapter.action := by
        exact congrArg (fun profile ↦ quittingLiteralOneDateProfile reward
          profile packet.payer frame.stage packet.payerAdapter.action)
            packet.pairProfile_eq_purePair
    _ = quittingLiteralPureRootProfile reward frame.targetProfile frame.stage
          (quittingCoalitionAction packet.payerAdapter.routedTerminal.val) := by
        simpa only [quittingLiteralOneDateProfile] using
          quittingLiteralPureRootProfile_update_eq_routed reward
            frame.targetProfile frame.stage
              packet.forcedAdapter.routedTerminal.val packet.payer
              packet.payerAdapter.action
              packet.payerAdapter.routedTerminal.val rfl

/-- The paid endpoint routes the marked mass without loss. -/
theorem payerRoutedStageMass_eq_forcedPairStageMass
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    quittingStageCoalitionMass reward packet.payerAdapter.targetProfile
        frame.stage packet.payerAdapter.routedTerminal =
      quittingStageCoalitionMass reward packet.forcedAdapter.targetProfile
        frame.stage packet.forcedAdapter.routedTerminal := by
  calc
    quittingStageCoalitionMass reward packet.payerAdapter.targetProfile
          frame.stage packet.payerAdapter.routedTerminal =
        quittingLiveMass reward frame.targetProfile frame.stage := by
      rw [packet.payerTargetProfile_eq_pureRouted,
        quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
        quittingLiveMass_literalPureRootProfile_eq,
        quittingProfileLiveRoot_literalPureRootProfile_self,
        quittingRootCoalitionMass_pureCoalitionAction_eq_one, mul_one]
    _ = quittingStageCoalitionMass reward packet.forcedAdapter.targetProfile
          frame.stage packet.forcedAdapter.routedTerminal :=
      packet.forcedPair_stageMass_eq_liveMass.symm

/-- The forced pair changes no behavior away from the marked date. -/
theorem forcedPairProfile_eq_of_time_ne
    (packet : FinFourSourcePreservingForcedPairPacket frame)
    (player : Fin 4) (time : ℕ)
    (history : (quittingGame reward).Hist time)
    (htime : time ≠ frame.stage) :
    packet.forcedAdapter.targetProfile player time history =
      frame.targetProfile player time history :=
  congrFun
    (packet.toSingletonFrameForcedPairPacket.forcedPairProfile_at_of_ne
      time htime player) history

/-- The paid target changes no behavior away from the marked date. -/
theorem payerTargetProfile_eq_of_time_ne
    (packet : FinFourSourcePreservingForcedPairPacket frame)
    (player : Fin 4) (time : ℕ)
    (history : (quittingGame reward).Hist time)
    (htime : time ≠ frame.stage) :
    packet.payerAdapter.targetProfile player time history =
      frame.targetProfile player time history :=
  congrFun
    (packet.toSingletonFrameForcedPairPacket.payerTargetProfile_at_of_ne
      time htime player) history

/-- The forced pair retains the exact complete post-date reference spine. -/
theorem forcedPair_postDateSpine_eq_reference
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    quittingAllContinueProfileSpine reward
        packet.forcedAdapter.targetProfile (frame.stage + 1) =
      quittingAllContinueProfileSpine reward frame.referenceProfile
        (frame.stage + 1) :=
  packet.toSingletonFrameForcedPairPacket.forcedPair_postDateSpine_eq_reference

/-- The paid target retains the exact complete post-date reference spine. -/
theorem payerTarget_postDateSpine_eq_reference
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    quittingAllContinueProfileSpine reward packet.payerAdapter.targetProfile
        (frame.stage + 1) =
      quittingAllContinueProfileSpine reward frame.referenceProfile
        (frame.stage + 1) :=
  packet.toSingletonFrameForcedPairPacket.payerTarget_postDateSpine_eq_reference

/-- Exact semantic-pair provenance of the forced target tail. -/
theorem forcedPair_postDateTail_eq_reference
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          packet.forcedAdapter.targetProfile (frame.stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward frame.referenceProfile
          (frame.stage + 1)) := by
  rw [packet.forcedPair_postDateSpine_eq_reference]

/-- Exact semantic-pair provenance of the paid target tail. -/
theorem payerTarget_postDateTail_eq_reference
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          packet.payerAdapter.targetProfile (frame.stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward frame.referenceProfile
          (frame.stage + 1)) := by
  rw [packet.payerTarget_postDateSpine_eq_reference]

/-- Exact complete terminal-outcome-law provenance of the forced target tail. -/
theorem forcedPair_postDateLaw_eq_reference
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    quittingTerminalOutcomeMass reward
        (quittingAllContinueProfileSpine reward
          packet.forcedAdapter.targetProfile (frame.stage + 1)) =
      quittingTerminalOutcomeMass reward
        (quittingAllContinueProfileSpine reward frame.referenceProfile
          (frame.stage + 1)) := by
  rw [packet.forcedPair_postDateSpine_eq_reference]

/-- Exact complete terminal-outcome-law provenance of the paid target tail. -/
theorem payerTarget_postDateLaw_eq_reference
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
    quittingTerminalOutcomeMass reward
        (quittingAllContinueProfileSpine reward
          packet.payerAdapter.targetProfile (frame.stage + 1)) =
      quittingTerminalOutcomeMass reward
        (quittingAllContinueProfileSpine reward frame.referenceProfile
          (frame.stage + 1)) := by
  rw [packet.payerTarget_postDateSpine_eq_reference]

/-- The forced pair produces the standard source-attached collision residual. -/
theorem nonempty_collisionMinimumResidual
    (packet : FinFourSourcePreservingForcedPairPacket frame) :
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

/-- Every constant-packet residual cluster is the frame's actual post-date
semantic tail. -/
theorem collisionCluster_eq_framePostDateTail
    (packet : FinFourSourcePreservingForcedPairPacket frame)
    (collision : QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 packet.forcedOwner packet.forcedAdapter.routedTerminal
        packet.forcedAdapter.packet) :
    collision.cluster =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward frame.targetProfile
          (frame.stage + 1)) := by
  have htail := collision.tail_tendsto
  have heq : (fun rank ↦
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (packet.forcedAdapter.profiles
            (packet.forcedAdapter.packet.subseq (collision.subseq rank)))
          (packet.forcedAdapter.packet.mark (collision.subseq rank) + 1))) =
      fun _rank ↦ quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward frame.targetProfile
          (frame.stage + 1)) := by
    funext rank
    have hforced := congrArg (quittingTerminalSemanticPair reward)
      packet.forcedPair_postDateSpine_eq_reference
    have hframe := congrArg (quittingTerminalSemanticPair reward)
      frame.postDateSpine_eq_reference
    simpa only [QuittingStageAtomConcentratedPacketAdapter.profiles,
      QuittingStageAtomConcentratedPacketAdapter.packet,
      QuittingStageAtomConcentratedPacketAdapter.packetWithScale,
      QuittingStageAtomConcentratedPacketAdapter.subseq,
      QuittingStageAtomConcentratedPacketAdapter.mark, id_eq] using
      hforced.trans hframe.symm
  rw [heq] at htail
  exact tendsto_nhds_unique htail tendsto_const_nhds

/-- One frame-level capstone retaining the paid packet, collision residual,
and exact source-tail cluster provenance. -/
structure ResidualCapstone
    (frame : FinFourSourcePreservingSingletonFrame entrance) where
  packet : FinFourSourcePreservingForcedPairPacket frame
  collision : QuittingConcentratedCollisionMinimumResidual reward
    source.point.1 packet.forcedOwner packet.forcedAdapter.routedTerminal
      packet.forcedAdapter.packet
  cluster_eq_framePostDateTail : collision.cluster =
    quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward frame.targetProfile
        (frame.stage + 1))

end FinFourSourcePreservingForcedPairPacket

namespace FinFourSourcePreservingSingletonFrame

/-- Every source-preserving singleton frame produces the full-gap pair and
positive-defect paid endpoint without inspecting its route-specific origin. -/
theorem nonempty_forcedPairPacket
    (frame : FinFourSourcePreservingSingletonFrame entrance) :
    Nonempty (FinFourSourcePreservingForcedPairPacket frame) := by
  obtain ⟨packet⟩ := frame.toSingletonFrame.nonempty_forcedPairPacket
  exact ⟨FinFourSourcePreservingForcedPairPacket.ofSingletonFrameForcedPairPacket
    packet⟩

/-- Construct the paid pair and its collision residual in one call. -/
theorem nonempty_forcedPairResidualCapstone
    (frame : FinFourSourcePreservingSingletonFrame entrance) :
    Nonempty (FinFourSourcePreservingForcedPairPacket.ResidualCapstone frame) := by
  obtain ⟨packet⟩ := frame.nonempty_forcedPairPacket
  obtain ⟨collision⟩ := packet.nonempty_collisionMinimumResidual
  exact ⟨{
    packet := packet
    collision := collision
    cluster_eq_framePostDateTail :=
      packet.collisionCluster_eq_framePostDateTail collision
  }⟩

end FinFourSourcePreservingSingletonFrame

end GameTheory
