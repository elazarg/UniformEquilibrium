/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.SingletonFrameForcedPair
import Research.Quitting.FinFourProducerAtlas.SourceFaithfulRenewedSingleton

/-!
# Forced pairs from an explicit-resolution singleton frame

The existing weak-core forced-pair theorem is tied definitionally to the
canonical minimum-law scale `mu^2 / 8`.  Source-faithful regeneration instead
produces singleton endpoints at a supplied renewable scale.  This module
factors the same local construction through a neutral frame carrying that
scale explicitly.

The table-selected outsider is forced to Quit from the pure singleton, giving
a literal pair.  Its marked defect is zero.  Among the other three players,
one payer has defect at least one third of the positive global minimum debt.
Its one-date best endpoint therefore has actual gain at least
`resolution * D_* / 3` and subtracts that gain exactly from its own
unrestricted terminal debt.  All profiles remain literal one-date siblings
of the frame and retain its complete post-date reference spine.

No near-return, recursive transition, or uniform-equilibrium conclusion is
asserted here.
-/

noncomputable section

namespace GameTheory

open QuittingNonsingletonMinimumLawTransfer
open QuittingSureSetOwnerRepair

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}

/-- The exact local data needed by the forced-pair construction, with the
resolution exposed rather than recovered from the minimum-law atom. -/
structure FinFourExplicitResolutionSingletonFrame
    (source : FinFourMinimumAtomProducer reward bound) where
  referenceProfile : (quittingGame reward).BehaviorProfile
  targetProfile : (quittingGame reward).BehaviorProfile
  stage : ℕ
  singleton : {S : Finset (Fin 4) // S.Nonempty}
  resolution : ℝ
  resolution_pos : 0 < resolution
  singleton_card : singleton.val.card = 1
  resolution_le_stageMass : resolution ≤
    quittingStageCoalitionMass reward targetProfile stage singleton
  postDateSpine_eq_reference :
    quittingAllContinueProfileSpine reward targetProfile (stage + 1) =
      quittingAllContinueProfileSpine reward referenceProfile (stage + 1)

namespace FinFourExplicitResolutionSingletonFrame

/-- Forget the source-faithful wrapper while retaining its exact local
singleton frame and supplied resolution. -/
def toSingletonFrame
    (frame : FinFourExplicitResolutionSingletonFrame source) :
    FinFourSingletonFrame source where
  referenceProfile := frame.referenceProfile
  targetProfile := frame.targetProfile
  stage := frame.stage
  singleton := frame.singleton
  resolution := frame.resolution
  resolution_pos := frame.resolution_pos
  singleton_card := frame.singleton_card
  resolution_le_stageMass := frame.resolution_le_stageMass
  postDateSpine_eq_reference := frame.postDateSpine_eq_reference

/-- Restore the explicit-resolution wrapper around a common singleton frame. -/
def ofSingletonFrame
    (frame : FinFourSingletonFrame source) :
    FinFourExplicitResolutionSingletonFrame source where
  referenceProfile := frame.referenceProfile
  targetProfile := frame.targetProfile
  stage := frame.stage
  singleton := frame.singleton
  resolution := frame.resolution
  resolution_pos := frame.resolution_pos
  singleton_card := frame.singleton_card
  resolution_le_stageMass := frame.resolution_le_stageMass
  postDateSpine_eq_reference := frame.postDateSpine_eq_reference

/-- The literal pure-singleton sibling at the same date. -/
def pureSingletonProfile
    (frame : FinFourExplicitResolutionSingletonFrame source) :
    (quittingGame reward).BehaviorProfile :=
  frame.toSingletonFrame.pureSingletonProfile

/-- Pureification assigns the full reached live mass to the singleton. -/
theorem pureSingleton_stageMass_eq_liveMass
    (frame : FinFourExplicitResolutionSingletonFrame source) :
    quittingStageCoalitionMass reward frame.pureSingletonProfile frame.stage
        frame.singleton =
      quittingLiveMass reward frame.targetProfile frame.stage :=
  frame.toSingletonFrame.pureSingleton_stageMass_eq_liveMass

/-- The explicit resolution survives pureification. -/
theorem resolution_le_pureSingletonStageMass
    (frame : FinFourExplicitResolutionSingletonFrame source) :
    frame.resolution ≤ quittingStageCoalitionMass reward
      frame.pureSingletonProfile frame.stage frame.singleton :=
  frame.toSingletonFrame.resolution_le_pureSingletonStageMass

/-- Pureification changes no behavior away from the marked date. -/
theorem pureSingletonProfile_at_of_ne
    (frame : FinFourExplicitResolutionSingletonFrame source)
    (time : ℕ) (htime : time ≠ frame.stage) (player : Fin 4) :
    frame.pureSingletonProfile player time = frame.targetProfile player time :=
  frame.toSingletonFrame.pureSingletonProfile_at_of_ne time htime player

/-- The pure singleton retains the frame's complete post-date reference
spine. -/
theorem pureSingleton_postDateSpine_eq_reference
    (frame : FinFourExplicitResolutionSingletonFrame source) :
    quittingAllContinueProfileSpine reward frame.pureSingletonProfile
        (frame.stage + 1) =
      quittingAllContinueProfileSpine reward frame.referenceProfile
        (frame.stage + 1) :=
  frame.toSingletonFrame.pureSingleton_postDateSpine_eq_reference

end FinFourExplicitResolutionSingletonFrame

/-- A full-gap forced pair and one exact paid endpoint at the frame's explicit
resolution. -/
structure FinFourExplicitResolutionForcedPairPacket
    (frame : FinFourExplicitResolutionSingletonFrame source) where
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
      frame.resolution
  forcedAction_eq_true : forcedAdapter.action = true
  payer : Fin 4
  payer_ne_forcedOwner : payer ≠ forcedOwner
  payerAdapter : QuittingStageAtomConcentratedPacketAdapter reward
    forcedAdapter.targetProfile forcedAdapter.routedTerminal payer frame.stage
      frame.resolution
  payerDefect_floor :
    quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      quittingRootCoordinateNashDefect reward payerAdapter.sourceTail.1
        payerAdapter.sourceRoot payer

namespace FinFourExplicitResolutionForcedPairPacket

variable {frame : FinFourExplicitResolutionSingletonFrame source}

/-- Forget the source-faithful wrapper while retaining the complete common
forced-pair packet. -/
def toSingletonFrameForcedPairPacket
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
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

/-- Restore the source-faithful wrapper around one common packet. -/
def ofSingletonFrameForcedPairPacket
    (packet : FinFourSingletonFrameForcedPairPacket frame.toSingletonFrame) :
    FinFourExplicitResolutionForcedPairPacket frame where
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

/-- The forced terminal is the displayed pair. -/
theorem forcedTerminal_val
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    packet.forcedAdapter.routedTerminal.val =
      {packet.singletonOwner, packet.forcedOwner} :=
  packet.toSingletonFrameForcedPairPacket.forcedTerminal_val

/-- The forced terminal is genuinely a pair. -/
theorem forcedTerminal_card
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    packet.forcedAdapter.routedTerminal.val.card = 2 :=
  packet.toSingletonFrameForcedPairPacket.forcedTerminal_card

/-- The forced owner has zero marked defect at the pair. -/
theorem forcedOwnerDefect_eq_zero
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    quittingRootCoordinateNashDefect reward
        packet.payerAdapter.sourceTail.1 packet.payerAdapter.sourceRoot
        packet.forcedOwner = 0 :=
  packet.toSingletonFrameForcedPairPacket.forcedOwnerDefect_eq_zero

/-- The payer's actual one-date best-endpoint gain. -/
def payerGain
    (packet : FinFourExplicitResolutionForcedPairPacket frame) : ℝ :=
  packet.toSingletonFrameForcedPairPacket.payerGain

/-- The payer gain has the exact explicit-resolution floor. -/
theorem payerGain_floor
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    frame.resolution * quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      packet.payerGain :=
  packet.toSingletonFrameForcedPairPacket.payerGain_floor

/-- The payer gain is strictly positive. -/
theorem payerGain_pos
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    0 < packet.payerGain :=
  packet.toSingletonFrameForcedPairPacket.payerGain_pos

/-- The payer's unrestricted debt decreases by exactly its actual payoff
gain. -/
theorem payerTargetDebt_eq_sourceDebt_sub_gain
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          packet.payerAdapter.targetProfile) packet.payer =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            packet.forcedAdapter.targetProfile) packet.payer -
        packet.payerGain :=
  packet.toSingletonFrameForcedPairPacket.payerTargetDebt_eq_sourceDebt_sub_gain

/-- The forced pair changes no behavior away from the marked date. -/
theorem forcedPairProfile_at_of_ne
    (packet : FinFourExplicitResolutionForcedPairPacket frame)
    (time : ℕ) (htime : time ≠ frame.stage) (player : Fin 4) :
    packet.forcedAdapter.targetProfile player time =
      frame.targetProfile player time :=
  packet.toSingletonFrameForcedPairPacket.forcedPairProfile_at_of_ne
    time htime player

/-- The paid target changes no behavior away from the marked date. -/
theorem payerTargetProfile_at_of_ne
    (packet : FinFourExplicitResolutionForcedPairPacket frame)
    (time : ℕ) (htime : time ≠ frame.stage) (player : Fin 4) :
    packet.payerAdapter.targetProfile player time =
      frame.targetProfile player time :=
  packet.toSingletonFrameForcedPairPacket.payerTargetProfile_at_of_ne
    time htime player

/-- The forced pair retains the complete post-date reference spine. -/
theorem forcedPair_postDateSpine_eq_reference
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    quittingAllContinueProfileSpine reward packet.forcedAdapter.targetProfile
        (frame.stage + 1) =
      quittingAllContinueProfileSpine reward frame.referenceProfile
        (frame.stage + 1) :=
  packet.toSingletonFrameForcedPairPacket.forcedPair_postDateSpine_eq_reference

/-- The paid target retains the same complete post-date reference spine. -/
theorem payerTarget_postDateSpine_eq_reference
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    quittingAllContinueProfileSpine reward packet.payerAdapter.targetProfile
        (frame.stage + 1) =
      quittingAllContinueProfileSpine reward frame.referenceProfile
        (frame.stage + 1) :=
  packet.toSingletonFrameForcedPairPacket.payerTarget_postDateSpine_eq_reference

end FinFourExplicitResolutionForcedPairPacket

namespace FinFourExplicitResolutionSingletonFrame
/-- Every explicit-resolution singleton frame produces the full-gap pair and
paid endpoint at that same resolution. -/
theorem nonempty_forcedPairPacket
    (frame : FinFourExplicitResolutionSingletonFrame source) :
    Nonempty (FinFourExplicitResolutionForcedPairPacket frame) := by
  obtain ⟨packet⟩ := frame.toSingletonFrame.nonempty_forcedPairPacket
  exact ⟨FinFourExplicitResolutionForcedPairPacket.ofSingletonFrameForcedPairPacket
    packet⟩
end FinFourExplicitResolutionSingletonFrame

namespace FinFourSourceFaithfulRenewedSingletonPacket

variable {point : QuittingTerminalSemanticLawPoint (Fin 4)}
variable {terminal : {S : Finset (Fin 4) // S.Nonempty}}
variable {profiles : ℕ → (quittingGame reward).BehaviorProfile}
variable {mark : ℕ → ℕ} {lambda resolution : ℝ}
variable {causal : QuittingSourceFaithfulMinimumCausalization
  point terminal profiles mark lambda}
variable {terminalNonsingleton : 1 < terminal.val.card}

/-- The renewed endpoint as a neutral singleton frame, retaining the literal
source-faithful causal profile as its reference. -/
def toSingletonFrame
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) (rank : ℕ) :
    FinFourSingletonFrame source where
  referenceProfile := sourceProfile causal packet.cutoff rank
  targetProfile := (packet.endpoint rank).targetProfile
  stage := sourceMark causal packet.cutoff rank
  singleton := (packet.endpoint rank).singleton
  resolution := resolution
  resolution_pos := packet.resolution_pos
  singleton_card := packet.singleton_card rank
  resolution_le_stageMass := packet.resolution_le_singletonStageMass rank
  postDateSpine_eq_reference := packet.endpoint_postDateSpine_eq_source rank

/-- One renewed singleton endpoint as an explicit-resolution forced-pair
frame, retaining the source-faithful causal profile as its reference. -/
def toExplicitResolutionFrame
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) (rank : ℕ) :
    FinFourExplicitResolutionSingletonFrame source :=
  FinFourExplicitResolutionSingletonFrame.ofSingletonFrame
    (packet.toSingletonFrame (source := source) rank)

/-- Every renewed singleton endpoint reconstructs the common forced-pair paid
packet at the same absolute resolution. -/
theorem nonempty_commonForcedPairPacket
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) (rank : ℕ) :
    Nonempty (FinFourSingletonFrameForcedPairPacket
      (packet.toSingletonFrame (source := source) rank)) :=
  (packet.toSingletonFrame (source := source) rank).nonempty_forcedPairPacket

/-- Every renewed singleton endpoint reconstructs the full forced-pair paid
packet at the same absolute resolution. -/
theorem nonempty_forcedPairPacket
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) (rank : ℕ) :
    Nonempty (FinFourExplicitResolutionForcedPairPacket
      (packet.toExplicitResolutionFrame (source := source) rank)) :=
  (packet.toExplicitResolutionFrame (source := source) rank).nonempty_forcedPairPacket

end FinFourSourceFaithfulRenewedSingletonPacket

end GameTheory
