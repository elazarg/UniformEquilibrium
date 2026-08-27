/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.StrongConcentratedPacket
import Research.Quitting.PureNonsingletonCollisionScreening
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PunishmentNormalAtomicCollisionHandoff
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.StaticCycleChronologyBarrier

/-!
# Paid forced pairs from weak Fin4 singleton cores

A source-attached weak concentrated singleton is first overwritten by the
literal pure singleton at its marked date.  The hard residual then selects a
table-level full-gap outsider.  Using that outsider as the prescribed packet
owner forces the exact best endpoint to be Quit, so the routed terminal is the
literal pair.

At the pure pair, the forced owner's coordinate defect is zero.  The pure
nonsingleton debt identity therefore places the positive minimum debt on the
other three Fin4 coordinates.  One fixed payer among them has defect at least
`D_* / 3`; its actual best-endpoint update gains at least
`lambda * D_* / 3`, routes the complete marked mass exactly, and subtracts
that gain exactly from its own unrestricted terminal debt.

The wrapper remains indexed by the original weak core, hence retains its
source and origin.  No near-minimality, cap--Nash preservation, collision
absence, total-debt descent, or downstream completion is asserted.
-/

noncomputable section

namespace GameTheory

open QuittingNonsingletonMinimumLawTransfer
open QuittingSureSetOwnerRepair

namespace FinFourAtlasWeakConcentratedSingletonCore

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The literal pure singleton sibling of the weak core at the same actual
date and over the same complete off-date behavior profile. -/
def pureSingletonProfile
    (core : FinFourAtlasWeakConcentratedSingletonCore source) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralPureRootProfile reward core.targetProfile core.stage
    (quittingCoalitionAction core.singleton.val)

/-- Pureification does not change the probability of reaching the marked
date and assigns all of that live mass to the displayed singleton. -/
theorem pureSingleton_stageMass_eq_liveMass
    (core : FinFourAtlasWeakConcentratedSingletonCore source) :
    quittingStageCoalitionMass reward core.pureSingletonProfile core.stage
        core.singleton =
      quittingLiveMass reward core.targetProfile core.stage := by
  unfold pureSingletonProfile
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_literalPureRootProfile_eq,
    quittingProfileLiveRoot_literalPureRootProfile_self,
    quittingRootCoalitionMass_pureCoalitionAction_eq_one, mul_one]

/-- The weak core's resolution survives the simultaneous pure overwrite. -/
theorem resolution_le_pureSingletonStageMass
    (core : FinFourAtlasWeakConcentratedSingletonCore source) :
    core.resolution ≤ quittingStageCoalitionMass reward
      core.pureSingletonProfile core.stage core.singleton := by
  rw [core.pureSingleton_stageMass_eq_liveMass]
  exact core.resolution_le_stageMass.trans
    (quittingStageCoalitionMass_le_liveMass reward core.targetProfile
      core.stage core.singleton)

/-- The pure singleton sibling keeps the core's complete post-date live-root
tail and hence its source origin. -/
theorem pureSingleton_postDate_liveRoot_eq_reference
    (core : FinFourAtlasWeakConcentratedSingletonCore source) (offset : ℕ) :
    quittingProfileLiveRoot reward core.pureSingletonProfile
        (core.stage + 1 + offset) =
      quittingProfileLiveRoot reward core.referenceProfile
        (core.stage + 1 + offset) := by
  rw [show quittingProfileLiveRoot reward core.pureSingletonProfile
        (core.stage + 1 + offset) =
      quittingProfileLiveRoot reward core.targetProfile
        (core.stage + 1 + offset) by
    exact quittingLiteralPureRootProfile_tail_eq reward core.targetProfile
      core.stage _ offset]
  exact core.postDate_liveRoot_eq offset

/-- Away from the marked date, the pure singleton sibling is literally the
weak core's profile on every player and every history. -/
theorem pureSingletonProfile_at_of_ne
    (core : FinFourAtlasWeakConcentratedSingletonCore source)
    (time : ℕ) (htime : time ≠ core.stage) (player : Fin 4) :
    core.pureSingletonProfile player time = core.targetProfile player time := by
  unfold pureSingletonProfile quittingLiteralPureRootProfile
    quittingLiteralOneDateOverride
  simp [htime]

end FinFourAtlasWeakConcentratedSingletonCore

/-- A direct paid endpoint attached to one weak singleton core.
The first adapter uses the table-selected outsider as its prescribed owner;
the second adapter is the directly selected positive-defect payer. -/
structure FinFourWeakCoreForcedPairPacket
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (core : FinFourAtlasWeakConcentratedSingletonCore source) where
  singletonOwner : Fin 4
  singleton_eq : core.singleton.val = {singletonOwner}
  forcedOwner : Fin 4
  forcedOwner_ne_singletonOwner : forcedOwner ≠ singletonOwner
  terminalGap_join :
    quittingSetReward reward {singletonOwner} forcedOwner +
          source.residual.witness.terminalGap ≤
      quittingSetReward reward {singletonOwner, forcedOwner} forcedOwner
  forcedAdapter : QuittingStageAtomConcentratedPacketAdapter reward
    core.pureSingletonProfile core.singleton forcedOwner core.stage
      core.resolution
  forcedAction_eq_true : forcedAdapter.action = true
  payer : Fin 4
  payer_ne_forcedOwner : payer ≠ forcedOwner
  payerAdapter : QuittingStageAtomConcentratedPacketAdapter reward
    forcedAdapter.targetProfile forcedAdapter.routedTerminal payer core.stage
      core.resolution
  payerDefect_floor :
    quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      quittingRootCoordinateNashDefect reward payerAdapter.sourceTail.1
        payerAdapter.sourceRoot payer

namespace FinFourWeakCoreForcedPairPacket

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {core : FinFourAtlasWeakConcentratedSingletonCore source}

/-- The source singleton and prescribed forced owner form the literal pair. -/
theorem forcedTerminal_val
    (packet : FinFourWeakCoreForcedPairPacket core) :
    packet.forcedAdapter.routedTerminal.val =
      {packet.singletonOwner, packet.forcedOwner} := by
  rw [QuittingStageAtomConcentratedPacketAdapter.routedTerminal_val]
  simp only [QuittingStageAtomConcentratedPacketAdapter.routedCoalition,
    packet.forcedAction_eq_true,
    quittingPureEndpointRoutedCoalition_true, packet.singleton_eq]
  exact Finset.pair_comm _ _

/-- The forced terminal is genuinely a pair. -/
theorem forcedTerminal_card
    (packet : FinFourWeakCoreForcedPairPacket core) :
    packet.forcedAdapter.routedTerminal.val.card = 2 := by
  rw [packet.forcedTerminal_val]
  have hnot : packet.singletonOwner ∉ ({packet.forcedOwner} : Finset (Fin 4)) := by
    simpa using packet.forcedOwner_ne_singletonOwner.symm
  rw [Finset.card_insert_of_notMem hnot]
  simp

/-- The first adapter is the existing strong singleton-stage payload with the
table-selected outsider retained as its prescribed packet owner. -/
def strong (packet : FinFourWeakCoreForcedPairPacket core) :
    FinFourSingletonStageStrongConcentratedPacket reward
      core.pureSingletonProfile core.singleton core.stage core.resolution where
  singletonOwner := packet.singletonOwner
  sourceTerminal_eq := packet.singleton_eq
  packetOwner := packet.forcedOwner
  packetOwner_ne_singletonOwner := packet.forcedOwner_ne_singletonOwner
  adapter := packet.forcedAdapter

/-- The forced adapter's target is literally the pure displayed pair over the
original core profile. -/
theorem pairProfile_eq_purePair
    (packet : FinFourWeakCoreForcedPairPacket core) :
    packet.forcedAdapter.targetProfile =
      quittingLiteralPureRootProfile reward core.targetProfile core.stage
        (quittingCoalitionAction
          packet.forcedAdapter.routedTerminal.val) := by
  rw [QuittingStageAtomConcentratedPacketAdapter.targetProfile_eq_literalOneDateProfile]
  exact quittingLiteralPureRootProfile_update_eq_routed reward
    core.targetProfile core.stage core.singleton.val packet.forcedOwner
      packet.forcedAdapter.action packet.forcedAdapter.routedTerminal.val rfl

/-- The literal forced pair retains exactly the full reached live mass. -/
theorem forcedPair_stageMass_eq_liveMass
    (packet : FinFourWeakCoreForcedPairPacket core) :
    quittingStageCoalitionMass reward packet.forcedAdapter.targetProfile
        core.stage packet.forcedAdapter.routedTerminal =
      quittingLiveMass reward core.targetProfile core.stage := by
  rw [packet.pairProfile_eq_purePair,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_literalPureRootProfile_eq,
    quittingProfileLiveRoot_literalPureRootProfile_self,
    quittingRootCoalitionMass_pureCoalitionAction_eq_one, mul_one]

/-- In particular, the forced pair retains the weak core's resolution. -/
theorem resolution_le_forcedPairStageMass
    (packet : FinFourWeakCoreForcedPairPacket core) :
    core.resolution ≤ quittingStageCoalitionMass reward
      packet.forcedAdapter.targetProfile core.stage
        packet.forcedAdapter.routedTerminal := by
  rw [packet.forcedPair_stageMass_eq_liveMass]
  exact core.resolution_le_stageMass.trans
    (quittingStageCoalitionMass_le_liveMass reward core.targetProfile
      core.stage core.singleton)

/-- The forced owner has exactly zero local defect at the displayed pair. -/
theorem forcedOwnerDefect_eq_zero
    (packet : FinFourWeakCoreForcedPairPacket core) :
    quittingRootCoordinateNashDefect reward
        packet.payerAdapter.sourceTail.1 packet.payerAdapter.sourceRoot
        packet.forcedOwner = 0 := by
  have htail : packet.payerAdapter.sourceTail =
      packet.forcedAdapter.targetTail := rfl
  have hroot : packet.payerAdapter.sourceRoot =
      quittingProfileLiveRoot reward packet.forcedAdapter.targetProfile
        core.stage := rfl
  rw [htail, hroot]
  exact packet.forcedAdapter.ownerMarkedDefect_eq_zero

/-- The actual gain made by the table-selected full-gap owner. -/
def forcedOwnerGain (packet : FinFourWeakCoreForcedPairPacket core) : ℝ :=
  packet.forcedAdapter.sourceToTargetGain

/-- Exact source-to-pair gain identity for the forced owner.  The live mass
need not equal the fixed resolution, and the table gap is only a lower bound
on the endpoint difference, so neither factor is replaced by a bound here. -/
theorem forcedOwnerGain_eq_liveMass_mul_defect
    (packet : FinFourWeakCoreForcedPairPacket core) :
    packet.forcedOwnerGain =
      quittingLiveMass reward core.pureSingletonProfile core.stage *
        quittingRootCoordinateNashDefect reward
          packet.forcedAdapter.sourceTail.1 packet.forcedAdapter.sourceRoot
            packet.forcedOwner :=
  packet.forcedAdapter.sourceToTargetGain_eq_liveMass_mul_defect

/-- The full terminal gap lower-bounds the forced owner's actual defect at the
literal pure singleton row. -/
theorem terminalGap_le_forcedOwnerDefect
    (packet : FinFourWeakCoreForcedPairPacket core) :
    source.residual.witness.terminalGap ≤
      quittingRootCoordinateNashDefect reward
        packet.forcedAdapter.sourceTail.1 packet.forcedAdapter.sourceRoot
          packet.forcedOwner := by
  have hsourceRoot : packet.forcedAdapter.sourceRoot =
      quittingPureSetRoot ({packet.singletonOwner} : Finset (Fin 4)) := by
    funext who
    simp only [QuittingStageAtomConcentratedPacketAdapter.sourceRoot,
      FinFourAtlasWeakConcentratedSingletonCore.pureSingletonProfile,
      quittingProfileLiveRoot_literalPureRootProfile_self, packet.singleton_eq]
    simp [quittingPureSetRoot, quittingSetAction, quittingCoalitionAction]
  have herase :
      (({packet.singletonOwner} : Finset (Fin 4)).erase
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

/-- The forced owner's actual payoff gain is at least the fixed resolution
times the full table gap.  Equality is not asserted: both inputs are lower
bounds rather than exact values. -/
theorem resolution_mul_terminalGap_le_forcedOwnerGain
    (packet : FinFourWeakCoreForcedPairPacket core) :
    core.resolution * source.residual.witness.terminalGap ≤
      packet.forcedOwnerGain := by
  exact packet.forcedAdapter.sourceToTargetGain_lowerBound
    core.resolution source.residual.witness.terminalGap
      (core.resolution_le_pureSingletonStageMass.trans
        (quittingStageCoalitionMass_le_liveMass reward
          core.pureSingletonProfile core.stage core.singleton))
      source.residual.witness.terminalGap_pos.le
      packet.terminalGap_le_forcedOwnerDefect

/-- The payer's actual best-endpoint gain on the forced pair. -/
def payerGain (packet : FinFourWeakCoreForcedPairPacket core) : ℝ :=
  packet.payerAdapter.sourceToTargetGain

/-- The payer gain is the actual reached live mass times its selected root
defect, before any lower bound is applied. -/
theorem payerGain_eq_liveMass_mul_defect
    (packet : FinFourWeakCoreForcedPairPacket core) :
    packet.payerGain =
      quittingLiveMass reward packet.forcedAdapter.targetProfile core.stage *
        quittingRootCoordinateNashDefect reward
          packet.payerAdapter.sourceTail.1 packet.payerAdapter.sourceRoot
            packet.payer :=
  packet.payerAdapter.sourceToTargetGain_eq_liveMass_mul_defect

/-- The direct paid endpoint has the advertised `lambda * D_* / 3` floor. -/
theorem payerGain_floor
    (packet : FinFourWeakCoreForcedPairPacket core) :
    core.resolution * quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      packet.payerGain := by
  have hlive : core.resolution ≤
      quittingLiveMass reward packet.forcedAdapter.targetProfile core.stage :=
    packet.payerAdapter.resolution_le_sourceStageMass.trans
      (quittingStageCoalitionMass_le_liveMass reward
        packet.forcedAdapter.targetProfile core.stage
          packet.forcedAdapter.routedTerminal)
  have hnonneg : 0 ≤
      quittingTerminalSemanticDebtSum source.point.1 / 3 := by
    exact div_nonneg source.minimumDebt_pos.le (by norm_num)
  have hbound := packet.payerAdapter.sourceToTargetGain_lowerBound
    core.resolution (quittingTerminalSemanticDebtSum source.point.1 / 3)
      hlive hnonneg packet.payerDefect_floor
  simpa only [payerGain] using (show
    core.resolution * quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      packet.payerAdapter.sourceToTargetGain by
        calc
          core.resolution * quittingTerminalSemanticDebtSum source.point.1 / 3 =
              core.resolution *
                (quittingTerminalSemanticDebtSum source.point.1 / 3) := by ring
          _ ≤ packet.payerAdapter.sourceToTargetGain := hbound)

/-- The payer's gain is strictly positive. -/
theorem payerGain_pos
    (packet : FinFourWeakCoreForcedPairPacket core) :
    0 < packet.payerGain := by
  have hresolution : 0 < core.resolution := by
    exact source.minimumSingletonClockResolution_pos
  have hfloor : 0 <
      core.resolution * quittingTerminalSemanticDebtSum source.point.1 / 3 := by
    exact div_pos (mul_pos hresolution source.minimumDebt_pos) (by norm_num)
  exact hfloor.trans_le packet.payerGain_floor

/-- At the fixed resolution `mu^2 / 8`, the paid endpoint has the explicit
`mu^2 * D_* / 24` gain floor. -/
theorem canonical_payerGain_floor
    (packet : FinFourWeakCoreForcedPairPacket core) :
    source.point.2 (some source.atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 24 ≤
      packet.payerGain := by
  calc
    source.point.2 (some source.atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 24 =
        core.resolution *
          quittingTerminalSemanticDebtSum source.point.1 / 3 := by
      simp only [FinFourAtlasWeakConcentratedSingletonCore.resolution,
        FinFourMinimumAtomProducer.minimumSingletonClockResolution]
      ring
    _ ≤ packet.payerGain := packet.payerGain_floor

/-- The payer's unrestricted terminal debt decreases by exactly its actual
payoff gain. -/
theorem payerTargetDebt_eq_sourceDebt_sub_gain
    (packet : FinFourWeakCoreForcedPairPacket core) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          packet.payerAdapter.targetProfile) packet.payer =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            packet.forcedAdapter.targetProfile) packet.payer -
        packet.payerGain :=
  packet.payerAdapter.targetOwnerDebt_eq_sourceOwnerDebt_sub_gain

/-- The payer update is literally the pure root of its routed nonempty
terminal over the original core profile. -/
theorem payerTargetProfile_eq_pureRouted
    (packet : FinFourWeakCoreForcedPairPacket core) :
    packet.payerAdapter.targetProfile =
      quittingLiteralPureRootProfile reward core.targetProfile core.stage
        (quittingCoalitionAction packet.payerAdapter.routedTerminal.val) := by
  calc
    packet.payerAdapter.targetProfile =
        quittingLiteralOneDateProfile reward
          packet.forcedAdapter.targetProfile packet.payer core.stage
            packet.payerAdapter.action := rfl
    _ = quittingLiteralOneDateProfile reward
          (quittingLiteralPureRootProfile reward core.targetProfile core.stage
            (quittingCoalitionAction
              packet.forcedAdapter.routedTerminal.val))
          packet.payer core.stage packet.payerAdapter.action := by
        exact congrArg (fun profile ↦ quittingLiteralOneDateProfile reward
          profile packet.payer core.stage packet.payerAdapter.action)
            packet.pairProfile_eq_purePair
    _ = quittingLiteralPureRootProfile reward core.targetProfile core.stage
          (quittingCoalitionAction packet.payerAdapter.routedTerminal.val) := by
        simpa only [quittingLiteralOneDateProfile] using
          quittingLiteralPureRootProfile_update_eq_routed reward
            core.targetProfile core.stage
              packet.forcedAdapter.routedTerminal.val packet.payer
              packet.payerAdapter.action
              packet.payerAdapter.routedTerminal.val rfl

/-- Because both source and target rows are literal pure coalitions, the payer
routes the complete marked mass exactly, not merely monotonically. -/
theorem payerRoutedStageMass_eq_forcedPairStageMass
    (packet : FinFourWeakCoreForcedPairPacket core) :
    quittingStageCoalitionMass reward packet.payerAdapter.targetProfile
        core.stage packet.payerAdapter.routedTerminal =
      quittingStageCoalitionMass reward packet.forcedAdapter.targetProfile
        core.stage packet.forcedAdapter.routedTerminal := by
  calc
    quittingStageCoalitionMass reward packet.payerAdapter.targetProfile
          core.stage packet.payerAdapter.routedTerminal =
        quittingLiveMass reward core.targetProfile core.stage := by
      rw [packet.payerTargetProfile_eq_pureRouted,
        quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
        quittingLiveMass_literalPureRootProfile_eq,
        quittingProfileLiveRoot_literalPureRootProfile_self,
        quittingRootCoalitionMass_pureCoalitionAction_eq_one, mul_one]
    _ = quittingStageCoalitionMass reward packet.forcedAdapter.targetProfile
          core.stage packet.forcedAdapter.routedTerminal :=
      packet.forcedPair_stageMass_eq_liveMass.symm

/-- Equivalently, the payer routes exactly the full live mass inherited from
the original weak core. -/
theorem payerRoutedStageMass_eq_liveMass
    (packet : FinFourWeakCoreForcedPairPacket core) :
    quittingStageCoalitionMass reward packet.payerAdapter.targetProfile
        core.stage packet.payerAdapter.routedTerminal =
      quittingLiveMass reward core.targetProfile core.stage := by
  rw [packet.payerRoutedStageMass_eq_forcedPairStageMass,
    packet.forcedPair_stageMass_eq_liveMass]

/-- The forced pair is a literal one-date edit of the original weak-core
profile; every complete strategy is unchanged away from that date. -/
theorem forcedPairProfile_at_of_ne
    (packet : FinFourWeakCoreForcedPairPacket core)
    (time : ℕ) (htime : time ≠ core.stage) (player : Fin 4) :
    packet.forcedAdapter.targetProfile player time =
      core.targetProfile player time := by
  exact (packet.forcedAdapter.targetProfile_at_of_ne time htime player).trans
    (core.pureSingletonProfile_at_of_ne time htime player)

/-- The final paid endpoint also changes no complete strategy away from the
one marked date. -/
theorem payerTargetProfile_at_of_ne
    (packet : FinFourWeakCoreForcedPairPacket core)
    (time : ℕ) (htime : time ≠ core.stage) (player : Fin 4) :
    packet.payerAdapter.targetProfile player time =
      core.targetProfile player time := by
  exact (packet.payerAdapter.targetProfile_at_of_ne time htime player).trans
    (packet.forcedPairProfile_at_of_ne time htime player)

/-- The forced pair keeps the weak core's literal post-date source tail. -/
theorem forcedPair_postDate_liveRoot_eq_reference
    (packet : FinFourWeakCoreForcedPairPacket core) (offset : ℕ) :
    quittingProfileLiveRoot reward packet.forcedAdapter.targetProfile
        (core.stage + 1 + offset) =
      quittingProfileLiveRoot reward core.referenceProfile
        (core.stage + 1 + offset) := by
  rw [packet.forcedAdapter.targetProfile_postDate_liveRoot_eq]
  exact core.pureSingleton_postDate_liveRoot_eq_reference offset

/-- The paid target retains that same literal post-date source tail. -/
theorem payerTarget_postDate_liveRoot_eq_reference
    (packet : FinFourWeakCoreForcedPairPacket core) (offset : ℕ) :
    quittingProfileLiveRoot reward packet.payerAdapter.targetProfile
        (core.stage + 1 + offset) =
      quittingProfileLiveRoot reward core.referenceProfile
        (core.stage + 1 + offset) := by
  rw [packet.payerAdapter.targetProfile_postDate_liveRoot_eq]
  exact packet.forcedPair_postDate_liveRoot_eq_reference offset

/-- Semantic-tail form of the forced pair's exact source provenance. -/
theorem forcedPair_postDateTail_eq_reference
    (packet : FinFourWeakCoreForcedPairPacket core) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          packet.forcedAdapter.targetProfile (core.stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward core.referenceProfile
          (core.stage + 1)) := by
  apply quittingTerminalSemanticPair_eq_of_liveRoot_eq
  funext offset player
  change (quittingAllContinueProfileSpine reward
      packet.forcedAdapter.targetProfile (core.stage + 1)) player offset
        (quittingLiveHist reward offset) =
    (quittingAllContinueProfileSpine reward core.referenceProfile
      (core.stage + 1)) player offset (quittingLiveHist reward offset)
  rw [quittingAllContinueProfileSpine_apply_liveHist,
    quittingAllContinueProfileSpine_apply_liveHist]
  exact congrFun (packet.forcedPair_postDate_liveRoot_eq_reference offset) player

/-- Semantic-tail form of the paid target's exact source provenance. -/
theorem payerTarget_postDateTail_eq_reference
    (packet : FinFourWeakCoreForcedPairPacket core) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          packet.payerAdapter.targetProfile (core.stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward core.referenceProfile
          (core.stage + 1)) := by
  apply quittingTerminalSemanticPair_eq_of_liveRoot_eq
  funext offset player
  change (quittingAllContinueProfileSpine reward
      packet.payerAdapter.targetProfile (core.stage + 1)) player offset
        (quittingLiveHist reward offset) =
    (quittingAllContinueProfileSpine reward core.referenceProfile
      (core.stage + 1)) player offset (quittingLiveHist reward offset)
  rw [quittingAllContinueProfileSpine_apply_liveHist,
    quittingAllContinueProfileSpine_apply_liveHist]
  exact congrFun (packet.payerTarget_postDate_liveRoot_eq_reference offset) player

end FinFourWeakCoreForcedPairPacket

namespace FinFourAtlasWeakConcentratedSingletonCore

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Every source-attached weak singleton core produces a literal
full-gap pair and a direct paid endpoint away from its zero-defect forced
owner. -/
theorem nonempty_forcedPairPacket
    (core : FinFourAtlasWeakConcentratedSingletonCore source) :
    Nonempty (FinFourWeakCoreForcedPairPacket core) := by
  obtain ⟨singletonOwner, hsingleton⟩ := Finset.card_eq_one.mp core.singleton_card
  obtain ⟨forcedOwner, hforcedNe, hgap⟩ :=
    source.residual.exists_terminalGap_collision_at_singleton singletonOwner
  have hterminalNe : core.singleton.val ≠ {forcedOwner} := by
    rw [hsingleton]
    exact fun heq ↦ hforcedNe (Finset.singleton_inj.mp heq).symm
  obtain ⟨forcedAdapter⟩ :=
    QuittingStageAtomConcentratedPacketAdapter.nonempty_of_stageMass
      core.pureSingletonProfile core.singleton forcedOwner core.stage
        core.resolution hterminalNe
        source.minimumSingletonClockResolution_pos
        core.resolution_le_pureSingletonStageMass
  have hsourceRoot : forcedAdapter.sourceRoot =
      quittingPureSetRoot ({singletonOwner} : Finset (Fin 4)) := by
    funext who
    simp only [QuittingStageAtomConcentratedPacketAdapter.sourceRoot,
      pureSingletonProfile,
      quittingProfileLiveRoot_literalPureRootProfile_self, hsingleton]
    simp [quittingPureSetRoot, quittingSetAction, quittingCoalitionAction]
  have herase : (({singletonOwner} : Finset (Fin 4)).erase forcedOwner).Nonempty := by
    simp [hforcedNe]
  have hcontinue : quittingRootContinuePayoff reward forcedAdapter.sourceTail.1
        forcedAdapter.sourceRoot forcedOwner =
      quittingSetReward reward {singletonOwner} forcedOwner := by
    rw [hsourceRoot,
      quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
        forcedAdapter.sourceTail.1 {singletonOwner} forcedOwner herase]
    simp [hforcedNe]
  have hquit : quittingRootQuitPayoff reward forcedAdapter.sourceTail.1
        forcedAdapter.sourceRoot forcedOwner =
      quittingSetReward reward {singletonOwner, forcedOwner} forcedOwner := by
    rw [hsourceRoot, quittingRootQuitPayoff_pureSetRoot_eq_insert]
    simp [Finset.pair_comm]
  have hstrict : quittingRootContinuePayoff reward forcedAdapter.sourceTail.1
        forcedAdapter.sourceRoot forcedOwner <
      quittingRootQuitPayoff reward forcedAdapter.sourceTail.1
        forcedAdapter.sourceRoot forcedOwner := by
    rw [hcontinue, hquit]
    linarith [source.residual.witness.terminalGap_pos]
  have hforcedAction : forcedAdapter.action = true := by
    unfold QuittingStageAtomConcentratedPacketAdapter.action
      quittingRootBestEndpointAction
    simp [not_le.mpr hstrict]
  have hforcedTerminal : forcedAdapter.routedTerminal.val =
      {singletonOwner, forcedOwner} := by
    rw [QuittingStageAtomConcentratedPacketAdapter.routedTerminal_val]
    simp only [QuittingStageAtomConcentratedPacketAdapter.routedCoalition,
      hforcedAction, quittingPureEndpointRoutedCoalition_true, hsingleton]
    exact Finset.pair_comm _ _
  have hforcedCard : forcedAdapter.routedTerminal.val.card = 2 := by
    rw [hforcedTerminal]
    have hnot : singletonOwner ∉ ({forcedOwner} : Finset (Fin 4)) := by
      simpa using hforcedNe.symm
    rw [Finset.card_insert_of_notMem hnot]
    simp
  let pairCoalition : QuittingNonsingletonCoalition (Fin 4) :=
    ⟨forcedAdapter.routedTerminal.val, by omega⟩
  have hpairProfile : forcedAdapter.targetProfile =
      quittingLiteralPureRootCoalitionProfile reward core.targetProfile
        core.stage pairCoalition := by
    simpa only [QuittingStageAtomConcentratedPacketAdapter.targetProfile,
      pureSingletonProfile, quittingLiteralOneDateProfile, pairCoalition,
      quittingLiteralPureRootCoalitionProfile, quittingPureRootOfCoalition] using
      quittingLiteralPureRootProfile_update_eq_routed reward
        core.targetProfile core.stage core.singleton.val forcedOwner
          forcedAdapter.action forcedAdapter.routedTerminal.val rfl
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward forcedAdapter.targetProfile
      (core.stage + 1))
  let root := quittingProfileLiveRoot reward forcedAdapter.targetProfile core.stage
  let current := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward forcedAdapter.targetProfile core.stage)
  have hcurrentCarrier : current ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have hminimumFloor : quittingTerminalSemanticDebtSum source.point.1 ≤
      quittingTerminalSemanticDebtSum current :=
    source.minimum current hcurrentCarrier
  have hsum : quittingTerminalSemanticDebtSum current =
      ∑ who, quittingRootCoordinateNashDefect reward tail.1 root who := by
    have hraw :=
      quittingTerminalSemanticDebtSum_pureNonsingletonRow_eq_totalDefect
        reward core.targetProfile core.stage pairCoalition
    rw [← hpairProfile] at hraw
    simpa only [current, tail, root] using hraw
  have hforcedZero :
      quittingRootCoordinateNashDefect reward tail.1 root forcedOwner = 0 := by
    change quittingRootCoordinateNashDefect reward
        forcedAdapter.targetTail.1
        (quittingProfileLiveRoot reward forcedAdapter.targetProfile core.stage)
        forcedOwner = 0
    exact forcedAdapter.ownerMarkedDefect_eq_zero
  let others : Finset (Fin 4) := Finset.univ.erase forcedOwner
  have hothers : others.Nonempty := by
    exact ⟨singletonOwner, Finset.mem_erase.mpr
      ⟨fun heq ↦ hforcedNe heq.symm, Finset.mem_univ singletonOwner⟩⟩
  obtain ⟨payer, hpayerMem, haverage⟩ :=
    QuittingMarkedFencePacket.exists_sum_le_card_mul others hothers
      (fun who ↦ quittingRootCoordinateNashDefect reward tail.1 root who)
  have hpayerNe : payer ≠ forcedOwner := by
    exact (Finset.mem_erase.mp hpayerMem).1
  have hsumOthers :
      ∑ who ∈ others,
          quittingRootCoordinateNashDefect reward tail.1 root who =
        ∑ who, quittingRootCoordinateNashDefect reward tail.1 root who := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun who ↦ quittingRootCoordinateNashDefect reward tail.1 root who)
      (Finset.mem_univ forcedOwner)]
    simp only [others, hforcedZero, add_zero]
  have haverage' :
      (∑ who, quittingRootCoordinateNashDefect reward tail.1 root who) ≤
        3 * quittingRootCoordinateNashDefect reward tail.1 root payer := by
    rw [← hsumOthers]
    simpa [others] using haverage
  have hpayerFloor : quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      quittingRootCoordinateNashDefect reward tail.1 root payer := by
    have htotal := hminimumFloor.trans (hsum.trans_le haverage')
    linarith
  have hpayerTerminal : forcedAdapter.routedTerminal.val ≠ {payer} := by
    intro heq
    have hone : forcedAdapter.routedTerminal.val.card = 1 := by
      rw [heq]
      simp
    omega
  have hpayerMass : core.resolution ≤
      quittingStageCoalitionMass reward forcedAdapter.targetProfile core.stage
        forcedAdapter.routedTerminal :=
    forcedAdapter.resolution_le_targetStageMass
  obtain ⟨payerAdapter⟩ :=
    QuittingStageAtomConcentratedPacketAdapter.nonempty_of_stageMass
      forcedAdapter.targetProfile forcedAdapter.routedTerminal payer core.stage
        core.resolution hpayerTerminal
        source.minimumSingletonClockResolution_pos hpayerMass
  exact ⟨{
    singletonOwner := singletonOwner
    singleton_eq := hsingleton
    forcedOwner := forcedOwner
    forcedOwner_ne_singletonOwner := hforcedNe
    terminalGap_join := hgap
    forcedAdapter := forcedAdapter
    forcedAction_eq_true := hforcedAction
    payer := payer
    payer_ne_forcedOwner := hpayerNe
    payerAdapter := payerAdapter
    payerDefect_floor := by
      simpa only [QuittingStageAtomConcentratedPacketAdapter.sourceTail,
        QuittingStageAtomConcentratedPacketAdapter.sourceRoot, tail, root] using
        hpayerFloor
  }⟩

end FinFourAtlasWeakConcentratedSingletonCore

end GameTheory
