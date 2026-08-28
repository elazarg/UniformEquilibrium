/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.ForcedPair
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

/-- The literal pure-singleton sibling at the same date. -/
def pureSingletonProfile
    (frame : FinFourExplicitResolutionSingletonFrame source) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralPureRootProfile reward frame.targetProfile frame.stage
    (quittingCoalitionAction frame.singleton.val)

/-- Pureification assigns the full reached live mass to the singleton. -/
theorem pureSingleton_stageMass_eq_liveMass
    (frame : FinFourExplicitResolutionSingletonFrame source) :
    quittingStageCoalitionMass reward frame.pureSingletonProfile frame.stage
        frame.singleton =
      quittingLiveMass reward frame.targetProfile frame.stage := by
  unfold pureSingletonProfile
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_literalPureRootProfile_eq,
    quittingProfileLiveRoot_literalPureRootProfile_self,
    quittingRootCoalitionMass_pureCoalitionAction_eq_one, mul_one]

/-- The explicit resolution survives pureification. -/
theorem resolution_le_pureSingletonStageMass
    (frame : FinFourExplicitResolutionSingletonFrame source) :
    frame.resolution ≤ quittingStageCoalitionMass reward
      frame.pureSingletonProfile frame.stage frame.singleton := by
  rw [frame.pureSingleton_stageMass_eq_liveMass]
  exact frame.resolution_le_stageMass.trans
    (quittingStageCoalitionMass_le_liveMass reward frame.targetProfile
      frame.stage frame.singleton)

/-- Pureification changes no behavior away from the marked date. -/
theorem pureSingletonProfile_at_of_ne
    (frame : FinFourExplicitResolutionSingletonFrame source)
    (time : ℕ) (htime : time ≠ frame.stage) (player : Fin 4) :
    frame.pureSingletonProfile player time = frame.targetProfile player time := by
  unfold pureSingletonProfile quittingLiteralPureRootProfile
    quittingLiteralOneDateOverride
  simp [htime]

/-- The pure singleton retains the frame's complete post-date reference
spine. -/
theorem pureSingleton_postDateSpine_eq_reference
    (frame : FinFourExplicitResolutionSingletonFrame source) :
    quittingAllContinueProfileSpine reward frame.pureSingletonProfile
        (frame.stage + 1) =
      quittingAllContinueProfileSpine reward frame.referenceProfile
        (frame.stage + 1) := by
  calc
    quittingAllContinueProfileSpine reward frame.pureSingletonProfile
          (frame.stage + 1) =
        quittingAllContinueProfileSpine reward frame.targetProfile
          (frame.stage + 1) := by
      apply quittingAllContinueProfileSpine_eq_of_eq_from
      intro player time history htime
      exact frame.pureSingletonProfile_at_of_ne time (by omega) player
        |> congrFun history
    _ = _ := frame.postDateSpine_eq_reference

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

/-- The forced terminal is the displayed pair. -/
theorem forcedTerminal_val
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    packet.forcedAdapter.routedTerminal.val =
      {packet.singletonOwner, packet.forcedOwner} := by
  rw [QuittingStageAtomConcentratedPacketAdapter.routedTerminal_val]
  simp only [QuittingStageAtomConcentratedPacketAdapter.routedCoalition,
    packet.forcedAction_eq_true,
    quittingPureEndpointRoutedCoalition_true, packet.singleton_eq]
  exact Finset.pair_comm _ _

/-- The forced terminal is genuinely a pair. -/
theorem forcedTerminal_card
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    packet.forcedAdapter.routedTerminal.val.card = 2 := by
  rw [packet.forcedTerminal_val]
  have hnot : packet.singletonOwner ∉
      ({packet.forcedOwner} : Finset (Fin 4)) := by
    simpa using packet.forcedOwner_ne_singletonOwner.symm
  rw [Finset.card_insert_of_notMem hnot]
  simp

/-- The forced owner has zero marked defect at the pair. -/
theorem forcedOwnerDefect_eq_zero
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    quittingRootCoordinateNashDefect reward
        packet.payerAdapter.sourceTail.1 packet.payerAdapter.sourceRoot
        packet.forcedOwner = 0 := by
  have htail : packet.payerAdapter.sourceTail =
      packet.forcedAdapter.targetTail := rfl
  have hroot : packet.payerAdapter.sourceRoot =
      quittingProfileLiveRoot reward packet.forcedAdapter.targetProfile
        frame.stage := rfl
  rw [htail, hroot]
  exact packet.forcedAdapter.ownerMarkedDefect_eq_zero

/-- The payer's actual one-date best-endpoint gain. -/
def payerGain
    (packet : FinFourExplicitResolutionForcedPairPacket frame) : ℝ :=
  packet.payerAdapter.sourceToTargetGain

/-- The payer gain has the exact explicit-resolution floor. -/
theorem payerGain_floor
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    frame.resolution * quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      packet.payerGain := by
  have hlive : frame.resolution ≤
      quittingLiveMass reward packet.forcedAdapter.targetProfile frame.stage :=
    packet.payerAdapter.resolution_le_sourceStageMass.trans
      (quittingStageCoalitionMass_le_liveMass reward
        packet.forcedAdapter.targetProfile frame.stage
          packet.forcedAdapter.routedTerminal)
  have hnonneg :
      0 ≤ quittingTerminalSemanticDebtSum source.point.1 / 3 :=
    div_nonneg source.minimumDebt_pos.le (by norm_num)
  have hbound := packet.payerAdapter.sourceToTargetGain_lowerBound
    frame.resolution (quittingTerminalSemanticDebtSum source.point.1 / 3)
      hlive hnonneg packet.payerDefect_floor
  simpa only [payerGain] using (show
    frame.resolution * quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
        packet.payerAdapter.sourceToTargetGain by
      calc
        frame.resolution * quittingTerminalSemanticDebtSum source.point.1 / 3 =
            frame.resolution *
              (quittingTerminalSemanticDebtSum source.point.1 / 3) := by ring
        _ ≤ packet.payerAdapter.sourceToTargetGain := hbound)

/-- The payer gain is strictly positive. -/
theorem payerGain_pos
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    0 < packet.payerGain := by
  have hfloor : 0 < frame.resolution *
      quittingTerminalSemanticDebtSum source.point.1 / 3 :=
    div_pos (mul_pos frame.resolution_pos source.minimumDebt_pos) (by norm_num)
  exact hfloor.trans_le packet.payerGain_floor

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
  packet.payerAdapter.targetOwnerDebt_eq_sourceOwnerDebt_sub_gain

/-- The forced pair changes no behavior away from the marked date. -/
theorem forcedPairProfile_at_of_ne
    (packet : FinFourExplicitResolutionForcedPairPacket frame)
    (time : ℕ) (htime : time ≠ frame.stage) (player : Fin 4) :
    packet.forcedAdapter.targetProfile player time =
      frame.targetProfile player time := by
  exact (packet.forcedAdapter.targetProfile_at_of_ne time htime player).trans
    (frame.pureSingletonProfile_at_of_ne time htime player)

/-- The paid target changes no behavior away from the marked date. -/
theorem payerTargetProfile_at_of_ne
    (packet : FinFourExplicitResolutionForcedPairPacket frame)
    (time : ℕ) (htime : time ≠ frame.stage) (player : Fin 4) :
    packet.payerAdapter.targetProfile player time =
      frame.targetProfile player time := by
  exact (packet.payerAdapter.targetProfile_at_of_ne time htime player).trans
    (packet.forcedPairProfile_at_of_ne time htime player)

/-- The forced pair retains the complete post-date reference spine. -/
theorem forcedPair_postDateSpine_eq_reference
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    quittingAllContinueProfileSpine reward packet.forcedAdapter.targetProfile
        (frame.stage + 1) =
      quittingAllContinueProfileSpine reward frame.referenceProfile
        (frame.stage + 1) := by
  calc
    quittingAllContinueProfileSpine reward packet.forcedAdapter.targetProfile
          (frame.stage + 1) =
        quittingAllContinueProfileSpine reward frame.targetProfile
          (frame.stage + 1) := by
      apply quittingAllContinueProfileSpine_eq_of_eq_from
      intro player time history htime
      exact packet.forcedPairProfile_at_of_ne time (by omega) player
        |> congrFun history
    _ = _ := frame.postDateSpine_eq_reference

/-- The paid target retains the same complete post-date reference spine. -/
theorem payerTarget_postDateSpine_eq_reference
    (packet : FinFourExplicitResolutionForcedPairPacket frame) :
    quittingAllContinueProfileSpine reward packet.payerAdapter.targetProfile
        (frame.stage + 1) =
      quittingAllContinueProfileSpine reward frame.referenceProfile
        (frame.stage + 1) := by
  calc
    quittingAllContinueProfileSpine reward packet.payerAdapter.targetProfile
          (frame.stage + 1) =
        quittingAllContinueProfileSpine reward frame.targetProfile
          (frame.stage + 1) := by
      apply quittingAllContinueProfileSpine_eq_of_eq_from
      intro player time history htime
      exact packet.payerTargetProfile_at_of_ne time (by omega) player
        |> congrFun history
    _ = _ := frame.postDateSpine_eq_reference

end FinFourExplicitResolutionForcedPairPacket

namespace FinFourExplicitResolutionSingletonFrame

/-- Every explicit-resolution singleton frame produces the full-gap pair and
paid endpoint at that same resolution. -/
theorem nonempty_forcedPairPacket
    (frame : FinFourExplicitResolutionSingletonFrame source) :
    Nonempty (FinFourExplicitResolutionForcedPairPacket frame) := by
  obtain ⟨singletonOwner, hsingleton⟩ :=
    Finset.card_eq_one.mp frame.singleton_card
  obtain ⟨forcedOwner, hforcedNe, hgap⟩ :=
    source.residual.exists_terminalGap_collision_at_singleton singletonOwner
  have hterminalNe : frame.singleton.val ≠ {forcedOwner} := by
    rw [hsingleton]
    exact fun heq ↦ hforcedNe (Finset.singleton_inj.mp heq).symm
  obtain ⟨forcedAdapter⟩ :=
    QuittingStageAtomConcentratedPacketAdapter.nonempty_of_stageMass
      frame.pureSingletonProfile frame.singleton forcedOwner frame.stage
        frame.resolution hterminalNe frame.resolution_pos
        frame.resolution_le_pureSingletonStageMass
  have hsourceRoot : forcedAdapter.sourceRoot =
      quittingPureSetRoot ({singletonOwner} : Finset (Fin 4)) := by
    funext who
    simp only [QuittingStageAtomConcentratedPacketAdapter.sourceRoot,
      pureSingletonProfile,
      quittingProfileLiveRoot_literalPureRootProfile_self, hsingleton]
    simp [quittingPureSetRoot, quittingSetAction, quittingCoalitionAction]
  have herase : (({singletonOwner} : Finset (Fin 4)).erase
      forcedOwner).Nonempty := by
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
      quittingLiteralPureRootCoalitionProfile reward frame.targetProfile
        frame.stage pairCoalition := by
    simpa only [QuittingStageAtomConcentratedPacketAdapter.targetProfile,
      pureSingletonProfile, quittingLiteralOneDateProfile, pairCoalition,
      quittingLiteralPureRootCoalitionProfile, quittingPureRootOfCoalition] using
      quittingLiteralPureRootProfile_update_eq_routed reward
        frame.targetProfile frame.stage frame.singleton.val forcedOwner
          forcedAdapter.action forcedAdapter.routedTerminal.val rfl
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward forcedAdapter.targetProfile
      (frame.stage + 1))
  let root := quittingProfileLiveRoot reward forcedAdapter.targetProfile
    frame.stage
  let current := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward forcedAdapter.targetProfile
      frame.stage)
  have hcurrentCarrier : current ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have hminimumFloor : quittingTerminalSemanticDebtSum source.point.1 ≤
      quittingTerminalSemanticDebtSum current :=
    source.minimum current hcurrentCarrier
  have hsum : quittingTerminalSemanticDebtSum current =
      ∑ who, quittingRootCoordinateNashDefect reward tail.1 root who := by
    have hraw :=
      quittingTerminalSemanticDebtSum_pureNonsingletonRow_eq_totalDefect
        reward frame.targetProfile frame.stage pairCoalition
    rw [← hpairProfile] at hraw
    simpa only [current, tail, root] using hraw
  have hforcedZero :
      quittingRootCoordinateNashDefect reward tail.1 root forcedOwner = 0 := by
    change quittingRootCoordinateNashDefect reward
        forcedAdapter.targetTail.1
        (quittingProfileLiveRoot reward forcedAdapter.targetProfile frame.stage)
        forcedOwner = 0
    exact forcedAdapter.ownerMarkedDefect_eq_zero
  let others : Finset (Fin 4) := Finset.univ.erase forcedOwner
  have hothers : others.Nonempty := by
    exact ⟨singletonOwner, Finset.mem_erase.mpr
      ⟨fun heq ↦ hforcedNe heq.symm, Finset.mem_univ singletonOwner⟩⟩
  obtain ⟨payer, hpayerMem, haverage⟩ :=
    QuittingMarkedFencePacket.exists_sum_le_card_mul others hothers
      (fun who ↦ quittingRootCoordinateNashDefect reward tail.1 root who)
  have hpayerNe : payer ≠ forcedOwner :=
    (Finset.mem_erase.mp hpayerMem).1
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
  have hpayerMass : frame.resolution ≤
      quittingStageCoalitionMass reward forcedAdapter.targetProfile frame.stage
        forcedAdapter.routedTerminal :=
    forcedAdapter.resolution_le_targetStageMass
  obtain ⟨payerAdapter⟩ :=
    QuittingStageAtomConcentratedPacketAdapter.nonempty_of_stageMass
      forcedAdapter.targetProfile forcedAdapter.routedTerminal payer frame.stage
        frame.resolution hpayerTerminal frame.resolution_pos hpayerMass
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

end FinFourExplicitResolutionSingletonFrame

namespace FinFourSourceFaithfulRenewedSingletonPacket

variable {point : QuittingTerminalSemanticLawPoint (Fin 4)}
variable {terminal : {S : Finset (Fin 4) // S.Nonempty}}
variable {profiles : ℕ → (quittingGame reward).BehaviorProfile}
variable {mark : ℕ → ℕ} {lambda resolution : ℝ}
variable {causal : QuittingSourceFaithfulMinimumCausalization
  point terminal profiles mark lambda}
variable {terminalNonsingleton : 1 < terminal.val.card}

/-- One renewed singleton endpoint as an explicit-resolution forced-pair
frame, retaining the source-faithful causal profile as its reference. -/
def toExplicitResolutionFrame
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) (rank : ℕ) :
    FinFourExplicitResolutionSingletonFrame source where
  referenceProfile := sourceProfile causal packet.cutoff rank
  targetProfile := (packet.endpoint rank).targetProfile
  stage := sourceMark causal packet.cutoff rank
  singleton := (packet.endpoint rank).singleton
  resolution := resolution
  resolution_pos := packet.resolution_pos
  singleton_card := packet.singleton_card rank
  resolution_le_stageMass := packet.resolution_le_singletonStageMass rank
  postDateSpine_eq_reference := packet.endpoint_postDateSpine_eq_source rank

/-- Every renewed singleton endpoint reconstructs the full forced-pair paid
packet at the same absolute resolution. -/
theorem nonempty_forcedPairPacket
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) (rank : ℕ) :
    Nonempty (FinFourExplicitResolutionForcedPairPacket
      (packet.toExplicitResolutionFrame rank)) :=
  (packet.toExplicitResolutionFrame rank).nonempty_forcedPairPacket

end FinFourSourceFaithfulRenewedSingletonPacket

end GameTheory
