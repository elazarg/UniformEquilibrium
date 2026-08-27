/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.MinimumReturnForcedPair
import Research.Quitting.MaximalCapSemanticPrefixReturn

/-!
# The source-facing Fin4 maximal-prefix ray dichotomy

A fixed cofinal forced-pair source supplies one literal pair, one marked
zero-defect owner, one fixed payer, and near-minimum reference tails.  This
module puts the date-zero pure pair followed by each reference tail behind a
single semantic-cap maximal-prefix word.

The minimum-limit arm constructs an actual concentrated packet at resolution
`D_* / D_0` and invokes the existing transfer and limit-chord consumers.  The
strict arm retains only the quantitative canonical-ray stall and its checked
support-entry alternative.  It has no downstream completion claim.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Set
open QuittingSureSetOwnerRepair

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}
  {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- The literal fixed pair at the base of the new common semantic ray. -/
def rayTerminal
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) : {S : Finset (Fin 4) // S.Nonempty} :=
  packet.movingTerminal

/-- The source semantic pair of a sure pure pair.  This formula is independent
of the behavioral continuation because the pair has two sure quitters. -/
def raySource
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) : QuittingTerminalSemanticPair (Fin 4) :=
  (quittingSetReward reward packet.rayTerminal.val,
    fun who ↦ max
      (quittingSetReward reward (insert who packet.rayTerminal.val) who)
      (quittingSetReward reward (packet.rayTerminal.val.erase who) who))

/-- The original cofinal near-minimum tail selected at one frozen-payer row. -/
def rayTail
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  packet.base.referenceProfile (packet.subsequence index)

/-- Date-zero pure pair followed counterfactually by the selected reference
tail.  No changed endpoint is used to recompute the outer maximal roots. -/
def rayBaseProfile
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward
    (quittingPureSetRoot packet.rayTerminal.val) (packet.rayTail index)

theorem rayBaseProfile_semantic_eq
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalSemanticPair reward (packet.rayBaseProfile index) =
      packet.raySource := by
  unfold rayBaseProfile raySource
  exact quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
    reward packet.rayTerminal.val (by
      rw [rayTerminal, packet.movingTerminal_card]) _

theorem rayBaseProfile_postMarkSpine_eq_tail
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingAllContinueProfileSpine reward (packet.rayBaseProfile index) 1 =
      packet.rayTail index := by
  change quittingProfileAllContinueContinuation reward
      (packet.rayBaseProfile index) = packet.rayTail index
  unfold rayBaseProfile
  exact
    quittingProfileAllContinueContinuation_pureSetRootThenContinuation
      reward packet.rayTerminal.val (packet.rayTail index)

theorem rayBaseProfile_stageMass_eq_one
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingStageCoalitionMass reward (packet.rayBaseProfile index) 0
      packet.rayTerminal = 1 := by
  rw [rayBaseProfile, quittingStageCoalitionMass_rootThenContinuation_zero]
  change quittingRootCoalitionMass
      (fun who ↦ PMF.pure (quittingSetAction packet.rayTerminal.val who))
      packet.rayTerminal.val = 1
  have hroot :
      (fun who ↦ PMF.pure (quittingSetAction packet.rayTerminal.val who)) =
        fun who ↦ PMF.pure
          (quittingCoalitionAction packet.rayTerminal.val who) := by
    funext who
    apply congrArg PMF.pure
    simp [quittingSetAction, quittingCoalitionAction]
  rw [hroot]
  exact quittingRootCoalitionMass_pureCoalitionAction_eq_one _

private theorem forcedMarkedRoot_eq_rayPureRoot
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingProfileLiveRoot reward
        (packet.base.forcedAdapter
          (packet.subsequence index)).targetProfile
        (packet.base.endpoint (packet.subsequence index)).stage =
      quittingPureSetRoot packet.rayTerminal.val := by
  let adapter := packet.base.forcedAdapter (packet.subsequence index)
  have hprofile : adapter.targetProfile =
      quittingLiteralPureRootProfile reward
        (packet.base.crossTailProfile (packet.subsequence index))
        (packet.base.endpoint (packet.subsequence index)).stage
        (quittingCoalitionAction adapter.routedTerminal.val) := by
    rw [QuittingStageAtomConcentratedPacketAdapter.targetProfile_eq_literalOneDateProfile]
    exact quittingLiteralPureRootProfile_update_eq_routed reward
      (packet.base.crossTailProfile (packet.subsequence index))
      (packet.base.endpoint (packet.subsequence index)).stage
      source.atom.terminal.val returnSource.forcedOwner adapter.action
      adapter.routedTerminal.val rfl
  rw [hprofile, quittingProfileLiveRoot_literalPureRootProfile_self]
  have hterminal := packet.forcedTerminal_eq_movingTerminal index
  rw [hterminal]
  rfl

theorem rayBaseProfile_ownerDefect_eq_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward (packet.rayTail index)).1
        (quittingProfileLiveRoot reward (packet.rayBaseProfile index) 0)
        returnSource.forcedOwner = 0 := by
  have hzero := packet.forcedOwnerDefect_eq_zero index
  rw [packet.forcedTargetTail_eq_referenceSemantic] at hzero
  rw [rayBaseProfile, quittingProfileLiveRoot_rootThenContinuation_zero]
  rw [← packet.forcedMarkedRoot_eq_rayPureRoot index]
  exact hzero

/-- The exact generic common-semantic marked family extracted from the fixed
source object and its fixed-resolution payer subsequence. -/
def rayFamily
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    QuittingCommonSemanticMarkedBaseFamily reward source.point.1
      packet.raySource returnSource.forcedOwner packet.rayTerminal where
  profiles := packet.rayBaseProfile
  tails := packet.rayTail
  source_eq := packet.rayBaseProfile_semantic_eq
  postMarkSpine_eq := packet.rayBaseProfile_postMarkSpine_eq_tail
  stageMass_eq_one := packet.rayBaseProfile_stageMass_eq_one
  ownerDefect_eq_zero := packet.rayBaseProfile_ownerDefect_eq_zero
  tailDebt_tendsto := by
    simpa only [rayTail] using packet.referenceDebt_tendsto

theorem raySource_mem
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    packet.raySource ∈ quittingTerminalSemanticCarrier reward := by
  rw [← packet.rayBaseProfile_semantic_eq 0]
  exact quittingTerminalSemanticPair_mem_carrier reward _

theorem raySourceDebt_pos
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    0 < quittingTerminalSemanticDebtSum packet.raySource :=
  source.minimumDebt_pos.trans_le
    (source.minimum packet.raySource packet.raySource_mem)

/-- The fixed resolution used by the equality-arm moving packet.  It is
selected from the semantic ray, not inherited from the packet's auxiliary
row-selection parameter `lambda`. -/
def rayResolution
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) : ℝ :=
  quittingTerminalSemanticDebtSum source.point.1 /
    quittingTerminalSemanticDebtSum packet.raySource

theorem rayResolution_pos
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    0 < packet.rayResolution :=
  div_pos source.minimumDebt_pos packet.raySourceDebt_pos

theorem rayResolution_le_one
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    packet.rayResolution ≤ 1 := by
  exact (div_le_one packet.raySourceDebt_pos).2
    (source.minimum packet.raySource packet.raySource_mem)

private theorem rayTerminal_ne_singleton_payer
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    packet.rayTerminal.val ≠ {packet.payer} := by
  intro heq
  have hcard : packet.rayTerminal.val.card = 1 := by simp [heq]
  rw [rayTerminal, packet.movingTerminal_card] at hcard
  omega

/-- At date zero, select the same table-determined best endpoint for the
already frozen payer, now on the literal pure-pair/reference-tail row. -/
theorem nonempty_rayPaidAdapter
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    Nonempty (QuittingStageAtomConcentratedPacketAdapter reward
      (packet.rayBaseProfile index) packet.rayTerminal packet.payer 0
        packet.rayResolution) := by
  apply QuittingStageAtomConcentratedPacketAdapter.nonempty_of_stageMass
  · exact packet.rayTerminal_ne_singleton_payer
  · exact packet.rayResolution_pos
  · rw [packet.rayBaseProfile_stageMass_eq_one]
    exact packet.rayResolution_le_one

/-- One actual date-zero paid endpoint.  Its owner label is the payer already
frozen by the cofinal source packet; no new label is selected. -/
theorem rayPaidAdapter
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    QuittingStageAtomConcentratedPacketAdapter reward
      (packet.rayBaseProfile index) packet.rayTerminal packet.payer 0
        packet.rayResolution :=
  Classical.choice (packet.nonempty_rayPaidAdapter index)

theorem rayPaidAdapter_sourceTail_eq_reference
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (packet.rayPaidAdapter index).sourceTail =
      quittingTerminalSemanticPair reward (packet.rayTail index) := by
  unfold QuittingStageAtomConcentratedPacketAdapter.sourceTail
  exact congrArg (quittingTerminalSemanticPair reward)
    (packet.rayBaseProfile_postMarkSpine_eq_tail index)

theorem rayPaidAdapter_sourceRoot_eq
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (packet.rayPaidAdapter index).sourceRoot =
      quittingPureSetRoot packet.rayTerminal.val := by
  unfold QuittingStageAtomConcentratedPacketAdapter.sourceRoot
  rw [rayBaseProfile, quittingProfileLiveRoot_rootThenContinuation_zero]

private theorem rowPayerAdapter_sourceTail_eq_reference
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (packet.row index).payerAdapter.sourceTail =
      quittingTerminalSemanticPair reward (packet.rayTail index) := by
  rw [← (packet.row index).payerAdapter.targetTail_eq_sourceTail]
  simpa only [rayTail] using packet.payerTargetTail_eq_referenceSemantic index

private theorem rowPayerAdapter_sourceRoot_eq
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (packet.row index).payerAdapter.sourceRoot =
      quittingPureSetRoot packet.rayTerminal.val := by
  unfold QuittingStageAtomConcentratedPacketAdapter.sourceRoot
  exact packet.forcedMarkedRoot_eq_rayPureRoot index

theorem rayPaidAdapter_defect_eq_row
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingRootCoordinateNashDefect reward
        (packet.rayPaidAdapter index).sourceTail.1
        (packet.rayPaidAdapter index).sourceRoot packet.payer =
      quittingRootCoordinateNashDefect reward
        (packet.row index).payerAdapter.sourceTail.1
        (packet.row index).payerAdapter.sourceRoot packet.payer := by
  rw [packet.rayPaidAdapter_sourceTail_eq_reference,
    packet.rayPaidAdapter_sourceRoot_eq,
    packet.rowPayerAdapter_sourceTail_eq_reference,
    packet.rowPayerAdapter_sourceRoot_eq]

theorem rayPaidAdapter_defect_floor
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      quittingRootCoordinateNashDefect reward
        (packet.rayPaidAdapter index).sourceTail.1
        (packet.rayPaidAdapter index).sourceRoot packet.payer := by
  rw [packet.rayPaidAdapter_defect_eq_row]
  exact packet.payerDefect_floor index

/-- The conditional date-zero payer gain. -/
def rayPaidBaseGain
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) : ℝ :=
  (packet.rayPaidAdapter index).sourceToTargetGain

theorem rayPaidBaseGain_eq_defect
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    packet.rayPaidBaseGain index =
      quittingRootCoordinateNashDefect reward
        (packet.rayPaidAdapter index).sourceTail.1
        (packet.rayPaidAdapter index).sourceRoot packet.payer := by
  rw [rayPaidBaseGain,
    (packet.rayPaidAdapter index).sourceToTargetGain_eq_liveMass_mul_defect]
  simp [quittingLiveMass_zero]

theorem rayPaidBaseGain_floor
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      packet.rayPaidBaseGain index := by
  rw [packet.rayPaidBaseGain_eq_defect]
  exact packet.rayPaidAdapter_defect_floor index

/-- Apply the unchanged explicit common outer word to the payer's target
profile.  The maximal roots are not recomputed from that changed endpoint. -/
def rayPaidTargetProfile
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingMaximalCapSemanticPrefixProfile reward packet.raySource
    (packet.rayPaidAdapter index).targetProfile index

/-- The actual whole-profile payer gain after copying the common outer word. -/
def rayPaidGain
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) : ℝ :=
  quittingTerminalPayoff reward (packet.rayPaidTargetProfile index)
      packet.payer -
    quittingTerminalPayoff reward (packet.rayFamily.rayProfiles index)
      packet.payer

theorem rayPaidGain_eq_survival_mul
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    packet.rayPaidGain index =
      quittingMaximalCapSemanticPrefixSurvival reward packet.raySource index *
        packet.rayPaidBaseGain index := by
  unfold rayPaidGain rayPaidTargetProfile
  simpa only [QuittingCommonSemanticMarkedBaseFamily.rayProfiles,
    rayFamily, rayPaidBaseGain] using
    (quittingTerminalPayoffGain_maximalCapSemanticPrefixProfile_eq reward
      packet.raySource (packet.rayPaidAdapter index).targetProfile
      (packet.rayBaseProfile index) index packet.payer
      (packet.rayPaidAdapter index).sourceToTargetGain rfl)

theorem rayResolution_mul_minimumDebt_div_three_le_rayPaidGain
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    packet.rayResolution *
          quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      packet.rayPaidGain index := by
  rw [packet.rayPaidGain_eq_survival_mul]
  have hsurvival :=
    minimumDebt_div_sourceDebt_le_maximalCapSemanticPrefixSurvival reward
      source.point.1 packet.raySource source.minimum source.minimumDebt_pos
      packet.raySource_mem index
  have hfloor := packet.rayPaidBaseGain_floor index
  have hdebt : 0 ≤ quittingTerminalSemanticDebtSum source.point.1 / 3 :=
    div_nonneg source.minimumDebt_pos.le (by norm_num)
  have hsurvivalNonneg : 0 ≤
      quittingMaximalCapSemanticPrefixSurvival reward packet.raySource index :=
    quittingMaximalCapSemanticPrefixSurvival_nonneg reward
      packet.raySource index
  have hmul := mul_le_mul hsurvival hfloor hdebt hsurvivalNonneg
  unfold rayResolution
  calc
    quittingTerminalSemanticDebtSum source.point.1 /
            quittingTerminalSemanticDebtSum packet.raySource *
          quittingTerminalSemanticDebtSum source.point.1 / 3 =
        (quittingTerminalSemanticDebtSum source.point.1 /
            quittingTerminalSemanticDebtSum packet.raySource) *
          (quittingTerminalSemanticDebtSum source.point.1 / 3) := by ring
    _ ≤ _ := hmul

/-- The fixed semantic-ray limit attached to this forced-pair source. -/
def rayLimit
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) : ℝ :=
  quittingMaximalCapSemanticPrefixDebtLimit reward packet.raySource

theorem minimumDebt_le_rayLimit
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    quittingTerminalSemanticDebtSum source.point.1 ≤ packet.rayLimit :=
  minimumDebt_le_quittingMaximalCapSemanticPrefixDebtLimit reward
    source.point.1 packet.raySource source.minimum packet.raySource_mem

/-- The whole diagonal source debt converges to the retained ray limit. -/
theorem rayProfiles_wholeDebt_tendsto
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Tendsto (fun index ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (packet.rayFamily.rayProfiles index))) atTop (nhds packet.rayLimit) := by
  simpa only [rayLimit, packet.rayFamily.rayProfiles_wholeDebt_eq] using
    quittingMaximalCapSemanticPrefixDebt_tendsto_limit reward source.point.1
      packet.raySource source.minimum packet.raySource_mem
        packet.raySourceDebt_pos.le

theorem rayProfiles_stageMass_eq_survival
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingStageCoalitionMass reward (packet.rayFamily.rayProfiles index)
        index packet.rayTerminal =
      quittingMaximalCapSemanticPrefixSurvival reward packet.raySource index :=
  packet.rayFamily.rayProfiles_stageMass_eq_survival index

theorem rayProfiles_postMarkSpine_eq_reference
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingAllContinueProfileSpine reward
        (packet.rayFamily.rayProfiles index) (index + 1) =
      packet.base.referenceProfile (packet.subsequence index) :=
  packet.rayFamily.rayProfiles_postMarkSpine_eq_tail index

/-- The bundled probability law whose real coordinates are the complete
terminal-outcome masses of the pure-pair base profile. -/
def rayBaseOutcomeLaw
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    PMF (QuittingTerminalOutcome (Fin 4)) :=
  (Math.ProbabilityMassFunction.stdSimplexEquiv
    (α := QuittingTerminalOutcome (Fin 4))).symm
      ⟨quittingTerminalOutcomeMass reward (packet.rayBaseProfile index),
        quittingTerminalOutcomeMass_mem_stdSimplex reward
          (packet.rayBaseProfile index)⟩

theorem rayBaseOutcomeLaw_apply_toReal
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ)
    (outcome : QuittingTerminalOutcome (Fin 4)) :
    (packet.rayBaseOutcomeLaw index outcome).toReal =
      quittingTerminalOutcomeMass reward (packet.rayBaseProfile index)
        outcome := by
  simp [rayBaseOutcomeLaw,
    Math.ProbabilityMassFunction.stdSimplexEquiv_symm_apply]
  rfl

/-- The complete outcome law of the pure pair is the point mass at its
displayed terminal; the counterfactual continuation contributes no mass. -/
theorem rayBaseOutcomeLaw_eq_pure
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    packet.rayBaseOutcomeLaw index = PMF.pure (some packet.rayTerminal) := by
  have hselectedReal :
      (packet.rayBaseOutcomeLaw index (some packet.rayTerminal)).toReal = 1 := by
    rw [packet.rayBaseOutcomeLaw_apply_toReal]
    rw [rayBaseProfile, quittingTerminalOutcomeMass_rootThenContinuation]
    rw [stationaryContinueMass_pureSetRoot_of_nonempty
      packet.rayTerminal.property]
    simp only [zero_mul, add_zero]
    have hstage := packet.rayBaseProfile_stageMass_eq_one index
    rw [rayBaseProfile,
      quittingStageCoalitionMass_rootThenContinuation_zero] at hstage
    exact hstage
  have hselected :
      packet.rayBaseOutcomeLaw index (some packet.rayTerminal) = 1 :=
    (ENNReal.toReal_eq_one_iff _).1 hselectedReal
  have hsupport :=
    (packet.rayBaseOutcomeLaw index).apply_eq_one_iff
      (some packet.rayTerminal) |>.1 hselected
  ext outcome
  by_cases houtcome : outcome = some packet.rayTerminal
  · subst outcome
    simp [hselected]
  · have hzero : packet.rayBaseOutcomeLaw index outcome = 0 :=
      (packet.rayBaseOutcomeLaw index).apply_eq_zero_iff outcome |>.2 (by
        rw [hsupport]
        simpa)
    simp [hzero, houtcome]

/-- Real-coordinate form of the exact pure point-mass outcome law. -/
theorem rayBaseProfile_outcomeMass_eq_pointMass
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalOutcomeMass reward (packet.rayBaseProfile index) =
      fun outcome ↦ ((PMF.pure (some packet.rayTerminal)) outcome).toReal := by
  funext outcome
  rw [← packet.rayBaseOutcomeLaw_apply_toReal index outcome,
    packet.rayBaseOutcomeLaw_eq_pure]

/-- The selected-terminal coordinate is the corresponding point-mass
corollary. -/
theorem rayBaseProfile_terminalMass_eq_one
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalOutcomeMass reward (packet.rayBaseProfile index)
      (some packet.rayTerminal) = 1 := by
  have hmass := congrFun
    (packet.rayBaseProfile_outcomeMass_eq_pointMass index)
    (some packet.rayTerminal)
  simpa using hmass

/-- The same sure pair has zero Never mass, independently of its
counterfactual reference tail. -/
theorem rayBaseProfile_neverMass_eq_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalOutcomeMass reward (packet.rayBaseProfile index) none =
      0 := by
  have hmass := congrFun
    (packet.rayBaseProfile_outcomeMass_eq_pointMass index) none
  simpa using hmass

/-- Marked pair mass and payer gain density have the same exact ray limit.
The denominator is the actual date-zero payer gain at that row, which is
uniformly positive; no constancy of the behavioral reference tails is used. -/
theorem rayMarkedMass_and_paidGainDensity_tendsto
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Tendsto (fun index ↦ quittingStageCoalitionMass reward
        (packet.rayFamily.rayProfiles index) index packet.rayTerminal) atTop
        (nhds (packet.rayLimit /
          quittingTerminalSemanticDebtSum packet.raySource)) ∧
      Tendsto (fun index ↦
        packet.rayPaidGain index / packet.rayPaidBaseGain index) atTop
        (nhds (packet.rayLimit /
          quittingTerminalSemanticDebtSum packet.raySource)) := by
  have hsurvival :=
    quittingMaximalCapSemanticPrefixSurvival_tendsto_limit_div reward
      source.point.1 packet.raySource source.minimum source.minimumDebt_pos
        packet.raySource_mem
  constructor
  · simpa only [rayLimit, packet.rayProfiles_stageMass_eq_survival] using
      hsurvival
  · have heq : (fun index ↦
        packet.rayPaidGain index / packet.rayPaidBaseGain index) =
        quittingMaximalCapSemanticPrefixSurvival reward packet.raySource := by
      funext index
      rw [packet.rayPaidGain_eq_survival_mul]
      have hgainPos : 0 < packet.rayPaidBaseGain index :=
        (div_pos source.minimumDebt_pos (by norm_num)).trans_le
          (packet.rayPaidBaseGain_floor index)
      exact mul_div_cancel_right₀ _ hgainPos.ne'
    rw [heq]
    simpa only [rayLimit] using hsurvival

theorem ray_positiveDebtSupport_eq
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (Finset.univ.filter fun who => 0 < quittingTerminalSemanticDebt
        (quittingMaximalCapSemanticPrefixOrbit reward packet.raySource index)
          who) =
      Finset.univ.filter fun who =>
        0 < quittingTerminalSemanticDebt packet.raySource who :=
  quittingMaximalCapSemanticPrefixOrbit_positiveDebtSupport_eq reward
    source.point.1 packet.raySource source.minimum source.minimumDebt_pos
      packet.raySource_mem index

theorem ray_normalizedDebt_eq
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) (who : Fin 4) :
    quittingTerminalSemanticDebt
          (quittingMaximalCapSemanticPrefixOrbit reward packet.raySource index)
          who /
        quittingTerminalSemanticDebtSum
          (quittingMaximalCapSemanticPrefixOrbit reward packet.raySource index) =
      quittingTerminalSemanticDebt packet.raySource who /
        quittingTerminalSemanticDebtSum packet.raySource :=
  quittingTerminalSemanticDebt_normalized_maximalCapSemanticPrefixOrbit_eq
    reward source.point.1 packet.raySource source.minimum
      source.minimumDebt_pos packet.raySource_mem index who

/-- Equality-arm data: the actual moving packet has resolution `D_*/D_0`,
the row-wise compiler is eventually in its executable transfer arm, and its
compact fixed-role consumer supplies a limit chord. -/
structure MaximalPrefixRayMinimumReturn
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  limit_eq : packet.rayLimit =
    quittingTerminalSemanticDebtSum source.point.1
  eventuallyTransfer : ∀ᶠ rank in atTop,
    Nonempty (ConcentratedCollisionFourRole.packetTransfer source.point.1
      (packet.rayFamily.returnPacket source.minimum source.minimumDebt_pos
        packet.raySource_mem) rank)
  limitChord : ∃ mover recipient,
    Nonempty (ConcentratedCollisionFourRole.ThreeRoleLimitChord reward
      source.point.1 returnSource.forcedOwner mover recipient
      (packet.rayFamily.returnPacket source.minimum source.minimumDebt_pos
        packet.raySource_mem).resolution)

/-- Strict-arm data.  This is a quantitative ray stall and its retained-law
support-entry alternative, not a completion consumer. -/
structure MaximalPrefixRayStall
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  stall : QuittingMaximalCapSemanticPrefixRayStall reward source.point.1
    packet.raySource
  retainedLaw : QuittingMaximalCapSemanticPrefixRetainedLaw reward
    packet.raySource (packet.rayBaseProfile 0) 0 packet.rayTerminal

/-- Exact source-facing dichotomy for the one fixed cofinal forced-pair
packet.  No chronology, outsider, pair, or payer is reselected. -/
theorem nonempty_maximalPrefixRayMinimumReturn_or_stall
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Nonempty (MaximalPrefixRayMinimumReturn packet) ∨
      Nonempty (MaximalPrefixRayStall packet) := by
  rcases packet.minimumDebt_le_rayLimit.eq_or_lt with hreturn | hstrict
  · left
    have hlimit : packet.rayLimit =
        quittingTerminalSemanticDebtSum source.point.1 := hreturn.symm
    exact ⟨{
      limit_eq := hlimit
      eventuallyTransfer :=
        packet.rayFamily.eventually_threeRoleTransfer_of_return
          source.semantic_mem source.minimum source.minimumDebt_pos
          packet.raySource_mem (by
            rw [rayTerminal, packet.movingTerminal_card]
            norm_num) hlimit
      limitChord :=
        packet.rayFamily.nonempty_threeRoleLimitChord_of_return
          source.semantic_mem source.minimum source.minimumDebt_pos
          packet.raySource_mem (by
            rw [rayTerminal, packet.movingTerminal_card]
            norm_num) hlimit
    }⟩
  · right
    let stall : QuittingMaximalCapSemanticPrefixRayStall reward source.point.1
        packet.raySource := {
      minimum_mem := source.semantic_mem
      source_mem := packet.raySource_mem
      minimum_global := source.minimum
      minimum_pos := source.minimumDebt_pos
      strict := hstrict
    }
    have hstage : 0 < quittingStageCoalitionMass reward
        (packet.rayBaseProfile 0) 0 packet.rayTerminal := by
      rw [packet.rayBaseProfile_stageMass_eq_one]
      norm_num
    obtain ⟨retainedLaw⟩ :=
      nonempty_quittingMaximalCapSemanticPrefixRetainedLaw reward
        source.point.1 packet.raySource (packet.rayBaseProfile 0)
        (packet.rayBaseProfile_semantic_eq 0) 0 packet.rayTerminal
        source.minimum source.minimumDebt_pos packet.raySource_mem hstage
    exact ⟨{
      stall := stall
      retainedLaw := retainedLaw
    }⟩

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
