/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.SameStageEndpointMonodromy
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionTemporalSplit

/-!
# Concentrated packet from one positive stage atom

One positive actual stage atom can be made recurrent in the formal packet
sense by changing one selected player's marked marginal to its exact best
endpoint and repeating the resulting literal profile.  The source atom is
routed without loss and the selected coordinate's marked local Nash defect is
exactly zero.

The routed terminal can be either the source coalition with the selected
player erased or with that player inserted.  It is not asserted to remain a
singleton.  This construction makes no full-root Nash, behavioral-debt,
near-minimum, source-chronology recurrence, or downstream-consumer claim.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- Actual source data sufficient to route one positive stage atom to a
literal best-endpoint profile and then repeat it as a concentrated packet. -/
structure QuittingStageAtomConcentratedPacketAdapter
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (sourceProfile : (quittingGame reward).BehaviorProfile)
    (sourceTerminal : {S : Finset iota // S.Nonempty})
    (owner : iota) (stage : ℕ) (resolution : ℝ) where
  sourceTerminal_ne_owner : sourceTerminal.val ≠ {owner}
  resolution_pos : 0 < resolution
  resolution_le_sourceStageMass : resolution ≤
    quittingStageCoalitionMass reward sourceProfile stage sourceTerminal

namespace QuittingStageAtomConcentratedPacketAdapter

variable
  {sourceProfile : (quittingGame reward).BehaviorProfile}
  {sourceTerminal : {S : Finset iota // S.Nonempty}}
  {owner : iota} {stage : ℕ} {resolution : ℝ}

/-- The actual shifted semantic tail used for the endpoint comparison. -/
def sourceTail
    (_adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) : QuittingTerminalSemanticPair iota :=
  quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward sourceProfile (stage + 1))

/-- The actual live root at the selected source date. -/
def sourceRoot
    (_adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) : iota → PMF Bool :=
  quittingProfileLiveRoot reward sourceProfile stage

/-- The exact better endpoint for the packet owner at the displayed source
root and shifted tail. -/
def action
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) : Bool :=
  quittingRootBestEndpointAction reward adapter.sourceTail.1 adapter.sourceRoot owner

/-- The literal target changes only the packet owner and only at the selected
date. -/
def targetProfile
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralOneDateProfile reward sourceProfile owner stage adapter.action

/-- The source coalition routed across the selected Boolean endpoint. -/
def routedCoalition
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) : Finset iota :=
  quittingPureEndpointRoutedCoalition sourceTerminal.val owner adapter.action

/-- The routed coalition is nonempty under the adapter's uniform assumption
`sourceTerminal.val ≠ {owner}`.  In Quit mode insertion would remain nonempty
even for the excluded singleton; this generic API intentionally keeps the
action-independent assumption rather than generalizing that safe subcase. -/
theorem routedCoalition_nonempty
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    adapter.routedCoalition.Nonempty := by
  cases haction : adapter.action with
  | false =>
      rw [routedCoalition, haction,
        quittingPureEndpointRoutedCoalition_false]
      rw [Finset.nonempty_iff_ne_empty]
      intro herase
      rcases (Finset.erase_eq_empty_iff sourceTerminal.val owner).mp herase with
        hempty | hsingleton
      · exact sourceTerminal.property.ne_empty hempty
      · exact adapter.sourceTerminal_ne_owner hsingleton
  | true =>
      rw [routedCoalition, haction,
        quittingPureEndpointRoutedCoalition_true]
      exact ⟨owner, Finset.mem_insert_self owner sourceTerminal.val⟩

/-- The fixed nonempty terminal carried by the target packet. -/
def routedTerminal
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    {S : Finset iota // S.Nonempty} :=
  ⟨adapter.routedCoalition, adapter.routedCoalition_nonempty⟩

@[simp] theorem routedTerminal_val
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    adapter.routedTerminal.val = adapter.routedCoalition := rfl

/-- The routed terminal is exactly the erase mode or the insert mode selected
by the best endpoint.  No cardinality conclusion is included. -/
theorem routedTerminal_erase_or_insert
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    (adapter.action = false ∧
        adapter.routedTerminal.val = sourceTerminal.val.erase owner) ∨
      (adapter.action = true ∧
        adapter.routedTerminal.val = insert owner sourceTerminal.val) := by
  cases haction : adapter.action with
  | false =>
      left
      exact ⟨rfl, by
        simp [routedTerminal, routedCoalition, haction]⟩
  | true =>
      right
      exact ⟨rfl, by
        simp [routedTerminal, routedCoalition, haction]⟩

/-- The target is definitionally the advertised literal one-date update. -/
theorem targetProfile_eq_literalOneDateProfile
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    adapter.targetProfile = quittingLiteralOneDateProfile reward sourceProfile
      owner stage adapter.action := rfl

/-- Every opponent's complete behavioral strategy is copied literally. -/
theorem targetProfile_opponent_eq
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution)
    (other : iota) (hother : other ≠ owner) :
    adapter.targetProfile other = sourceProfile other := by
  simp [targetProfile, quittingLiteralOneDateProfile, hother]

/-- At every date other than the selected one, every player's complete
behavior rule is copied literally, including off-live histories. -/
theorem targetProfile_at_of_ne
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution)
    (time : ℕ) (htime : time ≠ stage) :
    ∀ player, adapter.targetProfile player time = sourceProfile player time := by
  intro player
  by_cases hplayer : player = owner
  · subst player
    simp only [targetProfile, quittingLiteralOneDateProfile,
      Function.update_self]
    exact quittingLiteralOneDateOverride_of_ne
      (sourceProfile owner) stage time adapter.action htime
  · exact congrFun (adapter.targetProfile_opponent_eq player hplayer) time

/-- Every live root away from the selected date is unchanged. -/
theorem targetProfile_liveRoot_eq_of_ne
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution)
    (time : ℕ) (htime : time ≠ stage) :
    quittingProfileLiveRoot reward adapter.targetProfile time =
      quittingProfileLiveRoot reward sourceProfile time := by
  unfold quittingProfileLiveRoot
  funext player
  exact congrFun (adapter.targetProfile_at_of_ne time htime player)
    (quittingLiveHist reward time)

/-- The complete post-date live-root tail is unchanged. -/
theorem targetProfile_postDate_liveRoot_eq
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) (offset : ℕ) :
    quittingProfileLiveRoot reward adapter.targetProfile
        (stage + 1 + offset) =
      quittingProfileLiveRoot reward sourceProfile (stage + 1 + offset) := by
  exact quittingProfileLiveRoot_literalOneDateProfile_tail_eq
    sourceProfile owner stage offset adapter.action

/-- The target's shifted semantic tail, kept as a named actual-data
accessor. -/
def targetTail
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) : QuittingTerminalSemanticPair iota :=
  quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward adapter.targetProfile (stage + 1))

/-- The prescribed payoff and cap in the complete semantic tail are unchanged
strictly after the selected date. -/
theorem targetTail_eq_sourceTail
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    adapter.targetTail = adapter.sourceTail := by
  apply quittingTerminalSemanticPair_eq_of_liveRoot_eq
  funext offset player
  change (quittingAllContinueProfileSpine reward adapter.targetProfile
      (stage + 1)) player offset (quittingLiveHist reward offset) =
    (quittingAllContinueProfileSpine reward sourceProfile
      (stage + 1)) player offset (quittingLiveHist reward offset)
  rw [quittingAllContinueProfileSpine_apply_liveHist,
    quittingAllContinueProfileSpine_apply_liveHist]
  exact congrFun (adapter.targetProfile_postDate_liveRoot_eq offset) player

/-- Updating the packet owner's own strategy leaves that owner's unrestricted
best-response cap unchanged.  This is not a cap-attainment or Nash claim. -/
theorem targetProfile_ownerCap_eq
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    quittingContinuationBestResponseValue reward adapter.targetProfile owner =
      quittingContinuationBestResponseValue reward sourceProfile owner :=
  quittingContinuationBestResponseValue_literalOneDateProfile_self_eq
    reward sourceProfile owner stage adapter.action

/-- The probability of reaching the selected date is unchanged. -/
theorem target_liveMass_eq_source
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    quittingLiveMass reward adapter.targetProfile stage =
      quittingLiveMass reward sourceProfile stage :=
  quittingLiveMass_literalOneDateProfile_eq
    reward sourceProfile owner stage adapter.action

/-- The target marked root is the selected pure-coordinate update. -/
theorem target_markedRoot_eq
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    quittingProfileLiveRoot reward adapter.targetProfile stage =
      Function.update adapter.sourceRoot owner (PMF.pure adapter.action) :=
  quittingProfileLiveRoot_literalOneDateProfile
    reward sourceProfile owner stage adapter.action

/-- The source atom routes to the target terminal without losing
unconditional stage mass. -/
theorem sourceStageMass_le_targetStageMass
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    quittingStageCoalitionMass reward sourceProfile stage sourceTerminal ≤
      quittingStageCoalitionMass reward adapter.targetProfile stage
        adapter.routedTerminal := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    adapter.target_liveMass_eq_source, adapter.target_markedRoot_eq]
  exact mul_le_mul_of_nonneg_left
    (quittingRootCoalitionMass_le_pureEndpointRouted
      adapter.sourceRoot sourceTerminal.val owner adapter.action)
    (quittingLiveMass_nonneg reward sourceProfile stage)

/-- The routed target retains the requested positive resolution. -/
theorem resolution_le_targetStageMass
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    resolution ≤ quittingStageCoalitionMass reward adapter.targetProfile stage
      adapter.routedTerminal :=
  adapter.resolution_le_sourceStageMass.trans
    adapter.sourceStageMass_le_targetStageMass

/-- The routed target stage atom is genuinely positive. -/
theorem targetStageMass_pos
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    0 < quittingStageCoalitionMass reward adapter.targetProfile stage
      adapter.routedTerminal :=
  adapter.resolution_pos.trans_le adapter.resolution_le_targetStageMass

/-- The actual payoff gain made by the packet owner's literal best-endpoint
update.  This is a complete behavioral-profile payoff difference, not only a
one-row or stationary comparison. -/
def sourceToTargetGain
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) : ℝ :=
  quittingTerminalPayoff reward adapter.targetProfile owner -
    quittingTerminalPayoff reward sourceProfile owner

/-- The literal source-to-target gain is exactly reached live mass times the
owner's coordinate Nash defect at the actual source row and shifted tail. -/
theorem sourceToTargetGain_eq_liveMass_mul_defect
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    adapter.sourceToTargetGain =
      quittingLiveMass reward sourceProfile stage *
        quittingRootCoordinateNashDefect reward adapter.sourceTail.1
          adapter.sourceRoot owner := by
  simpa only [sourceToTargetGain, targetProfile, action, sourceTail, sourceRoot]
    using quittingTerminalPayoff_literalOneDateProfile_bestEndpoint_gain_eq
      reward sourceProfile owner stage

/-- Monotone lower-bound form of the exact gain identity.  The candidate
defect floor is required to be nonnegative; the actual live mass is
nonnegative by construction. -/
theorem sourceToTargetGain_lowerBound
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution)
    (liveLower defectLower : ℝ)
    (hlive : liveLower ≤ quittingLiveMass reward sourceProfile stage)
    (hdefectNonneg : 0 ≤ defectLower)
    (hdefect : defectLower ≤
      quittingRootCoordinateNashDefect reward adapter.sourceTail.1
        adapter.sourceRoot owner) :
    liveLower * defectLower ≤ adapter.sourceToTargetGain := by
  rw [adapter.sourceToTargetGain_eq_liveMass_mul_defect]
  exact mul_le_mul hlive hdefect hdefectNonneg
    (quittingLiveMass_nonneg reward sourceProfile stage)

/-- Updating only the packet owner's strategy leaves that owner's unrestricted
cap fixed, so the actual payoff gain is subtracted exactly from its terminal
semantic debt. -/
theorem targetOwnerDebt_eq_sourceOwnerDebt_sub_gain
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward adapter.targetProfile) owner =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward sourceProfile) owner -
        adapter.sourceToTargetGain := by
  simpa only [targetProfile, action, sourceTail, sourceRoot,
    sourceToTargetGain] using
      quittingTerminalSemanticDebt_literalOneDateProfile_bestEndpoint_eq_sub_gain
        reward sourceProfile owner stage

/-- The packet owner's marked local coordinate defect is exactly zero against
the unchanged actual post-date tail. -/
theorem ownerMarkedDefect_eq_zero
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    quittingRootCoordinateNashDefect reward adapter.targetTail.1
      (quittingProfileLiveRoot reward adapter.targetProfile stage) owner = 0 := by
  rw [adapter.targetTail_eq_sourceTail, adapter.target_markedRoot_eq]
  exact quittingRootCoordinateNashDefect_update_bestEndpoint_eq_zero
    reward adapter.sourceTail.1 adapter.sourceRoot owner

/-- The constant actual profile family used by the packet. -/
def profiles
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    ℕ → (quittingGame reward).BehaviorProfile :=
  fun _rank ↦ adapter.targetProfile

/-- The fixed cutoff immediately after the selected date. -/
def cutoff
    (_adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) : ℕ → ℕ :=
  fun _rank ↦ stage + 1

/-- The fixed marked date in the repeated target family. -/
def mark
    (_adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) : ℕ → ℕ :=
  fun _rank ↦ stage

/-- The identity packet subsequence. -/
def subseq
    (_adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) : ℕ → ℕ :=
  id

/-- A canonical positive scale tending to zero, returned explicitly for the
existing concentrated-packet consumers. -/
def scale
    (_adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) : ℕ → ℝ :=
  fun rank ↦ 1 / ((rank : ℝ) + 1)

theorem scale_pos
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) (rank : ℕ) :
    0 < adapter.scale rank := by
  simp only [scale]
  positivity

theorem scale_tendsto_zero
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    Tendsto adapter.scale atTop (nhds 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The packet's normalized marked owner-defect expression for an arbitrary
scale.  No positivity is needed to define it. -/
def normalizedMarkedOwnerDefect
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution)
    (scale : ℕ → ℝ) (rank : ℕ) : ℝ :=
  quittingLiveMass reward (adapter.profiles (adapter.subseq rank))
      (adapter.mark rank) *
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (adapter.profiles (adapter.subseq rank))
          (adapter.mark rank + 1))).1
      (quittingProfileLiveRoot reward
        (adapter.profiles (adapter.subseq rank))
        (adapter.mark rank)) owner /
    scale (adapter.subseq rank)

/-- Exact best-endpoint purification makes the normalized marked owner defect
zero at every rank for every scale, including scales not bounded away from
zero. -/
theorem normalizedMarkedOwnerDefect_eq_zero
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution)
    (scale : ℕ → ℝ) (rank : ℕ) :
    adapter.normalizedMarkedOwnerDefect scale rank = 0 := by
  simp only [normalizedMarkedOwnerDefect, profiles, subseq, id_eq, mark]
  change quittingLiveMass reward adapter.targetProfile stage *
      quittingRootCoordinateNashDefect reward adapter.targetTail.1
        (quittingProfileLiveRoot reward adapter.targetProfile stage) owner /
      scale rank = 0
  rw [adapter.ownerMarkedDefect_eq_zero, mul_zero, zero_div]

/-- Function-level form of the exact normalized-defect identity. -/
theorem normalizedMarkedOwnerDefect_identically_zero
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution)
    (scale : ℕ → ℝ) :
    adapter.normalizedMarkedOwnerDefect scale = fun _rank ↦ 0 := by
  funext rank
  exact adapter.normalizedMarkedOwnerDefect_eq_zero scale rank

/-- The normalized marked owner defect therefore tends to zero for every
scale; positivity and vanishing of the scale are consumer-side data. -/
theorem normalizedMarkedOwnerDefect_tendsto_zero
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution)
    (scale : ℕ → ℝ) :
    Tendsto (adapter.normalizedMarkedOwnerDefect scale) atTop (nhds 0) := by
  rw [adapter.normalizedMarkedOwnerDefect_identically_zero scale]
  exact tendsto_const_nhds

/-- Constant repetition of the literal target is an actual concentrated
reprojection packet for any supplied positive scale tending to zero.  The
normalized numerator is in fact exactly zero, but the scale hypotheses are
retained in this constructor because existing consumers require them. -/
def packetWithScale
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution)
    (scale : ℕ → ℝ) (_scale_pos : ∀ rank, 0 < scale rank)
    (_scale_tendsto_zero : Tendsto scale atTop (nhds 0)) :
    QuittingReprojectionConcentratedPacket reward adapter.profiles owner
      adapter.routedTerminal adapter.cutoff scale where
  resolution := resolution
  resolution_pos := adapter.resolution_pos
  subseq := adapter.subseq
  subseq_strictMono := strictMono_id
  mark := adapter.mark
  mark_lt := by
    intro rank
    simp [mark, cutoff]
  stageMass := by
    intro rank
    simpa [profiles, mark, subseq] using adapter.resolution_le_targetStageMass
  semanticPrefix := by
    intro rank
    simpa [profiles, mark, subseq] using
      (positive_stageCoalitionMass_has_semanticPrefixIncidence
        reward adapter.targetProfile stage adapter.routedTerminal
          adapter.targetStageMass_pos)
  defect_tendsto := adapter.normalizedMarkedOwnerDefect_tendsto_zero scale

/-- The canonical `1 / (rank + 1)` packet, retained as a thin wrapper around
the arbitrary-scale constructor.  Its recurrence is in the constructed
profile index; no recurrence of the source chronology is asserted. -/
def packet
    (adapter : QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :
    QuittingReprojectionConcentratedPacket reward adapter.profiles owner
      adapter.routedTerminal adapter.cutoff adapter.scale :=
  adapter.packetWithScale adapter.scale adapter.scale_pos
    adapter.scale_tendsto_zero

/-- Construct the dependent adapter directly from one source atom and the
three exact hypotheses; no packet or adapter is supplied as input. -/
theorem nonempty_of_stageMass
    (sourceProfile : (quittingGame reward).BehaviorProfile)
    (sourceTerminal : {S : Finset iota // S.Nonempty})
    (owner : iota) (stage : ℕ) (resolution : ℝ)
    (hterminal : sourceTerminal.val ≠ {owner})
    (hresolution : 0 < resolution)
    (hmass : resolution ≤
      quittingStageCoalitionMass reward sourceProfile stage sourceTerminal) :
    Nonempty (QuittingStageAtomConcentratedPacketAdapter reward sourceProfile
      sourceTerminal owner stage resolution) :=
  ⟨{
    sourceTerminal_ne_owner := hterminal
    resolution_pos := hresolution
    resolution_le_sourceStageMass := hmass
  }⟩

end QuittingStageAtomConcentratedPacketAdapter

end GameTheory
