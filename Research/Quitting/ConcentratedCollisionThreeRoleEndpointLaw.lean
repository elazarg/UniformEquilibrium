/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.NormalizedPassportMinimumReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLiveWeightedCollisionTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPureTimeRectangleDisintegration
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio

/-!
# Actual endpoint laws for recurrent three-role transfers

The public three-role chord remembers only two semantic limits.  This module
retains the actual recurrent packet and a common subsequence of its source
profiles and pure endpoint profiles, including the endpoint terminal law and
one routed terminal atom of uniformly positive mass.

The endpoint-law object projects to the old chord.  It is constructed from the
actual packet and frequent role witnesses, not from a supplied public chord.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A three-role compact limit retaining the actual endpoint terminal law and
one fixed routed terminal. -/
structure ConcentratedCollisionThreeRoleEndpointLaw
    (minimum : QuittingTerminalSemanticPair ι)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : ι} {marked : {S : Finset ι // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale)
    (mover recipient : ι) where
  endpointAction : Bool
  routedTerminal : {S : Finset ι // S.Nonempty}
  ranks : ℕ → ℕ
  ranks_strictMono : StrictMono ranks
  transfer : ∀ rank,
    ConcentratedCollisionFourRole.packetTransfer minimum packet (ranks rank)
  transfer_mover_eq : ∀ rank, (transfer rank).mover = mover
  transfer_recipient_eq : ∀ rank, (transfer rank).recipient = recipient
  endpointAction_eq : ∀ rank,
    ConcentratedCollisionFourRole.action reward
      (ConcentratedCollisionFourRole.packetProfile packet (ranks rank))
      (packet.mark (ranks rank)) mover = endpointAction
  routedTerminal_eq : routedTerminal.val =
    quittingPureEndpointRoutedCoalition marked.val mover endpointAction
  sourceLimit : QuittingTerminalSemanticPair ι
  targetPoint : QuittingTerminalSemanticLawPoint ι
  source_mem : sourceLimit ∈ quittingTerminalSemanticCarrier reward
  target_mem : targetPoint ∈ quittingTerminalSemanticLawCarrier reward
  source_tendsto : Tendsto (fun rank ↦
    ConcentratedCollisionFourRole.source reward
      (ConcentratedCollisionFourRole.packetProfile packet (ranks rank)))
    atTop (nhds sourceLimit)
  target_joint_tendsto : Tendsto (fun rank ↦
    let profile := ConcentratedCollisionFourRole.packetProfile packet
      (ranks rank)
    let target := ConcentratedCollisionFourRole.targetProfile reward profile
      (packet.mark (ranks rank)) mover
    (quittingTerminalSemanticPair reward target,
      quittingTerminalOutcomeMass reward target))
    atTop (nhds targetPoint)
  terminalMass_floor : packet.resolution ≤
    targetPoint.2 (some routedTerminal)
  mover_ne_owner : mover ≠ owner
  recipient_ne_mover : recipient ≠ mover
  source_on_minimum_fiber :
    quittingTerminalSemanticDebtSum sourceLimit =
      quittingTerminalSemanticDebtSum minimum
  target_above_minimum : quittingTerminalSemanticDebtSum minimum ≤
    quittingTerminalSemanticDebtSum targetPoint.1
  mover_drop : quittingTerminalSemanticDebt targetPoint.1 mover ≤
    quittingTerminalSemanticDebt sourceLimit mover -
      packet.resolution ^ 2 * quittingTerminalSemanticDebtSum minimum /
        (2 * (Fintype.card ι : ℝ))
  recipient_rise :
    packet.resolution ^ 2 * quittingTerminalSemanticDebtSum minimum /
          (4 * (Fintype.card ι : ℝ) ^ 2) ≤
      quittingTerminalSemanticDebtChange sourceLimit targetPoint.1 recipient
  target_fiber_or_ascent :
    quittingTerminalSemanticDebtSum targetPoint.1 =
        quittingTerminalSemanticDebtSum minimum ∨
      quittingTerminalSemanticDebtSum minimum <
        quittingTerminalSemanticDebtSum targetPoint.1

namespace ConcentratedCollisionThreeRoleEndpointLaw

variable
  {minimum : QuittingTerminalSemanticPair ι}
  {profiles : ℕ → (quittingGame reward).BehaviorProfile}
  {owner : ι} {marked : {S : Finset ι // S.Nonempty}}
  {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
  {packet : QuittingReprojectionConcentratedPacket
    reward profiles owner marked cutoff scale}
  {mover recipient : ι}

/-- Forgetting the actual profiles and endpoint law gives the public
three-role chord with exactly the same semantic limits and bounds. -/
def toThreeRoleLimitChord
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw minimum packet mover
      recipient) :
    ConcentratedCollisionFourRole.ThreeRoleLimitChord reward minimum owner
      mover recipient packet.resolution where
  sourceLimit := endpoint.sourceLimit
  targetLimit := endpoint.targetPoint.1
  source_mem := endpoint.source_mem
  target_mem := terminalSemanticLawCarrier_fst_mem_carrier
    endpoint.targetPoint endpoint.target_mem
  mover_ne_owner := endpoint.mover_ne_owner
  recipient_ne_mover := endpoint.recipient_ne_mover
  source_on_minimum_fiber := endpoint.source_on_minimum_fiber
  target_above_minimum := endpoint.target_above_minimum
  mover_drop := endpoint.mover_drop
  recipient_rise := endpoint.recipient_rise
  target_fiber_or_ascent := endpoint.target_fiber_or_ascent

omit [Nonempty ι] in
/-- The retained routed terminal has positive mass in the actual endpoint-law
limit. -/
theorem terminalMass_pos
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw minimum packet mover
      recipient) :
    0 < endpoint.targetPoint.2 (some endpoint.routedTerminal) :=
  packet.resolution_pos.trans_le endpoint.terminalMass_floor

omit [Nonempty ι] in
/-- The packet resolution is a lower bound for the original marked stage
mass at every retained rank. -/
theorem resolution_le_sourceMarkedStageMass
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw minimum packet mover
      recipient) (rank : ℕ) :
    packet.resolution ≤
      quittingStageCoalitionMass reward
        (ConcentratedCollisionFourRole.packetProfile packet
          (endpoint.ranks rank))
        (packet.mark (endpoint.ranks rank)) marked :=
  packet.stageMass (endpoint.ranks rank)

omit [Nonempty ι] in
/-- Pure endpoint routing does not decrease the unconditional marked stage
mass at any retained rank.  Nonsingletonity is the same explicit hypothesis
used by the endpoint-law constructor. -/
theorem sourceMarkedStageMass_le_routedTargetStageMass
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw minimum packet mover
      recipient) (hcollision : 1 < marked.val.card) (rank : ℕ) :
    quittingStageCoalitionMass reward
        (ConcentratedCollisionFourRole.packetProfile packet
          (endpoint.ranks rank))
        (packet.mark (endpoint.ranks rank)) marked ≤
      quittingStageCoalitionMass reward
        (ConcentratedCollisionFourRole.targetProfile reward
          (ConcentratedCollisionFourRole.packetProfile packet
            (endpoint.ranks rank))
          (packet.mark (endpoint.ranks rank)) mover)
        (packet.mark (endpoint.ranks rank)) endpoint.routedTerminal := by
  obtain ⟨hrouted, hmass⟩ :=
    quittingStageCoalitionMass_le_stagePureEndpointRouted reward
      (ConcentratedCollisionFourRole.packetProfile packet
        (endpoint.ranks rank))
      mover (packet.mark (endpoint.ranks rank)) marked endpoint.endpointAction
        hcollision
  rw [ConcentratedCollisionFourRole.targetProfile,
    endpoint.endpointAction_eq rank]
  have hterminal :
      (⟨quittingPureEndpointRoutedCoalition marked.val mover
          endpoint.endpointAction, hrouted⟩ :
        {S : Finset ι // S.Nonempty}) = endpoint.routedTerminal := by
    exact Subtype.ext endpoint.routedTerminal_eq.symm
  simpa only [hterminal] using hmass

omit [Nonempty ι] in
/-- The routed target stage cylinder contributes to the target's complete
terminal law at the same retained routed terminal. -/
theorem routedTargetStageMass_le_terminalOutcomeMass
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw minimum packet mover
      recipient) (rank : ℕ) :
    quittingStageCoalitionMass reward
        (ConcentratedCollisionFourRole.targetProfile reward
          (ConcentratedCollisionFourRole.packetProfile packet
            (endpoint.ranks rank))
          (packet.mark (endpoint.ranks rank)) mover)
        (packet.mark (endpoint.ranks rank)) endpoint.routedTerminal ≤
      quittingTerminalOutcomeMass reward
        (ConcentratedCollisionFourRole.targetProfile reward
          (ConcentratedCollisionFourRole.packetProfile packet
            (endpoint.ranks rank))
          (packet.mark (endpoint.ranks rank)) mover)
        (some endpoint.routedTerminal) :=
  quittingStageCoalitionMass_le_terminalOutcomeMass reward _ _ _

omit [Nonempty ι] in
/-- Literal per-rank mass chain from packet resolution through the source
marked cylinder and routed target cylinder to the complete target law. -/
theorem perRank_mass_chain
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw minimum packet mover
      recipient) (hcollision : 1 < marked.val.card) (rank : ℕ) :
    let sourceProfile := ConcentratedCollisionFourRole.packetProfile packet
      (endpoint.ranks rank)
    let stage := packet.mark (endpoint.ranks rank)
    let targetProfile := ConcentratedCollisionFourRole.targetProfile reward
      sourceProfile stage mover
    packet.resolution ≤
        quittingStageCoalitionMass reward sourceProfile stage marked ∧
      quittingStageCoalitionMass reward sourceProfile stage marked ≤
          quittingStageCoalitionMass reward targetProfile stage
            endpoint.routedTerminal ∧
        quittingStageCoalitionMass reward targetProfile stage
            endpoint.routedTerminal ≤
          quittingTerminalOutcomeMass reward targetProfile
            (some endpoint.routedTerminal) := by
  exact ⟨endpoint.resolution_le_sourceMarkedStageMass rank,
    endpoint.sourceMarkedStageMass_le_routedTargetStageMass hcollision rank,
    endpoint.routedTargetStageMass_le_terminalOutcomeMass rank⟩

end ConcentratedCollisionThreeRoleEndpointLaw

namespace ConcentratedCollisionFourRole

/-- The actual recurrent packet and frequent fixed-role transfers admit a
common compact subsequence retaining the endpoint law and routed atom. -/
theorem nonempty_threeRoleEndpointLaw_of_frequently_packetTransferRoles
    (minimum : QuittingTerminalSemanticPair ι)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : ι} {marked : {S : Finset ι // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale)
    (mover recipient : ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < marked.val.card)
    (hsourceDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (source reward (packetProfile packet rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum)))
    (hroles : ∃ᶠ rank in atTop,
      packetTransferRoles minimum packet rank mover recipient) :
    Nonempty (ConcentratedCollisionThreeRoleEndpointLaw minimum packet mover
      recipient) := by
  let eps : ℕ → ℝ := fun rank ↦ packetEpsilon minimum packet rank
  have hepsZero : Tendsto eps atTop (nhds 0) := by
    have hsub := hsourceDebt.sub_const
      (quittingTerminalSemanticDebtSum minimum)
    simpa only [eps, packetEpsilon, sub_self] using hsub
  have hcardPos : 0 < (Fintype.card ι : ℝ) := by positivity
  have hhalfPositive : 0 <
      packet.resolution ^ 2 * quittingTerminalSemanticDebtSum minimum /
        (4 * (Fintype.card ι : ℝ)) := by
    exact div_pos
      (mul_pos (sq_pos_of_pos packet.resolution_pos) hminimumDebt)
      (mul_pos (by norm_num) hcardPos)
  have hepsHalf : ∀ᶠ rank in atTop, eps rank ≤
      packet.resolution ^ 2 * quittingTerminalSemanticDebtSum minimum /
        (4 * (Fintype.card ι : ℝ)) :=
    (hepsZero.eventually_lt_const hhalfPositive).mono fun _ hlt ↦ hlt.le
  have hcombined : ∃ᶠ rank in atTop,
      packetTransferRoles minimum packet rank mover recipient ∧
        eps rank ≤ packet.resolution ^ 2 *
          quittingTerminalSemanticDebtSum minimum /
            (4 * (Fintype.card ι : ℝ)) :=
    hroles.mp (hepsHalf.mono fun _ heps hrole ↦ ⟨hrole, heps⟩)
  have hactionFrequently : ∃ᶠ rank in atTop, ∃ endpointAction,
      packetTransferRoles minimum packet rank mover recipient ∧
        eps rank ≤ packet.resolution ^ 2 *
          quittingTerminalSemanticDebtSum minimum /
            (4 * (Fintype.card ι : ℝ)) ∧
        action reward (packetProfile packet rank) (packet.mark rank) mover =
          endpointAction := by
    apply hcombined.mono
    intro rank hrow
    exact ⟨action reward (packetProfile packet rank) (packet.mark rank) mover,
      hrow.1, hrow.2, rfl⟩
  rw [Filter.frequently_exists] at hactionFrequently
  obtain ⟨endpointAction, hfixed⟩ := hactionFrequently
  obtain ⟨selected, hselectedMono, hselected⟩ :=
    extraction_of_frequently_atTop hfixed
  let sourceSeq : ℕ → QuittingTerminalSemanticPair ι := fun rank ↦
    source reward (packetProfile packet (selected rank))
  let targetProfileSeq : ℕ → (quittingGame reward).BehaviorProfile :=
    fun rank ↦ targetProfile reward (packetProfile packet (selected rank))
      (packet.mark (selected rank)) mover
  let targetSeq : ℕ → QuittingTerminalSemanticLawPoint ι := fun rank ↦
    (quittingTerminalSemanticPair reward (targetProfileSeq rank),
      quittingTerminalOutcomeMass reward (targetProfileSeq rank))
  let combinedSeq : ℕ →
      QuittingTerminalSemanticPair ι × QuittingTerminalSemanticLawPoint ι :=
    fun rank ↦ (sourceSeq rank, targetSeq rank)
  have hcombinedMem : ∀ rank, combinedSeq rank ∈
      quittingTerminalSemanticCarrier reward ×ˢ
        quittingTerminalSemanticLawCarrier reward := by
    intro rank
    exact ⟨quittingTerminalSemanticPair_mem_carrier reward _,
      quittingTerminalSemanticLawPoint_mem_carrier reward _⟩
  obtain ⟨limit, hlimitMem, compactSubseq, hcompactMono, hlimit⟩ :=
    ((quittingTerminalSemanticCarrier_isCompact reward).prod
      (quittingTerminalSemanticLawCarrier_isCompact reward)).tendsto_subseq
        hcombinedMem
  let finalRanks : ℕ → ℕ := selected ∘ compactSubseq
  have hfinalMono : StrictMono finalRanks :=
    hselectedMono.comp hcompactMono
  have hsourceLimit : Tendsto (fun rank ↦
      source reward (packetProfile packet (finalRanks rank))) atTop
      (nhds limit.1) := by
    have hfst := (continuous_fst.tendsto limit).comp hlimit
    change Tendsto (sourceSeq ∘ compactSubseq) atTop (nhds limit.1) at hfst
    exact hfst
  have htargetLimit : Tendsto (fun rank ↦
      let profile := packetProfile packet (finalRanks rank)
      let target := targetProfile reward profile (packet.mark (finalRanks rank))
        mover
      (quittingTerminalSemanticPair reward target,
        quittingTerminalOutcomeMass reward target)) atTop
      (nhds limit.2) := by
    have hsnd := (continuous_snd.tendsto limit).comp hlimit
    change Tendsto (targetSeq ∘ compactSubseq) atTop (nhds limit.2) at hsnd
    exact hsnd
  have hsourceMinimumLimit : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (source reward (packetProfile packet (finalRanks rank)))) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum)) :=
    hsourceDebt.comp hfinalMono.tendsto_atTop
  have hsourceClusterSum : quittingTerminalSemanticDebtSum limit.1 =
      quittingTerminalSemanticDebtSum minimum := by
    have hcontinuous :=
      continuous_quittingTerminalSemanticDebtSum.tendsto limit.1 |>.comp
        hsourceLimit
    exact tendsto_nhds_unique hcontinuous hsourceMinimumLimit
  let routedTerminal : {S : Finset ι // S.Nonempty} :=
    ⟨quittingPureEndpointRoutedCoalition marked.val mover endpointAction,
      quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
        marked.val mover endpointAction hcollision⟩
  have hlawTendsto : Tendsto (fun rank ↦
      quittingTerminalOutcomeMass reward
        (targetProfile reward (packetProfile packet (finalRanks rank))
          (packet.mark (finalRanks rank)) mover)
        (some routedTerminal)) atTop
      (nhds (limit.2.2 (some routedTerminal))) := by
    exact (((continuous_apply (some routedTerminal)).comp continuous_snd).tendsto
      limit.2).comp htargetLimit
  have hterminalMass : packet.resolution ≤
      limit.2.2 (some routedTerminal) := by
    apply ge_of_tendsto hlawTendsto
    exact Eventually.of_forall fun rank ↦ by
      let sourceProfile := packetProfile packet (finalRanks rank)
      have hstage := packet.stageMass (finalRanks rank)
      obtain ⟨_hrouted, hroutedMass⟩ :=
        quittingStageCoalitionMass_le_stagePureEndpointRouted reward
          sourceProfile mover (packet.mark (finalRanks rank)) marked
            endpointAction hcollision
      have haction := (hselected (compactSubseq rank)).2.2
      have hstageTarget : quittingStageCoalitionMass reward sourceProfile
          (packet.mark (finalRanks rank)) marked ≤
          quittingStageCoalitionMass reward
            (targetProfile reward sourceProfile (packet.mark (finalRanks rank))
              mover) (packet.mark (finalRanks rank)) routedTerminal := by
        simpa only [sourceProfile, routedTerminal, finalRanks,
          Function.comp_apply, targetProfile, haction] using hroutedMass
      exact hstage.trans (hstageTarget.trans
        (quittingStageCoalitionMass_le_terminalOutcomeMass reward _ _ _))
  have htargetSemanticMem : limit.2.1 ∈
      quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier limit.2 hlimitMem.2
  have htargetAbove := hminimum limit.2.1 htargetSemanticMem
  have hmoverNe : mover ≠ owner := by
    obtain ⟨transfer, hmover, _⟩ := (hselected 0).1
    exact hmover ▸ transfer.mover_ne_owner
  have hrecipientNe : recipient ≠ mover := by
    obtain ⟨transfer, hmover, hrecipient⟩ := (hselected 0).1
    exact hrecipient ▸ hmover ▸ transfer.recipient_ne_mover
  have hmoverLimit : Tendsto (fun rank ↦
      quittingTerminalSemanticDebt
          (target reward (packetProfile packet (finalRanks rank))
            (packet.mark (finalRanks rank)) mover) mover -
        quittingTerminalSemanticDebt
          (source reward (packetProfile packet (finalRanks rank))) mover) atTop
      (nhds (quittingTerminalSemanticDebt limit.2.1 mover -
        quittingTerminalSemanticDebt limit.1 mover)) := by
    have htargetFst := (continuous_fst.tendsto limit.2).comp htargetLimit
    exact ((continuous_quittingTerminalSemanticDebt mover).tendsto limit.2.1
      |>.comp htargetFst).sub
        ((continuous_quittingTerminalSemanticDebt mover).tendsto limit.1
          |>.comp hsourceLimit)
  have hmoverBound :
      quittingTerminalSemanticDebt limit.2.1 mover -
          quittingTerminalSemanticDebt limit.1 mover ≤
        -(packet.resolution ^ 2 * quittingTerminalSemanticDebtSum minimum /
          (2 * (Fintype.card ι : ℝ))) := by
    apply le_of_tendsto hmoverLimit
    exact Eventually.of_forall fun rank ↦ by
      obtain ⟨transfer, hmover, _⟩ := (hselected (compactSubseq rank)).1
      have hgain := transfer.gain_globalFloor
      have hexact := transfer.mover_debt_exact
      subst hmover
      dsimp only [finalRanks, packetTransfer, packetProfile, Function.comp_apply]
        at hexact hgain ⊢
      linarith
  have hrecipientLimit : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtChange
        (source reward (packetProfile packet (finalRanks rank)))
        (target reward (packetProfile packet (finalRanks rank))
          (packet.mark (finalRanks rank)) mover) recipient) atTop
      (nhds (quittingTerminalSemanticDebtChange limit.1 limit.2.1
        recipient)) := by
    have htargetFst := (continuous_fst.tendsto limit.2).comp htargetLimit
    unfold quittingTerminalSemanticDebtChange
    exact ((continuous_quittingTerminalSemanticDebt recipient).tendsto
      limit.2.1 |>.comp htargetFst).sub
        ((continuous_quittingTerminalSemanticDebt recipient).tendsto limit.1
          |>.comp hsourceLimit)
  have hrecipientBound : packetRecipientFloor minimum packet ≤
      quittingTerminalSemanticDebtChange limit.1 limit.2.1 recipient := by
    apply ge_of_tendsto hrecipientLimit
    exact Eventually.of_forall fun rank ↦ by
      obtain ⟨transfer, hmover, hrecipient⟩ :=
        (hselected (compactSubseq rank)).1
      have hfloor := transfer.recipient_globalFloor packet.resolution_pos
        hminimumDebt (hselected (compactSubseq rank)).2.1
      subst hmover
      subst hrecipient
      simpa only [packetRecipientFloor, finalRanks, packetTransfer,
        packetProfile, Function.comp_apply] using hfloor
  refine ⟨{
    endpointAction := endpointAction
    routedTerminal := routedTerminal
    ranks := finalRanks
    ranks_strictMono := hfinalMono
    transfer := fun rank ↦ Classical.choose (hselected (compactSubseq rank)).1
    transfer_mover_eq := fun rank ↦
      (Classical.choose_spec (hselected (compactSubseq rank)).1).1
    transfer_recipient_eq := fun rank ↦
      (Classical.choose_spec (hselected (compactSubseq rank)).1).2
    endpointAction_eq := fun rank ↦ (hselected (compactSubseq rank)).2.2
    routedTerminal_eq := rfl
    sourceLimit := limit.1
    targetPoint := limit.2
    source_mem := hlimitMem.1
    target_mem := hlimitMem.2
    source_tendsto := hsourceLimit
    target_joint_tendsto := htargetLimit
    terminalMass_floor := hterminalMass
    mover_ne_owner := hmoverNe
    recipient_ne_mover := hrecipientNe
    source_on_minimum_fiber := hsourceClusterSum
    target_above_minimum := htargetAbove
    mover_drop := by linarith
    recipient_rise := by
      simpa only [packetRecipientFloor] using hrecipientBound
    target_fiber_or_ascent := htargetAbove.eq_or_lt.imp Eq.symm id
  }⟩

end ConcentratedCollisionFourRole

namespace QuittingMarkedPairMinimumReturnActualizer

variable
  {family : QuittingMarkedPairDecoratedFamily reward}
  {minimum : QuittingTerminalSemanticPair ι}
  {massDensity gainDensity : ℝ}
  {point : QuittingMarkedPairDecoration ι}

/-- An actualized minimum-return family reaches the endpoint-law theorem
without accepting a public chord or fixed roles as new hypotheses. -/
theorem nonempty_threeRoleEndpointLaw_of_minimumReturn
    (actualizer : QuittingMarkedPairMinimumReturnActualizer
      family minimum massDensity gainDensity point)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < family.terminal.val.card)
    (hreturn : point.wholeDebt = quittingTerminalSemanticDebtSum minimum)
    (htail : point.tailDebt = quittingTerminalSemanticDebtSum minimum) :
    ∃ mover recipient,
      Nonempty (ConcentratedCollisionThreeRoleEndpointLaw minimum
        actualizer.packet mover recipient) := by
  have hsourceDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (ConcentratedCollisionFourRole.source reward
          (ConcentratedCollisionFourRole.packetProfile actualizer.packet rank)))
      atTop (nhds (quittingTerminalSemanticDebtSum minimum)) := by
    simpa [ConcentratedCollisionFourRole.packetProfile,
      ConcentratedCollisionFourRole.source, packet] using
      actualizer.wholeDebt_tendsto_minimum hreturn
  have hdispatch :=
    ConcentratedCollisionFourRole.packet_tailEscapeFrequently_or_fixedThreeRoleTransfer
      minimum actualizer.packet hminimumCarrier hminimum hminimum_pos hcollision
        actualizer.scale_pos actualizer.scale_tendsto_zero hsourceDebt
  rcases hdispatch with hescape | hroles
  · have htailDebt := actualizer.tailDebt_tendsto_minimum htail
    have hdiff : Tendsto (fun rank ↦
        quittingTerminalSemanticDebtSum
            (ConcentratedCollisionFourRole.tail reward
              (ConcentratedCollisionFourRole.packetProfile actualizer.packet rank)
              (actualizer.packet.mark rank)) -
          quittingTerminalSemanticDebtSum minimum) atTop (nhds 0) := by
      have hsub := htailDebt.sub_const
        (quittingTerminalSemanticDebtSum minimum)
      simpa [ConcentratedCollisionFourRole.packetProfile,
        ConcentratedCollisionFourRole.tail, packet] using hsub
    have hthreshold : 0 <
        actualizer.resolution * quittingTerminalSemanticDebtSum minimum / 2 :=
      div_pos (mul_pos actualizer.resolution_pos hminimum_pos) (by norm_num)
    have hsmall : ∀ᶠ rank in atTop,
        ¬ ConcentratedCollisionFourRole.packetEscape minimum actualizer.packet
          rank := by
      filter_upwards [hdiff.eventually_lt_const hthreshold] with rank hlt
      exact not_le_of_gt hlt
    exact (not_frequently.mpr hsmall hescape).elim
  · obtain ⟨mover, recipient, _hmover, _hrecipient, hfrequent⟩ := hroles
    exact ⟨mover, recipient,
      ConcentratedCollisionFourRole.nonempty_threeRoleEndpointLaw_of_frequently_packetTransferRoles
        minimum actualizer.packet mover recipient hminimum hminimum_pos
          hcollision hsourceDebt hfrequent⟩

end QuittingMarkedPairMinimumReturnActualizer

end GameTheory
