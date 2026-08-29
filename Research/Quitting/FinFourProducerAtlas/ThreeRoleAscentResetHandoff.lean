/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.ThreeRoleRegeneration
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinitePureTimeResetArrival

/-!
# Reset handoff from a strict Fin4 three-role endpoint

A strict three-role limit ascent is realized at one common actual rank.  At
that rank the literal endpoint profile retains positive routed terminal mass,
strict total-debt ascent over the literal source profile, and a quantitative
recipient debt.  The recipient then moves first in a bounded pure-time reset
path, whose literal final profile and law feed the fixed-law reset dispatch
from the original minimum source.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {profiles : ℕ → (quittingGame reward).BehaviorProfile}
  {owner : Fin 4} {marked : {S : Finset (Fin 4) // S.Nonempty}}
  {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
  {packet : QuittingReprojectionConcentratedPacket
    reward profiles owner marked cutoff scale}
  {mover recipient : Fin 4}

namespace FinFourThreeRoleAscentResetHandoff

/-- The quantitative recipient-rise scale retained from the three-role
endpoint theorem. -/
def riseScale
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale)
    (source : FinFourMinimumAtomProducer reward bound) : ℝ :=
  packet.resolution ^ 2 *
    quittingTerminalSemanticDebtSum source.point.1 / 64

/-- The literal source profile at an endpoint-law rank. -/
def sourceProfile
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1
      packet mover recipient)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  ConcentratedCollisionFourRole.packetProfile packet (endpoint.ranks rank)

/-- The literal pure endpoint profile at the same endpoint-law rank. -/
def endpointProfile
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1
      packet mover recipient)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  ConcentratedCollisionFourRole.targetProfile reward
    (sourceProfile endpoint rank) (packet.mark (endpoint.ranks rank)) mover

end FinFourThreeRoleAscentResetHandoff

/-- One common actual rank realizing a strict three-role ascent, followed by
a recipient-first reset arrival and a fixed-law dispatch from the unchanged
minimum source.  Every semantic point and law in this object is attached to
the displayed literal profiles. -/
structure FinFourThreeRoleAscentResetHandoff
    (source : FinFourMinimumAtomProducer reward bound)
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1
      packet mover recipient) where
  rank : ℕ
  endpoint_source_fiber :
    quittingTerminalSemanticDebtSum endpoint.sourceLimit =
      quittingTerminalSemanticDebtSum source.point.1
  endpoint_source_tendsto : Tendsto (fun index ↦
    ConcentratedCollisionFourRole.source reward
      (FinFourThreeRoleAscentResetHandoff.sourceProfile endpoint index))
    atTop (nhds endpoint.sourceLimit)
  limit_ascent : quittingTerminalSemanticDebtSum source.point.1 <
    quittingTerminalSemanticDebtSum endpoint.targetPoint.1
  actual_ascent_margin :
    (quittingTerminalSemanticDebtSum endpoint.targetPoint.1 -
          quittingTerminalSemanticDebtSum source.point.1) / 2 <
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (FinFourThreeRoleAscentResetHandoff.endpointProfile endpoint rank)) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (FinFourThreeRoleAscentResetHandoff.sourceProfile endpoint rank))
  routed_mass_floor : packet.resolution / 2 <
    quittingTerminalOutcomeMass reward
      (FinFourThreeRoleAscentResetHandoff.endpointProfile endpoint rank)
      (some endpoint.routedTerminal)
  recipient_debt_floor :
    3 * FinFourThreeRoleAscentResetHandoff.riseScale packet source / 4 <
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (FinFourThreeRoleAscentResetHandoff.endpointProfile endpoint rank))
        recipient
  arrival : QuittingFirstPlayerResetArrival reward
    source.residual.witness.terminalGap
    (FinFourThreeRoleAscentResetHandoff.riseScale packet source)
    (FinFourThreeRoleAscentResetHandoff.endpointProfile endpoint rank)
    recipient
  final_joint :
    (quittingTerminalSemanticPair reward arrival.finalProfile,
        quittingTerminalOutcomeMass reward arrival.finalProfile) ∈
      quittingTerminalSemanticLawCarrier reward
  returned : QuittingTerminalSemanticPair (Fin 4)
  dispatch : QuittingFixedLawResetDispatch (reward := reward) source.point.1
    (quittingTerminalSemanticPair reward arrival.finalProfile)
    (quittingTerminalOutcomeMass reward arrival.finalProfile)
    arrival.owner arrival.other returned

namespace FinFourThreeRoleAscentResetHandoff

variable
  (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1
    packet mover recipient)

/-- The selected source profile is the packet profile at the endpoint's
retained rank; no carrier representative is substituted. -/
theorem sourceProfile_eq_packetProfile
    (handoff : FinFourThreeRoleAscentResetHandoff source endpoint) :
    sourceProfile endpoint handoff.rank =
      ConcentratedCollisionFourRole.packetProfile packet
        (endpoint.ranks handoff.rank) := rfl

/-- The selected endpoint is the literal pure endpoint update of that same
source profile and marked date. -/
theorem endpointProfile_eq_targetProfile
    (handoff : FinFourThreeRoleAscentResetHandoff source endpoint) :
    endpointProfile endpoint handoff.rank =
      ConcentratedCollisionFourRole.targetProfile reward
        (sourceProfile endpoint handoff.rank)
        (packet.mark (endpoint.ranks handoff.rank)) mover := rfl

/-- The selected recurrent transfer is exactly the endpoint transfer at the
same common rank used by the literal profiles. -/
def selectedTransfer
    (handoff : FinFourThreeRoleAscentResetHandoff source endpoint) :=
  endpoint.transfer handoff.rank

/-- The selected transfer's mover is the fixed endpoint mover. -/
theorem selectedTransfer_mover_eq
    (handoff : FinFourThreeRoleAscentResetHandoff source endpoint) :
    (selectedTransfer endpoint handoff).mover = mover :=
  endpoint.transfer_mover_eq handoff.rank

/-- The selected transfer's recipient is the fixed endpoint recipient. -/
theorem selectedTransfer_recipient_eq
    (handoff : FinFourThreeRoleAscentResetHandoff source endpoint) :
    (selectedTransfer endpoint handoff).recipient = recipient :=
  endpoint.transfer_recipient_eq handoff.rank

/-- The recurrent source profiles converge to the endpoint's source limit,
which is retained separately from the fixed minimum dispatch source. -/
theorem sourceProfile_tendsto_endpointSourceLimit
    (handoff : FinFourThreeRoleAscentResetHandoff source endpoint) :
    Tendsto (fun index ↦ ConcentratedCollisionFourRole.source reward
      (sourceProfile endpoint index)) atTop (nhds endpoint.sourceLimit) :=
  handoff.endpoint_source_tendsto

/-- Only the total debt is identified across the source fibre; no equality of
the endpoint source limit with the fixed minimum semantic pair is asserted. -/
theorem endpointSourceLimit_debt_eq_fixedMinimum
    (handoff : FinFourThreeRoleAscentResetHandoff source endpoint) :
    quittingTerminalSemanticDebtSum endpoint.sourceLimit =
      quittingTerminalSemanticDebtSum source.point.1 :=
  handoff.endpoint_source_fiber

/-- The retained first edge is literally the recipient's pure-time update of
the selected endpoint profile. -/
theorem firstProfile_eq_update
    (handoff : FinFourThreeRoleAscentResetHandoff source endpoint) :
    handoff.arrival.firstProfile = Function.update
      (endpointProfile endpoint handoff.rank) recipient
      (quittingPureTimeBehaviorStrategy reward recipient
        handoff.arrival.firstQuitTime) :=
  handoff.arrival.firstProfile_eq

/-- The recipient's first actual edge gains more than half of the endpoint
rise scale. -/
theorem recipient_first_gain
    (handoff : FinFourThreeRoleAscentResetHandoff source endpoint) :
    riseScale packet source / 2 <
      quittingTerminalPayoff reward handoff.arrival.firstProfile recipient -
        quittingTerminalPayoff reward
          (endpointProfile endpoint handoff.rank) recipient :=
  handoff.arrival.first_gain

/-- The bounded path is structurally headed by the displayed recipient edge,
not merely accompanied by an unrelated recipient-gain certificate. -/
theorem recipient_first_path
    (handoff : FinFourThreeRoleAscentResetHandoff source endpoint) :
    QuittingProfitablePureTimePath reward
      (min (riseScale packet source / 2)
        (3 * source.residual.witness.terminalGap / 4))
      (endpointProfile endpoint handoff.rank) handoff.arrival.length
      handoff.arrival.finalProfile :=
  handoff.arrival.path

/-- The final reset dispatch is based at the original fixed minimum semantic
pair, not at the distinct endpoint source limit. -/
theorem dispatch_from_fixedMinimum
    (handoff : FinFourThreeRoleAscentResetHandoff source endpoint) :
    QuittingFixedLawResetDispatch (reward := reward) source.point.1
      (quittingTerminalSemanticPair reward handoff.arrival.finalProfile)
      (quittingTerminalOutcomeMass reward handoff.arrival.finalProfile)
      handoff.arrival.owner handoff.arrival.other handoff.returned :=
  handoff.dispatch

/-- On four players the entire reset arrival has at most seven pure-time
updates. -/
theorem length_le_seven
    (handoff : FinFourThreeRoleAscentResetHandoff source endpoint) :
    handoff.arrival.length ≤ 7 := by
  simpa using handoff.arrival.length_le

/-- The selected literal source and endpoint profiles have strict total-debt
ascent, not merely distinct limiting semantic points. -/
theorem actual_debt_ascent
    (handoff : FinFourThreeRoleAscentResetHandoff source endpoint) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (sourceProfile endpoint handoff.rank)) <
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (endpointProfile endpoint handoff.rank)) := by
  have hlimit : 0 <
      (quittingTerminalSemanticDebtSum endpoint.targetPoint.1 -
        quittingTerminalSemanticDebtSum source.point.1) / 2 := by
    linarith [handoff.limit_ascent]
  linarith [handoff.actual_ascent_margin]

/-- A strict endpoint-limit ascent produces the complete actual-profile reset
handoff without changing the minimum source or its exploitability witness. -/
theorem nonempty_of_strict_ascent
    (hascent : quittingTerminalSemanticDebtSum source.point.1 <
      quittingTerminalSemanticDebtSum endpoint.targetPoint.1) :
    Nonempty (FinFourThreeRoleAscentResetHandoff source endpoint) := by
  let eta := riseScale packet source
  let sourceAt : ℕ → (quittingGame reward).BehaviorProfile :=
    sourceProfile endpoint
  let endpointAt : ℕ → (quittingGame reward).BehaviorProfile :=
    endpointProfile endpoint
  have heta : 0 < eta := by
    dsimp only [eta, riseScale]
    exact div_pos
      (mul_pos (sq_pos_of_pos packet.resolution_pos) source.minimumDebt_pos)
      (by norm_num)
  have hsourceDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (sourceAt rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum endpoint.sourceLimit)) := by
    exact continuous_quittingTerminalSemanticDebtSum.tendsto
      endpoint.sourceLimit |>.comp endpoint.source_tendsto
  have htargetPair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward (endpointAt rank)) atTop
      (nhds endpoint.targetPoint.1) := by
    exact (continuous_fst.tendsto endpoint.targetPoint).comp
      endpoint.target_joint_tendsto
  have htargetDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (endpointAt rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum endpoint.targetPoint.1)) := by
    exact continuous_quittingTerminalSemanticDebtSum.tendsto
      endpoint.targetPoint.1 |>.comp htargetPair
  have hrecipientDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (endpointAt rank)) recipient)
      atTop (nhds (quittingTerminalSemanticDebt endpoint.targetPoint.1
        recipient)) := by
    exact (continuous_quittingTerminalSemanticDebt recipient).tendsto
      endpoint.targetPoint.1 |>.comp htargetPair
  have hlaw : Tendsto (fun rank ↦
      quittingTerminalOutcomeMass reward (endpointAt rank)) atTop
      (nhds endpoint.targetPoint.2) := by
    exact (continuous_snd.tendsto endpoint.targetPoint).comp
      endpoint.target_joint_tendsto
  have hrouted : Tendsto (fun rank ↦
      quittingTerminalOutcomeMass reward (endpointAt rank)
        (some endpoint.routedTerminal)) atTop
      (nhds (endpoint.targetPoint.2 (some endpoint.routedTerminal))) := by
    exact (continuous_apply (some endpoint.routedTerminal)).tendsto
      endpoint.targetPoint.2 |>.comp hlaw
  have hsourceLimit : quittingTerminalSemanticDebtSum endpoint.sourceLimit =
      quittingTerminalSemanticDebtSum source.point.1 :=
    endpoint.source_on_minimum_fiber
  have hrecipientSourceNonneg : 0 ≤
      quittingTerminalSemanticDebt endpoint.sourceLimit recipient :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      endpoint.source_mem recipient
  have hrecipientTarget : eta ≤
      quittingTerminalSemanticDebt endpoint.targetPoint.1 recipient := by
    have hrise := endpoint.finFour_recipient_rise
    dsimp only [eta, riseScale]
    rw [quittingTerminalSemanticDebtChange] at hrise
    linarith
  have hrecipientThreshold : 3 * eta / 4 <
      quittingTerminalSemanticDebt endpoint.targetPoint.1 recipient := by
    linarith
  have hroutedThreshold : packet.resolution / 2 <
      endpoint.targetPoint.2 (some endpoint.routedTerminal) :=
    (half_lt_self packet.resolution_pos).trans_le endpoint.terminalMass_floor
  let delta := quittingTerminalSemanticDebtSum endpoint.targetPoint.1 -
    quittingTerminalSemanticDebtSum source.point.1
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  have hsourceThreshold :
      quittingTerminalSemanticDebtSum endpoint.sourceLimit <
        quittingTerminalSemanticDebtSum source.point.1 + delta / 4 := by
    rw [hsourceLimit]
    linarith
  have htargetThreshold :
      quittingTerminalSemanticDebtSum source.point.1 + 3 * delta / 4 <
        quittingTerminalSemanticDebtSum endpoint.targetPoint.1 := by
    dsimp only [delta]
    linarith
  have heventuallySource : ∀ᶠ rank in atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (sourceAt rank)) <
        quittingTerminalSemanticDebtSum source.point.1 + delta / 4 :=
    hsourceDebt.eventually_lt_const hsourceThreshold
  have heventuallyTarget : ∀ᶠ rank in atTop,
      quittingTerminalSemanticDebtSum source.point.1 + 3 * delta / 4 <
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (endpointAt rank)) :=
    htargetDebt.eventually_const_lt htargetThreshold
  have heventuallyRecipient : ∀ᶠ rank in atTop,
      3 * eta / 4 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (endpointAt rank)) recipient :=
    hrecipientDebt.eventually_const_lt hrecipientThreshold
  have heventuallyRouted : ∀ᶠ rank in atTop,
      packet.resolution / 2 <
        quittingTerminalOutcomeMass reward (endpointAt rank)
          (some endpoint.routedTerminal) :=
    hrouted.eventually_const_lt hroutedThreshold
  obtain ⟨rank, hsourceRank, htargetRank, hrecipientRank, hroutedRank⟩ :=
    (heventuallySource.and (heventuallyTarget.and
      (heventuallyRecipient.and heventuallyRouted))).exists
  obtain ⟨arrival⟩ := nonempty_pureTimeResetArrival_with_firstPlayer reward
    source.residual.witness.terminalGap eta
    source.residual.witness.terminalGap_pos heta
    source.residual.witness.hasUniformTerminalDebtFloor
    (endpointAt rank) recipient hrecipientRank
  have hjoint :
      (quittingTerminalSemanticPair reward arrival.finalProfile,
          quittingTerminalOutcomeMass reward arrival.finalProfile) ∈
        quittingTerminalSemanticLawCarrier reward :=
    quittingTerminalSemanticLawPoint_mem_carrier reward arrival.finalProfile
  obtain ⟨returned, dispatch⟩ :=
    source.residual.witness.exists_fixedLawResetDispatch
      source.point.1
      (quittingTerminalSemanticPair reward arrival.finalProfile)
      (quittingTerminalOutcomeMass reward arrival.finalProfile)
      arrival.owner arrival.other source.minimum source.minimumDebt_pos
      hjoint arrival.owner_reset arrival.incidence_pos
  refine ⟨{
    rank := rank
    endpoint_source_fiber := endpoint.source_on_minimum_fiber
    endpoint_source_tendsto := endpoint.source_tendsto
    limit_ascent := hascent
    actual_ascent_margin := ?_
    routed_mass_floor := ?_
    recipient_debt_floor := ?_
    arrival := arrival
    final_joint := hjoint
    returned := returned
    dispatch := dispatch
  }⟩
  · change delta / 2 < _
    change quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (endpointAt rank)) -
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (sourceAt rank)) > delta / 2
    linarith
  · exact hroutedRank
  · exact hrecipientRank

end FinFourThreeRoleAscentResetHandoff

end GameTheory
