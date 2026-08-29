/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.CanonicalPairMinimumEndpointSupportRankHandoff
import Research.Quitting.FinFourProducerAtlas.MinimumSingletonClockCompression
import Research.Quitting.SourceFaithfulMinimumLawCausalization
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.PositiveMinimumDebtTangentFamily

/-!
# Endpoint source regeneration for the canonical Fin4 handoff

The exact endpoint packet is compactified in the joint semantic/law carrier.
Its retained positive marked atom reconstructs a complete same-residual minimum
source whose chronology keeps the literal endpoint profiles and dates.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open QuittingNonsingletonMinimumLawTransfer
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}
  {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket
namespace CanonicalPairMinimumEndpointSupportRankHandoff

/-- The literal endpoint profile selected by the coherent concentrated packet. -/
def renewalEndpointProfile
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  packet.rayPaidTargetProfile (handoff.endpointPacket.subsequence rank)

/-- The original canonical-ray date of that literal endpoint profile. -/
def renewalEndpointMark
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet)
    (rank : ℕ) : ℕ :=
  handoff.endpointPacket.subsequence rank

/-- Its complete joint terminal semantic/law point. -/
def renewalEndpointLawPoint
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet)
    (rank : ℕ) : QuittingTerminalSemanticLawPoint (Fin 4) :=
  (quittingTerminalSemanticPair reward (handoff.renewalEndpointProfile rank),
    quittingTerminalOutcomeMass reward (handoff.renewalEndpointProfile rank))

end CanonicalPairMinimumEndpointSupportRankHandoff
end FinFourOwnerCompressedMinimumReturnForcedPairPacket

open FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- Joint compactification of the exact endpoint packet.  The first coordinate
is identified with the endpoint cluster already stored by the handoff, and the
fixed marked-mass floor survives on the same composed subsequence. -/
structure CanonicalPairEndpointJointLimit
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) where
  point : QuittingTerminalSemanticLawPoint (Fin 4)
  point_mem : point ∈ quittingTerminalSemanticLawCarrier reward
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  tendsto : Tendsto
    (fun rank ↦ handoff.renewalEndpointLawPoint (subsequence rank))
    atTop (nhds point)
  semantic_eq : point.1 = handoff.supportHandoff.endpointCluster
  markedMass_floor : ∀ rank,
    packet.rayResolution ^ 2 ≤
      quittingStageCoalitionMass reward
        (handoff.renewalEndpointProfile (subsequence rank))
        (handoff.renewalEndpointMark (subsequence rank))
        handoff.endpointPacket.terminal

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket
namespace CanonicalPairMinimumEndpointSupportRankHandoff

/-- Compactify the literal endpoint profiles without selecting an unrelated
semantic endpoint or changing their stored dates. -/
theorem nonempty_endpointJointLimit
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) :
    Nonempty (CanonicalPairEndpointJointLimit handoff) := by
  have hmem : ∀ rank, handoff.renewalEndpointLawPoint rank ∈
      quittingTerminalSemanticLawCarrier reward := by
    intro rank
    exact quittingTerminalSemanticLawPoint_mem_carrier reward
      (handoff.renewalEndpointProfile rank)
  obtain ⟨point, hpoint, subsequence, hsubsequence, htendsto⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq hmem
  have hfirst : Tendsto
      (fun rank ↦ (handoff.renewalEndpointLawPoint
        (subsequence rank)).1) atTop (nhds point.1) := by
    exact continuous_fst.tendsto point |>.comp htendsto
  have hknown : Tendsto
      (fun rank ↦ (handoff.renewalEndpointLawPoint
        (subsequence rank)).1) atTop
      (nhds handoff.supportHandoff.endpointCluster) := by
    change Tendsto
      ((fun rank ↦ quittingTerminalSemanticPair reward
        (packet.rayPaidTargetProfile
          (handoff.endpointPacket.subsequence rank))) ∘ subsequence)
      atTop (nhds handoff.supportHandoff.endpointCluster)
    exact handoff.endpointPacket_endpoint_tendsto.comp
      hsubsequence.tendsto_atTop
  have hsemantic : point.1 = handoff.supportHandoff.endpointCluster :=
    tendsto_nhds_unique hfirst hknown
  refine ⟨{
    point := point
    point_mem := hpoint
    subsequence := subsequence
    subsequence_strictMono := hsubsequence
    tendsto := htendsto
    semantic_eq := hsemantic
    markedMass_floor := ?_ }⟩
  intro rank
  have hmass :=
    handoff.endpointPacket.concentrated.stageMass (subsequence rank)
  rw [handoff.endpointPacket.concentrated_resolution_eq_rayResolution_sq,
    handoff.endpointPacket.concentrated_subseq_eq_subsequence,
    handoff.endpointPacket.concentrated_mark_eq_subsequence] at hmass
  simpa only [renewalEndpointProfile, renewalEndpointMark] using hmass

end CanonicalPairMinimumEndpointSupportRankHandoff
end FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- A complete minimum source reconstructed at the exact canonical endpoint
joint-law limit.  The causalization keeps the literal endpoint profiles and
literal canonical dates; only finite cap--Nash words and cutoffs are new. -/
structure CanonicalPairEndpointSourceRegeneration
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) where
  joint : CanonicalPairEndpointJointLimit handoff
  causal : QuittingSourceFaithfulMinimumCausalization
    joint.point handoff.endpointPacket.terminal
    (fun rank ↦ handoff.renewalEndpointProfile
      (joint.subsequence rank))
    (fun rank ↦ handoff.renewalEndpointMark
      (joint.subsequence rank))
    (packet.rayResolution ^ 2)

namespace CanonicalPairEndpointSourceRegeneration

variable
  {handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet}

/-- The source atom obtained from the public source-faithful chronology. -/
def atom (regeneration : CanonicalPairEndpointSourceRegeneration handoff) :
    QuittingMinimumLawCausalSuffixAtom reward regeneration.joint.point where
  terminal := handoff.endpointPacket.terminal
  terminalMass_pos := regeneration.causal.terminalMass_pos
  chronology :=
    ⟨(fun rank ↦ handoff.renewalEndpointProfile
        (regeneration.joint.subsequence rank)),
      regeneration.causal.cutoff,
      (fun rank ↦ handoff.renewalEndpointMark
        (regeneration.joint.subsequence rank)),
      regeneration.causal.roots,
      regeneration.causal.profiles_tendsto,
      regeneration.causal.roots_length,
      regeneration.causal.roots_nash,
      regeneration.causal.prefix_debt_tendsto,
      regeneration.causal.causal⟩

/-- The complete regenerated Fin4 source. -/
def next (regeneration : CanonicalPairEndpointSourceRegeneration handoff) :
    FinFourMinimumAtomProducer reward bound where
  residual := source.residual
  point := regeneration.joint.point
  point_mem := regeneration.causal.point_mem
  semantic_mem := terminalSemanticLawCarrier_fst_mem_carrier
    regeneration.joint.point regeneration.causal.point_mem
  minimum := regeneration.causal.minimum
  inf_pos := regeneration.causal.inf_pos
  debt_eq_inf := regeneration.causal.debt_eq_inf
  atom := regeneration.atom

/-- Public chronology of the regenerated source. -/
def chronology
    (regeneration : CanonicalPairEndpointSourceRegeneration handoff) :
    FinFourMinimumAtomChronology regeneration.next where
  profiles := fun rank ↦ handoff.renewalEndpointProfile
    (regeneration.joint.subsequence rank)
  cutoff := regeneration.causal.cutoff
  mark := fun rank ↦ handoff.renewalEndpointMark
    (regeneration.joint.subsequence rank)
  roots := regeneration.causal.roots
  profiles_tendsto := regeneration.causal.profiles_tendsto
  roots_length := regeneration.causal.roots_length
  roots_nash := regeneration.causal.roots_nash
  prefix_debt_tendsto := by
    simpa only [prefixedProfile] using
      regeneration.causal.prefix_debt_tendsto
  causal := regeneration.causal.causal

@[simp] theorem next_residual_eq
    (regeneration : CanonicalPairEndpointSourceRegeneration handoff) :
    regeneration.next.residual = source.residual := rfl

@[simp] theorem next_point_eq
    (regeneration : CanonicalPairEndpointSourceRegeneration handoff) :
    regeneration.next.point = regeneration.joint.point := rfl

@[simp] theorem next_terminal_eq
    (regeneration : CanonicalPairEndpointSourceRegeneration handoff) :
    regeneration.next.atom.terminal = handoff.endpointPacket.terminal := rfl

@[simp] theorem chronology_profile_eq
    (regeneration : CanonicalPairEndpointSourceRegeneration handoff)
    (rank : ℕ) :
    regeneration.chronology.profiles rank =
      handoff.renewalEndpointProfile
        (regeneration.joint.subsequence rank) := rfl

@[simp] theorem chronology_mark_eq
    (regeneration : CanonicalPairEndpointSourceRegeneration handoff)
    (rank : ℕ) :
    regeneration.chronology.mark rank =
      handoff.renewalEndpointMark
        (regeneration.joint.subsequence rank) := rfl

/-- The endpoint semantic coordinate is exactly the one already stored by the
canonical handoff. -/
theorem next_semantic_eq_endpointCluster
    (regeneration : CanonicalPairEndpointSourceRegeneration handoff) :
    regeneration.next.point.1 =
      handoff.supportHandoff.endpointCluster :=
  regeneration.joint.semantic_eq

end CanonicalPairEndpointSourceRegeneration

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket
namespace CanonicalPairMinimumEndpointSupportRankHandoff

/-- Reconstruct a complete same-residual minimum source at the exact endpoint,
with a positive finite atom and literal profile/date provenance. -/
theorem nonempty_endpointSourceRegeneration
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) :
    Nonempty (CanonicalPairEndpointSourceRegeneration handoff) := by
  obtain ⟨joint⟩ := handoff.nonempty_endpointJointLimit
  have hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum joint.point.1 ≤
        quittingTerminalSemanticDebtSum candidate := by
    intro candidate hcandidate
    rw [joint.semantic_eq,
      handoff.supportHandoff.endpoint_debtSum_eq_minimum]
    exact source.minimum candidate hcandidate
  have hdebt : quittingTerminalSemanticDebtSum joint.point.1 =
      quittingTerminalDebtSumInf reward := by
    rw [joint.semantic_eq,
      handoff.supportHandoff.endpoint_debtSum_eq_minimum]
    exact source.debt_eq_inf
  obtain ⟨causal⟩ := nonempty_sourceFaithfulMinimumCausalization
    joint.point handoff.endpointPacket.terminal
    (fun rank ↦ handoff.renewalEndpointProfile
      (joint.subsequence rank))
    (fun rank ↦ handoff.renewalEndpointMark
      (joint.subsequence rank))
    (packet.rayResolution ^ 2) joint.point_mem joint.tendsto hminimum hdebt
    source.inf_pos (sq_pos_of_pos packet.rayResolution_pos)
    joint.markedMass_floor
  exact ⟨⟨joint, causal⟩⟩

end CanonicalPairMinimumEndpointSupportRankHandoff
end FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- A complete minimum source together with any tangent family based at its
semantic point.  The tangent family need not be extracted from the source
chronology; recursive provenance is carried by every regenerated source's
own chronology and by the literal full-replacement sequence used for its
child. -/
structure FinFourRenewableMinimumSourceNode
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) where
  source : FinFourMinimumAtomProducer reward bound
  chronology : FinFourMinimumAtomChronology source
  frontier : QuittingPositiveMinimumDebtTangentFamily reward
  frontier_base_eq : frontier.base = source.point.1

namespace FinFourRenewableMinimumSourceNode

/-- The node support is the support of its complete minimum source. -/
theorem support_eq_sourceSupport
    (node : FinFourRenewableMinimumSourceNode reward bound) :
    node.frontier.positiveDebtSupport =
      quittingPositiveDebtSupport node.source.point.1 := by
  rw [QuittingPositiveMinimumDebtTangentFamily.positiveDebtSupport,
    node.frontier_base_eq]

/-- Every node has nonempty positive-debt support. -/
theorem support_nonempty
    (node : FinFourRenewableMinimumSourceNode reward bound) :
    node.frontier.positiveDebtSupport.Nonempty :=
  node.frontier.positiveDebtSupport_nonempty

end FinFourRenewableMinimumSourceNode

namespace CanonicalPairEndpointSourceRegeneration

/-- Attach a tangent family to the regenerated endpoint source. -/
theorem exists_node
    {handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet}
    (regeneration : CanonicalPairEndpointSourceRegeneration handoff) :
    ∃ node : FinFourRenewableMinimumSourceNode reward bound,
      node.source = regeneration.next := by
  obtain ⟨frontier, hbase⟩ :=
    exists_positiveMinimumDebtTangentFamily_of_pair
      regeneration.next.point.1 regeneration.next.semantic_mem
      regeneration.next.minimum regeneration.next.minimumDebt_pos
  exact ⟨{
    source := regeneration.next
    chronology := regeneration.chronology
    frontier := frontier
    frontier_base_eq := hbase }, rfl⟩

/-- Forget the displayed source equality. -/
theorem nonempty_node
    {handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet}
    (regeneration : CanonicalPairEndpointSourceRegeneration handoff) :
    Nonempty (FinFourRenewableMinimumSourceNode reward bound) := by
  obtain ⟨node, _⟩ := regeneration.exists_node
  exact ⟨node⟩

end CanonicalPairEndpointSourceRegeneration

end GameTheory
