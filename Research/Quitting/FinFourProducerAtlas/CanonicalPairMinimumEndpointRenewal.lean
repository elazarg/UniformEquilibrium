/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.CanonicalPairMinimumEndpointSupportRankHandoff
import Research.Quitting.SourceFaithfulMinimumLawCausalization
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.FlatCirculationSupportRankElimination
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumLawFiniteAtom

/-!
# Renewable source regeneration after the canonical Fin4 endpoint handoff

A minimum canonical endpoint is compactified in the joint semantic/law carrier
on the exact concentrated-packet subsequence.  Its fixed positive marked atom
then gives a complete source-faithful minimum source at that endpoint.

The same construction applies to every minimum-fibre full-replacement cluster
of a positive-minimum tangent family.  Each such child retains the incoming
hard residual and a causal chronology whose suffix profiles are a subsequence
of the literal parent full-replacement profiles.  Flat no-entry geometry makes
the child's positive-debt support a strict subset of the parent's support.
Strong induction therefore gives a finite source-regenerating trace.

This module deliberately asserts no backward compiler across the horizontal
parent-to-full-replacement update.  Source-faithful causalization transports
response contrasts through its newly prefixed cap--Nash word only.  The
separate `HasVanishingHorizontalDeviationLeak` predicate records the missing
cap control at the horizontal seam.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
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
    simpa only [renewalEndpointLawPoint] using
      handoff.endpointPacket_endpoint_tendsto.comp
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
  exact hmass

end CanonicalPairMinimumEndpointSupportRankHandoff

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

variable {node : FinFourRenewableMinimumSourceNode reward bound}

/-- The node support is the support of its complete minimum source. -/
theorem support_eq_sourceSupport :
    node.frontier.positiveDebtSupport =
      quittingPositiveDebtSupport node.source.point.1 := by
  rw [QuittingPositiveMinimumDebtTangentFamily.positiveDebtSupport,
    node.frontier_base_eq]

/-- Every node has nonempty positive-debt support. -/
theorem support_nonempty : node.frontier.positiveDebtSupport.Nonempty :=
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

namespace FinFourRenewableMinimumSourceNode

/-- Literal parent full-replacement profile on the endpoint's retained
subsequence. -/
def replacementEndpointProfile
    (node : FinFourRenewableMinimumSourceNode reward bound)
    (mover : {who // who ∈ node.frontier.positiveDebtSupport})
    (endpoint : node.frontier.FullReplacementCluster mover)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  node.frontier.fullReplacementProfile mover (endpoint.subseq rank)

/-- Its complete joint terminal semantic/law point. -/
def replacementEndpointLawPoint
    (node : FinFourRenewableMinimumSourceNode reward bound)
    (mover : {who // who ∈ node.frontier.positiveDebtSupport})
    (endpoint : node.frontier.FullReplacementCluster mover)
    (rank : ℕ) : QuittingTerminalSemanticLawPoint (Fin 4) :=
  (quittingTerminalSemanticPair reward
      (node.replacementEndpointProfile mover endpoint rank),
    quittingTerminalOutcomeMass reward
      (node.replacementEndpointProfile mover endpoint rank))

end FinFourRenewableMinimumSourceNode

/-- Joint compactification of one literal parent full-replacement sequence. -/
structure FinFourFullReplacementJointLimit
    (node : FinFourRenewableMinimumSourceNode reward bound)
    (mover : {who // who ∈ node.frontier.positiveDebtSupport})
    (endpoint : node.frontier.FullReplacementCluster mover) where
  point : QuittingTerminalSemanticLawPoint (Fin 4)
  point_mem : point ∈ quittingTerminalSemanticLawCarrier reward
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  tendsto : Tendsto
    (fun rank ↦ node.replacementEndpointLawPoint mover endpoint
      (subsequence rank)) atTop (nhds point)
  semantic_eq : point.1 = endpoint.cluster

namespace FinFourRenewableMinimumSourceNode

/-- Compactify the exact full-replacement profiles and identify their semantic
coordinate with the supplied full-replacement cluster. -/
theorem nonempty_fullReplacementJointLimit
    (node : FinFourRenewableMinimumSourceNode reward bound)
    (mover : {who // who ∈ node.frontier.positiveDebtSupport})
    (endpoint : node.frontier.FullReplacementCluster mover) :
    Nonempty (FinFourFullReplacementJointLimit node mover endpoint) := by
  have hmem : ∀ rank, node.replacementEndpointLawPoint mover endpoint rank ∈
      quittingTerminalSemanticLawCarrier reward := by
    intro rank
    exact quittingTerminalSemanticLawPoint_mem_carrier reward
      (node.replacementEndpointProfile mover endpoint rank)
  obtain ⟨point, hpoint, subsequence, hsubsequence, htendsto⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq hmem
  have hfirst : Tendsto
      (fun rank ↦ (node.replacementEndpointLawPoint mover endpoint
        (subsequence rank)).1) atTop (nhds point.1) := by
    exact continuous_fst.tendsto point |>.comp htendsto
  have hknown : Tendsto
      (fun rank ↦ (node.replacementEndpointLawPoint mover endpoint
        (subsequence rank)).1) atTop (nhds endpoint.cluster) := by
    simpa only [replacementEndpointLawPoint, replacementEndpointProfile] using
      endpoint.fullReplacement_tendsto.comp
        hsubsequence.tendsto_atTop
  exact ⟨{
    point := point
    point_mem := hpoint
    subsequence := subsequence
    subsequence_strictMono := hsubsequence
    tendsto := htendsto
    semantic_eq := tendsto_nhds_unique hfirst hknown }⟩

end FinFourRenewableMinimumSourceNode

/-- Complete same-residual source regeneration at a minimum-fibre literal
full-replacement cluster.  The causal chronology keeps a subsequence of those
exact full-replacement profiles; its positive dates may be reselected. -/
structure FinFourFullReplacementSourceRegeneration
    (node : FinFourRenewableMinimumSourceNode reward bound)
    (mover : {who // who ∈ node.frontier.positiveDebtSupport})
    (endpoint : node.frontier.FullReplacementCluster mover)
    (hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
      quittingTerminalSemanticDebtSum node.frontier.base) where
  joint : FinFourFullReplacementJointLimit node mover endpoint
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  terminalMass_pos : 0 < joint.point.2 (some terminal)
  causal : QuittingSourceFaithfulMinimumCausalChronology
    joint.point terminal
    (fun rank ↦ node.replacementEndpointProfile mover endpoint
      (joint.subsequence rank))

namespace FinFourFullReplacementSourceRegeneration

variable
  {node : FinFourRenewableMinimumSourceNode reward bound}
  {mover : {who // who ∈ node.frontier.positiveDebtSupport}}
  {endpoint : node.frontier.FullReplacementCluster mover}
  {hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
    quittingTerminalSemanticDebtSum node.frontier.base}

/-- Causal atom of the regenerated child source. -/
def atom
    (regeneration : FinFourFullReplacementSourceRegeneration
      node mover endpoint hminimumFiber) :
    QuittingMinimumLawCausalSuffixAtom reward regeneration.joint.point where
  terminal := regeneration.terminal
  terminalMass_pos := regeneration.terminalMass_pos
  chronology :=
    ⟨(fun rank ↦ node.replacementEndpointProfile mover endpoint
        (regeneration.joint.subsequence rank)),
      regeneration.causal.cutoff,
      regeneration.causal.mark,
      regeneration.causal.roots,
      regeneration.causal.profiles_tendsto,
      regeneration.causal.roots_length,
      regeneration.causal.roots_nash,
      regeneration.causal.prefix_debt_tendsto,
      regeneration.causal.causal⟩

/-- Complete child source at the exact full-replacement joint-law limit. -/
def next
    (regeneration : FinFourFullReplacementSourceRegeneration
      node mover endpoint hminimumFiber) :
    FinFourMinimumAtomProducer reward bound where
  residual := node.source.residual
  point := regeneration.joint.point
  point_mem := regeneration.causal.point_mem
  semantic_mem := terminalSemanticLawCarrier_fst_mem_carrier
    regeneration.joint.point regeneration.causal.point_mem
  minimum := regeneration.causal.minimum
  inf_pos := regeneration.causal.inf_pos
  debt_eq_inf := regeneration.causal.debt_eq_inf
  atom := regeneration.atom

/-- Public causal chronology of the child source. -/
def chronology
    (regeneration : FinFourFullReplacementSourceRegeneration
      node mover endpoint hminimumFiber) :
    FinFourMinimumAtomChronology regeneration.next where
  profiles := fun rank ↦ node.replacementEndpointProfile mover endpoint
    (regeneration.joint.subsequence rank)
  cutoff := regeneration.causal.cutoff
  mark := regeneration.causal.mark
  roots := regeneration.causal.roots
  profiles_tendsto := regeneration.causal.profiles_tendsto
  roots_length := regeneration.causal.roots_length
  roots_nash := regeneration.causal.roots_nash
  prefix_debt_tendsto := by
    simpa only [prefixedProfile] using
      regeneration.causal.prefix_debt_tendsto
  causal := regeneration.causal.causal

@[simp] theorem next_residual_eq
    (regeneration : FinFourFullReplacementSourceRegeneration
      node mover endpoint hminimumFiber) :
    regeneration.next.residual = node.source.residual := rfl

@[simp] theorem next_point_eq
    (regeneration : FinFourFullReplacementSourceRegeneration
      node mover endpoint hminimumFiber) :
    regeneration.next.point = regeneration.joint.point := rfl

@[simp] theorem chronology_profile_eq
    (regeneration : FinFourFullReplacementSourceRegeneration
      node mover endpoint hminimumFiber)
    (rank : ℕ) :
    regeneration.chronology.profiles rank =
      node.replacementEndpointProfile mover endpoint
        (regeneration.joint.subsequence rank) := rfl

/-- The regenerated child semantic point is exactly the supplied endpoint
cluster. -/
theorem next_semantic_eq_cluster
    (regeneration : FinFourFullReplacementSourceRegeneration
      node mover endpoint hminimumFiber) :
    regeneration.next.point.1 = endpoint.cluster :=
  regeneration.joint.semantic_eq

/-- Attach an arbitrary tangent family at the regenerated child source. -/
theorem exists_node
    (regeneration : FinFourFullReplacementSourceRegeneration
      node mover endpoint hminimumFiber) :
    ∃ child : FinFourRenewableMinimumSourceNode reward bound,
      child.source = regeneration.next := by
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
    (regeneration : FinFourFullReplacementSourceRegeneration
      node mover endpoint hminimumFiber) :
    Nonempty (FinFourRenewableMinimumSourceNode reward bound) := by
  obtain ⟨child, _⟩ := regeneration.exists_node
  exact ⟨child⟩

end FinFourFullReplacementSourceRegeneration

namespace FinFourRenewableMinimumSourceNode

/-- Regenerate a complete child source at any minimum-fibre literal
full-replacement cluster. -/
theorem nonempty_fullReplacementSourceRegeneration
    (node : FinFourRenewableMinimumSourceNode reward bound)
    (mover : {who // who ∈ node.frontier.positiveDebtSupport})
    (endpoint : node.frontier.FullReplacementCluster mover)
    (hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
      quittingTerminalSemanticDebtSum node.frontier.base) :
    Nonempty (FinFourFullReplacementSourceRegeneration
      node mover endpoint hminimumFiber) := by
  obtain ⟨joint⟩ := node.nonempty_fullReplacementJointLimit mover endpoint
  have hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum joint.point.1 ≤
        quittingTerminalSemanticDebtSum candidate := by
    intro candidate hcandidate
    rw [joint.semantic_eq, hminimumFiber, node.frontier_base_eq]
    exact node.source.minimum candidate hcandidate
  have hdebt : quittingTerminalSemanticDebtSum joint.point.1 =
      quittingTerminalDebtSumInf reward := by
    rw [joint.semantic_eq, hminimumFiber, node.frontier_base_eq]
    exact node.source.debt_eq_inf
  obtain ⟨terminal, hmass⟩ :=
    exists_positive_finiteLawAtom_of_finFourHardResidual_minimum
      reward bound node.source.residual joint.point joint.point_mem hminimum
  obtain ⟨causal⟩ := nonempty_sourceFaithfulMinimumCausalChronology
    joint.point terminal
    (fun rank ↦ node.replacementEndpointProfile mover endpoint
      (joint.subsequence rank))
    joint.point_mem joint.tendsto hminimum hdebt node.source.inf_pos hmass
  exact ⟨{
    joint := joint
    terminal := terminal
    terminalMass_pos := hmass
    causal := causal }⟩

end FinFourRenewableMinimumSourceNode

/-- One source-preserving strict support descent. -/
structure FinFourRenewableSupportDescent
    (parent : FinFourRenewableMinimumSourceNode reward bound) where
  mover : {who // who ∈ parent.frontier.positiveDebtSupport}
  endpoint : parent.frontier.FullReplacementCluster mover
  flat : ∑ observer, parent.frontier.tangent mover observer = 0
  noEntry : ¬HasQuittingStoppingLawFlatSupportEntry
    parent.frontier.base parent.frontier.positiveDebtSupport
      parent.frontier.tangent
  minimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
    quittingTerminalSemanticDebtSum parent.frontier.base
  regeneration : FinFourFullReplacementSourceRegeneration
    parent mover endpoint minimumFiber
  child : FinFourRenewableMinimumSourceNode reward bound
  child_source_eq : child.source = regeneration.next
  support_ssubset : child.frontier.positiveDebtSupport ⊂
    parent.frontier.positiveDebtSupport

namespace FinFourRenewableMinimumSourceNode

/-- Build the complete child and orient it by the checked strict support drop. -/
theorem nonempty_supportDescent
    (parent : FinFourRenewableMinimumSourceNode reward bound)
    (mover : {who // who ∈ parent.frontier.positiveDebtSupport})
    (endpoint : parent.frontier.FullReplacementCluster mover)
    (hflat : ∑ observer, parent.frontier.tangent mover observer = 0)
    (hnoEntry : ¬HasQuittingStoppingLawFlatSupportEntry
      parent.frontier.base parent.frontier.positiveDebtSupport
        parent.frontier.tangent)
    (hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
      quittingTerminalSemanticDebtSum parent.frontier.base) :
    Nonempty (FinFourRenewableSupportDescent parent) := by
  obtain ⟨regeneration⟩ :=
    parent.nonempty_fullReplacementSourceRegeneration mover endpoint
      hminimumFiber
  obtain ⟨child, hchildSource⟩ := regeneration.exists_node
  have hraw :=
    endpoint.positiveDebtSupport_ssubset_of_exactDiagonal_of_flat_of_noEntry_of_minimumFiber
      hflat hnoEntry hminimumFiber
  have hsupport : child.frontier.positiveDebtSupport ⊂
      parent.frontier.positiveDebtSupport := by
    rw [QuittingPositiveMinimumDebtTangentFamily.positiveDebtSupport,
      child.frontier_base_eq, hchildSource]
    change quittingPositiveDebtSupport regeneration.joint.point.1 ⊂ _
    rw [regeneration.joint.semantic_eq]
    exact hraw
  exact ⟨{
    mover := mover
    endpoint := endpoint
    flat := hflat
    noEntry := hnoEntry
    minimumFiber := hminimumFiber
    regeneration := regeneration
    child := child
    child_source_eq := hchildSource
    support_ssubset := hsupport }⟩

end FinFourRenewableMinimumSourceNode

namespace QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster

/-- The missing horizontal-seam control for a stronger backward compiler.
It bounds every non-mover's deviation gain after full replacement by the same
response's gain before replacement, up to one vanishing error.  Causalization
does not prove this predicate. -/
def HasVanishingHorizontalDeviationLeak
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    {mover : {who // who ∈ frontier.positiveDebtSupport}}
    (endpoint : FullReplacementCluster frontier mover) : Prop :=
  ∃ error : ℕ → ℝ,
    (∀ rank, 0 ≤ error rank) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ rank observer, observer ≠ mover.1 →
        ∀ response : (quittingGame reward).BehaviorStrategy observer,
          quittingTerminalPayoff reward
              (Function.update
                (frontier.fullReplacementProfile mover
                  (endpoint.subseq rank)) observer response) observer -
              quittingTerminalPayoff reward
                (frontier.fullReplacementProfile mover
                  (endpoint.subseq rank)) observer ≤
            quittingTerminalPayoff reward
                (Function.update (frontier.source (endpoint.subseq rank))
                  observer response) observer -
              quittingTerminalPayoff reward
                (frontier.source (endpoint.subseq rank)) observer + error rank

end QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster

/-- The three nonrecursive exits of the renewable tangent lane. -/
def FinFourRenewableTerminalExit
    (node : FinFourRenewableMinimumSourceNode reward bound) : Prop :=
  (∃ mover, 0 < ∑ observer, node.frontier.tangent mover observer) ∨
  ((∀ mover, ∑ observer, node.frontier.tangent mover observer = 0) ∧
    HasQuittingStoppingLawFlatSupportEntry node.frontier.base
      node.frontier.positiveDebtSupport node.frontier.tangent) ∨
  ∃ mover : {who // who ∈ node.frontier.positiveDebtSupport},
    ∃ endpoint : node.frontier.FullReplacementCluster mover,
      endpoint.HasOffMinimumPaidFirstDisagreement

namespace FinFourRenewableMinimumSourceNode

/-- Every node either reaches one of the three retained terminal alternatives
or reconstructs a complete strict-support child. -/
theorem terminalExit_or_nonempty_supportDescent
    (node : FinFourRenewableMinimumSourceNode reward bound) :
    FinFourRenewableTerminalExit node ∨
      Nonempty (FinFourRenewableSupportDescent node) := by
  have continue_of_flat_noEntry
      (hflat : ∀ mover,
        ∑ observer, node.frontier.tangent mover observer = 0)
      (hnoEntry : ¬HasQuittingStoppingLawFlatSupportEntry
        node.frontier.base node.frontier.positiveDebtSupport
          node.frontier.tangent) :
      FinFourRenewableTerminalExit node ∨
        Nonempty (FinFourRenewableSupportDescent node) := by
    obtain ⟨who, hwho⟩ := node.support_nonempty
    let mover : {who // who ∈ node.frontier.positiveDebtSupport} :=
      ⟨who, hwho⟩
    obtain ⟨endpoint⟩ :=
      node.frontier.exists_fullReplacementEndpointCluster mover
    have hfloor :=
      node.frontier.base_minimum endpoint.cluster endpoint.cluster_mem
    rcases hfloor.eq_or_lt with hsame | hstrict
    · right
      exact node.nonempty_supportDescent mover endpoint (hflat mover)
        hnoEntry hsame.symm
    · left
      exact Or.inr (Or.inr ⟨mover, endpoint,
        hstrict, endpoint.exists_eventually_paidFirstDisagreement
          (hflat mover) hstrict⟩)
  rcases node.frontier.exhaustiveAlternative with hpositive | hentry |
      hcirculation | hpotential
  · exact Or.inl (Or.inl hpositive)
  · exact Or.inl (Or.inr (Or.inl hentry))
  · exact continue_of_flat_noEntry hcirculation.1 hcirculation.2.1
  · exact continue_of_flat_noEntry hpotential.1 hpotential.2.1

end FinFourRenewableMinimumSourceNode

/-- A finite source-preserving renewal trace. -/
inductive FinFourRenewableTrace
    (node : FinFourRenewableMinimumSourceNode reward bound) : Type
  | terminal (exit : FinFourRenewableTerminalExit node) :
      FinFourRenewableTrace node
  | descend (edge : FinFourRenewableSupportDescent node)
      (tail : FinFourRenewableTrace edge.child) :
      FinFourRenewableTrace node

namespace FinFourRenewableMinimumSourceNode

/-- Strong induction on support cardinality terminates the renewable lane. -/
theorem nonempty_renewalTrace
    (node : FinFourRenewableMinimumSourceNode reward bound) :
    Nonempty (FinFourRenewableTrace node) := by
  classical
  generalize hrank : node.frontier.positiveDebtSupport.card = rank
  induction rank using Nat.strong_induction_on generalizing node with
  | h rank ih =>
      rcases node.terminalExit_or_nonempty_supportDescent with hexit | hdescent
      · exact ⟨FinFourRenewableTrace.terminal hexit⟩
      · obtain ⟨edge⟩ := hdescent
        have hchild : edge.child.frontier.positiveDebtSupport.card < rank := by
          exact (Finset.card_lt_card edge.support_ssubset).trans_eq hrank
        obtain ⟨tail⟩ := ih _ hchild edge.child rfl
        exact ⟨FinFourRenewableTrace.descend edge tail⟩

end FinFourRenewableMinimumSourceNode

/-- A global phase-tagged state.  Regeneration can create only tangent states,
so the incoming phase cannot be reset. -/
inductive CanonicalPairRenewableState
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) : Type
  | incoming
  | tangent (node : FinFourRenewableMinimumSourceNode reward bound)
  | terminal

/-- Natural-valued rank combining the one-use source-origin phase and finite
positive-debt support cardinality. -/
def canonicalPairRenewableRank
    {handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet} :
    CanonicalPairRenewableState handoff → ℕ
  | .terminal => 0
  | .tangent node => 5 + node.frontier.positiveDebtSupport.card
  | .incoming => 10 + (quittingPositiveDebtSupport source.point.1).card

/-- The only legal edges: enter the tangent lane once, descend strict support,
or terminate. -/
inductive CanonicalPairRenewableTransition
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) :
    CanonicalPairRenewableState handoff →
      CanonicalPairRenewableState handoff → Type
  | enter (node : FinFourRenewableMinimumSourceNode reward bound) :
      CanonicalPairRenewableTransition handoff .incoming (.tangent node)
  | descend (edge : FinFourRenewableSupportDescent parent) :
      CanonicalPairRenewableTransition handoff
        (.tangent parent) (.tangent edge.child)
  | exit (node : FinFourRenewableMinimumSourceNode reward bound)
      (terminal : FinFourRenewableTerminalExit node) :
      CanonicalPairRenewableTransition handoff (.tangent node) .terminal

/-- Every legal global edge strictly lowers the single natural-valued rank. -/
theorem canonicalPairRenewableTransition_rank_lt
    {handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet}
    {from to : CanonicalPairRenewableState handoff}
    (edge : CanonicalPairRenewableTransition handoff from to) :
    canonicalPairRenewableRank to < canonicalPairRenewableRank from := by
  cases edge with
  | enter node =>
      have hcard : node.frontier.positiveDebtSupport.card ≤ 4 := by
        calc
          node.frontier.positiveDebtSupport.card ≤ Finset.univ.card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = 4 := by simp
      simp only [canonicalPairRenewableRank]
      omega
  | descend edge =>
      simp only [canonicalPairRenewableRank]
      exact Nat.add_lt_add_left
        (Finset.card_lt_card edge.support_ssubset) 5
  | exit node terminal =>
      simp only [canonicalPairRenewableRank]
      omega

/-- Complete compiler-free renewable conclusion for the canonical handoff. -/
structure CanonicalPairRenewalCertificate
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) where
  regeneration : CanonicalPairEndpointSourceRegeneration handoff
  firstNode : FinFourRenewableMinimumSourceNode reward bound
  firstNode_source_eq : firstNode.source = regeneration.next
  trace : FinFourRenewableTrace firstNode

namespace CanonicalPairMinimumEndpointSupportRankHandoff

/-- The canonical minimum endpoint reconstructs a complete source and enters a
finite same-residual support-descending renewal trace.  No horizontal-seam
backward compiler is claimed. -/
theorem nonempty_renewalCertificate
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) :
    Nonempty (CanonicalPairRenewalCertificate handoff) := by
  obtain ⟨regeneration⟩ := handoff.nonempty_endpointSourceRegeneration
  obtain ⟨firstNode, hfirstSource⟩ := regeneration.exists_node
  obtain ⟨trace⟩ := firstNode.nonempty_renewalTrace
  exact ⟨{
    regeneration := regeneration
    firstNode := firstNode
    firstNode_source_eq := hfirstSource
    trace := trace }⟩

end CanonicalPairMinimumEndpointSupportRankHandoff

end GameTheory
