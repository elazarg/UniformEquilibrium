/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.CanonicalPairEndpointSourceRegeneration
import Research.Quitting.SourceFaithfulMinimumLawCausalization
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.FlatCirculationSupportRankElimination
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumLawFiniteAtom

/-!
# Full-replacement source regeneration and strict support descent

A minimum-fibre full-replacement cluster is compactified on its literal
profile sequence, causalized without replacing those suffix profiles, and
repackaged as a complete same-residual Fin4 source.  The checked minimum-fibre
geometry orients the child by strict positive-debt-support inclusion.

No backward compiler across the horizontal replacement seam is asserted.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open QuittingNonsingletonMinimumLawTransfer
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}
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
    simpa only [replacementEndpointLawPoint, replacementEndpointProfile,
      QuittingPositiveMinimumDebtTangentFamily.fullReplacementPair,
      Function.comp_def, Function.comp_apply] using
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
It bounds the distortion of every non-mover's deviation gain across full
replacement by one vanishing error.  Causalization does not prove this
predicate. -/
def HasVanishingHorizontalDeviationLeak
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    {mover : {who // who ∈ frontier.positiveDebtSupport}}
    (endpoint : FullReplacementCluster frontier mover) : Prop :=
  ∃ error : ℕ → ℝ,
    (∀ rank, 0 ≤ error rank) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ rank observer, observer ≠ mover.1 →
        ∀ response : (quittingGame reward).BehaviorStrategy observer,
          |(quittingTerminalPayoff reward
                (Function.update
                  (frontier.fullReplacementProfile mover
                    (endpoint.subseq rank)) observer response) observer -
              quittingTerminalPayoff reward
                (frontier.fullReplacementProfile mover
                  (endpoint.subseq rank)) observer) -
            (quittingTerminalPayoff reward
                (Function.update (frontier.source (endpoint.subseq rank))
                  observer response) observer -
              quittingTerminalPayoff reward
                (frontier.source (endpoint.subseq rank)) observer)| ≤
            error rank

end QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster

end GameTheory
