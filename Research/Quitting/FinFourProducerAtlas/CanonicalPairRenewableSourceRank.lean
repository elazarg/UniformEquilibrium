/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.CanonicalPairFullReplacementSourceRegeneration

/-!
# Renewable source rank for the canonical Fin4 endpoint handoff

Every regenerated minimum-fibre child strictly lowers positive-debt-support
cardinality.  A one-use incoming phase and the tangent support cardinality
therefore form one natural-valued rank.  The construction terminates at a
positive-slope, support-entry, or off-minimum paid-row output.

This is a compiler-free renewable source/rank theorem.
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

open FinFourOwnerCompressedMinimumReturnForcedPairPacket
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
      refine Or.inr (Or.inr ⟨mover, endpoint, ?_⟩)
      exact ⟨hstrict,
        endpoint.exists_eventually_paidFirstDisagreement
          (hflat mover) hstrict⟩
  rcases node.frontier.exhaustiveAlternative with hpositive | hentry |
      hcirculation | hpotential
  · exact Or.inl (Or.inl hpositive)
  · exact Or.inl (Or.inr (Or.inl hentry))
  · exact continue_of_flat_noEntry hcirculation.1 hcirculation.2.1
  · exact continue_of_flat_noEntry hpotential.1 hpotential.2.1

end FinFourRenewableMinimumSourceNode

/-- A finite source-preserving renewal trace.  The source node is an
index, so recursive descent may change it to the strict-support child. -/
inductive FinFourRenewableTrace :
    FinFourRenewableMinimumSourceNode reward bound → Type
  | terminal (node : FinFourRenewableMinimumSourceNode reward bound)
      (exit : FinFourRenewableTerminalExit node) :
      FinFourRenewableTrace node
  | descend (node : FinFourRenewableMinimumSourceNode reward bound)
      (edge : FinFourRenewableSupportDescent node)
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
      · exact ⟨FinFourRenewableTrace.terminal node hexit⟩
      · obtain ⟨edge⟩ := hdescent
        have hchild : edge.child.frontier.positiveDebtSupport.card < rank := by
          exact (Finset.card_lt_card edge.support_ssubset).trans_eq hrank
        have htail : Nonempty (FinFourRenewableTrace edge.child) := by
          apply ih edge.child.frontier.positiveDebtSupport.card
          · exact hchild
          · rfl
        obtain ⟨tail⟩ := htail
        exact ⟨FinFourRenewableTrace.descend node edge tail⟩

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
  | enter
      (regeneration : CanonicalPairEndpointSourceRegeneration handoff)
      (node : FinFourRenewableMinimumSourceNode reward bound)
      (source_eq : node.source = regeneration.next) :
      CanonicalPairRenewableTransition handoff .incoming (.tangent node)
  | descend
      (parent : FinFourRenewableMinimumSourceNode reward bound)
      (edge : FinFourRenewableSupportDescent parent) :
      CanonicalPairRenewableTransition handoff
        (.tangent parent) (.tangent edge.child)
  | exit (node : FinFourRenewableMinimumSourceNode reward bound)
      (terminal : FinFourRenewableTerminalExit node) :
      CanonicalPairRenewableTransition handoff (.tangent node) .terminal

/-- Every legal global edge strictly lowers the single natural-valued rank. -/
theorem canonicalPairRenewableTransition_rank_lt
    {handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet}
    {src dst : CanonicalPairRenewableState handoff}
    (edge : CanonicalPairRenewableTransition handoff src dst) :
    canonicalPairRenewableRank dst < canonicalPairRenewableRank src := by
  cases edge with
  | enter _ node _ =>
      have hcard : node.frontier.positiveDebtSupport.card ≤ 4 := by
        calc
          node.frontier.positiveDebtSupport.card ≤ Finset.univ.card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = 4 := by simp
      simp only [canonicalPairRenewableRank]
      omega
  | descend _ edge =>
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
  entry : CanonicalPairRenewableTransition handoff .incoming
    (.tangent firstNode)
  trace : FinFourRenewableTrace firstNode

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket
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
    entry := CanonicalPairRenewableTransition.enter
      regeneration firstNode hfirstSource
    trace := trace }⟩

end CanonicalPairMinimumEndpointSupportRankHandoff
end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
