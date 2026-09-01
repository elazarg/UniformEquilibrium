/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.RenewableSourceTrace

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

/-- A global phase-tagged state.  Regeneration can create only tangent states,
so the incoming phase cannot be reset. -/
inductive CanonicalPairRenewableState
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) : Type
  | incoming
  | tangent (node : FinFourRenewableMinimumSourceNode reward bound)
  | terminal

/-- Exact compact rank combining the one-use source-origin phase and finite
positive-debt support cardinality. -/
def canonicalPairRenewableRank
    {handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet} :
    CanonicalPairRenewableState handoff → ℕ
  | .terminal => 0
  | .tangent node => 1 + node.frontier.positiveDebtSupport.card
  | .incoming => 6

/-- Every renewable state has rank at most six. -/
theorem canonicalPairRenewableRank_le_six
    {handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet}
    (state : CanonicalPairRenewableState handoff) :
    canonicalPairRenewableRank state ≤ 6 := by
  cases state with
  | incoming => simp [canonicalPairRenewableRank]
  | terminal => simp [canonicalPairRenewableRank]
  | tangent node =>
      have hcard : node.frontier.positiveDebtSupport.card ≤ 4 := by
        calc
          node.frontier.positiveDebtSupport.card ≤ Finset.univ.card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = 4 := by simp
      simp only [canonicalPairRenewableRank]
      omega

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
        (Finset.card_lt_card edge.support_ssubset) 1
  | exit _ _ => simp [canonicalPairRenewableRank]

/-- Proposition-valued transition relation in the well-founded orientation:
`dst` is an immediate successor of `src`. -/
def canonicalPairRenewableTransitionRel
    {handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet}
    (dst src : CanonicalPairRenewableState handoff) : Prop :=
  Nonempty (CanonicalPairRenewableTransition handoff src dst)

/-- The packet's global renewable transition relation is well founded. -/
theorem canonicalPairRenewableTransitionRel_wellFounded
    {handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet} :
    WellFounded (canonicalPairRenewableTransitionRel (handoff := handoff)) := by
  apply (InvImage.wf canonicalPairRenewableRank wellFounded_lt).mono
  intro dst src hedge
  obtain ⟨edge⟩ := hedge
  exact canonicalPairRenewableTransition_rank_lt edge

/-- Terminal states have no outgoing renewable transition. -/
theorem not_canonicalPairRenewableTransitionRel_from_terminal
    {handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet}
    (dst : CanonicalPairRenewableState handoff) :
    ¬ canonicalPairRenewableTransitionRel dst (.terminal) := by
  rintro ⟨edge⟩
  cases edge

/-- Complete compiler-free renewable conclusion for the canonical handoff. -/
structure CanonicalPairRenewalCertificate
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) where
  regeneration : CanonicalPairEndpointSourceRegeneration handoff
  firstNode : FinFourRenewableMinimumSourceNode reward bound
  firstNode_source_eq : firstNode.source = regeneration.next
  entry : CanonicalPairRenewableTransition handoff .incoming
    (.tangent firstNode)
  trace : FinFourRenewableTrace firstNode

namespace CanonicalPairRenewalCertificate

/-- A renewal certificate reaches a terminal descendant carrying the original
canonical source's hard residual. -/
theorem exists_terminalExit_sameResidual
    {handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet}
    (certificate : CanonicalPairRenewalCertificate handoff) :
    ∃ terminalNode : FinFourRenewableMinimumSourceNode reward bound,
      FinFourRenewableTerminalExit terminalNode ∧
        terminalNode.source.residual = source.residual := by
  obtain ⟨terminalNode, exit, hresidual⟩ :=
    certificate.trace.exists_terminalExit_sameResidual
  refine ⟨terminalNode, exit, hresidual.trans ?_⟩
  rw [certificate.firstNode_source_eq,
    certificate.regeneration.next_residual_eq]

/-- The recursive portion of every canonical renewal certificate has length
at most three. -/
theorem descentCount_le_three
    {handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet}
    (certificate : CanonicalPairRenewalCertificate handoff) :
    certificate.trace.descentCount ≤ 3 :=
  certificate.trace.descentCount_le_three

end CanonicalPairRenewalCertificate

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
