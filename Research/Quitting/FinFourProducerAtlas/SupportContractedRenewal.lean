import Research.Quitting.FinFourProducerAtlas.RenewableSourceTrace

/-!
# Renewal from a support-contracted minimum source

This generic adapter deliberately keeps the one-use incoming edge separate
from the renewable trace.  The trace starts at the regenerated minimum source
`target`, whose semantic point is `targetPoint`.  Consequently its descent
count records only further renewable strict-support children and never counts
the incoming one-use entry edge.

The caller supplies the proposition describing its concrete one-use edge into
the support-cardinality-at-most-three target.
This file does not construct that edge, regenerate the target source, or
identify any particular full-debt, reset-rigid, or signed source lane.
-/

noncomputable section

namespace GameTheory

/-- Source-independent contract needed to start the existing renewable trace
after one separately retained incoming support-contraction edge. -/
structure FinFourSupportContractedRenewalInput
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (origin : FinFourMinimumAtomProducer reward bound)
    (targetPoint : QuittingTerminalSemanticLawPoint (Fin 4))
    (EdgeIntoSupportContractedTarget :
      QuittingTerminalSemanticLawPoint (Fin 4) → Prop) where
  incoming : EdgeIntoSupportContractedTarget targetPoint
  target : FinFourMinimumAtomProducer reward bound
  target_point_eq : target.point = targetPoint
  target_residual_eq_origin : target.residual = origin.residual
  targetSupport_card_le_three :
    (quittingPositiveDebtSupport targetPoint.1).card ≤ 3

namespace FinFourSupportContractedRenewalInput

/-- The target point belongs to the joint terminal-semantic law carrier. -/
theorem targetPoint_mem
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {origin : FinFourMinimumAtomProducer reward bound}
    {targetPoint : QuittingTerminalSemanticLawPoint (Fin 4)}
    {EdgeIntoSupportContractedTarget :
      QuittingTerminalSemanticLawPoint (Fin 4) → Prop}
    (input : FinFourSupportContractedRenewalInput
      origin targetPoint EdgeIntoSupportContractedTarget) :
    targetPoint ∈ quittingTerminalSemanticLawCarrier reward := by
  rw [← input.target_point_eq]
  exact input.target.point_mem

/-- The target semantic point is the regenerated source's global minimum. -/
theorem targetPoint_globalMinimum
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {origin : FinFourMinimumAtomProducer reward bound}
    {targetPoint : QuittingTerminalSemanticLawPoint (Fin 4)}
    {EdgeIntoSupportContractedTarget :
      QuittingTerminalSemanticLawPoint (Fin 4) → Prop}
    (input : FinFourSupportContractedRenewalInput
      origin targetPoint EdgeIntoSupportContractedTarget) :
    ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum targetPoint.1 ≤
        quittingTerminalSemanticDebtSum candidate := by
  rw [← input.target_point_eq]
  exact input.target.minimum

/-- The regenerated target point has strictly positive minimum total debt. -/
theorem targetPoint_debtSum_pos
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {origin : FinFourMinimumAtomProducer reward bound}
    {targetPoint : QuittingTerminalSemanticLawPoint (Fin 4)}
    {EdgeIntoSupportContractedTarget :
      QuittingTerminalSemanticLawPoint (Fin 4) → Prop}
    (input : FinFourSupportContractedRenewalInput
      origin targetPoint EdgeIntoSupportContractedTarget) :
    0 < quittingTerminalSemanticDebtSum targetPoint.1 := by
  rw [← input.target_point_eq]
  exact input.target.minimumDebt_pos

end FinFourSupportContractedRenewalInput

/-- Renewable output beginning at the regenerated target.  `incoming` is
retained as separate data; `trace.descentCount` counts only recursive children
of `firstNode`. -/
structure FinFourSupportContractedRenewalResult
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {origin : FinFourMinimumAtomProducer reward bound}
    {targetPoint : QuittingTerminalSemanticLawPoint (Fin 4)}
    {EdgeIntoSupportContractedTarget :
      QuittingTerminalSemanticLawPoint (Fin 4) → Prop}
    (input : FinFourSupportContractedRenewalInput
      origin targetPoint EdgeIntoSupportContractedTarget) where
  incoming : EdgeIntoSupportContractedTarget targetPoint
  firstNode : FinFourRenewableMinimumSourceNode reward bound
  firstNode_source_eq : firstNode.source = input.target
  firstNode_base_eq_targetPoint : firstNode.frontier.base = targetPoint.1
  trace : FinFourRenewableTrace firstNode
  furtherDescentCount_le_two : trace.descentCount ≤ 2
  terminalNode : FinFourRenewableMinimumSourceNode reward bound
  terminalExit : FinFourRenewableTerminalExit terminalNode
  terminalResidual_eq_origin : terminalNode.source.residual = origin.residual

/-- A regenerated positive minimum with support cardinality at most three
starts an existing renewable trace with at most two further strict-support
descents.  The separately supplied entry edge is retained unchanged. -/
theorem nonempty_finFourSupportContractedRenewalResult
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {origin : FinFourMinimumAtomProducer reward bound}
    {targetPoint : QuittingTerminalSemanticLawPoint (Fin 4)}
    {EdgeIntoSupportContractedTarget :
      QuittingTerminalSemanticLawPoint (Fin 4) → Prop}
    (input : FinFourSupportContractedRenewalInput
      origin targetPoint EdgeIntoSupportContractedTarget) :
    Nonempty (FinFourSupportContractedRenewalResult input) := by
  obtain ⟨chronology⟩ := input.target.nonempty_chronology
  obtain ⟨frontier, hfrontier⟩ :=
    exists_positiveMinimumDebtTangentFamily_of_pair
      input.target.point.1 input.target.semantic_mem input.target.minimum
        input.target.minimumDebt_pos
  let firstNode : FinFourRenewableMinimumSourceNode reward bound := {
    source := input.target
    chronology := chronology
    frontier := frontier
    frontier_base_eq := hfrontier
  }
  have hsource : firstNode.source = input.target := rfl
  have hbase : firstNode.frontier.base = targetPoint.1 := by
    dsimp only [firstNode]
    rw [hfrontier, input.target_point_eq]
  obtain ⟨trace⟩ := firstNode.nonempty_renewalTrace
  have hcard : firstNode.frontier.positiveDebtSupport.card ≤ 3 := by
    rw [firstNode.support_eq_sourceSupport, hsource,
      input.target_point_eq]
    exact input.targetSupport_card_le_three
  have hcount : trace.descentCount ≤ 2 := by
    have hstrict := trace.descentCount_lt_support_card
    omega
  obtain ⟨terminalNode, terminalExit, hterminalResidual⟩ :=
    trace.exists_terminalExit_sameResidual
  exact ⟨{
    incoming := input.incoming
    firstNode := firstNode
    firstNode_source_eq := hsource
    firstNode_base_eq_targetPoint := hbase
    trace := trace
    furtherDescentCount_le_two := hcount
    terminalNode := terminalNode
    terminalExit := terminalExit
    terminalResidual_eq_origin :=
      hterminalResidual.trans input.target_residual_eq_origin
  }⟩

end GameTheory
