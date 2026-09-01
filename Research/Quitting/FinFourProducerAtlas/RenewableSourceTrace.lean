import Research.Quitting.FinFourProducerAtlas.CanonicalPairFullReplacementSourceRegeneration

/-!
# Finite renewable traces for four-player minimum sources

This neutral atlas owner contains the source-independent renewable trace.
Canonical-pair phase ranks and branch-specific entry edges remain in their
respective high modules.
-/

noncomputable section

namespace GameTheory

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}

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

/-- A finite source-preserving renewal trace.  The source node is an index,
so recursive descent may change it to the strict-support child. -/
inductive FinFourRenewableTrace :
    FinFourRenewableMinimumSourceNode reward bound → Type
  | terminal (node : FinFourRenewableMinimumSourceNode reward bound)
      (exit : FinFourRenewableTerminalExit node) :
      FinFourRenewableTrace node
  | descend (node : FinFourRenewableMinimumSourceNode reward bound)
      (edge : FinFourRenewableSupportDescent node)
      (tail : FinFourRenewableTrace edge.child) :
      FinFourRenewableTrace node

namespace FinFourRenewableTrace

/-- Number of recursive minimum-fibre child edges in a renewal trace. -/
def descentCount {node : FinFourRenewableMinimumSourceNode reward bound} :
    FinFourRenewableTrace node → ℕ
  | .terminal _ _ => 0
  | .descend _ _ tail => 1 + tail.descentCount

/-- Strict support inclusion bounds the number of recursive edges by the
initial positive-debt-support cardinality. -/
theorem descentCount_lt_support_card
    {node : FinFourRenewableMinimumSourceNode reward bound}
    (trace : FinFourRenewableTrace node) :
    trace.descentCount < node.frontier.positiveDebtSupport.card := by
  induction trace with
  | terminal terminalNode _ =>
      simpa only [descentCount] using
        Finset.card_pos.mpr terminalNode.support_nonempty
  | descend parent edge tail ih =>
      have hsupport := Finset.card_lt_card edge.support_ssubset
      simp only [descentCount]
      omega

/-- A Fin4 renewal trace contains at most three recursive child edges. -/
theorem descentCount_le_three
    {node : FinFourRenewableMinimumSourceNode reward bound}
    (trace : FinFourRenewableTrace node) :
    trace.descentCount ≤ 3 := by
  have htrace := trace.descentCount_lt_support_card
  have hcard : node.frontier.positiveDebtSupport.card ≤ 4 := by
    calc
      node.frontier.positiveDebtSupport.card ≤ Finset.univ.card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 4 := by simp
  omega

/-- The terminal descendant keeps the initial node's hard residual literally. -/
theorem exists_terminalExit_sameResidual
    {node : FinFourRenewableMinimumSourceNode reward bound}
    (trace : FinFourRenewableTrace node) :
    ∃ terminalNode : FinFourRenewableMinimumSourceNode reward bound,
      FinFourRenewableTerminalExit terminalNode ∧
        terminalNode.source.residual = node.source.residual := by
  induction trace with
  | terminal terminalNode exit => exact ⟨terminalNode, exit, rfl⟩
  | descend parent edge tail ih =>
      obtain ⟨terminalNode, exit, hresidual⟩ := ih
      refine ⟨terminalNode, exit, hresidual.trans ?_⟩
      rw [edge.child_source_eq, edge.regeneration.next_residual_eq]

end FinFourRenewableTrace

namespace FinFourRenewableMinimumSourceNode

/-- Strong induction on support cardinality terminates the renewable lane. -/
theorem nonempty_renewalTrace
    (node : FinFourRenewableMinimumSourceNode reward bound) :
    Nonempty (FinFourRenewableTrace node) := by
  classical
  generalize hrank : node.frontier.positiveDebtSupport.card = rank
  induction rank using Nat.strong_induction_on generalizing node with
  | h rank ih =>
      rcases node.terminalExit_or_nonempty_supportDescent with
        hexit | hdescent
      · exact ⟨FinFourRenewableTrace.terminal node hexit⟩
      · obtain ⟨edge⟩ := hdescent
        have hchild :
            edge.child.frontier.positiveDebtSupport.card < rank := by
          exact (Finset.card_lt_card edge.support_ssubset).trans_eq hrank
        have htail : Nonempty (FinFourRenewableTrace edge.child) := by
          apply ih edge.child.frontier.positiveDebtSupport.card
          · exact hchild
          · rfl
        obtain ⟨tail⟩ := htail
        exact ⟨FinFourRenewableTrace.descend node edge tail⟩

end FinFourRenewableMinimumSourceNode

end GameTheory
