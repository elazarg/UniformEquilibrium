/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact bounded trace-visible rank and pointwise post-limit recursion

The trace-visible theorem retains compact terminal and successor certificate
carriers, closed relations, a continuous terminal consumer, and a continuous
backward compiler.  Strict rank decrease supplies termination; the remaining
data supply compact closed output relations.

The final section gives a separate topology-free pointwise producer.  It may
be applied after one actual node is reconstructed, but it is not a
trace-visible edge and yields no closed-output theorem.
-/

noncomputable section

namespace Math
namespace Topology

universe uNode uTerminal uSuccessor uOutcome uExecution

variable {Node : Type uNode} {TerminalCertificate : Type uTerminal}
  {SuccessorCertificate : Type uSuccessor} {Outcome : Type uOutcome}
  [TopologicalSpace Node] [TopologicalSpace TerminalCertificate]
  [TopologicalSpace SuccessorCertificate] [TopologicalSpace Outcome]

/-- Complete data for a bounded trace-visible ranked adapter. -/
structure CompactRankedOutcomeAdapter
    (Node TerminalCertificate SuccessorCertificate Outcome : Type*)
    [TopologicalSpace Node] [TopologicalSpace TerminalCertificate]
    [TopologicalSpace SuccessorCertificate] [TopologicalSpace Outcome] where
  nodeSet : Set Node
  node_compact : IsCompact nodeSet
  rank : Node → ℕ
  rankBound : ℕ
  rank_le : ∀ node, node ∈ nodeSet → rank node ≤ rankBound
  level_compact : ∀ level,
    IsCompact {node | node ∈ nodeSet ∧ rank node = level}
  terminalCertificateSet : Set TerminalCertificate
  terminalCertificate_compact : IsCompact terminalCertificateSet
  terminal : Node → TerminalCertificate → Prop
  terminalGraph_closed : ∀ level, IsClosed
    {point : Node × TerminalCertificate |
      point.1 ∈ nodeSet ∧ rank point.1 = level ∧
        point.2 ∈ terminalCertificateSet ∧ terminal point.1 point.2}
  consume : Node × TerminalCertificate → Outcome
  consume_continuous : Continuous consume
  successorCertificateSet : Set SuccessorCertificate
  successorCertificate_compact : IsCompact successorCertificateSet
  successor : Node → SuccessorCertificate → Node → Prop
  successorGraph_closed : ∀ level, IsClosed
    {edge : (Node × SuccessorCertificate) × Node |
      edge.1.1 ∈ nodeSet ∧ rank edge.1.1 = level ∧
        edge.1.2 ∈ successorCertificateSet ∧ edge.2 ∈ nodeSet ∧
          successor edge.1.1 edge.1.2 edge.2}
  successor_rank_lt : ∀ parent certificate child,
    successor parent certificate child → rank child < rank parent
  back : ((Node × SuccessorCertificate) × Node) × Outcome → Outcome
  back_continuous : Continuous back
  complete : ∀ node, node ∈ nodeSet →
    (∃ certificate, certificate ∈ terminalCertificateSet ∧
      terminal node certificate) ∨
    ∃ certificate child,
      certificate ∈ successorCertificateSet ∧ child ∈ nodeSet ∧
        successor node certificate child

namespace CompactRankedOutcomeAdapter

variable
  (adapter : CompactRankedOutcomeAdapter Node TerminalCertificate
    SuccessorCertificate Outcome)

/-- Nodes at one literal rank. -/
def levelSet (level : ℕ) : Set Node :=
  {node | node ∈ adapter.nodeSet ∧ adapter.rank node = level}

/-- Proof-relevant terminal certificates at one literal rank. -/
def terminalDomain (level : ℕ) : Set (Node × TerminalCertificate) :=
  {point | point.1 ∈ adapter.nodeSet ∧ adapter.rank point.1 = level ∧
    point.2 ∈ adapter.terminalCertificateSet ∧
      adapter.terminal point.1 point.2}

/-- Terminal outputs retain the parent coordinate. -/
def terminalOutputSet (level : ℕ) : Set (Node × Outcome) :=
  (fun point ↦ (point.1, adapter.consume point)) ''
    adapter.terminalDomain level

theorem isCompact_terminalDomain (level : ℕ) :
    IsCompact (adapter.terminalDomain level) := by
  have hproduct := (adapter.level_compact level).prod
    adapter.terminalCertificate_compact
  exact hproduct.of_isClosed_subset (adapter.terminalGraph_closed level) <| by
    intro point hpoint
    exact ⟨⟨hpoint.1, hpoint.2.1⟩, hpoint.2.2.1⟩

theorem isCompact_terminalOutputSet (level : ℕ) :
    IsCompact (adapter.terminalOutputSet level) := by
  apply (adapter.isCompact_terminalDomain level).image
  exact continuous_fst.prodMk (adapter.consume_continuous)

/-- Proof-relevant successor/output fiber product.  The equality in the last
conjunct is the literal child-output attachment. -/
def successorOutcomeDomain
    (level : ℕ) (lower : Set (Node × Outcome)) :
    Set (((Node × SuccessorCertificate) × Node) × (Node × Outcome)) :=
  {point |
    point.1.1.1 ∈ adapter.nodeSet ∧
      adapter.rank point.1.1.1 = level ∧
      point.1.1.2 ∈ adapter.successorCertificateSet ∧
      point.1.2 ∈ adapter.nodeSet ∧
      adapter.successor point.1.1.1 point.1.1.2 point.1.2 ∧
      point.2 ∈ lower ∧ point.1.2 = point.2.1}

/-- Backward outputs retain the exact parent coordinate. -/
def successorOutputSet
    (level : ℕ) (lower : Set (Node × Outcome)) : Set (Node × Outcome) :=
  (fun point ↦ (point.1.1.1, adapter.back (point.1, point.2.2))) ''
    adapter.successorOutcomeDomain level lower

theorem isCompact_successorOutcomeDomain
    [T2Space Node]
    (level : ℕ) {lower : Set (Node × Outcome)}
    (hlower : IsCompact lower) :
    IsCompact (adapter.successorOutcomeDomain level lower) := by
  let graph : Set ((Node × SuccessorCertificate) × Node) :=
    {edge |
      edge.1.1 ∈ adapter.nodeSet ∧ adapter.rank edge.1.1 = level ∧
        edge.1.2 ∈ adapter.successorCertificateSet ∧
        edge.2 ∈ adapter.nodeSet ∧
        adapter.successor edge.1.1 edge.1.2 edge.2}
  have hgraphProduct := (adapter.level_compact level).prod
    adapter.successorCertificate_compact |>.prod adapter.node_compact
  have hgraph : IsCompact graph := by
    exact hgraphProduct.of_isClosed_subset
      (by simpa only [graph] using adapter.successorGraph_closed level) <| by
        intro edge hedge
        exact ⟨⟨⟨hedge.1, hedge.2.1⟩, hedge.2.2.1⟩, hedge.2.2.2.1⟩
  let ambient : Set
      (((Node × SuccessorCertificate) × Node) × (Node × Outcome)) :=
    graph ×ˢ lower
  have hambient : IsCompact ambient := hgraph.prod hlower
  have hequality : IsClosed
      {point : ((Node × SuccessorCertificate) × Node) × (Node × Outcome) |
        point.1.2 = point.2.1} := by
    exact isClosed_eq
      (continuous_snd.comp continuous_fst)
      (continuous_fst.comp continuous_snd)
  have heq : adapter.successorOutcomeDomain level lower =
      ambient ∩
        {point : ((Node × SuccessorCertificate) × Node) × (Node × Outcome) |
          point.1.2 = point.2.1} := by
    ext point
    simp only [successorOutcomeDomain, ambient, graph, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_prod]
    aesop
  rw [heq]
  exact hambient.inter_right hequality

theorem isCompact_successorOutputSet
    [T2Space Node]
    (level : ℕ) {lower : Set (Node × Outcome)}
    (hlower : IsCompact lower) :
    IsCompact (adapter.successorOutputSet level lower) := by
  apply (adapter.isCompact_successorOutcomeDomain level hlower).image
  exact (((continuous_fst.comp continuous_fst).comp continuous_fst).prodMk <|
    adapter.back_continuous.comp <|
      continuous_fst.prodMk (continuous_snd.comp continuous_snd))

/-- Complete output relation for all nodes of rank at most `level`. -/
def outcomeUpTo : ℕ → Set (Node × Outcome)
  | 0 => adapter.terminalOutputSet 0
  | level + 1 =>
      outcomeUpTo level ∪
        adapter.terminalOutputSet (level + 1) ∪
          adapter.successorOutputSet (level + 1)
            (outcomeUpTo level)

theorem outcomeUpTo_mono (level : ℕ) :
    outcomeUpTo adapter level ⊆ outcomeUpTo adapter (level + 1) := by
  intro point hpoint
  exact Or.inl (Or.inl hpoint)

theorem outcomeUpTo_mono_of_le {first second : ℕ} (h : first ≤ second) :
    outcomeUpTo adapter first ⊆ outcomeUpTo adapter second := by
  induction second, h using Nat.le_induction with
  | base => exact fun _ hpoint ↦ hpoint
  | succ second _ ih => exact ih.trans (outcomeUpTo_mono adapter second)

/-- Every bounded trace-visible outcome relation is compact. -/
theorem isCompact_outcomeUpTo
    [T2Space Node] : ∀ level, IsCompact (outcomeUpTo adapter level)
  | 0 => adapter.isCompact_terminalOutputSet 0
  | level + 1 => by
      have hlower := isCompact_outcomeUpTo level
      exact (hlower.union <| adapter.isCompact_terminalOutputSet (level + 1)).union
        (adapter.isCompact_successorOutputSet (level + 1) hlower)

/-- Every bounded trace-visible outcome relation is closed in Hausdorff
output space. -/
theorem isClosed_outcomeUpTo
    [T2Space Node] [T2Space Outcome] (level : ℕ) :
    IsClosed (outcomeUpTo adapter level) :=
  (isCompact_outcomeUpTo adapter level).isClosed

/-! ### Proof-relevant bounded executions

The relation `outcomeUpTo` is useful as an extensional summary.  The trace
grammar needs more: its execution object must retain the certificate and the
entire recursively chosen child history.  The following compact layers do
that, and recover the extensional relation only by continuous projection.
-/

/-- One compact proof-relevant execution layer with continuous exposed node
and outcome. -/
structure CompactRankedExecutionLayer
    (Node : Type uNode) (Outcome : Type uOutcome) [TopologicalSpace Node]
    [TopologicalSpace Outcome] where
  Execution : Type uExecution
  executionTopology : TopologicalSpace Execution
  executionCompact : @CompactSpace Execution executionTopology
  executionFirstCountable :
    @FirstCountableTopology Execution executionTopology
  executionT2 : @T2Space Execution executionTopology
  source : Execution → Node
  outcome : Execution → Outcome
  source_continuous : @Continuous Execution Node executionTopology
    inferInstance source
  outcome_continuous : @Continuous Execution Outcome executionTopology
    inferInstance outcome

namespace CompactRankedExecutionLayer

/-- Finite disjoint union of two proof-relevant execution layers. -/
def sum
    (first second : CompactRankedExecutionLayer Node Outcome) :
    CompactRankedExecutionLayer Node Outcome := by
  letI : TopologicalSpace first.Execution := first.executionTopology
  letI : CompactSpace first.Execution := first.executionCompact
  letI : FirstCountableTopology first.Execution :=
    first.executionFirstCountable
  letI : T2Space first.Execution := first.executionT2
  letI : TopologicalSpace second.Execution := second.executionTopology
  letI : CompactSpace second.Execution := second.executionCompact
  letI : FirstCountableTopology second.Execution :=
    second.executionFirstCountable
  letI : T2Space second.Execution := second.executionT2
  let sumFirstCountable :
      FirstCountableTopology (first.Execution ⊕ second.Execution) :=
    ⟨by
      intro execution
      cases execution with
      | inl execution =>
          rw [nhds_inl]
          infer_instance
      | inr execution =>
          rw [nhds_inr]
          infer_instance⟩
  exact {
    Execution := first.Execution ⊕ second.Execution
    executionTopology := inferInstance
    executionCompact := inferInstance
    executionFirstCountable := sumFirstCountable
    executionT2 := inferInstance
    source := Sum.elim first.source second.source
    outcome := Sum.elim first.outcome second.outcome
    source_continuous :=
      first.source_continuous.sumElim second.source_continuous
    outcome_continuous :=
      first.outcome_continuous.sumElim second.outcome_continuous }

end CompactRankedExecutionLayer

/-- A terminal execution retains the parent and its terminal certificate. -/
def terminalExecutionLayer
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    (level : ℕ) :
    CompactRankedExecutionLayer.{uNode, uOutcome,
      max uNode (max uTerminal uSuccessor)} Node Outcome := by
  let BaseExecution := adapter.terminalDomain level
  let Execution := ULift.{uSuccessor} BaseExecution
  let topology : TopologicalSpace Execution := inferInstance
  letI : CompactSpace BaseExecution := isCompact_iff_compactSpace.mp
    (adapter.isCompact_terminalDomain level)
  let compact : CompactSpace Execution := inferInstance
  let firstCountable : FirstCountableTopology Execution :=
    Homeomorph.ulift.isEmbedding.firstCountableTopology
  let t2 : T2Space Execution := inferInstance
  exact {
    Execution := Execution
    executionTopology := topology
    executionCompact := compact
    executionFirstCountable := firstCountable
    executionT2 := t2
    source := fun execution ↦ execution.down.1.1
    outcome := fun execution ↦ adapter.consume execution.down.1
    source_continuous := (continuous_fst.comp continuous_subtype_val).comp
      continuous_uliftDown
    outcome_continuous :=
      (adapter.consume_continuous.comp continuous_subtype_val).comp
        continuous_uliftDown }

/-- A successor execution retains the parent certificate, the literal child,
and one complete proof-relevant execution of that child. -/
def successorExecutionSet
    (level : ℕ)
    (lower : CompactRankedExecutionLayer.{uNode, uOutcome,
      max uNode (max uTerminal uSuccessor)} Node Outcome) :
    Set (((Node × SuccessorCertificate) × Node) × lower.Execution) :=
  {point |
    point.1.1.1 ∈ adapter.nodeSet ∧
      adapter.rank point.1.1.1 = level ∧
      point.1.1.2 ∈ adapter.successorCertificateSet ∧
      point.1.2 ∈ adapter.nodeSet ∧
      adapter.successor point.1.1.1 point.1.1.2 point.1.2 ∧
      point.1.2 = lower.source point.2}

theorem isCompact_successorExecutionSet
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    (level : ℕ)
    (lower : CompactRankedExecutionLayer.{uNode, uOutcome,
      max uNode (max uTerminal uSuccessor)} Node Outcome) :
    letI : TopologicalSpace lower.Execution := lower.executionTopology
    IsCompact (adapter.successorExecutionSet level lower) := by
  letI : TopologicalSpace lower.Execution := lower.executionTopology
  letI : CompactSpace lower.Execution := lower.executionCompact
  let graph : Set ((Node × SuccessorCertificate) × Node) :=
    {edge |
      edge.1.1 ∈ adapter.nodeSet ∧ adapter.rank edge.1.1 = level ∧
        edge.1.2 ∈ adapter.successorCertificateSet ∧
        edge.2 ∈ adapter.nodeSet ∧
        adapter.successor edge.1.1 edge.1.2 edge.2}
  have hgraphProduct := (adapter.level_compact level).prod
    adapter.successorCertificate_compact |>.prod adapter.node_compact
  have hgraph : IsCompact graph := by
    exact hgraphProduct.of_isClosed_subset
      (by simpa only [graph] using adapter.successorGraph_closed level) <| by
        intro edge hedge
        exact ⟨⟨⟨hedge.1, hedge.2.1⟩, hedge.2.2.1⟩, hedge.2.2.2.1⟩
  let ambient : Set
      (((Node × SuccessorCertificate) × Node) × lower.Execution) :=
    graph ×ˢ Set.univ
  have hambient : IsCompact ambient := hgraph.prod isCompact_univ
  have hequality : IsClosed
      {point : ((Node × SuccessorCertificate) × Node) × lower.Execution |
        point.1.2 = lower.source point.2} := by
    exact isClosed_eq
      (continuous_snd.comp continuous_fst)
      (lower.source_continuous.comp continuous_snd)
  have heq : adapter.successorExecutionSet level lower =
      ambient ∩
        {point : ((Node × SuccessorCertificate) × Node) × lower.Execution |
          point.1.2 = lower.source point.2} := by
    ext point
    simp only [successorExecutionSet, ambient, graph, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true]
    tauto
  rw [heq]
  exact hambient.inter_right hequality

/-- Compact layer of successor executions above a lower-rank layer. -/
def successorExecutionLayer
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    (level : ℕ)
    (lower : CompactRankedExecutionLayer.{uNode, uOutcome,
      max uNode (max uTerminal uSuccessor)} Node Outcome) :
    CompactRankedExecutionLayer.{uNode, uOutcome,
      max uNode (max uTerminal uSuccessor)} Node Outcome := by
  letI : TopologicalSpace lower.Execution := lower.executionTopology
  letI : CompactSpace lower.Execution := lower.executionCompact
  letI : FirstCountableTopology lower.Execution :=
    lower.executionFirstCountable
  letI : T2Space lower.Execution := lower.executionT2
  let Execution := adapter.successorExecutionSet level lower
  let topology : TopologicalSpace Execution := inferInstance
  let compact : CompactSpace Execution := isCompact_iff_compactSpace.mp
    (by simpa using adapter.isCompact_successorExecutionSet level lower)
  let firstCountable : FirstCountableTopology Execution := inferInstance
  let t2 : T2Space Execution := inferInstance
  exact {
    Execution := Execution
    executionTopology := topology
    executionCompact := compact
    executionFirstCountable := firstCountable
    executionT2 := t2
    source := fun execution ↦ execution.1.1.1.1
    outcome := fun execution ↦
      adapter.back (execution.1.1, lower.outcome execution.1.2)
    source_continuous := by
      exact (((continuous_fst.comp continuous_fst).comp
        continuous_fst).comp continuous_subtype_val)
    outcome_continuous := by
      exact adapter.back_continuous.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          (lower.outcome_continuous.comp
            (continuous_snd.comp continuous_subtype_val))) }

/-- All proof-relevant ranked histories of rank at most `level`.  The old arm
is retained, the new terminal arm stores its terminal certificate, and the
new successor arm stores its certificate and recursive child execution. -/
noncomputable def executionLayer
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate] :
    ℕ → CompactRankedExecutionLayer.{uNode, uOutcome,
      max uNode (max uTerminal uSuccessor)} Node Outcome
  | 0 => adapter.terminalExecutionLayer 0
  | level + 1 =>
      let lower := executionLayer level
      CompactRankedExecutionLayer.sum lower <|
        CompactRankedExecutionLayer.sum
          (terminalExecutionLayer adapter (level + 1)) <|
            successorExecutionLayer adapter (level + 1) lower

/-- The genuine proof-relevant bounded execution type. -/
abbrev ExecutionUpTo
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    (level : ℕ) : Type _ :=
  (adapter.executionLayer level).Execution

noncomputable instance executionUpToTopology
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    (level : ℕ) : TopologicalSpace (adapter.ExecutionUpTo level) :=
  (adapter.executionLayer level).executionTopology

noncomputable instance executionUpToCompact
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    (level : ℕ) : CompactSpace (adapter.ExecutionUpTo level) :=
  (adapter.executionLayer level).executionCompact

noncomputable instance executionUpToFirstCountable
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    (level : ℕ) : FirstCountableTopology (adapter.ExecutionUpTo level) :=
  (adapter.executionLayer level).executionFirstCountable

noncomputable instance executionUpToT2
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    (level : ℕ) : T2Space (adapter.ExecutionUpTo level) :=
  (adapter.executionLayer level).executionT2

/-- Exposed source node of a proof-relevant ranked execution. -/
def executionSource
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    {level : ℕ} : adapter.ExecutionUpTo level → Node :=
  (adapter.executionLayer level).source

/-- Compiled outcome of a proof-relevant ranked execution. -/
def executionOutcome
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    {level : ℕ} : adapter.ExecutionUpTo level → Outcome :=
  (adapter.executionLayer level).outcome

/-- Continuous extensional projection of one retained execution history. -/
def executionProjection
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    {level : ℕ} : adapter.ExecutionUpTo level → Node × Outcome :=
  fun execution ↦
    (adapter.executionSource execution, adapter.executionOutcome execution)

theorem continuous_executionProjection
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    (level : ℕ) : Continuous
      (@executionProjection Node TerminalCertificate SuccessorCertificate
        Outcome _ _ _ _ adapter _ _ _ _ _ _ level) :=
  (adapter.executionLayer level).source_continuous.prodMk
    (adapter.executionLayer level).outcome_continuous

/-- The extensional bounded outcome relation is derived from retained
execution histories by projection. -/
def projectedOutcomeSet
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    (level : ℕ) : Set (Node × Outcome) :=
  Set.range (@executionProjection Node TerminalCertificate
    SuccessorCertificate Outcome _ _ _ _ adapter _ _ _ _ _ _ level)

theorem isCompact_projectedOutcomeSet
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    (level : ℕ) : IsCompact (adapter.projectedOutcomeSet level) := by
  exact isCompact_range (adapter.continuous_executionProjection level)

theorem isClosed_projectedOutcomeSet
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    [T2Space Outcome] (level : ℕ) :
    IsClosed (adapter.projectedOutcomeSet level) :=
  (adapter.isCompact_projectedOutcomeSet level).isClosed

/-- Forgetting a retained recursive history gives exactly the earlier
extensional recursion, so consumers phrased with `outcomeUpTo` and the trace
evaluator's proof-relevant carrier describe the same complete relation. -/
theorem projectedOutcomeSet_eq_outcomeUpTo
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate] : ∀ level,
    adapter.projectedOutcomeSet level = adapter.outcomeUpTo level
  | 0 => by
      ext point
      constructor
      · rintro ⟨execution, rfl⟩
        let terminalExecution := execution.down
        exact ⟨terminalExecution.1, terminalExecution.2, rfl⟩
      · rintro ⟨terminalExecution, hterminalExecution, rfl⟩
        exact ⟨ULift.up ⟨terminalExecution, hterminalExecution⟩, rfl⟩
  | level + 1 => by
      ext point
      constructor
      · rintro ⟨execution, rfl⟩
        rcases execution with lowerExecution | newExecution
        · exact Or.inl <| Or.inl <| by
            rw [← projectedOutcomeSet_eq_outcomeUpTo level]
            exact ⟨lowerExecution, rfl⟩
        · rcases newExecution with terminalExecution | successorExecution
          · exact Or.inl <| Or.inr <|
              ⟨terminalExecution.down.1, terminalExecution.down.2, rfl⟩
          · rcases successorExecution with
              ⟨⟨edge, childExecution⟩, hsuccessor⟩
            refine Or.inr ⟨(edge,
              ((adapter.executionLayer level).source childExecution,
                (adapter.executionLayer level).outcome childExecution)), ?_, rfl⟩
            refine ⟨hsuccessor.1, hsuccessor.2.1, hsuccessor.2.2.1,
              hsuccessor.2.2.2.1, hsuccessor.2.2.2.2.1, ?_, ?_⟩
            · rw [← projectedOutcomeSet_eq_outcomeUpTo level]
              exact ⟨childExecution, rfl⟩
            · exact hsuccessor.2.2.2.2.2
      · intro hpoint
        rcases hpoint with hlower | hsuccessor
        · rcases hlower with hlower | hterminal
          · rw [← projectedOutcomeSet_eq_outcomeUpTo level] at hlower
            obtain ⟨execution, hexecution⟩ := hlower
            exact ⟨Sum.inl execution, hexecution⟩
          · obtain ⟨terminalExecution, hterminalExecution, hpoint⟩ := hterminal
            subst point
            exact ⟨Sum.inr (Sum.inl <|
              ULift.up ⟨terminalExecution, hterminalExecution⟩), rfl⟩
        · obtain ⟨successorPoint, hsuccessorPoint, hpoint⟩ := hsuccessor
          rcases successorPoint with ⟨edge, childPoint⟩
          rw [← projectedOutcomeSet_eq_outcomeUpTo level] at hsuccessorPoint
          obtain ⟨childExecution, hchildExecution⟩ :=
            hsuccessorPoint.2.2.2.2.2.1
          have hchildSource : edge.2 =
              (adapter.executionLayer level).source childExecution := by
            rw [hsuccessorPoint.2.2.2.2.2.2]
            exact (congrArg Prod.fst hchildExecution).symm
          let execution : adapter.successorExecutionSet (level + 1)
              (adapter.executionLayer level) :=
            ⟨(edge, childExecution), hsuccessorPoint.1,
              hsuccessorPoint.2.1, hsuccessorPoint.2.2.1,
              hsuccessorPoint.2.2.2.1, hsuccessorPoint.2.2.2.2.1,
                hchildSource⟩
          refine ⟨Sum.inr (Sum.inr execution), ?_⟩
          rw [← hpoint]
          apply Prod.ext
          · rfl
          · exact congrArg
              (fun outcome ↦ adapter.back (edge, outcome))
              (congrArg Prod.snd hchildExecution)

/-- Every certified node of rank at most `level` has a retained recursive
execution beginning at that literal node. -/
theorem exists_execution_of_rank_le
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate] : ∀ level node,
    node ∈ adapter.nodeSet → adapter.rank node ≤ level →
      ∃ execution : adapter.ExecutionUpTo level,
        adapter.executionSource execution = node
  | 0, node, hnode, hrank => by
      have hrankZero : adapter.rank node = 0 := by omega
      rcases adapter.complete node hnode with hterminal | hsuccessor
      · obtain ⟨certificate, hcertificate, hterminal⟩ := hterminal
        let execution : adapter.terminalDomain 0 :=
          ⟨(node, certificate), hnode, hrankZero, hcertificate, hterminal⟩
        exact ⟨ULift.up execution, rfl⟩
      · obtain ⟨certificate, child, _, _, hsuccessor⟩ := hsuccessor
        have := adapter.successor_rank_lt node certificate child hsuccessor
        omega
  | level + 1, node, hnode, hrank => by
      by_cases hlower : adapter.rank node ≤ level
      · obtain ⟨execution, hsource⟩ :=
          exists_execution_of_rank_le level node hnode hlower
        exact ⟨Sum.inl execution, hsource⟩
      · have hrankTop : adapter.rank node = level + 1 := by omega
        rcases adapter.complete node hnode with hterminal | hsuccessor
        · obtain ⟨certificate, hcertificate, hterminal⟩ := hterminal
          let execution : adapter.terminalDomain (level + 1) :=
            ⟨(node, certificate), hnode, hrankTop, hcertificate, hterminal⟩
          exact ⟨Sum.inr (Sum.inl (ULift.up execution)), rfl⟩
        · obtain ⟨certificate, child, hcertificate, hchild,
              hsuccessor⟩ := hsuccessor
          have hchildRank : adapter.rank child ≤ level := by
            have := adapter.successor_rank_lt
              node certificate child hsuccessor
            omega
          obtain ⟨childExecution, hchildSource⟩ :=
            exists_execution_of_rank_le level child hchild hchildRank
          let execution : adapter.successorExecutionSet (level + 1)
              (adapter.executionLayer level) :=
            ⟨(((node, certificate), child), childExecution),
              hnode, hrankTop, hcertificate, hchild, hsuccessor,
                hchildSource.symm⟩
          exact ⟨Sum.inr (Sum.inr execution), rfl⟩

/-- The projected compact relation is total over the certified node set at
the global rank bound. -/
theorem exists_projectedOutcome
    [FirstCountableTopology Node] [T2Space Node]
    [FirstCountableTopology TerminalCertificate]
    [T2Space TerminalCertificate]
    [FirstCountableTopology SuccessorCertificate]
    [T2Space SuccessorCertificate]
    {node : Node} (hnode : node ∈ adapter.nodeSet) :
    ∃ outcome, (node, outcome) ∈
      adapter.projectedOutcomeSet adapter.rankBound := by
  obtain ⟨execution, hsource⟩ := adapter.exists_execution_of_rank_le
    adapter.rankBound node hnode (adapter.rank_le node hnode)
  refine ⟨adapter.executionOutcome execution, execution, ?_⟩
  exact Prod.ext hsource rfl

/-- Every node at its literal rank has a compiled outcome at that rank. -/
theorem exists_outcome_at_rank
    [T2Space Node] : ∀ level node,
    node ∈ adapter.nodeSet → adapter.rank node = level →
      ∃ outcome, (node, outcome) ∈ outcomeUpTo adapter level
  | 0, node, hnode, hrank => by
      rcases adapter.complete node hnode with hterminal | hsuccessor
      · obtain ⟨certificate, hcertificate, hterminal⟩ := hterminal
        exact ⟨adapter.consume (node, certificate),
          ⟨(node, certificate),
            ⟨hnode, hrank, hcertificate, hterminal⟩, rfl⟩⟩
      · obtain ⟨certificate, child, _, _, hsuccessor⟩ := hsuccessor
        have := adapter.successor_rank_lt node certificate child hsuccessor
        omega
  | level + 1, node, hnode, hrank => by
      rcases adapter.complete node hnode with hterminal | hsuccessor
      · obtain ⟨certificate, hcertificate, hterminal⟩ := hterminal
        exact ⟨adapter.consume (node, certificate), Or.inl <| Or.inr <|
          ⟨(node, certificate),
            ⟨hnode, hrank, hcertificate, hterminal⟩, rfl⟩⟩
      · obtain ⟨certificate, child, hcertificate, hchild, hsuccessor⟩ := hsuccessor
        have hchildRank := adapter.successor_rank_lt
          node certificate child hsuccessor
        have hchildLe : adapter.rank child ≤ level := by omega
        obtain ⟨childOutcome, hchildOutcome⟩ :=
          exists_outcome_at_rank (adapter.rank child) child hchild rfl
        have hchildOutcome' :
            (child, childOutcome) ∈ outcomeUpTo adapter level :=
          outcomeUpTo_mono_of_le adapter hchildLe hchildOutcome
        exact ⟨adapter.back (((node, certificate), child), childOutcome),
          Or.inr <| ⟨(((node, certificate), child),
            (child, childOutcome)),
              ⟨hnode, hrank, hcertificate, hchild, hsuccessor,
                hchildOutcome', rfl⟩, rfl⟩⟩

/-- The final bounded relation is total over the certified node box. -/
theorem exists_outcome
    [T2Space Node]
    {node : Node} (hnode : node ∈ adapter.nodeSet) :
    ∃ outcome, (node, outcome) ∈ outcomeUpTo adapter adapter.rankBound := by
  obtain ⟨outcome, houtcome⟩ := exists_outcome_at_rank adapter
    (adapter.rank node) node hnode rfl
  exact ⟨outcome,
    adapter.outcomeUpTo_mono_of_le (adapter.rank_le node hnode) houtcome⟩

end CompactRankedOutcomeAdapter

/-! ## Pointwise post-limit rank -/

/-- A topology-free ranked producer applied to one already reconstructed
node.  It is intentionally not a trace-visible constructor. -/
structure PointwiseRankedProducer (Node Outcome : Type*) where
  rank : Node → ℕ
  terminal : Node → Prop
  consume : ∀ node, terminal node → Outcome
  isChild : Node → Node → Prop
  child_rank_lt : ∀ parent child,
    isChild parent child → rank child < rank parent
  back : ∀ parent child, isChild parent child → Outcome → Outcome
  complete : ∀ node, terminal node ∨ ∃ next, isChild node next

namespace PointwiseRankedProducer

variable {PointwiseNode PointwiseOutcome : Type*}
  (producer : PointwiseRankedProducer PointwiseNode PointwiseOutcome)

/-- Proof-relevant outcomes of topology-free pointwise recursion. -/
inductive IsOutcome : PointwiseNode → PointwiseOutcome → Prop
  | terminal (node : PointwiseNode) (certificate : producer.terminal node) :
      IsOutcome node (producer.consume node certificate)
  | successor (parent child : PointwiseNode)
      (edge : producer.isChild parent child) (outcome : PointwiseOutcome)
      (childOutcome : IsOutcome child outcome) :
      IsOutcome parent (producer.back parent child edge outcome)

/-- Natural-valued rank suffices for one pointwise outcome.  No continuity or
closed trace relation follows. -/
  theorem exists_outcome (node : PointwiseNode) :
    ∃ outcome, producer.IsOutcome node outcome := by
  induction node using WellFounded.induction
    (measure producer.rank).wf with
  | h node ih =>
      rcases producer.complete node with hterminal | hchild
      · exact ⟨producer.consume node hterminal,
          IsOutcome.terminal node hterminal⟩
      · obtain ⟨child, hedge⟩ := hchild
        obtain ⟨outcome, houtcome⟩ := ih child
          (producer.child_rank_lt node child hedge)
        exact ⟨producer.back node child hedge outcome,
          IsOutcome.successor node child hedge outcome houtcome⟩

end PointwiseRankedProducer

end Topology
end Math
