/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact proof-relevant executable adapters

This file isolates the topological core of a compact-witness adapter.  An
execution retains its witness, visible label, and compiled child.  Projecting
away the witness is a separate theorem; it is not the definition of an
execution.

The syntax tag below records only the trace-visible constructor class.  A
pointwise recursion performed after a limit is reconstructed is deliberately
not one of its constructors.
-/

noncomputable section

namespace Math
namespace Topology

/-- The trace-visible constructors of the executable adapter grammar. -/
inductive ExecutableTraceConstructorKind
  | compactWitness
  | summableDecoder
  | closedCase
  | boundedRank
  | composition
  deriving DecidableEq, Repr

/-- A compact-witness adapter with an explicit closed legality relation.
The compiler and visible-label maps are total functions whose continuity is
required only on the legal compact relation. -/
structure CompactProofRelevantAdapter
    (Parent Witness Label Child : Type*)
    [TopologicalSpace Parent] [TopologicalSpace Witness]
    [TopologicalSpace Label] [TopologicalSpace Child] where
  parentSet : Set Parent
  witnessSet : Set Witness
  legal : Parent → Witness → Prop
  parent_compact : IsCompact parentSet
  witness_compact : IsCompact witnessSet
  legal_closed : IsClosed
    {point : Parent × Witness |
      point.1 ∈ parentSet ∧ point.2 ∈ witnessSet ∧ legal point.1 point.2}
  total : ∀ parent, parent ∈ parentSet →
    ∃ witness, witness ∈ witnessSet ∧ legal parent witness
  compile : Parent × Witness → Child
  label : Parent × Witness → Label
  compile_continuousOn : ContinuousOn compile
    {point : Parent × Witness |
      point.1 ∈ parentSet ∧ point.2 ∈ witnessSet ∧ legal point.1 point.2}
  label_continuousOn : ContinuousOn label
    {point : Parent × Witness |
      point.1 ∈ parentSet ∧ point.2 ∈ witnessSet ∧ legal point.1 point.2}

namespace CompactProofRelevantAdapter

variable {Parent Witness Label Child : Type*}
  [TopologicalSpace Parent] [TopologicalSpace Witness]
  [TopologicalSpace Label] [TopologicalSpace Child]

/-- The compact relation of legal parent/witness pairs. -/
def legalSet
    (adapter : CompactProofRelevantAdapter Parent Witness Label Child) :
    Set (Parent × Witness) :=
  {point |
    point.1 ∈ adapter.parentSet ∧ point.2 ∈ adapter.witnessSet ∧
      adapter.legal point.1 point.2}

/-- A proof-relevant output retains the exact witness. -/
def executionOutput
    (adapter : CompactProofRelevantAdapter Parent Witness Label Child)
    (point : Parent × Witness) :
    (Parent × Witness) × Label × Child :=
  (point, adapter.label point, adapter.compile point)

/-- The complete proof-relevant execution relation. -/
def executionSet
    (adapter : CompactProofRelevantAdapter Parent Witness Label Child) :
    Set ((Parent × Witness) × Label × Child) :=
  adapter.executionOutput '' adapter.legalSet

/-- Projection which forgets the proof witness but retains parent, label, and
actual compiled child. -/
def visibleProjection
    (output : (Parent × Witness) × Label × Child) :
    Parent × Label × Child :=
  (output.1.1, output.2.1, output.2.2)

/-- Visible output relation after explicitly projecting the witness. -/
def visibleSet
    (adapter : CompactProofRelevantAdapter Parent Witness Label Child) :
    Set (Parent × Label × Child) :=
  visibleProjection '' adapter.executionSet

theorem isCompact_legalSet
    (adapter : CompactProofRelevantAdapter Parent Witness Label Child) :
    IsCompact adapter.legalSet := by
  have hproduct := adapter.parent_compact.prod adapter.witness_compact
  exact hproduct.of_isClosed_subset adapter.legal_closed fun point hpoint ↦
    ⟨hpoint.1, hpoint.2.1⟩

theorem continuousOn_executionOutput
    (adapter : CompactProofRelevantAdapter Parent Witness Label Child) :
    ContinuousOn adapter.executionOutput adapter.legalSet := by
  exact continuousOn_id.prodMk
    (adapter.label_continuousOn.prodMk adapter.compile_continuousOn)

/-- A compact-witness adapter has a compact proof-relevant execution set. -/
theorem isCompact_executionSet
    (adapter : CompactProofRelevantAdapter Parent Witness Label Child) :
    IsCompact adapter.executionSet := by
  exact (isCompact_legalSet adapter).image_of_continuousOn
    (continuousOn_executionOutput adapter)

theorem continuous_visibleProjection :
    Continuous
      (visibleProjection :
        ((Parent × Witness) × Label × Child) → Parent × Label × Child) := by
  change Continuous fun
    output : ((Parent × Witness) × Label × Child) ↦
      (output.1.1, output.2.1, output.2.2)
  fun_prop

/-- Existentially forgetting the compact witness preserves compactness. -/
theorem isCompact_visibleSet
    (adapter : CompactProofRelevantAdapter Parent Witness Label Child) :
    IsCompact adapter.visibleSet := by
  exact (isCompact_executionSet adapter).image continuous_visibleProjection

/-- The proof-relevant execution relation is closed in a Hausdorff output
space. -/
theorem isClosed_executionSet
    [T2Space Parent] [T2Space Witness] [T2Space Label] [T2Space Child]
    (adapter : CompactProofRelevantAdapter Parent Witness Label Child) :
    IsClosed adapter.executionSet :=
  (isCompact_executionSet adapter).isClosed

/-- The projected visible output relation is closed in a Hausdorff output
space. -/
theorem isClosed_visibleSet
    [T2Space Parent] [T2Space Label] [T2Space Child]
    (adapter : CompactProofRelevantAdapter Parent Witness Label Child) :
    IsClosed adapter.visibleSet :=
  (isCompact_visibleSet adapter).isClosed

/-- Totality of the witness relation produces a proof-relevant execution for
every certified parent. -/
theorem exists_executionOutput
    (adapter : CompactProofRelevantAdapter Parent Witness Label Child)
    {parent : Parent} (hparent : parent ∈ adapter.parentSet) :
    ∃ witness label child,
      ((parent, witness), label, child) ∈ adapter.executionSet := by
  obtain ⟨witness, hwitness, hlegal⟩ := adapter.total parent hparent
  exact ⟨witness, adapter.label (parent, witness),
    adapter.compile (parent, witness), ⟨(parent, witness),
      ⟨hparent, hwitness, hlegal⟩, rfl⟩⟩

end CompactProofRelevantAdapter

section ClosedCase

/-- A finite closed case split.  Every branch remains proof-relevant; branch
overlap is allowed, while the cover field rules out an unrecorded open test. -/
structure CompactClosedCaseAdapter
    (Branch Parent Witness Label Child : Type*)
    [Fintype Branch] [TopologicalSpace Branch]
    [TopologicalSpace Parent] [TopologicalSpace Witness]
    [TopologicalSpace Label] [TopologicalSpace Child] where
  branch : Branch → CompactProofRelevantAdapter Parent Witness Label Child
  parentSet : Set Parent
  parent_compact : IsCompact parentSet
  same_parent : ∀ tag, (branch tag).parentSet = parentSet
  cover : ∀ parent, parent ∈ parentSet →
    ∃ tag witness,
      witness ∈ (branch tag).witnessSet ∧ (branch tag).legal parent witness

namespace CompactClosedCaseAdapter

variable {Branch Parent Witness Label Child : Type*}
  [Fintype Branch] [TopologicalSpace Branch]
  [TopologicalSpace Parent] [TopologicalSpace Witness]
  [TopologicalSpace Label] [TopologicalSpace Child]

/-- Tagged proof-relevant executions of a finite closed case split. -/
def executionSet
    (adapter : CompactClosedCaseAdapter Branch Parent Witness Label Child) :
    Set (Branch × ((Parent × Witness) × Label × Child)) :=
  {output | output.2 ∈ (adapter.branch output.1).executionSet}

/-- The tagged execution set of a finite closed case split is compact. -/
theorem isCompact_executionSet
    [DiscreteTopology Branch]
    (adapter : CompactClosedCaseAdapter Branch Parent Witness Label Child) :
    IsCompact adapter.executionSet := by
  rw [show adapter.executionSet =
      ⋃ tag : Branch,
        (fun output ↦ (tag, output)) '' (adapter.branch tag).executionSet by
    ext output
    constructor
    · intro houtput
      exact Set.mem_iUnion.2
        ⟨output.1, ⟨output.2, houtput, rfl⟩⟩
    · intro houtput
      obtain ⟨tag, value, hvalue, heq⟩ := Set.mem_iUnion.1 houtput
      simpa [executionSet] using heq ▸ hvalue]
  exact isCompact_iUnion fun tag ↦
    ((adapter.branch tag).isCompact_executionSet).image <| by fun_prop

/-- The finite tagged case relation is closed in Hausdorff output spaces. -/
theorem isClosed_executionSet
    [DiscreteTopology Branch]
    [T2Space Parent] [T2Space Witness] [T2Space Label] [T2Space Child]
    (adapter : CompactClosedCaseAdapter Branch Parent Witness Label Child) :
    IsClosed adapter.executionSet :=
  adapter.isCompact_executionSet.isClosed

/-- Every certified parent occurs in some tagged proof-relevant branch. -/
theorem exists_executionOutput
    (adapter : CompactClosedCaseAdapter Branch Parent Witness Label Child)
    {parent : Parent} (hparent : parent ∈ adapter.parentSet) :
    ∃ tag witness label child,
      (tag, ((parent, witness), label, child)) ∈ adapter.executionSet := by
  obtain ⟨tag, witness, hwitness, hlegal⟩ := adapter.cover parent hparent
  refine ⟨tag, witness, (adapter.branch tag).label (parent, witness),
    (adapter.branch tag).compile (parent, witness), ?_⟩
  exact ⟨(parent, witness),
    ⟨by simpa [adapter.same_parent tag] using hparent, hwitness, hlegal⟩, rfl⟩

end CompactClosedCaseAdapter
end ClosedCase

end Topology
end Math
