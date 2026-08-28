/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Dependent compact inverse limits from finite compatible prefixes

The compact carrier at level `time` may have a different type from the
carrier at every other level.  If every finite family of adjacent relation
constraints is simultaneously realizable, compactness supplies one section
which satisfies all constraints.

This theorem does not turn separate nonempty fibers into a compatible
section.  The finite-prefix hypothesis is the exact finite-intersection datum
needed to avoid an inconsistent sequence of independent choices.
-/

noncomputable section

namespace Math
namespace Topology

variable {Point : ℕ → Type*} [∀ time, TopologicalSpace (Point time)]

/-- Dependent sections satisfying the first `horizon` adjacent constraints. -/
def compactDependentFinitePrefixSolutionSet
    (box : ∀ time, Set (Point time))
    (relation : ∀ time, Point time → Point (time + 1) → Prop)
    (horizon : ℕ) : Set (∀ time, Point time) :=
  {value |
    (∀ time, value time ∈ box time) ∧
      ∀ time : Fin horizon,
        relation time (value time) (value (time + 1))}

omit [∀ time, TopologicalSpace (Point time)] in
/-- Adding one adjacent constraint shrinks the dependent prefix set. -/
theorem compactDependentFinitePrefixSolutionSet_succ_subset
    (box : ∀ time, Set (Point time))
    (relation : ∀ time, Point time → Point (time + 1) → Prop)
    (horizon : ℕ) :
    compactDependentFinitePrefixSolutionSet box relation (horizon + 1) ⊆
      compactDependentFinitePrefixSolutionSet box relation horizon := by
  intro value hvalue
  refine ⟨hvalue.1, fun time ↦ ?_⟩
  exact hvalue.2 ⟨time, lt_trans time.isLt (Nat.lt_succ_self horizon)⟩

variable [∀ time, T2Space (Point time)]

/-- Compact fibers and closed adjacent graphs make every dependent prefix
solution set closed in the full dependent product. -/
theorem compactDependentFinitePrefixSolutionSet_isClosed
    (box : ∀ time, Set (Point time))
    (relation : ∀ time, Point time → Point (time + 1) → Prop)
    (hbox : ∀ time, IsCompact (box time))
    (hgraph : ∀ time, IsClosed
      {pair : Point time × Point (time + 1) |
        pair.1 ∈ box time ∧ pair.2 ∈ box (time + 1) ∧
          relation time pair.1 pair.2})
    (horizon : ℕ) :
    IsClosed (compactDependentFinitePrefixSolutionSet box relation horizon) := by
  let ambient : Set (∀ time, Point time) :=
    {value | ∀ time, value time ∈ box time}
  have hambientCompact : IsCompact ambient := by
    dsimp only [ambient]
    exact isCompact_pi_infinite hbox
  have hambientClosed : IsClosed ambient := hambientCompact.isClosed
  let relationGraph (time : ℕ) : Set (Point time × Point (time + 1)) :=
    {pair |
      pair.1 ∈ box time ∧ pair.2 ∈ box (time + 1) ∧
        relation time pair.1 pair.2}
  have hconstraint : ∀ time : Fin horizon,
      IsClosed {value : ∀ current, Point current |
        (value time, value (time + 1)) ∈ relationGraph time} := by
    intro time
    have hpair : Continuous (fun value : ∀ current, Point current ↦
        (value time, value ((time : ℕ) + 1))) :=
      (continuous_apply (time : ℕ)).prodMk
        (continuous_apply ((time : ℕ) + 1))
    apply IsClosed.preimage hpair
    simpa only [relationGraph] using hgraph time
  have hclosed : IsClosed
      (ambient ∩ ⋂ time : Fin horizon,
        {value : ∀ current, Point current |
          (value time, value (time + 1)) ∈ relationGraph time}) :=
    hambientClosed.inter (isClosed_iInter hconstraint)
  have heq : compactDependentFinitePrefixSolutionSet box relation horizon =
      ambient ∩ ⋂ time : Fin horizon,
        {value : ∀ current, Point current |
          (value time, value (time + 1)) ∈ relationGraph time} := by
    ext value
    simp only [compactDependentFinitePrefixSolutionSet, ambient,
      relationGraph, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro hvalue
      exact ⟨hvalue.1, fun time ↦
        ⟨hvalue.1 time, hvalue.1 ((time : ℕ) + 1), hvalue.2 time⟩⟩
    · intro hvalue
      exact ⟨hvalue.1, fun time ↦ (hvalue.2 time).2.2⟩
  rw [heq]
  exact hclosed

/-- Every dependent finite-prefix solution set is compact. -/
theorem compactDependentFinitePrefixSolutionSet_isCompact
    (box : ∀ time, Set (Point time))
    (relation : ∀ time, Point time → Point (time + 1) → Prop)
    (hbox : ∀ time, IsCompact (box time))
    (hgraph : ∀ time, IsClosed
      {pair : Point time × Point (time + 1) |
        pair.1 ∈ box time ∧ pair.2 ∈ box (time + 1) ∧
          relation time pair.1 pair.2})
    (horizon : ℕ) :
    IsCompact (compactDependentFinitePrefixSolutionSet
      box relation horizon) := by
  have hambient : IsCompact
      {value : ∀ time, Point time | ∀ time, value time ∈ box time} :=
    isCompact_pi_infinite hbox
  exact hambient.of_isClosed_subset
    (compactDependentFinitePrefixSolutionSet_isClosed
      box relation hbox hgraph horizon)
    (fun _ hvalue ↦ hvalue.1)

/-- **Dependent compact finite-prefix inverse limit.**  Simultaneous
realizability at every finite depth, rather than separate pointwise
nonemptiness, produces one globally compatible dependent section. -/
theorem exists_dependentInfiniteChain_of_finitePrefixes
    (box : ∀ time, Set (Point time))
    (relation : ∀ time, Point time → Point (time + 1) → Prop)
    (hbox : ∀ time, IsCompact (box time))
    (hgraph : ∀ time, IsClosed
      {pair : Point time × Point (time + 1) |
        pair.1 ∈ box time ∧ pair.2 ∈ box (time + 1) ∧
          relation time pair.1 pair.2})
    (hprefix : ∀ horizon,
      (compactDependentFinitePrefixSolutionSet
        box relation horizon).Nonempty) :
    ∃ value : ∀ time, Point time,
      (∀ time, value time ∈ box time) ∧
        ∀ time, relation time (value time) (value (time + 1)) := by
  let prefixSet : ℕ → Set (∀ time, Point time) :=
    fun horizon ↦ compactDependentFinitePrefixSolutionSet
      box relation horizon
  have hnested : ∀ horizon,
      prefixSet (horizon + 1) ⊆ prefixSet horizon :=
    compactDependentFinitePrefixSolutionSet_succ_subset box relation
  have hcompact0 : IsCompact (prefixSet 0) :=
    compactDependentFinitePrefixSolutionSet_isCompact
      box relation hbox hgraph 0
  have hclosed : ∀ horizon, IsClosed (prefixSet horizon) :=
    compactDependentFinitePrefixSolutionSet_isClosed box relation hbox hgraph
  obtain ⟨value, hvalue⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      prefixSet hnested hprefix hcompact0 hclosed
  have hprefixValue : ∀ horizon, value ∈ prefixSet horizon :=
    Set.mem_iInter.mp hvalue
  exact ⟨value, (hprefixValue 0).1, fun time ↦
    (hprefixValue (time + 1)).2 ⟨time, Nat.lt_succ_self time⟩⟩

end Topology
end Math
