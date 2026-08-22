/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.CompactBudgetedPrefixRelation
import MathUE.Topology.ExtendedOrbit

/-!
# Compact relation chains with edge budgets

Arbitrarily long finite relation prefixes satisfying every elapsed cumulative
edge-cost budget have a common infinite limit path. If the budgets tend to
infinity, that path is an extended orbit with unbounded edge-cost variation.

This is a sufficient compactness interface for Simon-type viability
questions. Its substantive input is the production of the budgeted finite
prefixes; compactness does not manufacture those prefixes from local
nonemptiness or contractibility alone.
-/

noncomputable section

namespace Math
namespace Topology

open Filter Set
open scoped BigOperators Topology

variable {Point : Type*} [TopologicalSpace Point] [T2Space Point]

/-- Relation prefixes satisfying every edge-cost budget whose cutoff has elapsed. -/
def compactEdgeBudgetedPrefixSolutionSet
    (box : Set Point) (relation : Point → Point → Prop)
    (cost : Point → Point → ℝ) (budget : ℕ → ℝ) (horizon : ℕ) :
    Set (ℕ → Point) :=
  {path |
    path ∈ compactFinitePrefixSolutionSet box relation horizon ∧
      ∀ cutoff ≤ horizon,
        budget cutoff ≤
          ∑ time ∈ Finset.range cutoff, cost (path time) (path (time + 1))}

omit [TopologicalSpace Point] [T2Space Point] in
/-- Increasing the horizon only adds relation and edge-budget constraints. -/
theorem compactEdgeBudgetedPrefixSolutionSet_succ_subset
    (box : Set Point) (relation : Point → Point → Prop)
    (cost : Point → Point → ℝ) (budget : ℕ → ℝ) (horizon : ℕ) :
    compactEdgeBudgetedPrefixSolutionSet
        box relation cost budget (horizon + 1) ⊆
      compactEdgeBudgetedPrefixSolutionSet box relation cost budget horizon := by
  intro path hpath
  refine ⟨compactFinitePrefixSolutionSet_succ_subset
    box relation horizon hpath.1, ?_⟩
  intro cutoff hcutoff
  exact hpath.2 cutoff (hcutoff.trans (Nat.le_succ horizon))

/-- Edge-budgeted prefixes form a closed set when the relation graph is
closed and the edge cost is continuous. -/
theorem compactEdgeBudgetedPrefixSolutionSet_isClosed
    (box : Set Point) (relation : Point → Point → Prop)
    (cost : Point → Point → ℝ) (budget : ℕ → ℝ)
    (hbox : IsCompact box)
    (hgraph : IsClosed
      {pair : Point × Point |
        pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2})
    (hcost : Continuous fun pair : Point × Point ↦ cost pair.1 pair.2)
    (horizon : ℕ) :
    IsClosed (compactEdgeBudgetedPrefixSolutionSet
      box relation cost budget horizon) := by
  have hprefix := compactFinitePrefixSolutionSet_isClosed
    box relation hbox hgraph horizon
  have hbudgetClosed : IsClosed {path : ℕ → Point |
      ∀ cutoff ≤ horizon,
        budget cutoff ≤
          ∑ time ∈ Finset.range cutoff,
            cost (path time) (path (time + 1))} := by
    rw [show {path : ℕ → Point |
        ∀ cutoff ≤ horizon,
          budget cutoff ≤
            ∑ time ∈ Finset.range cutoff,
              cost (path time) (path (time + 1))} =
      ⋂ cutoff : ℕ, ⋂ (_h : cutoff ≤ horizon),
        {path | budget cutoff ≤
          ∑ time ∈ Finset.range cutoff,
            cost (path time) (path (time + 1))} by
      ext path
      simp]
    apply isClosed_iInter
    intro cutoff
    apply isClosed_iInter
    intro _h
    apply isClosed_le continuous_const
    exact continuous_finsetSum _ fun time _ ↦ by
      have hpair : Continuous (fun path : ℕ → Point ↦
          (path time, path (time + 1))) :=
        (continuous_apply time).prodMk (continuous_apply (time + 1))
      change Continuous
        ((fun pair : Point × Point ↦ cost pair.1 pair.2) ∘
          fun path : ℕ → Point ↦ (path time, path (time + 1)))
      exact hcost.comp hpair
  rw [show compactEdgeBudgetedPrefixSolutionSet
      box relation cost budget horizon =
    compactFinitePrefixSolutionSet box relation horizon ∩
      {path : ℕ → Point |
        ∀ cutoff ≤ horizon,
          budget cutoff ≤
            ∑ time ∈ Finset.range cutoff,
              cost (path time) (path (time + 1))} by
    ext path
    rfl]
  exact hprefix.inter hbudgetClosed

/-- Every edge-budgeted prefix set is compact. -/
theorem compactEdgeBudgetedPrefixSolutionSet_isCompact
    (box : Set Point) (relation : Point → Point → Prop)
    (cost : Point → Point → ℝ) (budget : ℕ → ℝ)
    (hbox : IsCompact box)
    (hgraph : IsClosed
      {pair : Point × Point |
        pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2})
    (hcost : Continuous fun pair : Point × Point ↦ cost pair.1 pair.2)
    (horizon : ℕ) :
    IsCompact (compactEdgeBudgetedPrefixSolutionSet
      box relation cost budget horizon) := by
  exact (isCompact_pi_infinite fun _ ↦ hbox).of_isClosed_subset
    (compactEdgeBudgetedPrefixSolutionSet_isClosed
      box relation cost budget hbox hgraph hcost horizon)
    (fun _ hpath ↦ hpath.1.1)

/-- Arbitrarily long compatible edge-budgeted prefixes yield one infinite
relation chain satisfying every budget. -/
theorem exists_infiniteChain_of_edgeBudgetedFinitePrefixes
    (box : Set Point) (relation : Point → Point → Prop)
    (cost : Point → Point → ℝ) (budget : ℕ → ℝ)
    (hbox : IsCompact box)
    (hgraph : IsClosed
      {pair : Point × Point |
        pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2})
    (hcost : Continuous fun pair : Point × Point ↦ cost pair.1 pair.2)
    (hprefix : ∀ horizon,
      (compactEdgeBudgetedPrefixSolutionSet
        box relation cost budget horizon).Nonempty) :
    ∃ path : ℕ → Point,
      (∀ time, path time ∈ box) ∧
      (∀ time, relation (path time) (path (time + 1))) ∧
      ∀ cutoff, budget cutoff ≤
        ∑ time ∈ Finset.range cutoff,
          cost (path time) (path (time + 1)) := by
  let prefixSet : ℕ → Set (ℕ → Point) := fun horizon ↦
    compactEdgeBudgetedPrefixSolutionSet
      box relation cost budget horizon
  have hnested : ∀ horizon, prefixSet (horizon + 1) ⊆ prefixSet horizon :=
    compactEdgeBudgetedPrefixSolutionSet_succ_subset
      box relation cost budget
  have hnonempty : ∀ horizon, (prefixSet horizon).Nonempty := hprefix
  have hcompactZero : IsCompact (prefixSet 0) :=
    compactEdgeBudgetedPrefixSolutionSet_isCompact
      box relation cost budget hbox hgraph hcost 0
  have hclosed : ∀ horizon, IsClosed (prefixSet horizon) :=
    compactEdgeBudgetedPrefixSolutionSet_isClosed
      box relation cost budget hbox hgraph hcost
  obtain ⟨path, hpath⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      prefixSet hnested hnonempty hcompactZero hclosed
  have hpref : ∀ horizon, path ∈ prefixSet horizon := Set.mem_iInter.mp hpath
  refine ⟨path, (hpref 0).1.1, ?_, ?_⟩
  · intro time
    exact (hpref (time + 1)).1.2 ⟨time, Nat.lt_succ_self time⟩
  · intro cutoff
    exact (hpref cutoff).2 cutoff le_rfl

/-- Diverging finite edge budgets compile to an extended orbit with unbounded
edge-cost variation. -/
theorem exists_extendedOrbit_unboundedVariation_of_edgeBudgetedFinitePrefixes
    (box : Set Point) (relation : Point → Point → Prop)
    (cost : Point → Point → ℝ) (budget : ℕ → ℝ)
    (hbox : IsCompact box)
    (hgraph : IsClosed
      {pair : Point × Point |
        pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2})
    (hcost : Continuous fun pair : Point × Point ↦ cost pair.1 pair.2)
    (hbudget : Tendsto budget atTop atTop)
    (hprefix : ∀ horizon,
      (compactEdgeBudgetedPrefixSolutionSet
        box relation cost budget horizon).Nonempty) :
    ∃ orbit : ExtendedOrbitData (fun point ↦ {next | relation point next}),
      HasUnboundedExtendedVariationWith cost orbit := by
  obtain ⟨path, _, hrelation, hpathBudget⟩ :=
    exists_infiniteChain_of_edgeBudgetedFinitePrefixes
      box relation cost budget hbox hgraph hcost hprefix
  have hstep : IsInfiniteOrbit (fun point ↦ {next | relation point next}) path :=
    hrelation
  let orbit := ExtendedOrbitData.ofInfiniteOrbit path hstep
  refine ⟨orbit, ?_⟩
  intro bound
  obtain ⟨cutoff, hcutoff⟩ := ((tendsto_atTop.1 hbudget) bound).exists
  refine ⟨1, cutoff, ?_⟩
  rw [show orbit.prefixVariationWith cost 1 cutoff =
      ∑ time ∈ Finset.range cutoff,
        cost (path time) (path (time + 1)) by
    exact ExtendedOrbitData.prefixVariationWith_ofInfiniteOrbit
      path hstep cost cutoff]
  exact hcutoff.trans (hpathBudget cutoff)

end Topology
end Math
