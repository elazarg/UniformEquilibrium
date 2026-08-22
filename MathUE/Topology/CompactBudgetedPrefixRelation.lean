/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.CompactFinitePrefixRelation
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Compact relation chains with cumulative budgets

This module strengthens compact finite-prefix extraction by imposing every cumulative
weight budget whose cutoff has appeared. The resulting nested compact sets yield one
infinite relation chain satisfying all budgets. A separate analytic lemma records that
partial sums dominating a function tending to infinity cannot come from a summable
sequence.
-/

noncomputable section

open Finset Set Filter

namespace Math
namespace Topology

variable {Point : Type*} [TopologicalSpace Point] [T2Space Point]

/-- Box-valued relation prefixes satisfying every cumulative weight budget
whose cutoff has already appeared. -/
def compactBudgetedPrefixSolutionSet
    (box : Set Point) (relation : Point → Point → Prop)
    (weight : Point → ℝ) (budget : ℕ → ℝ) (horizon : ℕ) :
    Set (ℕ → Point) :=
  {path |
    path ∈ compactFinitePrefixSolutionSet box relation horizon ∧
      ∀ cutoff ≤ horizon,
        budget cutoff ≤
          ∑ time ∈ Finset.range cutoff, weight (path time)}

omit [TopologicalSpace Point] [T2Space Point] in
/-- Increasing the horizon only adds relation and budget constraints. -/
theorem compactBudgetedPrefixSolutionSet_succ_subset
    (box : Set Point) (relation : Point → Point → Prop)
    (weight : Point → ℝ) (budget : ℕ → ℝ) (horizon : ℕ) :
    compactBudgetedPrefixSolutionSet box relation weight budget (horizon + 1) ⊆
      compactBudgetedPrefixSolutionSet box relation weight budget horizon := by
  intro path hpath
  refine ⟨compactFinitePrefixSolutionSet_succ_subset
    box relation horizon hpath.1, ?_⟩
  intro cutoff hcutoff
  exact hpath.2 cutoff (hcutoff.trans (Nat.le_succ horizon))

/-- The budgeted prefix set is closed when the edge graph and weight are
closed/continuous. -/
theorem compactBudgetedPrefixSolutionSet_isClosed
    (box : Set Point) (relation : Point → Point → Prop)
    (weight : Point → ℝ) (budget : ℕ → ℝ)
    (hbox : IsCompact box)
    (hgraph : IsClosed
      {pair : Point × Point |
        pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2})
    (hweight : Continuous weight) (horizon : ℕ) :
    IsClosed
      (compactBudgetedPrefixSolutionSet
        box relation weight budget horizon) := by
  have hprefix := compactFinitePrefixSolutionSet_isClosed
    box relation hbox hgraph horizon
  have hbudgetClosed : IsClosed {path : ℕ → Point |
      ∀ cutoff ≤ horizon,
        budget cutoff ≤
          ∑ time ∈ Finset.range cutoff, weight (path time)} := by
    rw [show {path : ℕ → Point |
        ∀ cutoff ≤ horizon,
          budget cutoff ≤
            ∑ time ∈ Finset.range cutoff, weight (path time)} =
      ⋂ cutoff : ℕ, ⋂ (_h : cutoff ≤ horizon),
        {path | budget cutoff ≤
          ∑ time ∈ Finset.range cutoff, weight (path time)} by
      ext path
      simp]
    apply isClosed_iInter
    intro cutoff
    apply isClosed_iInter
    intro _h
    apply isClosed_le continuous_const
    exact continuous_finsetSum _ fun time _ =>
      hweight.comp (continuous_apply time)
  rw [show compactBudgetedPrefixSolutionSet
      box relation weight budget horizon =
    compactFinitePrefixSolutionSet box relation horizon ∩
      {path : ℕ → Point |
        ∀ cutoff ≤ horizon,
          budget cutoff ≤
            ∑ time ∈ Finset.range cutoff, weight (path time)} by
    ext path
    rfl]
  exact hprefix.inter hbudgetClosed

/-- Every budgeted prefix set is compact. -/
theorem compactBudgetedPrefixSolutionSet_isCompact
    (box : Set Point) (relation : Point → Point → Prop)
    (weight : Point → ℝ) (budget : ℕ → ℝ)
    (hbox : IsCompact box)
    (hgraph : IsClosed
      {pair : Point × Point |
        pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2})
    (hweight : Continuous weight) (horizon : ℕ) :
    IsCompact
      (compactBudgetedPrefixSolutionSet
        box relation weight budget horizon) := by
  exact (isCompact_pi_infinite fun _ => hbox).of_isClosed_subset
    (compactBudgetedPrefixSolutionSet_isClosed
      box relation weight budget hbox hgraph hweight horizon)
    (fun _ hpath => hpath.1.1)

/-- **Budgeted compact inverse limit.**  Arbitrarily long compatible prefixes
meeting all elapsed cumulative budgets yield one infinite relation chain that
meets every budget. -/
theorem exists_infiniteChain_of_budgetedFinitePrefixes
    (box : Set Point) (relation : Point → Point → Prop)
    (weight : Point → ℝ) (budget : ℕ → ℝ)
    (hbox : IsCompact box)
    (hgraph : IsClosed
      {pair : Point × Point |
        pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2})
    (hweight : Continuous weight)
    (hprefix : ∀ horizon,
      (compactBudgetedPrefixSolutionSet
        box relation weight budget horizon).Nonempty) :
    ∃ path : ℕ → Point,
      (∀ time, path time ∈ box) ∧
      (∀ time, relation (path time) (path (time + 1))) ∧
      ∀ cutoff, budget cutoff ≤
        ∑ time ∈ Finset.range cutoff, weight (path time) := by
  let prefixSet : ℕ → Set (ℕ → Point) := fun horizon =>
    compactBudgetedPrefixSolutionSet box relation weight budget horizon
  have hnested : ∀ horizon, prefixSet (horizon + 1) ⊆ prefixSet horizon :=
    compactBudgetedPrefixSolutionSet_succ_subset
      box relation weight budget
  have hnonempty : ∀ horizon, (prefixSet horizon).Nonempty := hprefix
  have hcompact0 : IsCompact (prefixSet 0) :=
    compactBudgetedPrefixSolutionSet_isCompact
      box relation weight budget hbox hgraph hweight 0
  have hclosed : ∀ horizon, IsClosed (prefixSet horizon) :=
    compactBudgetedPrefixSolutionSet_isClosed
      box relation weight budget hbox hgraph hweight
  obtain ⟨path, hpath⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      prefixSet hnested hnonempty hcompact0 hclosed
  have hpref : ∀ horizon, path ∈ prefixSet horizon :=
    Set.mem_iInter.mp hpath
  refine ⟨path, (hpref 0).1.1, ?_, ?_⟩
  · intro time
    exact (hpref (time + 1)).1.2 ⟨time, Nat.lt_succ_self time⟩
  · intro cutoff
    exact (hpref cutoff).2 cutoff le_rfl

/-! ## A divergent cumulative budget forces nonsummability -/

/-- A sequence whose partial sums dominate a function tending to `+∞` cannot be summable. -/
theorem not_summable_of_tendsto_budget_atTop_of_prefix_le
    (weight budget : ℕ → ℝ)
    (hbudget : Tendsto budget atTop atTop)
    (hprefix : ∀ cutoff, budget cutoff ≤
      ∑ time ∈ Finset.range cutoff, weight time) :
    ¬Summable weight := by
  intro hsummable
  have hpartial : Tendsto
      (fun cutoff => ∑ time ∈ Finset.range cutoff, weight time)
      atTop (nhds (∑' time, weight time)) :=
    hsummable.hasSum.tendsto_sum_nat
  have hsumEventually : ∀ᶠ cutoff in atTop,
      (∑ time ∈ Finset.range cutoff, weight time) <
        (∑' time, weight time) + 1 :=
    hpartial.eventually (Iio_mem_nhds (by linarith))
  have hbudgetEventually : ∀ᶠ cutoff in atTop,
      (∑' time, weight time) + 2 ≤ budget cutoff :=
    (tendsto_atTop.1 hbudget) ((∑' time, weight time) + 2)
  obtain ⟨cutoff, hsum, hbudgetLarge⟩ :=
    (hsumEventually.and hbudgetEventually).exists
  have := hprefix cutoff
  linarith
end Topology
end Math
