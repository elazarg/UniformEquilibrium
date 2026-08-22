/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.CompactEdgeBudgetedPrefixRelation
import MathUE.Topology.SimonViabilityQuestion

/-!
# A finite-prefix compiler for Simon's viability question

This module isolates a sufficient condition for the conclusion of Simon's
Question 1. The compact graph already supplies the compact ambient box and
closed relation needed by the inverse limit. The remaining substantive input
is a compatible finite prefix at every horizon meeting a common diverging
schedule of cumulative Euclidean-variation budgets.

The seven hypotheses supply one uniformly long local edge near each relevant
boundary piece, but they do not directly supply these arbitrarily long,
budget-compatible prefixes. Thus this compiler identifies the exact gap
between the local escape clause and the requested unbounded extended orbit.
-/

noncomputable section

namespace Math
namespace Topology
namespace SimonViability

open Filter Set
open scoped BigOperators Topology

/-- The compact box containing both coordinates of a graph. -/
def graphCoordinateBox {X : Type*} (graph : Set (X × X)) : Set X :=
  Prod.fst '' graph ∪ Prod.snd '' graph

/-- Both coordinates of a graph point lie in its coordinate box. -/
theorem graph_pair_mem_coordinateBox {X : Type*} {graph : Set (X × X)}
    {pair : X × X} (hpair : pair ∈ graph) :
    pair.1 ∈ graphCoordinateBox graph ∧ pair.2 ∈ graphCoordinateBox graph := by
  constructor
  · exact Or.inl ⟨pair, hpair, rfl⟩
  · exact Or.inr ⟨pair, hpair, rfl⟩

/-- A compact graph has a compact coordinate box. -/
theorem graphCoordinateBox_compact {X : Type*} [TopologicalSpace X]
    {graph : Set (X × X)} (hgraph : IsCompact graph) :
    IsCompact (graphCoordinateBox graph) := by
  exact (hgraph.image continuous_fst).union (hgraph.image continuous_snd)

/-- Restricting a graph relation to its coordinate box changes nothing. -/
theorem coordinateBox_relationGraph_eq {X : Type*}
    (graph : Set (X × X)) :
    {pair : X × X |
      pair.1 ∈ graphCoordinateBox graph ∧
        pair.2 ∈ graphCoordinateBox graph ∧ pair ∈ graph} = graph := by
  ext pair
  constructor
  · exact fun hpair ↦ hpair.2.2
  · intro hpair
    exact ⟨(graph_pair_mem_coordinateBox hpair).1,
      (graph_pair_mem_coordinateBox hpair).2, hpair⟩

/-- Euclidean edge cost is continuous on pairs of finite-coordinate vectors. -/
theorem continuous_euclideanDist
    {Coordinate : Type*} [Fintype Coordinate] :
    Continuous (fun pair : EuclideanSpace Coordinate × EuclideanSpace Coordinate ↦
      euclideanDist pair.1 pair.2) := by
  unfold euclideanDist euclideanNorm
  fun_prop

/-- The cumulative budget demanding one edge of cost at least `scale`. -/
def oneEdgeBudget (scale : ℝ) (cutoff : ℕ) : ℝ :=
  if cutoff = 0 then 0 else scale

/-- The seven hypotheses directly produce a charged one-edge prefix near each
relevant boundary piece. Iterating these prefixes compatibly is the additional
global obligation in Question 1. -/
theorem QuestionOneHypotheses.exists_oneEdgeBudgetedPrefix
    {Coordinate : Type*} [Fintype Coordinate] {pieceCount : ℕ}
    {domain : Set (EuclideanSpace Coordinate)}
    {piece : Fin pieceCount → Set (EuclideanSpace Coordinate)}
    {homotopy : EuclideanSpace Coordinate → UnitInterval →
      EuclideanSpace Coordinate × EuclideanSpace Coordinate}
    {neighborhood : Set (EuclideanSpace Coordinate)}
    {localGraph fullGraph :
      Set (EuclideanSpace Coordinate × EuclideanSpace Coordinate)}
    (hhypotheses : QuestionOneHypotheses
      domain piece homotopy neighborhood localGraph fullGraph) :
    ∃ scale : ℝ, 0 < scale ∧
      ∀ point ∈ neighborhood, ∀ index,
        (frontier domain ∩ piece index).Nonempty →
        euclideanInfDist point (frontier domain ∩ piece index) ≤ scale →
        (compactEdgeBudgetedPrefixSolutionSet
          (graphCoordinateBox fullGraph)
          (fun first second ↦ (first, second) ∈ fullGraph)
          euclideanDist (oneEdgeBudget scale) 1).Nonempty := by
  obtain ⟨scale, hscale, _, hescape⟩ := hhypotheses.exists_escapeScale
  refine ⟨scale, hscale, ?_⟩
  intro point hpoint index hpiece hnear
  obtain ⟨target, htarget, _, hlong, _⟩ :=
    hescape point hpoint index hpiece hnear
  have hfull : (point, target) ∈ fullGraph :=
    hhypotheses.localGraph_subset_fullGraph htarget
  have hcoordinates := graph_pair_mem_coordinateBox hfull
  let path : ℕ → EuclideanSpace Coordinate := fun time ↦
    if time = 0 then point else target
  refine ⟨path, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro time
      by_cases htime : time = 0
      · simpa [path, htime] using hcoordinates.1
      · simpa [path, htime] using hcoordinates.2
    · intro time
      have htime : (time : ℕ) = 0 := by omega
      simpa [path, htime] using hfull
  · intro cutoff hcutoff
    have hcases : cutoff = 0 ∨ cutoff = 1 := by omega
    rcases hcases with rfl | rfl
    · simp [oneEdgeBudget]
    · simpa [oneEdgeBudget, path] using hlong

/-- A compact graph plus compatible prefixes meeting diverging cumulative
budgets yields the extended orbit requested in Question 1. -/
theorem questionOneConclusion_of_edgeBudgetedFinitePrefixes
    {Coordinate : Type*} [Fintype Coordinate]
    (graph : Set (EuclideanSpace Coordinate × EuclideanSpace Coordinate))
    (budget : ℕ → ℝ) (hgraph : IsCompact graph)
    (hbudget : Tendsto budget atTop atTop)
    (hprefix : ∀ horizon,
      (compactEdgeBudgetedPrefixSolutionSet
        (graphCoordinateBox graph) (fun first second ↦ (first, second) ∈ graph)
        euclideanDist budget horizon).Nonempty) :
    QuestionOneConclusion graph := by
  have hbox := graphCoordinateBox_compact hgraph
  have hrelationClosed : IsClosed
      {pair : EuclideanSpace Coordinate × EuclideanSpace Coordinate |
        pair.1 ∈ graphCoordinateBox graph ∧
          pair.2 ∈ graphCoordinateBox graph ∧ pair ∈ graph} := by
    rw [coordinateBox_relationGraph_eq]
    exact hgraph.isClosed
  obtain ⟨orbit, horbit⟩ :=
    exists_extendedOrbit_unboundedVariation_of_edgeBudgetedFinitePrefixes
      (graphCoordinateBox graph) (fun first second ↦ (first, second) ∈ graph)
      euclideanDist budget hbox hrelationClosed continuous_euclideanDist
      hbudget hprefix
  exact ⟨orbit, horbit⟩

/-- The seven hypotheses imply Question 1 once their remaining finite-prefix
obligation is supplied for one diverging common budget schedule. -/
theorem QuestionOneHypotheses.conclusion_of_edgeBudgetedFinitePrefixes
    {Coordinate : Type*} [Fintype Coordinate] {pieceCount : ℕ}
    {domain : Set (EuclideanSpace Coordinate)}
    {piece : Fin pieceCount → Set (EuclideanSpace Coordinate)}
    {homotopy : EuclideanSpace Coordinate → UnitInterval →
      EuclideanSpace Coordinate × EuclideanSpace Coordinate}
    {neighborhood : Set (EuclideanSpace Coordinate)}
    {localGraph fullGraph :
      Set (EuclideanSpace Coordinate × EuclideanSpace Coordinate)}
    (hhypotheses : QuestionOneHypotheses
      domain piece homotopy neighborhood localGraph fullGraph)
    (budget : ℕ → ℝ) (hbudget : Tendsto budget atTop atTop)
    (hprefix : ∀ horizon,
      (compactEdgeBudgetedPrefixSolutionSet
        (graphCoordinateBox fullGraph)
        (fun first second ↦ (first, second) ∈ fullGraph)
        euclideanDist budget horizon).Nonempty) :
    QuestionOneConclusion fullGraph := by
  exact questionOneConclusion_of_edgeBudgetedFinitePrefixes
    fullGraph budget hhypotheses.fullGraph_compact hbudget hprefix

end SimonViability
end Topology
end Math
