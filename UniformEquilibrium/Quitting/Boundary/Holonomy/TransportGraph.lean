/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DirectedTransport.MaxAffine.Slopes
import UniformEquilibrium.Quitting.Boundary.Holonomy.Transport

/-!
# Source-matched graphs of realized quitting boundary blocks

A boundary transport graph selects nonempty blocks from one calibrated finite
chain and attaches their entry and exit times to graph vertices. Edges point
from exit to entry, in the direction of backward Bellman transport. Source
and target matching is part of the data.

Literal time decreases strictly along every edge. Hence these graphs have no
nonempty closed walks. The max-affine critical-cycle criterion then gives a
lax best-response section for every finite such graph. Thus a cycle
obstruction cannot arise from unquotiented chronological blocks alone: a
cyclic application needs additional, semantically justified identifications
or splice data.
-/

noncomputable section

namespace GameTheory

open Math Math.Probability Math.MaxAffineTransport

universe uV uE

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A directed graph whose edges are literal blocks from one calibrated
chain, with source and target vertices carrying the blocks' exit and entry
times respectively. -/
structure QuittingAnchoredBoundaryTransportGraph
    (anchor : QuittingCalibratedTerminalAnchor reward)
    (V : Type uV) (E : Type uE) where
  graph : EdgeGraph V E
  time : V → ℕ
  block : E → QuittingAnchoredBoundaryBlock anchor
  source_time : ∀ edge,
    time (graph.source edge) = (block edge).start + (block edge).length
  target_time : ∀ edge, time (graph.target edge) = (block edge).start

namespace QuittingAnchoredBoundaryTransportGraph

variable {anchor : QuittingCalibratedTerminalAnchor reward}
variable {V : Type uV} {E : Type uE}

/-- Playerwise best-response labels on a realized boundary graph. -/
def bestResponseLabel
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    (who : ι) (edge : E) : Label :=
  (diagram.block edge).bestResponseLabel who

@[simp] theorem bestResponseLabel_slope
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    (who : ι) (edge : E) :
    (diagram.bestResponseLabel who edge).slope =
      quittingOpponentSurvivalWeight anchor.roots who
        (diagram.block edge).start (diagram.block edge).length := by
  exact QuittingAnchoredBoundaryBlock.bestResponseLabel_slope
    (diagram.block edge) who

theorem bestResponseLabel_slope_nonneg
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    (who : ι) (edge : E) :
    0 ≤ (diagram.bestResponseLabel who edge).slope :=
  QuittingAnchoredBoundaryBlock.bestResponseLabel_slope_nonneg
    (diagram.block edge) who

theorem bestResponseLabel_slope_le_one
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    (who : ι) (edge : E) :
    (diagram.bestResponseLabel who edge).slope ≤ 1 :=
  QuittingAnchoredBoundaryBlock.bestResponseLabel_slope_le_one
    (diagram.block edge) who

/-- Literal time decreases strictly along every realized block edge. -/
theorem target_time_lt_source_time
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    (edge : E) :
    diagram.time (diagram.graph.target edge) <
      diagram.time (diagram.graph.source edge) := by
  rw [diagram.source_time edge, diagram.target_time edge]
  simp [QuittingAnchoredBoundaryBlock.length]

/-- Literal time is nonincreasing along every typed walk. -/
theorem walk_time_le
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    {start finish : V} (walk : diagram.graph.Walk start finish) :
    diagram.time finish ≤ diagram.time start := by
  induction walk with
  | nil => exact le_rfl
  | @concat middle walk edge legal ih =>
      have hedge := diagram.target_time_lt_source_time edge
      rw [legal] at hedge
      exact (Nat.le_of_lt hedge).trans ih

/-- A nonempty typed walk strictly decreases literal time. -/
theorem walk_time_lt_of_edges_ne_nil
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    {start finish : V} (walk : diagram.graph.Walk start finish)
    (hne : walk.edges ≠ []) :
    diagram.time finish < diagram.time start := by
  cases walk with
  | nil => exact (hne rfl).elim
  | @concat middle walk edge legal =>
      have hedge := diagram.target_time_lt_source_time edge
      rw [legal] at hedge
      exact hedge.trans_le (diagram.walk_time_le walk)

/-- Every closed walk in a literal boundary graph is empty. -/
theorem closedWalk_edges_eq_nil
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    (base : V) (walk : diagram.graph.Walk base base) :
    walk.edges = [] := by
  by_contra hne
  have hlt := diagram.walk_time_lt_of_edges_ne_nil walk hne
  exact (lt_irrefl _ hlt)

/-- Edges whose best-response transport has unit survival slope. -/
abbrev UnitSurvivalEdge
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    (who : ι) :=
  Math.MaxAffineTransport.UnitSlopeEdge (diagram.bestResponseLabel who)

/-- The subgraph of realized blocks with unit opponent survival. -/
def unitSurvivalGraph
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    (who : ι) : EdgeGraph V (diagram.UnitSurvivalEdge who) :=
  Math.MaxAffineTransport.unitSlopeGraph diagram.graph
    (diagram.bestResponseLabel who)

/-- The affine shift on a unit-survival boundary edge. -/
def unitSurvivalShift
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    (who : ι) (edge : diagram.UnitSurvivalEdge who) : ℝ :=
  Math.MaxAffineTransport.unitSlopeShift
    (diagram.bestResponseLabel who) edge

/-- The unit-survival subgraph is itself a literal boundary transport graph. -/
def unitSurvivalDiagram
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    (who : ι) :
    QuittingAnchoredBoundaryTransportGraph anchor V
      (diagram.UnitSurvivalEdge who) where
  graph := diagram.unitSurvivalGraph who
  time := diagram.time
  block edge := diagram.block edge.1
  source_time edge := diagram.source_time edge.1
  target_time edge := diagram.target_time edge.1

/-- Lax feasibility is equivalent to the additive cycle test on the
unit-survival subgraph. -/
theorem exists_bestResponseLaxSection_iff_unitSurvivalCycles_nonpos
    [Fintype V] [DecidableEq V] [Fintype E]
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    (who : ι) :
    (∃ potential : V → ℝ,
      IsLaxSection diagram.graph (diagram.bestResponseLabel who) potential) ↔
      ∀ (base : V) (cycle : (diagram.unitSurvivalGraph who).Walk base base),
        Math.MaxPlusPotential.walkWeight
          (diagram.unitSurvivalShift who) cycle ≤ 0 := by
  exact exists_isLaxSection_iff_unitSlopeCycles_nonpos_of_slope_le_one
    (diagram.bestResponseLabel_slope_le_one who)

/-- Every finite source-matched graph of literal chronological blocks admits
a playerwise lax best-response section. -/
theorem exists_bestResponseLaxSection
    [Fintype V] [DecidableEq V] [Fintype E]
    (diagram : QuittingAnchoredBoundaryTransportGraph anchor V E)
    (who : ι) :
    ∃ potential : V → ℝ,
      IsLaxSection diagram.graph (diagram.bestResponseLabel who) potential := by
  apply (diagram.exists_bestResponseLaxSection_iff_unitSurvivalCycles_nonpos who).mpr
  intro base cycle
  have hnil := (diagram.unitSurvivalDiagram who).closedWalk_edges_eq_nil
    base cycle
  change cycle.edges = [] at hnil
  unfold Math.MaxPlusPotential.walkWeight
  rw [hnil]
  rfl

end QuittingAnchoredBoundaryTransportGraph

end GameTheory

end
