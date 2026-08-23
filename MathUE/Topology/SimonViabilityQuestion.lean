/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.ExtendedOrbit
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Simon's extended-orbit viability question

This module states Question 1 from Robert Samuel Simon, *A Topological
Approach to Quitting Games* (2012), independently of quitting-game names.
It is a topological existence question for a compact correspondence containing
a straight-line homotopy image and satisfying a local escape condition.

The question itself is represented by `QuestionOneAffirmative`, a proposition,
not by a theorem. Sufficient conditions and applications should be stated
separately rather than folded into its seven hypotheses.
-/

noncomputable section

namespace Math
namespace Topology
namespace SimonViability

open Filter Set
open scoped BigOperators Topology

/-- The finite-dimensional real space used in Simon's question. -/
abbrev EuclideanSpace (Coordinate : Type*) := Coordinate → ℝ

/-- The closed unit interval, used as the homotopy parameter. -/
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

/-- The explicit Euclidean two-norm in a finite coordinate space. -/
def euclideanNorm {Coordinate : Type*} [Fintype Coordinate]
    (point : EuclideanSpace Coordinate) : ℝ :=
  Real.sqrt (∑ coordinate, (point coordinate) ^ 2)

/-- The explicit Euclidean distance in a finite coordinate space. -/
def euclideanDist {Coordinate : Type*} [Fintype Coordinate]
    (first second : EuclideanSpace Coordinate) : ℝ :=
  euclideanNorm (first - second)

/-- Euclidean distance from a point to a set, valued in the reals. -/
def euclideanInfDist {Coordinate : Type*} [Fintype Coordinate]
    (point : EuclideanSpace Coordinate)
    (target : Set (EuclideanSpace Coordinate)) : ℝ :=
  sInf (euclideanDist point '' target)

/-- The graph of a set-valued correspondence. -/
def correspondenceGraph {X Y : Type*} (relation : Correspondence X Y) :
    Set (X × Y) :=
  {pair | pair.2 ∈ relation pair.1}

/-- A graph, read as a correspondence in its first coordinate. -/
def graphCorrespondence {X : Type*} (graph : Set (X × X)) :
    Correspondence X X :=
  fun first ↦ {second | (first, second) ∈ graph}

/-- A bounded strict Lyapunov certificate on a graph rules out finite graph
orbits with arbitrarily large accumulated cost. The state type may itself be
a carrier subtype. This is only the finite-orbit obstruction and supplies no
bridge from that obstruction to a game-semantic claim. -/
theorem not_hasArbitrarilyLargeFiniteGraphOrbitVariationWith_of_potential_bounds
    {X : Type*} {graph : Set (X × X)} {cost : X → X → ℝ}
    {potential : X → ℝ} {constant lower upper : ℝ}
    (hconstant : 0 < constant)
    (hlower : ∀ state, lower ≤ potential state)
    (hupper : ∀ state, potential state ≤ upper)
    (hdecrease : ∀ pair ∈ graph,
      potential pair.2 ≤
        potential pair.1 - constant * cost pair.1 pair.2) :
    ¬HasArbitrarilyLargeFiniteOrbitVariationWith
      (graphCorrespondence graph) cost := by
  apply not_hasArbitrarilyLargeFiniteOrbitVariationWith_of_potential_bounds
    hconstant hlower hupper
  intro first next hnext
  exact hdecrease (first, next) hnext

/-- The fiber of a graph over its first coordinate. -/
def graphFiber {X Y : Type*} (graph : Set (X × Y)) (first : X) : Set Y :=
  {second | (first, second) ∈ graph}

/-- Simon's strict small-step graph `J_δ`. -/
def smallStepGraph {Coordinate : Type*} [Fintype Coordinate]
    (graph : Set (EuclideanSpace Coordinate × EuclideanSpace Coordinate))
    (scale : ℝ) : Set (EuclideanSpace Coordinate × EuclideanSpace Coordinate) :=
  {pair | pair ∈ graph ∧ euclideanDist pair.1 pair.2 < scale}

/-- Intrinsic contractibility of a subset, with the homotopy staying in it. -/
def IsContractibleSet {X : Type*} [TopologicalSpace X] (set : Set X) : Prop :=
  ∃ center : set, ∃ homotopy : set → UnitInterval → set,
    Continuous (fun pair : set × UnitInterval ↦ homotopy pair.1 pair.2) ∧
      (∀ point, homotopy point 0 = point) ∧
      ∀ point, homotopy point 1 = center

/-- A compact convex polytope with nonempty ambient interior. -/
def IsFullDimensionalCompactConvexPolytope
    {Coordinate : Type*} [Fintype Coordinate]
    (set : Set (EuclideanSpace Coordinate)) : Prop :=
  IsCompact set ∧ Convex ℝ set ∧ (interior set).Nonempty ∧
    ∃ vertices : Finset (EuclideanSpace Coordinate),
      set = convexHull ℝ (↑vertices : Set (EuclideanSpace Coordinate))

/-- The terminal image `H(C,1)` of the homotopy. -/
def homotopyTerminalImage {E : Type*} (domain : Set E)
    (homotopy : E → UnitInterval → E × E) : Set (E × E) :=
  {pair | ∃ point ∈ domain, homotopy point 1 = pair}

/-- The homotopy is continuous on `C × [0,1]` and linearly interpolates its endpoints. -/
def IsStraightLineOn {Coordinate : Type*} [Fintype Coordinate]
    (domain : Set (EuclideanSpace Coordinate))
    (homotopy : EuclideanSpace Coordinate → UnitInterval →
      EuclideanSpace Coordinate × EuclideanSpace Coordinate) : Prop :=
  Continuous (fun pair : domain × UnitInterval ↦ homotopy pair.1 pair.2) ∧
    ∀ point ∈ domain, ∀ time,
      homotopy point time =
        (time : ℝ) • homotopy point 1 +
          (1 - (time : ℝ)) • homotopy point 0

/--
The seven hypotheses of Simon 2012, Question 1.

The explicit nonemptiness guard in condition (7) implements the paper's
extended-real convention that distance to an empty boundary piece is infinite.
Here `euclideanInfDist` is real-valued, so the empty-set case must be excluded.
Condition (6) uses the strict graph `J_ω = {(x,y) ∈ J | ‖y-x‖ < ω}`.
-/
def QuestionOneHypotheses {Coordinate : Type*} [Fintype Coordinate]
    {pieceCount : ℕ}
    (domain : Set (EuclideanSpace Coordinate))
    (piece : Fin pieceCount → Set (EuclideanSpace Coordinate))
    (homotopy : EuclideanSpace Coordinate → UnitInterval →
      EuclideanSpace Coordinate × EuclideanSpace Coordinate)
    (neighborhood : Set (EuclideanSpace Coordinate))
    (localGraph fullGraph :
      Set (EuclideanSpace Coordinate × EuclideanSpace Coordinate)) : Prop :=
  0 < pieceCount ∧
  IsContractibleSet domain ∧
  (∀ index, IsFullDimensionalCompactConvexPolytope (piece index)) ∧
  domain = ⋃ index, piece index ∧
  IsStraightLineOn domain homotopy ∧
  (∀ point ∈ domain, homotopy point 0 = (point, point)) ∧
  (∀ point ∈ frontier domain, ∀ time,
    homotopy point time = (point, point)) ∧
  (∀ point,
    (point, point) ∈ homotopyTerminalImage domain homotopy →
      point ∈ frontier domain) ∧
  IsCompact neighborhood ∧ frontier domain ⊆ interior neighborhood ∧
  IsCompact localGraph ∧
  (∀ pair ∈ localGraph, pair.1 ∈ neighborhood) ∧
  (∀ point ∈ neighborhood,
    IsContractibleSet (graphFiber localGraph point) ∧
      point ∈ graphFiber localGraph point) ∧
  IsCompact fullGraph ∧
  homotopyTerminalImage domain homotopy ⊆ fullGraph ∧
  localGraph ⊆ fullGraph ∧
  ∃ scale : ℝ, 0 < scale ∧
    smallStepGraph fullGraph scale ⊆ localGraph ∧
    ∀ point ∈ neighborhood, ∀ index,
      (frontier domain ∩ piece index).Nonempty →
      euclideanInfDist point (frontier domain ∩ piece index) ≤ scale →
      ∃ target ∈ graphFiber localGraph point,
        euclideanInfDist target (piece index) ≤
            euclideanInfDist point (piece index) ∧
          scale ≤ euclideanDist point target ∧
          segment ℝ point target ⊆ graphFiber localGraph point

/-- The full correspondence graph in Question 1 is compact. -/
theorem QuestionOneHypotheses.fullGraph_compact
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
    IsCompact fullGraph := by
  rcases hhypotheses with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcompact, _⟩
  exact hcompact

/-- The local correspondence is contained in the full graph. -/
theorem QuestionOneHypotheses.localGraph_subset_fullGraph
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
    localGraph ⊆ fullGraph := by
  rcases hhypotheses with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsubset, _⟩
  exact hsubset

/-- Condition (7) supplies a common positive escape scale and a long local
edge near every nonempty boundary piece. This is the strongest moving-prefix
fact available by direct unpacking of the seven hypotheses. -/
theorem QuestionOneHypotheses.exists_escapeScale
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
    ∃ scale : ℝ, 0 < scale ∧ smallStepGraph fullGraph scale ⊆ localGraph ∧
      ∀ point ∈ neighborhood, ∀ index,
        (frontier domain ∩ piece index).Nonempty →
        euclideanInfDist point (frontier domain ∩ piece index) ≤ scale →
        ∃ target ∈ graphFiber localGraph point,
          euclideanInfDist target (piece index) ≤
              euclideanInfDist point (piece index) ∧
            scale ≤ euclideanDist point target ∧
            segment ℝ point target ⊆ graphFiber localGraph point := by
  rcases hhypotheses with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hscale⟩
  exact hscale

/-- The conclusion asked for in Simon 2012, Question 1. -/
def QuestionOneConclusion {Coordinate : Type*} [Fintype Coordinate]
    (graph : Set (EuclideanSpace Coordinate × EuclideanSpace Coordinate)) : Prop :=
  ∃ orbit : ExtendedOrbitData (graphCorrespondence graph),
    HasUnboundedExtendedVariationWith euclideanDist orbit

/-- An affirmative answer to Simon 2012, Question 1, in every finite dimension. -/
def QuestionOneAffirmative : Prop :=
  ∀ (Coordinate : Type*) [Fintype Coordinate] [Nonempty Coordinate]
    (pieceCount : ℕ)
    (domain : Set (EuclideanSpace Coordinate))
    (piece : Fin pieceCount → Set (EuclideanSpace Coordinate))
    (homotopy : EuclideanSpace Coordinate → UnitInterval →
      EuclideanSpace Coordinate × EuclideanSpace Coordinate)
    (neighborhood : Set (EuclideanSpace Coordinate))
    (localGraph fullGraph :
      Set (EuclideanSpace Coordinate × EuclideanSpace Coordinate)),
      QuestionOneHypotheses domain piece homotopy neighborhood localGraph fullGraph →
        QuestionOneConclusion fullGraph

end SimonViability
end Topology
end Math
