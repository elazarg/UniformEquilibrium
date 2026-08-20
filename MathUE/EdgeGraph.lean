/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.Count
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup

/-!
# Directed multigraphs with edge identities and their typed walks

A directed multigraph is represented by a vertex type, an edge type, and source
and target maps.  Edges are data rather than mere related vertex pairs, so
parallel edges retain their identities.

`EdgeGraph.Walk G start finish` is an endpoint-indexed finite walk.  It stores
the edge identities in chronological order and makes endpoint compatibility
part of the type.  This module supplies the reusable finite-walk calculus:
length and edge lists, endpoint facts, concatenation, singleton walks, edge
multiplicity, splitting at an edge, and splicing at a visited vertex.

The module deliberately assigns no labels or weights to edges.  Transport,
charges, discrepancy, circulations, and application-specific semantics belong
in modules that import this one.
-/

noncomputable section

namespace Math

universe uV uE

structure EdgeGraph (V : Type uV) (E : Type uE) where
  source : E → V
  target : E → V

namespace EdgeGraph

variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E)

/-- A finite directed walk, retaining the list of edge identities. -/
inductive Walk (start : V) : V → Type (max uV uE)
  | nil : Walk start start
  | concat {finish : V} (walkSoFar : Walk start finish) (edge : E)
      (legal : G.source edge = finish) : Walk start (G.target edge)

namespace Walk

variable {G} {start finish middle previous base : V}

/-- Number of edges in a finite walk. -/
def length {start : V} : {finish : V} → G.Walk start finish → ℕ
  | _, .nil => 0
  | _, .concat walkSoFar _ _ => walkSoFar.length + 1

/-- Edge identities in chronological order. -/
def edges {start : V} : {finish : V} → G.Walk start finish → List E
  | _, .nil => []
  | _, .concat walkSoFar edge _ => walkSoFar.edges ++ [edge]

@[simp] theorem length_nil : (Walk.nil : G.Walk start start).length = 0 := rfl

@[simp] theorem length_concat (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).length = walkSoFar.length + 1 := rfl

@[simp] theorem edges_nil : (Walk.nil : G.Walk start start).edges = [] := rfl

@[simp] theorem edges_concat (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).edges = walkSoFar.edges ++ [edge] := rfl

@[simp] theorem edges_length (walk : G.Walk start finish) :
    walk.edges.length = walk.length := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih => simp [edges, length, ih]

/-- Consecutive edge identities in a typed walk have matching endpoints. -/
theorem edges_isChain (walk : G.Walk start finish) :
    walk.edges.IsChain fun first second => G.target first = G.source second := by
  induction walk with
  | nil => exact List.isChain_nil
  | @concat middle walkSoFar edge legal ih =>
      cases walkSoFar with
      | nil => exact List.isChain_singleton edge
      | @concat previous walkBefore finalEdge finalLegal =>
          rw [edges, List.isChain_append]
          refine ⟨ih, List.isChain_singleton edge, ?_⟩
          simp [edges, legal]

private theorem head_append_of_ne_nil (left right : List E)
    (hleft : left ≠ []) (happend : left ++ right ≠ []) :
    (left ++ right).head happend = left.head hleft := by
  cases left with
  | nil => exact (hleft rfl).elim
  | cons first rest => rfl

/-- The first edge of a nonempty typed walk starts at its initial vertex. -/
theorem source_head (walk : G.Walk start finish) (hne : walk.edges ≠ []) :
    G.source (walk.edges.head hne) = start := by
  induction walk with
  | nil => simp [edges] at hne
  | @concat middle walkSoFar edge legal ih =>
      cases walkSoFar with
      | nil => simpa [edges] using legal
      | @concat previous walkBefore finalEdge finalLegal =>
          have hleft : walkBefore.edges ++ [finalEdge] ≠ [] := by simp
          change G.source (((walkBefore.edges ++ [finalEdge]) ++ [edge]).head _) = start
          rw [head_append_of_ne_nil _ _ hleft]
          simpa only [edges] using ih hleft

/-- The last edge of a nonempty typed walk ends at its terminal vertex. -/
theorem target_getLast (walk : G.Walk start finish) (hne : walk.edges ≠ []) :
    G.target (walk.edges.getLast hne) = finish := by
  cases walk with
  | nil => simp [edges] at hne
  | concat walkSoFar edge legal => simp [edges]

/-- Multiplicity of an edge identity in a finite walk. -/
def edgeMultiplicity [DecidableEq E] {start : V} : {finish : V} →
    G.Walk start finish → E → ℕ
  | _, .nil => fun _ => 0
  | _, .concat walkSoFar edge _ => fun candidate =>
      walkSoFar.edgeMultiplicity candidate + if candidate = edge then 1 else 0

@[simp] theorem edgeMultiplicity_nil [DecidableEq E] (candidate : E) :
    (Walk.nil : G.Walk start start).edgeMultiplicity candidate = 0 := rfl

@[simp] theorem edgeMultiplicity_concat [DecidableEq E]
    (walkSoFar : G.Walk start finish) (edge candidate : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).edgeMultiplicity candidate =
      walkSoFar.edgeMultiplicity candidate + if candidate = edge then 1 else 0 := rfl

theorem edgeMultiplicity_pos_iff_mem_edges [DecidableEq E]
    (walk : G.Walk start finish) (edge : E) :
    0 < walk.edgeMultiplicity edge ↔ edge ∈ walk.edges := by
  induction walk with
  | nil => simp [edgeMultiplicity, edges]
  | concat walkSoFar finalEdge legal ih =>
      by_cases h : edge = finalEdge <;> simp [edgeMultiplicity, edges, ih, h]

theorem edgeMultiplicity_eq_count [DecidableEq E]
    (walk : G.Walk start finish) (edge : E) :
    walk.edgeMultiplicity edge = walk.edges.count edge := by
  induction walk with
  | nil => rfl
  | concat walkSoFar finalEdge legal ih =>
      by_cases h : edge = finalEdge
      · subst edge
        simp [edgeMultiplicity, edges, List.count_append, ih]
      · simp [edgeMultiplicity, edges, List.count_append, ih, h, eq_comm]

theorem edgeMultiplicity_eq_one_iff_mem_edges [DecidableEq E]
    (walk : G.Walk start finish) (hnodup : walk.edges.Nodup) (edge : E) :
    walk.edgeMultiplicity edge = 1 ↔ edge ∈ walk.edges := by
  rw [walk.edgeMultiplicity_eq_count]
  exact ⟨fun h => List.count_pos_iff.mp (by omega),
    fun h => List.count_eq_one_of_mem hnodup h⟩

theorem edgeMultiplicity_le_one [DecidableEq E]
    (walk : G.Walk start finish) (hnodup : walk.edges.Nodup) (edge : E) :
    walk.edgeMultiplicity edge ≤ 1 := by
  rw [walk.edgeMultiplicity_eq_count]
  exact (List.nodup_iff_count_le_one.mp hnodup) edge

/-- Change only the terminal index of a typed walk along an equality. -/
def castFinish {start finish finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') : G.Walk start finish' :=
  hfinish ▸ walk

@[simp] theorem length_castFinish {start finish finish' : V}
    (walk : G.Walk start finish) (hfinish : finish = finish') :
    (walk.castFinish hfinish).length = walk.length := by
  subst finish'
  rfl

@[simp] theorem edges_castFinish {start finish finish' : V}
    (walk : G.Walk start finish) (hfinish : finish = finish') :
    (walk.castFinish hfinish).edges = walk.edges := by
  subst finish'
  rfl

/-- Concatenate two typed walks at their common endpoint. -/
def append {start middle : V} (first : G.Walk start middle) :
    {finish : V} → G.Walk middle finish → G.Walk start finish
  | _, .nil => first
  | _, .concat second edge legal =>
      .concat (first.append second) edge legal

@[simp] theorem append_nil (first : G.Walk start middle) :
    first.append (.nil : G.Walk middle middle) = first := rfl

@[simp] theorem append_concat (first : G.Walk start middle)
    (second : G.Walk middle finish) (edge : E)
    (legal : G.source edge = finish) :
    first.append (.concat second edge legal) =
      .concat (first.append second) edge legal := rfl

@[simp] theorem edges_append (first : G.Walk start middle)
    (second : G.Walk middle finish) :
    (first.append second).edges = first.edges ++ second.edges := by
  induction second with
  | nil => simp
  | concat second edge legal ih => simp [ih, List.append_assoc]

@[simp] theorem length_append (first : G.Walk start middle)
    (second : G.Walk middle finish) :
    (first.append second).length = first.length + second.length := by
  induction second with
  | nil => simp
  | concat second edge legal ih => simp [ih, Nat.add_assoc]

/-- The one-edge walk carrying a prescribed edge identity. -/
def singleton (edge : E) : G.Walk (G.source edge) (G.target edge) :=
  .concat .nil edge rfl

@[simp] theorem edges_singleton (edge : E) :
    (singleton (G := G) edge).edges = [edge] := rfl

@[simp] theorem length_singleton (edge : E) :
    (singleton (G := G) edge).length = 1 := rfl

/-- A typed decomposition of a walk at an occurrence of an edge. -/
theorem exists_splitAtEdge (walk : G.Walk start finish) (edge : E)
    (hmem : edge ∈ walk.edges) :
    ∃ (before : G.Walk start (G.source edge))
      (after : G.Walk (G.target edge) finish),
      walk.edges = before.edges ++ edge :: after.edges := by
  induction walk with
  | nil => simp at hmem
  | @concat middle walkSoFar finalEdge legal ih =>
      simp only [edges_concat, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | heq
      · obtain ⟨before, after, hsplit⟩ := ih hmem
        refine ⟨before, after.concat finalEdge legal, ?_⟩
        simp only [edges_concat, hsplit]
        simp [List.append_assoc]
      · subst finalEdge
        exact ⟨walkSoFar.castFinish legal.symm, .nil, by simp⟩

/-- A witness that a typed walk passes through a specified vertex. -/
structure VertexSplit (walk : G.Walk start finish) (vertex : V) where
  before : G.Walk start vertex
  after : G.Walk vertex finish
  edges_eq : walk.edges = before.edges ++ after.edges

/-- The source of every used edge is a visited vertex. -/
noncomputable def vertexSplitAtSource (walk : G.Walk start finish) (edge : E)
    (hmem : edge ∈ walk.edges) : walk.VertexSplit (G.source edge) := by
  apply Classical.choice
  obtain ⟨before, after, hsplit⟩ := walk.exists_splitAtEdge edge hmem
  refine ⟨⟨before, (singleton (G := G) edge).append after, ?_⟩⟩
  simpa [List.append_assoc] using hsplit

/-- The target of every used edge is a visited vertex. -/
noncomputable def vertexSplitAtTarget (walk : G.Walk start finish) (edge : E)
    (hmem : edge ∈ walk.edges) : walk.VertexSplit (G.target edge) := by
  apply Classical.choice
  obtain ⟨before, after, hsplit⟩ := walk.exists_splitAtEdge edge hmem
  refine ⟨⟨before.append (singleton (G := G) edge), after, ?_⟩⟩
  simpa [List.append_assoc] using hsplit

namespace VertexSplit

/-- Insert a closed walk at a visited vertex. -/
def splice {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex) :
    G.Walk start finish :=
  (split.before.append inserted).append split.after

@[simp] theorem edges_splice {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex) :
    (split.splice inserted).edges =
      split.before.edges ++ inserted.edges ++ split.after.edges := by
  simp [splice, List.append_assoc]

theorem edges_splice_perm {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex) :
    (split.splice inserted).edges.Perm (walk.edges ++ inserted.edges) := by
  rw [split.edges_eq]
  simpa [List.append_assoc] using
    (List.Perm.refl split.before.edges).append
      (List.perm_append_comm :
        (inserted.edges ++ split.after.edges).Perm
          (split.after.edges ++ inserted.edges))

@[simp] theorem length_splice {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex) :
    (split.splice inserted).length = walk.length + inserted.length := by
  rw [← Walk.edges_length, ← Walk.edges_length, ← Walk.edges_length]
  simpa using (split.edges_splice_perm inserted).length_eq

end VertexSplit

end Walk

end EdgeGraph

end Math
