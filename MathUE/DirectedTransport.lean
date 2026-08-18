/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Order.Monotone.Defs
import MathUE.BoundedDiscrepancyCirculation
import MathUE.CycleCoboundary

/-!
# Directed transport of vertex-indexed fibers

A finite directed multigraph whose vertices carry state spaces and whose edges
carry maps between the state spaces of their endpoints.  The vertex-indexed
family is the *fiber*, the edge data is the *edge map*, walks compose edge maps,
and closed walks give endomorphisms of the fiber over their base vertex.

The graph and its walks come from `MathUE.BoundedDiscrepancyCirculation`.  A
walk is built by `Math.BoundedDiscrepancy.EdgeGraph.Walk.concat`, which carries
a proof that the appended edge starts where the walk so far ends, so composing
edge maps along a walk moves fiber points across that equality of vertices;
`Math.DirectedTransport.fiberCast` performs the move.

## Vocabulary

The same data carries several names.

* The pair of a fiber family and edge maps is a representation of the free path
  category of the underlying quiver: walks are the morphisms and `walkMap` is
  the assignment of a function to each morphism.  Nothing below imports a
  category-theory library, and the statements are the induction lemmas rather
  than a functoriality package.
* When all fibers are one type and the edge maps come from a group acting on
  it, the data is a *gain graph* or *voltage graph* (Zaslavsky, *Biased
  graphs. I*, J. Combin. Theory Ser. B 47 (1989)); monoid actions and general
  fibers are a set-valued generalization, without the label inversion under
  edge reversal that the classical notion carries.
* Read geometrically the data is a *discrete connection*, `walkMap` is its
  parallel transport, and `holonomy` is its holonomy or monodromy.
* A section is also called a *flat section*, an *equivariant section*, or, in
  the gain-graph case with a group acting simply transitively on the fiber (a
  torsor), a *trivialization* or *switching function*.
* A lax section is also called a *subsolution*, a *subinvariant family*, or a
  super- or subharmonic section depending on the orientation convention; in
  program-analysis terms it is an *inductive invariant*.
* Read computationally the data is a labelled transition system whose
  transitions transform a per-state value, and `walkMap` is its exact
  (concrete) semantics -- the semantics an abstract interpretation would
  soundly overapproximate (Cousot and Cousot, *Abstract interpretation: a
  unified lattice model for static analysis of programs*, POPL 1977).  No
  abstraction of it is developed here.

## Main definitions

* `Math.DirectedTransport.Transport` — the fiber family's edge maps.
* `Math.DirectedTransport.fiberCast` — a fiber point moved along an equality of
  vertices.
* `Math.DirectedTransport.Transport.walkMap` — transport along a walk.
* `Math.DirectedTransport.Transport.holonomy` — transport around a closed walk.
* `Math.DirectedTransport.Transport.IsSection`,
  `Math.DirectedTransport.Transport.IsLaxSection`.
* `Math.DirectedTransport.ofEdgeAct`, `Math.DirectedTransport.ofSMul` — the
  constant-fiber transports.

## Main results

* `Math.DirectedTransport.Transport.walkMap_append` — transport composes along
  `Math.BoundedDiscrepancy.EdgeGraph.Walk.append`.
* `Math.DirectedTransport.Transport.IsSection.walkMap_eq` — a section is
  transported to itself, and
  `Math.DirectedTransport.Transport.IsSection.holonomy_eq` — every closed-walk
  holonomy fixes the point a section marks.
* `Math.DirectedTransport.Transport.IsLaxSection.walkMap_le` — for monotone edge
  maps a lax section is transported below itself, and
  `Math.DirectedTransport.Transport.IsLaxSection.holonomy_le` — every
  closed-walk holonomy has the marked point as a pre-fixed point.
* `Math.DirectedTransport.walkMap_ofEdgeAct` and
  `Math.DirectedTransport.walkMap_ofSMul_eq_walkLabel_smul` — with one common fiber,
  transport is `Math.CycleCoboundary.transport`, and for a monoid action it is
  the action of `Math.CycleCoboundary.walkLabel`.

## Relation to neighbouring modules

`MathUE.BoundedDiscrepancyCirculation` supplies `Math.BoundedDiscrepancy.EdgeGraph`
and its typed walks, including `Math.BoundedDiscrepancy.EdgeGraph.Walk.append`
and `Math.BoundedDiscrepancy.EdgeGraph.Walk.castFinish`, whose interaction with
transport is `Math.DirectedTransport.Transport.walkMap_castFinish`.

`MathUE.CycleCoboundary` is the constant-fiber case: its
`Math.CycleCoboundary.transport` is `walkMap` for a transport built by
`Math.DirectedTransport.ofEdgeAct`, its `Math.CycleCoboundary.walkLabel` is the
composite label of a walk, and `Math.CycleCoboundary.transport_eq_smul`
identifies the two for a monoid action.  That identification is used here, not
reproved.  Its `Math.CycleCoboundary.HasTrivialCycleLabels` is triviality of the
holonomy of the corresponding constant-fiber transport.

`MathUE.MaxPlusPotential` is the ordered constant-fiber case at translation edge
maps: `Math.MaxPlusPotential.IsPotential G w φ`, which reads
`φ (source e) + w e ≤ φ (target e)`, is the lax section condition for the
transport whose edge map at `e` is `x ↦ x + w e`.  No theorem below is stated in
those terms.

## Scope

This file provides vocabulary and the walk-induction lemmas that every
specialization would otherwise reprove.  It proves nothing about the existence
of sections or lax sections: that is potential theory of the particular label
algebra, developed for translation labels in `MathUE.MaxPlusPotential` and for
their equality case in `MathUE.CycleCoboundary`.
-/

namespace Math

namespace DirectedTransport

open Math.BoundedDiscrepancy

universe uV uE uF uX uM

variable {V : Type uV} {E : Type uE}

/-- A fiber point moved along an equality of vertices.  This is the coercion
that composing edge maps along a walk needs, because the legality proof of
`Math.BoundedDiscrepancy.EdgeGraph.Walk.concat` identifies the source of the
appended edge with the endpoint reached so far. -/
def fiberCast (Fiber : V → Type uF) {first second : V} (hvertex : first = second)
    (point : Fiber first) : Fiber second :=
  cast (congrArg Fiber hvertex) point

variable {Fiber : V → Type uF}

@[simp] theorem fiberCast_rfl {vertex : V} (point : Fiber vertex) :
    fiberCast Fiber rfl point = point := rfl

@[simp] theorem fiberCast_family {first second : V} (family : ∀ vertex, Fiber vertex)
    (hvertex : first = second) :
    fiberCast Fiber hvertex (family first) = family second := by
  subst hvertex
  rfl

theorem fiberCast_fiberCast {first second third : V} (hfirst : first = second)
    (hsecond : second = third) (point : Fiber first) :
    fiberCast Fiber hsecond (fiberCast Fiber hfirst point) =
      fiberCast Fiber (hfirst.trans hsecond) point := by
  subst hfirst
  rfl

/-- `fiberCast` on a constant fiber family is the identity. -/
@[simp] theorem fiberCast_const {X : Type uX} {first second : V}
    (hvertex : first = second) (point : X) :
    fiberCast (fun _ : V => X) hvertex point = point := rfl

theorem fiberCast_le_fiberCast [∀ vertex : V, Preorder (Fiber vertex)]
    {first second : V} (hvertex : first = second) {point other : Fiber first}
    (hle : point ≤ other) :
    fiberCast Fiber hvertex point ≤ fiberCast Fiber hvertex other := by
  subst hvertex
  exact hle

/-- Maps between the fibers of the endpoints of each edge of a directed
multigraph. -/
structure Transport (G : EdgeGraph V E) (Fiber : V → Type uF) where
  /-- The map from the fiber of the source of an edge to the fiber of its
  target. -/
  edgeMap : (edge : E) → Fiber (G.source edge) → Fiber (G.target edge)

namespace Transport

variable {G : EdgeGraph V E} (T : Transport G Fiber)

/-- Transport a fiber point along a walk, applying edge maps in chronological
order.  Each step moves the point to the fiber of the source of the next edge
along that edge's legality proof. -/
def walkMap {start : V} :
    {finish : V} → G.Walk start finish → Fiber start → Fiber finish
  | _, .nil => id
  | _, .concat walkSoFar edge legal =>
      fun point =>
        T.edgeMap edge (fiberCast Fiber legal.symm (walkMap walkSoFar point))

variable {T}
variable {start finish middle finish' base : V}

@[simp] theorem walkMap_nil (point : Fiber start) :
    T.walkMap (.nil : G.Walk start start) point = point := rfl

@[simp] theorem walkMap_concat (walk : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) (point : Fiber start) :
    T.walkMap (walk.concat edge legal) point =
      T.edgeMap edge (fiberCast Fiber legal.symm (T.walkMap walk point)) := rfl

@[simp] theorem walkMap_singleton (edge : E) (point : Fiber (G.source edge)) :
    T.walkMap (EdgeGraph.Walk.singleton (G := G) edge) point = T.edgeMap edge point := rfl

/-- Retyping the endpoint of a walk retypes its transport. -/
@[simp] theorem walkMap_castFinish (walk : G.Walk start finish)
    (hfinish : finish = finish') (point : Fiber start) :
    T.walkMap (walk.castFinish hfinish) point =
      fiberCast Fiber hfinish (T.walkMap walk point) := by
  subst hfinish
  rfl

/-- Transport along a concatenation of walks is the composite of the two
transports. -/
theorem walkMap_append (first : G.Walk start middle) (second : G.Walk middle finish)
    (point : Fiber start) :
    T.walkMap (first.append second) point = T.walkMap second (T.walkMap first point) := by
  induction second with
  | nil => rfl
  | concat walkSoFar edge legal ih =>
      rw [EdgeGraph.Walk.append_concat, walkMap_concat, walkMap_concat, ih]

/-- Transport around a closed walk, an endomorphism of the fiber over its base
vertex.  Also called the walk's holonomy or monodromy. -/
def holonomy (T : Transport G Fiber) {base : V} (cycle : G.Walk base base) :
    Fiber base → Fiber base :=
  T.walkMap cycle

@[simp] theorem holonomy_nil (point : Fiber base) :
    T.holonomy (.nil : G.Walk base base) point = point := rfl

/-- Traversing two closed walks at the same base vertex composes their
holonomies. -/
theorem holonomy_append (first second : G.Walk base base) (point : Fiber base) :
    T.holonomy (first.append second) point = T.holonomy second (T.holonomy first point) :=
  walkMap_append first second point

/-! ### Sections -/

/-- A family of fiber points that every edge map carries to the family's value
at the edge's target.  Also called a flat or equivariant section. -/
def IsSection (T : Transport G Fiber) (family : ∀ vertex, Fiber vertex) : Prop :=
  ∀ edge : E, T.edgeMap edge (family (G.source edge)) = family (G.target edge)

variable {family : ∀ vertex, Fiber vertex}

/-- **Sections transport exactly.**  Transport along any walk carries a section's
value at the initial vertex to its value at the terminal vertex. -/
theorem IsSection.walkMap_eq (hfamily : T.IsSection family) (walk : G.Walk start finish) :
    T.walkMap walk (family start) = family finish := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih =>
      rw [walkMap_concat, ih, fiberCast_family, hfamily edge]

/-- Every closed-walk holonomy fixes the point a section marks over the base
vertex. -/
theorem IsSection.holonomy_eq (hfamily : T.IsSection family) (cycle : G.Walk base base) :
    T.holonomy cycle (family base) = family base :=
  hfamily.walkMap_eq cycle

/-! ### Lax sections -/

section Ordered

variable [∀ vertex : V, Preorder (Fiber vertex)]

/-- A family of fiber points that every edge map carries below the family's
value at the edge's target.  Also called a subsolution, a subinvariant
family, or an inductive invariant. -/
def IsLaxSection (T : Transport G Fiber) (family : ∀ vertex, Fiber vertex) : Prop :=
  ∀ edge : E, T.edgeMap edge (family (G.source edge)) ≤ family (G.target edge)

theorem IsSection.isLaxSection (hfamily : T.IsSection family) : T.IsLaxSection family :=
  fun edge => (hfamily edge).le

/-- **Lax sections transport laxly.**  With monotone edge maps, transport along
any walk carries a lax section's value at the initial vertex below its value at
the terminal vertex. -/
theorem IsLaxSection.walkMap_le (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (hfamily : T.IsLaxSection family) (walk : G.Walk start finish) :
    T.walkMap walk (family start) ≤ family finish := by
  induction walk with
  | nil => exact le_rfl
  | concat walkSoFar edge legal ih =>
      rw [walkMap_concat]
      refine le_trans (hmono edge ?_) (hfamily edge)
      have hcast := fiberCast_le_fiberCast (Fiber := Fiber) legal.symm ih
      rwa [fiberCast_family] at hcast

/-- **Weak duality.**  With monotone edge maps, the point a lax section marks
over the base vertex is a pre-fixed point of every closed-walk holonomy. -/
theorem IsLaxSection.holonomy_le (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (hfamily : T.IsLaxSection family) (cycle : G.Walk base base) :
    T.holonomy cycle (family base) ≤ family base :=
  hfamily.walkMap_le hmono cycle

end Ordered

end Transport

/-! ### The constant-fiber case

With one common fiber the data is edge-indexed self-maps of a single type, which
is the setting of `Math.CycleCoboundary.transport`. -/

variable {G : EdgeGraph V E} {start finish : V}

/-- The transport whose fibers are all one type and whose edge maps are
prescribed self-maps of it. -/
def ofEdgeAct (G : EdgeGraph V E) (X : Type uX) (act : E → X → X) :
    Transport G (fun _ : V => X) where
  edgeMap edge := act edge

/-- Transport on a constant fiber is `Math.CycleCoboundary.transport` of the same
edge-indexed self-maps. -/
theorem walkMap_ofEdgeAct {X : Type uX} (act : E → X → X) (walk : G.Walk start finish)
    (point : X) :
    (ofEdgeAct G X act).walkMap walk point =
      Math.CycleCoboundary.transport act walk point := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih =>
      rw [Transport.walkMap_concat, fiberCast_const,
        Math.CycleCoboundary.transport_concat, Function.comp_apply, ih]
      rfl

/-- The transport whose fibers are all one type acted on by a monoid, with each
edge acting through its label. -/
def ofSMul (G : EdgeGraph V E) (X : Type uX) {M : Type uM} [Monoid M] [MulAction M X]
    (label : E → M) : Transport G (fun _ : V => X) :=
  ofEdgeAct G X fun edge point => label edge • point

/-- Transport by a monoid labelling is `Math.CycleCoboundary.transport` of the
labels' action. -/
theorem walkMap_ofSMul {X : Type uX} {M : Type uM} [Monoid M] [MulAction M X]
    (label : E → M) (walk : G.Walk start finish) (point : X) :
    (ofSMul G X label).walkMap walk point =
      Math.CycleCoboundary.transport (fun edge value => label edge • value) walk point :=
  walkMap_ofEdgeAct _ walk point

/-- **The walk-label bridge.**  Transport by a monoid labelling is the action
of the walk's composite label, by `Math.CycleCoboundary.transport_eq_smul`. -/
theorem walkMap_ofSMul_eq_walkLabel_smul {X : Type uX} {M : Type uM} [Monoid M] [MulAction M X]
    (label : E → M) (walk : G.Walk start finish) (point : X) :
    (ofSMul G X label).walkMap walk point = Math.CycleCoboundary.walkLabel label walk • point := by
  rw [walkMap_ofSMul, Math.CycleCoboundary.transport_eq_smul]

/-- The holonomy of a closed walk under a monoid labelling is the action of
its cycle label. -/
theorem holonomy_ofSMul_eq_walkLabel_smul {X : Type uX} {M : Type uM} [Monoid M] [MulAction M X]
    (label : E → M) {base : V} (cycle : G.Walk base base) (point : X) :
    (ofSMul G X label).holonomy cycle point = Math.CycleCoboundary.walkLabel label cycle • point :=
  walkMap_ofSMul_eq_walkLabel_smul label cycle point

/-- Under `Math.CycleCoboundary.HasTrivialCycleLabels` every closed-walk holonomy
of the labelled constant-fiber transport is the identity. -/
theorem holonomy_ofSMul_eq_self {X : Type uX} {M : Type uM} [Monoid M] [MulAction M X]
    {label : E → M} (hflat : Math.CycleCoboundary.HasTrivialCycleLabels G label)
    {base : V} (cycle : G.Walk base base) (point : X) :
    (ofSMul G X label).holonomy cycle point = point := by
  rw [holonomy_ofSMul_eq_walkLabel_smul, hflat base cycle, one_smul]

end DirectedTransport

end Math
