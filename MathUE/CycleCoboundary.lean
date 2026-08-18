/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Real.Basic
import MathUE.BoundedDiscrepancyCirculation
import MathUE.ChargedPathBudget
import MathUE.MaxPlusPotential

/-!
# Exactness of edge data on a finite directed multigraph

Edge data on a directed multigraph is a *coboundary* when it is the difference
of a vertex function across each edge.  This file proves the exactness
criterion: on a strongly connected graph, edge data is a coboundary exactly
when every closed walk has cycle sum zero, and it records the quantitative
obstruction supplied by a closed walk of nonzero cycle sum.

## Vocabulary

The same objects carry many names in different literatures.

* Edge data of the form `e ↦ φ (target e) - φ (source e)` is a *coboundary*,
  an *exact* `1`-cochain, a *potential difference*, a *gradient*, or a
  *tension*.  The vertex function `φ` is the *potential*.
* The criterion "every closed walk has cycle sum zero" is *Kirchhoff's voltage
  law*, *path independence*, or *conservativeness*; in its multiplicative form
  for transition rates it is the *Kolmogorov cycle criterion* for reversibility
  (Kelly, *Reversibility and Stochastic Networks*, Chapter 1).
* Edge data whose cycle sums do not all vanish carries a nonzero *circulation*,
  a nonzero class in the *first cohomology* of the graph, or a *curvature* or
  *holonomy obstruction*.
* Graphs with edge labels in a monoid are *gain graphs* or *voltage graphs*
  (Zaslavsky, *Biased graphs* and the gain-graph surveys); the composite label
  of a walk is its *gain*, *holonomy*, or *monodromy*, and a gain graph whose
  cycle gains are all trivial is *balanced* or *flat*.

## Main definitions

* `Math.CycleCoboundary.walkSum` — sum of edge data along a finite walk.
* `Math.CycleCoboundary.coboundary` — the edge data induced by a potential.
* `Math.CycleCoboundary.IsCoboundary`, `Math.CycleCoboundary.HasZeroCycleSums`.
* `Math.CycleCoboundary.LinkedTo`, `Math.CycleCoboundary.IsStronglyConnectedAt`
  — the reachability scope of the criterion.
* `Math.CycleCoboundary.gain`, `Math.CycleCoboundary.HasTrivialCycleGains`,
  `Math.CycleCoboundary.transport` — the monoid-labelled (gain-graph) layer.

## Main results

* `Math.CycleCoboundary.exists_coboundary_of_baseCycleSums_eq_zero` — the
  construction of a potential by path sums from a base vertex.  Only the
  closed walks *at the base vertex* are used, and only the endpoints of edges
  need to be linked to the base.
* `Math.CycleCoboundary.isCoboundary_iff_hasZeroCycleSums` — the exactness
  criterion on a strongly connected graph.
* `Math.CycleCoboundary.isCoboundary_iff_exists_defect_eq_zero` — exactness is
  the vanishing-defect case of the one-sided potential inequality of
  `MathUE.MaxPlusPotential`.
* `Math.CycleCoboundary.cycleSum_le_length_mul_of_defect_le`,
  `Math.CycleCoboundary.exists_edge_defect_ge_of_pos` and
  `Math.CycleCoboundary.exists_edge_abs_defect_ge` — the quantitative
  obstruction: a closed walk of cycle sum at least `γ > 0` forces some edge on
  it to deviate from every potential difference by at least `γ / length`, in
  the positive direction.
* `Math.CycleCoboundary.hasTrivialCycleGains_ofAdd_iff` and
  `Math.CycleCoboundary.isCoboundary_iff_hasTrivialCycleGains` — for real edge
  data, exactness is triviality of the cycle holonomy of the induced
  translation action.

## Relation to neighbouring modules

`MathUE.BoundedDiscrepancyCirculation` supplies the graph and walk
representation, and `Math.CycleCoboundary.charge_eq_walkSum` identifies its
integer walk charge with `walkSum`.

`MathUE.MaxPlusPotential` develops the *one-sided* theory of the same edge
graphs: `Math.MaxPlusPotential.IsPotential G w φ` says that the coboundary of
`φ` dominates `w` edgewise, `Math.MaxPlusPotential.defect` measures the failure
at one edge, and a potential exists exactly when no closed walk has positive
weight.  Its real-valued `Math.MaxPlusPotential.walkWeight` is definitionally
the real instance of `walkSum`, recorded by
`Math.CycleCoboundary.walkWeight_eq_walkSum`.  Exactness is the equality case,
so the quantitative obstruction below is inherited from that module rather than
reproved.

`MathUE.ChargedPathBudget` proves the *inequality* form of the same duality:
for nonnegative edge data, a bounded path budget is equivalent to a potential
satisfying `Φ (tgt e) + w e ≤ Φ (src e)`, and the least oscillation of such a
potential is the budget.  The criterion here is the equality form; the bridge
`Math.CycleCoboundary.chargedIsPotential_neg_of_isCoboundary` exhibits an exact
potential as a special case of an inequality potential.  Note that its sign
convention is the reverse of the one in `MathUE.MaxPlusPotential`.

`Math.LinearAlgebra.OwnerLabeledFlowHolonomy` treats the dual linear-programming
form (Farkas duality between a nonpositive flow-charge pairing and a
superharmonic account potential).  Its `holonomy` is the pairing of a
circulation with a charge cochain, which is a different object from the
composite walk label `gain` below.
-/

noncomputable section

namespace Math

namespace CycleCoboundary

open Math.BoundedDiscrepancy

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-! ### Sums of edge data along walks -/

section WalkSum

variable {A : Type*} [AddCommMonoid A]

/-- Sum of edge data along a finite walk, in chronological order.  Also called
the walk's tension, its line integral, or its cycle sum when the walk is
closed. -/
def walkSum (w : E → A) {start finish : V} (walk : G.Walk start finish) : A :=
  (walk.edges.map w).sum

variable {w : E → A} {start finish middle : V}

@[simp] theorem walkSum_nil : walkSum w (.nil : G.Walk start start) = 0 := rfl

@[simp] theorem walkSum_concat (walk : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    walkSum w (walk.concat edge legal) = walkSum w walk + w edge := by
  simp [walkSum]

@[simp] theorem walkSum_append (first : G.Walk start middle)
    (second : G.Walk middle finish) :
    walkSum w (first.append second) = walkSum w first + walkSum w second := by
  simp [walkSum]

@[simp] theorem walkSum_singleton (edge : E) :
    walkSum w (EdgeGraph.Walk.singleton (G := G) edge) = w edge := by
  simp [walkSum]

@[simp] theorem walkSum_castFinish {finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') :
    walkSum w (walk.castFinish hfinish) = walkSum w walk := by
  simp [walkSum]

/-- The integer walk charge of `MathUE.BoundedDiscrepancyCirculation` is the
walk sum of the same edge data. -/
theorem charge_eq_walkSum {κ : Type*} (edgeCharge : E → κ → ℤ)
    (walk : G.Walk start finish) :
    walk.charge edgeCharge = walkSum edgeCharge walk :=
  walk.charge_eq_sum_map edgeCharge

end WalkSum

/-- The real walk weight of `MathUE.MaxPlusPotential` is the real instance of
`walkSum`. -/
theorem walkWeight_eq_walkSum (weight : E → ℝ) {start finish : V}
    (walk : G.Walk start finish) :
    Math.MaxPlusPotential.walkWeight weight walk = walkSum weight walk := rfl

theorem walkSum_sub {A : Type*} [AddCommGroup A] (w₁ w₂ : E → A)
    {start finish : V} (walk : G.Walk start finish) :
    walkSum (fun edge => w₁ edge - w₂ edge) walk =
      walkSum w₁ walk - walkSum w₂ walk := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [walkSum_concat, walkSum_concat, walkSum_concat, ih]
      abel

/-! ### Coboundaries and the cycle criterion -/

section Coboundary

variable {A : Type*} [AddCommGroup A]

/-- The edge data induced by a vertex potential: the difference of the
potential across each edge.  Also called an exact `1`-cochain, a potential
difference, a discrete gradient, or a tension. -/
def coboundary (G : EdgeGraph V E) (φ : V → A) : E → A :=
  fun edge => φ (G.target edge) - φ (G.source edge)

@[simp] theorem coboundary_apply (φ : V → A) (edge : E) :
    coboundary G φ edge = φ (G.target edge) - φ (G.source edge) := rfl

/-- Edge data is *exact* when it is the coboundary of some vertex potential. -/
def IsCoboundary (G : EdgeGraph V E) (w : E → A) : Prop :=
  ∃ φ : V → A, ∀ edge : E, w edge = coboundary G φ edge

/-- Every closed walk has cycle sum zero.  This is Kirchhoff's voltage law, or
path independence of the walk sum. -/
def HasZeroCycleSums (G : EdgeGraph V E) (w : E → A) : Prop :=
  ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkSum w cycle = 0

variable {start finish : V}

/-- Telescoping: the walk sum of a coboundary depends only on the endpoints. -/
@[simp] theorem walkSum_coboundary (φ : V → A) (walk : G.Walk start finish) :
    walkSum (coboundary G φ) walk = φ finish - φ start := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [walkSum_concat, ih, coboundary_apply, legal]
      abel

theorem walkSum_eq_sub_of_isCoboundary {w : E → A} (hw : IsCoboundary G w)
    (walk : G.Walk start finish) :
    ∃ φ : V → A, walkSum w walk = φ finish - φ start := by
  obtain ⟨φ, hφ⟩ := hw
  refine ⟨φ, ?_⟩
  rw [show w = coboundary G φ from funext hφ, walkSum_coboundary]

/-- Exact edge data has vanishing cycle sums. -/
theorem IsCoboundary.hasZeroCycleSums {w : E → A} (hw : IsCoboundary G w) :
    HasZeroCycleSums G w := by
  obtain ⟨φ, hφ⟩ := hw
  intro vertex cycle
  rw [show w = coboundary G φ from funext hφ, walkSum_coboundary, sub_self]

end Coboundary

/-! ### Reachability scope

The converse construction needs the endpoints of every edge to lie on a closed
walk through a fixed base vertex: a walk out to the endpoint and a walk back.
In a directed graph neither direction follows from the other. -/

/-- `base` reaches `vertex` and `vertex` reaches `base`.  Equivalently, the two
vertices lie in a common strongly connected component. -/
def LinkedTo (G : EdgeGraph V E) (base vertex : V) : Prop :=
  Nonempty (G.Walk base vertex) ∧ Nonempty (G.Walk vertex base)

/-- Every vertex is linked to `base`: the graph is strongly connected. -/
def IsStronglyConnectedAt (G : EdgeGraph V E) (base : V) : Prop :=
  ∀ vertex : V, LinkedTo G base vertex

theorem IsStronglyConnectedAt.nonempty_walk {base : V}
    (hconnected : IsStronglyConnectedAt G base) (source target : V) :
    Nonempty (G.Walk source target) :=
  ⟨((hconnected source).2.some).append ((hconnected target).1.some)⟩

/-- The endpoints of every edge are linked to `base`.  This is all the
reachability the reconstruction below consumes. -/
def EdgeEndpointsLinkedTo (G : EdgeGraph V E) (base : V) : Prop :=
  ∀ edge : E, LinkedTo G base (G.source edge) ∧ LinkedTo G base (G.target edge)

theorem IsStronglyConnectedAt.edgeEndpointsLinkedTo {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    EdgeEndpointsLinkedTo G base :=
  fun _ => ⟨hconnected _, hconnected _⟩

/-! ### The exactness criterion -/

section Reconstruction

variable {A : Type*} [AddCommGroup A]

/-- The potential built by summing edge data along a chosen walk from `base`,
and by `0` on the vertices `base` does not reach.  Well-definedness on the
reachable part is the content of
`exists_coboundary_of_baseCycleSums_eq_zero`. -/
def basePotential (G : EdgeGraph V E) (w : E → A) (base vertex : V) : A :=
  @dite A (Nonempty (G.Walk base vertex)) (Classical.dec _)
    (fun hreach => walkSum w hreach.some) (fun _ => 0)

theorem basePotential_eq_walkSum_of_baseCycleSums_eq_zero
    {w : E → A} {base : V}
    (hzero : ∀ cycle : G.Walk base base, walkSum w cycle = 0)
    {vertex : V} (walk : G.Walk base vertex)
    (hback : Nonempty (G.Walk vertex base)) :
    basePotential G w base vertex = walkSum w walk := by
  have hreach : Nonempty (G.Walk base vertex) := ⟨walk⟩
  have hchosen := hzero (hreach.some.append hback.some)
  have hgiven := hzero (walk.append hback.some)
  rw [walkSum_append] at hchosen hgiven
  rw [basePotential, dif_pos hreach]
  linear_combination (norm := abel) hchosen - hgiven

/-- **Reconstruction of a potential.**  If every closed walk at `base` has
cycle sum zero and every edge endpoint is linked to `base`, then the edge data
is a coboundary.  The potential is the path sum from `base`; the zero-cycle
hypothesis at `base` alone makes it well defined. -/
theorem exists_coboundary_of_baseCycleSums_eq_zero {w : E → A} {base : V}
    (hlinked : EdgeEndpointsLinkedTo G base)
    (hzero : ∀ cycle : G.Walk base base, walkSum w cycle = 0) :
    IsCoboundary G w := by
  refine ⟨basePotential G w base, fun edge => ?_⟩
  obtain ⟨⟨hout, hbackSource⟩, ⟨houtTarget, hbackTarget⟩⟩ := hlinked edge
  have hsource :
      basePotential G w base (G.source edge) = walkSum w hout.some :=
    basePotential_eq_walkSum_of_baseCycleSums_eq_zero hzero hout.some hbackSource
  have htarget :
      basePotential G w base (G.target edge) =
        walkSum w (hout.some.concat edge rfl) :=
    basePotential_eq_walkSum_of_baseCycleSums_eq_zero hzero
      (hout.some.concat edge rfl) hbackTarget
  rw [coboundary_apply, hsource, htarget, walkSum_concat]
  abel

/-- **Exactness criterion.**  On a strongly connected directed multigraph, edge
data valued in an additive commutative group is a coboundary exactly when every
closed walk has cycle sum zero.  Also known as Kirchhoff's voltage law, or as
the Kolmogorov cycle criterion in its multiplicative form. -/
theorem isCoboundary_iff_hasZeroCycleSums {w : E → A} {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    IsCoboundary G w ↔ HasZeroCycleSums G w :=
  ⟨fun hw => hw.hasZeroCycleSums,
    fun hzero =>
      exists_coboundary_of_baseCycleSums_eq_zero
        hconnected.edgeEndpointsLinkedTo (hzero base)⟩

end Reconstruction

/-! ### The quantitative obstruction

A closed walk of positive cycle sum is not merely an obstruction to exactness:
it forces every candidate potential to be wrong on some edge of that walk, by
an amount inversely proportional to the walk's length.

The residual of a candidate potential at one edge is `Math.MaxPlusPotential.defect`,
and the one-sided existence statement is `Math.MaxPlusPotential.exists_edge_defect_ge`.
Exactness is the case where that residual vanishes on every edge. -/

section Quantitative

open Math.MaxPlusPotential

variable {w : E → ℝ} {φ : V → ℝ} {vertex : V}

/-- Exactness is the vanishing-defect case of the one-sided potential
inequality. -/
theorem isCoboundary_iff_exists_defect_eq_zero :
    IsCoboundary G w ↔ ∃ ψ : V → ℝ, ∀ edge : E, defect G w ψ edge = 0 := by
  constructor
  · rintro ⟨ψ, hψ⟩
    refine ⟨ψ, fun edge => ?_⟩
    have h : w edge = ψ (G.target edge) - ψ (G.source edge) := hψ edge
    simp only [defect]
    linarith
  · rintro ⟨ψ, hψ⟩
    refine ⟨ψ, fun edge => ?_⟩
    have h : ψ (G.source edge) + w edge - ψ (G.target edge) = 0 := hψ edge
    simp only [coboundary_apply]
    linarith

/-- An exact potential is in particular a one-sided potential. -/
theorem isPotential_of_isCoboundary (hφ : ∀ edge : E, w edge = coboundary G φ edge) :
    IsPotential G w φ := by
  intro edge
  have h : w edge = φ (G.target edge) - φ (G.source edge) := hφ edge
  linarith

/-- Around a closed walk the candidate potential cancels: the defects of the
traversed edges sum to the cycle sum of the edge data. -/
theorem sum_defect_cycle (cycle : G.Walk vertex vertex) :
    (cycle.edges.map (defect G w φ)).sum = walkSum w cycle := by
  rw [sum_defect_eq, add_sub_cancel_right]
  rfl

/-- A closed walk of cycle sum at least `γ > 0` has at least one edge. -/
theorem length_pos_of_le_cycleSum {γ : ℝ} (hγ : 0 < γ)
    (cycle : G.Walk vertex vertex) (hcycle : γ ≤ walkSum w cycle) :
    0 < cycle.length := by
  have hne : cycle.edges ≠ [] := by
    intro hnil
    rw [walkSum, hnil] at hcycle
    simp only [List.map_nil, List.sum_nil] at hcycle
    linarith
  have hpos : 0 < cycle.edges.length := List.length_pos_iff.mpr hne
  rwa [cycle.edges_length] at hpos

/-- A uniform one-sided bound on the defect caps every cycle sum by the walk's
length times the bound. -/
theorem cycleSum_le_length_mul_of_defect_le {δ : ℝ}
    (cycle : G.Walk vertex vertex)
    (hdefect : ∀ edge ∈ cycle.edges, defect G w φ edge ≤ δ) :
    walkSum w cycle ≤ (cycle.length : ℝ) * δ := by
  have hsum : (cycle.edges.map (defect G w φ)).sum ≤ cycle.edges.length • δ := by
    have hbound := List.sum_le_card_nsmul (cycle.edges.map (defect G w φ)) δ (by
      intro value hvalue
      obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hvalue
      exact hdefect edge hedge)
    rwa [List.length_map] at hbound
  rw [sum_defect_cycle] at hsum
  simpa [cycle.edges_length, nsmul_eq_mul] using hsum

/-- **One-sided obstruction class.**  A closed walk whose cycle sum is at least
`γ > 0` forces, for every candidate potential, some edge on that walk to exceed
the potential difference by at least `γ` divided by the walk's length.  This is
`Math.MaxPlusPotential.exists_edge_defect_ge` with the length hypothesis
supplied by positivity of `γ`. -/
theorem exists_edge_defect_ge_of_pos {γ : ℝ} (hγ : 0 < γ)
    (cycle : G.Walk vertex vertex) (hcycle : γ ≤ walkSum w cycle) :
    ∃ edge ∈ cycle.edges, γ / (cycle.length : ℝ) ≤ defect G w φ edge :=
  exists_edge_defect_ge φ cycle (length_pos_of_le_cycleSum hγ cycle hcycle) hcycle

/-- **Absolute obstruction class.**  The same closed walk forces a deviation of
absolute value at least `γ` divided by its length. -/
theorem exists_edge_abs_defect_ge {γ : ℝ} (hγ : 0 < γ)
    (cycle : G.Walk vertex vertex) (hcycle : γ ≤ walkSum w cycle) :
    ∃ edge ∈ cycle.edges, γ / (cycle.length : ℝ) ≤ |defect G w φ edge| := by
  obtain ⟨edge, hedge, hbound⟩ := exists_edge_defect_ge_of_pos (φ := φ) hγ cycle hcycle
  exact ⟨edge, hedge, hbound.trans (le_abs_self _)⟩

/-- A closed walk of strictly positive cycle sum excludes exactness outright. -/
theorem not_isCoboundary_of_cycleSum_pos (cycle : G.Walk vertex vertex)
    (hcycle : 0 < walkSum w cycle) : ¬ IsCoboundary G w := by
  intro hw
  exact absurd (hw.hasZeroCycleSums vertex cycle) hcycle.ne'

end Quantitative

/-! ### Gain graphs: monoid-labelled edges and cycle holonomy

Labels in a monoid `M` make the graph a *gain graph* (or voltage graph).  The
composite label of a walk is its *gain*, *holonomy*, or *monodromy*.  Labels
compose contravariantly here, so that the gain of a walk acts on a fibre
exactly as the composite of the per-edge transports; see `transport_eq_smul`. -/

section Gain

variable {M : Type*} [Monoid M]

/-- Composite label of a walk in a gain graph: the product of its edge labels,
with the last edge outermost.  Also called the walk's holonomy or monodromy. -/
def gain (label : E → M) {start : V} :
    {finish : V} → G.Walk start finish → M
  | _, .nil => 1
  | _, .concat walkSoFar edge _ => label edge * gain label walkSoFar

variable {label : E → M} {start finish middle : V}

@[simp] theorem gain_nil : gain label (.nil : G.Walk start start) = 1 := rfl

@[simp] theorem gain_concat (walk : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    gain label (walk.concat edge legal) = label edge * gain label walk := rfl

/-- Concatenation of walks composes gains contravariantly. -/
@[simp] theorem gain_append (first : G.Walk start middle)
    (second : G.Walk middle finish) :
    gain label (first.append second) = gain label second * gain label first := by
  induction second with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [EdgeGraph.Walk.append_concat, gain_concat, gain_concat, ih, mul_assoc]

/-- Every closed walk has trivial gain.  A gain graph with this property is
called *balanced* or *flat*; the condition is triviality of the holonomy. -/
def HasTrivialCycleGains (G : EdgeGraph V E) (label : E → M) : Prop :=
  ∀ (vertex : V) (cycle : G.Walk vertex vertex), gain label cycle = 1

/-- Transport a fibre point along a walk, applying edge transports in
chronological order. -/
def transport {X : Type*} (act : E → X → X) {start : V} :
    {finish : V} → G.Walk start finish → X → X
  | _, .nil => id
  | _, .concat walkSoFar edge _ => act edge ∘ transport act walkSoFar

@[simp] theorem transport_nil {X : Type*} (act : E → X → X) :
    transport act (.nil : G.Walk start start) = id := rfl

@[simp] theorem transport_concat {X : Type*} (act : E → X → X)
    (walk : G.Walk start finish) (edge : E) (legal : G.source edge = finish) :
    transport act (walk.concat edge legal) = act edge ∘ transport act walk := rfl

/-- For labels acting on a fibre, the gain of a walk is exactly its transport
map.  This is why the gain is called the holonomy of the walk. -/
theorem transport_eq_smul {X : Type*} [MulAction M X]
    (walk : G.Walk start finish) (point : X) :
    transport (fun edge value => label edge • value) walk point =
      gain label walk • point := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [transport_concat, Function.comp_apply, ih, gain_concat, mul_smul]

/-- Under trivial cycle gains, transport around any closed walk is the
identity. -/
theorem transport_cycle_eq_self {X : Type*} [MulAction M X]
    (hflat : HasTrivialCycleGains G label) {vertex : V}
    (cycle : G.Walk vertex vertex) (point : X) :
    transport (fun edge value => label edge • value) cycle point = point := by
  rw [transport_eq_smul, hflat vertex cycle, one_smul]

end Gain

/-! ### Real edge data as a translation gain graph -/

section Translation

variable {w : E → ℝ} {start finish : V}

/-- Real edge data labels the graph by translations of the line: the gain of a
walk is the exponentiated walk sum. -/
@[simp] theorem gain_ofAdd (walk : G.Walk start finish) :
    gain (fun edge => Multiplicative.ofAdd (w edge)) walk =
      Multiplicative.ofAdd (walkSum w walk) := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [gain_concat, ih, walkSum_concat, ← ofAdd_add, add_comm]

/-- Vanishing cycle sums is triviality of the cycle holonomy for the
translation labelling. -/
theorem hasTrivialCycleGains_ofAdd_iff :
    HasTrivialCycleGains G (fun edge => Multiplicative.ofAdd (w edge)) ↔
      HasZeroCycleSums G w := by
  constructor
  · intro hflat vertex cycle
    have := hflat vertex cycle
    rw [gain_ofAdd] at this
    simpa using this
  · intro hzero vertex cycle
    rw [gain_ofAdd, hzero vertex cycle]
    rfl

/-- **Exactness as flatness.**  On a strongly connected graph, real edge data is
a potential difference exactly when the translation gain graph it defines is
balanced. -/
theorem isCoboundary_iff_hasTrivialCycleGains {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    IsCoboundary G w ↔
      HasTrivialCycleGains G (fun edge => Multiplicative.ofAdd (w edge)) := by
  rw [hasTrivialCycleGains_ofAdd_iff]
  exact isCoboundary_iff_hasZeroCycleSums hconnected

end Translation

/-! ### Bridge to the inequality form

`MathUE.ChargedPathBudget` characterises finiteness of the path budget of
nonnegative edge data by existence of a *bounded* potential obeying the
one-sided decrement `Φ (tgt e) + w e ≤ Φ (src e)`.  With the sign convention
there, that inequality says exactly that the coboundary of `-Φ` dominates the
edge data.  An exact potential is the equality case. -/

section ChargedBridge

open Math.ChargedPathBudget

/-- Nonnegative real edge data on an edge graph, read as a charged relation. -/
def chargedRelation (G : EdgeGraph V E) (w : E → ℝ) (hw : ∀ edge, 0 ≤ w edge) :
    ChargedRelation V E where
  src := G.source
  tgt := G.target
  charge := w
  charge_nonneg := hw

variable {w : E → ℝ} {hw : ∀ edge, 0 ≤ w edge}

/-- The decrement inequality of `ChargedPathBudget` is domination of the edge
data by a coboundary.  Its sign convention is the reverse of
`Math.MaxPlusPotential.IsPotential`, hence the negation. -/
theorem chargedIsPotential_iff_le_coboundary (Φ : V → ℝ) :
    (chargedRelation G w hw).IsPotential Φ ↔
      ∀ edge : E, w edge ≤ coboundary G (fun vertex => -Φ vertex) edge := by
  constructor
  · intro hΦ edge
    have h : Φ (G.target edge) + w edge ≤ Φ (G.source edge) := hΦ edge
    show w edge ≤ -Φ (G.target edge) - -Φ (G.source edge)
    linarith
  · intro hΦ edge
    have h : w edge ≤ -Φ (G.target edge) - -Φ (G.source edge) := hΦ edge
    show Φ (G.target edge) + w edge ≤ Φ (G.source edge)
    linarith

/-- An exact potential is a charged-relation potential, with equality on every
edge. -/
theorem chargedIsPotential_neg_of_isCoboundary {φ : V → ℝ}
    (hφ : ∀ edge : E, w edge = coboundary G φ edge) :
    (chargedRelation G w hw).IsPotential (fun vertex => -φ vertex) := by
  intro edge
  have h : w edge = φ (G.target edge) - φ (G.source edge) := hφ edge
  show -φ (G.target edge) + w edge ≤ -φ (G.source edge)
  linarith

end ChargedBridge

end CycleCoboundary

end Math
