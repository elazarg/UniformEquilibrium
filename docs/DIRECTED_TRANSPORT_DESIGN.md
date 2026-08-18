# Design: directed transport and max-affine transport graphs

Status: Layers 0 and 1 (milestones M0 and M1) are implemented in
`MathUE/DirectedTransport.lean` and `MathUE/MaxAffineTransport.lean`, with
the T6a/T6b duality regimes in `MathUE/MaxAffineSectionDuality.lean`.  Each
stage below is marked implemented, staged, or refuted.

## The object, in one sentence

A finite directed multigraph whose vertices carry state spaces (*fibers*) and
whose edges carry maps between the fibers of their endpoints; walks compose
those maps, closed walks give endomorphisms of the base fiber (*holonomy*),
and the potential/section theory of the labels is the obstruction theory of
the graph.

Five committed `MathUE` modules are shadows of this object with all fibers
equal:

| Module | Reading inside the transport theory |
| --- | --- |
| `MathUE/CycleCoboundary.lean` | translation-valued transport on one fiber; cycle sums are holonomy; exact data is a trivialization |
| `MathUE/MaxPlusPotential.lean` | lax sections (subsolutions) for ordered translation transport |
| `MathUE/TransferSummaryMonoid.lean` | the label algebra: affine and max-affine endomorphism composition |
| `MathUE/InverseCoordinateRecurrence.lean` | conjugation of one-dimensional transport inside a projective-linear action |
| `MathUE/IndependenceModelValuation.lean` | leading-order degeneration of a hazard-parameterized transport family |

The vertex-indexed generality is not decoration.  The quitting frontier's
preemption cycle (issue `#40`) is a walk whose successive inequalities are
stated in successive *players'* payoff coordinates; a scalar-weighted graph
identifies those coordinates illegitimately, which is exactly why the cycle
inequalities do not telescope.  In this design the coordinates are the
fibers, the missing telescope is holonomy, and the additive telescope is the
trivial-transport special case.  Probabilities and hazards are then not edge
weights but *parameters of the edge maps*; survival products arise because
maps compose, and the valuation module describes the family's degeneration as
the hazards vanish.

## Two layers, two modules

### Layer 0 — `MathUE/DirectedTransport.lean`

Deliberately small; no category-theory library.  Data over
`Math.BoundedDiscrepancy.EdgeGraph V E`:

```
Fiber   : V → Type*
edgeMap : (e : E) → Fiber (source e) → Fiber (target e)
```

Definitions:

- `walkMap` — transport along a walk by dependent composition (the
  representation of the free path category of the graph, said without the
  word "category" in the code);
- `holonomy` — `walkMap` of a closed walk, an endomorphism of the base
  fiber;
- `IsSection s : ∀ e, edgeMap e (s (source e)) = s (target e)` — a
  transport-invariant family of fiber points; also called an equivariant or
  flat section, a trivialization when the fibers are groups acted on freely;
- `IsLaxSection` (fibers preordered, edge maps monotone):
  `∀ e, edgeMap e (s (source e)) ≤ s (target e)` — also called a subsolution,
  a subinvariant family, or a super-/subharmonic section depending on
  orientation.

Theorems (implemented, all by walk induction):

- `walkMap_append`, `walkMap` vs `Math.CycleCoboundary.transport` when all
  fibers are equal (definitional bridge);
- sections transport exactly: `walkMap walk (s start) = s finish`;
- lax sections transport laxly (monotone edge maps):
  `walkMap walk (s start) ≤ s finish`;
- weak duality: a section forces trivial holonomy on every fiber point it
  marks; a lax section forces every closed-walk holonomy to have `s base` as
  a pre-fixed point;
- for one common fiber and labels acting through a monoid, `walkMap` is the
  action of `Math.CycleCoboundary.walkLabel` (this is `transport_eq_smul`,
  re-exported rather than reproved).

Layer 0's job is vocabulary plus the four or five induction lemmas that every
specialization would otherwise reprove.  It should stay under a few hundred
lines.

### Layer 1 — `MathUE/MaxAffineTransport.lean`

The first useful specialization: one common fiber `ℝ`, edge maps monotone
max-affine.  This is where quantitative content lives.

Label type:

```
structure Label where
  floor : WithBot ℝ     -- ⊥ means "no floor": the affine class embeds there
  shift : ℝ
  slope : ℝ
```

with `apply` by cases on the floor (`⊥ ↦ shift + slope * x`,
`↑e ↦ max e (shift + slope * x)`); the action always lands in `ℝ`.  Design
decisions:

1. **Floors in `WithBot ℝ`, not `EReal`.**  A `⊤` floor makes the action
   constant `+∞` and leaves `ℝ`; nothing wants it.  `⊥` is the missing
   identity: `⟨⊥, 0, 1⟩` acts as the identity, so nonnegative-slope labels
   form a monoid — the repair of the semigroup-only situation recorded in
   `TransferSummaryMonoid`'s scope note, and the reason its docstring calls
   the finite floor "not an incidental inconvenience": the natural carrier is
   the ordered completion with a bottom element.
2. **Slope zero is admitted; strict positivity is a carried hypothesis.**
   Slope `0` would send the inner floor through `0 * ⊥`, which `WithBot`
   multiplication leaves junk — but the composite floor is pushed through `Option.map`, which
   preserves `⊥` and keeps slope zero coherent, so the monoid instance lives
   on `{f : Label // 0 ≤ f.slope}`; strict positivity is demanded only where
   a positive denominator needs it.

Embeddings and identifications (T1, implemented):

- `Math.TransferSummary.AffineSummary` at floor `⊥` (a monoid homomorphism)
  and `Math.TransferSummary.MaxAffineSummary` at coerced floors, both
  action-preserving;
- the `MulAction` of nonnegative-slope labels on `ℝ`, so Layer 0's `walkMap` and
  `Math.CycleCoboundary.walkLabel` agree here;
- the identification tying the two representations together: the transfer
  matrices of
  `Math.InverseCoordinate` assemble into a monoid homomorphism
  `AffineSummary →* Matrix (Fin 2) (Fin 2) ℝ` (upper-triangular image), whose
  composition law is `affineTransferMatrix_mul`; this ties the matrix
  representation to the summary monoid instead of leaving them parallel.

Core definitions:

- `IsLaxSection φ : ∀ e, (label e).apply (φ (source e)) ≤ φ (target e)` —
  Layer 0's lax section at these labels (named in parallel with Layer 0,
  since it is an inequality, not an invariance); the potential of
  `MaxPlusPotential` with the translation replaced by the edge's transfer;
- `defect φ e := (label e).apply (φ (source e)) - φ (target e)`;
- suffix weights `W i` — the product of the slopes after position `i` of a
  walk; the abstract form of the survival-weighted accounting recurring
  throughout the quitting development.

Theorem ladder:

**T2 — the weighted-defect telescope (implemented; centerpiece).**  For a
walk `e₁ … eₙ` and any candidate `φ`:

```
holonomy (φ start) ≤ φ finish + Σᵢ Wᵢ · max 0 (defect φ eᵢ)
```

by induction from the one-sided Lipschitz estimate
`apply f (x + d) ≤ apply f x + slope * d` for `0 ≤ d`.  At all slopes `1`
this is `Math.MaxPlusPotential.sum_defect_eq` weakened to an inequality; at
reflected labels it is the survival-weighted accounting of
`Math.TransferSummary.reflectedIter_eq_sup'` read as a bound.  This is the
checkable content of "the inequalities live in different fibers and do not
telescope additively": they telescope with slope-product weights.

**T3 — weak duality (implemented).**  A lax section gives every cycle
holonomy the pre-fixed point `φ base`.  Layer 0's weak duality specialized.

**T4 — the expansivity trichotomy (implemented).**  For a single label
`(E, t, a)` with `0 ≤ a`, `∃ x, apply f x ≤ x` iff `a < 1`, or `a = 1 ∧
t ≤ 0`, or `a > 1 ∧ E ≤ -t / (a - 1)` (`E = ⊥` always admissible).
Decidable in the coefficients; applied to a cycle's composed label it decides
pre-fixed-point existence from the holonomy coefficients — the
generalization of "cycle weight ≤ 0".

**T5 — quantitative obstruction (implemented).**  If a cycle's holonomy
satisfies `holonomy x ≥ x + γ` at `x = φ base`, some edge has
`defect φ e ≥ γ / (Σᵢ Wᵢ)`.  At slopes `1` this is
`Math.MaxPlusPotential.exists_edge_defect_ge`.  T4 identifies when the
hypothesis holds at every `x`, making the obstruction candidate-free.

**T6 — strong duality (a and b implemented in
`MathUE/MaxAffineSectionDuality.lean`).**  Does "every cycle holonomy has a
pre-fixed point" give a lax section?

  a. *Slope 1* (implemented; floors may be `⊥` or finite): a lax section
     exists iff no cycle has positive shift-sum, and iff every cycle's
     composite label has a pre-fixed point.  Proved by lifting
     `MaxPlusPotential`'s canonical potential for the shift weights by one
     constant large enough to clear every floor — the classical added
     anchor (slack) vertex done as a constant lift, with no augmented
     graph.  `Fintype V` enters only through the max-plus duality.
  b. *Uniformly contractive* (implemented; `slope < 1` edgewise, no sign
     condition and no monotonicity): a constant section already closes edge
     by edge, so existence needs no operator iteration and holds for any
     `Finite E`.
  c. *General mixed slopes*: the cyclewise test is REFUTED as a complete
     proof rule.  Two loops at one vertex — a constant reset `x ↦ 10`
     (slope `0`) and a doubling `x ↦ 2x` — admit no lax section
     (`10 ≤ x` and `2x ≤ x` conflict), yet every closed word passes the
     per-cycle test: a word containing the reset has slope `0`, and a pure
     doubling word has floor `⊥`, so the trichotomy grants each a pre-fixed
     point.  The existential witnesses of separate cycles do not
     synchronize.  The correct general duality is not cyclewise but linear:
     each edge contributes the rows `floor_e ≤ φ(target e)` and
     `shift_e + slope_e · φ(source e) ≤ φ(target e)`, a finite linear
     system in `φ` whatever the slope signs, so existence is governed by
     the Farkas alternative already in
     `MathUE/FiniteInequalityCompatibility.lean`: a lax section exists iff
     no nonnegative balanced combination of the rows is infeasible.  At
     nonnegative slopes the certificate reads as a generalized-flow
     (gain-flow) certificate; the classical positive cycle is the
     affine-only case at unit slope product, and floor rows enter for
     expanding cycles.  (Implemented in
     `MathUE/MaxAffineFarkasDuality.lean`: the counterexample and the
     Farkas instantiation.)  The spectral reading —
     min-max function theory (Gunawardena, Discrete Event Dynamic Systems 4
     (1994)), topical-map Perron–Frobenius (Gaubert–Gunawardena, Trans.
     Amer. Math. Soc. 356 (2004)) — remains the right frame for eigenvalue
     questions, which stay out of scope.

**T7 — periodic certificates (implemented, bridge).**  A fixed point of a
cycle's holonomy is a solution of that cycle's cyclic system; bridge to
`Math.CyclicMaxAffine.CyclicSolution`, whose equations
`C k = max (1 - p k) (q k * C (k + 1) + p k)` are the labels
`⟨↑(1 - p k), p k, q k⟩` read around a cycle, and whose survival-weighted
bound is T2 on that cycle.

**Specializations to recover as theorems**: translation labels recover
`Math.MaxPlusPotential.IsPotential` and its duality; their equality case
recovers `Math.CycleCoboundary.IsCoboundary` through
`isCoboundary_iff_exists_defect_eq_zero`; reflected labels `⟨↑0, -g, a⟩`
recover `Math.TransferSummary.reflectedIter` as transport along a path.

## Naming

Layer 0: `Math.DirectedTransport`.  Other names for the object, to be listed
in its docstring: a labelled transition system whose transitions transform a
per-state value, with `walkMap` as its exact (concrete) semantics — the
thing an abstract interpretation would soundly overapproximate, none being
built here — and a lax section as an inductive invariant; a representation
of the free path category of a quiver; a functor from the path category to
types (said structurally, not through a category-theory library); a (set-valued) gain graph or voltage graph when the
fibers coincide (Zaslavsky, *Biased graphs. I*, J. Combin. Theory Ser. B 47
(1989)); a discrete connection, with `holonomy` as its holonomy; sections are
flat/equivariant sections, and `IsLaxSection` is a subsolution.

Layer 1: `Math.MaxAffineTransport`.  Nearest named neighbours: min-max
function networks (Gunawardena), topical maps (Gaubert–Gunawardena; the
slope-1 sublattice is topical, general slopes are monotone but not additively
homogeneous), timed event graphs of max-plus discrete-event theory (Baccelli,
Cohen, Olsder, Quadrat, *Synchronization and Linearity*, Wiley 1992), and per
vertex a one-player Bellman operator.  The general object appears to carry no
established name.

## The relation-labelled variant, resolved

A variant of Layer 0 with relations in place of functions — edge labels
`R_e ⊆ Fiber (source e) × Fiber (target e)`, walks composing relations,
sections satisfying `(s (source e), s (target e)) ∈ R_e` — would faithfully
carry constraint data that is not functional, and for labels that are finite
conjunctions of affine inequalities the Farkas layer already covers it: the
row encoding of `MathUE/MaxAffineFarkasDuality.lean` never uses
functionality.  The variant is nonetheless not written, and the reason has a
proved core with an honest scope: on the one-real-coordinate-per-player
vertex set, the constraints the counterexample regime forces on preemption
edges are floorless constant labels
(`Research/Quitting/PreemptionTransport.lean`), which compose without
obstruction.  That rules out the scalar-per-player compression, not every
encoding: on the payoff-cell vertex set of ordered player pairs, with
`(x, y)` carrying `r_y({x})`, each preemption is a genuine unit-slope
translation edge into the target's diagonal cell, and what is missing is not
transport but concatenation — the within-row observer-switch edges from a
diagonal cell to the next off-diagonal cell, which no static datum supplies.
A relational or fibered layer becomes worth writing when a producer supplies
those switch edges from dynamic data — chronologies or blocks — rather than
from the static table.

## Exogenous and endogenous transport

In a many-state stochastic game the transition system is exogenous: the
kernel supplies it, and a transport system on state vertices with
one-dimensional shadows of the Shapley operator as labels would analyze
given data (a coherent, unbuilt instance; the full operator couples all
successors, so per-edge scalar labels appear only after fixing a stationary
policy or restricting to deterministic transitions).  In a quitting game the
kernel has one live state and the transition system is endogenous: a profile
supplies it — a periodic profile is an automaton on phases, and the phase
counter is the state variable the kernel lacks — while the table supplies
only rewards and absorption.  This is why the static table forces no
transport (`Research/Quitting/PreemptionTransport.lean`) and the anchored
renewal transport exists only per profile: equilibrium existence quantifies
over the induced transport systems, so a producer theorem must extract a
canonical labelled system from an arbitrary chronology rather than analyze a
given one.

## Intended consumers (game side; not part of these modules)

The adapter that would make this progress on the open frontier rather than
generic mathematics: exhibit the `#40` preemption lasso as a directed
transport problem — fibers the players' payoff/debt coordinates, edge maps
supplied by a producer theorem from the counterexample regime's collision and
repair data — and ask T2/T4/T5 about its holonomy.
`UniformEquilibrium.Quitting.Boundary.Holonomy` already composes per-player
affine and max-affine block summaries (words in Layer 1's label monoid); its
documented gap, source-labelled splice admissibility, is that producer
theorem's game-semantic half and stays game-side.  The debt transport law
(`UniformEquilibrium/Quitting/Debt/Dynamic/DebtTransportLaw.lean`) is the
reflected specialization on a path, and its documented refusal to compute
cyclic mismatch corresponds to T4's `a = 1, t ≤ 0` boundary.

## Milestones

All implemented.

- **M0**: Layer 0 (`MathUE/DirectedTransport.lean`).
- **M1**: Layer 1 label algebra + T2 + T3 + T4 + T5 + T7 + specialization
  theorems + the `AffineSummary →* Matrix` identification
  (`MathUE/MaxAffineTransport.lean`).
- **M2**: T6a and T6b (`MathUE/MaxAffineSectionDuality.lean`).
- **M3**: the cyclewise-completeness refutation and the general Farkas
  duality (`MathUE/MaxAffineFarkasDuality.lean`).

## Sibling-module completions (recorded)

Scope notes recorded in the five modules' docstrings (literature-only
citations there, per docstring policy); cross-referenced here:

- `MathUE/MaxPlusPotential.lean`: potential side only; missing toward
  max-plus Perron–Frobenius: eigenvector existence, the Collatz–Wielandt
  attained form of the max cycle mean, the critical graph, the Kleene star
  (of which `maxIncomingWeight` is one row).  Natural setting: topical maps.
- `MathUE/TransferSummaryMonoid.lean`: the missing identity is the finite
  floor; `WithBot` floors (Layer 1) repair it.  Missing on the Lindley side:
  stationary (Loynes) theory, two-sided reflection.
- `MathUE/CycleCoboundary.lean`: criterion and obstruction, not the Hodge
  decomposition (coboundary + circulation), not `H¹` as a quotient;
  general-group switching (Zaslavsky) only in the translation case.
- `MathUE/InverseCoordinateRecurrence.lean`: single steps and two-phase
  products; the `n`-phase trace trichotomy of the projective action is the
  completion, and the matrix representation should be identified with the
  summary monoid (Layer 1, T1).
- `MathUE/IndependenceModelValuation.lean`: the all-small chart only; the
  boundary charts where some coordinates approach `1` (cofactors carrying
  the valuation) are the piece actual schedules need first.  The chamber
  structure over varying exponents is the normal fan of the family's Newton
  polytope, not the tropicalization of the model's ideal.
