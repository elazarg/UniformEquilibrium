# Independent review of the C¹-convex full-box drift obstruction

Reviewer: CODEX_RENY.

Reviewed original:
[C¹-convex global root drift](../notes/CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY.md).
Its SHA-256 was verified before reading:

    7abde160a5d8715f1c3b42e19e18f3a248e571f6c157864b77a59bfbf99b8a23

Verdict: **PASS for the complete C¹ theorem and its stated polynomial
consequence.** No mathematical correction is required. This review does
not establish a nonsmooth extension, convexification preservation, any
negative game, or an equilibrium producer. No author file or export was
edited and no Lean build was run.

## 1. Exact claim checked

Let I be any nonempty finite player set, with arbitrary real quitting
rewards satisfying |r_i(S)|≤M, M≥0. Put s_i=r_i({i}), choose B>M,
and let K=[−B,B]^I. For a product root q, let a(q) be its absorption
probability and F(q,v) its expected root payoff with supplied continuation
v. Exact root Nash tests both pure root actions against that same v.

The theorem excludes every H which is C¹ on a neighborhood of K,
convex on K, and satisfies

    H(v)−H(F(q,v))≥a(q)

for every v∈K and every exact Nash root q against v. Equivalently each
such convex function admits a violating exact edge with positive charge.
Any strictly positive fixed drift coefficient gives the same obstruction
after rescaling H.

This is a payoff-only full-box potential, not a function on an actual
terminal-semantic carrier, a payoff/cap pair, a selected orbit, or a
chosen invariant subset. It makes no assertion that a supplied annotation
v is strategically realizable. The normality and positive-singleton
hypotheses of the separate negative characterization are not hypotheses
of this root-level theorem.

## 2. Independence and the decisive boundary checks

Before reading the author's proof I inspected the root and charged-edge
definitions and tested an alternative minimization on the union of the
lower singleton half-boxes. That calculation isolated exactly the two
delicate points: several binding singleton faces do not automatically
permit a solo Nash root, and gradients at upper box faces must be
controlled by feasible directions rather than set equal to zero.

The author's proof handles both points correctly and more directly.
No other review of this candidate was read.

### The small solo root is used legally

At v_i=s_i and v_j>s_j for j≠i, only player i quits with a small
probability t. The owner is indifferent. A nonowner's Quit-minus-Continue
value is exactly

    (1−t)(s_j−v_j)+t(r_j({i,j})−r_j({i})).

The first term is strictly negative at t=0, so all nonowners Continue
optimally for sufficiently small positive t. Finiteness gives one common
small interval; collision rewards need no sign restriction. The successor
is v+t(r({i})−v), and the absorption charge is t, not a sum of
unrelated marginal hazards. Dividing the assumed drift by t has the
correct sign and yields

    ∇H(v)·(v−r({i}))≥1.

At multiple weak singleton equalities the proof does NOT assert this solo
root remains Nash. It approaches from strictly higher nonowner values,
using B>s_j and continuity of the gradient. The root size may shrink
with the approach point. This is sufficient for the derivative inequality
and does not require a uniform admissibility radius.

### Full-box minimizers cannot bind a singleton equality

Every exact Nash root at a full-box global minimizer must have zero
absorption: its successor lies in K, and a positive charge would force
a lower value. Exact finite-game Nash existence is available at every
annotation. Thus all-Continue is Nash there, implying v≥s.

If one coordinate equalled its singleton, the derived face inequality
would require a strictly negative directional derivative toward r({i}).
The whole segment to that reward vector is feasible in K, contradicting
one-sided minimality. This establishes STRICT v_i>s_i at every global
minimum, including minima on upper box faces. No interior critical-point
assumption is smuggled in, and convexity is not yet used.

### Convexity really excludes several lower-face bindings

Let C=∏[s_i,B] and let L be the union of its lower faces. Compactness
and the previous strict statement give min_L H>min_K H. At a minimizer
x on L with at least two binding lower coordinates, each coordinate
segment toward a global minimizer z stays in L: another lower binding
coordinate remains fixed. Therefore

    ∂_kH(x)(z_k−x_k)≥0       for every k.

Summing and applying the convex supporting-gradient inequality gives
H(z)≥H(x), contradicting the strict difference of the minima. The
argument works with any number of binding lower faces and any number
of upper faces; it uses actual one-coordinate feasible segments.

There is consequently exactly one binding lower coordinate. Only NOW
the proof selects a small solo Nash root. Its owner stays exactly on
that lower face, and the other coordinates remain above their respective
singletons for small t. Reward containment keeps every coordinate within
the upper box. Its successor remains in L, contradicting the strict
positive drift from the L-minimizer. No limiting root selection or
lower-hemicontinuity assumption is needed.

## 3. Explicit attempted falsifiers and scope boundaries

1. **One player.** At v=s the absorbing root is a positive-charge
   self-loop. Every H fails the drift there. The general proof also
   covers the singleton lower-boundary set without an artificial
   requirement of at least two players.
2. **Empty player set.** All charges vanish, so a constant convex
   function works. Nonemptiness is necessary and stated.
3. **Signed own and nonowner rewards.** Every step uses only |r|≤M
   and −B<s_i<B. No punishment comparison or sign assumption is used.
4. **Multiple singleton equalities.** The proof never treats small solo
   roots as automatically Nash there; strict-face approximation and then
   the convex coordinate-segment argument address the issue separately.
5. **Upper-box minima.** Both the reward segment and coordinate segments
   are inward feasible. No zero-gradient assertion at the upper boundary
   is required.
6. **Restricted domain.** With one player, reward s=0, and annotations
   restricted to [1,2], the only exact root is all-Continue, so a constant
   convex potential satisfies the zero-charge tests. Thus the theorem
   cannot be transferred to an arbitrary smaller box or selected region.
   This is an explicit failure of that broader domain claim, not a
   counterexample to the padded full-box theorem.
7. **Padding.** The stated B>M supplies all needed strict singleton
   room. This review does not assert that B=M is impossible to handle by
   another argument; it verifies the strict padded statement as written.
8. **No Nash-versus-full-cap confusion.** Root Nash is used only to
   construct tested algebraic edges. The theorem never equates these
   finite inequalities to unrestricted behavioral Nash of an actual
   infinite profile.

## 4. Exact source correspondence and bounded novelty check

The following declarations and definitions were inspected directly:

- `quittingRootSuccessorPayoff`, `quittingRootQuitPayoff`,
  `quittingRootContinuePayoff`, and
  `quittingRootSuccessorPayoff_eq_endpointMix` in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`;
- `IsεQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/FirstBranch.lean`;
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
- `quittingRootCoordinateNashDefect` and its endpoint decomposition in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
- `IsQuittingNashBellmanEdge` and `quittingNashBellmanBox` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`;
- `QuittingPunishmentFloorBoxEdge` and
  `quittingPunishmentFloorBoxChargedRelation` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorChargedRelation.lean`;
- the full-box path orientation in
  `UniformEquilibrium/Quitting/Bellman/Finite/FullBoxExactPredecessorAbsorptionBudget.lean`.

The convention is important: `IsQuittingNashBellmanEdge` lists current
before tail, while the charged relation runs from tail v to current
F(q,v). Therefore H(v)−H(F(q,v)) is the correct potential drop.

The already derived singleton-face test is in
[HILBERT's face note](../notes/CODEX_HILBERT__POLYNOMIAL_DRIFT_SINGLETON_FACE_TEST.md).
The non-strict global-minimum location and all-Continue exit are in
[the all-anchor test](../notes/CODEX_FRECHET_CYCLE__POLYNOMIAL_ALL_ANCHOR_DISCOUNTED_NASH_TEST.md).
Neither gives the lower-boundary convexity contradiction. Narrow searches
in the named root, Bellman, and controller subtrees did not reveal an
existing C¹-convex full-box drift impossibility declaration.

The earlier quadratic payoff/cap reset-rank obstruction concerns a
different eight-coordinate barrier domain and monotonicity under arbitrary
semantic prefixes. It is not a proof of this payoff-only, absorption-
weighted exact-Nash-edge theorem. Conversely this theorem does not exclude
indefinite quadratics in that other language.

This is a bounded source comparison, not a worldwide novelty claim and
not evidence of a completed Lean implementation.

## 5. Practical relevance and precise remaining boundary

The floor-free polynomial packet tests ALL triples (v,q,w) in the full
padded box with small absorption-weighted root regret and Bellman error.
Every exact root with w=F(q,v) is one of those triples. Its radius M+2
satisfies B>M. Thus a polynomial certificate in that packet cannot be
convex on the box. For a polynomial this means its Hessian has a negative
quadratic direction at some interior point: positive-semidefinite Hessian
everywhere in the interior would imply convexity on the whole box by
the segment criterion and continuity.

This excludes affine potentials, positive-semidefinite quadratic
potentials, and globally convex polynomial restrictions on the stated
certificate. It does NOT exclude arbitrary indefinite quadratics,
nonconvex polynomials, or sum-of-squares methods used to verify the edge
inequalities. A sum-of-squares polynomial need not itself be convex.

The theorem supplies a genuine structural restriction on candidate
negative certificates. It does not remove the arbitrary-polynomial
alternative, prove a positive charged return, prove or refute UE for any
new table, or establish completeness of any restricted convex grammar.
Export relevance should be assessed at that restricted search-language
level, separately from this PASS on correctness. Nonsmooth envelopes and
whether smoothing preserves their robust drift remain outside the
reviewed mathematical surface.
