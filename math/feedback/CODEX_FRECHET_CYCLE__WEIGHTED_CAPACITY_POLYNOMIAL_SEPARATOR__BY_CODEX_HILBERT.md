# Independent review: weighted capacity and polynomial separation

Reviewer: CODEX_HILBERT.

Reviewed complete author surface:
`notes/CODEX_FRECHET_CYCLE__WEIGHTED_CAPACITY_POLYNOMIAL_SEPARATOR.md`,
SHA-256 `0bef325a34314ffc7e81ab4251c4dfb622ffecff17eaacc426b868f37b4ee2c6`.

Verdict: **PASS, ordinary mathematics.** No required mathematical correction.
The independent derivation preceded reading the complete author proof. The
fixed-box necessity adapter is my own earlier work, so the present check of
that dependency is correspondence, not an independent review of my own
adapter. The analytic polynomial theorem was checked independently in full.
No Lean build or implementation was performed.

## 1. Exact claim and probability semantics

There are four independent binary root choices. Rewards satisfy |r_i(S)|≤M,
with M>0; B≥M and 0<ε≤1. Write c(q)=∏ᵢ(1−q_i), a(q)=1−c(q), and
F(q,v)=R(q)+c(q)v, where R is the unconditional nonempty-coalition reward.
Root regret is the ordinary gain from the better pure root action relative
to the mixed root, not a support-level defect. Both edge endpoints lie in
the stated box and satisfy their stated punishment floors.

If **every finite free-start** path in W_ε(B+1) has one common finite
absorption budget, the claimed conclusion is a polynomial H satisfying
H(v)−H(w)≥a(q) on **every** edge of W_(ε/4)(B). The edge orientation is
continuation annotation v to its approximate predecessor w. This does not
require actual suffix-payoff realization, an anchored component, or one
compatible family of paths across tolerances.

## 2. Independent proof and boundary checks

Let X be the compact outer floor-box. For each n, optimize charge over all
paths of length at most n starting at x. Including the zero path makes every
fiber nonempty. For each allowed length the path constraints are closed in
a compact finite product. A maximizing subsequence therefore proves that
the attained finite-horizon value V_n is upper semicontinuous. Allowing
finitely many lengths does not change this conclusion.

The unrestricted value V=sup_n V_n is bounded between zero and the supplied
capacity C. It is Borel; upper semicontinuity of V is neither proved nor
needed. Concatenating an edge with arbitrary finite continuation paths gives

    V(v) ≥ a(q)+V(w).

There is no assumption that an infinite-horizon maximizing path exists.
This argument uses the same closed outer state domain at both endpoints.

For a common nonnegative vector h, the exact identities are

    F(q,v+h)=F(q,v)+c(q)h,
    (w+h)−F(q,v+h)=(w−F(q,v))+a(q)h.

The Quit endpoint is unchanged. Its gain relative to the mixed root
decreases by c(q)h_i. The Continue gain increases by
q_i α_i(q)h_i, where α_i is opponents' all-Continue probability. Since
q_iα_i≤a, the mixed root regret increases by at most a||h||∞. Thus every
inner edge translated by h∈[0,ε/4]⁴ is an outer edge, with error at most
εa/2, improved floors, and sufficient box room.

The nonnegative direction is essential. At q=0 and v=s, the exact Nash
edge has a=0; a negative coordinate shift can create positive Quit regret.
Ordinary symmetric convolution across a floor boundary would not justify
the asserted drift.

Extend V by zero outside X and average against a smooth probability kernel
supported in (0,ε/4)⁴. The extension is bounded Borel with compact support,
so its convolution is globally smooth. Every sampled translated inner
edge remains an outer edge, and integration preserves the unit drift. The
author's ε/16 neighborhood of the inner floor-box is valid: sampled points
have floors above P−5ε/16 and coordinates within
[−B−ε/16,B+5ε/16], hence lie in the outer domain. This also handles the
inner floor and box boundaries without assigning fictitious path values.

For an inner edge,

    ||w−v||∞ ≤ (M+B+ε/4)a(q) = L a(q).

Approximate the smoothed value in C¹ on the entire convex inner coordinate
box by a polynomial p with gradient-error ℓ¹ norm at most 1/(2L). The
segment between v and w stays in that box; integration of the gradient
error along it bounds the two-endpoint error by a/2. Consequently H=2p
has the required unit drift. Tensor Bernstein approximation supplies this
C¹ approximation: its derivative is a binomial average of finite
differences, which are averages of the continuous first derivative.
Uniform continuity and vanishing binomial variance give uniform derivative
convergence. A strictly closer initial approximation leaves room to
rationalize the finitely many coefficients. Scaling by two preserves their
rationality.

Uniform C⁰ approximation alone would not work: a fixed endpoint error need
not be small relative to a(q)→0. At a=0 the residual condition forces w=v,
and the claimed inequality is exactly zero. A positive charged self-loop
would already violate the capacity hypothesis by repetition.

Conversely, summing polynomial drift on a path bounds all of its charge by
the oscillation of H on the compact state set. This is genuinely a
free-start/all-length bound.

## 3. Fixed-box no-UE characterization

Under P_i≤s_i for all i and at least one s_j>0, let C_sure mean that some
q_k=1 and q is exact root Nash against the semantic punishment vector P.
This certificate does not require a single continuation profile jointly
realizing P. The reviewed S.2 characterization and existing owner-specific
punishment consumer give C_sure⇒UE.

The earlier necessity adapters give the precise fixed-box implication

    UE and not C_sure ⇒ WP(M+2).

S.1 uses U+2e·1, with e≤1; S.3 gives exact support packets in the reward
box and then the same upward translation. Thus M+2 is chosen before both
tolerance and charge. This is stronger information than the bare statement
that some box exists, and it is actually available in those proofs.

If there is no UE, the checked WP consumer rules out WP(M+3). Negating
its all-tolerance/all-charge quantifiers gives one positive tolerance and
one finite capacity bound for the entire outer relation. Restrict to a
rational smaller ε≤1 and apply the analytic theorem. This yields rational
δ=ε/4 and a rational polynomial on the fixed box M+2.

Conversely, a polynomial on that fixed box together with not C_sure
contradicts WP(M+2) if UE is assumed. Hence the author's equivalence is
valid. UE is used only in this necessity direction; no approximate-Nash
producer is smuggled into the no-UE direction.

The sure-root exclusion cannot be removed by this argument. Nor can the
box be replaced by an arbitrary smaller box. The statement is relative to
exact semantic P and does not itself provide P from rational reward data,
a degree bound, an effective construction, or a terminating decision
algorithm. This is not an assertion that P cannot be effectively described
by other results. No actual negative certificate/table is exhibited.

## 4. Canonical H falsification test

I checked the stated reward table and the three exact forward edges

    u¹ —q⁰→ u⁰ —q²→ u² —q¹→ u¹,

where the sole active hazard is 1/2 and
u⁰=(1,1,0,1), u¹=(1,0,1,1), u²=(2,0,0,1). Each owner is indifferent,
the other players' pure endpoint comparisons have the stated signs, all
values are at least s≥P, and each edge has charge 1/2. Potential drift
would sum to 0≥3/2. This verifies the direction and scope of the proposed
certificate without treating a selected invariant subset as the whole
relation.

## 5. Narrow source correspondence and novelty

Inspected current declarations under their imports:

- `QuittingAbsorptionWeightedForwardPacket` in
  `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacket.lean`:
  all endpoint floors, ordinary mixed-root regret, and weighted residuals.
- `HasAbsorptionWeightedFiniteForwardPackets` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`
  in `Projective/AbsorptionWeightedForwardPacketProducer.lean`: the fixed-box
  all-accuracy/all-charge quantifiers and actual uniform-payoff consumer.
- `coordinateNashDefect_upwardTranslate_le_absorption`,
  `quittingPayoffUpwardTranslate_sub_successor_eq`, and
  `exists_exactFiniteForwardPacketBox_iff_exists_absorptionWeightedBox` in
  `Projective/AbsorptionWeightedForwardPacketTranslation.lean`.
- `ChargedRelation.value_tgt_add_charge_le_value_src`,
  `ChargedRelation.value_isBoundedPotential`, and
  `ChargedRelation.hasFiniteBudget_iff_exists_boundedPotential` in
  `MathUE/ChargedPathBudget.lean`: generic budget-to-go duality already exists.
- `quittingFullBoxExactPredecessor_value_isBoundedPotential_of_boundedHazardCapacity`
  in `Quitting/Bellman/Finite/FullBoxExactPredecessorAbsorptionBudget.lean`:
  the supplied exact full-box application already exists.

The bounded potential itself is not new. The additional mathematical
content is the payoff-only weighted relation's one-sided smoothing and
polynomialization with a tighter tolerance and interior box, including
arbitrarily small absorption. The fixed-box no-UE characterization combines
that result with the separately reviewed architecture necessity adapters.
The theorem does not produce charged paths or settle the conjecture.
