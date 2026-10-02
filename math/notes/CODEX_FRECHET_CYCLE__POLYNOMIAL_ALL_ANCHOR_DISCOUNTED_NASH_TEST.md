# All-anchor discounted Nash: the polynomial minimizer has a zero-charge exit

Author: CODEX_FRECHET_CYCLE.

Status: completed bounded global-variational test, ordinary mathematics.
The proposed attack does not contradict a polynomial certificate and does
not produce a sure-root exit. Its exact surviving results are a uniform
all-anchor absorption bound, recovery of the already-known full standard-Q
condition, and a literal all-Continue fixed point at every global polynomial
minimum. No export, new excluded residual, or new equilibrium claim is made.

## 1. Self-contained question and finite data

There are four players, independent product Quit roots q∈[0,1]⁴,
nonempty-coalition rewards r(S) with |r_i(S)|≤M, M>0, and zero Never.
The intended application is canonical normal data, with own-singleton vector
s=(1,0,0,0), but the deductions below do not require normality or that
normalization. Set

    c(q)=∏_i(1−q_i),        a(q)=1−c(q),
    R(q)=Σ_[S≠∅]p_q(S)r(S),
    F(q,v)=R(q)+c(q)v,
    Q_i(q)=E[r_i(T∪{i})],
    C_i(q,v)=A_i(q)+α_i(q)v_i,
    α_i(q)=∏_(j≠i)(1−q_j),
    e_i(q,v)=max(Q_i(q),C_i(q,v))−F_i(q,v).

Here T is the product opponent coalition and A_i is the unconditional
reward from nonempty opponent absorption. Exact root Nash means e_i=0
for all i. It is not itself an unrestricted terminal Nash claim.

Fix B>M and a polynomial H satisfying the reviewed all-edge certificate:
for some δ>0 and EVERY v,w∈[−B,B]⁴ and q with

    |w−F(q,v)|∞≤δa(q),      e_i(q,v)≤δa(q) for all i,

one has H(v)−H(w)≥a(q). The only part used by this test is its restriction
to EXACT root-Nash/Bellman edges. In particular, this attack does not yet
exploit all the additional robust edges of the full certificate.

The proposed global mechanism was to choose a free artificial exit vector
z∈[−B,B]⁴ variationally and use stationary discounted-Nash existence to
obtain, for discount complement 0<λ<1,

    q exact root Nash against v,
    v=(1−λ)F(q,v)+λz.                                 (AN)

The anchor is an auxiliary synthesis datum, not a played-game payoff
intervention or an assumed jointly realizable punishment vector. The
objective was to force an absorbing edge uphill in H, or a sure-root
semantic certificate, by varying z over the ENTIRE box. No selected
discounted branch or approximate terminal equilibrium was supplied.

## 2. Exact existence source for the artificial-anchor family

This step does not assume undiscounted stationary equilibrium existence.
For a fixed z define the shifted reward table rᶻ(S)=r(S)−z. The checked
analytic discounted Bellman germ exists for this arbitrary finite table.
Along its physical domain, its root q is exact Nash against its live value
y and

    y=(1−λ)F_(rᶻ)(q,y),          λ=t^k↓0,

where k≥1 is the germ's ramification. Put v=y+z. Both endpoints and the
selected root value shift by z, so q is exact Nash for r against v.
Also F_(rᶻ)(q,y)=F_r(q,v)−z, which gives (AN).

These claims are exactly supplied by
`nonempty_analyticBellmanGerm_quittingGame`,
`quittingGermValue_eq_smul_rootSuccessorPayoff`, and
`isεQuittingRootEndpointNash_quittingGermRoot` in
`UniformEquilibrium/Quitting/Boundary/Analytic/Germ.lean`. The physical
restriction is 0<t<min(radius,1). A sequence λ↓0 suffices here; no
common germ, parameter radius, or continuity in z is assumed.

Every solution of (AN), not just a chosen germ, stays in the needed box.
Indeed, writing d=1−λ and a=a(q),

    v=[dR(q)+λz]/[λ+da].                              (1)

If a>0, this is a convex combination of R/a∈[−M,M]⁴ and z. If a=0,
it says v=z. Thus v∈[−B,B]⁴, and w=F(q,v), a convex combination of
the terminal reward lottery and v, also belongs to the box.

## 3. The polynomial controls ALL anchors and ALL roots uniformly

Let

    L=max_[x∈[−B,B]⁴] Σ_i|∂_iH(x)| < ∞.

For every solution of (AN), exact root Nash makes (v,q,w=F(q,v)) an
admissible certificate edge. Moreover

    w−v = [λ/(1−λ)](v−z).

The segment between v and w is inside the box. Therefore

    a(q)≤H(v)−H(w)
         ≤L|v−w|∞
         ≤2BL·λ/(1−λ).                              (2)

In particular a(q)/λ≤4BL when λ≤1/2. This estimate is uniform over
the WHOLE anchor cube and EVERY discounted root/value solution there.
It does not assert that the roots form a connected family, and needs no
root selection. Since q_i≤a(q), every root coordinate is O(λ) with the
same constant.

Thus the global certificate excludes absorbing zero-discount limits
through this source. It does not exclude the discount-matching regime
q_i≈λh_i, which is the actual remaining case.

## 4. The all-anchor matching limit recovers full standard Q

Fix z and take any sequence of the solutions from Section 2 with λ_n↓0.
By (2), after a subsequence

    q_(n,i)/λ_n→h_i≥0,        v_n→v.

All relevant vectors are uniformly bounded. If A=Σ_i h_i, finite product
expansion, with q_i=O(λ), gives

    a(q_n)/λ_n→A,
    R(q_n)/λ_n→Σ_j h_j r({j}).

The contributions of coalitions of cardinality at least two are O(λ²).
Divide the policy equation by λ and pass to the limit:

    (1+A)v=z+Σ_j h_j r({j}).                           (3)

Root Nash at q_n→0 implies v_i≥s_i. If h_i>0, then for all sufficiently
large n the coordinate q_(n,i) is strictly between zero and one; both
endpoints tie. Passing that equality to the limit gives v_i=s_i. Hence

    v−s≥0,           h_i(v_i−s_i)=0.                  (4)

Let Γ_ij=r_i({j})−s_i, so Γ_ii=0. Subtract (1+A)s from (3) and set
w=(1+A)(v−s). Equations (3)–(4) become

    h≥0,        w=z−s+Γh≥0,        h_iw_i=0.          (5)

These are exactly the textbook standard LCP equations with right-hand side
z−s. Because B>M and |s_i|≤M, the allowed anchors contain a neighborhood
of s. For ANY b∈ℝ⁴ choose t>0 sufficiently small that z=s+tb lies in
the box. Equation (5) at this z, divided by t, gives a solution with
weight h/t to the LCP w'=b+Γ(h/t). Thus Γ is a full standard-Q matrix.

This is a valid consequence of the polynomial certificate, but not a new
excluded residual. `StandardLCPSolution` and `IsStandardQMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean` use
precisely (5). The production declaration
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`
already places a counterexample's normal-core matrix on the nonhomogeneous
standard-Q side. The maintained full-normal-core reduction supplies the
full-matrix interpretation in the canonical contrary case. The stationary
gate in `Classification/LCP/ZeroSoloGeneratedStandardQ.lean` is another
existing home of the same unresolved standard-Q alternative.

The strict B>M condition matters in this deduction: it allows every
right-hand-side direction to be rescaled into the anchor cube. It is
available for the reviewed certificate's B=M+2. This step does not claim
that a single boundary anchor already tests all standard-Q right-hand sides.

## 5. A global H minimizer has the literal zero-charge escape

Choose ANY global minimizer z of H on [−B,B]⁴. Finite root-game Nash
existence gives an exact Nash root against z. For EVERY such root q,
w=F(q,z) remains in the box, so the all-edge certificate and minimality give

    a(q)≤H(z)−H(w)≤0.

Therefore q is all Continue. Since all Continue is root Nash exactly when
z_i≥s_i for every i, the complete conclusion is

    every global H minimizer z lies in z≥s,
    every exact root Nash at that z is all Continue.     (6)

The finite existence input is `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`; it requires only
the finite one-stage game, not any full-behavior equilibrium premise.

Now set q=0 and v=z. For EVERY 0<λ<1 this is an actual solution of the
auxiliary fixed-point equations (AN): F(0,z)=z, and q is Nash by (6).
Its edge charge is zero. Thus the proposed global-minimizer choice of
anchor cannot force a positive root through discounted-Nash existence:
the existence problem has a literal zero-charge solution at every discount.
No nonconvex Jensen inference, approximate-root limit, or degree calculation
is needed for this obstruction.

This does not prove that every other discounted solution at the same anchor
is zero, or that no more global mechanism can use other anchors. It proves
the exact limitation of this variational selection: existence alone is
already satisfied by the neutral point. That point is NOT C_sure, since
all Quit probabilities are zero, and its abstract continuation annotation
need not be a realizable terminal payoff.

As an exact boundary test, for the canonical H stress table recorded in
the polynomial separator proof, M=3 and s=(1,0,0,0). At anchor
z=(3,3,3,3), q=0,v=z solves (AN) at every discount, even though the
same solved table has an exact charged three-cycle elsewhere in payoff
space. This does not exhibit a polynomial certificate on that table: the
cycle forbids one. It shows why an anchored zero-charge solution carries
no conclusion about other states, actual equilibrium, or the global sign.

## 6. Source comparison and exact stopping point

The narrow lookup began from `docs/TOOLKIT.md`'s weighted-packet,
analytic-source and standard-Q routes. In addition to the declarations
named above, two existing ordinary notes delimit this attempt:

- `CODEX_STRENGTHEN__FIN4_CAPACITY_POTENTIAL_STATIC_TOPOLOGY_SEPARATION.md`,
  Sections 6–8, separates a fixed-cap active field from passive singleton
  data and gives an abstract semialgebraic Zeno ledger. That is NOT a
  refutation of the current ALL-state relation; the present calculations
  do use the same table for every anchor. Nevertheless the limit in
  Section 4 loses all collision terms and returns to the existing matrix
  condition rather than exploiting finite collision effects.
- `CODEX_CEDAR__DISCOUNTED_RADIAL_DEBIASING.md` already computes the full
  behavioral refusal price of discounted roots. No stationary repetition,
  branch-switch repair, or new refusal-price calculation was attempted here.

Proved: the uniform estimate (2), the all-anchor LCP consequence (5), and
the all-minimizer uniqueness/neutral discounted solution (6).

Failed implication retained: global minimization of H plus discounted-Nash
existence does NOT force an absorbing edge or sure-root exit. The first
order all-anchor consequence merely recovers full standard Q, already
retained by the live counterexample classification.

Unproved: any constraint from this family that uses finite collision
effects beyond standard Q, or any contradiction to the global polynomial
certificate on a canonical contrary-case table. No further infinitesimal
expansion is planned in this route. A genuinely different next mechanism
must escape the proved neutral minimizer solution and use information
discarded by (5), rather than rename the same extremum or matching limit.
