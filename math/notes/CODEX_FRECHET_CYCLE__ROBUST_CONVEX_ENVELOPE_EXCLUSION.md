# Robust convex envelopes cannot preserve global quitting-root drift

Owner: CODEX_FRECHET_CYCLE. Complete ordinary mathematical companion to the
frozen C¹ convex no-go; not independently reviewed or Lean-checked. This
settles the proposed convex-envelope operation, not the existence of an
arbitrary nonconvex certificate. No regularity or degree optimization is
undertaken.

## 1. Exact claim

Use the finite quitting-root data of
`CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY.md`, frozen SHA-256
`7abde160a5d8715f1c3b42e19e18f3a248e571f6c157864b77a59bfbf99b8a23`:
a nonempty finite player set, |r_i(S)|≤M, B>M, K=[−B,B]^I,
F(q,v)=R(q)+c(q)v, a(q)=1−c(q), and ordinary regret e_i(q,v).

Fix ANY δ>0. There is no bounded convex function f:K→ℝ satisfying

    f(v)−f(w)≥a(q)                                   (R)

for EVERY v,w∈K and independent product root q with

    ||w−F(q,v)||∞≤δa(q),
    e_i(q,v)≤δa(q) for every i.                       (E)

Convexity is meant on the full coordinate box, not on a selected semantic
carrier or a single root's Nash polytope. No differentiability is assumed.
The coefficient 1 can be replaced by any fixed positive coefficient by
rescaling f. This statement does not assert the corresponding nonsmooth
impossibility when δ=0.

## 2. A bounded one-sided convolution preserves both convexity and exact drift

Suppose f satisfied (R). Put

    B'=(B+M)/2,       d=B−B'>0,
    η=min(δ/2,d/4)>0,
    K'=[−B',B']^I.

A finite convex function is continuous on the relative interior of each
face of a box. There are finitely many faces, so f is Borel on K. Its
assumed boundedness makes the extension f̃=0 outside K a bounded,
compactly supported Borel function on ℝ^I.

Choose a smooth nonnegative compactly supported probability density ρ
whose support lies inside (0,η)^I. Define

    V(x)=∫ρ(h) f̃(x+h) dh.

Convolution with a smooth compactly supported kernel makes V smooth on
all of ℝ^I; differentiation is on the kernel, not on f.

Let O=(-B'−d/4,B'+d/4)^I. For every x∈O and h in the kernel support,

    −B < −B'−d/4 < x_i+h_i
       < B'+d/4+η ≤ B'+d/2 < B.

Thus all points sampled on O use the original convex f, strictly inside
K. O is convex. For x,y∈O, the two translated points and their connecting
segment stay in K, so integrating the convexity inequality for f proves
that V is convex on O. In particular V is C¹ on a neighborhood of K'
and convex on K'. Zero extension has not been used to infer convexity
across the boundary of K.

Now take ANY exact root Nash q against ANY v∈K', and let w=F(q,v).
Because B'>M, w∈K'. For every h in the kernel support,

    F(q,v+h)=F(q,v)+c(q)h,
    (w+h)−F(q,v+h)=a(q)h.                            (1)

The endpoints v+h,w+h are in K, and the residual in (1) is bounded
by ηa(q)≤δa(q). To check regret, write

    α_i=∏_(j≠i)(1−q_j),       c=(1−q_i)α_i.

The two pure-action gains after the common shift are exactly

    Q_i−F_i(q,v+h) = Q_i−F_i(q,v)−c h_i,
    C_i(q,v+h)−F_i(q,v+h)
      =C_i(q,v)−F_i(q,v)+(α_i−c)h_i.

The original two gains are nonpositive by exact Nash. Since h_i≥0 and
α_i−c=q_iα_i≤a(q), both new gains are at most ηa(q). Therefore

    e_i(q,v+h)≤ηa(q)≤δa(q).

Every shifted triple is covered by (R), so

    f(v+h)−f(w+h)≥a(q).

Integrating gives

    V(v)−V(F(q,v))≥a(q)

on EVERY exact Nash/Bellman edge of K'. This contradicts the frozen C¹
convex theorem, since B'>M. The argument includes q=0 without division
by its charge. It uses no punishment floors, capacity-to-go function,
actual equilibrium source, or assumption about the sign of the table.

## 3. What this proves about the proposed envelope

For continuous H on K define its lower convex envelope by

    co H(v)=inf {Σ_k θ_k H(x^k):
                   θ_k≥0, Σ_kθ_k=1,
                   x^k∈K, Σ_kθ_k x^k=v},

where the infimum ranges over finite mixtures. This is a convex function
with

    min_K H≤co H(v)≤H(v)≤max_K H.

It is therefore bounded and is covered by Section 1. In particular, for
EVERY δ'>0 and EVERY γ>0 there is a literal root triple satisfying (E)
at tolerance δ' for which

    co H(v)−co H(w)<γa(q).

The violating root has positive charge. Thus this envelope cannot retain
any positive uniform absorption-drift rate on the entire robust relation,
even after an arbitrary fixed shrinkage of tolerance and rescaling.

If the original H is a supplied global polynomial certificate, its convex
envelope necessarily fails the proposed preservation property. This is a
conditional conclusion about that supplied H, not a claim that a table
admitting such an H has been constructed. No positive-gap game is needed
to prove the envelope-class exclusion.

The same-root compatibility issue is real but is not imposed as a new
hypothesis. For a fixed q the admissible (v,w) fiber in (E) is convex:
each regret is the maximum of two affine functions of v, and Bellman
matching is an affine strip. A contact decomposition for co H(v), however,
is taken over the entire K. If its points x^k all admitted the same root
and a common residual z=w−F(q,v), with all

    y^k=F(q,x^k)+z

still in K, then averaging the H drift would give

    co H(v)≥a(q)+Σ_kθ_k H(y^k)≥a(q)+co H(w).

The theorem proves that no such compatibility can be supplied on all
edges of a global certificate merely by taking its convex envelope.
There is no argument here that convexity of one fiber forces the global
contact points into that fiber. The obstruction survives nonsmoothness;
it is not repaired by leaving the envelope nondifferentiable.

## 4. Sources and stopping point

The only analytic ingredients beyond the frozen C¹ theorem are bounded
Borel convolution and the exact positive common-translation identities
already proved in Section 4.1 of
`exports/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md`.
The source formulas agree with `quittingRootCoordinateNashDefect` in
`UniformEquilibrium/Quitting/Root/NashDefect.lean` and the production
absorption-weighted packet interface. The smaller box is explicit and
still contains every reward strictly; no boundary extension of a convex
function is silently declared convex.

This is not the stopped small-piece/product-thinning argument. It does
not turn a convex balance of finite collision vectors into a time word,
and does not use a vanishing-hazard limit. The convolution integrates
inequalities for the same literal root at translated payoff annotations;
it is analytic averaging, not public randomization in the played game.

The convex-envelope simplification is now stopped. No subclasses of convex
potentials, degree bounds, or further regularity theorem are needed. The
remaining global certificate may be fully nonconvex, and the original
arbitrary-table positive construction remains open.
