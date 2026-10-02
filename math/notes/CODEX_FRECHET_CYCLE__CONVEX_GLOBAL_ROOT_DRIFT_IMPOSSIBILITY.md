# No C¹ convex global quitting-root drift potential

Owner: CODEX_FRECHET_CYCLE. Complete ordinary mathematical proof; not
Lean-checked. This is a restriction on a certificate class, not a theorem
excluding arbitrary nonconvex polynomials or producing an equilibrium.
The nonsmooth envelope extension is separate from this proof.

## 1. Exact theorem and finite data

Let I be a nonempty finite player set. Each player independently chooses
Quit or Continue at a root. For every nonempty coalition S⊆I let
r(S)∈ℝ^I be its absorbing reward vector, with

    |r_i(S)|≤M,

where M≥0. Let B>M, K=[−B,B]^I, and s_i=r_i({i}). In particular
−B<s_i<B for every i. Never may have reward zero; its value is not used
in this root-level theorem.

For q∈[0,1]^I define

    c(q)=∏_i(1−q_i),       a(q)=1−c(q),
    R(q)=Σ_(S≠∅)p_q(S)r(S),
    F(q,v)=R(q)+c(q)v.

Let Q_i(q) be player i's expected payoff from immediate Quit, and
C_i(q,v) its expected payoff from Continue against the same product
opponents, with continuation v after all players Continue. Thus

    F_i(q,v)=q_iQ_i(q)+(1−q_i)C_i(q,v),
    e_i(q,v)=max(Q_i(q),C_i(q,v))−F_i(q,v)≥0.

An exact root Nash means e_i(q,v)=0 for every i. This is a finite one-stage
game against the supplied vector v, not a claim that v is an actual terminal
payoff or that the root controls all later behavioral deviations.

**Theorem.** There is no function H which is C¹ on a neighborhood of K,
convex on K, and satisfies

    H(v)−H(F(q,v))≥a(q)                               (D)

for EVERY v∈K and EVERY exact root Nash q against v.

All endpoints F(q,v) lie in K: they are convex combinations of v and
the bounded absorbing reward vectors. The theorem assumes no canonical
normalization, punishment normality, positive singleton, no-equilibrium
premise, minimum semantic carrier, matrix class, or root selection.

For any supplied C¹ convex H, the conclusion equivalently gives an actual
finite root q and v∈K with e(q,v)=0 and

    H(v)−H(F(q,v))<a(q).

Such a violating root necessarily has a(q)>0, since q=0 is the identity.
The drift coefficient 1 can be replaced by any fixed strictly positive
number, by rescaling H.

## 2. The singleton-face inequality

Assume temporarily that a C¹ function H satisfies (D), without assuming
convexity. For each i and every v∈K with

    v_i=s_i,       v_j≥s_j for all j≠i,

one has

    ∇H(v)·(v−r({i}))≥1.                              (F)

First suppose all the nonowner inequalities are strict. Give only owner i
hazard t>0, all other players hazard zero. Its two endpoints are both s_i.
For every nonowner j, its Quit-minus-Continue difference is exactly

    (1−t)(s_j−v_j)
      +t[r_j({i,j})−r_j({i})].                       (1)

It is negative for all sufficiently small positive t, since v_j>s_j.
There are finitely many players, so one t-range works for all of them.
The root is exact Nash in that range. Its absorption is t and

    F(q,v)=v+t(r({i})−v).

Apply (D), divide by t, and let t decrease to zero. Differentiability
gives (F). This remains valid if some coordinates of v are on the upper
box boundary: the entire displayed segment stays in K.

For weak nonowner inequalities replace each nonowner coordinate by

    v_j^(ε)=(1−ε)v_j+εB,        0<ε<1,

while keeping v_i^(ε)=s_i. Because B>s_j, all nonowner inequalities are
now strict. These vectors remain in K and converge to v. Continuity of
∇H passes (F) to the limit. The small Nash-root size may depend on ε;
no uniform admissibility at an intersection of singleton faces is assumed.

This is the exact-edge version of the already recorded singleton-face
inequality. Collision rewards appear in (1), where finiteness is enough
to obtain a small exact root; they are not set to zero or discarded from
the root Nash test.

## 3. Every global minimum is strictly above all singletons

Let z be any global minimizer of H on K. Finite mixed Nash existence
supplies an exact root Nash against z. For every such q, (D) and
minimality give

    0≤a(q)≤H(z)−H(F(q,z))≤0.

Thus q=0. All-Continue is root Nash exactly when z_i≥s_i for all i,
because its Quit payoff is s_i and its Continue payoff is z_i. Hence
every global minimizer lies in the upper singleton orthant.

In fact all these inequalities are strict. Suppose z_i=s_i. Apply (F):

    ∇H(z)·(z−r({i}))≥1.

But the feasible segment z+t(r({i})−z), 0≤t≤1, stays in K. Since z
minimizes H on K, its one-sided directional derivative along this segment
is nonnegative:

    ∇H(z)·(r({i})−z)≥0.

The two inequalities contradict each other. Therefore

    z_i>s_i for every i at every global minimum.       (2)

This argument allows a minimum on any upper box face. It does not require
an interior critical point or replace the global minimum by an actual
game payoff. Convexity has not yet been used.

## 4. A convex potential cannot minimize on the lower boundary

Now assume H is also convex on K. Put

    C=∏_i[s_i,B],
    L={x∈C : x_i=s_i for at least one i}.

Both sets are nonempty and compact. Let m=min_K H. By (2), every global
minimizer belongs to C but none belongs to L. Consequently

    b:=min_L H>m.

Choose x∈L with H(x)=b, and choose a global minimizer z. Let
J={i:x_i=s_i}; this set is nonempty.

Suppose |J|≥2. For each coordinate k, the entire one-coordinate segment

    x+t(z_k−x_k)e_k,       0≤t≤1,

belongs to L. It stays in C because both coordinate endpoints do. At
least one lower-tight coordinate different from k remains unchanged.
Therefore minimality of x on L gives

    ∂_kH(x)(z_k−x_k)≥0.

Sum over k to obtain ∇H(x)·(z−x)≥0. Convexity and differentiability
on the segment from x to z give the supporting-gradient inequality

    H(z)≥H(x)+∇H(x)·(z−x)≥b,

contradicting H(z)=m<b. Thus J has exactly one member, say i.

This step is valid even when some other coordinates of x or z equal B.
The one-coordinate segments, rather than an unsupported interior KKT
condition, supply all required directional inequalities.

## 5. The literal solo root gives the contradiction

At the boundary minimizer x just obtained,

    x_i=s_i,       x_j>s_j for every j≠i.

Give only i a sufficiently small positive hazard t. By (1), this is an
exact root Nash against x. Its successor is

    w=x+t(r({i})−x).

The owner's coordinate stays exactly s_i. The other coordinates stay
strictly above their respective singletons for small t, since they start
strictly above them. They stay at most B because r_j({i})≤M<B and
x_j≤B. Hence w∈L.

Minimality on L gives H(w)≥H(x)=b. On the other hand (D) requires

    H(x)−H(w)≥t>0.

This is the contradiction and completes the theorem.

## 6. Consequences, boundary checks, and source status

The frozen robust-polynomial alternative implies (D) by restricting its
universal relation to exact Nash/Bellman edges. Therefore any polynomial
certificate supplied there must be genuinely nonconvex on the padded box.
Equivalently, its Hessian has a negative quadratic direction at some
interior point: if the Hessian were positive semidefinite throughout the
interior, the segment criterion and continuity would make H convex on K.
No obstruction to an indefinite or otherwise nonconvex polynomial follows.

The strictly padded box B>M is explicit. It places every own-singleton
below the upper face, permits the face approximation in Section 2, and
keeps all root successors in K. The proof has not been asserted for an
arbitrary smaller box or a restricted semantic carrier.

Nonemptiness of the player set is necessary: with no players every charge
is zero and a constant convex function satisfies (D). With one player the
proof still works, or one can directly use the absorbing self-loop at its
singleton payoff. No test requires a table without uniform equilibrium.

The narrow source search used `docs/TOOLKIT.md`'s weighted-packet and
root-Nash routes, followed by:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` for finite root-game
  existence at every continuation;
- `quittingRootCoordinateNashDefect` and
  `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean` for ordinary regret;
- the frozen polynomial packet
  `exports/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md`,
  SHA-256 `14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`;
- `notes/CODEX_HILBERT__POLYNOMIAL_DRIFT_SINGLETON_FACE_TEST.md` for the
  already derived singleton-face derivative inequality; and
- `notes/CODEX_FRECHET_CYCLE__POLYNOMIAL_ALL_ANCHOR_DISCOUNTED_NASH_TEST.md`
  for the existing non-strict all-Continue location of global minima.

The new step is the global convex lower-boundary argument, not a new
singleton first derivative or standard-Q test. Narrow searches of the
relevant notes, ideas, architecture, formalized packets, and root/weighted
source interfaces found no existing convex-envelope preservation theorem
or this convex global-drift impossibility. This is a bounded source finding,
not a claim to have surveyed every project file. No Lean build was run.

What remains separate: whether nonsmooth envelopes can preserve the robust
relation, and the original problem of excluding arbitrary nonconvex
polynomials or constructing an actual positive charged return. This theorem
does not settle either the quitting-game conjecture or the arbitrary
polynomial certificate alternative.
