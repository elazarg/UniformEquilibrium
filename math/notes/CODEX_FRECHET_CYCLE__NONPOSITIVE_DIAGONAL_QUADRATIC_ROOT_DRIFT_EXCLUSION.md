# A nonpositive-diagonal quadratic cannot provide global charged-root drift

Author: CODEX_FRECHET_CYCLE.

Status: complete ordinary-mathematical bounded ansatz exclusion, not yet
independently reviewed and not Lean-checked. The Hessian may be INDEFINITE:
all cross coefficients are unrestricted, but every diagonal entry is
nonpositive. This is not an arbitrary-quadratic exclusion, a uniform-
equilibrium existence theorem, or a negative reward-table certificate.

## 1. Exact relation and the tested ansatz

Let I be finite and nonempty, with terminal rewards r(S)∈ℝ^I for every
nonempty coalition S⊆I. Assume |r_i(S)|≤M and own singleton levels

    s_i=r_i({i})≥0.

Let B>M and K=[−B,B]^I. A product root has independent Quit probabilities
q_i∈[0,1]. Define

    p_q(S)=∏_(i∈S)q_i ∏_(i∉S)(1−q_i),
    c(q)=∏_i(1−q_i),             a(q)=1−c(q),
    R(q)=Σ_(S≠∅)p_q(S)r(S),     F(q,v)=R(q)+c(q)v,
    Q_i(q)=Σ_(T⊆I\{i})p_(q,−i)(T)r_i(T∪{i}),
    A_i(q)=Σ_(∅≠T⊆I\{i})p_(q,−i)(T)r_i(T),
    α_i(q)=∏_(j≠i)(1−q_j),      C_i(q,v)=A_i(q)+α_i(q)v_i,
    e_i(q,v)=max(Q_i(q),C_i(q,v))−F_i(q,v).

Exact root Nash means e_i(q,v)=0 for every i. The continuation annotation
v need not be an actual terminal payoff. Since |R_i(q)|≤Ma(q), F(q,v)
belongs to K whenever v∈K.

The tested quadratic is

    H(v)=h+ℓ·v+½vᵀAv,       A=Aᵀ,       A_ii≤0 for all i.     (Q)

Every coefficient is otherwise arbitrary real; rational coefficients are
included. In particular, arbitrary bilinear cross terms are allowed.

THEOREM. No H of form (Q) satisfies

    H(v)−H(F(q,v))≥a(q)
      for EVERY v∈K and EVERY exact Nash root q against v.     (D)

The theorem uses actual product-root equations, not a chosen root orbit,
correlated roots, a restricted semantic carrier, or a supplied favorable
selector. No assumption concerning equilibrium existence is made.

The floor-free robust certificate asks for the stronger inequality
H(v)−H(w)≥a(q) for all v,w∈K satisfying

    |w−F(q,v)|∞≤δa(q),          e_i(q,v)≤δa(q) for all i.

It includes every exact edge in (D), for every δ≥0. Thus the theorem
excludes (Q) from that universal robust certificate language as well.
For canonical Fin4, s=(1,0,0,0) and B=M+2 satisfy the hypotheses.

## 2. Pure and stationary exact-root screens

These preliminary screens apply to EVERY potential, independently of (Q).
They explain why a known-equilibrium reward family should not be fitted.

If a nonempty coalition S with |S|≥2 satisfies all pure membership-toggle
inequalities

    r_i(S)≥r_i(S\{i})             for i∈S,
    r_j(S)≥r_j(S∪{j})             for j∉S,

then its pure root is exact Nash against every v. At v=r(S) it gives an
exact charged self-loop, contradicting (D). One unilateral deviation cannot
remove every sure quitter, so this is also an actual exact terminal Nash
profile against full behavioral deviations.

More generally, let a(q)>0 and put u=R(q)/a(q)∈[−M,M]^I. If q is exact
root Nash against u, then F(q,u)=u, again a charged self-loop. Under the
nonnegative-singleton hypothesis it is also an actual stationary terminal
Nash profile. Indeed, whenever α_i<1, the full stationary-opponent cap is

    max(Q_i, A_i/(1−α_i)).

Root Nash at u gives Q_i≤u_i and A_i+α_i u_i≤u_i, so this cap is at
most u_i. If α_i=1, all opponents always Continue; positive absorption
then makes i the sole active owner, u_i=Q_i=s_i, and its only endpoint
values are s_i at a finite Quit and zero at Never. Since s_i≥0, its
full cap is again u_i. These endpoints cover all mixtures of finite dates
and Never, hence all behavioral deviations on the unique live history.

These are rejection screens, not proofs that a table passing them lacks
equilibrium. No parametric reward table is retained or advertised as a
negative candidate in this note. The obstruction below applies to (Q) even
on an arbitrary table for which these preliminary screens find nothing.

## 3. Two existing exact-edge consequences, with proofs

Temporarily let H be any C¹ function on a neighborhood of K satisfying
(D), without a quadratic or convexity premise.

### Singleton-face inequality

For every i and v∈K with v_i=s_i and v_j≥s_j for j≠i,

    ∇H(v)·(v−r({i}))≥1.                                      (F)

First assume v_j>s_j for every nonowner. Give only owner i a small
positive Quit probability t. Its endpoints both equal s_i. A nonowner j's
Quit-minus-Continue difference is

    (1−t)(s_j−v_j)+t[r_j({i,j})−r_j({i})].

This is negative for all sufficiently small t>0, simultaneously for all
nonowners. Therefore the root is exact Nash, has charge t, and sends v
to v+t(r({i})−v). Divide (D) by t and let t↓0 to obtain (F).

For weak nonowner inequalities approximate each nonowner coordinate by
(1−ε)v_j+εB, keeping the owner's coordinate s_i. These approximants
stay in K and have strict inequalities since B>s_j. Continuity of ∇H
passes (F) to the limit. This does not assert a common positive root size
at an intersection of several singleton faces.

### Every global minimum is strictly above the singletons

Let z minimize H on K. Finite root-game Nash existence gives an exact
root at z. Minimality and (D) force its charge to be zero, so all-Continue
is Nash at z. Its endpoint inequalities are exactly z_i≥s_i for all i.

If some z_i=s_i, (F) gives ∇H(z)·(z−r({i}))≥1. But the segment from
z to r({i}) lies in K, and minimum optimality along it gives the reverse
inequality ∇H(z)·(z−r({i}))≤0. Contradiction. Hence

    z_i>s_i for EVERY i at EVERY global minimizer z.           (G)

Both facts already occur in the earlier C¹-convex note, before its use of
convexity. They retain their full-box and all-exact-root quantifiers here.

## 4. Vertex minima and the quadratic reflection

Now assume (Q). Each one-coordinate restriction of H is concave because
its second derivative is A_ii≤0. A concave function on a compact interval
has a minimum at an endpoint. Applying this successively to all coordinates
shows that every coordinate box has a vertex attaining its global minimum
of H. Other, nonvertex minimizers may also exist.

Apply this to K. By (G), a minimizing vertex cannot have any coordinate
−B, since s_i≥0. Thus

    b=B·1 is a global minimizer of H on K.                     (V)

Let C=∏_i[s_i,B] and let L be its lower boundary:

    L={x∈C : some x_i=s_i}.

The finite union L of compact faces is nonempty. On each face one lower
coordinate is fixed and the same coordinate-concavity argument selects a
vertex minimizer in all remaining coordinates. Therefore H has a minimum
on L at a point x with every x_i equal to s_i or B. Let

    J={i:x_i=s_i},       h_i=B−s_i>0 for i∈J.

If J has exactly one member i, give only i a sufficiently small positive
hazard t. The exact root from Section 3 applies because all other x_j=B>s_j.
Its successor keeps coordinate i equal to s_i, keeps every other coordinate
strictly above its singleton for small t, and remains at most B. It belongs
to L. This contradicts H-minimality on L and the positive drift required by
(D).

Suppose instead |J|≥2. For each i∈J, the point x+h_i e_i remains in L,
because a different lower-binding coordinate is unchanged. Therefore

    0≤H(x+h_i e_i)−H(x)
      =h_i∂_iH(x)+½A_ii h_i².

Using A_ii≤0 gives

    h_i∂_iH(x)≥0                    for every i∈J.            (S)

Set d=b−x, so d_i=h_i on J and d_i=0 outside J, and reflect b in x:

    y=2x−b=x−d.

For i∉J, y_i=B. For i∈J,

    y_i=2s_i−B≥−B,       y_i<s_i<B.

Thus y∈K, but y is not strictly above the singleton vector. The lower
bound is exactly where nonnegative singleton levels are used.

Since H is quadratic, its equal opposite displacements have the same
quadratic part. Hence the exact identity is

    H(y)−H(b)
      =H(x−d)−H(x+d)
      =−2∇H(x)·d
      =−2Σ_(i∈J)h_i∂_iH(x)≤0,                               (R)

by (S). But b is a global minimizer by (V), so y is another global
minimizer. This contradicts (G). All cases are exhausted, proving the
theorem.

The reflection is a comparison inside the global optimization domain, not
a claim that y is the successor of x or that reflected root edges exist.
Every actual root used in the proof was explicitly Nash against its own
continuation annotation.

## 5. Exact scope and boundary tests

The excluded class is genuinely nonconvex. For example, in four variables

    H(v)=−½Σ_i v_i²+2v_0v_1

has Hessian eigenvalues 1, −3, −1, −1. Its diagonal entries are all −1,
so it lies in (Q), but it is indefinite. Arbitrary linear terms and constants
do not change these facts. The entire bilinear ansatz with no squared
coordinates is also excluded, since then A_ii=0.

The proof does NOT extend as written to a quadratic having some positive
diagonal entry: coordinatewise minima need not occur at vertices, and the
sign implication (S) is no longer available. Such a Hessian may still be
indefinite, so the remaining quadratic synthesis problem is not empty merely
as an algebraic class. No actual universal certificate in that remaining
class is constructed here.

For s_i<0, reflection may leave the box: y_i=2s_i−B<−B. The stated
theorem therefore retains s≥0, which includes the requested canonical
Fin4 setting. No conclusion for mixed signed singleton levels is inferred.

The drift coefficient 1 can be replaced by any fixed positive number by
rescaling H. Empty player sets are excluded because every charge is zero.
Strict padding B>M places every singleton below B and keeps the singleton-
face approximation and small-root successor inside the required box.

Together with the earlier convex C¹ exclusion, this says that a quadratic
certificate in the canonical problem would need both a negative eigenvalue
and at least one positive diagonal entry. These are necessary coefficient
conditions only. Their feasibility would not establish the universal edge
inequality or the separate absence of the semantic sure-root alternative.

## 6. Narrow source comparison and bounded outcome

The source interface was selected through `docs/TOOLKIT.md`. Current exact
declarations inspected at HEAD 7e7a4de include:

- `IsQuittingFloorFreeRobustEdge` and
  `quittingFloorFreeRobustChargedRelation` in
  `UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`;
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`;
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`; and
- `exists_stationaryAbsorbingRoot_generating_weightedPackets` in
  `UniformEquilibrium/Quitting/Projective/StationaryAbsorptionWeightedForwardPacket.lean`.

The [frozen polynomial packet](../formalized/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md)
has SHA-256
`14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`.
Its full-box exact-edge restriction is precisely (D). The packet and all
conference exports remain unchanged. No Lean build was run.

The earlier [convex global-drift exclusion](CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY.md)
supplies the already known consequences (F)--(G), not the reflection argument
for indefinite quadratics. Narrow searches for coordinatewise concavity,
nonpositive diagonal Hessians, bilinear potentials, and quadratic reflection
in the relevant notes and root/projective source found no earlier statement
of this restriction. This is a bounded source finding, not a priority claim.

The older [quadratic reset-rank test](CODEX_FRECHET_CYCLE__QUADRATIC_FULL_BOX_BARRIER_RESET_RANK_TEST.md)
uses a different eight-coordinate payoff/cap domain and monotonicity under
ALL semantic prefixes, not Nash roots. Its reset rank argument is not
transferred to the current four-payoff-coordinate relation; its reward
family was also independently solved and is not a negative candidate.

The bounded outcome is the exact coefficient-class exclusion (Q), not a
table subclass theorem. The remaining question is actual universal
quadratic feasibility with some positive diagonal and a negative eigenvalue.
No candidate table passed a full stationary/periodic exclusion and universal
root test in this work, and no positive all-behavior gap is claimed.
