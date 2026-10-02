# Universal quitting-root drift cannot be additively separable

Owner: CODEX_RADO_BOUNDARY.

Status: complete ordinary mathematical lemma; not Lean-checked. This is a
bounded, all-degree restriction on the current polynomial certificate, not
an equilibrium construction or an exclusion of arbitrary polynomials.
The summands below can be arbitrarily nonconvex. Keep internal: no export
or independent importance judgment is requested.

## 1. Question and exact statement

Let I be a nonempty finite player set. For every nonempty coalition S let
r(S) be its terminal reward vector, with |r_i(S)| ≤ M. Fix B > M, put
K = [−B,B]^I, and write s_i = r_i({i}). Each root uses independent private
Quit/Continue draws q_i ∈ [0,1]. Set

    c(q) = ∏_i(1−q_i),        a(q) = 1−c(q),
    F(q,v) = Σ_(S≠∅) p_q(S)r(S) + c(q)v.

Let Q_i(q) and C_i(q,v) be the literal Quit and Continue endpoints, and

    e_i(q,v) = max(Q_i(q),C_i(q,v)) − F_i(q,v).

All annotations v ∈ K are permitted; no terminal-law realization, punishment
floor, properness, support, or sure-quitter condition is imposed on them.

**Theorem.** There are no C¹ functions h_i on neighborhoods of [−B,B] such
that

    H(v) = Σ_i h_i(v_i)

satisfies

    H(v) − H(F(q,v)) ≥ a(q)                           (D)

for every v ∈ K and every exact root Nash q, meaning e_i(q,v) = 0 for all i.

The theorem allows arbitrary signed rewards and singleton levels. It
does not use normality, a positive singleton, or absence of a sure root.

In particular it excludes every additively separable rational polynomial
from the CURRENT robust relation in the controller/tester question, at
every degree and every positive tolerance δ. Indeed, an exact root with
w = F(q,v) is an edge of that relation: both its Bellman residual and its
Nash defects are zero, hence at most δa(q). Its endpoint belongs to K
because F is a convex combination of v and the bounded reward vectors.

## 2. The known exact-root starting facts

These facts are already proved in the singleton-face and convex-potential
notes linked below; their short arguments are included to expose every
quantifier used by the new minimization step.

Assume temporarily that a general C¹ H satisfies (D). For any owner i,

    v_i = s_i,   v_j ≥ s_j for j≠i
        ⇒  ∇H(v) · (v−r({i})) ≥ 1.                   (F)

First take every nonowner inequality strict and let only i quit, with
probability t > 0. Owner i is indifferent. For a nonowner j its exact
Quit-minus-Continue difference is

    (1−t)(s_j−v_j) + t[r_j({i,j})−r_j({i})].          (1)

It is negative for all sufficiently small t. Thus this is an exact Nash
root, with absorption t and successor v+t(r({i})−v). Dividing (D) by t
and taking t down to zero proves (F). For weak nonowner inequalities,
move those coordinates slightly toward B and use continuity of ∇H.
The admissible t need not be uniform in this approximation. In particular,
this does not falsely assert that the same solo root is Nash at every
intersection of singleton faces.

Every global minimizer z of H on K has

    z_i > s_i for every i.                           (2)

For finite root-game Nash existence supplies an exact q against z.
Minimality and (D) imply a(q) = 0, so q is all-Continue. Its Nash
condition is precisely z ≥ s. If z_i = s_i, (F) contradicts the
nonnegative one-sided derivative at z along the feasible segment toward
r({i}). This proves (2), including minimizers on upper box faces.

This argument uses an exact root at each arbitrary minimizing annotation,
then explicitly allows that root to have zero charge. It does not infer
positive absorption from finite Nash existence.

## 3. The separable lower-boundary minimum

Now use H(v) = Σ_i h_i(v_i). Define

    m_i = min_[−B,B] h_i,       m = Σ_i m_i,
    Δ_i = h_i(s_i) − m_i.

Every choice of scalar minimizers z_i forms a global H-minimizer.
Consequently (2) says that EVERY scalar minimizer of h_i lies strictly
above s_i. In particular Δ_i > 0. Choose scalar minimizers z_i once.

Put

    C = ∏_i[s_i,B],
    L = {v ∈ C : v_i=s_i for at least one i}.

For any v ∈ L choose a tight coordinate k. Then

    H(v) ≥ h_k(s_k) + Σ_(j≠k) m_j
         = m + Δ_k ≥ m + min_i Δ_i.

Choose i attaining min_i Δ_i and define

    x_i = s_i,       x_j = z_j for j≠i.

Equality holds in that lower bound. Therefore x minimizes H on L, and
it has exactly one tight coordinate. This is the additional step: it
uses additive separability, not convexity or a supporting hyperplane.

Give only i a sufficiently small positive hazard t. Formula (1) makes
this an exact Nash root. Its successor

    w = x+t(r({i})−x)

still belongs to L: coordinate i stays s_i; the finitely many other
coordinates stay strictly above their singleton levels for small t;
all coordinates remain at most B by convexity of the box. Thus

    H(w) ≥ H(x),

while (D) requires H(x)−H(w) ≥ t > 0. This contradiction proves the
theorem. For one player L is a singleton and the same argument is simply
the absorbing singleton self-loop.

## 4. Exact paired-table calibration

Use the literal c=1 table of the frozen paired-collision packet. It has
singleton vectors

    r(0)=(1,4,0,0), r(1)=(4,1,0,0),
    r(2)=(0,0,1,4), r(3)=(0,0,4,1),

and all pair-member rewards are 1. This table is already solved; this
test is not offered as a new equilibrium or as a hard-table claim.
Take B=6 and the genuinely nonconvex additive quartic

    h(t)=(t−2)²(t−3)²,       H(v)=Σ_i h(v_i).

Its scalar minima are 2 and 3, and h''(5/2)=−1, so the existing convex
exclusion does not apply to this H. Set

    v=(1,2,2,2),       q=(1/4,0,0,0).

The four Quit endpoints are (1,1,1,1); the Continue endpoints are
(1,5/2,3/2,3/2). Thus every prescribed root action is optimal, every
coordinate defect is exactly zero, and

    w=F(q,v)=(1,5/2,3/2,3/2),       a(q)=1/4,
    H(v)=4,       H(w)=83/16,
    H(v)−H(w)=−19/16 < 1/4.

These equalities were independently checked using exact rational
arithmetic. Only the singleton and owner-pair entries occur in this
root computation; no collision tester was omitted from its endpoint
test. This is a root-annotation test, not a full behavioral strategy
certificate and not a claim about the terminal exploitability of q.

## 5. Current-source accounting and stopping boundary

The current question is
[QUITTING_CONTROLLER_TESTER_DUALITY](../questions/QUITTING_CONTROLLER_TESTER_DUALITY.md).
Its floor-free robust relation has arbitrary boxed annotations, including
zero-charge and arbitrarily small positive-charge roots. The proof uses
a literal subset of those edges; it neither replaces the full relation
by that subset nor claims this subset is complete for general H.

Following the named routes in `docs/TOOLKIT.md`, the actual declarations
inspected were:

- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`;
- `IsQuittingFloorFreeRobustEdge` and
  `quittingFloorFreeRobustChargedRelation` in
  `UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`;
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
- `quittingRootCoordinateNashDefect`,
  `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`, and
  `isεQuittingRootNash_iff_coordinateNashDefect_le` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`.

The first declaration is the CURRENT normal-positive-singleton/no-sure-root
equivalence, not an older Simon finite-cell obstruction. This note adds
no strategic input to that source and makes no new fixed-payoff inference.
If the equivalence produces H under positive exploitability, this lemma
only says that H cannot be additive. For a polynomial H, at least one
mixed second partial derivative must therefore be nonzero somewhere.

Nearby prior results used or distinguished:

- [singleton-face test](CODEX_HILBERT__POLYNOMIAL_DRIFT_SINGLETON_FACE_TEST.md):
  (F), its robust strengthening, and its already-known homogeneous-LCP exit;
- [convex global-root exclusion](CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY.md):
  (2), the lower-boundary strategy, and the separate convexity argument;
- [potential-guided zero-charge test](CODEX_FRECHET_CYCLE__POTENTIAL_GUIDED_ANCHOR_ZERO_CHARGE_TEST.md):
  the failure of a gradient-guided anchor to produce an absorbing root;
- [nonpositive-diagonal quadratic exclusion](CODEX_FRECHET_CYCLE__NONPOSITIVE_DIAGONAL_QUADRATIC_ROOT_DRIFT_EXCLUSION.md):
  a different, quadratic-only class with a diagonal-sign hypothesis.

A narrow search found no existing additive, arbitrarily nonconvex,
all-degree exclusion in the relevant notes. The new piece is the exact
separable lower-boundary minimization in Section 3; the source facts in
Section 2 are not claimed as new. The result does not rule out coupled
nonconvex rational polynomials, supply an equilibrium, bound degree, or
resolve the conjecture. Stop this operation here. The concrete unresolved
question remains whether the coupled nonconvex class can satisfy the full
robust relation; no next degree search or barrier hierarchy is proposed.
