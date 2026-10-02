# Full-relation quasiconvex exclusion without a matrix hypothesis

Owner: CODEX_HADAMARD.

This ordinary-mathematical consequence combines the quasiconvex boundary
argument in
[QUITTING_POTENTIAL_EXCLUSION](../gpt/QUITTING_POTENTIAL_EXCLUSION.md)
with FRECHET's full-box minimum lemma. CODEX_ALEXANDROV independently checked
this exact note, including the K'-only face probes, global-minimum step,
and strict-interior quasiconvex argument; see
[the independent review](../feedback/QUITTING_POTENTIAL_EXCLUSION__BY_CODEX_ALEXANDROV.md).
The result is not Lean-checked.

## Exact scope

Let there be finitely many players, n >= 2, and an arbitrary reward vector
r(S) for every nonempty quitting coalition, with |r_j(S)| <= M and M >= 0.
Each root is a product of independent Quit/Continue draws. Put

    s_i = r_i({i}),       L = M+1,
    K' = [-L,L]^n,        C = product_i [s_i,L],
    B = {x in C : x_i=s_i for some i}.

For a product root q, a(q) is its absorption probability and F(q,v) its
expected one-stage payoff with continuation v after all Continue. An exact
root Nash means that every player's prescribed mixture maximizes its
one-stage payoff against the other root mixtures and continuation v.

Assume P is continuous on K', differentiable on a neighborhood of C, and

    P(v) - P(F(q,v)) >= a(q)                         (E)

for EVERY v in K' and EVERY exact root Nash q against v. There is no
restriction to realized continuation payoffs, selected roots, or chosen
faces. All successors lie in K', by the reward bound and convexity of K'.

Then P is not quasiconvex on C. No matrix-Q, normality, positive-singleton,
or no-uniform-equilibrium assumption is required.

This applies to every polynomial satisfying the packet's full robust
relation on [-M-2,M+2]^n, by restricting to exact Nash/Bellman edges whose
sources lie in K'. The endpoint perturbations of the robust relation are
not needed here. P being differentiable only near C is enough, but its
continuity on all K' is used and must not be omitted.

## Proof

First, (E) implies the singleton-face inequality

    gradient P(x) dot (x-r({i})) >= 1
        whenever x in C and x_i=s_i.                (F)

At points below the upper faces this follows from the packet's explicit
exact one-quitter probe, whose adjusted continuation approaches x at order
h; differentiability at x makes the adjustment cancel between endpoints.
To retain K' at an upper coordinate, use the following adjustment instead:
for j != i with x_j<L set

    v_j^h = x_j + h/(1-h) * max(r_j({i,j})-r_j({i}),0),

and for x_j=L leave v_j^h=L. Set v_i^h=s_i. For upper coordinates,
Continue-minus-Quit tends to L-s_j >= 1, so their inequalities hold for
small h. For the other coordinates the packet's exact calculation gives
nonnegative Continue-minus-Quit. Both endpoints remain in K'. Applying
(E) to the resulting exact solo-i root and differentiating proves (F).

Every global minimizer z of P on K' satisfies z_i>s_i for every i. To see
this, finite root-game Nash existence supplies an exact q against z.
Minimality and (E) force a(q)=0. Thus q is all Continue, whose Nash
inequalities give z_i>=s_i, and consequently z belongs to C. If z_i=s_i,
(F) contradicts the nonnegative one-sided derivative at z along the
feasible segment toward r({i}). This is FRECHET's existing minimum lemma;
it does not assume positive absorption at a minimum.

Choose x minimizing P on B. If only coordinate i is lower-tight, the
one-coordinate first-order conditions give zero derivatives on free
interior coordinates and nonpositive derivatives on upper coordinates.
As L-r_j({i})>0 and the own-coordinate contribution vanishes, these signs
give gradient P(x) dot (x-r({i})) <= 0, contrary to (F). Thus at least two
coordinates of x are lower-tight.

Now every permitted one-coordinate variation in C remains in B. Writing
g=gradient P(x), this gives g_j>=0 at lower coordinates, g_j=0 at interior
coordinates, and g_j<=0 at upper coordinates. Condition (F) gives g!=0.
It follows that

    g dot (v-x) > 0 for EVERY v in the strict interior of C.    (G)

Suppose P were quasiconvex on C. If P(v)<P(x) at any v in C, continuity
allows v to be moved slightly into the strict interior while preserving
this strict inequality. Differentiable quasiconvexity gives
g dot (v-x)<=0, contradicting (G). Hence x minimizes P on C.

But a global K' minimizer z lies in C, while x cannot minimize on K'
because x has a lower-tight coordinate. Therefore P(z)<P(x), contradicting
minimality on C. This proves the claim.

## Sources and mathematical scope

The same-gradient and multiple-binding boundary facts already appear in
[TARSKI's reviewed note](CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR.md).
The full-box minimum lemma is Section 3 of
[FRECHET's convex exclusion](CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY.md).
The move from an inward nonzero gradient to global minimality on C under
quasiconvexity is the first half of the packet's Theorem 2. This note
records their composition, without an independent priority claim.

The exact source route was `docs/TOOLKIT.md`'s full robust relation and
rational-polynomial characterization. Declarations inspected:

- `IsQuittingFloorFreeRobustEdge` and
  `quittingFloorFreeRobustChargedRelation` in
  `UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`;
- `ChargedRelation.IsPotential` in `MathUE/ChargedPathBudget.lean`;
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
- `quittingRootCoordinateNashDefect` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`; and
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.

No external paper theorem is used. These were source inspections at commit
`5aac30ad2553dadd5895dc79fbc4f1f5680d7570`; no Lean check was run.

This does not remove Q from the packet's analytic theorem assuming only
face drift. Nor does it remove Q from its negative-curvature estimate:
adding a convexifying quadratic preserves the relevant face inequality
under that estimate but need not preserve (E) on all exact roots. No reward
table or unrestricted strategy class is excluded by this shape restriction.

The source and quantitative review is in
[the feedback file](../feedback/QUITTING_POTENTIAL_EXCLUSION__BY_CODEX_HADAMARD.md).
The theorem does not decide whether a coupled nonquasiconvex certificate
can satisfy the full relation.
