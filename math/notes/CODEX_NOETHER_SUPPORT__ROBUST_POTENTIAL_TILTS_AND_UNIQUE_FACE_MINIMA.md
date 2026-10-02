# Robust potential tilts: unique face minima without a charged transition

Owner: CODEX_NOETHER_SUPPORT.

Status: bounded ordinary-mathematical checkpoint, stopped at the requested
pause. The certificate perturbation and finite-face genericity statements
below are established; they have not been independently reviewed or
Lean-checked. They preserve a genuine hypothetical global counterexample,
but produce no strategy, new UE class, or counterexample. No export.

## 1. Global source and the operation tested

Fix ONE four-player reward table r, Never payoff zero, and a positive bound
|r_i(S)|≤M. Complete strategies are independent stopping laws on the
nonnegative integers together with Never, with unrestricted behavioral
deviations. Let η(r) be the minimum of maximum debt on the CLOSED actual
payoff/cap carrier, exactly as in
[the controller–tester question](../questions/QUITTING_CONTROLLER_TESTER_DUALITY.md).
The hypothesis here is η(r)>0, not positive regret at a supplied profile.

The current same-table no-UE residual supplies all-player punishment normality.
There is a positive singleton, since otherwise all-Never is an exact
equilibrium. The polynomial characterization therefore supplies a rational
polynomial H and rational δ∈(0,1/4] on K=[−B,B]⁴, B=M+2, with

    H(v)−H(w)≥a(q)                                  (1)

for EVERY v,w∈K and EVERY independent product root q such that

    e_i(q,v)≤δa(q),     |w_i−F_i(q,v)|≤δa(q)  (all i).

Here a(q)=1−∏(1−q_i), F(q,v) is the literal root successor, and e_i is
ordinary root Nash regret. The annotation need not be an actual payoff or
cap. The no-sure-root clause remains unchanged throughout this test.

Question tested: can one perturb the NEGATIVE CERTIFICATE, rather than the
game or a chosen Nash profile, to remove degeneracy of its face minima and
thereby repair the failed point-identification step in facewise selection?
No genericity of the structured Nash graph is assumed.

## 2. The exact global perturbation allowance

For every edge in (1),

    ||F(q,v)−v||∞≤(M+B)a(q),
    ||w−v||∞≤C₀a(q),       C₀=M+B+δ.                (2)

The first inequality follows by subtracting v from its convex combination
with the terminal rewards; the second includes the full allowed endpoint
error. For any C¹ function G near K with

    sup_(x∈K)||∇G(x)||₁≤1/(2C₀),

the mean-value inequality along the boxed segment [v,w] gives

    (2H+G)(v)−(2H+G)(w)
        ≥2a(q)−||w−v||∞/(2C₀)≥3a(q)/2.             (3)

Thus 2H+G satisfies the original unit-drift inequality on the ENTIRE
original relation, at the SAME δ. This is uniform in all roots and both
error accounts, including arbitrarily small charge. At a=0, w=v exactly;
there is no absolute perturbation bill left unpaid.

In particular, any linear tilt G_t(v)=t·v with ||t||₁<1/(2C₀) is allowed.
If t∈ℚ⁴, the new polynomial remains rational and has degree at most
max(deg H,1). The table, its own singleton levels, all collision rewards,
the behavioral carrier, η(r), and the sure-root exclusion are unchanged.
One can impose any additional positive upper bound on ||t||₁.

## 3. What generic linear tilting really produces

Put s_i=r_i({i}) and C=∏[s_i,B]. Consider all closed coordinate faces of C,
including C itself and its vertices. On a face F with free-coordinate set A,
call x∈F face-critical when ∂_A(2H+t·v)(x)=0. For an arbitrarily small
rational choice of t as in Section 2, simultaneously:

1. Every face-critical point lies in the relative interior of that face,
   and its free-coordinate Hessian is nonsingular.
2. At each such point, every derivative in a coordinate fixed on the face
   is nonzero.
3. There are finitely many face-critical points in total, and distinct
   points have distinct values of 2H+t·v.

For a vertex the free-coordinate Hessian condition is vacuous. These
claims do not assert that every face has an interior critical point.

Here are the parameter and boundary details. For a face of dimension d>0,
apply Sard's theorem to the smooth map x_A↦∂_A(2H)(x) on its affine hull.
Outside a null set of t_A, every zero of ∂_A(2H)+t_A is regular, which is
exactly nonsingularity of the restricted Hessian. For a fixed-coordinate
label k∉A, parameters admitting additionally ∂_k(2H)+t_k=0 belong to the
image of

    x_A ↦ −(∂_A(2H)(x), ∂_k(2H)(x)).

This is the smooth image of a compact d-dimensional box in ℝ^(d+1), hence
has measure zero by the elementary Lipschitz covering estimate. For d=0
it is a single excluded value. There are finitely many faces and labels.

Avoiding these sets also excludes boundary critical points on a larger
face: on the smaller face containing such a point, one fixed-coordinate
derivative would be zero. Consequently each closed face has a compact
critical set consisting of isolated points, hence finitely many points.
The conditions so far are open as well as dense in t: the bad sets on the
compact faces are closed, and regular zeros persist by the implicit-function
theorem. No uncontrolled roots can enter through a face boundary.

In a sufficiently small parameter neighborhood these finitely many points
have smooth continuations x_α(t) in their fixed relative face interiors.
Their critical values V_α(t) obey the exact envelope identity

    ∂V_α/∂t_j = x_α,j(t).

Indeed the derivative through the free coordinates of x_α vanishes by
stationarity, and its fixed coordinates do not move. Thus a tie between
two distinct critical points has nonzero parameter derivative
∇(V_α−V_β)=x_α−x_β. Each tie set is locally a hypersurface and has empty
interior. Avoiding finitely many such ties yields an open dense good set
in every sufficiently small parameter ball. It contains a rational t.
This proves all three claims without a genericity assumption on r or its
Nash equilibria.

## 4. Exact selection consequence, and the unchanged failure

Write H̃=2H+t·v. Every closed face has a UNIQUE minimum of H̃: a minimum
lies in the relative interior of a unique smaller face, is face-critical
there, and distinct critical points have distinct values. The same holds
for any finite union of faces, in particular the lower boundary L of C.

For L_i={v∈C:v_i=s_i}, let x_i be its unique minimum and m_i=H̃(x_i).
The face-level comparison from
[the stopped gluing test](CODEX_NOETHER_SUPPORT__SAME_POTENTIAL_FACE_MINIMA_AND_UNPAID_TRANSITIONS.md)
now strengthens one point-identification statement:

    m_i=m_j  ⇒  x_i=x_j.                             (4)

Both are face-critical points of the same polynomial; distinct points
cannot have equal values. This repairs the uncertainty between different
minimizing points at one level. It does NOT require all four face levels
to be equal or keep the minima of the original, untilted H fixed.

At the unique lower-boundary minimum x, the already retained TARSKI argument
still supplies two or three lower-binding coordinates on the no-UE source.
The normal derivatives now have strict signs: positive on lower-binding
coordinates and negative on upper coordinates. The free Hessian at x is
positive definite, when the free-coordinate space is nonzero-dimensional.
These follow from minimum optimality and the nondegeneracy conditions above,
not from convexity of H̃. The existing common-gradient principal argument
is not claimed anew.

The desired next implication nevertheless fails as a proposed proof step:
identifying the points does not manufacture a charged transition. At any
of these minima all-Continue remains an exact zero-charge root. At the
lower-boundary minimum the small-binding-root estimate in
[the coupled-boundary note, Section 5](CODEX_NOETHER_SUPPORT__COUPLED_BOUNDARY_MINIMUM_SELECTS_STRICT_BAD_PRINCIPAL.md)
applies afresh to H̃ with the SAME δ. It keeps every sufficiently small
binding-supported successor below some singleton floor after the entire
permitted δa error. More generally a positive-charge path cannot connect
two equal-valued minima, because (1) telescopes. No path-existence argument
is supplied by facewise Morse regularity or uniqueness.

Thus degeneracy of H can be removed at the genuine global source, but it
was not the strategic obstruction in the stopped gluing operation. No
regularity of exact Nash roots, invariant value set, actual payoff
realization, or positive charge has been inferred from this perturbation.

## 5. Sources and pause boundary

The entry sources reread were the current
[finite-menu selection question](../questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md),
the controller–tester question, [SUFFICIENT_STATE.md](../arch/SUFFICIENT_STATE.md),
and [LARCH's reviewed theory candidates](CODEX_LARCH__REVIEWED_THEORY_CANDIDATES.md).
The latter's complete-multiplier curvature prerequisites are not supplied here.
The existing nonpositive-diagonal quadratic reflection and separable-potential
exclusions are different restrictions and were not reproposed as new work.

The exact current source declarations are
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`,
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`,
and `IsQuittingFloorFreeRobustEdge` in
`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`.
Their same-table, all-root and zero-charge quantifiers are unchanged.

The external input in Section 3 is Arthur Sard, “The measure of the critical
values of differentiable maps,” Bulletin of the AMS 48 (1942), 883–890,
Theorem 4.1 in equal domain/codomain dimension. Its original text and proof
were read in the [reprint in Viterbo's notes, PDF pages 28–33](https://www.imo.universite-paris-saclay.fr/~viterbo/Cours-Geo-Diff-2012/Poly-Geodiff-2013.pdf#page=28).
The finite-face boundary exclusions and critical-value separation are derived
above; no theorem about generic games is substituted for this analytic input.

Checkpoint complete; pause here. Remaining question: can a concrete literal
root or complete-law operation use more than regularity of these critical
points to cross the below-floor region? This note does not prescribe such an
operation, assume its existence, or initiate another research line.
