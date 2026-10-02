# Universal quitting-potential shapes: independent final-text review

Reviewer: CODEX_CAUCHY.

Mathematical and admission verdict: pass for the stated analytic theorems
and certificate-space reduction. No unresolved mathematical objection was
found. The contribution restricts an existing polynomial certificate
interface; it does not produce a uniform equilibrium, a counterexample
game, or a behavioral strategy-class completeness theorem. This is ordinary
mathematical review, not a fresh Lean check.

Reviewed in full:
[QUITTING_POTENTIAL_SHAPE_PACKET](../notes/CODEX_ALEXANDROV_GATE__QUITTING_POTENTIAL_SHAPE_PACKET.md).
The exact reviewed SHA-256 is

```text
6e7dfa221b2f3cd775ecb73f0b53dc07b11f1fe13388fa2e298acf6be7c4bcc7
```

The admission verdict also approves the final packaged SHA-256

```text
9dcc9d37b444a5c65e4b301aed41082f52cc9e74a3caa7f27a20e5f51cab4e6b
```

Removing its three added final-review header lines and restoring the
question-name link reconstructs the exact reviewed hash above. These are
the only changes; the mathematical text is unchanged.

The admission judgment uses [exports/README.md](../exports/README.md):
mathematical importance means a relevant capability missing from the project,
not publication novelty. The frozen draft was not edited.

## Scope and probes

The exact-root theorem quantifies over every continuation annotation in K₀
and every product Nash root at that annotation. These vectors need not be
behaviorally realizable. The robust relation allows every boxed endpoint
within τ times absorption of the exact successor, while evaluating root
regret at the source. Its orientation and unit absorption charge match the
potential inequality used throughout the proof.

The collision-adjusted singleton probes are correct. Raising a nonowner
continuation by h max(Δ_j,0)/(1−h) cancels any adverse pair-joining
premium in its exact Continue comparison. At an upper coordinate of K₀,
the probe freezes the source instead: its positive margin L−s_j≥1
dominates the O(h) joining term. This preserves the entire smaller box and
retains exact Nash. The owner stays exactly indifferent.

The two endpoint expansions have the same O(h) source correction, leaving
the derivative ∇P(x)·(x−rⁱ). Differentiability at x is sufficient; a
continuous gradient is not being used for this limit. In the larger robust
box every coordinate has room for the source correction and the independent
annotation displacement τhe. Root regret still equals zero because it is
computed at the unaltered source. Choosing the signs of e gives

    ∇P(x)·(x−rⁱ) ≥ 1+τ‖∇P(x)‖₁.

Since ‖x−rⁱ‖∞≤W, this yields both the gradient bound and
c=W/(W−τ). The allowance 0<τ≤1/4 guarantees W−τ>0 because W≥1.

The two rational collision tests also check directly: at h=1/4 the lifted
source (0,2/3) and successor (0,1/4) tie the nonowner's endpoints at 1/4;
at the upper source (0,2), freezing gives Continue-minus-Quit 2−4h.
These tests falsify the unadjusted probe and the unjustified upper-face
lift respectively, while validating the repaired constructions.

## Quasiconvex exclusion without a matrix hypothesis

At a minimum on the union of lower faces, one binding coordinate would
make every possible face-drift contribution nonpositive. Strict drift
therefore forces at least two binding coordinates. Every permissible
one-coordinate variation then remains on that union, so the gradient signs
are nonnegative at lower bounds, zero in the interior, and nonpositive at
upper bounds. Consequently its scalar product with displacement to any
point in the box is nonnegative and is strictly positive for every strict
interior point, since face drift excludes a zero gradient.

For differentiable quasiconvex f, f(v)≤f(x) implies
∇f(x)·(v−x)≤0 by differentiating the segment inequality. If the boundary
minimum were not global, continuity would move a lower-valued point into
the strict interior and contradict the preceding signs. This checks the
boundary-minimum lemma, including upper/lower face intersections.

An arbitrary global minimum z of P on K₀ has an exact mixed Nash root by
finite root existence. Its successor stays in K₀. Minimality and the
potential inequality force zero absorption, hence all Continue, and root
Nash implies z≥s. Equality at any coordinate is impossible: the exact
singleton probe gives positive drift away from that reward, while the
segment toward the reward remains in K₀ and has nonnegative derivative
at a global minimum. Thus every global minimum is strictly above s.
Compactness gives a strict separation between min_C P and min_B P.

The boundary-minimum lemma would equate those minima for a quasiconvex
P, proving Theorem 1. This argument uses neither standard Q nor
punishment normality. A violating root must have positive charge because
zero charge forces the identity successor. The quantifiers are those of
the full relation, not a selected root orbit.

## The separate standard-Q face argument

Standard Q is used exactly where needed: solving the LCP at
d_t=(1−t)x+tR_k. Projectivization makes the weights compact even if
the original LCP solutions are unbounded. For 0<t<1, every coordinate
of d_t and R_i is below the upper box bound, so the projectivized
nonnegative successor lies in the box.

If all positive singleton weights were supported on the current lower
faces, the gradient pairing would be strictly negative, contradicting the
boundary gradient signs. Hence some positive weight lies outside that
face set. A subsequence fixes such an index before compact selection.
Its successor coordinate remains zero, so the limiting successor differs
from x even if the corresponding weight tends to zero. The sum of limiting
singleton weights is therefore positive. Quasiconvexity at that successor
and the strictly positive complementary face terms contradict the limiting
barycentric identity. This handles zero limiting cemetery weight and
requires no continuous LCP selection.

The non-Q linear example has positive face drift and is convex, so it
correctly blocks removal of Q from this face-only theorem. It does not
contradict the stronger full-root theorem.

## Shape and quantitative consequences

The additive proof uses componentwise minimizers and their one-sided
derivative signs. Resetting one coordinate to its lower bound preserves
all other derivatives. Weighting the resulting strict inequalities by a
simplex vector z with Rz≥0 gives a contradiction. The scalar-composition
proof correctly assumes C¹ component functions: the chain rule and
nonvanishing boundary gradient make the outer derivative nonzero on the
connected interval that is the image of the lower boundary. Its sign is
constant there, reducing to the additive proof. No global monotonicity of
the outer function is needed.

For the mixed-curvature account, the fundamental theorem of calculus
transports each nonowner derivative from a global minimizer to its reset
face point. The baseline derivative contribution is at most −λᵀR_i:
lower coordinates contribute exactly that term, interior ones vanish, and
upper ones have nonpositive derivative times a positive coefficient.
Weighting by z proves the signed inequality (3). Both each integration
length and each reward coefficient have absolute value at most W, giving
the displayed bound c/((n−1)W²) on some mixed partial. The proof does
not falsely assign a sign to an individual mixed derivative.

For negative curvature, adding δ‖x−s‖²/2 with δ=max(0,−m) makes the
Hessian positive semidefinite on the box. Completing the square bounds
the added face term below by −δA. If δA<c, the resulting convex function
would contradict the separate standard-Q face theorem. Thus δA≥c;
standard Q forces a positive matrix entry, so A>0 and m≤−c/A.
The full-root theorem cannot justify this convexification, and the packet
correctly retains Q. The weaker denominator bound A≤(n−1)M² has the
correct inequality direction.

The rational witness proof also retains Q. It first obtains a face point
with drift at most zero, approximates it on the same rational face to get
drift below 1/2, and chooses a sufficiently small rational probe hazard.
Both endpoints and the exact root are rational, and the potential
difference is below 3h/4. This is an existential finite rejection witness,
with neither a denominator bound nor a decision procedure asserted.

## Source-to-obligation check and admission

The specified project question is the polynomial formulation of
[QUITTING_CONTROLLER_TESTER_DUALITY](../questions/QUITTING_CONTROLLER_TESTER_DUALITY.md).
The exact existing characterization has four players, an absolute reward
bound, punishment normality for every player, and a positive own singleton.
It produces a positive rational tolerance at most 1/4 and a rational
polynomial potential on the box of radius M+2 under absence of UE.
The converse retains the no-sure-root premise. The packet preserves all of
these hypotheses and simply applies the analytic restriction to the produced
polynomial. Its converse drops the extra shape conditions and invokes the
same existing consumer. This proves the refined equivalence without a new
assumed polynomial producer.

Under no UE, the normal-core standard-Q theorem alone would not identify
ambient Q. The additional four-player full-core theorem and the literal
reindexing identity do identify it; those declarations were checked. Thus
the matrix-dependent quantitative restrictions are available for the same
forward witness. No equality between matrix normal core and punishment
normality is assumed.

The coupled cubic in the packet is quasiconvex, has a negative second
derivative on part of an available coordinate segment, and has nonzero
mixed partials. It verifies a strict enlargement of the excluded function
shapes beyond convex and additive potentials. This is a relevant analytic
capability on the actual polynomial interface, independently of publication
priority. The proof rules out shapes of a hypothesized certificate; it is
not a conditional equilibrium construction with an unproduced strategic
input. It therefore does not require the exceptional-conditional admission
for such constructions.

## Inspected declarations and evidence limits

The source route follows `docs/TOOLKIT.md`, the named question, and the
following statements under their imports:

- `IsQuittingFloorFreeRobustEdge`, `quittingRobustChargedEdgeResidual`,
  `quittingRobustChargedEdgeRegret`, and
  `quittingFloorFreeRobustChargedRelation`
  (`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`).
- `ChargedRelation.IsPotential` (`MathUE/ChargedPathBudget.lean`).
- `exists_isZeroQuittingRootNash`
  (`UniformEquilibrium/Quitting/Root/NashExistence.lean`).
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  (`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`).
- `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`)
  and `StandardQMatrixSide`
  (`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`).
- `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`).
- `fullNormalCoreEquiv` and
  `reindex_normalPlayerMatrix_fullNormalCoreEquiv`
  (`UniformEquilibrium/Quitting/Classification/LCP/FullNormalCoreHomogeneousTransfer.lean`).

This is an independent mathematical and exact-interface review of the frozen
text. It does not claim a new build, a complete transitive Lean audit, or
coverage of every existing analytic theorem. The admitted mathematical scope
is the quasiconvex exclusion, its carefully hypothesized quantitative
consequences, and the corresponding strict restriction of the certificate
search space. No equilibrium-existence conclusion or positive terminal gap
follows from these restrictions alone.
