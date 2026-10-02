# Universal potential exclusions: review synthesis

The packet contains a valid and useful exclusion of certificate shapes, not a
new reward-table existence class or an exclusion of arbitrary polynomial
certificates. The independent analytic and source reviews support its core
claims after the specification repairs below. No Lean check was performed.

Reviewed input: [QUITTING_POTENTIAL_EXCLUSION.md](../gpt/QUITTING_POTENTIAL_EXCLUSION.md),
SHA-256 `9ec1f05668d65f116f9ef33d12c9839e0ff136b4b81c00c5569f4e41274392ec`.
The inspected repository revision is
`5aac30ad2553dadd5895dc79fbc4f1f5680d7570`.

Independent reviews:

- [CODEX_ALEXANDROV](QUITTING_POTENTIAL_EXCLUSION__BY_CODEX_ALEXANDROV.md):
  exact root probes, quasiconvex boundary argument, projectivized LCP limit,
  rational violating edges, and negative-curvature argument.
- [CODEX_HADAMARD](QUITTING_POTENTIAL_EXCLUSION__BY_CODEX_HADAMARD.md):
  source correspondence, separability and scalar-transform scope, quantitative
  curvature accounts, prior-result comparison, and the stronger full-relation
  corollary described below.

## Mathematical content and its limits

The source hypothesis quantifies over every root edge in the padded payoff
box, with ordinary root Nash regret and Bellman error measured relative to
absorption. A certificate must drop by at least the edge's absorption. These
are the actual orientation and quantifiers of `IsQuittingFloorFreeRobustEdge`
and `quittingFloorFreeRobustChargedRelation`
(`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`).

The packet extracts derivative restrictions on every singleton lower face
using literal exact Nash probes. Under its stated matrix condition, the
face restrictions exclude differentiable quasiconvex functions. Its
quantitative accounts also force mixed-coordinate curvature and a negative
Hessian direction of a specified magnitude, with scale fixed by the unit
absorption coefficient. Rational quasiconvex polynomial candidates admit
literal rational exact-root witnesses violating that coefficient.

This tests a subset of the universal relation to disprove a candidate
certificate. It does not substitute that subset for the full certificate
test. No claim is made that satisfying the derivative conditions is enough
to certify nonexistence.

The exact polynomial characterization
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
(`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`)
retains its normality, positive-singleton, and sure-root conditions. A general
coupled nonquasiconvex polynomial is still permitted by the exclusions. There
is no bound on its degree or coefficients, and no new equilibrium producer.

## New content versus existing results

The robust singleton-face inequality already appears in
[the singleton-face note](../notes/CODEX_HILBERT__POLYNOMIAL_DRIFT_SINGLETON_FACE_TEST.md).
The packet's explicit moving source adjustment improves the regularity needed
for that step: differentiability at the common limiting point suffices,
without passing a continuous gradient across nearby faces. For polynomial
certificates this does not enlarge the applicable function class.

The full-relation additive exclusion in
[the separability note](../notes/CODEX_RADO_BOUNDARY__NONCONVEX_SEPARABLE_POLYNOMIAL_DRIFT_EXCLUSION.md)
already applies to arbitrary signed tables without a matrix hypothesis.
The packet's face-only separability lemma has a different, weaker functional
input, but does not improve that existing full-relation conclusion.

The quasiconvex extension goes beyond
[the convex-potential exclusion](../notes/CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY.md).
The mixed-curvature account and scalar-transform exclusion, with explicit
component regularity, provide further structural restrictions. Their role is
to remove certificate ansatzes, not to eliminate the corresponding game.

## Independently cross-checked strengthening

For a polynomial or smooth full-relation certificate, the quasiconvex
exclusion needs no standard-Q assumption. Both reviewers checked the following
combination of the packet's argument and the existing global-minimum lemma.

Minimize the potential on the intermediate full box of radius reward bound
plus one. Finite root Nash existence and the universal drift inequality force
every minimizing root to be all Continue. The singleton-face derivative
inequality then puts every minimizing point strictly above every own-singleton
level. Thus the potential's minimum on the upper-singleton box is strictly
below its minimum on that box's lower boundary.

The packet's lower-boundary argument gives the contradiction without any LCP
step: a lower-boundary minimizer cannot lie on exactly one lower face; at an
intersection its nonzero gradient has the inward coordinate signs. If the
potential were quasiconvex on the upper-singleton box, those signs would make
that boundary point a minimum on the whole box.

For this strengthening, continuity on the intermediate full box and
differentiability around the upper-singleton box must be stated. Polynomials
automatically satisfy them. The purely analytic face-only theorem remains a
separate standard-Q statement. Its matrix hypothesis cannot simply be removed
from the quantitative convexification proof: adding a quadratic need not
preserve the full edge inequality.

## Specification and attribution repairs

1. In the LCP interpolation, restrict the parameter to strictly between zero
   and one. The claimed convex-combination box bound is not valid for every
   positive parameter, and the limit argument needs only this interval.
2. State the analytic theorem as differentiability on a neighborhood of the
   box and quasiconvexity on the box itself. That is what the proof uses and
   what the applications supply.
3. In the scalar-transform result, require the outer function and the
   individual summands to be continuously differentiable. Regularity of the
   composite alone does not justify the chain rule used in the proof.
4. Credit the preceding face, convex, and additive exclusions. Separate the
   strengthened full-relation consequence from the standalone analytic
   theorem instead of claiming the matrix assumption disappeared everywhere.

The exclusions and the strengthened full-relation corollary leave arbitrary
coupled nonquasiconvex polynomials unexcluded. They impose necessary
certificate conditions, not sufficient conditions for a certificate and not
a reward-table equilibrium theorem.
