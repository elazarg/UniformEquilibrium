# Independent source, scope, and quantitative review

Reviewer: CODEX_HADAMARD.

Target: [QUITTING_POTENTIAL_EXCLUSION](../gpt/QUITTING_POTENTIAL_EXCLUSION.md),
read in full. This review audits the source bridge, prior results,
Theorem 4/Corollary 5, and bounds (4), (11), (12), and (13). The core
standard-Q/quasiconvex proof has a separate
[independent review by CODEX_ALEXANDROV](QUITTING_POTENTIAL_EXCLUSION__BY_CODEX_ALEXANDROV.md).

Verdict: the source orientation and displayed constants check out under
the intended regularity assumptions. Corollary 5 needs explicit regularity
of its outer and inner functions. The packet's additive full-relation
conclusion is already implied by a stronger existing ordinary theorem.
A Q-free qualitative quasiconvex consequence for full-relation smooth
certificates is recorded separately below. No Lean build was run.

## 1. Exact source and quantifier audit

The inspected source commit matches the packet's source pin:
`5aac30ad2553dadd5895dc79fbc4f1f5680d7570`.

`IsQuittingFloorFreeRobustEdge` in
`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean` quantifies
over every player and simultaneously bounds the absolute Bellman residual
and ordinary coordinate Nash defect by tolerance times absorption. Both
endpoints are arbitrary boxed payoff annotations. The root is a product
root stored on the edge. No floor, source-realization, support, or selected
root condition appears. In particular regret is calculated against the
source continuation, not against the displayed target.

`quittingFloorFreeRobustChargedRelation` in that file has this continuation
as source, the prefixed payoff as target, and absorption as charge.
`ChargedRelation.IsPotential` in `MathUE/ChargedPathBudget.lean` means
potential(target)+charge <= potential(source). The packet's orientation
and its use of arbitrary target perturbations agree exactly with this API.
`quittingRootCoordinateNashDefect` in
`UniformEquilibrium/Quitting/Root/NashDefect.lean` confirms that the defect
is max(Quit payoff, Continue payoff) minus prescribed payoff.

The exact certificate theorem is
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in
`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.
Its player type is specifically `Fin 4`. It assumes a reward bound,
`IsQuittingNormalPlayer reward player` for EVERY player, and at least one
positive own-singleton reward. Its conclusion is an equivalence with both
the no-sure-root condition and one rational polynomial on ALL robust edges,
at an existential rational tolerance in (0,1/4], in the box of radius
rewardBound+2. The forward proof constructs the polynomial from a finite
outer capacity; a supplied polynomial producer is not an extra premise.
The arbitrary-n analytic theorems in the packet must remain distinct from
this four-player semantic characterization.

The exact ambient standard-Q bridge is slightly longer than the packet's
source list makes explicit:

1. `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
   `UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`
   supplies `StandardQMatrixSide reward`. Its `normal_standardQ` field
   is Q only for `normalizedNormalPlayerMatrix reward`; see
   `StandardQMatrixSide` in
   `UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`.
2. `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
   in
   `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`
   supplies equality of the recursively normal core with all players.
3. `fullNormalCoreEquiv` and
   `reindex_normalPlayerMatrix_fullNormalCoreEquiv` in
   `UniformEquilibrium/Quitting/Classification/LCP/FullNormalCoreHomogeneousTransfer.lean`,
   together with `isStandardQMatrix_reindexMatrix` in
   `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`,
   transport this standard-Q property to the ambient matrix.
4. `normalizedSoloMatrix_eq_projectiveLCPMatrix` in
   `UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`
   identifies that ambient matrix with receiver-row, sole-quitter-column
   entries r_j({i})-s_j, exactly the packet's R.

`exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform` in
`UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean`
explicitly uses the first two source facts, but transfers the no-homogeneous
property there. Its conclusion is not itself the ambient-Q theorem. The
reindexing declarations above make the claimed Q consequence precise.

The recursive matrix normal core and the punishment-normal predicate in
the polynomial theorem are different definitions; their shared word
"normal" is not an adapter. The packet appropriately keeps the polynomial
characterization under its stated normality and positive-singleton premises.
`IsQuittingNormalPlayer` was inspected in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`: it is
the inequality punishment value <= own-singleton payoff.

These are existing Lean declarations inspected under their imports, not
newly checked results of this review. The packet's analytic results remain
ordinary mathematics. No external paper theorem or unbuilt Literature
claim is required. `Literature/README.md` was inspected to retain that
distinction. Matrix coordinate translation does not translate the game's
Never payoff; the packet states this correctly.

## 2. Overlap and genuine differences within the bounded comparison

[HILBERT's singleton-face test](../notes/CODEX_HILBERT__POLYNOMIAL_DRIFT_SINGLETON_FACE_TEST.md)
already records the full robust differential inequality, including the
tolerance times gradient 1-norm. The packet supplies a useful alternate
proof: raising the nonowner continuation by h/(1-h) times its positive
collision premium gives exact Nash directly at multiply binding faces.
Its cancellation between both endpoints is valid and needs differentiability
at the limiting point, whereas HILBERT passes a continuous gradient to a
face limit. Thus the displayed face constraint is prior; the construction
and weaker differentiability requirement are distinguishable additions.

[FRECHET's convex exclusion](../notes/CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY.md)
already excludes every C1 convex full-relation potential for arbitrary
finite reward data without Q. Its Section 3 also proves that every
full-box global minimum of a differentiable potential lies strictly above
every singleton. This uses
`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`, not an assumption
that Nash existence supplies positive absorption.

[RADO's nonconvex separable exclusion](../notes/CODEX_RADO_BOUNDARY__NONCONVEX_SEPARABLE_POLYNOMIAL_DRIFT_EXCLUSION.md)
already excludes ALL additively separable C1 potentials on the full exact
root relation, for arbitrary signed rewards and any nonempty finite player
set. It needs neither Q nor a simplex z with Rz>=0. Its summands may be
arbitrarily nonconvex. Consequently Theorem 4 does not establish a new or
stronger additive exclusion for the full quitting relation.

Theorem 4 remains a different useful analytic lemma: it assumes only
strict face drift and a simplex z with Rz>=0, and does not need global
root-game Nash existence or inequalities at all other annotations. Its
coordinate-minimum proof is sound, including upper-boundary terms and
zero weights z_i. For a differentiable additively separable f on a product
neighborhood, the component derivatives used here follow by fixing all
other coordinates and restricting f to coordinate slices.

[TARSKI's reviewed common-gradient argument](../notes/CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR.md),
[NOETHER's coupled-boundary comparison](../notes/CODEX_NOETHER_SUPPORT__COUPLED_BOUNDARY_MINIMUM_SELECTS_STRICT_BAD_PRINCIPAL.md),
and
[NOETHER's same-potential face-minimum note](../notes/CODEX_NOETHER_SUPPORT__SAME_POTENTIAL_FACE_MINIMA_AND_UNPAID_TRANSITIONS.md)
already retain the multiple-binding minimum and full constrained gradient
signs. They explicitly do not manufacture a charged transition between
equal-level face minima. The packet's quasiconvex/global-minimum step and
standard-Q projective argument go beyond that local common-gradient step;
the latter is not itself a novelty claim here.

The scalar-transform analytic extension and the explicit mixed-Hessian
and negative-curvature constants were not found in this narrow same-potential
comparison. This is a bounded overlap finding, not a global priority audit.
None is a new reward-table class or a new unrestricted strategy producer.

## 3. Corollary 5 needs explicit component regularity

As written, "a C1 function of the form F(c0+sum_j f_j(x_j))" asserts C1
regularity of the composite. That alone does not justify differentiating
F and all f_j separately. Amend the statement to assume each f_j is C1
near [0,b_j] and F is C1 on an open interval containing the image of
g(x)=c0+sum_j f_j(x_j) on D. Equivalently it is enough to state suitable
differentiability and continuity hypotheses for this chain-rule argument.

With that repair, the proof is valid. The lower boundary B is path-connected
for n>=2, since each lower face contains the zero vertex. The image g(B)
is a compact interval. Nonzero gradient of F composed with g on B forces
F' to be nonzero throughout g(B). Continuity gives one sign sigma there.
Then sigma*g is additively separable and, at EVERY lower-face point,

    gradient(sigma*g) dot (x-R_i)
       = [gradient f dot (x-R_i)] / |F'(g(x))| > 0.

This contradicts Theorem 4. F need not be globally monotone outside that
interval. No positive lower bound on |F'| is needed for strict face drift.
The extension is a regular representation theorem; unrestricted scalar
encodings with no component regularity are not covered by this proof.

## 4. Quantitative audit

On C, each |x_j-r_j({i})| is at most W=2M+1. Since W>=1 and
0<tau<=1/4, W-tau>0. Writing g=gradient P(x), (3) implies

    1+tau*||g||_1 <= g dot (x-r({i})) <= W*||g||_1.

Thus ||g||_1 >= 1/(W-tau), and the drift is at least
c=1+tau/(W-tau)=W/(W-tau). Bound (4) is correct. The bound has the
right normalization for unit absorption charge; it must scale with a
changed drift coefficient.

For (11), let a minimize P on C. The base-gradient contribution at the
point obtained by resetting coordinate i to s_i is at most -lambda^T R_i.
The i-term is exactly zero, lower-boundary derivatives form lambda>=0,
interior derivatives vanish, and upper derivatives multiply strictly
positive M+1-r_j({i}). The fundamental theorem of calculus in coordinate i
then gives the displayed mixed-Hessian correction with exactly its minus
sign. Multiply each face inequality by z_i and sum. If T denotes the
left side of (11), the proof actually gives

    T >= c + lambda^T Rz >= c.

No sign of an individual mixed partial is inferred. Each integration
length a_i-s_i and payoff factor |a_j-r_j({i})| is at most W. Since
sum_i z_i=1 and at most n-1 terms remain for each i,

    c <= T <= |T| <= (n-1) W^2 * max_(C,i!=j) |partial_ij P|.

This verifies (12), including the Fin4 denominator 3W^2. C2 regularity
near compact C makes the displayed maximum available. The single matrix
premise used is the stated simplex z with Rz>=0.

For (13), C2 regularity similarly makes the minimum Hessian eigenvalue
attained. With delta as defined, P+(delta/2)||x-s||_2^2 is convex on C.
For y_j>=0,

    y_j(y_j-R_ji) >= -(max(R_ji,0))^2/4.

The extra face drift is consequently at least -delta*A. If delta*A<c,
the convexified function has strictly positive face drift, contradicting
the packet's analytic standard-Q theorem. Hence delta>=c/A and the
minimum Hessian eigenvalue is at most -c/A. Q at right-hand side -1
supplies a nonnegative vector with Rz>=1, so R has a positive entry and
A>0. Finally R_ji<=2M gives A<=(n-1)M^2. The simplified bound is valid
when M>0, as stated; M=0 cannot satisfy standard Q in these data.

For clarity, state Theorem 2 as "differentiable on a neighborhood of D and
quasiconvex on D." Its argument only uses quasiconvexity on D, whereas the
phrase "quasiconvex on a neighborhood" is stronger than the convexification
step has supplied. This is a statement-level repair, not a defect in the
box-based proof or the constants.

The rational exact-edge witness also checks out: rational rewards and
rational face coordinates make the adjusted continuations rational for
rational h. Polynomial derivative continuity allows a rational face point
with drift <1/2, and the exact quotient limit then gives a positive rational
h with drift drop <3h/4. It is a witness for rejecting the supplied
quasiconvex polynomial, not a behavioral equilibrium construction.

## 5. Stronger qualitative full-relation consequence and scope boundary

For smooth full-relation certificates, the qualitative quasiconvex exclusion
can drop Q entirely. A complete derivation is in
[FULL_RELATION_QUASICONVEX_SCOPE_AUDIT](../notes/CODEX_HADAMARD__FULL_RELATION_QUASICONVEX_SCOPE_AUDIT.md).
Its inputs are P continuous on K'=[-M-1,M+1]^n, differentiable near C,
and unit drift on every exact Nash/Bellman edge with source in K'.
Every polynomial in the packet satisfies these regularity conditions.

The already known global-minimum lemma places every K' minimum strictly
above s. The packet's multiple-binding boundary minimum and quasiconvex
strict-interior argument would force a lower-boundary point to minimize
P on all C, contradicting that global-minimum lemma. This composition uses
global exact-root quantifiers and finite Nash existence; it is not a
strengthening of the standalone face-only standard-Q theorem.

In particular it cannot be substituted into the negative-curvature proof:
the convexifying quadratic has the required face drift when delta*A<c,
but need not have drift on all exact root edges. The matrix hypothesis
therefore remains part of the audited quantitative result.

The packet therefore restricts the SHAPE of a negative certificate. A
polynomial violating these restrictions is rejected even if it was merely
proposed for an already solved table. The source theorem gives no reason
an arbitrary no-UE table must admit a quasiconvex or separable certificate;
all coupled nonquasiconvex certificates with sufficiently large curvature
remain unexcluded. The universal full-edge checker is not replaced by
the necessary differential inequalities, and no selected-face certificate
has been made complete for unrestricted behavioral deviations.

The necessary statement clarifications are Corollary 5's component
regularity and Theorem 2's box quasiconvexity. The stronger RADO overlap
and the distinction between the Q-free full-relation consequence and the
face-only theorem determine the scope of the additional conclusions.
