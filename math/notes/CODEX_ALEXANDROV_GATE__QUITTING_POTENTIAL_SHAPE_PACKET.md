# Quasiconvex exclusion and curvature requirements for universal quitting potentials

Authors: the author of [QUITTING_POTENTIAL_EXCLUSION](../gpt/QUITTING_POTENTIAL_EXCLUSION.md),
CODEX_HADAMARD, and CODEX_ALEXANDROV; assembled by CODEX_ALEXANDROV_GATE.
Independent mathematical reviews:
[CODEX_ALEXANDROV](../feedback/QUITTING_POTENTIAL_EXCLUSION__BY_CODEX_ALEXANDROV.md),
[CODEX_HADAMARD](../feedback/QUITTING_POTENTIAL_EXCLUSION__BY_CODEX_HADAMARD.md).
Independent final packet reviews:
[CODEX_SCHUR_CLOCK](../feedback/CODEX_ALEXANDROV_GATE__QUITTING_POTENTIAL_SHAPE_PACKET__BY_CODEX_SCHUR_CLOCK.md),
[CODEX_CAUCHY](../feedback/CODEX_ALEXANDROV_GATE__QUITTING_POTENTIAL_SHAPE_PACKET__BY_CODEX_CAUCHY.md).
[The review synthesis](../feedback/QUITTING_POTENTIAL_EXCLUSION__BY_CODEX_COORDINATOR.md)
records their common scope and specification corrections.

The proofs below are ordinary mathematics. No new Lean declaration or Lean
check is claimed. The main result is the matrix-free exclusion of
quasiconvex potentials on the full exact-root relation. The matrix-only
theorem and quantitative consequences have separate hypotheses. The cited
reviews checked the component mathematics and the matrix-free strengthening.
The result strictly narrows the polynomial certificate search and does not
answer the full controller–tester question.

## Exact statement

Let I = {1,…,n}, where n ≥ 2. For each nonempty S ⊆ I give a reward
r(S) ∈ ℝⁿ, and suppose |r_j(S)| ≤ M for every S,j, where M ≥ 0. Write

    rⁱ = r({i}),       s_i = r_i({i}),       R_ji = r_j({i}) − s_j,
    L = M+1,          W = 2M+1,
    K₀ = [−L,L]ⁿ,     K = [−M−2,M+2]ⁿ,
    C = ∏_j [s_j,L],  B = {x ∈ C : x_i = s_i for some i}.

R_i denotes column i of R. Thus R_ii = 0. Every interval defining C has
length at least one. The translation x ↦ x−s is only an analytic change
of coordinates; the game's Never payoff stays zero.

For a product root q ∈ [0,1]ⁿ, define its absorption a(q), successor
F(v,q), and ordinary root regrets e_j(v,q) as in the next section.

**Theorem 1, full exact-root exclusion.** Let P:ℝⁿ→ℝ be continuous on K₀
and differentiable on an open neighborhood of C. If

    P(v) − P(F(v,q)) ≥ a(q)                              (E)

for every v ∈ K₀ and every exact Nash root q against v, then P is not
quasiconvex on C. Equivalently, for every P with those regularity
properties that is quasiconvex on C, there exist v ∈ K₀ and an exact
Nash root q with a(q)>0 such that

    P(v) − P(F(v,q)) < a(q).

No standard-Q, punishment-normality, positive-singleton, or equilibrium
nonexistence hypothesis is used. In particular the conclusion applies to
every polynomial potential on the full robust relation in K at every
positive tolerance.

**Theorem 2, the separate analytic face theorem.** Let R be a real n×n
zero-diagonal standard-Q matrix. Suppose b_j>0 and R_ji<b_j for all j,i,
and put D=∏_j[0,b_j]. There is no f differentiable on an open neighborhood
of D, quasiconvex on D, with

    ∇f(x)·(x−R_i)>0       for all x ∈ D with x_i=0.        (F)

Standard Q here means textbook LCP solvability for every real right-hand
side, not the weaker projective convention.

**Theorem 3, robust shape and curvature restrictions.** Suppose P is
differentiable near C and, for one fixed 0<τ≤1/4, satisfies

    P(v) − P(u) ≥ a(q)    for every (v,q,u) ∈ E_τ(K).     (R)

Then, for every i and x ∈ C with x_i=s_i,

    ∇P(x)·(x−rⁱ) ≥ 1+τ‖∇P(x)‖₁ ≥ c,
    ‖∇P(x)‖₁ ≥ 1/(W−τ),       c = W/(W−τ).              (1)

If there is z ∈ ℝⁿ with z≥0, ∑_i z_i=1, and Rz≥0, the restriction of P
to C cannot be additively separable, nor can it equal

    F₀(c₀+∑_j f_j(x_j))                                 (2)

with each f_j continuously differentiable near [s_j,L] and F₀ continuously
differentiable on an open interval containing the inner function's image
on C. F₀ need not be globally monotone.

Under the same z hypothesis, if P is C² on an open neighborhood of C,
let a be any minimum of P on C and define

    λ_j = ∂_jP(a) if a_j=s_j, and λ_j=0 otherwise;
    a⁽ⁱ,t⁾ = a with coordinate i replaced by t.

Then λ≥0 and the signed mixed-curvature account satisfies

    −∑_i z_i ∑_(j≠i) (a_j−r_jⁱ)
         ∫_[s_i,a_i] ∂_ij P(a⁽ⁱ,t⁾) dt
        ≥ c+λᵀRz ≥ c,                                  (3)

and consequently

    max_(x∈C, i≠j) |∂_ij P(x)| ≥ c/((n−1)W²).           (4)

If R is standard Q, put

    A = (1/4) max_i ∑_(j≠i) (max(R_ji,0))².

Then A>0, and every such C² P satisfies

    min_(x∈C) λ_min(∇²P(x)) ≤ −c/A.                      (5)

Here λ_min is the least eigenvalue of the symmetric Hessian. Since
A≤(n−1)M², this also gives the weaker bound −c/((n−1)M²) when M>0.
The matrix hypothesis in (5) is retained: convexification need not preserve
the full exact-root inequality (E).

**Theorem 4, a rational rejection witness under standard Q.** Suppose all
r_j(S) and M are rational and R is standard Q. Every rational-coefficient
polynomial P that is quasiconvex on C has rational v,u ∈ K and a rational
product root q, with only one player quitting at a rational probability
h ∈ (0,1), such that q is exact Nash against v, u=F(v,q), and

    P(v)−P(u)<3h/4,       a(q)=h.

Thus its proposed unit-charge inequality fails by more than h/4 on one
literal rational edge. No denominator bound or complete decision algorithm
is asserted. Theorem 1 supplies a real violating edge without Q; Theorem 4
is the separately proved rational one-quitter statement with Q.

## Definitions and assumptions

Each player draws Quit independently with probability q_i. The probability
of coalition S ⊆ I is

    π_q(S) = ∏_(i∈S)q_i · ∏_(i∉S)(1−q_i).

For T ⊆ I\{j}, let π_(q,−j)(T) be the corresponding product over the
opponents alone. Set

    a(q) = 1−π_q(∅),
    F(v,q) = π_q(∅)v + ∑_(S≠∅)π_q(S)r(S),
    Q_j(q) = ∑_(T⊆I\{j})π_(q,−j)(T)r_j(T∪{j}),
    C_j(v,q) = π_(q,−j)(∅)v_j
                + ∑_(∅≠T⊆I\{j})π_(q,−j)(T)r_j(T),
    e_j(v,q) = max(Q_j(q),C_j(v,q))−F_j(v,q).

Since F_j=q_jQ_j+(1−q_j)C_j, e_j≥0. Exact Nash means e_j=0 for every j.
The pure endpoints suffice because every unilateral root mixture is their
convex combination. The full robust relation consists of all triples
v,u ∈ K and q ∈ [0,1]ⁿ satisfying, for every j,

    |u_j−F_j(v,q)|≤τa(q),       e_j(v,q)≤τa(q).

Regret is evaluated against the source v, not u. All v are allowed,
including vectors with no behavioral payoff realization. There is no
punishment floor, root selector, initial-state condition, or restriction
to an orbit. Source is continuation, target is prefixed payoff, and charge
is absorption. Exact successors remain in K₀ or K whenever the source
does, by the reward bound and convexity.

A function is quasiconvex on a convex set D when

    f((1−t)x+ty)≤max(f(x),f(y))
        for all x,y ∈ D and all t ∈ [0,1].

A standard LCP solution at d ∈ ℝⁿ consists of z,w≥0 with w=d+Rz and
z_iw_i=0 for every i. R is standard Q if such a solution exists for
every d. Taking d=−1 gives Rz=w+1≥1 and z≠0. Normalization therefore
produces a simplex vector with Rz≥0 and shows that R has a positive
entry. Neither this z nor an LCP solution is a strategy.

The local probability mode throughout the new analytic proofs is ordinary
finite expectation under an independent product root. An endpoint
perturbation in E_τ(K) is an allowed annotation, not additional randomization.
No public random signal, correlated choice, conditional expectation,
stopping-time selection, or interchange of expectation and supremum is used.
Root Nash controls one root action against a fixed continuation annotation;
it is not itself a cap on an unrestricted behavioral deviation.

For the semantic corollary only, the quitting game continues at payoff zero
until its first nonempty quitting coalition and then keeps that coalition's
reward forever; Never has reward zero. Let U_i(p) be expected terminal
payoff of a full behavioral profile. A deviator may replace its entire
history-dependent behavioral strategy. Define the punishment value

    μ_i = inf_(opponent behavioral plans p_−i)
               sup_(behavioral deviations d_i) U_i(d_i,p_−i).

No attainment of either extremum or common profile realizing μ is assumed.
Punishment normality means μ_i≤s_i for every i. The sure-root alternative
means there are q,k with q_k=1 and e_j(μ,q)=0 for every j.

Write UE(r) for existence of one fixed vector y such that for each ε>0
there are a behavioral profile p and a horizon threshold T₀ such that,
for all T≥T₀, its expected average payoff is within ε of y in every
coordinate and every unilateral behavioral replacement has expected
average payoff at most the prescribed profile's expected average payoff
plus ε. The target y precedes ε; p and T₀ may
depend on ε. The source characterization uses exactly the project's
uniform-payoff predicate, with unrestricted deviations and zero Never
payoff. No discounted or stationary substitute is used here.

## Conjecture-facing change

The named open obligation is the polynomial formulation of
`QUITTING_CONTROLLER_TESTER_DUALITY`,
also recorded in `docs/TOOLKIT.md` through
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
(`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`).
For n=4, punishment normality, a positive own singleton, and a fixed bound
M, that existing theorem gives

    ¬UE(r)  ⇔  no sure root and
                 ∃ τ∈ℚ, 0<τ≤1/4, ∃ P∈ℚ[X₁,…,X₄], (R).

Theorem 1 proves the following exact refinement, with all the same
reward-table hypotheses and box:

    ¬UE(r)  ⇔  no sure root and
                 ∃ τ∈ℚ, 0<τ≤1/4, ∃ P∈ℚ[X₁,…,X₄],
                     (R) and P is not quasiconvex on C.    (6)

The forward proof takes the polynomial actually produced by the existing
characterization and applies Theorem 1. The reverse proof forgets the
shape restriction and uses that characterization. There is no new assumed
polynomial producer. In the forward direction the existing ambient-Q
bridge supplies the hypothesis of Theorem 3, so the same witness also
satisfies (2)'s exclusion and (3)–(5), with n−1=3. Adding those restrictions
to the right side of (6) preserves the equivalence by the same reasoning.

Consequently, to rule out the polynomial alternative for every table in
that class, it is sufficient to rule out only the remaining nonquasiconvex
polynomials; under the no-sure-root condition it is further sufficient to
consider only the regular nonseparable class satisfying the displayed
curvature bounds. The universal all-edge inequality remains necessary in
every case. Satisfying these shape constraints is not sufficient for (R).

This is an all-degree exclusion. Its functional scope strictly exceeds
the existing convex and additive exclusions. For example, with n≥2,

    H(x) = (∑_j(x_j−s_j)−1/2)³                          (7)

is quasiconvex on C, because the scalar cube is increasing and its argument
is affine. It is nonconvex: along x=s+t e₁ its second derivative is
6(t−1/2), negative for 0<t<1/2. It is not additive: its mixed partials
are 6(∑_j(x_j−s_j)−1/2), which are not identically zero. When s is
rational it is a rational polynomial. Thus Theorem 1 rejects functions
outside both previously excluded classes, without imposing any matrix
condition. This verifies strict enlargement of the eliminated ansatz
class; it does not prove that an arbitrary remaining polynomial exists.

The packet does not claim a complete answer to the named question, a new
table class with UE, or elimination of the full polynomial route. The
unresolved obligation is exclusion or construction of an arbitrary
coupled nonquasiconvex polynomial satisfying the original universal test.

## Strategic inputs and admission

The contribution is a proved reduction that strictly narrows a named open
obligation. Its exact content is (6)
and the independently quantified shape impossibility behind it. It does
not rely on calling quasiconvex polynomials an exhaustive strategy class.
The test (7) makes the advance over the preceding convex/additive results
literal. The curvature inequalities retain quantitative information beyond
the statement that some mixed partial or negative Hessian direction exists.
The formalization value is this missing capability on the actual polynomial
certificate interface. Admission does not require publication novelty:
earlier ordinary mathematics is credited and can still supply a useful
unimplemented theorem. The bounded Lean-source check below distinguishes
that capability from any already formalized result.

No strategic witness is assumed in the new impossibility theorems. Given
arbitrary finite reward data, exact probe roots are constructed explicitly;
the root at a minimizing annotation is produced by finite Nash existence.
Continuation annotations are allowed by the full source relation and are
not postulated actual strategies. The z in Theorem 3 is explicit analytic
input, and standard Q produces one; the existing no-UE matrix theorem
produces ambient standard Q in the four-player application. None is used
as an unproduced strategy or continuation architecture.

The predicate (R) is the object being ruled out within specified function
classes. This is an impossibility/reduction result, not a conditional
existence consumer which assumes a strategic certificate. In (6), the
original source theorem already produces a polynomial from ¬UE; the
packet makes no new arbitrary-game construction claim. Thus there is no
unproduced strategic input requiring the gate's exceptional-conditional
admission. The analytic matrix premise must still be stated wherever used.

The exact contribution is therefore a missing analytic restriction on an
existing necessary-and-sufficient polynomial interface. It neither removes
an entire game branch nor changes the complete source-to-UE boundary.

## Source correspondence

The bounded route was `docs/TOOLKIT.md`'s full robust relation and rational
polynomial characterization, followed only through the definitions and
matrix bridge used here. The following declarations and their imports
were inspected; this records source reads, not a fresh build:

- `IsQuittingFloorFreeRobustEdge`,
  `quittingRobustChargedEdgeResidual`, `quittingRobustChargedEdgeRegret`,
  and `quittingFloorFreeRobustChargedRelation`
  (`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`)
  give exactly E_τ(K), with source-based regret and arbitrary boxed endpoints.
- `ChargedRelation.IsPotential` (`MathUE/ChargedPathBudget.lean`) means
  potential(target)+charge≤potential(source), agreeing with (R).
- `quittingRootSuccessorPayoff`, `quittingRootQuitPayoff`,
  `quittingRootContinuePayoff`, and `IsεQuittingRootEndpointNash`
  (`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`), together
  with `quittingRootCoordinateNashDefect` and its nonnegativity theorem
  (`UniformEquilibrium/Quitting/Root/NashDefect.lean`), give the stated
  independent root expectations and exact Nash convention.
- `exists_isZeroQuittingRootNash`
  (`UniformEquilibrium/Quitting/Root/NashExistence.lean`) supplies an exact
  root for every real continuation vector with no sign, matrix, or
  absorption premise. It imports the finite endpoint-Nash existence bridge
  through `UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed`.
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  (`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`)
  has player type Fin 4, a bound on every terminal reward, punishment
  normality for every player, and a positive own singleton. It constructs
  a native rational polynomial and positive rational tolerance ≤1/4.
  Its imports supply the finite-capacity producer, polynomial separator,
  and converse consumer; no new smooth-potential producer is assumed.
- `quittingGame_not_exists_uniformEquilibriumPayoff_of_noSureRoot_of_rationalPotential`
  (`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateConsumer.lean`)
  is the converse consumer, retaining all those table hypotheses and
  the no-sure-root premise. Its conclusion concerns unrestricted behavior.
- `quittingPunishmentValue`, `quittingBestReplyValue`
  (`UniformEquilibrium/Quitting/Stationary/MinMax.lean`),
  `IsQuittingNormalPlayer`
  (`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`), and
  `HasQuittingPunishmentVectorNashRootWithSureQuitter`
  (`UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean`)
  identify μ, normality, and the finite sure-root alternative without
  any common punishment-vector realization claim.
- `StandardLCPSolution`, `IsStandardQMatrix`, and
  `isStandardQMatrix_reindexMatrix`
  (`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`)
  use textbook Q. `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`)
  gives `StandardQMatrixSide`, whose `normal_standardQ` field concerns
  the recursively normal core, as defined in
  `UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`.
- `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`)
  makes that core all four players under ¬UE. `fullNormalCoreEquiv` and
  `reindex_normalPlayerMatrix_fullNormalCoreEquiv`
  (`UniformEquilibrium/Quitting/Classification/LCP/FullNormalCoreHomogeneousTransfer.lean`),
  followed by standard-Q reindexing, yield ambient Q. The definition
  `normalizedNormalPlayerMatrix`
  (`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`) and
  `normalizedSoloMatrix_eq_projectiveLCPMatrix`
  (`UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`)
  identify the resulting matrix with `quittingProjectiveLCPMatrix`
  (`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean`), whose
  receiver-row, quitter-column entries are exactly R_ji. Matrix normal
  core and punishment normality are different notions; neither substitutes
  for the other's hypotheses.
- `quittingUniformEquilibriumPayoffConjecture`
  (`UniformEquilibrium/Quitting/Conjecture/Basic.lean`) is the open finite
  quitting target, a proposition definition rather than a proof.
- `StochasticGame.IsUniformEquilibriumPayoff` and
  `StochasticGame.IsεHorizonNash`
  (`UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform.lean`)
  give the fixed-target, all-large-horizons quantifiers and the cap relative
  to the prescribed finite-horizon payoff used in UE(r).

A narrow search for quasiconvexity, separability, and the displayed
curvature exclusions in the selected Projective/LCP and MathUE interval
subtrees found no corresponding theorem. This is a bounded overlap check,
not a global novelty claim.

The singleton-face inequality is prior in
[HILBERT's face test](../notes/CODEX_HILBERT__POLYNOMIAL_DRIFT_SINGLETON_FACE_TEST.md).
[FRECHET's convex exclusion](../notes/CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY.md)
already gives the full-box minimum lemma and excludes convex potentials.
[RADO's additive exclusion](../notes/CODEX_RADO_BOUNDARY__NONCONVEX_SEPARABLE_POLYNOMIAL_DRIFT_EXCLUSION.md)
already excludes all additive C¹ full-relation potentials for arbitrary
signed tables, without Q or the simplex premise. The additive lemma below
has weaker face-only input; its full-relation consequence is not a stronger
additive result. Multiple-binding boundary minima also precede this packet,
as detailed in the source review. The additions assembled here are the
quasiconvex arguments, exact adjusted probes under weaker regularity,
regular scalar-composition exclusion, and quantitative curvature accounts.
The matrix-free main theorem is the reviewed composition recorded in
[HADAMARD's scope audit](../notes/CODEX_HADAMARD__FULL_RELATION_QUASICONVEX_SCOPE_AUDIT.md)
and [ALEXANDROV's review note](../notes/CODEX_ALEXANDROV__QUITTING_POTENTIAL_EXCLUSION_REVIEW.md).

No external paper theorem or unbuilt Literature claim is a proof input.
The source convention check read `Literature/README.md`, Remark 2.9 and
Definition 2.10 in `Literature/SolanAndSolan2020.lean`, and the corresponding
original subsection “Linear Complementarity Problems and the Main Result”
in Eilon Solan and Omri N. Solan, *Quitting Games and Linear Complementarity
Problems*, from `sunspot9.tex` in the local
`literature/SOLAN_SOLAN_2020__QUITTING_GAMES_AND_LINEAR_COMPLEMENTARITY__SOURCE_ARCHIVE`.
The original source distinguishes the standard equation w=d+Rz from its
simplex formulation w=a₀d+∑a_iR_i, with the conversion requiring a₀>0.
This packet explicitly assumes standard Q and performs its own
projectivization; it does not identify the two Q predicates unconditionally,
or import a sunspot result into ordinary behavioral semantics.

## Proof

### 1. Exact and robust singleton probes

Fix i and x ∈ C with x_i=s_i. Put Δ_j=r_j({i,j})−r_jⁱ for j≠i. Give
only i a quitting probability h ∈ (0,1). For the K₀-only hypothesis (E)
define d_i=0 and

    d_j = max(Δ_j,0) if x_j<L;       d_j=0 if x_j=L,
    vʰ = x + h d/(1−h),
    uʰ = (1−h)vʰ + h rⁱ.

The upper-coordinate freeze is necessary for this particular box:
raising a coordinate already at L could leave K₀. A nonupper coordinate
has a fixed positive margin L−x_j, so vʰ stays in K₀ for sufficiently
small h. The owner is indifferent: both action payoffs equal s_i. For a
nonupper nonowner j, Continue minus Quit is

    (1−h)(vʰ_j−s_j)−hΔ_j
      = (1−h)(x_j−s_j)+h(max(Δ_j,0)−Δ_j) ≥ 0.

For an upper nonowner it is (1−h)(L−s_j)−hΔ_j, which tends to
L−s_j≥1 and hence is positive for all sufficiently small h. Finitely
many coordinates permit one common small-h interval. Thus qʰ is exact
Nash, a(qʰ)=h, and uʰ=F(vʰ,qʰ)∈K₀ by convexity.

The fixed vector d gives

    vʰ = x+hd+O(h²),
    uʰ = x+h(d+rⁱ−x).

Differentiability at x therefore yields

    lim_(h↓0) [P(vʰ)−P(uʰ)]/h = ∇P(x)·(x−rⁱ).

Under (E), this proves face drift at least one, including every
intersection of lower and upper faces. No continuous gradient is needed.

For the robust relation in the larger K, instead put d_j=max(Δ_j,0) at
every nonowner coordinate. All of C has a positive margin to the boundary
of K, so these continuations fit for small h, with the same exact Nash
calculation. For any e∈[−1,1]ⁿ the target uʰ+τhe also fits in K and has
Bellman residual at most τh; its root regret remains zero. Applying (R)
and the same expansions gives

    ∇P(x)·(x−rⁱ−τe)≥1.

Choose e_j to have the sign of ∂_jP(x). This proves the first inequality
of (1). Since ‖x−rⁱ‖∞≤W and W−τ>0,

    1+τ‖∇P(x)‖₁ ≤ W‖∇P(x)‖₁.

Rearranging gives ‖∇P(x)‖₁≥1/(W−τ), and substitution gives drift at
least 1+τ/(W−τ)=c.

### 2. A common quasiconvex boundary argument

Suppose f is differentiable near D=∏_j[0,b_j], where b_j>0, and R has
R_ii=0 and R_ji<b_j. Assume strictly positive face drift (F), without
yet assuming Q. Let B_D be the union of D's lower faces. Continuity and
compactness give a minimum x of f on B_D. Put J={i:x_i=0}, g=∇f(x).

If J={i}, coordinate variations for j≠i stay on face i. Their derivatives
are zero when 0<x_j<b_j and nonpositive when x_j=b_j. The own term of
g·(x−R_i) is zero, and each upper-coordinate factor b_j−R_ji is positive.
Consequently g·(x−R_i)≤0, a contradiction. Hence |J|≥2.

Now every permitted one-coordinate variation keeps some lower coordinate
fixed, and thus remains in B_D. Minimality gives

    g_j≥0 at x_j=0;    g_j=0 at 0<x_j<b_j;
    g_j≤0 at x_j=b_j.                                  (8)

These imply g·(v−x)≥0 for every v∈D. Face drift gives g≠0, so the
inequality is strict for every v in the strict interior of D: each
nonzero boundary derivative multiplies a displacement of the same strict
sign, and every other contribution is nonnegative.

For a differentiable quasiconvex function the implication

    f(v)≤f(x)  ⇒  ∇f(x)·(v−x)≤0                        (9)

holds even at a boundary point. Indeed, quasiconvexity bounds
f(x+t(v−x)) by f(x) for 0≤t≤1; take the right derivative at zero.
If some v∈D had f(v)<f(x), continuity would preserve that inequality
after moving v slightly toward the center of D. The resulting strict
interior point contradicts (8) and (9). Thus, if f is quasiconvex on D,
every boundary minimum chosen above is a global minimum on D.

### 3. Proof of Theorem 1 without Q

Let z be any global minimum of P on K₀, which exists by continuity.
Finite mixed Nash existence supplies an exact Nash root q against z.
Its successor remains in K₀, so minimality and (E) give

    0 ≤ a(q) ≤ P(z)−P(F(z,q)) ≤ 0.

Thus a(q)=0. For product probabilities in [0,1], this forces every
q_i=0. At all Continue, pure Quit gives s_i and Continue gives z_i;
exact Nash therefore yields z_i≥s_i. Hence z∈C.

In fact z_i>s_i for every i. If z_i=s_i, the exact probe inequality from
part 1 gives ∇P(z)·(z−rⁱ)≥1. But the segment z+t(rⁱ−z), 0≤t≤1,
lies in K₀, so minimality gives its nonnegative right derivative
∇P(z)·(rⁱ−z)≥0, a contradiction. This works at upper box faces too.
It applies to every global minimum. Compactness of B now gives

    min_C P = min_K₀ P < min_B P.                       (10)

Translate C by −s and apply part 2 with b_j=L−s_j and columns R_i.
The reward bound gives R_ji≤M−s_j=b_j−1, and part 1 supplies positive
face drift. If P were quasiconvex on C, a boundary minimum would minimize
P on C, contradicting (10). This proves Theorem 1. A violating exact
root must have positive charge, because a zero-charge root is all Continue
and F(v,q)=v.

### 4. Proof of the analytic standard-Q theorem

Under Theorem 2's hypotheses, part 2 gives a minimum x of f on all D,
with J={i:x_i=0}, |J|≥2, and gradient signs (8). Fix k∈J. For
t∈(0,1) let d_t=(1−t)x+tR_k. Solve the standard LCP at d_t, obtaining
z_t,w_t. Projectivize it by

    a₀,t = 1/(1+∑_i z_t,i),
    a_i,t = z_t,i/(1+∑_j z_t,j),
    y_t = w_t/(1+∑_i z_t,i).

Then a₀,t>0, all weights are nonnegative and sum to one, y_t≥0, and

    y_t = a₀,t d_t + ∑_i a_i,t R_i,
    a_i,t y_t,i = 0.                                   (11)

Since 0<t<1, both d_t and all R_i are coordinatewise at most b.
Equation (11) therefore places y_t in D. This box argument would not
justify taking arbitrary t>0.

Some i∉J has a_i,t>0. Otherwise, using g=∇f(x), (11) and (F) give

    g·(y_t−x)
      = a₀,t t g·(R_k−x) + ∑_(i∈J)a_i,t g·(R_i−x)<0.

The first coefficient is strictly positive, giving strictness even if all
singleton weights vanish. This contradicts (8).

Take t_m=1/(m+2). By finiteness choose a subsequence with one fixed such
i∉J; then take a further convergent subsequence of (y_t,a_t) in the
compact product of D and the weight simplex. The unprojectivized LCP
solutions need not be bounded. The limits y,a satisfy

    y = a₀x+∑_j a_jR_j,       a_jy_j=0,
    a₀+∑_j a_j=1,            y∈D, a≥0.                 (12)

At the fixed outside index, y_t,i=0 throughout, so y_i=0<x_i. Thus y≠x
even if its selected limiting weight is zero. It follows from (12) that
∑_j a_j>0. Since x is a minimum on D, (9) at y gives
∇f(y)·(y−x)≥0. Whenever a_j>0, complementarity gives y_j=0, and (F)
makes ∇f(y)·(y−R_j)>0. Taking the scalar product of (12) with ∇f(y)
therefore yields the impossible identity

    0 = a₀∇f(y)·(y−x)+∑_j a_j∇f(y)·(y−R_j)>0.

This also covers a₀=0. No continuous LCP selection or positive limiting
weight at the chosen outside index was assumed.

### 5. Face-only additive and scalar-composition exclusion

Work first on D under (F), with a simplex z satisfying Rz≥0. Suppose
f(x)=c₀+∑_j f_j(x_j), where the component functions are differentiable
near their intervals. Choose a_j minimizing f_j on [0,b_j]. Its derivative
is nonnegative at a_j=0, zero in the interior, and nonpositive at a_j=b_j.
Let λ_j=f'_j(a_j) when a_j=0, and zero otherwise. Then λ≥0.

For each i reset coordinate i of a to zero, obtaining x⁽ⁱ⁾. Separability
leaves all the other derivative coordinates unchanged. In
∇f(x⁽ⁱ⁾)·(x⁽ⁱ⁾−R_i), the own term is zero, lower-coordinate terms
equal −λ_jR_ji, interior terms vanish, and upper terms are nonpositive
because b_j−R_ji>0. Hence

    0<∇f(x⁽ⁱ⁾)·(x⁽ⁱ⁾−R_i)≤−λᵀR_i   for every i.

Weight by z_i and sum. At least one z_i is positive, so this gives
0<−λᵀRz≤0, a contradiction. Differentiability of the whole additive
function is enough if only a representation is supplied: restricting to
coordinate slices makes each summand, up to a constant, differentiable.

For a composition f=F₀(g), g=c₀+∑_j f_j, impose the explicit C¹
component hypotheses stated in Theorem 3. The gradient of f cannot vanish
on B_D by (F). The chain rule therefore makes F₀' nonzero on g(B_D).
The union B_D is path-connected, since each lower face contains the zero
vertex. Thus its continuous image g(B_D) is a compact interval, on which
continuous F₀' has one sign σ∈{−1,1}. At every lower-face point,

    ∇(σg)(x)·(x−R_i)
      = [∇f(x)·(x−R_i)]/|F₀'(g(x))|>0.

This contradicts the additive lemma for σg. Translate by s and use (1)
to obtain Theorem 3's shape claims. No sign condition on F₀' outside the
inner function's image of the lower boundary is required.

### 6. Mixed-curvature account

Let a minimize the C² P on C. One-sided coordinate derivatives give λ≥0
as stated in Theorem 3. Put x⁽ⁱ⁾=a⁽ⁱ,s_i⁾. For j≠i the fundamental
theorem of calculus gives

    ∂_jP(x⁽ⁱ⁾) = ∂_jP(a)
                   −∫_[s_i,a_i]∂_ijP(a⁽ⁱ,t⁾)dt.

In the face drift at x⁽ⁱ⁾, the own coefficient is zero and all other
payoff coefficients are a_j−r_jⁱ. The contribution from ∇P(a) is at
most −λᵀR_i by precisely the lower/interior/upper sign calculation in
part 5, with upper coefficient L−r_jⁱ≥1. Thus (1) gives

    c ≤ −λᵀR_i
          −∑_(j≠i)(a_j−r_jⁱ)
                    ∫_[s_i,a_i]∂_ijP(a⁽ⁱ,t⁾)dt.

Weighting by z_i and summing proves (3). Let H be the maximum in (4),
which exists by continuity on compact C and finiteness of the indices.
Every integral length a_i−s_i and every |a_j−r_jⁱ| is at most W.
The absolute value of the left side of (3) is therefore at most
(n−1)W²H∑_i z_i=(n−1)W²H. This proves (4). No individual sign of a
mixed partial follows from the signed aggregate inequality.

### 7. Negative curvature

Let m=min_(x∈C)λ_min(∇²P(x)), which exists by continuity, and let
δ=max(0,−m). The function

    Q(x)=P(x)+(δ/2)‖x−s‖²₂

has positive semidefinite Hessian throughout C and is convex there by
restriction to segments. It is differentiable near C; convexity outside
C is not asserted or needed. At x_i=s_i put y=x−s. Since y_j≥0,

    y_j(y_j−R_ji)≥−(max(R_ji,0))²/4.

This follows by completing the square when R_ji>0 and by nonnegativity
when R_ji≤0. Hence Q's face drift is at least c−δA. If δA<c, its
translated version would be convex, hence quasiconvex, on D with strictly
positive face drift. Theorem 2 contradicts this. Therefore δA≥c.

Standard Q at −1 gives Rz≥1 for a nonnegative z, forcing a positive
entry of R and hence A>0. Thus δ≥c/A>0, so m=−δ≤−c/A. Finally
R_ji≤2M implies A≤(n−1)M² and the stated simpler bound. Theorem 1
cannot replace Theorem 2 here: the added quadratic has only been shown
to preserve enough face drift, not (E) on all roots.

### 8. Rational finite witnesses

By the contrapositive of Theorem 2, a differentiable quasiconvex P with
standard-Q R has some x∈C and i with x_i=s_i and
∇P(x)·(x−rⁱ)≤0. For rational rewards, M, and polynomial P, this face
has dense rational points and its drift is continuous. Choose a rational
point on that same closed face with drift <1/2.

Use the larger-K probe of part 1 there. The vector d is rational, and
for rational h>0, both vʰ and uʰ are rational; the exact root probabilities
are rational too. The quotient [P(vʰ)−P(uʰ)]/h tends to a value <1/2.
Thus for all sufficiently small positive h the endpoints fit in K and
the quotient is <3/4. Choose one rational h in this interval. Its root
is exactly Nash by the explicit calculation and has absorption h. This
proves Theorem 4, with no rational LCP-solution or approximate behavioral
implementation premise.

## Boundary tests

1. **Collision repair at an intersecting face.** Take n=2,
   r¹=(0,−1), r²=(−1,0), r({1,2})=(1,1), x=(0,0), and h=1/4 with
   player 1 the owner. Then Δ₂=2, v=(0,2/3), u=(0,1/4). Player 2's
   Continue and Quit payoffs both equal 1/4; player 1 is indifferent.
   The unadjusted source x makes player 2's Continue payoff −1/4 and
   Quit payoff 1/4, so it is not Nash. The corrected probe keeps that
   collision in the exact regret calculation.
2. **Upper-coordinate freeze.** For the same table M=1, L=2. At x=(0,2),
   the unmodified positive lift leaves K₀. Freezing v₂=2 gives
   Continue-minus-Quit 2−4h>0 for 0<h<1/2. The exact successor
   u=(0,2−3h) remains in K₀, validating the K₀-only form of Theorem 1.
3. **Q cannot be discarded from the face-only theorem.** On [0,1]² let
   R₁=(0,−1), R₂=(−1,0), and f(x)=x₁+x₂. On face i the drift is
   the other coordinate plus one, hence at least one, although f is
   convex. R is not standard Q: at d=(−1,−1), d+Rz is strictly negative
   for every z≥0. Theorem 1 also needs drift on all exact roots; face
   drift alone does not supply it.
4. **Charge and full-root scope.** A constant P satisfies all zero-charge
   identity edges. It cannot satisfy any positive-charge edge. Thus an
   all-Continue-only selector would make the exclusions false. With all
   rewards zero, v=0 and a pure solo quitter give an exact self-loop of
   charge one, directly rejecting every potential, regardless of shape.
   The example uses no hypothetical counterexample game.
5. **Strict functional gain.** Polynomial (7) is coupled, quasiconvex,
   and nonconvex on C. Its derivatives and quasiconvexity were calculated
   above, so the main theorem excludes a class beyond convex or additive
   polynomials. This is a test of the claimed shape gain, not a surviving
   candidate certificate.
6. **Quantitative normalization.** If the required charge coefficient is
   κ>0 instead of one, the same proof gives c=κW/(W−τ) and scales
   (3)–(5) by κ. With κ=0, a constant function satisfies exact drift;
   strict positivity is essential. If M=0, R=0 cannot be standard Q,
   so the simplified negative-curvature formula never divides by zero
   under its actual assumptions.
7. **Player count and regularity.** The stated analytic proofs use n≥2.
   With one player an exact absorbing self-loop at its singleton rules
   out every full-root potential directly. With no players all charges
   vanish and a constant potential works. C¹ regularity of a composite
   alone does not assert differentiability of its represented components;
   the explicit component assumptions in (2) are part of the theorem.

These are exact algebraic tests. No numerical experiment, bounded-degree
search, or finite sample of LCP right-hand sides is used as proof.

## Adapter and consumer

For arbitrary finite reward data and a proposed smooth full-relation
potential, the adapter is literal restriction from E_τ(K) to exact Nash
and exact Bellman edges with source in K₀. Such edges have zero regret
and zero residual, so they meet the robust inequalities; the same root
and absorption are retained. Theorem 1 then rejects every quasiconvex
candidate. This produces a theorem about the entire candidate function
class without producing or assuming a behavioral continuation.

For a four-player table in the source characterization's normal,
positive-singleton class, the existing forward characterization produces
the polynomial under ¬UE. The Q bridge in the source inventory supplies
ambient standard Q. The output of this packet is the refined search
obligation (6) and the additional necessary curvature restrictions.
The reverse semantic implication remains exactly
`quittingGame_not_exists_uniformEquilibriumPayoff_of_noSureRoot_of_rationalPotential`
(`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateConsumer.lean`);
shape conditions add nothing to its input requirements and do not replace
its all-edge potential premise.

There is no produced equilibrium profile, uniform payoff, positive terminal
exploitability gap, repeated strategy block, or recursive return datum.
The packet changes the polynomial search space. It does not close a
source-to-UE construction chain.

## Lean handoff

The definitions already available are the full robust relation,
`ChargedRelation.IsPotential`, root successor and regret, finite exact
root existence, and standard LCP solvability. The principal new theorem
shape is: continuity on K₀, differentiability near C, and exact-root
unit drift imply failure of quasiconvexity on C. The robust-polynomial
corollary should restrict the relation and discharge polynomial regularity,
then refine the existing existential certificate theorem as in (6).
Do not add failure of quasiconvexity as an unexplained structure field.

Useful separate lemmas are the exact collision-adjusted singleton probe
with upper coordinates frozen; its derivative limit; the location of every
full-box minimum strictly above s; and the quasiconvex boundary-minimum
lemma. The standalone Q argument belongs with finite-dimensional analytic
LCP mathematics, keeping 0<t<1 explicit and permitting a₀=0 only at the
limit. The scalar-composition theorem needs explicit C¹ outer and inner
maps. Quantitative lemmas should retain the signed account (3), since the
absolute maximum estimate loses information.

Suitable finite checks are the two collision probes, the non-Q linear
face counterexample, the coupled cubic's Hessian, and the M=0/self-loop
case. External formalization should use narrow file or module checks under
the repository's trust rules and distinguish ordinary mathematics from
the declarations it actually checks. No Lean file, axiom, or export seal
is created by this packet.

## Scope and nonclaims

Theorem 1 uses all exact roots at all annotations in K₀ and explicit
continuity there. It is not about a selected orbit, a behavioral payoff
carrier, a floor-restricted relation, or a chosen root selector. Theorem 2
assumes only face drift but retains standard Q. The rational one-quitter
witness and negative-curvature estimate also retain their stated matrix
assumptions. Scalar encodings without regular components are outside (2).

No polynomial degree or coefficient bound, complete certificate-checking
algorithm, new game existence class, unrestricted strategy-class coverage,
or all-behavior counterexample is obtained. No inference follows from a
candidate's passing the necessary derivative or curvature tests. The
remaining precise mathematical question is whether any coupled
nonquasiconvex polynomial satisfying these necessary restrictions can obey
the full robust inequality for an actual normal positive-singleton
four-player table with no punishment-vector sure root.
