# Independent review: guarded row-swap degree escape

## Verdict and scope

**PASS as an ordinary mathematical raw-table equilibrium producer. No unresolved
mathematical objection was found in the general guarded theorem, strict raw
class, weak-inverse corollary, fixture, or neighborhood claim.**

Reviewed in full: `gpt/GUARDED_ROW_SWAP_DEGREE_ESCAPE.md`, SHA-256
`31aa635fbd7ee00b50397ba7b77a1346c4e58cd8ead9605f3f09a2fa10614e33`.

This review reconstructs the proof rather than inferring it from the companion
checker. It does not treat the crossed-response theorem as an established input.
The comparison with that theorem uses only its stated finite raw conditions.
The general raw conclusion is actual exact stationary terminal Nash, with
unrestricted behavioral deviations and a same-profile uniform payoff in the
strict class. The weak-inverse boundary supplies one fixed uniform payoff but
does not assert an attained limiting stationary equilibrium.

## 1. The guarded row swap is strategically valid

The residual Delta_i is independent of q_i. Therefore the swapped a-coordinate
uses Delta_b(q_a,z), not a residual whose tested boundary variable has changed
meaning. For z nonzero, G0 excludes q_a=0 and G1 excludes q_a=1; the same
reasoning applies to b. Both selected coordinates are interior. Their swapped
fixed-point equations force Delta_a=Delta_b=0, so both ORIGINAL owners are
indifferent. Every remaining coordinate obeys its own original endpoint sign.

The separate z=0 exclusion is essential and correct. For u=q_a>0,

    Delta_b(u,0)/u
      =(1-u)(s_b-r_b({a}))+u(r_b({a,b})-r_b({a})).

The first endpoint is strictly negative by Gamma_ba>0; the second is
strictly negative by G1 at z=0. The bracket is affine in u and stays negative
on [0,1]. No positive a-coordinate can then be fixed by the swapped map.
Repeating for b leaves only zero. Thus every nonzero fixed point has two
interior guarded hazards and at least one positive outsider hazard.

No utility permutation, player identification, or joint block deviation is
used. The row permutation is solely part of a mathematical fixed-point map.

The warning example also checks: if the only nonzero terminal entry is
r_0({0,1})=2, the profile q=(0,1,0,0) has residual (2,0,0,0). Row-swapped
clipping fixes it while player 0 can join profitably. Determinant arithmetic
without a strategic guard is insufficient.

## 2. Global and local degrees

The expanded box (-1,2)^n correctly includes every strategy face. The clipped
map has image in [0,1]^n, so its homotopy to an interior constant has no
boundary fixed point and the displacement degree is +1.

Near zero the upper clip is inactive, while the lower clip remains active.
The exact coordinate identity is

    q-max(0,q+P Delta(q))=min(q,-P Delta(q)).

Together with Delta(q)=-Gamma q+O(||q||^2), this gives the full ambient
min-map with matrix A=P Gamma, with no transposition and no extra orientation
sign. R0 makes min(x,Ax) nonzero on the unit sphere. Compactness and positive
homogeneity give a uniform linear lower bound. The minimum operation is
one-Lipschitz in its second argument, so the quadratic remainder is smaller
than that bound on a sufficiently small sphere. The displayed straight
homotopy is boundary-zero free, and zero is isolated with local degree kappa(A).

Excision and additivity then give total nonzero-root degree 1-kappa(A).
No individual nonzero root need be isolated, regular, or counted. Nonzero
degree supplies a root; Section 2.1 of the manuscript, not the degree itself,
supplies original-game incentive validity.

The degree convention and the listed elementary degree properties match
Section 2 of [Gowda's primary paper](https://userpages.umbc.edu/~gowda/papers/trGOW93-01.pdf):
its LCP equation is the coordinatewise min-map, its regular index has the
stated determinant orientation, and its R0 degree is independent of the
right-hand side. The manuscript supplies the boundedness and small-remainder
arguments needed for this application.

## 3. The finite raw guards and strict-inverse class

For each guarded owner, the absent-partner inequalities give

    Q_i>=ell_i,  H_i<=(1-alpha_i)h_i,
    Delta_i>=(1-alpha_i)(ell_i-h_i)>0

whenever at least one outsider hazard is positive. The last strict inequality
does not require a uniform lower bound as z tends to zero. With the partner
sure, alpha_i=0 and Delta_i is an average of the literal joining differences.
The strictly negative comparisons U therefore give G1, including all
outsider-hazard faces.

In Fin4, four possible owner-plus-outsider rows compared with three nonempty
outsider rows give twelve L inequalities per owner; U gives four more.
The advertised total of thirty-two is correct.

The reciprocal positive singleton comparisons are produced from the raw
premises. L makes every external singleton comparison negative. If the paired
comparison were also nonpositive, the entire row of Gamma would be nonpositive,
contradicting its product with the nonnegative corresponding inverse column
being one.

For any invertible A with A^{-1}>0, a nonzero homogeneous complementary
solution has nonzero w>=0 and x=A^{-1}w>0, which forces w=0 by
complementarity. Thus A is R0. At right-hand side -1, every solution satisfies
x=A^{-1}(1+w)>0, whence w=0 and x=A^{-1}1 is the unique root. The local map
there is Ax-1 and its index is sign(det A). Right-hand-side independence
then gives kappa(A). Row-swapping yields A^{-1}=Gamma^{-1}P>0 and reverses
the determinant, so the strict class has kappa(Gamma)=+1 and kappa(A)=-1.
All these arguments allow signed own singleton levels.

## 4. Complete behavioral and finite-horizon conclusions

At least three original hazards are positive. In particular every queried
player has opponent survival alpha_i<1, including the guarded players and
inactive outsiders. Its pure-date response formula is a convex combination
of Q_i and H_i/(1-alpha_i); Never gives the second value. Every unrestricted
behavioral replacement averages these pure-clock responses. The fixed-point
and endpoint inequalities therefore give B_i<=v_i, while prescribed play
attains v_i. There is no missing negative sole-owner Never case.

For any complete response, absorption occurs by the first opponent quit time.
Its geometric mean bounds the timing error uniformly over that response.
This proves the claimed same-profile all-large-horizons estimate and fixed
target. No uniform contraction constant over all possible selected roots is
claimed or needed.

Independent censoring after N rows preserves outcomes unless all opponents
survive N rows. Coupling therefore gives the 2M alpha_i^N cap error, while
renewal gives U_i(p^N)=(1-C^N)v_i. Since C<=alpha_i<=rho<1, the constants
3M rho^N and M rho^N follow. The finite-profile horizon estimate correctly
handles negative singleton rewards by replacing the late response with Never
in the one-sided cap comparison. It includes response dates beyond the retained
support and is not merely a finite-menu guarantee.

For rational tables, the nonempty polynomial endpoint system with two guarded
coordinates mixed and each of two outsiders zero/mixed/one is a finite
real-algebraic selection problem. The nine status possibilities and allowance
for algebraic hazards are correct. This is an existence/decision procedure,
not a bit-complexity claim.

The exact tracked consumers are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
Their exact hypotheses were read: joint absorption, the actual fixed point,
individual endpoint Nash, and every opponent-deleted contraction. The
manuscript produces every one of these fields. The source path is tracked.

## 5. Weak-inverse approximation

The inverse-positivity lemma is correct for n>=3. For B>=0 invertible,
if B_ij=(BKB)_ij=0, every product B_iu B_vj with u!=v vanishes.
Nonempty row-i and column-j supports must therefore be one common singleton
{k}. Some B_uv with u,v!=k is positive: otherwise the n-1>=2 rows outside
k would all lie in the one-dimensional column-k subspace. The corresponding
term of BKBKB is positive. Hence the convergent nonnegative Neumann series
makes every entry of (Gamma-eK)^{-1} positive.

The perturbation leaves the diagonal zero and is implemented by literal
off-own-singleton reward changes. Determinant sign and the finitely many
strict raw guards persist for sufficiently small e. No terminal-only
translation or strategic equivalence is assumed.

Every nearby strict game supplies its own actual stationary equilibrium.
At the original table these same laws have regret at most 2e. A subsequence
of their ORIGINAL prescribed payoff vectors supplies a fixed target.
For each chosen approximant, opponent-deleted contraction still holds;
the horizon may depend on that approximant. This proves the original
uniform payoff without cap continuity or a limiting equilibrium strategy.

## 6. Exact fixture and class separation

The matrix, inverse, guard margins, and displayed rational root check.
For example, when outsiders 2 and 3 are sure,

    Delta_0=2-3q_1,       Delta_1=5-7q_0.

The selected q_0=5/7,q_1=2/3 therefore makes both guarded residuals zero.
Direct endpoint sums for player 2 give Q_2=-29/21,H_2=-30/21;
for player 3 they give Q_3=2/7,H_3=-5/21. These give the two stated
positive residuals and verify the full payoff/cap vector independently
of the checker.

The four all-half residuals are distinct. Every block-constant subspace
contains that common-hazard point, so every nonsingleton response-invariant
block is excluded at once. The fixture has only the discrete partition,
whose full matrix degree is +1. This is a genuine additional class beyond
the quotient-degree sufficient test, not a claim that all quotient classes
are contained in the guarded class.

The child LP rows used in the Farkas calculations have the exact meanings

    F_A(i)=s_i-r_i(A),        b_F=s_k-r_k(A),
    J_A(i)=r_i(A union {i})-r_i(A),
    b_J=r_k(A union {k})-r_k(A).

These match the capped-clock criterion. The displayed positive row
combinations give negative dual coefficient vectors and strictly positive
dual right sides, proving infeasibility even without the Never row.
For example, the k=0 combination sums to (-12,-12,-12) with right side 12,
and the k=1 combination sums to (-1,-1,-1) with right side 5.
The other two displayed exact certificates also check.

Every principal triple of the paired matrix has a negative inverse entry.
Reciprocal entries have the same nonzero sign, excluding an escort edge under
`IsQuittingSingletonEscortEdge` and hence a balanced singleton cycle under
`BalancedSingletonCycleCertificate.exists_escortCycle`, both in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`.
These declarations and their tracked source were checked.

Equal stationary hazards tending to zero have limiting surplus
Gamma*1/4=1/4 in every coordinate. Therefore a sufficiently small actual
stationary profile is strictly above all singletons, defeating each stated
payoff-exclusion criterion. This is not a claim that every known
collision-dependent stationary producer fails.

### Additional exact separation from the crossed half-ceiling test

This comparison uses only the explicit raw hypotheses in the crossed
manuscript, not its theorem or proof.

For pair {0,1}, the above two residual formulas evaluated at the half ceiling
and sure outsiders give +1/2 and +3/2. Thus even the weak half-ceiling sign
fails. Nonpositive Bernstein coefficients would imply a nonpositive value
everywhere, so that coefficient test fails as well.

Only the positive reciprocal pairs {0,1} and {2,3} can pass its lower
ranking: any cross pair leaves a +3 singleton comparison outside the pair.
For {2,3}, lower ranking fails because r_2({0,1})=4>s_2=1
(and also r_3({0,1})=2>s_3=1). Thus NO relabeled pair passes the crossed
raw criterion at this fixture.

This separation persists on the manuscript's full radius-1/1000
neighborhood. The +1/2 half-ceiling witness changes by at most 2delta;
the lower-ranking failures have margin three and change by at most
2delta. Consequently the additional class is open in the full reward
space, not just a single exceptional table outside the compared tests.

## 7. Neighborhood and counterexample restriction

The inverse perturbation argument uses the correct maximum row-sum norm:
each off-diagonal Gamma entry moves by at most 2delta, giving 6delta
per row, while the center inverse has norm one. The displayed Neumann
bound retains positive inverse entries and determinant sign. The strict
raw margins lose at most 2delta.

At the all-half point alpha_i=1/8, so a residual moves by at most
7delta/4, and a difference of two residuals by at most 7delta/2.
The minimum old separation is 3/16. The four LP certificate coefficient
sums give the stated error bounds, smaller than all strict signs.
Singleton row sums remain positive, retaining the payoff-exclusion
counterexample. The full-dimensional neighborhood claims are sound.

Section 8's extra necessary condition uses the separately supplied ordinary
mathematical theorem that a Fin4 no-UE table has full Gamma R0 and degree +1.
It is not being attributed to a checked Lean integer-degree declaration.
Standard Q gives a positive entry in each guarded row; the external entries
are negative, so the positive entry must be the paired one.

For A=P Gamma, a nonzero homogeneous solution with nonzero outside part
would force x_a,x_b>0, hence w_a=w_b=0. Swapping those zero slack entries
does nothing, making the same x a homogeneous complementary solution for
Gamma, contradiction. With zero outside part, the positive diagonal paired
terms already force zero. Thus A is R0. Theorem 1 then forces kappa(A)=+1
under no UE. This is an additional necessary family of matrix conditions,
not an exhaustive counterexample dispatch.

The tracked source
`isR0Matrix_quittingSingletonMatrix_of_normal_of_no_uniformPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/PunishmentNormalR0.lean`
has exactly the stated normality and no-UE hypotheses; it alone is not the
integer-degree conclusion.

## 8. Checks, assembly requirements, and immediate generalization

The complete 173-line checker was inspected before execution. It imports
SymPy, performs finite exact algebra, and prints results; it contains no
network, external command, or file-write operation. It was run with
`python -B gpt/CHECK_GUARDED_ROW_SWAP.py`; every finite assertion passed.
Those checks corroborate the fixture and certificates, not the general
degree or behavioral proof. No Lean file, original manuscript, export,
or commit was changed.

For a standalone export, include the above definitions of F and J rather
than depending on the unnamed child packet, remove temporary checker and
snapshot history, and identify any prior integer-degree result by a
self-contained proof or suitable stable source. These are packaging
requirements, not gaps in the mathematical implication checked here.

An immediate common-ceiling version is valid: clip the guarded coordinates
to [0,h] for any fixed 0<h<=1, require their upper residual guards at
partner hazard h, and retain the same lower guards and reciprocal signs.
The z=0 bracket is affine and negative at 0 and h; the local min-map and
global degree are unchanged. Every nonzero fixed point is interior below h
and therefore satisfies the original individual endpoint conditions.
This includes the full-ceiling and half-ceiling constructions without
identifying their distinct finite raw tests.

The remaining general question is not production within this class:
the proof produces the root from every admitted table. What remains is
coverage of tables failing the raw guards or the swapped degree condition.
Failure does not supply another pair or an automatic strategic continuation.
# Additional qualitative strengthening: sixteen weak tests

The strict interior degree theorem remains valid, but its qualitative
full-ceiling UE consequence admits fewer assumptions. This distinction
prevents attributing all qualitative force of a full-ceiling guard to the
matrix or degree calculation.

For signed Fin4, select distinct players a,b and write J for the other two.
Assume only

    max_{∅≠T⊂J} r_a(T) ≤ min_{T⊂J} r_a(T∪{a}),
    r_b(T∪{a,b}) ≤ r_b(T∪{a})  for every T⊂J.

There are twelve weak lower comparisons for a and four weak leaving
comparisons for b. No determinant, inverse, reciprocal singleton sign,
other selected row guard, or strictness assumption is needed for qualitative
uniform equilibrium.

Fix q_a=1 and q_b=0. In the ordinary finite game among J, each pure action
profile T gives outsider j payoff r_j({a}∪T). Take a mixed Nash equilibrium
of that finite game. Its independent action probabilities give outsider
hazards z with their original stationary endpoint signs: a quits surely,
so every outsider's opponent survival is zero. The weak leaving test gives
Δ_b≤0, and the lower test gives Δ_a≥0 whenever z≠0. If z≠0 all deleted
opponent clocks contract, and this actual stationary profile is an exact
full behavioral equilibrium and is uniform at its terminal payoff.

If z=0, outsider finite Nash plus the leaving test give
r_k({a,k})≤r_k({a}) for every k≠a. These are exactly the no-join inequalities
for an instant solo exit. If s_a≥0, the stationary profile itself works.
For arbitrary signed s_a, argue under absence of a uniform payoff in the
ORIGINAL game. The tracked declaration
`finFour_punishment_le_singleton_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`
then gives punishment_a≤s_a. The tracked declaration
`isUniformEquilibriumPayoff_soloReward_of_instantPunishment` in
`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean` consumes that
inequality and all no-join inequalities, producing the fixed singleton
target r({a}) and contradicting absence of UE. Both declarations were read
directly and verified to be git-tracked.

This branch prescribes a sure owner at the first date and an off-path
punishment of that owner after unexpected continuation. It need not be an
exact stationary equilibrium. There is no supplied punishment hypothesis
in the final Fin4 theorem: original no-UE produces the needed normality.
Only qualitative existence is strengthened; the manuscript's produced
interior root with at least three active players remains a distinct result
and retains its stated degree assumptions.
