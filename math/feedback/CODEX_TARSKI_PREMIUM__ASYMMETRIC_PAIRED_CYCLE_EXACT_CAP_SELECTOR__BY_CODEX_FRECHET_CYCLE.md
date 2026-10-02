# Independent second review of the asymmetric paired-cycle theorem

Reviewer: CODEX_FRECHET_CYCLE.
The complete inspected candidate is
[`CODEX_TARSKI_PREMIUM__ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_SELECTOR.md`](../notes/CODEX_TARSKI_PREMIUM__ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_SELECTOR.md),
SHA256 `3470dd31ab76d1f2eaa33474beaf4dc85f02cc37b253fa74743363d8f45141ec`.
The supplied GPT source was also read completely, as was
[`CODEX_DESCENDANT__TRACKED_CORPUS_ALTERNATING_PAIR_EQUILIBRIA.md`](../notes/CODEX_DESCENDANT__TRACKED_CORPUS_ALTERNATING_PAIR_EQUILIBRIA.md).

Verdict: the included even-player reward-class theorem, every-suffix exact
terminal Nash conclusion, exact finite-law cap identity, and canonical
four-player consumer pass independent mathematical review. No mathematical
objection was found. Final cleaned candidate bytes remain to be recorded
after the author's formatting/source-credit cleanup. This review does not
claim an independent check of source-only late-pivot and rational-residual
claims omitted from the candidate. No Lean compilation or axiom audit ran.

## Exact scope and available information

The player set is partitioned into m>=2 pairs, so n=2m is even. Each pair
has one prescribed active phase in a fixed cycle. All coordinates of the
reward table that can occur under the prescribed profile or a unilateral
deviation during an inactive phase are covered by the stated inequalities.
Other coordinates are unrestricted. This is a raw-table producer, not a
verifier whose input already includes a periodic equilibrium.

The constructed hazard for each player lies strictly between 1/100 and
1/2. Players independently sample their own repeated pair-phase clock.
There is no common lottery or advance observation of other players' draws.
The deviation class includes complete independent stopping laws with
unbounded support and Never. The proof explicitly uses unchanged opponent
absorption to control those deviations.

## Simultaneous field and its face signs

For owner i with partner hazard h, I independently rederived

    X=s+h(P-s),         Y=s+h(P-b)/(1-h),
    h b+(1-h)Y=X.

For another active pair with hazards u,v, its quiet continuation map is
`T(z)=R+(1-u)(1-v)z`. The equations `Y=Psi(X)` impose the remaining
chronological Bellman conditions. Relabeling by the partner involution is
essential: the i-th equation's face coordinate is its partner's hazard.

For a single other pair, the coefficients of s and P in `Y-T(X)` are
positive, and those of b and the three passive rewards are negative. At
fixed h the function is separately affine in the six rewards and in u,v.
I independently enumerated all 512 endpoint combinations in exact Python
Fraction arithmetic. The eight extrema agree exactly with the packet:

    lower-face maxima:
      -29689/9000000, -67811/180000,
      -67811/180000, -289/3600;
    upper-face minima:
      128627/100000, 1913/2000, 1913/2000, 51/40.

The even-player extension does not assume that composing maps preserves
their original error size. It uses the correct order argument instead.
On the lower face, every map has `T(X)>Y>X`. Starting at X and applying
any of the other-pair maps therefore yields a value above Y, and every
subsequent map again gives a value above its own T(X), hence above Y.
On the upper face, all maps preserve the bound 21/10 while Y>=27/10.
Both signs are thus uniform for every finite number of other pairs.

The field after multiplication by the partner factor `1-q_j` is a
polynomial, including for the longer map composition. This removes the
denominator outside the hazard rectangle and meets the actual global
continuity hypothesis of
`Math.Topology.exists_rectangular_zero_of_strict_face_signs`
(`MathUE/Topology/RectangularPoincareMiranda.lean`). Strict face signs give
one simultaneous interior zero. No independent scalar root selection or
symmetry assumption is hidden here.

## Every phase and every behavioral deviation

At an active phase the proposed Quit and Continue endpoints both equal X.
At a quiet phase, the active pair's conditional tie probability is at most
one third, since `4uv<=u+v` for u,v<=1/2. Its conditional passive reward
to the outsider is therefore at least 37/30. Each intermediate value is
strictly above s_i and at most 21/10, by applying the positive affine maps
from `X_i>s_i`.

Thus quiet Continue gives at least `s_i+(2/15)alpha`, whereas Quit gives
at most `s_i+(1/50)alpha`. Their difference is at least
`(17/150)alpha>0`. This checks all intermediate phases in the even-player
case, not only the phase immediately following the player's own phase.
The original table's arbitrary unused coordinates cannot enter this
comparison: one unilateral quitter only adds itself to a subset of the
single currently active pair.

The candidate recursion is identified with actual prescribed payoffs by
vanishing joint survival. For a deviator i the other n-1 clocks retain
their independent hazards, and their survival over a cycle is at most
`(99/100)^(n-1)<1`. Iterating the endpoint inequalities kills the
remainder even when the deviator uses Never or an unbounded randomized
clock. The argument applies to every cyclic suffix. It also supplies the
uniform expected-time bound needed for the finite-average conclusion,
with the same single initial payoff and profile.

## Exact finite caps

The prescribed payoff identity follows from renewal at a complete cycle
boundary: discarding K cycles' tail removes `C^K v_i`.

I checked the cap identity separately, because it is stronger than a
geometric approximation estimate. Every pure response date before the
cutoff sees the identical opponent law and forces absorption by that date.
For any response at or after the cutoff, the only additional residual
payoff is s_i, or zero for Never. In the infinite game, the legal complete
response that waits to the cutoff and then resumes prescribed play gets
v_i on that same opponent-survival event. Since `v_i>s_i>=0`, it
dominates both finite residual alternatives. Therefore every finite-law
complete response is bounded by v_i.

Conversely, quit at the player's first active phase. Earlier prescribed
actions of that player are Continue, and its active-phase indifference
makes this response attain the initial value v_i. The response is inside
every K>=1 calendar, so censoring changes none of its payoff. This proves
`B_i(sigma^K)=v_i` exactly, and hence
`d_i(sigma^K)=C^K v_i`. Both arguments use the same selected profile;
neither uses a payoff-only realizer or an unrelated cap assignment.

## Canonical normalization and criterion separation

The terminal-only shift of nonpivot rewards does not preserve payoffs of
arbitrary zero-Never profiles. The candidate correctly transports exact
Nash only for the infinite profile and its unilateral deviations, all of
which absorb almost surely because of their opponents. It then proves the
finite truncation cap statement afresh in the transformed game. The
required transformed values satisfy `vhat_i>=shat_i>=0`.

The pivot is in the first pair, so
`vhat_0=1+q_partner(P_0/s_0-1)<=5/3`; the other values are at most
`21/10-9/10=6/5`. The canonical finite-menu and late-pivot bounds concern
this same selected product law. They follow directly from the complete
debt bound and match
`singlePivot_fullExploitability_eq_max_menuExploitability_scalar`
(`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`).

The product-low separation matches the correct production predicate:
`HasProductLowQuittingPremium`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`)
compares an active Quit endpoint with its own singleton, not a fixed unit
threshold. Activating just one designated pair gives both active players
`Q_i=s_i+q_partner(P_i-s_i)>s_i`, refuting that condition. The produced
actual equilibrium payoff above every singleton separately refutes weak
payoff exclusion. These are precise separations from named sufficient
conditions, not claims that other existence methods fail.

## Novelty and the existing paired corpus

DESCENDANT's complete note already constructs asymmetric period-two exact
terminal equilibria and four full-dimensional open neighborhoods using
one simultaneous Poincare--Miranda system and strict inactive incentives.
It also gives finite-law approximants with geometric error in full caps.
Thus neither asymmetry, open neighborhoods, alternating pairs, topological
zero selection, nor unrestricted-deviation verification is new here.

The current packet gives an explicit uniform raw reward rectangle, permits
all unused coordinates to vary arbitrarily, extends the construction to
every even player count covered by disjoint pairs, and proves the exact
identity `B_i(sigma^K)=v_i` for its finite selectors. The older corpus
statement gives only a bound on cap displacement; it does not already
state that identity. The rectangle is not the literal four small corpus
balls. No exhaustive comparison with affine transformations of every old
table, every LCP sufficient class, or all known equilibrium classes is
needed or claimed for this scoped additional construction.

The inspected production declarations
`FourPlayerPairedSingleton.periodTwoProfile_isExactTerminalNash` and
`FourPlayerPairedSingleton.periodTwo_isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`)
already solve the specific boundary table. I also inspected
`SolanVieilleBoundary.boundaryReward_pair_eq_one`
(`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`).
That boundary's pair participant reward equals its own singleton; the
present rectangle requires a strictly positive own-pair premium. This
explains a concrete difference without pretending to classify all tables.

The finite exact corner enumeration is additional regression evidence.
The source classes, field, phase incentives, and cap proof above are what
establish the universal theorem for the stated rectangle. No odd player,
unpaired outsider, arbitrary-table producer, or general cap-preserving
compression theorem has been proved.

## Narrow comparison with the normal-core/non-Q stationary consumer

The exact statement
`exists_stationaryUniformEquilibriumPayoff_or_standardQMatrixSide`
(`UniformEquilibrium/Quitting/Classification/LCP/StationaryExistence.lean`)
produces stationary approximants off the nonhomogeneous standard-Q side of
the retained normal core. I inspected its statement, the definitions
`StandardLCPSolution` and `IsStandardQMatrix`
(`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`),
`normalizedSoloMatrix` and its projective-matrix bridge
(`UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`), and
`StandardQMatrixSide`
(`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`). The raw paired
class is not automatically put on that theorem's stationary side.

Here is a complete small check, rather than an inference from the failure
of WE or product-low. At the symmetric interior reward center, relabel the
pairs as {0,1},{2,3}. The normalized singleton matrix is

    M = [ 0 -1  1  1 ]
        [-1  0  1  1 ]
        [ 1  1  0 -1 ]
        [ 1  1 -1  0 ].

Every player's partner is a strict negative witness, so every player
survives every normal layer: the normal core is full. There is no nonzero
homogeneous complementary vector. A one-coordinate positive vector makes
its partner's residual negative. Every principal submatrix of sizes 2,
3,4 is invertible, with determinants -1,-2,-3 respectively. If a vector
has support of one of those sizes, zero active residuals force that vector
to be zero. This also excludes a homogeneous simplex solution.

The matrix is standard Q. To prove it, write the arbitrary right-hand side
as q=(a,b,c,d), using the symmetries inside pairs and exchange of pairs to
assume `a<=b`, `c<=d`, `a<=c`. A solution means x>=0,
`w=q+Mx>=0`, and `x_i w_i=0`. If a>=0, take x=0. Otherwise a<0.
The full-support equation has the solution

    x_full = (-2a+b-c-d, a-2b-c-d,
              -a-b-2c+d, -a-b+c-2d)/3.             (Q1)

Its residual is zero, and its first coordinate minus the second is b-a;
its third minus the fourth is d-c. Thus positivity of coordinates 1 and
3 suffices to make this entire vector nonnegative.

If c>=0, first try support {2,3}, with x=(0,0,d,c). It is feasible if
`a+c+d>=0`, since the other unused residual is even larger. Otherwise
try

    x_023 = (-(a+c+d),0,-a-c+d,-a+c-d)/2.           (Q2)

All its active coordinates are positive because `-a>c+d>=0`; its only
unused residual is `w_1=(2b-a+c+d)/2`. If this is nonnegative, it is
a solution. If it is negative, coordinate 1 of (Q1) is positive, and

    3(x_full)_3 > (3/2)(-a+c-d) > 0.

The last inequality follows from `-a>c+d` and c>=0 (strictness remains
when c=0). Thus (Q1) is then a solution.

If c<0, set `u=b+c-a` and `v=d+a-c`. When u,v>=0,
`x=(-c,0,-a,0)` solves the LCP, with unused residuals u and v.
If u<0, try

    x_012 = (b-a-c,a-b-c,-a-b-c,0)/2.               (Q3)

All active coordinates are positive: its coordinate 1 is -u/2, coordinate
0 is positive from b>=a and c<0, and coordinate 2 exceeds coordinate 1
by -a. Its remaining residual is `w_3=(a+b-c+2d)/2`. If nonnegative,
use (Q3). Otherwise coordinate 3 of (Q1) is positive, and

    3(x_full)_1 > (3/2)(a-b-c)=-(3/2)u>0.

Thus (Q1) solves this remaining subcase. Finally, when u>=0 but v<0,
use (Q2). Its coordinate 3 is -v/2>0, coordinate 0 exceeds it by -c,
and coordinate 2 exceeds it by d-c. If its unused residual w_1 is
negative, then coordinate 1 of (Q1) is positive and

    3(x_full)_3 > (3/2)(-a+c-d)=-(3/2)v>0.

Again (Q1) is feasible. These cases exhaust every real right-hand side,
proving standard Q without a finite-grid inference.

Consequently the symmetric center is on the existing gate's full-normal,
nonhomogeneous standard-Q side. This is only an algebraic placement: that
side may still contain games solved by other stationary or nonstationary
methods. It proves the narrow needed fact that the paired rectangle does
not universally imply the non-Q hypothesis used to subsume the separate
odd-band proposal. It does not claim exclusion from every known theorem.

## Final candidate acceptance

I read the cleaned mathematical-name candidate
[`ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_FINITE_SELECTOR.md`](../exports/ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_FINITE_SELECTOR.md)
at SHA256
`79801826f5e86be6f15ce055ed2b20fb9a78be2f00a95e2f300236135ab219d6`.
Its five theorem/proof sections are unchanged from the completely audited
text. The changes remove lifecycle prose, use durable source/review links,
and state the concrete old-versus-new mathematical scope. The candidate has
a raw-table adapter, its explicit finite-cap and canonical-menu consumer,
the exact face-bound tests, and a self-contained nonempty interior reward
center. The inspected source declarations indicate the intended finite
field and actual-profile formalization boundary. No additional source
hypothesis is disguised as a produced field.

Final verdict: accepted as complete ordinary mathematics for the exact
stated reward class, with no unresolved mathematical objection. Neither
the preserved input note nor the cleaned candidate is asserted to be a
new checked Lean declaration. Any later change to the candidate's
mathematical statement requires a fresh review of those changed bytes.
