# Coverage review: finite singleton split

Verdict: PASS within the coverage scope stated below.

Reviewed artifact:
`math/exports/FINITE_SINGLETON_SPLIT_UNIFORM_EQUILIBRIUM.md`

Reviewed complete-file SHA256:
`16c3ad54f6d442d0440f8e3a5e29ed06bd81101b2dd054cb3dea6fa4a93519b8`

The reviewed bytes were supplied as the 760-line assembled artifact. This
review applies to those bytes, including the complete native table, and
does not automatically apply after any modification.

## Scope

I reviewed the raw statement and example as they bear on coverage, all of
Section 6, the correspondence between its exclusions and the named raw
producers, and the conclusion's claimed narrowing of the remaining class.
I independently checked the stationary and sure-root exclusion mathematics
and exact rational computations. I did not independently review the whole
finite-core production and behavioral consumer in Sections 2--4; those
need their separate mathematical reviews. No Lean check was run or is
asserted here.

## Raw example and actual enlargement

The Section 5 table has the singleton matrix specified in Section 6 when
ell=1/2. Its native joining values are zeta=(-1,-10,1), and its core data
are A=100, c=3, u=10, v=-100, p=0, q0=0. The general theorem's remaining
raw guards hold. Its count of eighteen unrestricted nonpivot joining
coordinates is consistent with seven nonsingleton coalitions containing
player 0, seven constrained row-0 entries, and three selected joining
coordinates.

The exact values C=5/4, J=7/8, a=5/14, b=5/9, B1=-1/9 and B3=5/9
check. The complete split interval at this point is (1/19,5/23), so
x=1/10 lies strictly inside it. The stated X, diffuse-prefix mass 2/7,
finite-root offers and all three strict finite-0 margins are correct.
The two consecutive solo-0 phases have the original total continuation
factor 9/14. The general sufficient split test specializes to ell>-1/6;
the singleton return conditions specialize to -1<ell<4. Consequently
the stated new interval (-1/6,2/3) is real enlargement across the old
nonnegative-return boundary, not a renaming of the former B1>0 test.

The artifact correctly separates two thresholds: its new UE construction
applies for sufficiently large K, without a proved numerical threshold;
its exclusions on the specified ell=1/2, p=0, kappa=1 ray hold for every
K>=100. In particular it does not assert that its construction proves UE
at K=100.

## Exact exclusions and reproduction

The definitions of P, Q, H and F give the necessary stationary signs,
including all mixed, quiet and sure supports. AllNever is separately
excluded using the original own singleton reward one. The lower cap
L=(-12,-8,-10,-12) is valid for every actual native continuation because
the pure-Never response has normalized original Never payoff -1 and
otherwise obtains an opponent-only terminal reward. With a sure quitter,
the G signs are necessary even for arbitrary actual continuation laws.
The argument excludes exact full Nash roots with a sure quitter; it does
not exclude arbitrary approximate nonstationary equilibria.

I checked the K-monotone relaxation, both direct stationary exclusions,
the principal-inverse linear combinations, and the origin estimates.
The relaxed row-1 inverse column is nonnegative on all remaining no-sure
supports, which justifies q<=VR rather than an unjustified equality.
The D and E table matches the exact coefficient bounds. Tensor Bernstein
conversion, positive denominator clearing, strict-sign rejection, origin
rejection and integer dyadic subdivision give a valid finite covering
certificate, including boundaries of the cubes.

The added stationary approximation argument also checks. For a fixed
table, a nonzero hazard limit of profiles with vanishing full regret
satisfies the excluded F conditions. At a zero hazard limit, divide by
the total hazard and take a simplex limit x. The prescribed native
terminal payoff tends to Gamma x and immediate Quit tends to zero,
so Gamma x>=0. When 0<x_i<1, the native payoff from Never tends to
(Gamma x)_i/(1-x_i); vanishing regret therefore forces
x_i(Gamma x)_i=0. A singleton support contradicts a negative entry
in its Gamma column. Every larger support contradicts nonsingularity
of its principal matrix. All six pair determinants, all four triple
determinants and the full determinant are nonzero. This proves the
claimed positive stationary regret floor for each fixed K, and makes
no uniform-in-K or unrestricted-profile regret-floor claim.

Two separately implemented exact rational calculations agree with the
artifact: all 80 nonzero stationary patterns are excluded in 862 nodes;
all 65 sure-root patterns are excluded in 365 nodes. The independent
standard-library checker was rerun against the final assembled table:

    python /tmp/split_coverage_independent.py --uniform-k 0 10

It returned both stated exact passes. The checker SHA256 is
`c6c33000a1ded016aae3887141daa9179ab56e8cea8a060e2ad0f38870c7829e`.
The separate symbolic/rational implementation has SHA256
`7395ddf1549c77c6c17c55a16385197536cd764e2efa3670b73063a23b5a1d3a`.
These scratch implementations were review aids. The export itself contains
the complete table, necessary systems, all origin constants and the
finite exact algorithm; it requires no external data payload.

## Complete selector comparisons

The 24-label enumeration, principal inverse arithmetic and native reward
tests in Section 6 check. Only the identity labeling satisfies the eight
singleton chamber signs; it has B1=-1/9 and Gamma10=2, defeating both
previously compared outer-return alternatives. Positive playerwise row
rescaling preserves these failures.

The strongly connected positive singleton graph and strictly positive
participant vector on123 defeat every ordered-anchor block selection
and every indicated supportwise participant-balance selection. The
full-proper H-ledger obstruction uses coalition12 and singleton1.
The filtered H/J obstruction uses the exact identity
J_02(w)=w1+w3/2 and the mandatory singleton inequalities. These are
obstructions to all eligible nonnegative weights, not a failed sampled
weight or one selected finite ledger.

Only triple023 has nonnegative inverse, and its exterior inverse row is
(-7/10,9/10,-1/5). Full inverse column2 has both signs. The reciprocal
singleton pair counts, the intersection of the two exceptional pairs,
and all three participant-increment failures check. The attached-pair
template has exactly the stated labeling (3,1,0,2). Its required premium
is negative; the alternative allowing both premiums to be arbitrary has
the explicit h,m>=0 requirement, which fails at m=Gamma21=-2. I checked
that last requirement in the raw theorem statement of
`BOTH_JOINT_PREMIUMS_ARBITRARY_UNIFORM_EQUILIBRIUM.md`, rather than
inferring it from the example alone. The mixed-trap charge is exactly 7.

For the named checked interfaces, I inspected the hypotheses/definitions
identified in Section 6: `RawPassiveRowInverseCriterion.lean`,
`NonnegativeInverseCriterion.lean`, `SupportwiseQuittingPremium.lean`
and its existence consumer, and `SignedFourCycleRewardAdapter.lean`
with its larger-eigenvalue consumer. The raw comparisons have the stated
scope. The complete stationary and sure-root certificates also exclude
all producers whose output is respectively stationary or sure-first,
regardless of their internal proof weights or selected actual punishment.

## What this removes from the frontier

Subject to the separately reviewed production and consumer proof, this
packet proves UE on an additional raw interval class with a negative
return annotation, including an explicit full reward ray beyond its
finite threshold. On that ray the two older chamber returns, all exact
stationary producers, all sure-first actual-continuation producers, and
the other named selector classes fail over their complete relevant
selection domains. Thus the example is meaningful nonredundancy
evidence for the new producer.

The artifact correctly makes no claim that arbitrary Fin4 is solved,
that every conceivable nonstationary certificate is excluded, or that
all games in a global source case are eliminated. The result does not
supply a positive full-strategy regret gap or a counterexample to UE.
No coverage correction is required for the reviewed bytes.
