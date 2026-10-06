# Independent review: two crossed joint phases

Reviewer: CODEX_BROUWER.

## Claim and verdict

**PASS, ordinary mathematics.** The reviewed surface is the section
“Two crossed joint phases in the favorable-matching chamber” through EOF
of `notes/CODEX_KREIN__ALL_PLAYER_CLOCK_RESEARCH.md`, whole-note SHA256
`dbc80dcee726bfe1591a93bea422ac0ca42ac2cf62de9bfca9895d0d17d6d547`.
The earlier singleton sign-chamber consolidation is not being regated here.
I independently checked the complete raw-to-original-game strategy chain
and attempted to falsify it, without reading another review.

The actual raw inputs are arbitrary signed own singletons, positive row
scales, H>2, one common normalized participant increment Π>−1, one
common normalized passive increment K∈ℝ, the displayed singleton/pair
equalities, and exactly twelve outsider joining caps. They produce all
four independent laws, an exact period-two terminal Nash profile against
unrestricted behavioral deviations, and one fixed uniform payoff. No
strategic profile, root, favorable eigenvalue, or root selection is assumed.

I find no unresolved mathematical or strategic objection. This is not a
new Lean-check assertion, not arbitrary Fin4 coverage, and not a proof
that every exact stationary profile is impossible for the fixture.

## Selector, signed boundaries, and all action endpoints

For

    P(t)=Πt³+(H−1−K)t²+Kt−(Π+1),

the signs P(0)=−(Π+1)<0 and P(1)=H−2>0 are exact and do not depend
on the sign of K or Π. Thus a proper t∈(0,1) exists. The polynomial
is nonzero because its two endpoint values differ in sign. Selecting
the smallest interior zero is legitimate: there are finitely many zeros,
none at the endpoints. No uniqueness or continuous-root claim is needed.

The zero-cubic degeneracy Π=0 is harmless. For example H=3,K=2
reduces P to 2t−1, retaining the proper root1/2 even when the quadratic
coefficient also vanishes. The strict hypotheses H>2 and Π>−1 are
used for the two endpoint signs; no assertion is made at their excluded
boundary values.

Set q=1−t. At an active phase,

    U_i=s_i+qΠb_i,
    W_i=s_i+q(Π+1)b_i/t.

The Quit endpoint equals U_i; the Continue endpoint is
q(s_i−b_i)+tW_i=U_i. At a passive phase the Continue payoff is

    s_i+b_i[qt(H−1)+q²K+t²qΠ].

After dividing by q and multiplying by t, equality to W_i is precisely
P(t)=0. The forced Quit payoff averages the own singleton and the
three literal collision entries bounded in (20), hence is at most
s_i<W_i. This checks all sixteen pure action endpoints as well as the
eight policy coordinates, including every simultaneous outsider triple.

When Π<0, U_i<s_i. This is NOT a gap: that player is mixing at its
active phase, and both actual endpoints equal U_i; the singleton floor
is needed only to bound its Quit at the other, passive phase, where
W_i>s_i holds because Π+1>0. No refinement inserts additional dates
at which the below-singleton active value would be exposed.

### Exact adverse signed test

I independently tested the simultaneous negative-Π, positive-K arm:

    H=25/8, Π=−1/4, K=1, t=q=1/2,
    s=(−7,2,−3,−11), b=(1,2,3,5).

The cubic vanishes exactly. The values are

    U=(−57/8,7/4,−27/8,−93/8),
    W=(−25/4,7/2,−3/4,−29/4).

Use the prescribed singleton and active-pair rewards, set all twelve
outsider cap entries to s_i, and set every remaining unconstrained
entry r_i(S) to (−1)^(mask(S)+i)(37+11i), where mask(S)=∑_{j∈S}2^j.
This is one complete finite signed table. Exact rational evaluation of
all sixteen endpoint equations/inequalities passed. In particular the
four active values lie below their singleton floors, while every passive
Quit cap binds its permitted upper bound s_i. This test is outside my
separate nonnegative-premium/nonpositive-passive cone proposal and is
not being inferred from that proposal.

## Complete behavioral and uniform-horizon consumer

Joint survival is t⁴ per period. The bounded Bellman remainder tends
to zero, so the two algebraic phase vectors are the actual terminal
values. Against a deviating player, all three opponent clocks remain
independent with period survival t³<1. Iteration of the exact local
supersolution bounds therefore controls an arbitrary behavioral strategy,
including Never, with a remainder tending to zero as t^(3n).
This is opponent-deleted survival, not merely on-path joint absorption.

With M=max|r_i(S)|, the opponent stopping time has a geometric
two-date-block bound. The displayed conservative constant
1+2/(1−t³) bounds its date-plus-one expectation from either phase.
Absorption under ANY deviation is no later. The expected terminal to
N-date-average error is consequently at most
2M[1+2/(1−t³)]/N. The on-path error has the same bound; adding the
two errors bounds every finite-horizon regret. The first live zero date
is included. The profile and initial payoff are fixed before accuracy,
and one threshold works for all subsequent horizons and all deviations.

I inspected the exact declarations
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`, and the
endpoint definitions in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`.
Their inputs are the literal cyclic policy equalities, exact root Nash,
and each player's opponent-cycle contraction. All are produced by the
raw construction; there is no missing supplied strategic witness.

## Exact fixture and source coverage

The final H=53/8, Π=5, K=−1, t=4/5 fixture checks exactly. Its two
phase roots are (1/5,0,1/5,0) and (0,1/5,0,1/5), and the values
alternate (2,5/2,2,5/2) and (5/2,2,5/2,2). An active player's endpoints
are both2. A passive player's Quit value is9/25 and its Continue value
is5/2, giving the stated107/50 strict margin.

The displayed inverse of Γ_H is strictly positive and its determinant
H²(H²−4) is positive. Thus the actual negative-determinant premise of
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse` in
`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`
fails. Positive inverse does not by itself provide that exit. All
principal determinants and the negative-column R₀ test check; the
degree is +1 by `r0Degree_eq_sign_det_of_nonnegative_inverse` in
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`.

The claims about traps and pure exits are exact. Only02,13,I are
premium traps. Every member of either pair strictly prefers joining;
the full support has positive singleton aggregate premium charge
5−2−2=1. Thus the pair-free boxed tests and the mixed-trap larger-support
negative-charge test do not consume the fixture. Every grand-coalition
participant premium is negative, ruling out all nonempty protected sets
and every nonzero nonnegative global floor weight. All pure exits fail
by the explicit join/leave deviations stated in the note.

The fourteen-child claim has the correct quantifiers. If a proper child
cuts an active pair, choose a member j whose active mate is omitted.
Pure j is exact child Nash, joint Never is zero, and that mate gains6
by joining. The only remaining proper nonempty children are02 and13;
their sure joint exits are child Nash, and either outsider gains1.
Consequently no universal fixed nonnegative weighted child-debt plus
finite Never bound works for every child: each child has SOME profitable
omitted player. This does not exclude all possible quiet profiles.

The all-sure response displacements −11,−12,−13,−14 are pairwise
distinct. Since the all-sure point is block-constant for every partition,
every nondiscrete response quotient fails there. The literal definition
is `QuittingResponseInvariantOnUnitCube` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
The unique positive singleton predecessor map is two transpositions,
not a four-cycle, excluding both signed four-clock raw sign patterns.
The paired raw region's unique below-own partner restriction fails
because every row has two negative entries. The reciprocal-sign
integral-tournament test, cyclic-child tests on every deletion, and the
visible overlapping-cylinder ratio bound likewise fail as stated.

### The two-joint full-table neighborhood: intrinsic branch exclusion

I checked the actual elimination and floor identities in the accepted
`TWO_JOINT_PHASES_FULL_TABLE_NEIGHBORHOOD.md` packet. Its certified
four-phase branch has two distinct solo players a,b, proper solo rates,
V_D,a>s_a, V_B,b>s_b, and

    s_a=w r_a({b})+(1−w)V_D,a,
    V_B,b=z r_b({a})+(1−z)s_b.

Therefore Γ_ab<0<Γ_ba. These are intrinsic necessary signs of the
produced branch, not an estimate of its unspecified neighborhood radius.
Here both directed entries of every unordered pair have the same strict
sign. No relabeling can satisfy that branch. No exclusion of arbitrary
two-joint constructions is inferred.

### Crossed and one-sided stationary raw consumers

For any ordered selected pair (i,j), the lower polynomial face has an
exact negative witness. If j≠f(i), choose the favorite f(i) surely Quit
and all other opponents Continue. The displacement is −69/8. If
j=f(i), choose the harmful nonactive partner o(i) surely Quit, giving
displacement−1. The selected partner is absent in both cases. Thus even
the weak actual-polynomial lower faces fail, not only stronger reward
rankings or Bernstein sufficient conditions.

The exact inspected declarations/files are:

- `QuittingCrossedStrictLowerRanking`,
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseRawTests.lean`;
- `exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_strictRawUnit`,
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseRawProducer.lean`;
- `exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_halfStrictRaw`,
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseHalfCeilingProducer.lean`;
- `QuittingHalfWeakRawGuards`,
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakBoundaryProducer.lean`;
- `QuittingHalfWeakPolynomialGuards`,
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`;
- `exists_stationary_uniformPayoff_witnesses_of_weakHalfPolynomialGuards`,
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialProducer.lean`;
- `QuittingOneSidedWeakUnitGuards`, `QuittingOneSidedWeakUnitRawGuards`,
  `exists_uniformPayoff_of_oneSidedWeakUnitGuards`,
  `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`;
- `halfCeiling_fullRewardBall_source`, `unitCeiling_fullRewardBall_source`,
  `UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseFullRewardNeighborhood.lean`.

The last two neighborhoods internally produce precisely the excluded
guards. Positive playerwise scaling preserves the negative witnesses;
row translation cancels in these zero-discount differences.

### Proper-three stationary and literal owner-risky families

The author's proper-three-support contradiction checks independently.
For support012 with proper hazards(a,x,c), player2's Never value is0,
so indifference requires1+5a−2x−14ax=0. Hence3/8<x<1/2 and
a=(1−2x)/(14x−5). Player0 has

    Q₀=(14x−5)(a−c),
    N₀=(61/8)x(1−c)/(x+c−xc)>0.

Their equality forces c<a<1, while Q₀<(14x−5)(1−c) and
N₀≥(61/8)x(1−c); the latter is strictly larger. The Klein symmetry
of all rows of size at most three handles every deleted label. The
grand row is not used in this symmetry claim.

`PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`
produces exactly three proper active hazards and a zero fourth hazard,
so this contradiction excludes every relabeling of that branch.
The literal `sharpReward` family in
`UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyStationaryClosure.lean`
has a zero off-diagonal singleton comparison, whereas this fixture has
none. Its checked consumer does not claim a full-reward neighborhood.

## Export significance and remaining research boundary

This is an actual original-table producer with a complete unrestricted
strategic output, not a verifier for supplied clocks. The exact fixture
survives the applicable named raw families and accepted local branches
checked above. Its restricted equality-stratum scope is explicit, and
its arbitrary signed singleton, negative-Π, and positive-K arms are real.
There is no unresolved strategic witness or mathematical objection in
this reviewed theorem.

A meaningful separate enlargement is the asymmetric inverse-positive
cone construction being developed in my own notebook. It does not
currently subsume the full signed Π/K range reviewed here. Nor does this
verdict establish a universal stationary or periodic strategy grammar.
No export or new Lean certification is performed by this review.
