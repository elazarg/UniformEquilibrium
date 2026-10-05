# A zero-premium joint phase with a positive outsider buffer

## Raw class and conclusion

Let I={0,1,2,3}. At each live date the four players independently
choose Continue or Quit, with arbitrary behavioral strategies and
complete unilateral behavioral deviations. First nonempty quitting
coalition S absorbs at the finite reward r(S), received thereafter.
Live stages and perpetual continuation pay zero; no correlation device
or extra information is available. Let R be ANY real number and σ≥0.
Prescribe only these five rows:

    r(0)=(1,−1,−1,−1),
    r(1)=(2,0,2,−1),
    r(2)=(2,−1,0,2),
    r(3)=(R,2,−1,0),
    r(03)=(1,σ,−1,0).                              (1)

Require the six actual collision caps

    r₁(01), r₁(13), r₁(013) ≤ 1/2,
    r₂(02), r₂(23), r₂(023) ≤ 0.                   (2)

Every other coordinate of every nonsingleton reward is arbitrary.
In particular the two premiums at 12 and all four grand-coalition
coordinates are unrestricted. Both participants of 03 have exactly
zero premium. Its outsider σ is permitted throughout the nonnegative
halfline, while all three undiffused joins of player 1 may be positive.

**Theorem.** Every such original table has one fixed uniform-equilibrium
payoff. On the constructive interval the proof produces one target
and finite independent stopping-law profiles with arbitrarily small
terminal regret and target error against complete behavioral deviations.
The uniform finite-horizon conclusion follows directly from the
uncensored profiles below. Neither hazards nor continuation values
are supplied as hypotheses.

## The two original-table exits

For a real matrix Γ, a complementarity root at offset b is u≥0
with b+Γu≥0 and u_i(b+Γu)_i=0 for each i. The matrix is R₀
when its zero-offset problem has only the zero root. The degree
facts used below are specified by their exact declarations at the end.

The singleton-difference matrix is

    Γ=[[0,1,1,R−1],[-1,0,-1,2],
       [-1,2,0,-1],[-1,-1,2,0]].                  (3)

Its child123 matrix A has determinant 7 and inverse

    A⁻¹=[[2,4,1],[1,2,4],[4,1,2]]/7,
    A*1=1.

For R≠−1, Γ is R₀. A positive pivot p in a homogeneous
complementarity root forces all child coordinates positive, by the
cyclic negative edges and the positive right-hand side p*1. They
then equal p*1, and the pivot residual is p(R+1), impossible.
For example, if the first child coordinate vanished with positive
right-hand side p, its first inequality would force the third
coordinate positive. That active equation forces the second positive;
the second active equation would then read minus the third coordinate
equals p, a contradiction. Cycling the coordinates treats either
other zero. At zero pivot, each positive child coordinate forces
the next one positive through a negative edge inequality. Full support
would require A times that vector to vanish, so invertibility excludes it.
The same argument applies to any positive scalar right-hand side.

For R<−1 put d=−(R+1)>0. At offset (q₀,−1,−1,−1), q₀>d,
every child coordinate is positive and the child vector is (1+p)*1.
The pivot residual is q₀−d(1+p). Exactly two complementarity roots
remain: p=0 and p=q₀/d−1. The first has active determinant 7
and strict inactive residual q₀−d; the second has determinant
7(R+1)<0. The regular root-sum degree is zero, so the original
game satisfies the existing degree-not-one UE criterion. At R=−1,
(1,1,1,1) is a nonzero homogeneous root; the existing Fin4 no-UE
implication to R₀ supplies UE by contraposition.

For R≥1/4 the actual passive inverse row is

    (1,1,R−1)A⁻¹=(4R−1,R+5,2R+3)/7≥0.

Together with A⁻¹>0, the original-table passive-inverse criterion
gives UE, including equality. Thus only −1<R<1/4 remains. These
exits use no simultaneous-reward restriction and do not change the
table or invoke openness of UE.

## One scalar crossing produces all four rates

Fix −1<R<1/4 and put

    τ=1−4R ∈ (0,5),    δ=1−R=(τ+3)/4.

Use odds Y>0 as the scalar parameter, and define

    X=τY/(5+3Y),
    x=X/(1+X),             y=Y/(1+Y),
    z=(X+Y+XY)/2,
    a₁=(−X+2Y+σXY)/[(1+X)(1+Y)],
    w=a₁/(1+a₁).                                  (4)

The joint hazards will be x,y for players 0,3; z,w are solo hazards
for players 1,2. The numerator defining a₁ is

    Y[10−τ+(6+στ)Y]/(5+3Y)>0.

Thus a₁>0 and 0<w<1 for every finite Y>0. The odds X are
positive and finite, so 0<x,y<1. The function z increases strictly
from zero to infinity. Let Y_* be its unique z=1 point. For clarity,

    2(5+3Y)(z−1)=(τ+3)Y²+(τ−1)Y−10.             (5)

At Y=1/δ=4/(τ+3), the right side equals −6. Therefore
Y_*>1/δ. Throughout (0,Y_*), all four hazards are proper.

Define the scalar pivot residual

    F(Y)=δY−z−w+zw.

Near zero, X/Y→τ/5, z/Y→(5+τ)/10, and
w/Y→(10−τ)/5. Consequently

    lim[Y→0] F(Y)/Y = 7(τ−5)/20 < 0.              (6)

At the other endpoint,

    F(Y_*)=δY_*−1>0.                             (7)

Continuity supplies a root Y∈(0,Y_*). Fix any such root and its
four rates. No uniqueness or global continuation of roots is assumed.
At this root, δY=z+w−zw. The choice of X in (4) also gives

    X=2δY−3z=−z+2w(1−z).                         (8)

These are exactly the two owner equations needed below. In
particular the second expression in (8) is strictly positive,
not an extra sign hypothesis supplied to the selector.

## Literal three-phase values and exact undiffused comparisons

Repeat the three aggregate phases

    A: joint 0,3 at hazards x,y;
    B: solo 1 at hazard z;
    C: solo 2 at hazard w.

Define

    V_A=(1,a₁,0,0),
    V_B=(1+z+w−zw,0,2z,X),
    V_C=(1+w,0,0,2w).                             (9)

All three vectors are coordinatewise at least s=(1,0,0,0).
Every prescribed Continue and policy equation is exact:

* At A, player 0's Quit value is 1 and its Continue value is
  yR+(1−y)(1+δY)=1. Player 3's Quit value is zero and its
  Continue value is −x+(1−x)X=0.
* Player 1's A Continue contribution is precisely the three-term
  expectation defining a₁; its next B coordinate is zero. At C,
  −w+(1−w)a₁=0, so its B owner Continue value is also zero.
* At A, player 2's Continue value is
  −(x+y−xy)+2z(1−x)(1−y)=0 by (4). Its B value is 2z,
  and its C owner Continue value is the next A value zero.
* The remaining player-0 equations give 1+w at C and
  1+z+w−zw at B. Player 3's C value is 2w and its B
  value is −z+2w(1−z)=X by (8).

Both solo owners have their singleton Quit value zero. Together
these identities check all twelve Continue equations and supported
Quit indifferences, hence all twelve policy equations.

Let m=x+y−xy be the joint phase's nonempty absorption probability.
The actual positive buffer for player 1 satisfies

    a₁/m=[10−τ+(6+στ)Y]/[5+τ+(3+τ)Y] > 1/2.      (10)

Indeed, subtracting half the denominator from the numerator gives
3(5−τ)/2+[9/2−τ/2+στ]Y>0. By (2), its forced-Quit value
at A is at most m/2, including the simultaneous coalition 03 in
the opponents' law. Player 2's forced-Quit value at A is at most
zero, equal to its value. The two joint participants are already
indifferent. Thus A satisfies every undiffused Quit comparison.
This uses an aggregate continuation buffer, not pointwise domination
of each collision payoff by its corresponding passive reward.

## Finite laws, full behavioral regret, and one uniform target

Replace B and C by n solo dates with hazards

    β_n=1−(1−z)^(1/n),   γ_n=1−(1−w)^(1/n).

Their aggregate survival and terminal singleton laws are unchanged.
The target remains exactly V_A, independent of n. Inside a solo
block, the value is the convex interpolation between its two macro
endpoint values; all singleton floors in (9) persist, and Continue
remains exact. The owner remains indifferent. Set

    L=max(0,r_i(ij)−s_i : j∈{1,2}, i≠j),
    ε_n=L max(β_n,γ_n) → 0.

Each outsider's immediate Quit is at most its current value plus
ε_n. The retained joint row needs no error. Adding the SAME ε_n
to the whole value path gives a global Bellman supersolution:
Continue transports only opponent-survival times that constant,
whereas Quit has no future value. It is not summed over dates.

For players 0,1,2,3, opponent survival over a complete refined
period is respectively

    ρ₀=(1−y)(1−z)(1−w),
    ρ₁=(1−x)(1−y)(1−w),
    ρ₂=(1−x)(1−y)(1−z),
    ρ₃=(1−x)(1−z)(1−w).

Each is strictly below one, independently of n. Fixed opponent coins
can be presampled for this estimate without being shown to the
deviator. Their first Quit bounds actual absorption under every
behavioral replacement. Geometric survival therefore removes the
bounded Bellman remainder and proves terminal regret at most ε_n
against every complete deviation, with prescribed payoff exactly V_A.

If M bounds absolute rewards, every phase value is bounded by M:
the exact policy equations and geometric survival identify it with
the actual terminal expectation. A period has 1+2n dates. For every
replacement the expected absorption date is at most

    K_n=(1+2n) max_i 1/(1−ρ_i).

The discrepancy between N-horizon and terminal expected payoff is
at most 2MK_n/N uniformly over replacements. Thus N-horizon regret
is at most ε_n+4MK_n/N, and delivery error is at most 2MK_n/N.
Choose n and then one horizon threshold. The same profile works
at every larger horizon, with the same target V_A.

For explicitly finite independent stopping laws, censor each player's
law after K periods by moving its remaining mass to Never. The sum
of changed marginal masses is

    t_K=(1−x)^K+(1−z)^K+(1−w)^K+(1−y)^K → 0.

Product coupling changes prescribed payoff by at most 2Mt_K. Against
a fixed complete deviation, couple only the opponents' changed laws;
then compare prescribed payoff as well. Full terminal regret is at
most ε_n+4Mt_K, uniformly over every deviation. This is an actual
finite-law family, not a bounded-deviation test or a changing target.

## A signed opposite-pair member beyond the named raw criteria

Set R=0,σ=2 and complete (1) by the following full table:

| S | r(S) |
|---|---|
| 0 | (1,−1,−1,−1) |
| 1 | (2,0,2,−1) |
| 2 | (2,−1,0,2) |
| 3 | (0,2,−1,0) |
| 01 | (1,0,−1,−1) |
| 02 | (1,−1,0,−1) |
| 03 | (1,2,−1,0) |
| 12 | (2,1/2,1/2,1) |
| 13 | (0,0,1,0) |
| 23 | (2,1,0,0) |
| 012 | (1,0,0,−1) |
| 013 | (1,0,−1,0) |
| 023 | (1,−1,0,0) |
| 123 | (0,0,0,0) |
| 0123 | (−1,−2,−2,−2) |

The only positive participant premiums are the two halves at 12.
Thus the sole premium trap and greatest core are 12. Its join gaps
are d₁=3/2 and d₂=−3/2, so the signed same-sign criterion does
not apply. Every player has a negative premium at the grand row,
so the canonical protected set is empty. Trap12 fails the all-member
positive-weight aggregate-leave test, since player 1 strictly joins.
Boxed-charge hypotheses exclude pair traps, and product-low fails
at the sure12 product law. These failures concern the actual raw
tests, not all imaginable consequences of those theorems.

For this exact table, τ=1 and the scalar equation reduces to

    28Y³+60Y²+Y−35=0.

Its unique positive root lies between 3/5 and 7/10: the polynomial
is strictly increasing on the nonnegative axis and has opposite signs
at those rational endpoints. With X=Y/(5+3Y), the explicit rates are

    x=Y/(5+4Y), y=Y/(1+Y),
    z=Y(2Y+3)/(3Y+5),
    w=Y(8Y+9)/(12Y²+18Y+5).

These exact algebraic numbers give the producer above, not a numerical
root claim. In (10) this table even has a₁/m≥3/2; the theorem only
uses the uniform all-R bound 1/2.

The singleton matrix is (3) at R=0. At offset (1,−1,−1,−1),
the child complementarity coordinates equal (1+p)1, and the pivot
residual is 2+p. Hence the only root is (0,1,1,1), with strict
inactive residual 2 and positive active determinant 7. The matrix
is R₀ by the argument above and has degree one, so the degree-not-one
criterion does not apply. Only child123 has a nonnegative inverse;
its passive row is (−1/7,5/7,3/7). Inverses for child012 and child013
have first diagonal entries −2 and −2/3 respectively. For child023
the first-row second entry is −2/3. The full inverse has entry −5/7
at row0,column2. These are exact failures of the named raw inverse
screens, not a claim that the full singleton matrix is non-Q.

A literal response quotient requires equal singleton block-row sums
for two receivers in the same block. Of the fifteen partitions, the
following thirteen already fail this necessary condition. Each row
gives two receivers in one block, a column block, and its unequal sums:

| Partition | Receivers | Column block | Sums |
|---|---|---|---|
| 01 / 2 / 3 | 0,1 | 01 | 1,−1 |
| 02 / 1 / 3 | 0,2 | 02 | 1,−1 |
| 03 / 1 / 2 | 0,3 | 1 | 1,−1 |
| 0 / 12 / 3 | 1,2 | 12 | −1,2 |
| 0 / 13 / 2 | 1,3 | 13 | 2,−1 |
| 0 / 1 / 23 | 2,3 | 1 | 2,−1 |
| 012 / 3 | 0,1 | 012 | 2,−2 |
| 013 / 2 | 0,1 | 013 | 0,1 |
| 023 / 1 | 0,2 | 023 | 0,−2 |
| 01 / 23 | 0,1 | 01 | 1,−1 |
| 02 / 13 | 0,2 | 02 | 1,−1 |
| 03 / 12 | 0,3 | 12 | 2,1 |
| 0123 | 0,1 | 0123 | 1,0 |

The remaining nondiscrete partition is 0|123. It fails at
q=(0,t,t,t): its three response coordinates are

    −t+t²(1−t)(2−t)/2,
    −t+t²(1−t)(2−t)/2,
    −t.

They are unequal for 0<t<1. This uses the literal zero-discount
response (opponent absorption)*Q minus passive absorbing reward.
The specified cyclic-child joint03 raw classes also do not consume this
table: its joint participant premiums are zero, its passive player-1
entry is 2 rather than the prescribed −1, and its three player-1
collision entries are zero rather than at most −1. The positive-own-
singleton pivot is uniquely player 0, and it has no positive
participant premium at any pair. No unrestricted chronology exclusion
is being inferred from these input failures.

For every proper child except 123, exact child Nash profiles can be
chosen as follows. A listed singleton owner quits at date zero;
otherwise both members of 03 quit surely. All remaining child players
use Never. The entries are (quitting coalition, omitted beneficiary):

    0:(0,1), 1:(1,3), 2:(2,1), 3:(3,0),
    01:(1,3), 02:(2,1), 03:(03,2), 12:(1,3),
    13:(3,0), 23:(2,1), 012:(1,3), 013:(03,2),
    023:(2,1).

The omitted gain is 3/2 when singleton2 is used and 1 otherwise.
Each other child player weakly prefers not to join. A sole owner
cannot improve beyond its nonnegative singleton after preventing
absorption, because all opponents then stay at Never. At sure03,
each owner strictly prefers the pair to withdrawing, and player 1
in child013 receives 2 rather than the joining reward zero. Thus all
child debts and joint-Never probabilities are exactly zero.

For child123, use the half-hazard solo cycle 3,1,2. Its phase values
are (1,0,0),(0,1,0),(0,0,1) in child coordinates. Refine every
solo phase into n hazards α_n=1−2^(−1/n). Continue remains exact,
and the largest positive participant premium is 1/2, so the common
supersolution error is at most α_n/2. Joint Never is zero. Quiet
player 0 receives 6/7, while immediate Quit at the first microdate
receives exactly 1, since both its singleton and actual03 reward
are 1. The gain is the fixed 1/7. Consequently every proper child
has an omitted player for whom no universal fixed nonnegative
weighted-child-debt-plus-Never bound can hold.

## Exact exclusion of every stationary profile with a quiet player

This is a boundary test for the fixture, not a premise of the producer.
For a stationary product hazard q with positive absorption, let w be
its terminal payoff. Every active player has w_i=Q_i≥C_i(w,q);
if its hazard is strictly between zero and one, equality holds.

If q₀=0 and all three child hazards are positive, active player 1
has Q₁=q₂(1−q₃)/2 and passive absorbing reward −q₂+2q₃.
Its Nash inequality implies q₃≤3q₂/4. Active player 2 has
Q₂=q₁(1−q₃)/2 and passive reward 2q₁−q₃, implying
q₃≥3q₁/2. Player 3 has Q₃=0 and passive reward −q₁+2q₂,
so its inequality implies q₁≥2q₂. These inequalities contradict
positivity. If only a child pair is active, respectively the positive
passive singleton of player 2 in pair12, player 1 in pair13, or
player 3 in pair23 makes that player's Continue strictly exceed its
Quit payoff. A singleton is defeated by a profitable join. Therefore
q₀=0 is impossible for a stationary equilibrium.

If q₃=0 and q₀>0, then Q₀=w₀=1. Every nonempty opponent
coalition in 12 pays player 0 exactly 2, so any positive q₁ or q₂
would make Continue exceed 1. Only player 0 could remain active,
but player 1 profits by joining. Thus q₃=0 is also impossible.

Suppose q₁=0, with q₀>0 as already established. If q₂>0, its
Quit value is zero and every nonempty opponent coalition in 03
pays it −1. Its Continue is strictly worse, so q₂=1. But player
0 then receives 2 by Continue, above its Quit value 1. Therefore
q₂=0. With only 0,3 active, each strictly prefers Quit to Continue,
forcing both hazards to one. The resulting pure03 is defeated by
player 2's join, from −1 to zero.

Finally suppose q₂=0. The established cases leave q₀,q₁,q₃>0.
Player 3 has Quit value zero and strictly negative passive reward
against nonempty coalitions in 01, so q₃=1. Player 0 then has
Continue value zero and Quit value 1, forcing q₀=1. But player 1
receives passive value 2 at 03, above its Quit value zero, so it
cannot be active. This is a contradiction. All Never fails by
player 0's positive singleton. Every stationary equilibrium, if any,
must therefore have all four hazards positive. This covers sure
hazards as well as interior ones and permits no inference of full
stationary nonexistence. In particular no proper pure coalition is an
equilibrium. The grand coalition is also not an equilibrium: player 0
withdraws from payoff −1 to the passive reward zero at 123.

## Tracked mathematical inputs and Lean handoff

The original-table exits use these named declarations under their imports:

- `exists_finset_r0Degree_eq_sum_sign_det` in
  `MathUE/LinearProgramming/R0DegreeSum.lean` identifies the degree
  with the signed sum at a regular finite-root offset.
- `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
  `UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
  supplies UE for an original game whose R₀ singleton matrix has
  degree different from one.
- `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`
  says no UE forces R₀ and degree one, giving the non-R₀ equality exit.
- `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
  in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`
  uses exactly the child inverse and the actual outside inverse weights.

The constructive semantic inputs have the shape of
`QuittingInfinitePathQuitErrorCertificate`,
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`,
and `isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
The bounded values, exact Continue, single common Quit error,
playerwise vanishing opponent survival and fixed target are all
produced explicitly above. The direct horizon argument independently
states the uniform quantifier contract.

The universal quiet-debt bound compared here is
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
The response-partition necessary condition is
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
The exact zero-discount response is the literal stationary displacement
defined in `UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`.

The raw predicate to formalize consists only of (1)–(2), with
R real and σ≥0. Its constructive producer proves the odds reduction,
the two scalar endpoint signs, existence of a proper root, the
values (9), and the positive buffer (10). Solo subdivision then
supplies the exact-Continue common-error consumer at the same target;
the singleton source exits complete the R axis. No equilibrium,
favorable hazard, continuation annotation or controller is an input.

This theorem is ordinary mathematics, not a claim of a new Lean-checked
declaration or of completeness for all quitting games. It does not
cover arbitrary opposite-sign pair cores. The fixture is an actual
global temporal equilibrium construction despite that residual local
root geometry; it is not a counterexample to uniform existence.
