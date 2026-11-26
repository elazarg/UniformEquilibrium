# Low passive pair rewards produce alternating friendly-pair equilibria

This is an ordinary mathematical raw-table producer, not a Lean-checked
result or a full Fin4 closure. All strategic quantities below are produced
from raw rewards.

## 1. Raw class and exact conclusion

There are four players I={0,1,2,3}. The first nonempty quitting coalition
S absorbs at a finite real vector r(S). Live play and perpetual Continue
pay zero. Private randomizations are independent. A unilateral deviation
may replace the player's ENTIRE behavioral strategy, equivalently its
complete private stopping law on Nat plus literal Never.

Partition I into A={0,1} and B={2,3}; write m(i) for the other member of
i's pair, and O(i) for the opposite pair. Relabelings are permitted.
Choose finite real parameters

    a>2b>0, Pi<a, c=Pi-a<0,
    K<(7/2)Pi-4a+2b.                                  (1.1)

For each i choose an arbitrary own level s_i in R and a positive scale
lambda_i. Write Z_i(S)=(r_i(S)-s_i)/lambda_i for NONEMPTY S only.
This notation does not change the original game's live or Never payoff.
Require the following literal raw comparisons:

    Z_i({i})=0,
    Z_i({m(i)})=a,
    Z_i({j})=-b                    for j in O(i),
    Z_i({i,m(i)})=Pi,
    Z_i(O(i))=K.                                       (1.2)

For O(i)={j,k}, require just the two inactive-response bounds

    Z_i({i,j})+Z_i({i,k})<=2c,
    Z_i({i,j,k})<=2c.                                  (1.3)

The individual cross-pair participant rewards in the first bound can
have either sign; a positive coordinate may be offset by the other
negative coordinate. No individual above-own join is excluded.

All other reward coordinates are arbitrary finite numbers. Among the
44 nonsingleton coordinates, eight scheduled-pair coordinates are fixed
by (1.2), eight cross-pair participant coordinates enter the four sum
bounds, and four joining-triple coordinates enter the remaining bounds.
The 24 unmentioned coordinates are eight passive cross-pair entries,
twelve other triple entries, and four grand-coalition entries.

**Theorem.** Every original table satisfying (1.1)--(1.3) has an exact
proper period-two terminal Nash profile against ALL unilateral behavioral
replacements. All four hazards are the same number q in (0,1/2), produced
below from a,b,Pi,K. Players in A act at one phase and players in B at the
other; inactive players Continue. Every deleted-opponent family absorbs
geometrically. The actual initial-phase payoff is one fixed original-game
uniform-equilibrium target. The SAME profile supplies every positive
accuracy at all sufficiently large finite horizons.

Both scheduled pairs have strictly negative participant joining increments
c. This is a different raw region from pair producers that require those
increments to be nonnegative. The conclusion permits negative intermediate
native phase values and does not use a nonnegative singleton-word invariant.

## 2. A scalar crossing produces the hazard

For x in [1/2,1] define the continuous function

    F(x)=c/x+2bx-K(1-x)-Pi*x^2.                         (2.1)

At the two endpoints,

    F(1)=2b-a<0,
    F(1/2)=(7/4)Pi-2a+b-K/2>0.                        (2.2)

The intermediate value theorem supplies x in (1/2,1) with F(x)=0.
Choose one such x ONCE from the table and put q=1-x. Then
0<q<1/2. No uniqueness or selected-branch regularity is assumed.
The equation is exactly

    c q/x=-2bqx+Kq^2+x^2 Pi q.                         (2.3)

The simultaneous opposite-pair event Kq^2 remains in this equation.
It is not replaced by a singleton approximation. No strategic root,
continuation value, or hazard is an input to (2.1)--(2.2).

## 3. Exact values and all sixteen pure endpoints

Let V_i be the proposed value when i's own pair is active and W_i when
the opposite pair is active:

    V_i=s_i+lambda_i Pi q,
    W_i=s_i+lambda_i c q/x.                            (3.1)

At its active phase, i's Quit endpoint is V_i: the other active player
is m(i), and its two possible coalition outcomes pay own s_i or
s_i+lambda_i Pi. The Continue endpoint is also V_i, since

    q(s_i+lambda_i a)+x W_i
       =s_i+lambda_i(a+c)q=V_i.                       (3.2)

At i's inactive phase the prescribed Continue endpoint is

    2qx(s_i-lambda_i b)+q^2(s_i+lambda_i K)+x^2 V_i
       =s_i+lambda_i[-2bqx+Kq^2+x^2 Pi q]=W_i,        (3.3)

using (2.3). An immediate inactive Quit has the exact endpoint

    x^2 s_i+qx[r_i({i,j})+r_i({i,k})]+q^2 r_i({i,j,k}).

By (1.3) this is at most

    s_i+2lambda_i c qx+2lambda_i c q^2
       =s_i+2lambda_i c q
       <s_i+lambda_i c q/x=W_i.                       (3.4)

The strict inequality uses c<0 and 1/2<x<1. Its sign is essential:
2c<c/x. This covers all simultaneous-join responses. Every active owner
mixes between two maximizing endpoints, and every inactive owner strictly
prefers Continue. These are the entire sixteen phase/player/action
endpoints, not merely active indifference equations.

## 4. Actual infinite laws, full behavioral caps, and one uniform target

At even dates the two A owners independently Quit with probability q;
at odd dates the two B owners do so. All other actions are Continue.
Each owner uses an independent sequence of private coins. This is an
actual behavioral profile and hence actual independent complete clocks.

Joint survival per phase is x^2 and per full period is x^4<1. Iterating
the policy recursion in Section 3 leaves a bounded residual multiplied
by x^(4n), which tends to zero. Thus the proposed phase vectors are
the ACTUAL terminal prescribed values, not free annotations.

Deleting any one owner leaves opponent survival x^3 per full period.
This probability is independent of that owner's replacement law. For
any finite pure deadline, iterate the exact Continue recursion until
that deadline, where the Quit inequality in Section 3 caps the payoff.
For literal Never, iterate Continue forever: the bounded continuation
remainder tends to zero at rate x^(3n). Hence Never obtains exactly the
appropriate phase value, and every finite deadline obtains at most that
value. A complete replacement law averages these pure responses.
The profile is therefore exact terminal Nash against every behavioral
replacement, including arbitrary randomized delay and Never.

This also justifies the row offsets s_i and positive scales lambda_i in
the ORIGINAL game. Under every unilateral replacement the fixed opponents
absorb surely, so the same recipient offset is received on every response
and prescribed outcome. We have not asserted affine invariance at positive
joint Never.

Let R bound all absolute ORIGINAL absorbing rewards. Under every unilateral
replacement, the first opponent quit occurs by the end of a geometric
number of two-date periods. Thus its expected date plus one is at most
2/(1-x^3). The first absorption of the deviating profile is no later.
With the repository convention that the selecting live date pays zero,
the terminal/N-stage payoff error is at most

    2R/[N(1-x^3)]                                      (4.1)

uniformly over all complete deviations, and the same bound covers the
prescribed profile. Terminal Nash therefore bounds all N-stage gains by
4R/[N(1-x^3)], and prescribed averages converge to the actual initial
phase vector (V_0,V_1,W_2,W_3). That one vector is fixed before accuracy.
This proves the stated uniform-equilibrium conclusion.

The corresponding existing semantic consumers are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
(`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`). The direct
proof above supplies their endpoint and opponent-contraction data without
using any additional source theorem. No new Lean verification is claimed.

## 5. A full sixty-coordinate calibration

Put a=3, b=1, Pi=0, c=-3 and K=-100039998/9999. Let h be the directed cycle

    h(0)=2, h(2)=1, h(1)=3, h(3)=0.                    (5.1)

The arrow j -> h(j) means that h(j) is the unique favorable cross-pair
joiner against sole quitter j. Define EVERY native coordinate Z_i(S).
If i is absent from S, use

    Z_i({m(i)})=3,  Z_i({j})=-1 for j in O(i),
    Z_i(S)=K if S=O(i),
    Z_i(S)=0 for any other opponent pair,
    Z_i(I\{i})=1001.

If i belongs to S, use

    Z_i({i})=0,
    Z_i({i,m(i)})=0,
    Z_i({i,j})=1 if i=h(j), and -100 otherwise, for j in O(i),
    Z_i({i,j,k})=-6 if {j,k}=O(i), and -100 otherwise,
    Z_i(I)=1000.                                     (5.2)

This specifies all sixty coordinates with no convention for an empty
coalition. The actual original calibration is

    r_i(S)=1+Z_i(S) for every NONEMPTY S.              (5.3)

Its own singletons are positive, equal to one; literal AllNever remains
zero and is not an equilibrium. In (1.3) each cross sum is -99<=-6 and
each queried triple is -6. The threshold (1.1) is K<-10, which holds.
Equation (2.1) has the exact interior root x=9999/10000, so q=1/10000. Indeed

    K=(2x-3/x)/(1-x)=-100039998/9999.

The ORIGINAL
phase values are

    v^A=(1,1,3332/3333,3332/3333),
    v^B=(3332/3333,3332/3333,1,1).                     (5.4)

The inactive native Quit endpoint is -99qx-6q^2, whereas its native Continue
value is -3q/x. Continue minus Quit is strictly positive by (3.4), since
-99<=-6 and x>1/2. The exact control below checks every
phase endpoint and geometric continuation equation with rational arithmetic.

The same fixed completion, with ONLY the four opposite-pair passive entries
K varying, belongs to the theorem for every K<-10. All complete-selection
exclusions below hold throughout K<-4956. In particular its participant
rewards remain fixed while these passive entries tend to minus infinity.
Positive participant-coalition jackpot constructions instead let selected
participant rewards grow and keep the other nonsingleton data in a fixed
bounded box. They do not supply this entire passive direction. This is a
comparison of actual raw families, not a claim about every isolated table
under an unspecified older large-parameter threshold.

## 6. Whole-selection comparison with named older producers

The following comparisons concern the COMPLETE calibration (5.2)--(5.3),
not merely one failed parameter choice of an older architecture. They do
not assert noncoverage by every unknown certificate or arbitrary strategy.

### Pure exits and every stationary profile with a sure owner

No pure nonempty quitting coalition is Nash. A sole quitter j recruits
h(j), whose joining gain is 1-(-1)=2. A friendly pair has a member who
leaves reward zero for the passive singleton reward three. Every crossed
pair has one member receiving -100, who prefers leaving for -1. Every
triple contains a friendly pair; either member of that pair receives
-100 and can leave for its passive cross-pair reward zero. Every grand
member can leave 1000 for passive opponent-triple reward 1001. All these
comparisons are unchanged by the original offset one.

In fact there is no stationary Nash profile with any sure owner j.
Its friendly mate m(j) strictly prefers Continue for EVERY opponent
coalition containing j: the joining increments are -3 at {j}, -100 at
the two larger two-opponent events, and -1 at all three opponents.
Thus m(j) has hazard zero. Put k=h(j), and let l=m(k), the remaining
cross owner. Given m(j)'s zero hazard, l's possible opponent coalitions
are {j} and {j,k}; its respective joining increments are -99 and -100.
Hence l also has hazard zero. Now k faces only sure j and has joining
gain two, forcing k to Quit surely. But j's joining gain against k is
-99, contradicting j's sure Quit. This argument covers every choice of
j and all remaining hazards, including boundary mixtures. It excludes
the ordinary sure-owner stationary selection class on this calibration.

More precisely, the first three strict comparisons do not use j's own
best response. They show that the ENTIRE complementary induced Nash
correspondence with j fixed at Quit consists of the one pure law
m(j)=0, l=0, k=h(j)=1. At that law j's leave gain is 99. The opponents'
joint Continue probability is zero, so the coefficient of EVERY supplied
punishment value in the owner's continuation floor is zero. Thus the
singleton-base induced-Nash punishment-tail consumer fails for every
owner, every induced Nash choice, and every punishment continuation.

The same conclusion covers persistent-base selections with additional
fixed outsiders. If the complementary free owners are Nash and every
fixed outsider passes its root no-join test, extending the fixed outsiders
by Continue gives a full complementary induced Nash point. For a singleton
base, the preceding uniqueness then gives the same failed owner floor.
For a base with at least two sure members, a departing base member still
faces another sure opponent, so no punishment coefficient occurs; the base
leave and outsider tests together would give a stationary Nash profile
with a sure owner, already excluded. This audits the full punishment-tail
selection sets without substituting a stationary Never comparison for
their actual continuation values.

These are the actual inputs of
`quittingSingletonBaseOwnerFloorExcess_nonpos_iff` and
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`),
`nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`),
and `QuittingInducedOwnerChamber`
(`UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`).
`QuittingInducedOwnerNeverChamber` in the last file also fails its
own-singleton-nonpositive condition because all original owns are one.

### Product-low premiums and all supportwise upper-average weights

An additional universal raw admission is `HasProductLowQuittingPremium`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`):
every absorbing independent product root must have an active player whose
forced-Quit payoff is at most its own singleton. The exact checked UE
consumer for nonnegative own rewards is
`exists_uniformEquilibriumPayoff_of_productLowPremium`
(`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`).
It fails on this calibration. At the product root where ALL four Quit
surely, EVERY player's forced-Quit reward is 1001, strictly above own1.
The native premium is 1000 for each player. A failed pure-Nash test would
not establish this fact; the literal forced-Quit product witness does.

The full set I is a premium trap, since its grand reward is above own
for every player. At S=I every weighted forced-Quit upper-average row is
1000 SUM_i w_i>0 for every nonzero nonnegative weight vector. Thus no
supportwise nonpositive upper-average certificate can be selected for
that trap. This excludes all such weights, including zero coordinates,
and hence the ordered-premium and supportwise-upper families implying
product-low. A mixed upper-average/boxed-charge class cannot use its
upper branch on I; its charge branch fails the size-two row below.

### All pair schedules and the named pair producers

In the friendly partition, every participant joining increment is -3.
In EITHER crossed partition, every scheduled pair has one favorable
participant and one participant with reward -100 below its passive
singleton -1. Thus EVERY pair partition has a strictly unfavorable
participant comparison. This is invariant under every relabeling.

In particular every pair schedule fails the admission condition that all
scheduled participants receive at least their passive partner-singleton
reward. This is the common necessary raw comparison in the two-pair
join-cap, crossed-matching, bounded inverse-corner and nonmatching
positive-passive-pair classes. The opposite-sign matching class requires its two
members of each scheduled crossed pair to share the required side of the
passive singleton comparison; here each crossed pair has one member on
each side. It therefore also fails for every relabeling.

The positive singleton pairs are exactly the friendly pairs. Their
participant values zero are strictly below their positive passive
singletons three. Therefore the required positive-premium pair in
the negative-pair-funded boundary class does not exist under
any relabeling. The same comparison defeats the global asymmetric
friendly-pair class requiring each friendly participant at least its
passive singleton. Its explicitly bounded open box also cannot contain
the joining increment -3. That box has scheduled increments near 0 or 9/26,
and permits perturbations of only 1/1000000 in raw coordinates.

The simple two-owner stationary negative-pair construction also cannot
apply: a crossed pair always has a participant with value one ABOVE its
passive singleton -1, whereas that construction needs both below. Friendly
singleton comparisons are positive, outside its negative-pair premise.
For the same reason the below-singleton crossed-pair phase class fails:
it requires both scheduled participants below their negative passive
singleton, but every crossed pair has one above. The triple singleton
collision box requires all six directed within-triple pair joining
increments positive; here positive joining increments form only the
directed four-cycle (5.1), so no triple can pass that test.

### Every capped-clock quiet-extension LP fails

Let S be ANY nonempty proper child set, not only a three-player deletion.
The directed four-cycle (5.1) has an edge j in S -> k=h(j) outside S.
In the capped-clock joining row at child coalition {j}, the outsider k's
gain is two. Every potential child responder i in S different from j has
joining gain either -3 (the friendly mate) or -99 (the other cross owner);
the child j's own joining term is zero. Thus for ALL nonnegative weights,

    2 <= SUM_(i in S) lambda_i[Z_i({i,j})-Z_i({j})]

is impossible. This is an exact one-row infeasibility certificate for
every choice of child and outside weights. It defeats both the capped-
clock quiet lift and its nonnegative-singleton terminal relaxation, before
their future or Never rows need to be tested. Original row offsets cancel
from every joining increment. It also defeats unweighted join-antitone
quiet deletion. This comparison uses the actual finite J rows in
`CappedClockParentRewardCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`).
The nonnegative-singleton quiet relaxation changes only its Never row;
it retains this exact joining row and hence has the same obstruction.

### Premium traps and passive-cap chambers

The full set I is a premium trap: every i has its favorable cross pair
reward one above its native own level zero. For T equal to either friendly
pair, the mixed-premium-trap joining sum is

    L_I(T)=2[-6-K]>0.                                 (6.1)

The mixed-premium-trap class requires this size-two row L_I(T)<=0 and
therefore fails outright. No choice of its charge constants, own offsets,
or relabeling repairs this violated
raw row. The unit-own capped-participant class fails because the original
favorable cross participant receives two, above its own one.

The same intermediate L row excludes the boxed-charge alternative of
the mixed upper-average/charge criterion: both outsiders have positive
joining gain -6-K at a mate pair. It also excludes every strictly
positive weighted aggregate-leave test on the full trap, because its
weighted sum is (-6-K)(w_j+w_k)>0. Independently, a global nonnegative
forced-Quit floor would require w_(h(j))>=100 w_(h^(-1)(j)) at each
singleton {j}. Taking the four singleton rows forces w_0=w_1=0 and
w_2=w_3=0. Thus there is no nonzero nonnegative floor weight either.

The greatest premium core is all four players, so classes requiring
its size at most two or exactly three do not apply under any relabeling.
Every player has a cross-pair participant premium -100<0, so no player
has nonnegative participant premiums at EVERY containing coalition.
The maximal protected set is therefore empty, excluding both a common
protected leaver and every support-specific protected-leaver selection.

The sink-or-receiver-cap weighted passive-ledger condition is
H_w(S)=SUM_i w_i[Z_i(S)-Z_i({i})]>=0 at every proper nonempty S,
for some nonzero nonnegative weight vector w. It fails for EVERY such
vector: H_w(01)>=0 would give
K(w_2+w_3)>=0 and hence w_2=w_3=0. The required H_w(23)>=0 then gives
w_0=w_1=0, contradiction. The specific monotone-passive and passive-triple
cap table families require their passive pair entries to be positive;
the calibration has passive original friendly-pair reward 1+K<0.

Finally define the singleton matrix by Gamma_ii=0 and Gamma_ij=Z_i({j})
for i!=j. It has paired reciprocal signs, determinant 45, and inverse

    Gamma^(-1)=(1/15) [[2,7,3,3], [7,2,3,3],
                       [3,3,2,7], [3,3,7,2]].

It does not enter the
negative-determinant inverse theorem. Each proper triple has an unpaired
row with both off-diagonal entries negative, so no proper triple has a
nonnegative inverse: otherwise its inverse applied to the all-one vector
would be nonnegative, yet its unpaired row could not produce one.
The cross principal block [[0,-1],[-1,0]] is not a Q matrix, since for
the constant vector (-1,-1), the vector w=(-1,-1)+Gamma_block*z has
both entries negative for every z>=0. It also has no nonzero nonnegative
homogeneous solution: Gamma_block*z=(-z_1,-z_0)>=0 forces z=0, which
cannot belong to the simplex. The standard-or-homogeneous split in
`isProjectiveQMatrix_iff_standard_or_homogeneous` therefore excludes the
projective Q property too. In particular `IsProjectiveQBarMatrix` fails,
because it requires that property on every nonempty principal block
(`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`).
The exact implemented balanced-singleton certificate
requires an escort cycle by
`BalancedSingletonCycleCertificate.exists_escortCycle`
(`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`). Every
escort edge i -> j requires Gamma_ij<=0<=Gamma_ji with i!=j. The paired
matrix has strictly reciprocal same signs on every distinct pair, so it
has no such edge on the full set or on any principal restriction. This
is the exact named singleton-certificate exclusion, not a statement about
all singleton strategies.

The cyclic-three-child families require a principal triple with the
cyclic positive-inverse singleton pattern; the negative unpaired row
just identified excludes every triple choice. Their explicit reference
tables also have reciprocal opposite singleton signs, absent here.
The scalar singular-circuit criterion requires a pair with
s_i-r_i({j})>0 and r_j({i})-s_j>0, hence opposite reciprocal singleton
signs. It fails under every role permutation for the same reason.

Among the paired-singleton finite calendar classes, the four-joint-row
rectangle and its explicit bounded reference box require friendly
participant rewards above their passive singleton rewards, whereas here
they equal own and lie below. The four-phase nonnegative-passive ray
requires positive native friendly participant rewards and nonnegative
original passive pair rewards, whereas here they are zero and 1+K<0. The exact
four-singleton-phase cap class requires both members of every cross pair
to have original participant reward at most own; every cross pair here
has one reward2>own1. These are failures of their stated raw admissions,
not exclusion of arbitrary alternative calendar solutions.

Finally the positive singleton-joining graph is exactly h. Each edge
j -> h(j) has gain2 at the empty background but gain -100 on the
nonempty background {mate(h(j))}: the queried participant triple has
native reward -100 and its passive cross-pair reward is0. Therefore the
no-strict-background-reversal criterion fails, and no one of these edges
is a background-uniform robust join. All other edges already have
negative gain at the empty background. This checks that distinct
graph-based source as well as the singleton escort source above.
The exact implemented consumer is
`finFour_exists_uniformPayoff_of_noStrictBackgroundReversal`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/RobustJoinStrictBackgroundReversal.lean`).

### Every role choice in the three-passive-poles endpoint class

For completeness the following spells out the finite raw guard that is
enough to exclude all role selections of that stationary producer, without
making any assertion about unknown large-parameter thresholds.
For an ordered role permutation (u,v,w,z) of I, its initial guards include

    A0=Z_u({u,z})-Z_u({z})>0,
    B0=Z_u({u,w,z})-Z_u({w,z})<0,
    d=A0/(A0-B0),
    F1=(1-d)[Z_z({u,z})-Z_z({u})]
           +d[Z_z({u,w,z})-Z_z({u,w})]<0.             (6.2)

These are translation-invariant raw endpoint expressions; positive row
scales preserve their signs. A0>0 requires u=h(z), since this is the only
positive joining increment in that column. If w=m(z), then B0=-6-K>0,
which violates the second guard. The only remaining choice is w=m(u).
Thus exactly four ordered role choices can pass the first two guards:

    (0,2,1,3), (1,3,0,2), (2,1,3,0), (3,0,2,1).

For every one, A0=2, B0=-100 and d=1/51. Consequently

    F1=[-4950-6-K]/51=16828318/169983>0,              (6.3)

contradicting (6.2). This excludes the complete set of 24 role selections
before its strategic root or asymptotic threshold is considered.

The comparisons above establish a concrete selection-set separation from
the applicable named raw families. They do NOT exclude all stationary
profiles with every positive hazard strictly below one, arbitrary other
periodic schedules, or possible separate existence proofs for this table.

## 7. Exact boundary tests

The complete control in Section 9 checks all sixteen phase endpoints, the actual geometric policy and
Never recursions, every nonempty pure coalition, all proper child J-row
certificates, every relabeled pair comparison, the larger-trap obstruction,
all 24 passive-pole role permutations, and the sure-owner elimination
inequalities. The all-deadline and uniform-
horizon proof is Section 4; a finite response sample is not substituted
for that proof.

The root interval is essential. In the exact calibration the same scalar
equation has another root x=1/3334. It gives q=3333/3334 and inactive native
Continue value -9999, whereas inactive Quit is
-66983301/11115556. Its gain is 111077461143/11115556>0. Thus a supplied
scalar zero alone would not establish Nash: selecting x>1/2 is a real
part of the raw producer and the full endpoint proof.

The inactive-response bounds are also substantive. For example, retain
the selected calibration and replace both cross-participant entries of
one inactive player by 100. Its inactive native Quit is then
200qx-6q^2>0, strictly above its negative Continue value. All active
indifference equations remain unchanged. Hence those equations cannot
substitute for (1.3).

The hypothesis bounds K from above but need not make K negative: taking
a=3, b=1 and Pi=29/10 makes the upper threshold 3/20. A small positive
K below that number is allowed by the same proof. The main calibration
uses negative K to separate the previous finite admission conditions.

## 8. Adapter, semantic consumer and Lean handoff

No strategic witness is assumed. The adapter reads the literal 60 rewards,
extracts the given pair partition and raw parameters in (1.1)--(1.3),
uses the scalar intermediate value theorem to choose x once, and builds
the two actual product roots with q=1-x. Formula (3.1) gives their value
annotations; Sections 3--4 prove that they are the actual terminal values.

A Lean raw-data structure should contain only the pair relabeling, real
parameters, positive row scales, exact reward equalities, and finite
inequalities (1.1)--(1.3). It should not contain a root, continuation value,
Nash strategy, threshold selection, or the desired conclusion. A scalar
existence theorem first produces x in (1/2,1) satisfying (2.1). The finite
phase root uses a Bernoulli q for each scheduled owner and pure Continue
for each other owner. Its proof obligations are precisely:

1. policy recursion `value phase = quittingRootSuccessorPayoff reward
   (value nextPhase) (cycle phase)`, supplied by (3.2)--(3.3);
2. `IsεQuittingRootNash reward (value nextPhase) 0 (cycle phase)`, supplied
   by the sixteen endpoint comparisons including (3.4);
3. every player's product of opponent Continue masses over the two phases
   is x^3<1.

The two existing periodic declarations named at the end of Section 4 then
consume exactly those fields. The new mathematical obligation is the raw
producer, not another checker for a supplied periodic certificate. Its
uniform target can either be stated as the existing actual cyclic terminal
value or identified with (V_0,V_1,W_2,W_3) using policy uniqueness.

The source audit here is static: no new Lean file was written or checked.
Only the ordinary mathematics and exact finite controls are asserted.

## 9. Complete exact control

Run the following self-contained Python 3 program. It uses only the standard
library and exact rational arithmetic. Its finite deadline samples are
supplementary; Section 4 proves the complete behavioral and horizon caps.

```python
"""Exact full60 calibration; finite samples do not replace the all-deadline proof."""
from fractions import Fraction as F
from itertools import combinations, permutations

I = frozenset(range(4))
COALITIONS = [frozenset(s) for n in range(1, 5) for s in combinations(I, n)]
H = (2, 3, 1, 0)
K, X, Q = -F(100039998, 9999), F(9999, 10000), F(1, 10000)


def mate(i):
    return i ^ 1


def opposite(i):
    return I - {i, mate(i)}


def native(i, s):
    assert s
    if i not in s:
        if len(s) == 1:
            return F(3 if mate(i) in s else -1)
        return F(1001) if len(s) == 3 else (K if s == opposite(i) else F(0))
    if len(s) == 1:
        return F(0)
    if len(s) == 2:
        j = next(iter(s - {i}))
        return F(0 if j == mate(i) else (1 if H[j] == i else -100))
    if len(s) == 3:
        return F(-6 if s - {i} == opposite(i) else -100)
    return F(1000)


Z = {(i, s): native(i, s) for i in I for s in COALITIONS}
R = {key: 1 + z for key, z in Z.items()}
assert len(Z) == len(R) == 60
assert all(R[i, frozenset({i})] == 1 for i in I)
assert all(R[i, I] == 1001 > R[i, frozenset({i})] for i in I)
assert all(Z[i, I] == 1000 and Z[i, I-{i}] == 1001 for i in I)
# The literal allQuit product root falsifies product-low for every active owner.
# The same grand row falsifies every nonzero nonnegative upper-average weight.
assert all(Z[i, I] > 0 for i in I)


def join(i, s):
    assert i not in s and s
    return Z[i, s | {i}] - Z[i, s]


def product_law(players, hazards):
    players = tuple(players)
    for bits in range(1 << len(players)):
        s, probability = set(), F(1)
        for k, i in enumerate(players):
            quit_now = bool(bits & (1 << k))
            probability *= hazards[i] if quit_now else 1 - hazards[i]
            if quit_now:
                s.add(i)
        yield frozenset(s), probability


ACTIVE = (frozenset({0, 1}), frozenset({2, 3}))
HAZARDS = [{i: Q if i in a else F(0) for i in I} for a in ACTIVE]
V = [[F(1) if i in a else F(3332, 3333) for i in I] for a in ACTIVE]


def endpoint(phase, i, quit_now, next_value):
    total = F(0)
    for s, probability in product_law(I - {i}, HAZARDS[phase]):
        result = s | {i} if quit_now else s
        total += probability * (R[i, result] if result else next_value)
    return total


for i in I:
    j, k = sorted(opposite(i))
    assert Z[i, frozenset({i, mate(i)})] == 0
    assert Z[i, opposite(i)] == K
    assert Z[i, frozenset({i, j})] + Z[i, frozenset({i, k})] == -99
    assert Z[i, frozenset({i, j, k})] == -6
assert K < -10
assert -3 / X + 2 * X - K * (1 - X) == 0
assert -3 / F(1, 2) + 1 - K / 2 > 0
assert -3 + 2 < 0
for phase in range(2):
    for i in I:
        cont = endpoint(phase, i, False, V[1 - phase][i])
        quit_value = endpoint(phase, i, True, V[1 - phase][i])
        assert cont == V[phase][i]
        if i in ACTIVE[phase]:
            assert quit_value == V[phase][i]
        else:
            assert quit_value == 1 - 99 * Q * X - 6 * Q**2
            assert cont - quit_value > 0
        assert (HAZARDS[phase][i] * quit_value
                + (1 - HAZARDS[phase][i]) * cont) == V[phase][i]

# Solve actual affine policy and Never recursions, without value annotations.
for i in I:
    nr, ns, pr, ps = [], [], [], []
    for phase in range(2):
        never_pay = never_surv = policy_pay = policy_surv = F(0)
        for s, probability in product_law(I - {i}, HAZARDS[phase]):
            if s:
                never_pay += probability * R[i, s]
            else:
                never_surv += probability
        for s, probability in product_law(I, HAZARDS[phase]):
            if s:
                policy_pay += probability * R[i, s]
            else:
                policy_surv += probability
        nr.append(never_pay)
        ns.append(never_surv)
        pr.append(policy_pay)
        ps.append(policy_surv)
    assert ns[0] * ns[1] == X**3 < 1
    assert ps[0] * ps[1] == X**4 < 1
    for phase in range(2):
        other = 1 - phase
        never = (nr[phase] + ns[phase] * nr[other]) / (1 - X**3)
        policy = (pr[phase] + ps[phase] * pr[other]) / (1 - X**4)
        assert never == policy == V[phase][i]
    for deadline in range(20):
        continuation = endpoint(deadline % 2, i, True, F(0))
        for date in reversed(range(deadline)):
            continuation = endpoint(date % 2, i, False, continuation)
        assert continuation <= V[0][i]

for s in COALITIONS:
    gains = []
    for i in I:
        altered = s - {i} if i in s else s | {i}
        gains.append((R[i, altered] if altered else F(0)) - R[i, s])
    assert max(gains) > 0

# Whole sure-owner induced Nash set; the sole forced opponent makes all
# punishment/empty-opponent coefficients zero, with owner leave gain99.
for j in I:
    m, k = mate(j), H[j]
    l = mate(k)
    assert len({j, m, k, l}) == 4
    for s in COALITIONS:
        if j in s and m not in s:
            assert join(m, s) < 0
    assert join(l, frozenset({j})) == -99
    assert join(l, frozenset({j, k})) == -100
    assert join(k, frozenset({j})) == 2
    assert join(j, frozenset({k})) == -99
    assert join(m, I-{m}) == -1
    assert join(k, frozenset({j, l})) == -100  # strict background reversal

for child in COALITIONS:
    if child == I:
        continue
    edges = [j for j in child if H[j] not in child]
    assert edges
    j, outsider = edges[0], H[edges[0]]
    assert join(outsider, frozenset({j})) == 2
    assert all(join(i, frozenset({j})) in {-3, -99} for i in child - {j})

PARTITIONS = [({0, j}, set(I - {0, j})) for j in (1, 2, 3)]
for partition in PARTITIONS:
    increments = []
    for pair in partition:
        i, j = sorted(pair)
        inc = [join(i, frozenset({j})), join(j, frozenset({i}))]
        assert sorted(inc) == ([-3, -3] if mate(i) == j else [-99, 2])
        increments.extend(inc)
    assert min(increments) < 0
for pair in combinations(I, 2):
    i, j = pair
    if mate(i) == j:
        assert max(join(i, frozenset({j})), join(j, frozenset({i}))) < 0
    else:
        assert max(join(i, frozenset({j})), join(j, frozenset({i}))) > 0
for pair in ACTIVE:
    assert sum(join(i, pair) for i in I - pair) == 2 * (-6 - K) > 0
    assert all(Z[i, pair] == 0 for i in pair)
    assert all(Z[i, pair] == K < 0 for i in I - pair)
assert all(max(Z[i, s] for s in COALITIONS if i in s) > 0 for i in I)
assert all(min(Z[i, s] for s in COALITIONS if i in s) < 0 for i in I)
traps = [a for a in COALITIONS if all(
    any(s <= a and i in s and Z[i, s] > 0 for s in COALITIONS) for i in a)]
assert traps == [I]
inverse_h = {H[j]: j for j in I}
for j in I:
    assert Z[H[j], frozenset({H[j], j})] == 1
    assert Z[inverse_h[j], frozenset({inverse_h[j], j})] == -100
    assert H[H[j]] == mate(j)
G = [[F(0) if i == j else Z[i, frozenset({j})] for j in I] for i in I]
INV = [[F(v, 15) for v in row] for row in
       [[2, 7, 3, 3], [7, 2, 3, 3], [3, 3, 2, 7], [3, 3, 7, 2]]]
assert all(sum(G[i][k] * INV[k][j] for k in I) == int(i == j)
           for i in I for j in I)
for omitted in I:
    triple = I - {omitted}
    assert all(G[mate(omitted)][j] < 0 for j in triple - {mate(omitted)})
assert all(G[i][j] * G[j][i] > 0 for i in I for j in I if i != j)

# The older three-passive-poles producer: all24 role selections.
def z(i, *s):
    return Z[i, frozenset(s)]


first_guard_roles = 0
for i, j, k, l in permutations(I):
    a0, b0 = z(i, i, l) - z(i, l), z(i, i, k, l) - z(i, k, l)
    if not (a0 > 0 and b0 < 0):
        continue
    first_guard_roles += 1
    c = a0 / (a0 - b0)
    a2, b2 = z(k, k, l) - z(k, l), z(k, i, k, l) - z(k, i, l)
    l0 = (1-c) * (z(j, j, l)-z(j, l)) + c * (z(j, j, k, l)-z(j, k, l))
    l1 = (1-c) * (z(j, i, j, l)-z(j, i, l)) + c * (z(j, i, j, k, l)-z(j, i, k, l))
    f0 = c * ((1-c)*z(l, l) + c*z(l, k, l) - z(l, k))
    f1 = (1-c)*(z(l, i, l)-z(l, i)) + c*(z(l, i, k, l)-z(l, i, k))
    assert (a0, b0, c) == (2, -100, F(1, 51))
    assert a2 < 0 and b2 < 0 and l0 < 0 and l1 < 0 and f0 == F(52, 2601)
    assert f1 == F(16828318, 169983) > 0  # old admission requires f1<0
assert first_guard_roles == 4

# A second scalar root fails a full cap: an exact falsification attempt.
bad_x, bad_q = F(1, 3334), F(3333, 3334)
assert -3 / bad_x + 2 * bad_x - K * (1-bad_x) == 0
bad_cont, bad_quit = -3 * bad_q / bad_x, -99 * bad_q * bad_x - 6 * bad_q**2
assert bad_cont == -9999 and bad_quit == -F(66983301, 11115556)
assert bad_quit - bad_cont == F(111077461143, 11115556) > 0
assert 200 * Q * X - 6 * Q**2 > 0 > -3 * Q / X
print("PASS: full60; scalar root; all16 endpoints; actual policy/Never; 20 deadlines")
print("PASS: all pure exits; whole sure-owner/punishment selections; all14 child J rows")
print("PASS: all3 pair partitions; all6 pairs; all24 pole roles; trap/ledger; positive inverse")
print("PASS: second scalar root violates full cap; missing inactive bound violates full cap")
print("PASS: literal allQuit defeats product-low/upper weights; protected set empty; full core")
print("PASS: singleton floor-weight obstruction; every positive edge reverses on a background")
```

## 10. Scope and remaining frontier

The theorem restricts the scheduled-pair and inactive-response coordinates;
it does not cover all 44 nonsingleton completions of the paired singleton
matrix. It is an actual raw producer beyond the stated older admission
sets, not an arbitrary-game claim or an inert-source contradiction. The
no-UE Fin4 frontier remains open.
