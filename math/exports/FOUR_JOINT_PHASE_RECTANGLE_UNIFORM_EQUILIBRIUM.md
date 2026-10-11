# Four joint phases on an unbounded reward region

## Raw game data and conclusion

Let I={0,1,2,3}. At every live date players independently choose Continue
or Quit, using private behavioral randomization and publicly observed past
actions. The first nonempty quitting coalition S absorbs at the given finite
reward vector r(S) in R^4. Live dates and the selecting date pay zero;
subsequent absorbed dates pay r(S). Perpetual continuation pays zero.
Deviations replace one player's entire behavioral rule, including unrestricted
memory, randomization, late deadlines and Never. All conclusions are in
expectation. No public correlation is added.

Fix the singleton rows literally as

    r(0)=(1,4,0,0),       r(1)=(4,1,0,0),
    r(2)=(0,0,1,4),       r(3)=(0,0,4,1).                    (1)

Choose any finite real parameters

    R≥0,       S≥6,       V≥10,       W≥48,

and fix the four scheduled pair rows as

    r(01)=(5,9/2,R,S),       r(23)=(R,S,5,9/2),
    r(12)=(V,2,2,W),         r(03)=(2,W,V,2).                (2)

The eight triple-recipient coordinates in the next table are arbitrary
finite numbers. The last column lists the other, completely unrestricted
recipients of each triple.

| S | Triple coordinates used in L | Other arbitrary recipients |
|---|---|---|
| 012 | 0,2 | 1,3 |
| 013 | 1,3 | 0,2 |
| 023 | 0,2 | 1,3 |
| 123 | 1,3 | 0,2 |

Set

    M=max(5,R,S,V,W),
    L=max(5,r_0(012),r_2(012),r_1(013),r_3(013),
                r_0(023),r_2(023),r_1(123),r_3(123)).

Require only the following four additional upper bounds:

    r_0(02),r_2(02),r_1(13),r_3(13) < −24 M L.             (3)

The four passive coordinates r_1(02),r_3(02),r_0(13),r_2(13), the other
eight triple coordinates, and all four grand-row coordinates r_i(I) are
arbitrary finite rewards. In particular no triple or grand reward has a
sign restriction; positive triple rewards affect L and are paid for by (3).
All sixty rewards remain finite original-game inputs.

**Theorem.** Every raw table satisfying (1)–(3) has an exact terminal Nash
equilibrium against all complete unilateral behavioral deviations. It uses
the deterministic repeated pair schedule

    A=01,       B=12,       C=23,       D=03,

with independent private scheduled Quit probabilities strictly between1/6
and1, and pure Continue for unscheduled players. Its actual phase-A
terminal payoff is one fixed original-game uniform-equilibrium payoff.
The same profile works for every accuracy and all sufficiently large
finite horizons.

No root, clock, continuation target, Nash row, strategic certificate or
limiting law is a supplied hypothesis. No payoff normalization, transport
or public seed is used. The proof produces the hazards from two continuous
raw-data equations with exact opposite boundary signs. The reward region
is unbounded, but retains the exact singleton and pair identities (1)–(2);
this is not an arbitrary-Fin4 or full-dimensional-class theorem, a claim
that four phases are necessary, or a stationary-equilibrium exclusion.
It is ordinary mathematics, not a new Lean-checked result.

## Two variables produce all owner equalities

For variables a,g put

    b=g/[2(1−g)],       d=a/[2(1−a)].

The scheduled hazards in increasing player order are

    A:(a,b),       B:(g,d),       C:(a,b),       D:(d,g).      (4)

Define explicit scalar functions of the raw data and these variables:

    v0=1+4b,             v1=1+(7/2)a,
    u1=1+d,              u2=1+g,
    w0=abR+(1−a)(1−b)u2,
    z0=4g(1−d)+gdV+(1−g)(1−d)w0,
    z1=4d(1−g)+dgW+(1−d)(1−g)v1,
    w1=abS+(1−a)(1−b)z1.                                  (5)

Only two residuals remain:

    F_A(a,g)=1−(1−b)z0,
    F_B(a,g)=1+d−(1−d)w1.                                 (6)

At a simultaneous zero, the four phase vectors are

    U_A=(v0,v1,w0,w1),       U_B=(z0,u1,u2,z1),
    U_C=(w0,w1,v0,v1),       U_D=(u2,z1,z0,u1).              (7)

These are not independently supplied continuations. The passive-coordinate
policy recursions are exactly the four definitions w0,z0,z1,w1 in (5).
For the active coordinates, the literal Quit and Continue endpoints are

| Slot | Quit | Continue | Difference |
|---|---|---|---|
| A0 | 1+4b | 4b+(1−b)z0 | F_A |
| A1 | 1+(7/2)a | 4a+(1−a)(1+d) | 0 |
| B1 | 1+d | (1−d)w1 | F_B |
| B2 | 1+g | (1−g)(1+4b) | 0 |

The second and fourth equalities use precisely d=a/[2(1−a)] and
b=g/[2(1−g)]. The half-turn (0 2)(1 3) gives the corresponding four
rows at C,D, since all prescribed singleton and scheduled-pair rows have
that identity. No symmetry of the other reward coordinates is needed.

Thus the sixteen policy-recursion residuals, namely U_t minus its immediate
reward vector minus joint survival times U_(t+1), are (1−a)F_A at A0,C2,
(1−g)F_B at B1,D3, and zero at the other twelve coordinates. At a zero
of (6), every recursion is literal. Proper hazards make period survival
less than one, so uniqueness of the contracting policy recursion identifies
(7) with the actual expected terminal payoffs.

## A zero on an explicit rectangle

Put

    e=1/(4M),       h=(1−e)/(3/2−e),
    Q=[1/4,h]×[1/4,h] in coordinates (a,g).                (8)

Because M≥48, h>1/4 and h<2/3. On Q,

    1/4≤a,g≤h<2/3,       1/6≤b,d≤1−e<1.

Every scalar in (5) belongs to [0,M]. First v0≤5, v1≤10/3,
u1≤2 and u2≤5/3. The remaining formulas are nonnegative combinations
of numbers already bounded by M, with coefficient sum at most one.
In particular z0,w1≤M. All formulas are continuous on Q.

On its lower g face, g=1/4 and b=1/6. Since d≥1/6 and V≥10,

    z0 ≥ g[(1−d)4+dV]
        =1+d(V−4)/4 ≥5/4,
    F_A ≤1−(5/6)(5/4)=−1/24.                              (9)

On its lower a face, a=1/4 and d=1/6. Since S≥6,W≥48,g≥1/4,

    w1 ≥ bS/4+(1−b)gW/8
        ≥(3/2)b+(3/2)(1−b)=3/2,
    F_B ≤7/6−(5/6)(3/2)=−1/12.                           (10)

On its upper g face, b=1−e, hence

    F_A=1−e z0 ≥1−eM=3/4.

On its upper a face, d=1−e, hence

    F_B=1+d−e w1 ≥1−eM=3/4.                              (11)

Apply Poincare–Miranda to the field (F_B,F_A) in coordinate order (a,g).
The strict opposite signs (9)–(11) produce a simultaneous zero strictly
inside Q. All eight hazards in (4) therefore exceed1/6 and are less than1.
The rectangle, fields and boundary signs are produced from the raw reward
parameters before any equilibrium is selected. No nonsingularity, uniqueness
or executable numerical root-selection assumption is needed.

## Inactive endpoints retain all simultaneous quit outcomes

At each inactive slot, the Quit endpoint has exactly one reward from (3),
with coefficient a scheduled hazard times the other scheduled Continue
probability. The complete list is

| Slot | Negative barrier reward | Its coefficient |
|---|---|---|
| A2 | r_2(02) | a(1−b) |
| A3 | r_3(13) | (1−a)b |
| B0 | r_0(02) | (1−g)d |
| B3 | r_3(13) | g(1−d) |
| C0 | r_0(02) | a(1−b) |
| C1 | r_1(13) | (1−a)b |
| D1 | r_1(13) | (1−d)g |
| D2 | r_2(02) | d(1−g) |

On Q every scheduled hazard is at least1/6 and every scheduled Continue
probability is at least e. Each coefficient is therefore at least
e/6=1/(24M). All other constituents of the inactive Quit endpoint are
bounded above by L: its own singleton1, a scheduled-pair participant reward
at most5, and one of the eight listed triple coordinates. If c is the
barrier coefficient, that endpoint is strictly less than

    (1−c)L−c(24ML) ≤ L−c(24ML) ≤0.                        (12)

Its Continue value is nonnegative, because every prescribed singleton and
scheduled-pair reward is nonnegative. Thus all eight inactive inequalities
are strict at the produced zero. No triple outcome was removed or replaced
by a categorical approximation; its full positive contribution is included
in L and paid by (3).

For completeness, the only possible extra non-prescribed coalition rows
in a replacing player's OWN payoff are02,012,023 for players0/2, and
13,013,123 for players1/3. Hence the twelve arbitrary proper coordinates
outside those recipient lists and all four grand coordinates are absent
from their recipient's unilateral comparisons. They may affect another
player's reward during somebody else's deviation, which is irrelevant to
unilateral Nash. Grand is unreachable under any replacement because at most
two opponents are scheduled at a live date.

## Independent clocks and complete behavioral equilibrium

Let q_i(t) be (4), periodically repeated when i is scheduled, and zero
otherwise. Independently sample private clocks with

    Pr(T_i=t)=q_i(t) product_(s<t)(1−q_i(s)).                (13)

Each player is scheduled twice per period with hazard greater than1/6,
so each clock is proper and has zero Never mass. This produces exactly
the four-phase policy and actual values (7), without a public random seed.

All active endpoints equal the actual continuation value and all inactive
Quit endpoints are inferior. Fix any complete unilateral replacement.
Its three opponents retain six scheduled private coins per period, each
with Quit probability greater than1/6. Their deleted-player period
survival is bounded by

    rho=(5/6)^6<1,
    Pr(survive m periods under the replacement)≤rho^m.     (14)

The opponents' coins on the unique live all-Continue history are unaffected
by the replacement. Its unrestricted memory and private randomization only
mix its two current endpoints. Iterate their upper bounds through m periods,
retaining the actual absorbing rewards. The remaining continuation term
is bounded by a fixed finite value bound times rho^m. Letting m tend to
infinity proves that EVERY complete behavioral replacement has terminal
payoff at most U_Ai. This includes all finite deadlines, arbitrarily late
deadlines and Never. The prescription attains U_Ai, so its full terminal
cap is exactly U_Ai and its full regret is zero.

Choose any finite B bounding absolute rewards of the given original table.
For the first selecting date tau starting at zero, (14) gives

    E[tau+1]≤4/(1−rho)

uniformly under every replacement. The N-date expected average differs
from the terminal expectation by at most4B/[(1−rho)N]; the selecting
date's zero is included in tau+1. Every average-game deviation gain is
therefore at most8B/[(1−rho)N]. The actual target U_A is fixed before
accuracy, and the same profile works at every sufficiently large horizon.
This proves the theorem. No reward bound uniform over the entire unbounded
source class is needed.

## Exact tests against named source selection sets

For ANY parameters allowed in (2), choose a finite K satisfying

    K>max(4,24M max(5,R+1,W+1)).

Set both unscheduled pair rows to (−K,−K,−K,−K) and take

    r(012)=(−K,−K,R+1,−K),
    r(013)=(−K,W+1,−K,−K),
    r(023)=(R+1,−K,−K,−K),
    r(123)=(−K,−K,−K,W+1),
    r(I)=(−2K,−2K−1,−2K−2,−2K−3).                        (15)

This is a member of (1)–(3) for every parameter choice in the unbounded
region. One explicit finite instance is R=0,S=6,V=10,W=48,K=56449.
The following bounded comparisons concern these completions, not every
arbitrary completion admitted by the theorem.

### Singleton and literal response-quotient tests

The receiver-row/solo-owner-column comparison matrix is

    Gamma=[0,3,−1,−1; 3,0,−1,−1;
           −1,−1,0,3; −1,−1,3,0].

It has eigenvalues1,5,−3,−3, determinant45, and positive inverse with
diagonal2/15, favorite entries7/15 and cross entries1/5. Principal pair
determinants are−9 or−1; each triple determinant is6 and its inverse
has a negative diagonal. All principal matrices are nonsingular. A nonzero
homogeneous complementarity support of size at least two would require
a kernel vector of a principal matrix; singleton support is excluded by
a negative off-diagonal entry in every column. Thus Gamma is R0 with
degree+1, not the negative-determinant inverse criterion. The literal paired
matrix is also ordinary standard-Q, has full normal core, has no homogeneous
simplex solution, and fails projective Q-bar. The named full/triple inverse,
non-Q and projective singleton sources therefore do not dispatch (15).

At all-sure hazards the responses are

    r_i(I)−r_i(I−i)=(−K,−K−1,−K−2,−K−3).

Every nondiscrete partition equates two unequal responses, excluding all
fourteen literal response-invariant quotients. Positive playerwise affine
rescaling does not repair this: summing necessary singleton block-row
identities, using common row sum1, forces equal positive scales inside
each block. The displayed unequal responses remain unequal. The discrete
quotient has degree+1. This is not a claim about every possible strategy
quotient, and changing the grand row could restore a solved symmetry.

### Every nonnegative-weight proper quiet child, including withdrawal

The nonnegative donor criterion requires outsider joining gain to be at
most a nonnegative weighted sum of child joining gains, for EVERY child
coalition T. Every triple child fails for every weight vector:

| Child | T | Omitted outsider's gain | Sole child donor's gain |
|---|---|---|---|
| 013 | 01 | 1 | −K−S |
| 123 | 23 | 1 | −K−S |
| 012 | 12 | 1 | −K−V |
| 023 | 03 | 1 | −K−V |

Members of T have zero gain, so no nonnegative weights can repair these
comparisons. Each scheduled pair child fails at its whole coalition, with
outsider gain1 and no child donor. Child02 at T={2} has outsider1 gain2
against donor0 gain−K; child13 at T={3} has outsider0 gain2 against
donor1 gain−K. Every singleton child has an outsider joining gain2.
Thus the entire proper-child selection set fails this named quiet-lift test.

The same witnesses exclude all five raw withdrawal kinds, not only
advancing-only weights. In a child C, let A be its first nonempty coalition.
Every corresponding future/join-only certificate requires the joining row

    r_e(A+e)−r_e(A)
       ≤ sum_(i in C) [lambda_i (r_i(A+i)−r_i(A))
                                      +mu_i w_i^kind(A)],  (15a)

with lambda_i,mu_i≥0. A nonmember of A has withdrawal gain0. For a member
of nonsingleton A, ALL five kinds have exactly

    w_i^kind(A)=r_i(A−i)−r_i(A).

The member withdrawal gains on the scheduled pairs are

    A=01 or23: (−1,−1/2),       A=12 or03: (−2,−2).         (15b)

For a singleton A={i}, the gain is its selected restart floor minus
s_i=1. Every kind's floor is at most1. The patient floor is at most
max(s_i,0)=1. Deadline and cancellation use a zero-or-passive floor≤0.
Terminal security uses the maximum of that floor and a security LP value;
the LP has the own-singleton constraint, so its value≤1. Evaluated
security further truncates that terminal floor at0. These are the literal
five floors, not a bound on an arbitrary hypothetical restart operation.

Thus every withdrawal term in each chosen child witness is nonpositive.
Every advancing term is also nonpositive by the table above, and the
omitted outsider's joining gain is strictly positive. Equation (15a)
is impossible for EVERY nonnegative pair of weight arrays and every
patient, deadline, evaluated-security, terminal-security or cancellation
kind. This excludes all their F/J-only certificates and therefore the
stronger full Never/future/join certificates. Charging or omitting a Never
row cannot repair a joining row already contradicted in this way. A
multiple-outsider family necessarily contains the selected bad outsider
of each child, so it also fails. No claim about every conceivable quiet
mechanism is made.

### Every sure-owner and persistent-base induced Nash selection

For sure owner0 let (x,y,z)=(q1,q2,q3). The other players' exact
Quit-minus-Continue differences in its full induced game are

    d1=(1−y)(1/2+z/2)−(K+1)yz,
    d2=(1−z)[−K+(K+1)x]+z[−K−V+(V−2)x],
    d3=2−(K+S+2)x−2y+(S−1)xy.                             (16)

At Nash, z>0 implies d3≥0 and x≤2/(K+3); then d2<0 forces y=0,
and d1>0 forces x=1, a contradiction. Thus z=0. If y<1, d1>0
forces x=1, then d2>0 forces y=1. Consequently the full induced Nash
set is precisely

    z=0,       y=1,       x∈[K/(K+1),1].

The owner's reward is−K and its Continue payoff is Vx. Opponents'
joint Continue mass is zero, so every punishment-floor excess is K+Vx>0,
whatever the supplied punishment value.

For sure owner1 let (x,y,z)=(q0,q2,q3). The exact differences are

    d0=(1−z)[1−(K+V+1)y]−Kyz,
    d2=(1−z)(2−x)−(K+2)xz,
    d3=−K−Sx+(K+1)y+(S−K−4)xy.                            (17)

If z=0, d2>0 forces y=1, d0<0 forces x=0, then d3=1 contradicts
z=0. If z>0, d3≥0 forces y≥K/(K+1), since its x coefficient is
strictly negative. Hence d0<0 forces x=0. If z<1 then d2>0 forces
y=1 and d3=1 forces z=1. The full Nash set is precisely

    x=0,       z=1,       y∈[K/(K+1),1].

The owner reward is−K, its Continue payoff is Sy, and opponents' Continue
mass is zero; every floor excess is K+Sy>0.

No asymmetric-grand symmetry is assumed for the other owners. For owner2
and (x,y,z)=(q3,q0,q1), the three differences are

    d3=(1−y)(1/2+z/2)−(K+3)yz,
    d0=(1−z)[−K+(K+1)x]+z[−K−V+Vx],
    d1=2−(K+S+2)x−2y+(S+1)xy.                             (18)

The bound x≤2/(K+1) when z>0 still makes d0<0 because K>4.
The same contradiction and classification as (16) follow, with owner
floor K+Vx. For owner3 and (x,y,z)=(q2,q0,q1), the differences are

    d2=(1−z)[1−(K+V+1)y]−(K+2)yz,
    d0=(1−z)(2−x)−Kxz,
    d1=−K−Sx+(K+1)y+(S−K−2)xy.                            (19)

The same implications as (17) hold, giving owner floor K+Sy.

All smaller free-player selections accepted with fixed-outsider no-join
signs extend by Continue outsiders to these full induced Nash sets.
Thus no singleton-owner punishment compiler passes. Its all-Never variant
also requires nonpositive own singleton, whereas every own singleton is1.

No full zero-tail one-shot Nash root has a sure quitter: its other coordinates
would lie in one of the sets above, where that owner strictly benefits
from Continue. Hence no pair/triple persistent-base and free-player
selection can satisfy the combined induced Nash, base leave and outsider
join screens either. Those screens together imply just such a full root.
This excludes the whole existential selection, not only pure base points.
It does not exclude proper stationary equilibria.

### Scheduled, guarded and premium tests

All three pair partitions fail the joining-cap sources:01|23 has
r_0(03)=2>1;02|13 has negative participant reward−K;03|12 has
r_0(01)=5>1. In the signed-inverse-column test all column signs must
be positive because Gamma inverse is positive;01|23 has forbidden
K_1=S−1>0,03|12 has K_0=V−1>0, and02|13 has negative participant
premiums. Thus that source cannot select another partition or column sign.

Every guarded lower face fails under all relabelings: a nonfavorite partner
exposes the negative favorite outsider axis at small hazards; a favorite
partner exposes the sure harmful outsider with pair reward−K. The four
premium pairs01,12,23,03 overlap, the greatest premium core is all four,
and the grand protected set is empty. Product-low fails at01. The positive
singleton graph is two transpositions, not a favorable three- or four-cycle.
These exclude the corresponding inspected lower-guard, disjoint-trap,
small-premium-core, protected-set and favorable-cycle raw screens.

These are bounded comparisons against named input conditions, not an
exhaustive novelty theorem. Earlier qualitative stationary or periodic
implicit-function neighborhoods have unspecified radii; different centers
do not prove disjointness from them. No stationary nonexistence, fixed-period
completeness or unrestricted counterexample is asserted.

## Source correspondence and Lean handoff

The source-to-consumer chain uses tracked declarations under their imports:

- `Math.Topology.exists_rectangular_zero_of_strict_face_signs` in
  `MathUE/Topology/RectangularPoincareMiranda.lean` produces the two-variable
  zero. A coordinatewise clamped extension of the field gives global
  continuity if required; the displayed rational denominators stay positive.
- The literal endpoint definitions and mixture identities are in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`.
- `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
  `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
  in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` consume
  actual policy recursion, exact `IsεQuittingRootNash` with error0, and
  playerwise opponent-cycle contraction. Equations (4)–(14) produce all
  these inputs without any strategy-class restriction on deviations.

The mathematical implementation tasks are the raw family (1)–(3), scalar
elimination (4)–(7), rectangle and face estimates (8)–(11), the eight
barrier endpoint estimates (12), and the direct periodic compiler instance.
The two-coordinate zero must first be turned into all eight owner
equalities; a compiler enumerating one active slot per field coordinate
is not by itself a two-to-eight adapter. The theorem quantifies every
finite raw reward table with these displayed conditions, then produces
its hazards, exact terminal equilibrium and fixed uniform payoff.

Relevant bounded comparison declarations are:

- `pairedSingletonMatrix_standardQ`, `pairedSingletonMatrix_noHomogeneous`
  and `pairedSingletonMatrix_normalCore_eq_univ` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean`;
- `pairedSingletonMatrix_not_projectiveQBar` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`;
- `exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse` in
  `UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`;
- `r0Degree_eq_sign_det_of_nonnegative_inverse` in
  `MathUE/LinearProgramming/NonnegativeInverseDegree.lean`;
- `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`;
- `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`;
- `CappedClockParentRewardCertificate` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`;
- `WithdrawalFutureJoinKind.gain` and `WithdrawalFutureJoinRewardCertificate`
  in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`;
- `DeadlineWithdrawalRewardCertificate`, `deadlineWithdrawalGainFloor` and
  `deadlineWithdrawalZeroFloor_le_zero` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRaw.lean`;
- `deadlineSecurityGainFloorWithRestart` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRestartPointwiseCore.lean`;
- `patientWithdrawalFloor_le_ownNeverAlternative` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalRaw.lean`;
- `deadlineWithdrawalSecurityValue_le_singleton` and
  `deadlineWithdrawalSecurityFloor` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`;
- `deadlineSecurityGainFloor` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityMixedPointwise.lean`;
- `QuittingInducedOwnerChamber`, `QuittingInducedOwnerNeverChamber` in
  `UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`;
- `quittingSingletonBaseOwnerFloorExcess_nonpos_iff` and
  `nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
- `nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
  `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`;
- `QuittingHalfWeakPolynomialGuards` in
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`;
- `QuittingOneSidedWeakUnitGuards` in
  `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.

The new reward-family producer remains ordinary mathematics. The named
declarations establish exact source/consumer correspondence and delimit
compared inputs; they do not confer a Lean trust seal on this construction.

## What is removed and what remains

The argument needs neither a nonsingular rate Jacobian nor a small
reward perturbation. Passive scheduled rewards may be arbitrarily large,
and all triple own-recipient rewards are accepted if the four negative
barriers pay their inactive effect. This is an unbounded reward-region
producer, not a resolution of source-chronology cap leakage.

Arbitrary tables need not have the exact paired/half-turn owner elimination
or selectable sufficiently negative barrier rewards. Those are game-data
restrictions, not dispensable certificate conditions. No solved-game-or-
barrier disjunction, inactive-wall handoff, or arbitrary-table producer
is supplied by this theorem.
