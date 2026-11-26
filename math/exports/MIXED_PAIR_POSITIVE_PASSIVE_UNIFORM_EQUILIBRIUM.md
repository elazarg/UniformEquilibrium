# A mixed-premium pair funded by a positive passive reward

This is a complete raw reward-class producer in ordinary mathematics. It treats
a pair whose two joining gaps have opposite strict signs and permits both
complementary passive pair rewards to be positive, with one unbounded uniformly
in the other. No minimum, selected root, strategy or continuation is an input.
The general Fin4 conjecture remains open; no new Lean verification is claimed.

## 1. Finite raw class

There are four players. Nonempty quitter coalition A absorbs at the finite
original reward vector r(A). Live dates and Never pay zero. Put
s_i=r_i({i}) and Z_i(A)=r_i(A)-s_i for nonempty A only. The own levels s_i
may be arbitrary signed finite numbers. Define Gamma_ij=Z_i({j}) and
J_ij=Z_i({i,j}) for i!=j, with zero diagonals.

The following singleton and participant comparisons are used:

    Gamma_02=-b_2, Gamma_03=-b_3,
    Gamma_20=-d_2, Gamma_30=-d_3,
    Gamma_23=a_2,  Gamma_32=a_3,
    b_2,b_3,d_2,d_3,a_2,a_3>0;

    p_2=J_23>a_2,       0<p_3=J_32<a_3;
    c_i=p_i-a_i,       rho_i=d_i/a_i, i=2,3;
    J_02,J_03,J_12,J_13,J_20<0;
    J_30<c_3*rho_3.                                  (1)

Thus c_2>0 and c_3<0. The final inequality is a strict raw comparison;
in particular J_30<0. Set

    g_10=Gamma_10>0, g_12=Gamma_12<0, g_13=Gamma_13<0,
    T_0=g_10+g_12*rho_3+g_13*rho_2>0,
    K_0=Z_0(23), K_1=Z_1(23)>=0, Pi_1=J_10.

The two higher participant caps actually used by the schedule are

    Z_0(023)<=0, Z_1(123)<=0.                         (2)

All unlisted coordinates are arbitrary finite numbers. In particular the
additional matching-anchor caps on Z_0(012),Z_0(013),Z_0(0123) and the
anchor inequality J_01<=0 are unnecessary for this producer. They may be
imposed to obtain a subclass of the matching-anchor region with those two caps removed.

Here is a completely explicit threshold for K_0. Define positive constants

    C_i=[3*rho_i*(d_i+p_i)+9*abs(c_i)*rho_i^2]/a_i,
    Dmax=1+3*rho_2+3*rho_3+9*rho_2*rho_3,
    beta=T_0/(2*Dmax),
    E=abs(g_12)*C_3+abs(g_13)*C_2,
    eta=c_3*rho_3-J_30>0,
    Pplus=max(Pi_1,0),

    u_0=min(1/2,
      a_2/[4*(d_2+p_2)], a_3/[4*(d_3+p_3)],
      a_2^2/[16*abs(c_2)*d_2], a_3^2/[16*abs(c_3)*d_3],
      T_0/[2*(E+1)], beta/[4*(Pplus+1)],
      eta/[2*(1+abs(c_3)*C_3)])>0.                    (3)

For 0<u<=u_0 put

    B_i(u)=a_i-u*(d_i+p_i),
    Delta_i(u)=B_i(u)^2-4*c_i*u*d_i,
    Y_i(u)=2*u*d_i/[B_i(u)+sqrt(Delta_i(u))],
    Kcrit=b_2/Y_2(u_0)+b_3/Y_3(u_0).                  (4)

All square roots and denominators are strictly positive, as proved below.
The last hypothesis is simply

    K_0>Kcrit.                                        (5)

In particular K_0>0. The threshold depends on the listed singleton and
participant inputs, but is independent of K_1 over its entire nonnegative
half-line, and independent of every unlisted reward.

**Theorem.** Every original table satisfying (1)--(5) has an exact
absorbing terminal Nash profile against every unilateral complete behavioral
replacement. It has period two: solo0, then joint23, with independent proper
hazards at the designated phases; owner1 is Never. Every deleted-opponent
family absorbs geometrically. One fixed phase payoff is a uniform-equilibrium
payoff, with the same profile at every accuracy and all sufficiently long
finite horizons. All signed original own levels are allowed.

## 2. The two branches and a raw scalar producer

Write B_i=B_i(u). The explicit bounds give

    B_i>=3*a_i/4,
    4*abs(c_i)*u*d_i<=a_i^2/4,
    Delta_i>=5*a_i^2/16>0,
    Delta_i<=5*a_i^2/4.

The formula Y_i is positive, solves

    c_i*Y_i^2+[u*(d_i+p_i)-a_i]*Y_i+u*d_i=0,          (6)

and satisfies

    4*rho_i*u/5 < Y_i < 3*rho_i*u.                   (7)

For the lower bound its denominator is at most
a_i+sqrt(5)*a_i/2<5*a_i/2. For the upper bound the denominator is at
least 3*a_i/4. These arguments do not require c_i>0. For c_2>0 the
formula is the smaller of the two positive roots; for c_3<0 it is the
unique positive root. In either case

    2*c_i*Y_i+u*(d_i+p_i)-a_i=-sqrt(Delta_i),
    Y_i'(u)=[d_i+(d_i+p_i)*Y_i]/sqrt(Delta_i)>0.       (8)

Consequently K(u)=b_2/Y_2(u)+b_3/Y_3(u) is continuous and strictly
decreasing on (0,u_0], and tends to infinity at zero. Condition (5)
therefore produces a unique u in (0,u_0) with K(u)=K_0. No selected
solution is assumed in the theorem.

Let R_i=Y_i/u. Dividing (6) by a_i*u and using (7) gives

    abs(R_i-rho_i)
      =u*abs((d_i+p_i)*R_i+c_i*R_i^2)/a_i
      <=C_i*u.                                      (9)

Set X_2=Y_3(u), X_3=Y_2(u), and q_i=X_i/(1+X_i) for i=2,3.
All three hazards u,q_2,q_3 belong to (0,1). The index swap is deliberate:
Y_i is the odds of the opponent of owner i in the joint phase.

At phase A only owner0 uses hazard u. At phase B owners2,3 independently
use q_2,q_3. Others Continue. Repeat A,B forever. This is an actual
independent private stopping-law profile on the original calendar.

## 3. Observer payoff and every action endpoint

Define the native observer values

    B=[g_10+g_12*R_3+g_13*R_2+K_1*u*R_2*R_3]
        /[1+R_2+R_3+u*R_2*R_3],
    A=g_10*u+(1-u)*B.                                (10)

The numerator of B is at least T_0-E*u>T_0/2, because K_1>=0;
its denominator is at most Dmax. Hence

    B>beta, A>beta/2, Pi_1*u<beta/4.                  (11)

The second inequality uses g_10>0 and u<1/2. The third uses the bound
in (3) and is valid for either sign of Pi_1.

Writing H=(1-q_2)*(1-q_3), direct multiplication proves

    A=g_10*u+(1-u)*B,
    B=g_12*q_2*(1-q_3)+g_13*q_3*(1-q_2)
        +K_1*q_2*q_3+H*A.                            (12)

The proposed native phase values are

    V^A=(0,A,c_2*Y_2,c_3*Y_3),
    V^B=(0,B,p_2*q_3,p_3*q_2).                       (13)

The original values are s+V^A and s+V^B. Each Continue endpoint below
uses the next phase value.

Owner0 at A is indifferent between own Quit0 and the next value0.
At B, its Continue endpoint is

    -b_2*q_2*(1-q_3)-b_3*q_3*(1-q_2)+K_0*q_2*q_3=0

by K_0=b_2/Y_2+b_3/Y_3. Its Quit endpoint is

    J_02*q_2*(1-q_3)+J_03*q_3*(1-q_2)+Z_0(023)*q_2*q_3<0.

Owner1 at A has Continue value A>beta/2 and Quit value Pi_1*u<beta/4.
At B its Continue value is B>beta and its Quit value

    J_12*q_2*(1-q_3)+J_13*q_3*(1-q_2)+Z_1(123)*q_2*q_3<0.

For i=2,3, let j be its joint partner. At B the Quit value is p_i*q_j;
the Continue value is a_i*q_j+(1-q_j)*c_i*Y_i=p_i*q_j. At A,

    -d_i*u+(1-u)*p_i*q_j=c_i*Y_i                      (14)

is exactly (6). Owner2's Quit value is J_20*u<0, while its Continue
value c_2*Y_2 is positive. Owner3's Continue value can be negative, so
its comparison must be retained. Equation (9) and (3) give

    c_3*Y_3/u >= c_3*rho_3-abs(c_3)*C_3*u
                 > c_3*rho_3-eta/2
                 = J_30+eta/2 > J_30.               (15)

Thus its Continue value strictly exceeds its Quit value J_30*u.
All sixteen forced-action endpoints and all phase policy equations have
now been verified. The negative owner3 value at phase A is intentional;
discarding that endpoint would invalidate this mixed-sign extension.

## 4. Full behavioral deviations and one uniform target

The opponent survival products per cycle, deleting owners0,1,2,3
respectively, are

    (1-q_2)*(1-q_3),
    (1-u)*(1-q_2)*(1-q_3),
    (1-u)*(1-q_3),
    (1-u)*(1-q_2).                                   (16)

All are strictly less than one. Iterating the exact policy equations
identifies (13) with actual terminal values: any bounded terminal remainder
is multiplied by the joint geometric survival factor. For a replacement
behavioral strategy, condition on each live history and apply the two
endpoint inequalities above. Iteration bounds every replacement payoff
by the phase value plus a bounded remainder times the corresponding
factor in (16) to the number of complete cycles. The remainder vanishes
uniformly over the replacement.

This proves the entire cap: all finite deadlines, Never, arbitrary private
mixtures, and equivalently every complete behavioral replacement. Each
opponent absorption time has a geometric tail independent of the deviator.
Thus its expected value is finite uniformly over replacements, and the
difference between terminal and N-stage average payoffs is bounded by a
fixed constant/N. The prescribed play has the same property. Taking
s+V^A as one fixed target proves the uniform claim with this same profile.

The row offsets s_i are legitimate even when signed: opponents absorb
almost surely under every unilateral replacement. Every terminal response
therefore receives exactly the same offset. No affine transformation of
the live or Never payoff has been used.

The tracked semantic compiler has exactly these hypotheses:
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`. Its source
was inspected; no Lean build or formalization of this raw producer is
claimed.

## 5. A nonempty family with actual zero-root inertia

The following complete calibration is useful for comparison. Fix any finite
M>=200 and N>=0. Let Gamma have favorite entries3 within01 and23 and
all cross entries-1. Define

    L=[[0,-4,-1,9/10],[-4,0,9/10,-1],
       [9/10,-1,0,1],[-1,9/10,-2,0]],
    J=Gamma+L.

For each receiver i define F_i on subsets of the other three owners by:
F_i(empty)=0, F_i({j})=Gamma_ij, every two-element F_i=-1 except
F_0(23)=M and F_1(23)=N, and every three-element F_i=-1. For nonempty A,
write B=A minus{i} and prescribe

    Z_i(A)=F_i(B)+1_(i in A)*[
       sum_(j in B)L_ij
       -(M+1)*1_(i=0 and {2,3} subset B)
       -(N+1)*1_(i=1 and {2,3} subset B)].             (17)

These disjoint rules specify all sixty entries. Set original r_i(A)=1+Z_i(A).
The parameters are

    a_2=a_3=3, b_2=b_3=d_2=d_3=1,
    p_2=4, p_3=1, J_30=-2, Pi_1=-1,
    g_10=3, g_12=g_13=-1, K_0=M, K_1=N.

Consequently rho_i=1/3, C_2=2, C_3=4/3, T_0=7/3, Dmax=4,
beta=7/24, E=10/3, eta=4/3 and u_0=7/96. By (7),

    Kcrit < (5/(4*u_0))*(b_2/rho_2+b_3/rho_3)=720/7<200.

All required participant signs and caps are strict. In particular the
five matching-anchor participant caps are

    Z_0(012)=-6, Z_0(013)=-41/10, Z_0(023)=-11/10,
    Z_0(0123)=-M-61/10, Z_1(123)=-11/10.

Both removed passive caps fail whenever N>0. There are no imposed
equalities in the raw theorem; strict instances with N>0 have an open
neighborhood in all sixty reward coordinates.

For arbitrary hazards q, the actual zero-input joining polynomial is

    Delta_0(q)=(Lq)_0-(M+1)*q_2*q_3,
    Delta_1(q)=(Lq)_1-(N+1)*q_2*q_3,
    Delta_i(q)=(Lq)_i, i=2,3.                         (18)

Every reciprocal sum L_ij+L_ji is strictly negative, and every column
contains a positive entry. At a zero-input Nash root, q_i*Delta_i>=0
for every i, including sure hazards. Summing gives a strict negative
number whenever at least two owners have positive hazards, a contradiction.
If exactly one owner j moves, a positive entry in column j gives an
inactive owner with a profitable Quit, again a contradiction. Thus the
literal AllContinue point is the unique actual zero-input root, including
all boundary supports. This is a full-polynomial fact for (17), not an
inference from the singleton matrix alone. The produced periodic profile
nevertheless has exact terminal debt zero and absorbs surely.

## 6. Exact old-selection comparison

The only premium trap of (17) is23. Owners0,1 have strictly negative
nontrivial participant rewards everywhere, and both participants of23
receive positive native rewards4,1. Hence ProductLow fails at pure23.
The pair joining product is (4-3)*(1-3)=-2. The old mixed-premium-trap
theorem, including its weak nonnegative product boundary, does not apply.
For any positive weights on trap23, its inserted singleton0 floor is
lambda_2*J_20+lambda_3*J_30=-lambda_2/10-2*lambda_3<0;
the weighted-floor-return criterion for that trap also fails.

The earlier positive-passive joint-pair/solo producer requires both
scheduled participant rewards to exceed their positive singleton rewards.
The only possible scheduled pair in this calibration is23, and its owner3
violates that hypothesis. Pair01 has negative participant rewards; all
cross pairs have negative singleton entries and negative participant
rewards. This excludes every relabeling of that particular raw producer.
The same all-participant-positive, strictly positive joining-gap requirement
excludes every partition in the two-pair positive inverse-cone producer.

The previous matching-anchor theorem requires both complementary passive
pair rewards nonpositive. Its sole premium trap must be23 here, hence the
anchor is01, and for M,N>0 both required caps fail in either anchor order.
Changing which favorite matching is declared cannot repair this: the strict
positive singleton entries determine the matching uniquely.

The stronger ordered nonpositive-anchor-block criterion also fails for
EVERY marked set, EVERY ordered partition into blocks, and EVERY strictly
positive block weight choice when N>0. If the marked set C meets23, take
coalition A=23 and its first intersected block. Every marked participant
appearing in that block receives either4 or1, so its positively weighted
participant sum is strictly positive. If instead C is a nonempty subset
of01, then23 is contained in its unmarked complement. The passive reward
at23 of every marked owner is M>0 or N>0, contrary to its passive cap.
This covers all149 ordered-partition/subset choices, without restricting
their weights or invoking a numerical LP. The N=0 boundary is not used
for this separation claim. This comparison uses the two literal admission
inequalities of the ordered-block criterion; its independent proof
is not assumed by the present construction.

### All fourteen quiet children

For a proper child C and outsider o, a nonnegative full clock weight vector
lambda must satisfy the literal singleton rows

    sum_(i in C)lambda_i*(-Gamma_ij)>=-Gamma_oj,
    sum_(i in C)lambda_i*L_ij>=L_oj,   j in C.         (19)

The first is its future row and the second its joining row. They are
necessary even if every other row of the clock certificate is discarded.
The following choices (C,o,j) have L_oj=9/10>0 and L_ij<=0 for every
i in C, immediately contradicting the second inequality:

    (0,2,0), (1,3,1), (2,1,2), (3,0,3),
    (01,2,0), (02,1,2), (03,2,0), (12,3,1),
    (13,0,3), (23,1,2), (012,3,1), (013,2,0), (023,1,2).

For the remaining child C=123 and o=0, add its two future rows j=2,3
and twice its joining row j=3. The resulting left coefficients, in
child order1,2,3, are (0,-1,-3), while the right side is19/5>0.
This excludes every nonnegative weight vector. The calculation uses only
the singleton entries and singleton joining rows, which (17) retains
exactly. It therefore excludes the whole fourteen-child capped-clock LP,
not merely a favored weight or stationary continuation. The relaxation
with nonnegative singleton payoffs changes only the Never row and fails
these same inequalities.

The inspected interfaces are `rawChild_future_delta`,
`rawChild_future_base`, `rawChild_joining_delta`, `rawChild_joining_base`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockOriginalCoalitionRows.lean`
and `nonempty_cappedClockParentRewardCertificate_iff` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockExactLPAlternative.lean`.

### Entire sure-owner Nash families, including every punishment tail

At a designated sure owner k, the complementary induced game has the
joining polynomials (18), with q_k=1. An opponent with strictly positive
gap must Quit surely; one with strictly negative gap must Continue.
The entire four induced Nash correspondences are as follows:

    owner0: (1,0,1,0);
    owner1: (0,1,t,1), 0<=t<=9/20;
    owner2: (0,1,1,0);
    owner3: (0,0,1,1).                               (20)

Here are complete eliminations, rather than only a list of candidate
points. With q0=1, Delta1=-4+(9/10)q2-q3-(N+1)q2q3<0, so q1=0.
Then Delta2=9/10+q3>0 forces q2=1, and Delta3=-3 forces q3=0.
With q1=1, Delta0=-4-q2+(9/10)q3-(M+1)q2q3<0, so q0=0.
If q3<1 then Delta2=-1+q3<0 gives q2=0, which forces q3=1 from
Delta3=9/10; this is a contradiction. Thus q3=1, Delta2=0, and
Delta3=9/10-2q2>=0 is precisely 0<=q2<=9/20.
With q2=1, Delta0=-4q1-1-(M+1/10)q3<0, so q0=0.
Then Delta3=(9/10)q1-2<0 gives q3=0, and Delta1=9/10 forces q1=1.
With q3=1, Delta1=-4q0-1-(N+1/10)q2<0 gives q1=0.
Then Delta2=(9/10)q0+1>0 forces q2=1, and Delta0=-M-11/10<0
forces q0=0. These arguments include all boundary hazards and intervals.

Each induced root has another sure owner. The forced owner's joining gap
at these families is respectively

    -1, -1-(N+1/10)t, -1, -2.                        (21)

Thus Continue exceeds Quit by at least1 for that owner, regardless of any
punishment tail: the probability that every other owner Continues is zero.
This excludes every tail choice in the singleton and persistent-base
punishment consumers, not merely stationary repetition. The relevant
inspected declarations are `quittingSingletonBaseOwnerFloorExcess_nonpos_iff`
and `nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`,
and `nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
It also excludes the sure-owner and sure-owner-Never chamber admissions in
`UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`.

### Weight, singleton and finite phase families

The coalition01 vector is (-1,-1,-1,-1). Hence every nonzero nonnegative
global or proper passive-ledger weight fails on that coalition. The proper
trap23 also defeats every proper-flat two-ledger premise. The two global
inserted singleton rows at0 and1 sum to (-1,-1,-21/10,-21/10), excluding
every nonzero nonnegative global floor weight. The native singleton columns
sum to (1,1,1,1), excluding every nonzero nonnegative global upper weight.
Every player has negative cross participant premiums, so the protected set
is empty: common-leaver and support-specific-leaver criteria fail. The
greatest-premium-core-at-most-two theorem requires all participant premiums
nonnegative, and the mixed-sign triple-core theorem requires core size3;
both respective premises fail. These are distinct from merely counting
players with some positive reward.

Every reciprocal singleton product is positive. Thus there is no directed
escort edge Gamma_ij<=0<=Gamma_ji between distinct owners, including in
any principal restriction. This defeats
`BalancedSingletonCycleCertificate.exists_escortCycle` in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`.
Mutual negative cross pairs defeat the no-mutually-negative-pair class.
The positive singleton graph consists of two disjoint two-cycles; it has
no positive directed triple or Hamiltonian singleton cycle.

The cross principal matrix [[0,-1],[-1,0]] is not standard Q: its residual
at offset(-1,-1) is always strictly negative. It also has no nonzero
homogeneous solution, since x>=0 and (-x1,-x0)>=0 imply x=0. Thus it is
not projective Q, and Gamma is not projective Q-bar, using both branches
of `isProjectiveQMatrix_iff_standard_or_homogeneous` and the definition
`IsProjectiveQBarMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.
The full determinant is45 and its inverse is strictly positive, so the
negative-determinant inverse entrance does not apply. Each proper triple
has an unmatched row with both offdiagonal entries negative; no such
triple maps a nonnegative vector to a strictly positive vector. In
particular there is no positive-inverse proper child.

Every pair has at least one strictly negative joining gap. Therefore
every partition fails the necessary scheduled-owner comparison in the
two-pair joining-cap, crossed-matching, signed-inverse-column,
nonmatching-positive-passive, and bounded-inverse-corners producers. The
signed inverse-column choice is forced positive here by Gamma inverse
positivity; it cannot reverse the failed comparison. Every cross pair
has opposite joining signs, excluding the both-below negative-pair and
below-singleton two-joint phase families. Neither favorite pair has both
joining gaps positive, excluding the older funded-pair and global
asymmetric favorite-pair families under every labeling.

The low-passive friendly-pair scalar class requires a common normalized
participant value on all favorite coordinates. Here those values are
(-1,-1,4,1); the identical singleton rows fix identical normalization
scales. Its premise fails. The four-joint-phase center and rectangle
families require both favorite participants to be above their passive
favorite singleton; that fails already. The literal four-singleton-phase
favorite-pair cap is original reward at most (5+sqrt(5))/2<4; original
owner2 payoff5 at23 fails it in either favorite orientation. No triple
has all six joining gaps positive, excluding the triple collision box.
These comparisons concern the displayed raw classes; they are not a
classification of all finite schedules or an assertion about an
unspecified older perturbation neighborhood.

The one-negative-pair/two-solo families, their arbitrary-premium extensions,
and the three-owner positive-passive-triple producer all require a
reciprocal-opposite singleton pair in their literal singleton patterns.
There is none here. The exact passive-cap families with negative favorite
participants cannot fit the positive23 row. Earlier full-zero source
exclusions may apply to Gamma,J; they are not global UE existence theorems
and are not counted as missing this source.

### All twenty-four passive-pole roles and the unbounded-family caveat

The exact coefficient-sign census tests every role assignment on the entire
M>=200,N>=0 family. Exactly one assignment passes all eight strict endpoint
guards of the three-passive-poles theorem:

    (old0,old1,old2,old3)=(1,3,0,2).

Its c is9/40 and its remaining six guard values are

    (a2,b2,l0,l1,f0,f1)
       =(-1,-5,-89/40,-53/40,3519/16000,-319/400).     (22)

Passing these guards does not establish membership in that theorem's
input-dependent eventual ray. Under this role assignment its two required
negative passive poles are original rewards r3(01)=0 and r0(23)=1+M;
the third, nonnegative-slope pole is r2(13)=0. Along M tending to infinity
with N=1, one required negative pole instead tends to positive infinity
and the other stays fixed. This whole ray is not supplied by the old
fixed-background negative-pole asymptotic schema. No isolated-table
nonmembership is inferred from its unspecified threshold.

The same family-level qualification applies to participant-jackpot and
signed-passive-coalition asymptotic schemas: the increasing passive
coordinate M is linked here to a decreasing participant grand coordinate
-M-61/10. Neither is a fixed bounded completion for the other's growth
direction. Allowing the old bounded-background constant to grow with M
provides no diagonal guarantee. This is an exact distinction between
quantified families, not a claim about every unknown finite threshold.

## 7. A necessary restriction of this schedule

The new phase-A condition on owner3 is substantive. In the calibration,
change only its participant reward J_30 from-2 to-1/10. All six relevant
singleton signs, mixed joint rewards, positive passive coordinates and
higher queried caps remain. In the produced small-root schedule, however,

    (Continue_3 at A)/u=c_3*Y_3(u)/u -> -2/3,
    (Quit_3 at A)/u=J_30=-1/10.

As K_0 tends to infinity, the unique produced u tends to zero. Hence for
all sufficiently large K_0 that owner strictly prefers Quit at phase A.
The two indifference equations and the passive funding equation alone do
not produce an equilibrium. The explicit condition and margin (15) are
needed. This falsifies removal of that condition from this schedule, not
existence of equilibrium for the modified game by another strategy.

## 8. Exact reproduction

Save the following block as a Python file and run it with Python and SymPy.
It reconstructs all sixty coordinates, exact joining polynomials, threshold
constants and all sixteen literal phase endpoints. Policy equalities are
reduced modulo the two quadratic equations and the K0 equation, with M,N
symbolic. It additionally checks all fourteen quiet Farkas rows, the four
analytically exhaustive sure-owner family formulas, all149 ordered-block
admissions for N>0, trap/weight and matrix/pair screens, and every passive-pole
role uniformly in M,N by exact polynomial-coefficient signs after M=200+m,N=n.
No floating point or bounded root search is used. The full behavioral and
horizon statements follow from Section4, not a finite deadline sample.

```python
"""Exact full60 and phase-polynomial checks for a mixed-premium producer.

Run with Python/SymPy. All arithmetic and sign certificates are exact.
No Lean claim and no exclusion of all possible equilibrium architectures.
"""
from itertools import combinations, permutations, product
import sympy as s

R = s.Rational
I = tuple(range(4))
COAL = tuple(A for n in range(1, 5) for A in combinations(I, n))
M, N = s.symbols('M N', positive=True)
G = s.Matrix([[0, 3, -1, -1], [3, 0, -1, -1],
              [-1, -1, 0, 3], [-1, -1, 3, 0]])
L = s.Matrix([[0, -4, -1, R(9, 10)], [-4, 0, R(9, 10), -1],
              [R(9, 10), -1, 0, 1], [-1, R(9, 10), -2, 0]])
J = G+L


def native(i, A):
    A = tuple(sorted(set(A)))
    B = tuple(j for j in A if j != i)
    if not B:
        passive = s.S.Zero
    elif len(B) == 1:
        passive = G[i, B[0]]
    elif B == (2, 3) and i in (0, 1):
        passive = (M, N)[i]
    else:
        passive = -s.S.One
    if i not in A:
        return passive
    correction = (M+1 if i == 0 else N+1 if i == 1 else 0)
    return passive+sum(L[i, j] for j in B)-correction*int({2, 3} <= set(B))


def joining(i, A):
    return native(i, set(A) | {i})-native(i, A)


TABLE = {A: tuple(native(i, A) for i in I) for A in COAL}
assert len(TABLE)*4 == 60
assert all(native(i, [i]) == 0 for i in I)
CAPS = [(0, (0, 1, 2)), (0, (0, 1, 3)), (0, (0, 2, 3)),
        (0, I), (1, (1, 2, 3))]
assert [native(i, A) for i, A in CAPS] == [
    -6, -R(41, 10), -R(11, 10), -M-R(61, 10), -R(11, 10)]
assert native(0, [2, 3]) == M and native(1, [2, 3]) == N
assert J[2, 3] == 4 and J[3, 2] == 1
assert J[3, 0] == -2 < -R(2, 3)

rho = R(1, 3)
C2, C3 = R(2), R(4, 3)
T0, Dmax, beta, E, eta = R(7, 3), R(4), R(7, 24), R(10, 3), R(4, 3)
u0 = min(R(1, 2), R(3, 20), R(3, 8), R(9, 16), R(9, 32),
         T0/(2*(E+1)), beta/4, eta/(2*(1+2*C3)))
assert u0 == R(7, 96)
assert 5/(4*u0)*(2/rho) == R(720, 7) < 200

q = s.symbols('q0:4')
gaps = L*s.Matrix(q)-s.Matrix([(M+1)*q[2]*q[3], (N+1)*q[2]*q[3], 0, 0])
for i in I:
    opponents = tuple(j for j in I if j != i)
    derived = 0
    for bits in product((0, 1), repeat=3):
        A = tuple(j for j, bit in zip(opponents, bits) if bit)
        probability = s.prod(q[j] if bit else 1-q[j]
                             for j, bit in zip(opponents, bits))
        derived += probability*joining(i, A)
    assert s.expand(derived-gaps[i]) == 0
assert all(L[i, j]+L[j, i] < 0 for i, j in combinations(I, 2))
assert all(any(L[i, j] > 0 for i in I) for j in I)

# Literal enumeration of all16 phase endpoints, reduced modulo the three
# exact root identities. M and N remain symbols: this tests the whole family.
u, y2, y3 = s.symbols('u y2 y3')
x2, x3 = y3, y2
q2, q3 = x2/(1+x2), x3/(1+x3)
B = (3*u-y2-y3+N*y2*y3)/(u+y2+y3+y2*y3)
A = 3*u+(1-u)*B
values = [s.Matrix([0, A, y2, -2*y3]), s.Matrix([0, B, 4*q3, q2])]
hazards = [s.Matrix([u, 0, 0, 0]), s.Matrix([0, 0, q2, q3])]
ideal = s.groebner([y2**2+(5*u-3)*y2+u,
                   -2*y3**2+(2*u-3)*y3+u,
                   M*y2*y3-y2-y3], M, u, y2, y3, domain=s.QQ.frac_field(N))


def zero_mod(expr):
    numerator = s.cancel(expr).as_numer_denom()[0]
    return ideal.reduce(numerator)[1] == 0


ENDPOINTS = []
for phase in (0, 1):
    following = values[1-phase]
    for i in I:
        quit_value, continue_value = 0, 0
        opponents = tuple(j for j in I if j != i)
        for bits in product((0, 1), repeat=3):
            coalition = tuple(j for j, bit in zip(opponents, bits) if bit)
            probability = s.prod(hazards[phase][j] if bit else 1-hazards[phase][j]
                                 for j, bit in zip(opponents, bits))
            quit_value += probability*native(i, set(coalition) | {i})
            continue_value += probability*(native(i, coalition) if coalition else following[i])
        quit_value, continue_value = s.cancel(quit_value), s.cancel(continue_value)
        assert zero_mod(continue_value-values[phase][i])
        if hazards[phase][i] != 0:
            assert zero_mod(quit_value-continue_value)
        ENDPOINTS.append((phase, i, quit_value, continue_value))
# Inactive endpoint signs are proved from the raw inequalities and bounds;
# these identities ensure that the literal table supplies exactly those tests.
assert ENDPOINTS[1][2] == -u
assert ENDPOINTS[2][2] == -u/10
assert ENDPOINTS[3][2] == -2*u
assert zero_mod(ENDPOINTS[4][2]-(-2*q2*(1-q3)-q3*(1-q2)/10-R(11, 10)*q2*q3))
assert zero_mod(ENDPOINTS[5][2]-(-q2*(1-q3)/10-2*q3*(1-q2)-R(11, 10)*q2*q3))
assert len(ENDPOINTS) == 8  # Two forced actions in each of these eight rows.

# All14 proper quiet children fail exact singleton joining/passive rows.
QUIET = []
for C in COAL:
    if len(C) == 4:
        continue
    if C == (1, 2, 3):
        o, terms = 0, [('F', 2, 1), ('F', 3, 1), ('J', 3, 2)]
    else:
        j, o = next((j, o) for j in C for o in I if o not in C
                    and L[o, j] > 0 and max(L[i, j] for i in C) <= 0)
        terms = [('J', j, 1)]
    coefficients = tuple(sum(w*(-G[i, j] if kind == 'F' else L[i, j])
                             for kind, j, w in terms) for i in C)
    rhs = sum(w*(-G[o, j] if kind == 'F' else L[o, j]) for kind, j, w in terms)
    assert max(coefficients) <= 0 and rhs > 0
    QUIET.append((C, o, terms, coefficients, rhs))
assert len(QUIET) == 14

# Exact complementary-root fibers, analytically exhausted in the note.
t = s.symbols('t', nonnegative=True)
FIBERS = [(1, 0, 1, 0), (0, 1, t, 1), (0, 1, 1, 0), (0, 0, 1, 1)]
FIBER_GAPS = [gaps.subs(dict(zip(q, v))) for v in FIBERS]
assert all(s.expand(FIBER_GAPS[i][i]-target) == 0
           for i, target in enumerate([-1, -1-(N+R(1, 10))*t, -1, -2]))
assert s.expand(FIBER_GAPS[1][0]-(-4-t+R(9, 10)-(M+1)*t)) == 0
assert FIBER_GAPS[1][2] == 0 and FIBER_GAPS[1][3] == R(9, 10)-2*t

# All coefficients after M=200+m, N=n must be nonnegative (or positive
# constant). This exact sufficient sign test is used only where it passes.
m, n = s.symbols('m n', nonnegative=True)


def positive_on_family(expr):
    pp = s.Poly(s.expand(expr.subs({M: 200+m, N: n})), m, n)
    return all(c >= 0 for c in pp.coeffs()) and pp.eval({m: 0, n: 0}) > 0


TRAPS = [C for C in COAL if all(any(i in A and set(A) <= set(C)
         and positive_on_family(native(i, A)) for A in COAL) for i in C)]
assert TRAPS == [(2, 3)]
assert L[2, 3]*L[3, 2] == -2
assert J[2, 0] < 0 and J[3, 0] < 0
assert TABLE[(0, 1)] == (-1, -1, -1, -1)
assert tuple(native(i, {0, i})+native(i, {1, i}) for i in I) == (
    -1, -1, -R(21, 10), -R(21, 10))
assert G*s.ones(4, 1) == s.ones(4, 1)
assert all(min(L[i, j], L[j, i]) < 0 for i, j in combinations(I, 2))
assert all(L[i, j]*L[j, i] < 0 for i, j in combinations(I, 2)
           if i//2 != j//2)
assert all(G[i, j]*G[j, i] > 0 for i, j in combinations(I, 2))
assert G.det() == 45 and min(G.inv()) > 0
for C in combinations(I, 3):
    assert any(all(G[i, j] < 0 for j in C if j != i) for i in C)

# All ordered nonempty marked-set/block choices fail for N>0, independently
# of positive block weights. No weight LP or bounded sampling is involved.
ordered_count = 0
for C in COAL:
    for number in range(1, len(C)+1):
        for labels in product(range(number), repeat=len(C)):
            if set(labels) != set(range(number)):
                continue
            blocks = [tuple(i for i, label in zip(C, labels) if label == k)
                      for k in range(number)]
            marked = set(C) & {2, 3}
            if marked:
                first = next(B for B in blocks if set(B) & {2, 3})
                assert all(native(i, [2, 3]) > 0 for i in first if i in (2, 3))
            else:
                assert set(C) <= {0, 1}
                assert all(native(i, [2, 3]) > 0 for i in C)  # N>0 here.
            ordered_count += 1
assert ordered_count == 149

# Old passive-pole endpoint census on the ENTIRE M>=200,N>=0 family.
# Passing endpoint guards alone do not establish an unspecified asymptotic
# threshold. The output preserves any such passing roles honestly.


def polynomial_sign(polynomial):
    if polynomial.is_zero:
        return 0
    coefficients = polynomial.coeffs()
    constant = polynomial.eval({m: 0, n: 0})
    if all(c >= 0 for c in coefficients) and constant > 0:
        return 1
    if all(c <= 0 for c in coefficients) and constant < 0:
        return -1
    raise AssertionError(('Sign not certified by coefficient test', polynomial))


def family_sign(expr):
    numerator, denominator = s.cancel(expr.subs({M: 200+m, N: n})).as_numer_denom()
    return polynomial_sign(s.Poly(numerator, m, n))*polynomial_sign(s.Poly(denominator, m, n))


POLES = []
POLE_DETAILS = []
for i, j, k, l in permutations(I):
    a, b = joining(i, [l]), joining(i, [k, l])
    if not (family_sign(a) == 1 and family_sign(b) == -1):
        continue
    c = a/(a-b)
    a2, b2 = joining(k, [l]), joining(k, [i, l])
    l0 = (1-c)*joining(j, [l])+c*joining(j, [k, l])
    l1 = (1-c)*joining(j, [i, l])+c*joining(j, [i, k, l])
    f0 = c*(c*native(l, [k, l])-native(l, [k]))
    f1 = (1-c)*joining(l, [i])+c*joining(l, [i, k])
    guards = tuple(s.cancel(g) for g in (a2, b2, l0, l1, f0, f1))
    signs = tuple(family_sign(g) for g in guards)
    POLE_DETAILS.append(((i, j, k, l), c, signs))
    if signs == (-1, -1, -1, -1, 1, -1):
        POLES.append(((i, j, k, l), c, guards))
assert [p[0] for p in POLES] == [(1, 3, 0, 2)]

if __name__ == '__main__':
    print('PASS: all60, raw threshold and five strict anchor participant caps.')
    print('PASS: literal polynomial zero-root inertia and all16 phase endpoint identities.')
    print('PASS: all14 quiet Farkas rows; four complete sure-owner fiber formulas.')
    print('PASS: sole opposite-sign trap23, floor return and positive-gap pair screens.')
    print('PASS: all149 ordered nonpositive-anchor block admissions excluded for N>0.')
    print('Table:', TABLE)
    print('Quiet rows:', QUIET)
    print('Sure-owner fiber gaps:', FIBER_GAPS)
    print('Old pole endpoint passing roles on the whole family:', POLES)
    print('All first-two-guard pole roles:', POLE_DETAILS)
```

## 9. Source correspondence and formalization handoff

The mathematical raw adapter consists of the literal centered coordinates,
the constants (3), both positive radical branches (4), the strictly monotone
scalar equation K(u)=K_0, and the two produced hazard/value vectors. Its
proof requires no game-theoretic source assumption or generic matrix guard.
The only exact equations to hand to the existing periodic compiler are the
two policy recursions and both-action Nash inequalities at each phase. The
four opponent-cycle products in (16) discharge its contraction hypothesis.

A formalization would first prove the signed quadratic branch estimates and
monotone scalar root existence, then construct these actual phase data from
an arbitrary raw input satisfying (1)--(5). Applying the two named existing
PeriodicCompiler declarations would yield the original-game conclusions.
Their validity as supplied-certificate consumers is not being presented as
an existing formal proof of this raw production theorem. No Lean code was
changed or built for this packet.

The calibration's complete joining-polynomial identity proves actual
zero-input inertia; the explicit periodic profile proves exact absorbing
terminal debt zero. Thus it supplies an honest equilibrium comparison, not
a claim that a virtual source or candidate counterexample has been realized.
The old-criterion comparisons distinguish finite raw selection failures from
the explicitly qualified asymptotic-family comparisons in Section6.
