# A ten-phase uniform equilibrium on a full reward cube

## 1. Complete raw class and statement

The four-player quitting game has independent private randomization, zero
live and Never payoffs, and absorbing rewards on nonempty coalitions. A
unilateral deviation may replace an entire behavioral strategy, without
memory, time or randomness restrictions.

Define the following60-coordinate real center Z, with recipients ordered
0,1,2,3:

| Coalition | Z(A) |
|---|---|
| 0 | (0,3,-1,-1) |
| 1 | (3,0,-1,-1) |
| 2 | (-1,-1,0,3) |
| 3 | (-1,-1,3,0) |
| 01 | (-1,-1,-1,-1) |
| 02 | (-2,-1,-1/10,-1) |
| 03 | (-1/10,-1,-1,-2) |
| 12 | (-1,-1/10,-2,-1) |
| 13 | (-1,-2,-1,-1/10) |
| 23 | (4,4,4,1) |
| 012 | (-6,-41/10,-11/10,-1) |
| 013 | (-41/10,-6,-1,-11/10) |
| 023 | (-11/10,-1,9/10,-4) |
| 123 | (-1,-11/10,-1,-21/10) |
| 0123 | (-101/10,-101/10,-1/10,-31/10) |

Put epsilon=1/1000000. Let W be ANY real reward table such that

    |W_i(A)-Z_i(A)|<=epsilon for every nonempty A != I,
    W_0(I)<=-101/10+epsilon,
    W_2(I)<=-1/10+epsilon.                              (1)

The two remaining grand-coalition rewards W_1(I),W_3(I) are arbitrary
finite real numbers. No restriction fixes any own singleton to zero, and
all56 non-grand coordinates may vary independently.

**Theorem.** Every table(1) admits a proper period-ten exact
terminal Nash profile against all behavioral replacements and one fixed
uniform-equilibrium payoff. In particular the displayed center game and every
table obtained by decreasing only its recipient0 grand reward by T>=0 have
such an equilibrium. Arbitrary signed recipient offsets and positive recipient
scales may subsequently be applied to every absorbing coordinate.

The chronological active supports, with the listed owners mixing and all
others Continuing, are

    02, 013, 123, 123, 123, 123, 123, 123, 13, 12.       (2)

The27 hazards are produced by a contraction. No strategy, continuation,
root or cycle witness is assumed from the input game. The game criterion
is the explicit box and one-sided inequalities(1), rather than existence
of an unspecified certificate.

## 2. The rational hazard center and exact equations

In phase order, and increasing owner order within each phase, use the
following EXACT decimal rationals as the center h*. They are not asserted
to solve the indifference equations exactly:

    02:  .6325497567632887, .08879557335326287
    013: .01698680638857422, .03227897357149102,
         .33108423804822423
    123: .06760992875293761, .02439015231250483,
         .3059328798073793
    123: .22380439946248434, .10848819936038465,
         .2451127758480039
    123: .31453288329789203, .1591852043042641,
         .21771744678665797
    123: .37459292405262073, .19205376846927352,
         .1977028589574382
    123: .415002872799142, .2100456245095365,
         .17331022480699212
    123: .4271990349355332, .20630519924427315,
         .13045585395902404
    13:  .6187739431193668, .05748712065185276
    12:  .05949182192737265, .6099345898764957.

Put r=1/10000 and let H be the closed sup-norm hazard cube of radius r
around h*. Every active hazard in H lies strictly between zero and one.
For any table W first satisfying the full60-coordinate cube
|W_i(A)-Z_i(A)|<=epsilon, and any h in H, let q_t be its four hazards at
phase t, filling inactive entries with zero. Define

    C_t=product_i(1-q_ti),
    E_t=sum_(A nonempty)Pr_qt(A) W(A),
    A_period=product_(t=0..9)C_t,
    V_t=[sum_(k=0..9)(product_(j<k)C_(t+j)) E_(t+k)]
                       /(1-A_period).                  (3)

Indices on phases are modulo10. This is the actual prescribed terminal
value because A_period<1 and all absorbing rewards are bounded.

For each phase/owner define the literal forced-Quit and passive Continue
contributions by summing over all coalitions B of its active opponents:

    Q_ti=sum_B Pr_qt,-i(B) W_i(B union{i}),
    P_ti=sum_(B nonempty)Pr_qt,-i(B) W_i(B),
    H_ti=product_(j!=i)(1-q_tj),
    g_ti=Q_ti-P_ti-H_ti V_(t+1,i).                       (4)

All simultaneous outcomes, including deviations creating the grand
coalition, are included. Let G be the27 components for active owners in
the same order as h; the other13 components are inactive gaps.

## 3. Exact finite certificate on the entire reward cube

The complete self-contained standard-library checker is the first
program in Section10.
It contains all60 center rewards, the27 rational hazard centers, and a
fixed27-by-27 rational matrix B whose entries have denominator10^10.
The matrix is a witness to the inequalities below; it is NOT assumed to
be the exact inverse of any Jacobian. Its numerical origin is irrelevant
to the exact checks.

The checker proves, uniformly for every h in H and every W in the full60
reward cube,

    ||I-B D_h G(h,W)||_infinity <1/5,                    (5)
    ||B G(h*,W)||_infinity <1/25000,                     (6)
    g_ti<-1/3 for all13 inactive phase/owner pairs,      (7)
    A_period<1/1000.                                    (8)

There is no sampling step. Every interval endpoint is an integer multiple
of10^-30. Addition is exact; multiplication rounds the minimum product
down and maximum product up; reciprocal reverses endpoints and rounds
outwards after checking that the interval avoids zero. A dual interval
carries all27 first derivatives; product and reciprocal rules enclose
the derivatives of the explicit rational formulas(3)--(4). Repeated reward
occurrences may be treated independently within their intervals, enlarging
the enclosure and therefore retaining validity. The denominator1-A_period
is positive throughout the hazard cube.

The program reconstructs all literal coalition expectations, forms(5)
by matrix multiplication on the interval Jacobian, and bounds its row
sums of absolute values. Equation(6) is evaluated at the rational center
h* over the ENTIRE reward cube. This includes both the residual of the
approximate hazard center and all permissible reward changes. Every final
comparison is an exact integer or Fraction comparison; no floating-point
operation or root solver is used in the durable certificate.

## 4. Contraction produces an exact proper equilibrium

For each fixed W in the full cube define T_W(h)=h-BG(h,W). By(5) it is a
contraction with Lipschitz constant at most1/5. Equations(5)--(6) give

    ||T_W(h)-h*||_infinity
      <=1/25000+r/5=3/50000 <r.

Thus T_W maps H strictly into itself. Banach's theorem supplies a unique
fixed point h(W) in H. To justify G(h(W),W)=0 without assuming B is an
inverse, choose any point in H. By(5), B D_hG there is invertible by the
Neumann-series criterion. Both factors are square, so B is invertible.
Therefore BG=0 at the fixed point implies G=0.

All active owners are exactly indifferent, all inactive owners strictly
prefer Continue by(7), and every hazard remains proper. The values in(3)
are actual payoffs and satisfy the cyclic Bellman equations by construction.
Consequently all40 phase/owner Nash comparisons hold, not merely those
observed at the numerical discovery point.

For the larger raw class(1), first choose a table Wbar in the full cube
which agrees with W at every non-grand coordinate. If i is0 or2, take
Wbar_i(I)=max(W_i(I),Z_i(I)-epsilon); this belongs to the cube by(1).
For i=1,3 take Wbar_i(I)=Z_i(I). Obtain the produced profile for Wbar.
No prescribed phase contains all four owners, so changing grand rewards
never changes its values. Only owner0, at a123 phase, and owner2, at the013
phase, can cause the grand coalition by a unilateral deviation. Returning
from Wbar to W only decreases those two Quit endpoints. The grand values
of owners1 and3 are never queried under prescription or unilateral
replacement. The same profile is therefore Nash for every table(1).

## 5. Complete behavioral responses, signed offsets, and fixed target

The period has strictly positive hazards for every owner. Deleting any
one owner still leaves positive opponent hazard in the period, giving a
strict opponent period-survival factor rho_i<1. The fixed opponents force
absorption geometrically under every unilateral behavioral replacement.

At each phase the Continue equality and Quit inequality allow a backward
induction for every finite deterministic quitting deadline. Literal Never
is priced by the same recurrence with a residual tending to zero under
rho_i^n. These deadline and Never values are all bounded by the current
V_ti. Before absorption the only public nonterminal history is repeated
Continue, so every unilateral behavioral replacement is a private stopping
law on those deadlines and Never, independent of the opponents' private
randomness. Averaging the inequalities covers all such replacements.

For any finite table satisfying(1), bound all absolute rewards by L. The
finite-stage average differs from terminal payoff in expectation by at most
2L times the opponent stopping date plus one, divided by the horizon. Its
expectation is finite, uniformly over the deviator, by the geometric tail.
Thus the same exact terminal profile supplies one fixed uniform-equilibrium
payoff, its actual initial V_0. Only the horizon threshold depends on the
requested accuracy. Arbitrary signed row offsets and positive row scales
preserve the conclusion because absorption still occurs under every
unilateral replacement; original live and Never rewards remain zero.

The signed affine statement can also be checked directly at every root.
For fixed finite mu_i and lambda_i>0, set r_i(A)=mu_i+lambda_i W_i(A)
on NONEMPTY coalitions only. The prescribed policy and each player's fixed
opponents absorb surely, so actual values transform as

    V^r_ti=mu_i+lambda_i V^W_ti.

The forced-Quit endpoint transforms by the same formula. In the Continue
endpoint, immediate opponent absorption has total mass1-H_ti, while the
surviving actual continuation has mass H_ti; their offset contributions
sum to mu_i. Hence g^r_ti=lambda_i g^W_ti. Every phase equality and
inequality is preserved. The geometric full-response argument then proves
the conclusion in the original game, including negative offsets. This does
not assert affine invariance of arbitrary nonabsorbing quitting profiles.

## 6. Actual source, implemented consumer, and theorem scope

The raw original-game class can be stated directly: choose any finite real
recipient offsets mu_i and positive scales lambda_i, and require that
W_i(A)=(r_i(A)-mu_i)/lambda_i satisfy(1). These are finite numerical
conditions on the original sixty rewards. In particular mu_i=1 and lambda_i=1
give an independent full60 reward cube around the strictly positive-own center
1+Z, enlarged by the two arbitrary and two one-sided grand coordinates.
The mu_i need not equal the perturbed own-singleton entries.

Every strategic input is produced. The table determines the rational
indifference system; one fixed rational preconditioner and exact interval
inequalities produce a fixed point for each input table. Invertibility of
that preconditioner is deduced, not assumed. The fixed point gives all27
hazards. Formula(3) gives their actual ten phase values. The40 action
comparisons and opponent-deleted contraction supply complete terminal Nash
and the fixed uniform target. No minimum, root selector, supplied strategy,
continuation annotation, strategic certificate, or unproved recurrence is
an input to the raw class.

The exact policy, full root Nash, and deleted-opponent contraction are the
three hypotheses of
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
The first concludes exact terminal Nash for the cyclic behavioral profile;
the second concludes that its actual phase value is a uniform-equilibrium
payoff, witnessed by the same profile at every accuracy. Their exact
hypotheses are the cyclic policy recursion, all phase root inequalities,
and a playerwise opponent-cycle Continue product less than one. Sections2--5
supply each of them without adding public correlation. The existing consumer
does not produce the ten-support word or the contraction; those are the new
raw-data production here. No new Lean verification is asserted.

## 7. Complete original calibration and prior-producer comparisons

For every real T>=0, take r_i(A)=1+Z_i(A) on nonempty coalitions, with

| A | Z(A) in recipient order0,1,2,3 |
| --- | --- |
| 0 | (0,3,-1,-1) |
| 1 | (3,0,-1,-1) |
| 2 | (-1,-1,0,3) |
| 3 | (-1,-1,3,0) |
| 01 | (-1,-1,-1,-1) |
| 02 | (-2,-1,-1/10,-1) |
| 03 | (-1/10,-1,-1,-2) |
| 12 | (-1,-1/10,-2,-1) |
| 13 | (-1,-2,-1,-1/10) |
| 23 | (4,4,4,1) |
| 012 | (-6,-41/10,-11/10,-1) |
| 013 | (-41/10,-6,-1,-11/10) |
| 023 | (-11/10,-1,9/10,-4) |
| 123 | (-1,-11/10,-1,-21/10) |
| 0123 | (-101/10-T,-101/10,-1/10,-31/10) |

All original own-singleton rewards equal one. Original AllNever has prescribed
payoff zero and complete response cap one for every player, so it is not an
equilibrium. Native AllNever being exact is not an existence argument for this
original family. The ten-phase theorem instead produces an absorbing profile
with opponent-deleted geometric absorption; that property justifies its signed
offset and positive-scale transfer to the original rewards.

The point T=0 is the center of the new full sixty-coordinate reward cube.
Every T>=0 is covered by the new theorem's one-sided recipient0 grand bound.
This ray is useful for the family-level comparisons below; it does not assert
that the finite screens hold throughout the entire new reward cube.

Write Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}), L=J-Gamma, all with zero diagonals.
The singleton matrix has favorite pairs01,23 with entries3 and cross entries-1.
Its determinant is45 and

    Gamma^-1=(1/15)[2,7,3,3;7,2,3,3;3,3,2,7;3,3,7,2].

The joining matrix is

    L=[0,-4,-1,9/10; -4,0,9/10,-1;
       9/10,-1,0,1; -1,9/10,-2,0].

For native continuation zero, the four complete joining fields are

    g0=L0*q-5q2*q3-T*q1*q2*q3,
    g1=L1*q-5q2*q3,
    g2=L2*q,       g3=L3*q.                                  (C1)

The exact checker reconstructs these from all sixty coordinates. Reciprocal
L sums are strictly negative, and the higher terms contribute nonpositively
to q dot g. Every L column has a positive entry. Hence native zero has unique
AllContinue as a whole root: two or more active owners contradict q dot g<0,
and a singleton active owner recruits an inactive player. This is only a
root-inertia check, not a UE obstruction or a replacement for original scope.

### 7.1. All fourteen quiet children and all punishment selectors

For any nonempty proper child S and outsider o, necessary capped-clock rows
for nonnegative weights lambda are, for each j in S,

    sum_(i in S) lambda_i*(-Gamma_ij)>=-Gamma_oj,
    sum_(i in S) lambda_i*L_ij>=L_oj.                         (C2)

For the following(S,o,j), the joining row has positive right side and all
nonpositive left coefficients:

    (0,2,0),(1,3,1),(2,1,2),(3,0,3),
    (01,2,0),(02,1,2),(03,2,0),(12,3,1),(13,0,3),(23,1,2),
    (012,3,1),(013,2,0),(023,1,2).

For S=123,o=0, add future rows j=2,3 and twice joining row j=3. Its
left coefficients in child order1,2,3 are(0,-1,-3), and its right side is
19/5. Thus every one of the fourteen children fails over its entire weight
cone, including the version without a restrictive Never row. These arguments
are independent of T and do not select a favorable child equilibrium.

The ENTIRE complementary Nash correspondences with one owner fixed sure are

| Sure owner | Complete complementary profiles |
| --- | --- |
| 0 | (1,0,1,0) |
| 1 | (0,1,t,1), 0<=t<=9/20 |
| 2 | (0,1,1,0) |
| 3 | (0,0,1,1) |

Equation(C1) proves exhaustion on every boundary face. With owner0 sure, row1
is strictly negative, then row3 is strictly negative, then row2 is positive.
With owner1 sure, row0 is strictly negative. After q0=0, row2 equals q3-1;
if q3<1 it forces q2=0 and row3 then forces q3=1, a contradiction. Thus
q3=1 and row3=9/10-2q2 gives the full interval. With owner2 sure, row0 forces
q0=0, then row3 forces q3=0, then row1 forces q1=1. With owner3 sure, row1
forces q1=0, then row2 forces q2=1, then row0 forces q0=0. The additional
negative T term either strengthens a strict sign or vanishes.

The designated owner's Quit-minus-Continue gaps are respectively

    -1,       -1-(41/10)t,       -1,       -2.                 (C3)

Every listed profile has ANOTHER sure quitter. Hence the coefficient of any
punishment continuation in that owner's comparison is zero. No punishment
law, including the exact optimal one, can repair(C3). This excludes the full
singleton sure-owner alternative, not just stationary repetition. A larger
persistent base satisfying all its leave and join tests would be a whole
Nash root with a sure owner, and so would also contradict this exhaustive
comparison. It is not enough to test only one induced pure profile; the full
interval has been retained.

### 7.2. All marked blocks, passive bounds, and calendar roles

Owners2,3 both have strictly positive participant reward at23. For ANY marked
set intersecting23 and ANY ordered partition into positive-weight blocks,
the first block meeting coalition23 has strictly positive participant sum.
It fails the required first-active-block inequality. A marked set contained
in01 instead has strictly positive passive reward4 at its disjoint coalition23.
Thus the unboxed ordered-anchor theorem fails over all149 ordered-subset/block
choices and every positive weighting.

The two finite-player funding theorems have exactly two unmarked owners.
Their marked set is therefore forced to be01. All its possible partitions,
namely one block01 and the two singleton orders, have the same per-marked
funding tests. Opposite joining signs force the unmarked order(2,3), with
c2=1,c3=-2 and both marked singleton magnitudes one. The exact passive extrema
are positive upper3 for row2 and negative lower-1 for row3. The old separate
threshold is7/3, strictly below K0=K1=4.

The newer calendar threshold is EXACTLY32/11, also below4. This is true
nonadmission, not failure of a merely sufficient estimate. A deterministic
calendar is an ordered list of disjoint nonempty cohorts; owners omitted
from the list choose Never. Its prescribed payoff u_i is the reward at the
first cohort, or zero if the list is empty. Its own-Never payoff m_i is the
reward at the first cohort left after deleting owner i from every cohort,
or zero if none remains. Convex mixtures of these finitely many paired
vectors define the calendar polytope. Every deterministic calendar satisfies

    20u2-41u3<=63+62(u2-m2)-3(u3-m3),     m3>=-1.

On the diagonal put x=u2=m2>0 and s=-u3=-m3>0. Then s<=1 and
x<=(63-41s)/20, so the reciprocal funding is at least

    20/(63-41s)+2/s >=32/11.

The difference from32/11 is exactly

    2(1-s)(693-656s)/[11s(63-41s)] >=0.

Thus this is a bound on the entire diagonal polytope, not on one mixture.
The three-calendar mixture with time vectors(0,0,0,0),(1,0,0,1),(1,1,1,0), weighted respectively
1/4,9/40,21/40, has observed vector(11/10,-1,11/10,-1). It attains32/11.
All observed rows are unchanged when T varies. This exhausts all36 discrete
block/role choices and all continuous positive weights. Therefore neither passive funding
class covers the present ray under any relabeling.

### 7.3. Pair phases, rotating pairs, and four singleton phases

Every pair has at least one strictly negative L entry. Each of the three
partitions therefore fails the necessary all-owner nonnegative scheduled
joining condition of the general two-pair join-cap theorem and crossed
matching. Every partition also has a negative scheduled participant entry.
This excludes nonmatching positive-passive and bounded-inverse-corner pair
criteria. Since Gamma inverse is strictly positive, the signed all-column
two-pair criterion forces every column sign positive and fails the same
participant condition. This is not a claim about the different single-column
asymptotic theorem.

The negative-singleton pairs have participant coordinates(-2,-1/10) or their
reverse. No such pair has both normalized participant values below-1.
Consequently the below-singleton and opposite-sign matching-phase raw classes
fail under every partition. The low-passive friendly-pair class must choose
the positive-singleton matching01|23, but its normalized common participant
value would have to equal all four numbers(-1,-1,4,1). Equal negative singleton
magnitudes force equal row scales, so normalization cannot cure that mismatch.
The positive-joining friendly-pair and global asymmetric favorite-pair classes
likewise fail their required favorable participant comparisons at01 and32.
The negative-pair-funded boundary class requires both members of its positive
singleton pair to have participant reward above that singleton; pair01 fails
at both members and pair23 fails at owner3. The complete four-phase passive
reward ray also requires one common favorite participant reward, inconsistent
with the literal original values(0,0,5,2).

The mixed-positive-passive solo/joint theorem has only the ordered joint pair
(2,3) available, with anchor0 or1. Its whole proper period-two architecture
is excluded more strongly than its sufficient threshold. Let u be the solo hazard, x the joint hazard of owner2, and y that of
owner3. Define the opponent odds Y2=y/(1-y) and Y3=x/(1-x). The solo
owner's zero-value mixing equations give -x-y+6xy=0. The actual native
values of owners2,3 just before the joint date are 4y and x. Their values
just before the solo date are -u+4(1-u)y and -u+(1-u)x. Their joint-date
Continue comparisons therefore give

    4y=3y+(1-y)[-u+4(1-u)y],
    x=3x+(1-x)[-u+(1-u)x].

Converting these three exact equations to odds forces

    Y2^2+(5u-3)Y2+u=0,
    -2Y3^2+(2u-3)Y3+u=0,
    4=1/Y2+1/Y3,       0<u<1, Y2,Y3>0.                       (C4)

The first discriminant forces u<=9/25. The second gives
Y3=u/(3-2u+2Y3)<u/(3-2u)<=3/19. Thus the right side of the final equality
is greater than19/3>4. No choice of positive proper hazards solves the
architecture; its other quadratic branch is not silently discarded. These
comparisons do not address arbitrary multi-phase controllers.

The rotating mixed-pair class requires every recipient to have
a positive forward pair participant reward b/2 after positive normalization.
Owners0 and1 have no positive participant pair coordinate at all. Thus all24
circular role assignments fail before the passive ordering or triple bounds
are considered. This comparison uses the positive-forward-participant raw theorem.

There is also a complete exclusion of all24 proper positive four-singleton
orders. If i then j are consecutive solo owners in an exact Nash period, the
own-zero mixing equations force

    J_ij<=0,              J_ji<=Gamma_ji.                       (C5)

The first is owner i's Quit comparison at j's date, when its prescribed
value is zero; the second is owner j's comparison at i's date, whose next
own date has value zero. For this table(C5) leaves only the cyclic order
2,0,3,1 and its rotations. In that order each favorite is opposite. Writing
u_i for the four Continue probabilities, the four exact owner equations are

    u_i(4-4u_(i+1)+u_(i+1)u_(i+2))-1=0.

Subtracting opposite equations gives a two-by-two linear system for
u0-u2,u1-u3 with strictly positive determinant

    16(1-u1)(1-u2)+u2u3(4-u0)(4-u1).

Hence u0=u2,u1=u3; the remaining difference forces all four equal, and the
proper root is u=(3-sqrt5)/2. Put p=1-u. At owner3's date, recipient2's
native prescribed value is1+p, while immediate Quit pays4p. Their difference
is3p-1>0. Thus the entire positive four-singleton architecture fails, including
any locally selected branch with this support word. No unspecified local
radius is used in this exclusion.

The fixed four-joint rectangle and bounded-radius four-joint center require
the positive-singleton favorite pair participant values5 and9/2 in original
units. Here one favorite pair has both original participant values zero.
The center's declared radius is at most1/2, so all singleton-compatible
relabelings fail quantitatively. The fixed passive chambers require different
literal opposite-participant and adjacent-participant coordinates. The scalar
singular circuit requires two distinct positive participant pairs03 and13,
whereas23 is the only positive participant pair here; all its roles fail.

### 7.4. Matrix geometry, traps, and every weight cone

The positive singleton graph is two disjoint reciprocal pairs. There is no
directed positive triple or Hamiltonian cycle and every reciprocal singleton
product is strictly positive. Thus the cyclic-child, opposite-sign escort,
opposition-cycle, and one-mutually-negative-pair attachment raw geometries
cannot fit any relabeling. There are four mutually negative pairs, excluding
the no-mutually-negative class. Every proper triple has a row whose two
off-diagonal singleton entries are negative; it has no positive image from
a nonnegative vector, and no nonnegative inverse. Positive two-owner children
have strictly negative outsider passive rows. A crossing negative2x2 block
fails standard Q and has no nonzero nonnegative homogeneous complementary
vector, so the full projective Q-bar premise also fails. This does not claim
that the full Gamma is not Q; its positive inverse is displayed above.

Only owners2,3 have any positive participant entry; the positive triple
Z2(023)=9/10 is included. Consequently23 is the sole premium trap and the
greatest premium core. At that pair its two joining increments are1 and-2,
whose product is-2. This defeats even the weak mixed-pair-trap condition.
The boxed-charge class requires trap size at least three. The supportwise
upper-average alternative fails because every nonzero nonnegative weighting
on23 sees the positive inserted coefficients4,1 at coalition23. The triple
core classes fail their computed core-size premise. The core-at-most-two
theorem still requires globally nonnegative participant premiums, violated
here in every row.

Every player has some negative participant reward, so the protected-player
set is empty. For the sole trap23, the global inserted-floor test at singleton
coalition0 has coefficients Z2(02)=-1/10 and Z3(03)=-2, excluding all its
positive weights. Pure quitting by2,3 gives both active forced-Quit premiums
positive and directly falsifies the product-low condition.

For all nonzero nonnegative weights, coalition01 has native vector(-1,-1,-1,-1),
so no global or proper-coalition lower ledger can pass. Summing the inserted
singleton tests for owners0,1 gives recipient coefficients
(-1,-1,-21/10,-21/10), so no nonzero nonnegative global inserted floor exists.
Summing all four native singleton columns gives(1,1,1,1), excluding any
nonzero nonnegative global upper ledger. In particular the graph-free H/J-flat,
sink-or-receiver, and two-ledger classes fail their lower ledger, independently
of their proper-flat condition, which also fails on trap23. These are exact
cone obstructions, not failures of selected numerical weights.

### 7.5. Complete pole census and honest asymptotic comparison

The exact script evaluates every one of the24 three-passive-pole role
assignments uniformly for T>=0. Seven pass the first two endpoint signs.
Exactly one passes all eight guards:

    (old0,old1,old2,old3)=(1,3,0,2),     c=9/40,
    (a2,b2,l0,l1,f0,f1)
      =(-1,-5,-89/40,-53/40,3519/16000,-319/400).

Its relevant original passive coordinates are r3(01)=0,r0(23)=5,r2(13)=0.
The passing endpoint role is retained honestly. The entire T ray varies
only a negative PARTICIPANT grand coordinate; it is not this producer's
fixed-background ray of two increasingly negative passive poles.

All columns of Gamma inverse are positive. Thus the signed passive-coalition
criterion requires negative growing passive entries for every recipient,
whereas all passive coordinates here are fixed. The single-column criterion
can use only its positive sign, requiring a positive growing participant
entry. The sole growing participant entry here goes to negative infinity.
The positive-inverse participant-jackpot theorem likewise cannot supply this
ray from its stated positive-growth guarantee. Reselecting an unbounded
background box with T does not yield the missing uniform diagonal guarantee.

These are family-level comparisons. They DO NOT prove that each finite table
is outside every theorem with an unspecified eventual threshold, arbitrary
residual box, or unrelated unquantified local neighborhood. A new bounded
reward cube is also not automatically disjoint from every earlier existential
neighborhood merely because their numerical centers differ. The exact finite
selector failures above and this limitation must be stated together.

No complete stationary-support census or stationary nonexistence is
asserted. The finite raw-selector comparisons above do not require one.
In particular the theorem is not a claim that ten phases are necessary.

## 8. Coverage source correspondence and exact boundary tests

The complete stopping-law information mode agrees with
`quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.
These identify the law payoff and law-replacement cap with the terminal
behavioral payoff and unrestricted behavioral best-response value. The
direct proof in Section5 prices the same complete response set.

For the quiet-child comparison, `rawChild_future_delta`,
`rawChild_future_base`, `rawChild_joining_delta`, and
`rawChild_joining_base` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockOriginalCoalitionRows.lean`
give the exact original-coalition expressions used in(C2).
`nonempty_cappedClockParentRewardCertificate_iff` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockExactLPAlternative.lean`
identifies the certificate with nonnegative feasibility of those full rows.
Thus the14 dual obstructions exclude all choices, rather than a supplied
child law or one proposed weight vector.

`quittingSingletonBaseOwnerFloorExcess_nonpos_iff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
retains the exact punishment value multiplied by opponent Continue mass.
That coefficient is zero on every member of the four complete fibers above.
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`
requires all base leave and outsider join comparisons; together with induced
Nash they would contradict those same fibers.

The product-low comparison uses `HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`:
every absorbing product root must have an active low forced-Quit coordinate.
Pure23 is its exact counterwitness here. The global insertion quantifier in
`HasWeightedQuittingTrapLeavers`, in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`,
is why singleton coalition0 may be used to defeat the trap23 floor.
`IsQuittingSingletonEscortEdge` in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean` requires the
reciprocal signs absent from this singleton table. Finally,
`isProjectiveQMatrix_iff_standard_or_homogeneous` and `IsProjectiveQBarMatrix`
in `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`
explain why both branches of a negative principal block are checked.

The positive boundary control is the full independent reward cube itself:
all60 errors of size1/1000000 are simultaneous, not one-coordinate tests.
The hazard box remains strictly proper, its period survival is below1/1000,
and all13 inactive action gaps are below-1/3. The enlarged grand-coordinate
class has a proof of which coordinates prescription and each unilateral
deviation can query; arbitrary rewards are not discarded by assumption.

Exact negative controls distinguish the relevant claims. At original own
levels one, AllNever has debt one for each player. The true calendar optimum
is below4 even though the construction succeeds at4. The sole positive pair
trap has negative joining product, while every sure-owner fiber retains a
strict leave gain independent of any punishment. All proper positive
once-per-owner four-singleton orders fail. These facts show failures of the named earlier producers and
architectures; none is a positive exploitability gap for the quitting game.
The passing passive-pole role and the unknown-threshold limitation are not
suppressed. Source-only least-Never restrictions and verifiers for supplied
strategic data are not treated as unconditional earlier UE producers.

## 9. Formalization handoff and nonclaims

A raw theorem can take the sixty input rewards, four optional signed offsets,
four positive scales, and the explicit numerical inequalities(1). Define the
ten support rows and27-coordinate closed hazard cube. Define rational policy
evaluation and the27 active gap functions; show their denominator is positive
throughout that cube. Formalize outward fixed-point interval arithmetic and
its first-derivative extension, then check the fixed rational matrix and the
three strict bounds(5)--(7). A generic contraction lemma yields the exact
hazard vector and proves the matrix invertible from the derivative norm.
The thirteen inactive inequalities and ten policy recursions then instantiate
the existing periodic compiler.

The cap comparisons for grand-coordinate enlargement should precede the
signed affine transfer. The transfer must retain opponent-deleted absorption,
since it is not a general payoff-shift principle for nonabsorbing profiles.
The actual phase target is fixed once the raw table and its produced hazards
are fixed. Neither a chosen equilibrium nor an unexplained limiting root
belongs in the raw assumptions.

The class has a full-dimensional sixty-coordinate cube and the stated
unbounded grand freedoms. It does not cover arbitrary rewards, all passive
pair parameters, or all four-player games. There is no completeness claim
for periodic strategies, no stationary nonexistence claim, and no claim that
the support word is minimal. The general Fin4 UE conjecture remains open.
This is an ordinary mathematical computer-assisted proof, not a new
Lean-checked result.

## 10. Complete exact reproduction

The first program uses only standard-library Python. Save it as
`ten_phase_cube_check.py` and run `python ten_phase_cube_check.py`. All
inequalities use integers or exact fractions. The fixed rational matrix is
included in full; no numerical solver, external data, or precomputed output
file is required.

```python
"""Exact full60 reward-cube certificate for a ten-phase quitting equilibrium.

Save as ten_phase_cube_check.py and run with standard-library Python.
Standard-library only. Every interval endpoint is an integer multiple of10^-30.
The decimal hazard and inverse approximations below are rational witnesses;
no floating arithmetic or unchecked root solving is used by this certificate.
"""
from fractions import Fraction as F
from itertools import product

SUP=[[0, 2], [0, 1, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 3], [1, 2]]
HS=[F(v) for v in (
    '0.6325497567632887',
    '0.08879557335326287',
    '0.01698680638857422',
    '0.03227897357149102',
    '0.33108423804822423',
    '0.06760992875293761',
    '0.02439015231250483',
    '0.3059328798073793',
    '0.22380439946248434',
    '0.10848819936038465',
    '0.2451127758480039',
    '0.31453288329789203',
    '0.1591852043042641',
    '0.21771744678665797',
    '0.37459292405262073',
    '0.19205376846927352',
    '0.1977028589574382',
    '0.415002872799142',
    '0.2100456245095365',
    '0.17331022480699212',
    '0.4271990349355332',
    '0.20630519924427315',
    '0.13045585395902404',
    '0.6187739431193668',
    '0.05748712065185276',
    '0.05949182192737265',
    '0.6099345898764957',
)]
NV=len(HS);NT=len(SUP);D=10**30
INVERSE_SCALE=10**10
INVERSE_ROWS=(
    "18963796 4222258635 2173092703 -185891946 4784881248 -823862721 -898433551 -4652651849 14685450 -1086782748 1787024977 572756421 -991888410 -204034106 639766765 -1083462744 -71241774 731056425 -933458039 -35098747 845814561 -574012930 125079541 1977389822 234737791 -1979266699 -58253449",
    "-9183384797 -547470988 6344295416 -2368579171 10501950499 -533573423 1422537723 -9674423135 -787137673 2424623670 2686868687 -1081900434 3707803979 -164217280 -1861674915 3929790744 262873295 -2386746008 3432377038 146084752 -2910623686 2155827611 -406269289 -6833383615 -878187255 6807256829 246607285",
    "-128106697 -937745429 -1340764253 -1026679707 -5653990478 1409938930 3030242977 5736466391 -272033233 4792625430 -1950770004 -1939156462 5981746124 583570572 -3006568004 6571785308 489036522 -3912268407 5766400281 275503307 -4814894820 3647200669 -646466553 -11261577963 -1488525961 11183865397 425177843",
    "-66656665 -501000306 -1465750022 -1088822444 4798565992 -10801247 1445475124 -4474143621 -531735065 2355987906 1181312451 -1028013718 3327956624 21592191 -1682278135 3570537268 249643204 -2159417186 3122977428 138957143 -2637918971 1965675143 -363407825 -6182975564 -801441062 6152836719 225774919",
    "238479227 1723506888 3721383393 -3466843365 15666394879 -3155417588 -5933349291 -13888208640 568282425 -9022080792 4477780874 3790231095 -11013198204 -1223453895 5644350255 -12111392272 -919538557 7263287193 -10622758475 -513283758 8903325939 -6714303473 1194164142 20799709976 2742329326 -20654374402 -777365796",
    "282638489 2023752753 -56268791 88536747 -158379273 -7628003144 -9083205225 3647659537 1366056230 -9269652198 -1803443997 3731221265 -12753850764 -856185401 6193173787 -13956088322 -1101629072 8176820517 -12284815714 -624297856 10141173221 -7806167980 1327620490 23674109976 3188612928 -23464681014 -923264187",
    "148051720 1058203209 -29549044 46352053 -83021946 -3506478988 -4180767676 -3356222815 11261604 -5421190286 3570521678 2099323424 -6557370133 -920108003 3237191748 -7295172200 -575893122 4273655237 -6421635361 -327258742 5300283884 -4081008545 693150125 12371248821 1667131220 -12260798552 -482690522",
    "-125967542 -951994681 23099010 -40132474 68997427 -4181014844 2549601039 2037592939 -223045225 4601605152 -740936225 -1699889902 6069148269 379725395 -2922836319 6643758170 468490576 -3896927861 5832773177 269468065 -4835685006 3692696188 -652697951 -11342758611 -1504434752 11269316487 436350467",
    "168751181 1165163487 -35301532 52281333 -95931652 -25681808 -79716098 -2140144 -4769426347 -9029152348 1541667691 2244194356 -7246998907 -668517057 3557225104 -7967527750 -676455794 4664244032 -7026489880 -380272015 5782545891 -4476605786 740089651 13452487885 1831965555 -13310296789 -529807820",
    "97262787 653070634 -21078064 29884565 -55879424 -14371756 -45131349 694923 -2078065969 -3954002499 -4281828227 342167651 -4732987185 2637861093 1995360257 -4431746408 -411067022 2595211051 -3917478872 -222998091 3216140641 -2501215854 403980179 7461050353 1025091302 -7371742758 -296175039",
    "-37557400 -335570415 4840974 -12661346 18928194 7490519 21099968 8427890 -4530558012 1331592531 1428046719 -505336089 2237050718 -16676698 -1039802731 2418758545 116977087 -1423075566 2108757011 71298519 -1768372731 1321814387 -257661959 -4200204778 -534686526 4198877775 155805429",
    "127741603 776721162 -30886729 38159970 -75963469 -16990135 -55706640 9359292 12125074 -84372198 13258858 -3349094460 -8273280954 796855452 2281381040 -5191441727 -387912176 2995748763 -4569191381 -298589142 3712345414 -2939484762 432446718 8517808598 1211507640 -8368310160 -348734172",
    "85215664 466122972 -22661250 24757183 -52328242 -10123738 -34871681 11666444 7939239 -52778146 6738133 -1383566720 -3460536450 -4566859661 422183825 -3718902462 2024528801 1689832452 -2712942695 -104371777 2145113250 -1741815286 232547545 4859828665 722275697 -4739443549 -206771720",
    "-2317585 -151176906 -4861389 -2536077 -2976960 3498901 7048183 14125565 -613742 10775080 -5794246 -4416098145 789210876 1045191108 -548402063 1209066372 97785386 -749518159 1060192772 -11748208 -933022967 638321104 -174457744 -2323042899 -250189977 2374837031 74449155",
    "147108432 671161146 -44400725 40942780 -94576147 -14369178 -54319041 34062667 13322065 -82107824 6223136 37530291 -105014975 -3584304 -2569876695 -7617349951 444476977 2244354470 -3728192414 -206449087 2860296408 -2436898439 238493554 6277542842 1024545715 -6016633231 -290607150",
    "116178815 437263925 -38723463 31097431 -77652242 -9198731 -38836266 36537932 10256496 -58626944 1170968 27034302 -75491386 -2071820 -1012098860 -3088692387 -4682942600 476762749 -2941173907 1691726610 1620452732 -1582072631 209915671 3500750403 667393509 -3258345013 -183127046",
    "36788682 -55528947 -19937440 7235258 -30748684 1604964 -3747665 31809571 2690066 -5472582 -7492265 3077016 -8224941 940598 -4316599811 469833674 743318301 -619103524 622102071 28139688 -698293554 340704550 -204087661 -1962950553 -114903229 2116982351 38342090",
    "251601509 767423054 -90974988 64918855 -173855703 -15730827 -76170700 97894098 21694010 -114813266 -4754846 53457669 -148931548 -3005327 79748537 -159243153 -10406665 -2090575079 -7105650427 182662205 2435429259 -2599159823 83408051 4729077547 1131971128 -4132115124 -307680614",
    "201445917 510386731 -76806119 50715999 -142670010 -10303777 -56713132 88736002 17094941 -85409765 -7828346 40060829 -111468102 -1604718 59807513 -118978682 -7726083 -798186908 -2879403272 -4785935720 623353007 -2318479387 1652098316 2278051106 895202117 -1765601500 -191175798",
    "114361333 47785448 -53251289 25464452 -88593581 -148803 -21376236 75868708 8996939 -31906087 -14349265 15803117 -43407279 1107786 23653031 -45764589 -2835159 -4344112454 178594220 374532863 -820533031 76205555 -260120580 -2606984654 19802368 2997745585 9879983",
    "526880983 1108464300 -210154949 129312018 -379998542 -21404277 -137709353 256741622 44009998 -207065722 -30057120 97964781 -271934248 -2220476 146281468 -289696453 -18676235 181377840 -251911680 -10077466 -1852466879 -6828766212 -119132302 2086755536 1623787120 -641941212 -394763803",
    "256084552 407660875 -105206480 63054001 -191224087 -9215415 -65571194 131409682 21362139 -98943870 -17151309 46746951 -130551667 -775543 70091693 -139033865 -8959150 86985128 -120909663 -4838294 -760950930 -2864411776 -4960817680 903919498 2882542558 -247723114 -77356195",
    "254599284 175909631 -115744639 57679027 -195088401 -1999868 -50770654 161463508 20238739 -75913161 -29053806 37222509 -102493849 1873452 55691129 -108303842 -6769091 68461476 -94010351 -3613315 -4689183584 -252602247 -334473080 -4650964460 222312129 5490606195 -11219944",
    "1604138001 -2494529446 -776973157 402806947 -1449302678 -11983564 -358340131 1078209564 132719974 -554404932 -205338118 259413533 -755448299 6836412 400293229 -802770027 -51568514 499770812 -698505478 -28006917 602022531 -436208565 85883508 1413927642 4413546504 923694360 3925083029",
    "364139019 226897222 -166743302 81955752 -279559403 -2089208 -71061886 234249897 28838719 -106156555 -42846189 52241021 -143651920 2964207 78145249 -151679224 -9451257 95976603 -131637158 -5039057 114699158 -81876821 16609245 -9155632459 33352767 8470554448 -8975148",
    "1677453 8433592350 192222139 -16443177 423249366 -72875241 -79471446 -411552940 1299010 -96131980 158072301 50663492 -87738048 -18047952 56590930 -95838307 -6301731 64666008 -82569557 -3104679 74817003 -50774637 11063981 174911131 20763863 -175077151 -9410234622",
    "4099138865 2554198178 -1877041218 922581741 -3147020107 -23518362 -799948714 2636967773 324639516 -1195011893 -482322597 588080894 -1617099887 33368285 879686630 -1707463829 -106393469 1080415459 -1481848859 -56725022 1291176587 -921693209 186971453 3033739423 375454474 1302816714 -101033879",
)
INVERSE_NUMERATORS=[list(map(int,row.split())) for row in INVERSE_ROWS]
def ceildiv(a,b):return -((-a)//b)
class Int:
    def __init__(self,lo,hi=None,raw=False):
        if raw:self.lo,self.hi=lo,hi;return
        l=F(lo);h=l if hi is None else F(hi)
        self.lo=(l.numerator*D)//l.denominator
        self.hi=ceildiv(h.numerator*D,h.denominator)
    def __add__(self,b):
        b=iv(b);return Int(self.lo+b.lo,self.hi+b.hi,True)
    __radd__=__add__
    def __neg__(self):return Int(-self.hi,-self.lo,True)
    def __sub__(self,b):return self+-iv(b)
    def __rsub__(self,b):return iv(b)+-self
    def __mul__(self,b):
        b=iv(b);v=[x*y for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
        return Int(min(v)//D,ceildiv(max(v),D),True)
    __rmul__=__mul__
    def reciprocal(self):
        assert self.lo*self.hi>0
        return Int(D*D//self.hi,ceildiv(D*D,self.lo),True)
    def __truediv__(self,b):return self*iv(b).reciprocal()
    def mag(self):return max(abs(self.lo),abs(self.hi))

def iv(x):return x if isinstance(x,Int) else Int(x)
class Dual:
    def __init__(self,v,d=None):self.v=iv(v);self.d=[Int(0) for _ in range(NV)] if d is None else d
    def __add__(self,b):
        b=du(b);return Dual(self.v+b.v,[x+y for x,y in zip(self.d,b.d)])
    __radd__=__add__
    def __neg__(self):return Dual(-self.v,[-x for x in self.d])
    def __sub__(self,b):return self+-du(b)
    def __rsub__(self,b):return du(b)+-self
    def __mul__(self,b):
        b=du(b);return Dual(self.v*b.v,[x*b.v+self.v*y for x,y in zip(self.d,b.d)])
    __rmul__=__mul__
    def reciprocal(self):
        z=self.v.reciprocal();return Dual(z,[-v*z*z for v in self.d])
    def __truediv__(self,b):return self*du(b).reciprocal()

def du(x):return x if isinstance(x,Dual) else Dual(x)
def prod(xs):
    z=du(1)
    for x in xs:z=z*x
    return z
TABLE={
1:(0,3,-1,-1),2:(3,0,-1,-1),4:(-1,-1,0,3),8:(-1,-1,3,0),
3:(-1,-1,-1,-1),5:(-2,-1,F(-1,10),-1),9:(F(-1,10),-1,-1,-2),
6:(-1,F(-1,10),-2,-1),10:(-1,-2,-1,F(-1,10)),12:(4,4,4,1),
7:(-6,F(-41,10),F(-11,10),-1),11:(F(-41,10),-6,-1,F(-11,10)),
13:(F(-11,10),-1,F(9,10),-4),14:(-1,F(-11,10),-1,F(-21,10)),
15:(F(-101,10),F(-101,10),F(-1,10),F(-31,10))}

def evaluate(rad,eps):
    h=[]
    for j,v in enumerate(HS):
        der=[Int(0) for _ in range(NV)];der[j]=Int(1)
        h.append(Dual(Int(v-rad,v+rad),der))
    qs=[];k=0
    for sup in SUP:
        row=[du(0) for _ in range(4)]
        for i in sup:row[i]=h[k];k+=1
        qs.append(row)
    def reward(i,A):
        if not A:return du(0)
        z=TABLE[sum(1<<j for j in A)][i];return Dual(Int(z-eps,z+eps))
    C=[prod(1-q[i] for i in range(4)) for q in qs]
    E=[]
    for q,sup in zip(qs,SUP):
        row=[du(0) for _ in range(4)]
        for bits in product((0,1),repeat=len(sup)):
            A={j for j,b in zip(sup,bits) if b}
            if not A:continue
            mass=prod(q[j] if b else 1-q[j] for j,b in zip(sup,bits))
            for i in range(4):row[i]=row[i]+mass*reward(i,A)
        E.append(row)
    survival=prod(C);V=[]
    for t in range(NT):
        row=[]
        for i in range(4):
            mass=du(1);v=du(0)
            for k in range(NT):
                phase=(t+k)%NT;v=v+mass*E[phase][i];mass=mass*C[phase]
            row.append(v/(1-survival))
        V.append(row)
    active=[];inactive=[]
    for t,(q,sup) in enumerate(zip(qs,SUP)):
        for i in range(4):
            other=[j for j in sup if j!=i];Q=du(0);P=du(0)
            for bits in product((0,1),repeat=len(other)):
                A={j for j,b in zip(other,bits) if b}
                mass=prod(q[j] if b else 1-q[j] for j,b in zip(other,bits))
                Q=Q+mass*reward(i,A|{i});P=P+mass*reward(i,A)
            H=prod(1-q[j] for j in other)
            gap=Q-P-H*V[(t+1)%NT][i]
            (active if i in sup else inactive).append(gap)
    return active,inactive,survival,V

assert NV==27 and NT==10
assert all(len(row)==NV for row in INVERSE_NUMERATORS)
B=[[Int(F(v,INVERSE_SCALE)) for v in row] for row in INVERSE_NUMERATORS]
rad,eps=F(1,10000),F(1,1000000)
assert all(0<h-rad<h+rad<1 for h in HS)
G,gaps,A,V=evaluate(rad,eps)
assert len(G)==27 and len(gaps)==13
beta=max(sum((Int(int(i==j))-sum((B[i][k]*G[k].d[j] for k in range(NV)),Int(0))).mag() for j in range(NV)) for i in range(NV))
Gc,_,_,_=evaluate(F(0),eps)
residual=max(sum((B[i][k]*Gc[k].v for k in range(NV)),Int(0)).mag() for i in range(NV))
assert 5*beta<D
assert 25000*residual<D
assert F(residual,D)+F(beta,D)*rad<rad
assert all(3*g.v.hi<-D for g in gaps)
assert 1000*A.v.hi<D
# A strict norm bound ||I-B DG||<1 at any point also proves B invertible:
# B DG is invertible by the Neumann series, so the square factor B is.
print('PASS: all27 active gaps enclosed with all60 reward coordinates variable')
print('PASS: contraction derivative norm<1/5 throughout hazard radius1/10000')
print('PASS: center displacement<1/25000 throughout reward radius1/1000000')
print('PASS: strict self-map; all13 inactive gaps<-1/3; period survival<1/1000')
print('PASS: exact ten-phase terminal Nash and uniform-equilibrium cube')
```

The second program requires SymPy. Save it as `ten_phase_coverage_check.py`
and run `python ten_phase_coverage_check.py`. It reconstructs the complete
original-own-one family and proves the stated uniform finite-selection
comparisons algebraically. Its output is not a stationary or arbitrary-word
completeness claim.

```python
"""Exact old-selector coverage for the original-own-one middle table.

Save as ten_phase_coverage_check.py and run with Python and SymPy.
Requires SymPy. T>=0 decreases only the native recipient0 grand reward.
This is a coverage checker, not the ten-phase existence certificate and not
a complete stationary-equilibrium or arbitrary-controller census.
"""
from itertools import combinations, permutations, product
import sympy as s

I = tuple(range(4))
T = s.symbols('T', nonnegative=True)
q = s.symbols('q0:4', nonnegative=True)
R = s.Rational
Z = {frozenset(A): tuple(map(s.sympify, row)) for A, row in {
    (0,): (0,3,-1,-1), (1,): (3,0,-1,-1),
    (2,): (-1,-1,0,3), (3,): (-1,-1,3,0),
    (0,1): (-1,-1,-1,-1), (0,2): (-2,-1,R(-1,10),-1),
    (0,3): (R(-1,10),-1,-1,-2),
    (1,2): (-1,R(-1,10),-2,-1), (1,3): (-1,-2,-1,R(-1,10)),
    (2,3): (4,4,4,1), (0,1,2): (-6,R(-41,10),R(-11,10),-1),
    (0,1,3): (R(-41,10),-6,-1,R(-11,10)),
    (0,2,3): (R(-11,10),-1,R(9,10),-4),
    (1,2,3): (-1,R(-11,10),-1,R(-21,10)),
    (0,1,2,3): (-R(101,10)-T,-R(101,10),-R(1,10),-R(31,10))
}.items()}
assert len(Z) == 15 and all(len(v) == 4 for v in Z.values())

def z(i, A):
    return Z[frozenset(A)][i] if A else s.Integer(0)

def original(i, A):
    return 1+z(i,A) if A else s.Integer(0)

def subsets(A):
    return [frozenset(B) for n in range(len(A)+1)
            for B in combinations(sorted(A),n)]

ALL = subsets(I)
G = s.Matrix([[z(i,{j}) for j in I] for i in I])
J = s.Matrix([[z(i,{i,j}) for j in I] for i in I])
L = J-G
assert all(original(i,{i}) == 1 for i in I)
assert G.det() == 45
assert G.inv() == s.Matrix([[2,7,3,3],[7,2,3,3],
                           [3,3,2,7],[3,3,7,2]])/15
assert L == s.Matrix([[0,-4,-1,R(9,10)],[-4,0,R(9,10),-1],
                      [R(9,10),-1,0,1],[-1,R(9,10),-2,0]])
assert all(L[i,j]+L[j,i] < 0 for i,j in combinations(I,2))
assert all(any(L[i,j] > 0 for i in I) for j in I)

def field(i):
    others=[j for j in I if j != i]
    return s.expand(sum(s.prod(q[j] if j in A else 1-q[j] for j in others)
                        *(z(i,A|{i})-z(i,A)) for A in subsets(others)))

g = [field(i) for i in I]
models = list(L*s.Matrix(q))
models[0] -= 5*q[2]*q[3]+T*q[1]*q[2]*q[3]
models[1] -= 5*q[2]*q[3]
assert all(s.expand(a-b) == 0 for a,b in zip(g,models))

# Complete sure-owner elimination is justified by strict signs on each cube
# and the surviving one-dimensional face, not by sampling equilibria.
def strict_negative_on_cube(expr, variables):
    # Affine in T with a nonpositive coefficient on the hazard cube.
    assert s.diff(expr,T,2) == 0
    for bits in product((0,1),repeat=len(variables)):
        v=s.expand(expr.subs(dict(zip(variables,bits))))
        assert v.subs(T,0) < 0 and s.diff(v,T) <= 0

strict_negative_on_cube(g[1].subs(q[0],1),[q[2],q[3]])
assert s.expand(g[3].subs({q[0]:1,q[1]:0})) == -1-2*q[2]
assert g[2].subs({q[0]:1,q[1]:0,q[3]:0}) == R(9,10)
strict_negative_on_cube(g[0].subs(q[1],1),[q[2],q[3]])
assert g[2].subs({q[0]:0,q[1]:1}) == q[3]-1
assert g[3].subs({q[0]:0,q[1]:1}) == R(9,10)-2*q[2]
strict_negative_on_cube(g[0].subs(q[2],1),[q[1],q[3]])
strict_negative_on_cube(g[3].subs({q[2]:1,q[0]:0}),[q[1]])
assert g[1].subs({q[2]:1,q[0]:0,q[3]:0}) == R(9,10)
strict_negative_on_cube(g[1].subs(q[3],1),[q[0],q[2]])
assert g[2].subs({q[3]:1,q[1]:0}) == 1+R(9,10)*q[0]
strict_negative_on_cube(g[0].subs({q[3]:1,q[1]:0,q[2]:1}),[])
t = s.symbols('t', nonnegative=True)
fibers=[(1,0,1,0),(0,1,t,1),(0,1,1,0),(0,0,1,1)]
owner_gaps=[s.expand(g[i].subs(dict(zip(q,p)))) for i,p in enumerate(fibers)]
assert owner_gaps == [-1,-1-R(41,10)*t,-1,-2]
for i,p in enumerate(fibers):
    assert any(p[j] == 1 for j in I if j != i)
print('PASS: entire four forced-owner fibers; every actual punishment coefficient is zero')

# All14 quiet-child systems have an exact dual obstruction using singleton
# future/joining rows, independent of all grand entries.
for child in (A for A in ALL if 0 < len(A) < 4):
    if child == {1,2,3}:
        outside=0; terms=[('F',2,1),('F',3,1),('J',3,2)]
    else:
        j,outside=next((j,o) for j in child for o in I if o not in child
                       and L[o,j]>0 and max(L[i,j] for i in child)<=0)
        terms=[('J',j,1)]
    coeff=[sum(w*(-G[i,j] if kind=='F' else L[i,j]) for kind,j,w in terms)
           for i in child]
    rhs=sum(w*(-G[outside,j] if kind=='F' else L[outside,j])
            for kind,j,w in terms)
    assert max(coeff)<=0<rhs
print('PASS: all14 full quiet-child weight systems fail exact necessary rows')

# All149 ordered-subset/block choices fail the old unboxed criterion for
# every strictly positive weighting. The two box/polytope criteria force C01.
block_count=0
for marked in ALL[1:]:
    owners=sorted(marked)
    for n in range(1,len(marked)+1):
        for labels in product(range(n),repeat=len(marked)):
            if set(labels)!=set(range(n)): continue
            blocks=[{i for i,label in zip(owners,labels) if label==k} for k in range(n)]
            if marked & {2,3}:
                first=next(B for B in blocks if B & {2,3})
                assert all(z(i,{2,3})>0 for i in first & {2,3})
            else:
                assert marked <= {0,1}
                assert all(z(i,{2,3})>0 for i in marked)
            block_count+=1
assert block_count==149

# Exact calendar threshold at the sole viable unmarked orientation2,3.
def calendars(remaining):
    yield ()
    for A in subsets(remaining)[1:]:
        for tail in calendars(remaining-A): yield (A,)+tail

CALS=list(calendars(frozenset(I)))
assert len(CALS)==150
def value(calendar,i,never=False):
    for A in calendar:
        B=A-{i} if never else A
        if B: return z(i,B)
    return s.Integer(0)

for cal in CALS:
    u2,u3,m2,m3=value(cal,2),value(cal,3),value(cal,2,True),value(cal,3,True)
    assert 20*u2-41*u3 <= 63+62*(u2-m2)-3*(u3-m3)
    assert m3>=-1
def time_vector(times):
    cal=tuple(frozenset(i for i in I if times[i]==v) for v in sorted(set(times)))
    return s.Matrix([value(cal,2),value(cal,3),value(cal,2,True),value(cal,3,True)])
mix=sum((w*time_vector(times) for w,times in [
    (R(1,4),(0,0,0,0)),(R(9,40),(1,0,0,1)),(R(21,40),(1,1,1,0))]),s.zeros(4,1))
assert mix==s.Matrix([R(11,10),-1,R(11,10),-1])
assert 1/mix[0]+2/(-mix[1])==R(32,11)<4
passive_up=max([0]+[z(2,A) for A in ALL[1:] if 2 not in A])
passive_down=max([0]+[-z(3,A) for A in ALL[1:] if 3 not in A])
assert passive_up==3 and passive_down==1
assert 1/passive_up+2/passive_down==R(7,3)<4
print('PASS: all weighted-block roles; true calendar32/11 and passive-extrema7/3 both fail K4')

# Traps and weight cones: all assertions hold uniformly for T>=0.
traps=[A for A in ALL[1:] if all(any(i in B and z(i,B)>0
               for B in subsets(A)[1:]) for i in A)]
assert traps==[frozenset({2,3})]
assert all(any(z(i,A)<0 for A in ALL[1:] if i in A) for i in I)
assert all(z(i,{0,1})==-1 for i in I)
assert [J[i,0]+J[i,1] for i in I]==[-1,-1,-R(21,10),-R(21,10)]
assert [sum(G[i,j] for j in I) for i in I]==[1]*4
assert J[2,3]>0 and J[3,2]>0 # Pure23 falsifies ProductLow.
assert L[2,3]*L[3,2]==-2 # Weak mixed pair-trap product fails.
assert z(2,{0,2})<0 and z(3,{0,3})<0 # Trap global inserted floor fails.
print('PASS: sole trap23; all nonzero lower/upper/floor weights and pair-trap alternatives fail')

# All partitions fail nonnegative pair joining; all fail nonnegative pair
# participant premises, including the signed-column variant since G^-1>0.
PARTITIONS=[((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2))]
for partition in PARTITIONS:
    pairs=[(i,j) for A in partition for i in A for j in A if i!=j]
    assert any(L[i,j]<0 for i,j in pairs)
    assert any(J[i,j]<0 for i,j in pairs)
assert not any(J[i,j]<G[i,j]<0 and J[j,i]<G[j,i]<0
               for i,j in combinations(I,2))
assert [J[i,j] for i,j in ((0,1),(1,0),(2,3),(3,2))]==[-1,-1,4,1]
assert all(G[i,j]*G[j,i]>0 for i,j in combinations(I,2))
assert sum(bool(G[i,j]<0 and G[j,i]<0) for i,j in combinations(I,2))==4
assert not any(all(G[p[k],p[(k+1)%3]]>0 for k in range(3))
               for p in permutations(I,3))
assert not any(all(G[p[k],p[(k+1)%4]]>0 for k in range(4))
               for p in permutations(I))
assert all(any(all(G[i,j]<0 for j in A if j!=i) for i in A)
           for A in combinations(I,3))

# Rotating class: each recipient must have a positive forward pair premium;
# rows0,1 have none. Check all circular role assignments literally as well.
assert all(all(J[i,j]<=0 for j in I) for i in (0,1))
assert not any(all(J[p[k],p[(k+1)%4]]>0 for k in range(4))
               for p in permutations(I))
# Scalar singular circuit needs TWO distinct positive pairs03 and13.
assert not any(J[p[3],p[0]]>0 and J[p[1],p[3]]>0 for p in permutations(I))

# Necessary endpoint inequalities for consecutive singleton owners.
orders=[p for p in permutations(I) if all(
    J[p[k],p[(k+1)%4]]<=0 and
    J[p[(k+1)%4],p[k]]<=G[p[(k+1)%4],p[k]] for k in range(4))]
assert len(orders)==4
assert set(orders)=={(2,0,3,1),(0,3,1,2),(3,1,2,0),(1,2,0,3)}
p=(s.sqrt(5)-1)/2
assert s.simplify(p*p+p-1)==0
assert 3*p-1>0 # Mate2's native forced Quit4p exceeds actual1+p.
print('PASS: all3 pair partitions, all24 rotating/scalar roles, all24 proper singleton orders')

# The mixed-positive pair theorem can use only2,3 in this orientation, with
# anchor0 or1. Its actual quadratic architecture forces K>19/3>4.
roles=[]
for a,o,i,j in permutations(I):
    if (G[a,i]<0 and G[a,j]<0 and G[i,a]<0 and G[j,a]<0
        and G[i,j]>0 and G[j,i]>0 and J[i,j]>G[i,j]
        and 0<J[j,i]<G[j,i]): roles.append((a,o,i,j))
assert roles==[(0,1,2,3),(1,0,2,3)]
u,y=s.symbols('u y',real=True)
assert s.expand((5*u-3)**2-4*u)==s.expand(25*(u-R(9,25))*(u-1))
assert R(9,25)/(3-2*R(9,25))==R(3,19)
assert R(19,3)>4

# Complete passive-pole guard census. Each expression is affine in T, so
# endpoint and slope signs certify the entire T>=0 ray.
def uniform_sign(expr):
    expr=s.cancel(expr)
    assert s.diff(expr,T,2)==0
    a,b=expr.subs(T,0),s.diff(expr,T)
    if a==0 and b==0:return 0
    if a>0 and b>=0:return 1
    if a<0 and b<=0:return -1
    raise AssertionError(('Nonconstant sign requires subdivision',expr))
def joining(i,A):return z(i,set(A)|{i})-z(i,A)
preliminary=[];passing=[]
for i,j,k,l in permutations(I):
    a,b=joining(i,{l}),joining(i,{k,l})
    if not (a>0>b):continue
    c=s.cancel(a/(a-b))
    guards=tuple(s.cancel(v) for v in (
        joining(k,{l}),joining(k,{i,l}),
        (1-c)*joining(j,{l})+c*joining(j,{k,l}),
        (1-c)*joining(j,{i,l})+c*joining(j,{i,k,l}),
        c*(c*z(l,{k,l})-z(l,{k})),
        (1-c)*joining(l,{i})+c*joining(l,{i,k})))
    signs=tuple(uniform_sign(v) for v in guards)
    preliminary.append(((i,j,k,l),c,guards))
    if signs==(-1,-1,-1,-1,1,-1):passing.append(((i,j,k,l),c,guards))
assert len(preliminary)==7 and len(passing)==1
role,c,guards=passing[0]
assert role==(1,3,0,2) and c==R(9,40)
assert guards==(-1,-5,-R(89,40),-R(53,40),R(3519,16000),-R(319,400))
assert (original(3,{0,1}),original(0,{2,3}),original(2,{1,3}))==(0,5,0)
print('PASS: all24 pole roles, exactly one passing endpoint role retained honestly')
print('PASS: complete literal original-own-one family and all listed finite selectors, T>=0')
print('Asymptotic comparisons are family-level only; no complete stationary census asserted.')
```
