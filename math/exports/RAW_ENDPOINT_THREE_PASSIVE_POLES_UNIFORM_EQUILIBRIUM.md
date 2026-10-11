# A raw endpoint producer with three passive poles

Status: complete ordinary mathematical result, not implemented in Lean.
The hypotheses are finite reward inequalities, not a supplied equilibrium,
continuation value, Jacobian, inverse, or degree certificate.

## 1. Model and raw-data theorem

There are four players I={0,1,2,3}. At every live date each chooses Continue
or Quit. The first nonempty quitter coalition S absorbs at a finite reward
vector r(S). Live dates and perpetual continuation pay0. Randomization is
independent and private across players. A unilateral replacement may be an
arbitrary complete behavioral strategy, including every finite quitting
deadline and Never. All payoff comparisons below are in expectation.

Fix arbitrary real rewards at57 of the60 nonempty-coalition recipient
coordinates. The three remaining coordinates are PASSIVE: their recipient
does not belong to the displayed coalition. They are

    r1(02)=-beta1*M+e1,
    r2(13)=-beta2*M+e2,
    r3(01)=a*M+e3,                                      (1)

where beta1,beta2>0 and a>=0. All other57 coordinates are fixed input.
Singleton levels, signs and singleton matrices are unrestricted.

Define from the fixed coordinates

    A0=r0(03)-r0(3),       B0=r0(023)-r0(23).

The first two strict guards are A0>0 and B0<0. Put

    c=A0/(A0-B0),              0<c<1.

Define

    A2=r2(23)-r2(3),       B2=r2(023)-r2(03),
    L0=(1-c)*(r1(13)-r1(3))+c*(r1(123)-r1(23)),
    L1=(1-c)*(r1(013)-r1(03))+c*(r1(0123)-r1(023)).

The next four strict guards are

    A2<0,       B2<0,       L0<0,       L1<0.              (2)

Finally define the quadratic polynomial

    Q(x)=(1-x)*(1-c)*r3(3)+x*(1-c)*r3(03)
               +(1-x)*c*r3(23)+x*c*r3(023),
    W(x)=x*(1-c)*r3(0)+(1-x)*c*r3(2)+x*c*r3(02),
    F(x)=(c+(1-c)*x)*Q(x)-W(x).                          (3)

The last two strict guards are

    F(0)=c*((1-c)*r3(3)+c*r3(23)-r3(2))>0,
    F(1)=(1-c)*(r3(03)-r3(0))
                        +c*(r3(023)-r3(02))<0.          (4)

None of these eight guards uses a coordinate in(1).

**Theorem.** For every fixed admissible input, every a>=0 and every finite
R>=0 there is M0 such that, for ALL M>M0 and ALL |e1|,|e2|,|e3|<=R, the
resulting game has an all-interior stationary Nash equilibrium against ALL
complete behavioral replacements, for the original terminal payoff. Its
actual terminal payoff is a uniform-equilibrium payoff delivered by the SAME
profile over all sufficiently long finite horizons.

The threshold and produced branch can be chosen uniformly on every compact
set of the57 fixed coordinates, beta1,beta2 and a preserving the eight
strict guards and beta1,beta2>0, with R bounded. Own-singleton coordinates
are included in that compact raw data. In particular this does not assert
uniformity over unbounded own-singleton shifts or unbounded a.

The theorem is an unconditional producer on this explicit reward class. It
does not transform an arbitrary fixed quitting game into this class, settle
the Fin4 conjecture, or assume that its raw guards describe every surviving
positive-gap source.

## 2. Exact stationary polynomial and limiting equations

For a stationary product hazard vector q, let the random opponent set B of
player i be independently sampled with hazards q_-i. Write

    alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(B union{i})],
    B_i=E[r_i(B)*1_(B nonempty)],
    H_i(q)=(1-alpha_i)*Q_i-B_i.                          (5)

Equivalently each expectation is the finite sum over B subset I\{i},
weighted by product_(j in B)q_j times product_(j notin B,j!=i)(1-q_j).
This defines every coefficient directly from the raw reward table.

Use t=1/M and the four unknowns x,y,c',z with

    q=(x,t*y,c',1-t*z).                                (6)

Substitution of(1) in(5) extends to an EXACT polynomial system in
t,x,y,c',z and the bounded residuals. Indeed the pole r1(02) has opponent
probability x*c'*(t*z), the pole r2(13) has probability
(t*y)*(1-x)*(1-t*z), and the pole r3(01) has probability
x*(t*y)*(1-c'). Thus every factor t^(-1) cancels. The selected residuals
have at least one remaining factor t.

At t=0, literal opponent-set evaluation gives

    H0=(1-c')*A0+c'*B0,
    H1=(1-x)*L0(c')+x*L1(c')+beta1*x*c'*z,
    H2=(1-x)*A2+x*B2+beta2*y*(1-x),
    H3=F(x,c')-a*x*y*(1-c').                            (7)

The expressions L0(c'),L1(c'),F(x,c') mean(2),(3) with c replaced by c'.
There is no external continuation annotation in this system. It uses the
actual stationary root quantities(5).

The first equation forces c'=c. For every0<x<1 the next two equations
then have the unique positive solutions

    y(x)=[-A2-x*B2/(1-x)]/beta2,
    z(x)=-[(1-x)*L0+x*L1]/(beta1*x*c).                  (8)

Consequently the remaining equation is

    F(x)-a*D(x)=0,
    D(x)=x*y(x)*(1-c)
        =K*x*[b+d*x/(1-x)],
    K=(1-c)/beta2>0, b=-A2>0, d=-B2>0.                (9)

## 3. Global scalar selection and automatic Jacobian

**Quadratic ratio lemma.** Let F have degree at most2, F(0)>0 and F(1)<0,
and let D(x)=K*x*[b+d*x/(1-x)] with K,b,d>0. There is one simple zero
x_star of F in(0,1). On(0,x_star), F/D has strictly negative derivative,
decreases from infinity to0, and has strictly negative derivative also at
x_star.

Proof. Endpoint signs give a zero. A quadratic cannot have two distinct
zeros inside(0,1) while reversing endpoint sign; a double zero does not
reverse sign. Hence the zero is unique and simple, F is positive before it,
and F'(x_star)<0. Write F=h0+h1*x+h2*x^2, with h0>0.

If h2<=0, then

    (F/x)'=-h0/x^2+h2<0,
    (D/x)'=K*d/(1-x)^2>0.

Both quotients are positive before x_star, so their ratio has strictly
negative derivative. If h2>0, then F' is increasing and
F'(x)<F'(x_star)<0 before x_star; D'>0 there, giving the same conclusion.
At x_star the derivative is F'(x_star)/D(x_star)<0. The limits follow from
D(x)~K*b*x near0 and F(x_star)=0. This proof permits initially increasing
concave F, for example F=1+10x-12x^2.

Apply the lemma to(9). For each a>0 there is exactly one x(a) in(0,x_star)
with F(x(a))/D(x(a))=a. For a=0 take x=x_star. Thus x,c,y,z are produced
from finite raw data, and none is an input witness. They depend smoothly
locally on the data, including a=0, and lie in positive compact ranges
over compact admissible data and bounded a.

Order unknowns in(7) as(c',z,y,x). Successive elimination gives the first
three pivots

    B0-A0<0,       beta1*x*c>0,       beta2*(1-x)>0.

The final Schur pivot at the selected root is

    [F-a*D]'=D*(F/D)'<0.                               (10)

The equality uses F=a*D at that root and holds also when a=0. Therefore
the COMPLETE limiting Jacobian is automatically nonsingular.

The parameter-dependent implicit function theorem applied to the exact
polynomial system now produces a zero for every sufficiently small positive
t, uniformly over a bounded residual box. Its hazards satisfy

    q0 -> x(a),       q2 -> c,
    q1/t -> y(x(a))>0,       (1-q3)/t -> z(x(a))>0.       (11)

All four hazards lie in(0,1) once t is sufficiently small. A finite
compact-parameter implicit-function cover proves the stated uniformity:
the limiting selected root varies continuously, the four pivots never
vanish, and all limiting coordinates stay away from their forbidden
boundaries on an admissible compact parameter set. The polynomial
perturbation is uniformly small with its first derivatives on that cover.

No global uniqueness of stationary Nash is claimed. The scalar uniqueness
selects this limiting branch and supplies the local nonsingularity needed
to construct an actual equilibrium.

## 4. Complete behavioral agency and the fixed uniform target

Fix one resulting finite table and one produced stationary profile. Every
player has a positive-hazard opponent, so alpha_i<1. Equation H_i=0 gives

    V_i=Q_i=B_i/(1-alpha_i).

The actual stationary payoff U_i obeys

    U_i=q_i*Q_i+(1-q_i)*(B_i+alpha_i*U_i).

Joint absorption is proper, and its unique solution is U_i=V_i. A pure
deadline h in{0,1,...} earns

    B_i*(1-alpha_i^h)/(1-alpha_i)+alpha_i^h*Q_i=V_i.

Never earns B_i/(1-alpha_i)=V_i as well. On the unique live history,
every complete unilateral private behavioral replacement is a mixture of
these independent stopping-clock laws. It therefore also earns V_i.
This proves terminal Nash against the full behavioral class, not merely
against stationary hazards, one-step deviations or a finite menu. No reward
sign assumption is used.

Let C be a finite bound on the absolute terminal rewards of this FIXED
table. Under every replacement of player i, absorption occurs no later
than the opponents' geometric first-quit time, with mean at most
1/(1-alpha_i). The expected N-date average/terminal discrepancy is at
most2C/[N*(1-alpha_i)], uniformly over that replacement class. Applying
this estimate to both sides of terminal Nash and to prescribed payoff
delivery proves that this SAME profile has uniform-equilibrium target V.
The target is fixed before accuracy. M and the table are fixed before N
grows; no horizon threshold uniform over unbounded M is asserted.

The exact existing semantic consumers are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
The raw-data polynomial producer proved above has not been implemented
in Lean.

## 5. Exact admissible four-player family

For every M>0 and a>=0 take singleton rows

    r(0)=(10,9,8,13),       r(1)=(12,10,17,7),
    r(2)=(4,14,10,17),      r(3)=(7,14,4,10).

Take pair rows

    r(01)=(-1,40,1,a*M),    r(12)=(1,-1,40,1),
    r(23)=(1,1,-1,40),     r(03)=(40,1,1,-1),
    r(02)=(-1,-M,-1,1),    r(13)=(1,-1,-M,-1).

Every triple pays-1 to its participants and1 to its outsider. The grand
row is(-10,-11,-12,-13). Thus beta1=beta2=1 and the selected residuals
are0. Exact substitution gives

    A0=33, B0=-2, c=33/35, A2=-5, B2=-2,
    L0=-96/35, L1=-80/7,
    F(x)=(4917-5025*x-550*x^2)/245,
    F(0)=4917/245>0,       F(1)=-94/35<0.               (12)

This is an entire admissible ray for each a, not a numerical strategic
witness substituted for the general producer. An exact limiting test is

    a=2267/49, x=1/2, c=33/35, y=7, z=496/33.

In unknown order(c',z,y,x), the full limiting Jacobian here is

    [-35,0,0,0;
     595/66,33/70,0,192/35;
     0,0,1/2,-4;
     5133/28,0,-2267/1715,-10109/245],

with determinant2933667/6860!=0.

The guards are substantive, not a generic boundary-root principle. For
example, if the fixed coordinates instead give Q identically0 and W>0
on(0,1), then F<0 and F-aD has no root there for any a>=0. Such a table
can still have equilibria of another form; only this proposed scale fails.

## 6. Whole-selection comparisons on the exact family

These comparisons distinguish this raw class from the explicitly named
existing source predicates. They do not classify all conditional verifiers,
unknown local radii, or all possible pointwise uses of an unspecified
scale-thick threshold.

### 6.1 Singleton, selective passive-row and quotient predicates

Set s_i=r_i(i)=10 and Gamma_ij=r_i(j)-s_i off diagonal, Gamma_ii=0. Here

    Gamma=[0,2,-6,-3; -1,0,4,4; -2,7,0,-6; 3,-3,7,0],
    det Gamma=265,
    Gamma^-1=(1/265)*[268,171,-20,132;
                       170,150,15,60;
                       -42,-9,15,7;
                       109,118,-20,26].               (13)

The six principal pair determinants are(2,-12,9,-28,12,42), in
lexicographic support order; the four triple determinants are
(26,15,150,268). Each singleton column has a negative off-diagonal entry.
Consequently Gamma is R0: an active support of size at least2 would be
annihilated by its invertible principal block, and an axis support fails
nonnegativity of the remaining residual.

At offset ones the complete complementarity roots are

    empty support: z=0, residual=(1,1,1,1), index+1;
    support02: z=(1/2,0,1/6,0), residual=(0,7/6,0,11/3), index-1;
    support012: z=(31/13,7/13,9/26,0),
                residual=(0,0,0,233/26), index+1.

All are strictly complementary. The local index is the sign of the active
principal determinant, by
`IsStandardLCPSolution.exists_box_localDegree_eq_sign_det`
in `MathUE/LinearProgramming/LocalDegree.lean`; the complete sum is
`exists_finset_r0Degree_eq_sum_sign_det`
in `MathUE/LinearProgramming/R0DegreeSum.lean`. Thus the actual R0 degree
is1, and the degree-not-one exit in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
does not apply. R0 excludes the homogeneous simplex branch. Every row has
a negative blocker, so `normalLayer` in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`
retains all4. The core is standard-Q by
`isStandardQ_of_r0Degree_ne_zero`
in `MathUE/LinearProgramming/R0Degree.lean`, so the ordinary non-Q core
exit is unavailable. The03 block[0,-3;3,0] itself is not Q: at offset
(-1,-1), its first residual is negative throughout the nonnegative orthant.

For the selective passive-row criterion, deleting0 has inverse entry
-6/67, deleting1 has inverse entry-7/50, and deleting3 has inverse entry
-14/13. Deleting2 has positive inverse, but its actual outside row times
that inverse is(14/5,3/5,-7/15). Every deletion therefore fails the actual
conjunction in
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.

The all-sure Quit-minus-Continue responses are(-11,-12,-13,-14), pairwise
distinct. Players in a common block of a full response-invariant quotient
would have equal responses at this block-constant point, so any such quotient
is injective. The actual predicate `QuittingResponseInvariantOnUnitCube`
and the criterion in
`UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`
require response invariance, not superficial table asymmetry.

All six cyclic orders starting with0 fail `SignedFourCycleSingletonData`
in `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`:
for0123,0132,0213,0231,0312,0321, respective failed witnesses are successor0,
successor0, predecessor0, predecessor2, predecessor0, successor3. No column
is negative at all other recipients. Rows1 and3 have multiple positive
off-diagonal entries, excluding the weak matching singleton pattern.

### 6.2 Every sure root and persistent base

Suppose any player i is sure to Quit at a root, with arbitrary independent
probabilities for the other three and any continuation annotation. The
opposite player i+2 gets at most-1 by joining and at least0 by continuing.
Neither negative passive pole can enter this comparison: its opponent
coalition contains i. The positive passive pole can only raise Continue.
Thus i+2 strictly Continues.

Both negative opposite-pair coalitions are now impossible. The remaining
nonsuccessor i-1 also strictly Continues, since all its joining rewards are
negative and all reachable passive rewards are nonnegative. The successor
i+1 strictly Joins for40 instead of a passive singleton at most17. Owner i
then receives-1, but withdrawing yields its passive singleton at i+1,
which is at least4. This contradicts root Nash.

This excludes ALL independent free-player mixtures and ALL nonempty sure
bases, including partial or empty free sets, not just pure roots. The
adapter `exists_uniformPayoff_of_persistentBase_inducedNash_signs`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`
combines its base-leave, quiet-outsider and induced-Nash hypotheses into
precisely such a full sure root.

### 6.3 Every proper quiet child and all five withdrawal kinds

For every nonempty proper child C, choose d in C with d+1 outside C.
Only d Quits0; all other child players Never. This is full child Nash:
d receives10 instead of Never0, while another member receives a passive
singleton at least4 and would get-1 by joining. The child debts and child
joint-Never mass are0. Outside successor d+1 gains at least40-17=23 by
joining. Hence no universal outsider-debt bound by child debts plus finite
Never slack can hold for this child.

The literal F/J rows fail separately. At A={d}, each nonowner child
advancing gain is-1-r_i(d)<=-5; the owner's is0. Nonmembers have withdrawal
coefficient0. For all five withdrawal kinds the owner's singleton withdrawal
floor minus10 is nonpositive: patient floor<=max(10,0), deadline/cancellation
floor<=0, evaluated security floor<=0, and terminal security floor<=10.
Thus EVERY nonnegative-weight right side of the joining row is nonpositive,
against the positive outsider gain. This covers F/J-only certificates,
without requiring an N row.

The actual definitions are `WithdrawalFutureJoinKind.gain` and
`WithdrawalFutureJoinRewardCertificate.join_row`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
The needed floor bounds are
`patientWithdrawalFloor_le_ownNeverAlternative`,
`deadlineWithdrawalZeroFloor_le_zero`,
`deadlineSecurityGainFloor_singleton`,
`deadlineSecurityGainFloor_singletonWithRestart`, and
`deadlineWithdrawalSecurityValue_le_singleton`, in respectively
`PatientWithdrawalRaw.lean`, `DeadlineWithdrawalRaw.lean`,
`DeadlineWithdrawalSecurityMixedPointwise.lean`,
`DeadlineWithdrawalRestartPointwiseCore.lean`, and
`DeadlineWithdrawalSecurityLP.lean` in that same directory.

### 6.4 Entire weight sets, traps, pair and crossed selections

The only premium trap is all4: the only above-own participant row of i is
its incoming40 pair, forcing closure under the predecessor cycle. For
every nonzero w>=0, exact singleton sums are

    sum_d sum_i w_i*[r_i({d,i})-s_i]=8*sum_i w_i>0,
    sum_d sum_(i!=d)w_i*[r_i({d,i})-r_i(d)]
                                  =15*w0+w1+9*w2+w3>0.  (14)

Thus the entire upper-average and weighted insertion-leave sign selections
fail, including weights with zeros. The unweighted singleton insertion-leave
sums are(8,2,3,13), contradicting
`QuittingTrapChargeCoefficients.leave_nonpos`
in `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`
before any quantitative charge threshold. At background012 the inserted
own-premium vector is(-11,-11,-11,-23), excluding every nonzero nonnegative
global floor weighting. Participant premiums across the four cycle pairs
sum to19*sum_i w_i>0. These are distinct subtractions, not interchangeable
notions of leave gain.

Every player has both an incoming40 premium and an outgoing-1 deficit,
excluding both participant-at-most-own protection and participant-at-least-own
common-leaver protection. Every pair has a negative participant joining gap;
every triple contains such a gap. Hence every pair partition fails its
two-positive-join row and every triple fails its six-positive-join rows.

For any owner i and partner p choose j in{i+1,i+2} distinct from p. At the
sole-sure outsider j and partner hazard0, the owner's actual residual is

    r_i({i,j})-r_i(j)=-1-r_i(j)<=-5.

Even the weak lower crossed face therefore fails for every pair and height.
This uses `QuittingCrossedSourceGuards`
in `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseGuards.lean`
and `QuittingOneSidedWeakUnitGuards`
in `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.

### 6.5 Other carrying and calendar architectures

The negative passive poles have field directions+e1,+e2, both with mixed
inverse images under(13). The positive passive pole has field direction-e3,
whose inverse image is strictly negative. No actual growing coordinate
has a positive carrying inverse direction. This defeats the literal
single-signed-column and selected-signed-column-cone hypotheses. A full
signed inverse also fails because columns1 and2 remain mixed under either
sign. The positive-inverse participatory-coalition jackpot hypotheses fail
both their inverse prerequisite and their pole-membership prerequisite.
An unused positive column is not a pole in this raw table.

Paired-singleton calendar sources have two equal negative off-diagonal
entries in each row, an identity absent here even after positive row scaling
and terminal row translation. The explicit local four-joint box has own
levels near1 with radius at most1/2, whereas these levels are10. No claim
is made about an unspecified larger local radius.

For the strict scalar singular-circuit ladder, its two favorite inequalities
force three consecutive labels0->3->1 on the only above-own participant
cycle, and A2>0 forces label2 to follow label1. Its singleton guards need
negative incoming Gamma entries at three consecutive receivers. Here the
incoming entries at receivers0,1,2,3 are(-3,-1,7,7); only two are negative.
Every relabeling therefore fails those literal guards.

For completeness, an all-small positive leading scale q=M^-1*w is impossible
on this family when a>=1/4. Let r=w3/w2>0 and Y=w2>0. The leading equations
force w1=(3+1.5r)*Y and

    Y*[2+4.5r-4a*(1+r)*(3+1.5r)]=10+7.5r.

The bracket is at most-1-1.5r^2<0, a contradiction. This only excludes
that all-small scale. It does not exclude stationary Nash, the macroscopic
branch proved here, or unknown pointwise scale-thick applications.

## 7. Narrow Lean handoff

Represent the60 raw rewards, the eight guards and the three pole parameters
as finite input. Define the polynomial system by the literal opponent-set
sum(5), substitute(6), and prove its polynomial extension and limit(7).
The only new analytic ingredients are the quadratic ratio lemma, its strict
derivative, the four Schur pivots and compact-parameter IFT production.
The output must include actual hazards in(0,1), H=0 and the actual value
Q=B/(1-alpha); a merely displayed continuation is insufficient.

The existing stationary endpoint compiler then supplies full terminal Nash
and the same-profile uniform-payoff conclusion. Unrestricted behavioral
response coverage for this constructed profile is proved in Section4.
Completeness of a stationary strategy family for arbitrary games, exhaustive
raw table classification, a fixed target across distinct games, and
conjecture closure are not claimed.
