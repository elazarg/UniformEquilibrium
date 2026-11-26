# Uniform equilibrium from a joint three-player step and a finite return

This raw linear/quadratic criterion constructs exact finite-period equilibria
beyond the positive quiet-player joining barrier of two-player return tests.
An exact five-date example lies outside the complete stationary/sure-first
selection sets and the audited earlier raw producers. It is ordinary
mathematics, not checked in Lean. Arbitrary Fin4 remains open.

## 1. A finite raw triple-root producer

Four players independently choose Quit/Continue at each live date,
the first nonempty coalition D absorbs at finite original reward r(D), live
and Never pay zero, and a deviation is a complete behavioral replacement.
Write kappa_i=r_i({i}) and Z_i(D)=r_i(D)-kappa_i for nonempty D. Original own
levels are arbitrary. Set Gamma_ij=Z_i({j}), so Gamma_ii=0.
Row shifts are justified by the opponents-only absorption
proof below, not by treating the live reward as shifted.

Assume k,h,g>0, A>g and c>0. Define the other raw quantities by

    Gamma02=-beta, Gamma32=e, Gamma20=f, Gamma03=k,
    Gamma23=-h, Gamma13=-g, Z0(02)=-s,
    Z2(02)=f+eta, Z1(13)=-A, Z2(23)=c.

The quantities beta,e,f,s,eta may have either sign. Set d=-Gamma30, w=Z3(02), v=Z3(23), a3=Z3(03), t3=Z3(023), and
omega=w+d-e. These entries may have either sign. Require zeta0=Z0(03)<k.
First solve the raw linear equation

    J0+J1*b=0,
    J0=e*a3+d*v, J1=e*(t3-a3)-(omega+e)*v !=0.       (1)

Retain b=-J0/J1 only if

    0<b<1, D=d-omega*b!=0, x=e*b/D in(0,1).

Put C=b*(beta-s)/(1-b) and T=x*eta/(1-x). These are algebraic
bases, not required to be positive; the actual continuations are tested below.

Define the following raw numbers, whose superscript 3 means that player3
quits at the joint date:

    Q0=-s*b, Q2=x*(f+eta),
    Q0^3=(1-b)*zeta0+b*Z0(023),
    Q2^3=(1-x)*c+x*Z2(023),
    a0=zeta0-k+b*[Z0(023)-Z0(23)]/(1-b),
    a2=c+h+x*[Z2(023)-Z2(03)]/(1-x).

Consider the polynomial of degree at most two

    W(lambda)=(C-k+lambda*a0)*(Q2+h+lambda*(Q2^3+h))
               -(T+h+lambda*a2)*(Q0-k+lambda*(Q0^3-k)).       (2)

Require W to be nonzero and select a positive real root lambda. There are at
most two roots to test. Put

    z=lambda/(1+lambda),
    X0=(Q0+lambda*Q0^3)/(1+lambda),
    X2=(Q2+lambda*Q2^3)/(1+lambda),
    U0=C+lambda*a0, U2=T+lambda*a2,
    tau=(U0-X0)/(k-X0).

Require X0<k, 0<tau<1, U0>0 and U2>0. Let P1=sum_(nonempty S subset{0,2,3}) w_q(S)*Z1(S), where w_q(S)
is the independent quitting-coalition probability at hazards (x,0,b,z), and
H=(1-x)(1-b)(1-z). Define

    X1=(P1-g*tau*H)/[1-(1-tau)*H],
    U1=-g*tau+(1-tau)*X1=-j, X3=U3=0.             (3)

The denominator is positive. Require X1,X2>0 and the wash condition

    U2>=c*max(j,0)/A.                              (4)

Finally let B=max(-X0,0), H0=k-max(zeta0,0), and require

    H0>0,
    B/(H0+B) < min(tau, X1/(X1+g), X2/(X2+h+c)).   (5)

Choose a in this explicit open interval. Set Z1(12)=-K. For S contained in
{0,2,3}, let w_q(S) be its independent quitting probability under (x,b,z).
The explicit observer threshold is

    K >= 1 + sum_(nonempty S !={2})
                    w_q(S)*max(Z1(S union{1}),0)
                      /[(1-x)*b*(1-z)].            (6)

Every other reward is arbitrary finite; in particular Z2(12) is unrestricted.
All selected roots and thresholds depend only on fixed raw entries other than K.

THEOREM. These finite tests produce an exact finite-period terminal Nash
profile and an original uniform-equilibrium payoff, against every complete
behavioral deviation. The construction uses one joint023 date, a solo3 prefix,
and a finite solo3 wash/return. No continuation or cycle is supplied as input.

## 2. Exact equations and the literal return

At hazards (x,0,b,z), player3's passive sum and Quit offer do not depend on z.
The physical substitution x=e*b/D gives P3=0, while direct substitution gives

    Q3=b/D * [J0+J1*b]=0.

Thus X3=U3=0 makes player3 exactly indifferent. Literal owner0 and owner2
indifference gives respectively U0=C+lambda*a0 and U2=T+lambda*a2; their
current Quit values are the displayed X0,X2. Equation (2), after division by
1+lambda, says

    (U0-k)(X2+h)=(U2+h)(X0-k).

Together with (3) this is the complete-vector identity

    U=tau*G+(1-tau)*X, G=(k,-g,-h,0).              (7)

The joint-date quiet1 Quit offer is strictly negative by (6), below X1>0.
Every joint comparison is now proved. The prefix solo3 hazard a has current
Y=aG+(1-a)X. Conditions (5) give Y0,Y1,Y2>0, Y2>ca, and
Y0>a*max(zeta0,0). These are all its quiet comparisons; owner3 is indifferent.

If j<=0, U1>=0 and (7) gives a direct return from U to Y with aggregate
solo3 mass (tau-a)/(1-a). Its row0,row2 endpoints are positive and its row1
endpoints nonnegative. Subdivide the mass into finitely many positive hazards
small enough that each q*c<min(U2,Y2) and
q*max(zeta0,0)<min(U0,Y0). All solo3 comparisons follow.

If j>0, identity (7) and prefix positivity imply

    U0-k*j/g=(1-tau)*(X0+k*X1/g)
             =(1-tau)*(Y0+k*Y1/g)/(1-a)>0.

Since U0<k, this also gives j<g. Starting from U=(U0,-j,U2,0), use regular
solo3 hazard v/A at a current (s,-v,y,0). The conditions
0<v<g, s>kv/g and y>=cv/A make it legal: quiet1's joining offer is -v,
quiet2's is cv/A, and quiet0's offer is zeta0*v/A<kv/A<s. Its successor is

    v'=v*(A-g)/(A-v),
    s'=(s-k*v/A)/(1-v/A), y'=(y+h*v/A)/(1-v/A).

The same conditions persist. With R=1-g/A, after n regular roots the
survival is S_n=1-j/g+(j/g)*R^n and

    v_n=j*R^n/S_n, y_n=[U2+h*(1-S_n)]/S_n.

A finite n makes y_n>=c*v_n/g, since it suffices that
R^n<=(g*U2+h*j)/[(c+h)*j]. A final hazard v_n/g then reaches

    V=((U0-k*j/g)/(1-j/g),0,(U2+h*j/g)/(1-j/g),0).

All its comparisons hold, and V0,V2>0. Along (7), its affine parameter is
sigma=X1/(X1+g)>a. Hence aggregate mass (sigma-a)/(1-a) connects V to Y.
Subdivide it using the same positive row0,row2 endpoint bounds. Quiet1's
annotations are nonnegative and its joining reward -A is negative.
This closes a literal finite period.

At its joint date every deviator faces opponents-only absorption at least
rho=min(x,b)>0. Under every behavioral deviation, survival after n periods
is at most (1-rho)^n. Thus annotations equal actual terminal payoffs and
unrolling the one-date comparisons caps every complete deviation, including
Never. Original own levels add kappa to both sides. Finite expected
opponents-only absorption time makes terminal versus T-horizon average
payoff errors O(1/T), uniformly over deviations. The fixed profile and fixed
payoff kappa+Y therefore satisfy the original uniform-equilibrium contract.

## 3. An exact five-date certificate

Take eta=12281660/12608823 and the following complete native table, with
K>=2 and arbitrary p. The row1 full-coalition entry is -9. Pure023 is excluded by
player2's -100 versus its -5 Continue offer.

| D | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
|0|0|2|2|-1|
|1|3|0|-2|-2|
|2|-1|1/2|0|1|
|3|3|-3|-1|0|
|01|0|-1|-10|-12|
|02|-1/10|5|2+eta|-219/29|
|12|-12|-K|p|-6|
|03|-20|3|-5|1|
|13|2|-100|-1|10|
|23|-100|9|3|-100|
|012|-20|6|-100|11|
|013|-20|8|10|-10|
|023|-20|-8|-100|987|
|123|-8|11|2|1|
|0123|-5|-9|-100|21/2|

The linear equation (1) gives exactly

    b=319/1066, x=319/3475.

After multiplication by a positive rational, (2) is

    -7528736073788085780*lambda^2
      +1458905088176045923*lambda-61079706181272=0.  (8)

Its values at 1/25000 and 1/23000 have opposite signs, negative then
positive; its derivative is positive throughout that interval. Select its
unique root there. This supplies an exact algebraic number, not a numerical
existence premise. Evaluate the formulas (2)--(3) at that root and put

    a=1/20, q=3/100,
    q_f=(100*j-9)/291,
    q_r=[X1/(X1+3)-1/20]/(19/20).

Repeat exactly these five hazard vectors:

    (0,0,0,a), (x,0,b,lambda/(1+lambda)),
    (0,0,0,q), (0,0,0,q_f), (0,0,0,q_r).            (9)

For a direct rational verification, interval-evaluate the displayed formulas
on lambda in [1/25000,1/23000], with exact fraction arithmetic, endpoint
addition, the minimum/maximum of four products, and reciprocal [l,u] mapped
to [1/u,1/l] only when zero is excluded. This gives the strict rational bounds

    -.031<X0<-.030, .310<X1<.312, .272<X2<.274,
    .384<U0<.386, .097<U2<.099,
    .142<j<.145, .136<tau<.138.                    (10)

All decimals here are exact decimal rationals. Every denominator excludes
zero. The bounds can also be checked directly by clearing positive
polynomial denominators on the stated short rational interval.

They imply all five-date comparisons as follows. At the prefix, Y0,Y1>0
and Y2>3a. At the joint root owners0,2,3 are exactly indifferent. For quiet1,
all positive Quit terms divided by (1-x)b(1-z) sum to at most

    6*x/(1-x)+19*lambda < 2/3+19/23000 <1.

Here x<b and x<1/10. Thus K>=2 satisfies the raw threshold (6), and the
joint quiet1 comparison is strict. At the first wash q=3/100, quiet1's
offer -3 is below -j, quiet2's offer .09 is below U2, and quiet0 has positive
value and negative joining offer. Its successor has debt
v=(j-.09)/.97>0 and row2 value (U2+.03)/.97>v. The next hazard q_f=v/3
therefore legally makes row1 zero. Its successor is exactly

    V0=(U0-j)/(1-j/3)>0,
    V1=V3=0, V2=(U2+j/3)/(1-j/3)>.144.

The final q_r lies in (0,1), obeys 3q_r<.14<V2, and closes to Y by
(7). Row0 is positive with negative joining offer, and row1's joining offer
is negative. All remaining comparisons are strict. Thus (9) is an exact
five-date terminal Nash profile. Its original uniform target lies in

    kappa + ((.12055,.1215), (.1445,.1464), (.2084,.2103), 0).

The interval endpoints are rational; the profile and target are fixed for
each table. At K=1000,p=0 all active hazards, all quiet comparisons and
all root-selection brackets are strict. Equations (1) and (8) have simple
selected roots, so the five-date construction persists in an open
neighborhood of all sixty original terminal rewards. Under perturbation
keep a=1/20 and q=3/100, and use
q_f=(j-g*q)/(g*(1-q)) and q_r=[X1/(X1+g)-a]/(1-a). The radius is
existential. The same argument applies at any fixed K>=2 and finite p.

## 4. It crosses the formerly mandatory guard

Keep the table above but regard t=Z3(023) as variable. The two-owner joint02 return cubic, derived by setting player3's joint
hazard to zero, is

    (10b-3)*(71659209b^2-1272539233b-210147050)/126088230.

Its quadratic factor is negative throughout 0<b<1. Thus its only
physical root is b0=3/10, x0=87/947. At that root,

    Q3_join=b0/D0 *[-99+b0*(t-19029/29)].

Its zero is t0=28599/29<987, so at t=987 the old quiet3 guard fails strictly.
Changing the passive row0 entry Z0(23) from -6 to -100 does not affect any
of those old raw quantities because that coalition was never prescribed.
The new active3 date uses a nearby b at which BOTH its passive and joining
values are zero, and its extra odds solve the exact return quadratic.

The new example has a strictly negative owner0 annotation X0, positive
player3 mixing at the joint date, and a literal finite return. It is not
just a relabeling of the old quiet3 comparison. Section6 gives the complete stationary/sure-first exclusions and the
comparisons over the full selection sets of the audited raw producers.

## 5. A sharp limitation of simply adding player3

In any finite exact period with one proper joint023 date and otherwise
proper solo3 dates, at least one with positive hazard, mixed3 at a solo3
date forces its successor native value to zero. Along the intervening solo3
arc, row3 values multiply by positive survival factors. Both ends of the
joint date therefore have row3 value zero. If player3 also mixes properly
there, necessarily P3=Q3=0. In particular, adding positive q3 while keeping
old x,b fixed cannot repair a strictly positive old quiet3 joining offer.
The exact necessary second zero is equation (1), since after P3=0

    Q3=b/D * [e*Z3(03)+d*v
          +b*(e*(Z3(023)-Z3(03))-(omega+e)*v)].

The present producer changes x,b and the return, as this obstruction requires.
It makes no claim about arbitrary multiple-joint-date architectures.

## 6. Nonredundancy over complete raw selection sets

Use the complete Section3 table at p=0, K>=1000 and all original own levels1.
The comparisons below quantify over every selector and weight in the named
raw families. They do not concern unspecified maximal neighborhoods of older
local theorems or all conceivable nonstationary equilibrium mechanisms.

### 6.1. Entire stationary and sure-first selection sets

For independent hazards q, write

    H_i = product_(j!=i)(1-q_j),
    P_i = sum_(nonempty S excludes i) w_q(S) Z_i(S),
    Q_i = sum_(S excludes i) w_q(S) Z_i(S union{i}),
    F_i = (1-H_i)Q_i-P_i,
    L_i = min({-1} union {Z_i(S): nonempty S excludes i}),
    G_i = Q_i-P_i-H_i L_i.

The four lower caps are L=(-100,-8,-10,-12). The entry Z0(23)=-100
sets the row0 pure-Never lower cap.
Every actual continuation best-response cap, after own-level subtraction,
is at least L_i, because playing Never gives a mixture of passive terminal
rewards and original Never zero, whose native level is -1.

A stationary Nash profile requires F_i<=0,=0,>=0 respectively for
q_i=0,0<q_i<1,q_i=1. AllNever is not Nash since each player can obtain 1.
At a sure-quitter full-response Nash root, G obeys the corresponding
signs as a necessary condition. Only a unique sure quitter can have H_i>0;
replacing that quitter's actual continuation cap by its LOWER bound L_i
weakens its necessary Quit comparison. With two sure quitters all H_i=0.
Thus this audit includes arbitrary actual punishment tails and all their
possible continuation caps, not merely stationary tails.

The exact K variations are

    F1(K)=F1(1000)-(K-1000)(1-H1)(1-q0)q2(1-q3),
    G1(K)=G1(1000)-(K-1000)(1-q0)q2(1-q3).

Whenever the final factor need not vanish, a quiet row1 is omitted and an
active/sure row1 is weakened to its baseline >=0 inequality. Otherwise its
baseline sign is retained. This enlarges the necessary set for all K>=1000.

At the fixed eta of Section3, the exact calculation below excludes all80
nonzero stationary patterns in692 nodes and all65 sure-root patterns
in167 nodes, uniformly for K>=1000 and p=0. No eta-interval conclusion
is asserted. Construct F,G at K=1000 by the displayed coalition formulas,
then apply the stated row1 relaxation for every K>=1000.

After fixed-coordinate substitution, every polynomial has degree at most2
in each remaining variable. For p(x)=sum_m a_m x^m, use tensor degree2
Bernstein coefficients

    B_k=sum_(m<=k) a_m product_i binom(k_i,m_i)/binom(2,m_i),
    k in{0,1,2}^d.

Clear a common positive denominator. Reject a box when an equality has a
strictly common coefficient sign or an inequality has its forbidden strict
coefficient sign. Reject any box inside its excluded origin cube. Otherwise
bisect the least-subdivided player coordinate, with index-order ties and
left-child first. A one-axis subdivision uses

    (a,b,c) -> (4a,2(a+b),a+2b+c),
               (a+2b+c,2(b+c),4c).

The shortcut q0=0, mixed q2, q1+q3>0 is valid because
Q2=q3(3-q1)>=0 and P2=-2q1-q3+2q1q3<0. For a sole mixed owner j with no sure owner, choose
quiet witness i=3,2,0,2 for j=0,1,2,3 respectively:
Gamma_ij<min(0,Z_i(ij)) gives F_i=q_j[q_j Z_i(ij)-Gamma_ij]>0. None uses
the potentially omitted row1.

For every remaining mixed set S of size at least2, including faces with
a sure owner, let V=Gamma_SS inverse. Add the V linear combinations of
the mixed baseline polynomials. Their signs are equalities unless row1
was relaxed; then each sign is that of its row1 coefficient in V.

When no owner is sure, write F_S=-Gamma_SS q+R. Every monomial of R has
player-degree at least2. The relevant V column for a relaxed row1 is
nonnegative, so q=VR or q<=VR. If c_i is the sum of absolute coefficients
of R_i, put D=max_i sum_j |V_ij|c_j. Any nonzero solution satisfies
||q||_infinity>=1/D. The exact origin constants are:

| S | D | E with 2^-E<1/D |
|---|---:|---:|
|01|1/2|1|
|02|18749653/12608823|1|
|03|20/3|3|
|13|100/3|6|
|012|807394756907/147102935|13|
|013|1695|11|
|023|471667122912/105073525|13|
|0123|36782401198133/735514675|16|

The other no-sure mixed faces are directly excluded. No origin box is
silently accepted or discarded without this nonzero-solution bound.
The exact finite traversal closes every remaining box.

A stationary approximate-terminal-equilibrium sequence for a fixed table
also cannot escape this census. A nonzero hazard limit satisfies the
excluded F signs. At zero hazard limit normalize hazards by their sum.
Immediate-Quit and Never comparisons give Gamma x>=0 and complementarity
on every positive limiting coordinate if at least two coordinates are
positive. A singleton support violates the negative entry in each column.
A larger support would satisfy Gamma_SS x_S=0, contradicting the nonzero
principal determinants below. Hence each fixed table has positive
stationary regret floor; no uniform floor over K or all-strategy gap is
claimed.

Consequently stationary-output raw producers, including signed single-column
jackpots, boundary inverse-column jackpots, positive-inverse coalition
jackpots and applicable weighted-collision stationary producers, cannot
cover this family at any selection or asymptotic threshold. Sure-first
producers with actual full caps are separately excluded by the 65-pattern
census. This inference uses their output classes rather than guessing an
unspecified numerical threshold.

### 6.2. All 24 older joint/solo return role assignments

The finite-core, direct finite-return, finite-singleton-split, signed-d
finite-core, signed-e direct and signed-h no-wash direct refinements all
retain the necessary conditions

    beta=-Gamma[new0,new2]>0, f=Gamma[new2,new0]>0,
    k=Gamma[new0,new3]>0, g=-Gamma[new1,new3]>0,
    c=Z_new2({new2,new3})>0.

The complete first-failure table over all24 permutations is:

| Role tuple | Failure | Role tuple | Failure |
|---|---|---|---|
|0123|passes screen|1023|beta=-1/2|
|0132|beta=-3|1032|f=-2|
|0213|beta=-3|1203|beta=-2|
|0231|beta=-3|1230|f=-2|
|0312|beta=-3|1302|beta=-2|
|0321|c=0|1320|beta=-1/2|
|2013|k=-1|3012|f=-3|
|2031|k=-2|3021|beta=-1|
|2103|beta=-2|3102|g=-1/2|
|2130|g=-2|3120|beta=-1|
|2301|beta=-2|3201|k=-2|
|2310|c=-1|3210|f=-3|

Thus only identity survives even after BOTH e and h signs are relaxed.
The potentially new signed-h orientation 2310 has c=Z1(01)=-1; the
signed-d/e alternative 0321 has c=Z2(12)=0.

Identity has D=1+219b/29 and x=29b/(29+219b). Its shared raw cubic is
eta(b)=eta, where

    eta(b)=-(3b-1)(73b-1450)(190b+29)
                  /[29b(219b^2-1030b-1160)],
    eta(b)-eta=-(10b-3)(71659209b^2-1272539233b-210147050)
                  /[434787b(219b^2-1030b-1160)].

The denominator never vanishes on 0<b<1, and the quadratic is strictly
less than -1200880024b-210147050<0 there. Hence b=3/10 is the ONLY physical
root, already before imposing any other admissibility test; x=87/947.
At that root quiet3 has current value zero but Quit offer

    Q3=x(1-b)-100(1-x)b+987xb
      =9b(1066b-319)/(219b+29)=108/4735>0.

Every listed joint/core/direct refinement retains this Bellman inequality.
All therefore fail at every possible selected root. The exact old threshold
is Z3(023)<=28599/29, and 987 exceeds it by 24/29. Changing Z0(23) has
no effect on these identity root equations.

Finite singleton split independently fails its required
Z2(02)<=Gamma20: here 2+eta>2. No alternative core length, hazard choice,
K threshold or role assignment repairs that raw premise.

Positive recipient rescalings preserve every sign test and multiply the
identity quiet3 offer by a positive scalar. The cubic zeros and physical
hazards remain unchanged. Thus such rescalings do not repair the failures.

### 6.3. Earlier singleton chambers and fixed-matrix premium classes

The eight-sign template beta,d,e,f,k,h,g,d1>0 permits only identity.
Indeed beta,f,k,g>0 leave 0123,0321,2310; orientation0321 has d=-2,
and2310 has h=-2. Thus all older stronger orientations are exhausted.
The singleton-entrance raw criterion has the necessary condition B1>0.
Its identity values are

    C=5/4, b=5/9, a=5/14, L0=2/7,
    A10=25/28, J=7/8, B1=b*(1/2)-(1-b)*J=-1/9.

Its required B1>0 fails; positive recipient scaling multiplies B1 by its
positive row1 scale. The negative-pair outer return criterion requires
the same signs and in addition Gamma10=-n<0. Identity instead
has Gamma10=2. Neither obstruction depends on any higher reward.

The fixed-matrix positive/negative wedge and premium reference classes fix

    Gamma_ref=[0,3,-1,3;2,0,1,-3;2,-2,0,-1;-1,-2,1,0].

Only identity can match the sign pattern. Matching Gamma10=2 fixes row1
scale to1, but then candidate Gamma12=1/2 differs from required1.
Equivalently Gamma12/Gamma10 equals1/4 instead of1/2, an invariant under
positive row scaling. This excludes every exact reference family with
that matrix, including its unbounded pair-premium and diffuse-core reward
parameters, over all labelings and positive row scalings.

As throughout these comparisons, exact reference-class mismatch does not bound
the maximal neighborhood of a theorem with an unspecified existential
perturbation radius. No such neighborhood membership or exclusion is
asserted. In particular the displayed old outer construction retains
B1>0, which this table violates, but that is not a radius computation.

### 6.4. The broader positive-continuation producer

The positive-continuation variant permits arbitrary singleton signs and
arbitrary solo joining rewards, but requires
X0=b R0>0 and X2=x R2>0 with b,x>0. Its chosen pair must therefore have
BOTH participants' native pair rewards strictly positive. The complete
unordered-pair list is

    01:(0,-1), 02:(-1/10,37499306/12608823), 03:(-20,1),
    12:(-K,0), 13:(-100,10), 23:(3,-100).

Every pair fails. Two orders per pair and two assignments of the remaining
roles give all 24 choices, so this is a complete existential-selector
exclusion independent of any cubic-root choice. Its scalar solo3 endpoint
classification alone is not a raw-table producer and is not counted as
one. Another construction would have to produce new endpoints and roots.

### 6.5. Weighted, matching, matrix and premium selectors

For any nonnegative weight w, put

    H_S=sum_i w_i Z_i(S),
    J_S=sum_(i outside S) w_i[Z_i(S+i)-Z_i(S)].

Full-proper-payoff ledgers require nonnegative H on every nonempty proper
coalition. But H12+H1 has coefficients (-9,-K,-2,-8), strictly negative
against every nonzero nonnegative w. This excludes every weight, finite
family of weights, and marked-orientation ledger requiring those rows.

For support-filtered ledgers requiring singleton H>=0 and joining J<=0,
the changed exact expressions are

    J02=w1+(28842/29)w3,
    4H2+H1-3J02=(-1,-1,-2,-86468/29) dot w.

The right side is strictly negative for every nonzero w. Support filters and arbitrary numbers of weights cannot repair these
necessary rows. For universal forced-Quit-floor weights, with
k(S)_i=Z_i(S+i),

    k(01)+k(2)=(-1/10,-K-1,-100,-110),

again strictly negative for every nonzero nonnegative weight. This also
excludes the global inserted-reward floor used by the compared weighted
trap-leaver criterion.

The unique mutually positive reciprocal singleton pair is 01 and the
unique mutually negative pair is 13. They intersect. Thus the no-negative-
pair, two-disjoint-positive-pair, two-negative-pair and signed-four-cycle
raw templates fail. A legal Hamiltonian adjacent cycle would require four
opposite-sign reciprocal edges; the opposite-sign edge graph has vertex1
of degree1 (only edge12), so there is no such cycle. This also excludes the
negative-opposite-chord Hamiltonian and larger-eigenvalue signed-cycle
criteria, not merely one cycle orientation.

Every matching fails a necessary positive pair joining increment:

    01|23: Z0(01)-Gamma01=-3;
    02|13: Z1(13)-Gamma13=-97;
    03|12: Z0(03)-Gamma03=-23.

Hence the finite-invariant-cone pair criterion fails before any of its
1300 weight-dependent coefficient tests; no proof-weight matrix V helps.
Every principal triple contains one of these failing pairs (012 contains01,
013 contains01/03/13, 023 contains03, 123 contains13), excluding the
compared good-subset criteria that require those increments throughout.

The attached-negative-pair ten-sign template has exactly one role tuple,
(3,1,0,2). Its selected negative pair is original13, where one participant
premium is Z1(13)=-100, contradicting the nonnegative premium condition.
The broader BOTH_JOINT_PREMIUMS_ARBITRARY template allows that premium but
requires the formerly unused nonnegative singleton h; at this orientation
h=Gamma01=3 while m=Gamma21=-2, so the required h,m>=0 fails. This exhausts
all role choices before its remaining cap or inverse tests.

The exact singleton principal determinants are

    pair01,02,03,12,13,23: -6,2,3,1,-6,1;
    triple012,013,023,123: 7,-3,5,7;
    full: 35/2.

The full inverse is

    [2/5,2/7,12/35,9/35;
     1/5,2/7,-9/35,2/35;
     4/5,6/7,-6/35,48/35;
     2/5,0,1/5,2/5].

Only principal triple023 has a nonnegative inverse; its outside inverse
row is (-7/10,9/10,-1/5). All four passive-inverse child choices fail.
The actual full nonnegative-inverse theorem also requires negative
full determinant, whereas det Gamma=35/2>0; BOTH its determinant and
inverse conditions fail. The mixed column at2 prevents ANY assignment
of signs to inverse columns from making the full inverse strictly positive.
This excludes the signed all-column criterion over its entire sign set.
Do not confuse this with signed SINGLE-column jackpot producers: columns0
and3 are positive, but those producers are separately excluded by their
stationary output, as above.

Every singleton column has at least one positive off-diagonal entry, so
no pivot has an all-negative incoming child column. In particular the
sole inverse-positive child's incoming column is (3,-2,-2). Thus all
compared raw cyclic-child choices requiring that column fail.

The only premium trap is123, with all-positive participant vector(11,2,1).
Here 'premium trap' means every member has SOME positive participant premium
on a contained coalition, not necessarily on one common coalition. The
claim follows from the literal table: player0 has no positive participant
premium anywhere; no pair is a trap; 123 is a trap. Thus the greatest
premium core is exactly123. The witness also directly violates product-low
and every normalized supportwise participant balance on that support.

The weak joining-attractive core fails at
Z1(12)-Gamma12=-K-1/2<0. The triple joining gaps at123 are(2,3,7), so every
labeling fails the two zero gaps required by the weak mixed-sign triple
criterion. The mixed-trap leave sum at T=12 is
Z3(123)-Z3(12)=7>0, contradicting the mandatory negative leave bound.
None of the changed coordinates enters these tests.

The positive singleton graph is strongly connected. For example its edges
include 2->3->0->1 and 1->0->2, with arrows giver->recipient. The passive
singleton caps for ordered anchor-block criteria force every nonempty marked
set to be predecessor-closed, hence all four players. The first block that
meets123 then has strictly positive participant sum on123 for every choice
of strictly positive block weights. All marked sets, block orders, and
weights fail. For the calendar-polytope criterion with two marked owners,
every two-element marked set meets123 and its first meeting block already
has strictly positive participant sum. No calendar polytope choice can
repair that earlier cap failure.

A scalar singular circuit requires three distinct recipients with a
positive native pair premium at a negative singleton mate. The complete
eligible (recipient,mate) list here is (2,3),(3,0),(3,1). Only two distinct
recipients qualify. Every scalar-circuit relabeling therefore fails.

The below-own witnesses Z0(02), Z1(13), Z2(012), Z3(23) defeat the
protected-return lower bounds in the compared criteria. Player0 separately
has nonpositive participant premiums on all containing coalitions; these
are different conditions.

### 6.6. All 14 children and all five withdrawal operations

For child C, outside player o and nonempty A subset C, every compared
certificate implies the relaxed inequalities

    F_A: -Z_o(A) <= sum_(i in C) lambda_i[-Z_i(A)]
                      +sum_(i in C) mu_i max(W_i(A),0),
    J_A: Z_o(A+o)-Z_o(A)
             <=sum_(i in C) lambda_i[Z_i(A+i)-Z_i(A)]
                      +sum_(i in C) mu_i W_i(A),

with lambda,mu>=0, and
W_i(A)=Z_i(A-i)-Z_i(A) if i in A and A!={i}, and zero otherwise.
The child-specific coordinate order in the table below is increasing.

The source definitions `WithdrawalFutureJoinKind.gain`, `.futureWeight`,
and `WithdrawalFutureJoinRewardCertificate.future_row` and `.join_row`
are defined in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
They cover patient, deadline, evaluated-security, terminal-security and
cancellation withdrawals. Own singleton is1. Patient floor is bounded by
its own-Never alternative max(1,0)=1, terminal-security floor by own
singleton1, and deadline/cancellation/evaluated-security floors are
nonpositive. Hence every singleton withdrawal gain is <=0. Nonsingleton
gains are exactly W; the future gain is W or0. Replacing it by max(W,0)
and replacing singleton gain by0 ENLARGES every actual feasible set.
The Never row is omitted, weakening it further. Advancing-only capped
clock certificates are included by mu=0.

Sum the indicated rows with their positive coefficients. Exact substitution
gives the following exhaustive Farkas contradictions:

| C | o | Combination | LHS | lambda coefficients | mu coefficients |
|---|---:|---|---:|---|---|
|0|2|J0|eta|(0)|(0)|
|1|2|J1|2|(0)|(0)|
|2|0|J2|9/10|(0)|(0)|
|3|1|F3|3|(0)|(0)|
|01|2|J0|eta|(0,-3)|(0,0)|
|02|1|J02|1|(0,0)|(-9/10,-eta)|
|03|1|F3|3|(-3,0)|(0,0)|
|12|0|F2|1|(-1/2,0)|(0,0)|
|13|2|J3|4|(-97,0)|(0,0)|
|23|0|J2|9/10|(0,-101)|(0,0)|
|012|3|3F0+3F1+10J2+67J02|1903385/29|(0,56-10K,0)|(-603/10,0,-67eta)|
|013|2|J3|4|(-23,-97,0)|(0,0,0)|
|023|1|F0+F2+2F3|7/2|(-5,0,0)|(0,0,0)|
|123|0|J123|3|(0,0,0)|(-2,-3,-7)|

Every LHS is strictly positive and every RHS coefficient is nonpositive
for K>=1000. This excludes ALL nonnegative lambda,mu choices, not one
selected child equilibrium. The old child012 LHS433/58 becomes

    433/58 + 67*(987-15/2) = 1903385/29,

while all its RHS coefficients remain unchanged. The lowered Z0(23) does
not weaken any listed Farkas combination. Every one of the 14 proper
nonempty children has an excluded outside row, so no ordering of successive
raw child lifts can repair these premises. An arbitrary strategically
selected child-specific lift outside these raw certificates remains outside
the claim.


## 7. Source correspondence and formalization

The raw linear equation produces b, the quadratic supplies at most two odds
candidates, and the remaining explicit inequalities select legal data. All
continuation values, probabilities, finite wash length, and return subdivision
are produced. No strategic witness remains assumed.

The complete Bellman interface is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`). The semantic
consumer is
`quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
Section2 supplies their needed exact payoff and complete-deviation content,
including proper opponent absorption and one fixed original target.

The withdrawal comparisons use `WithdrawalFutureJoinKind.gain`,
`WithdrawalFutureJoinKind.futureWeight`,
`WithdrawalFutureJoinRewardCertificate.future_row`, and
`WithdrawalFutureJoinRewardCertificate.join_row`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`),
with `patientWithdrawalFloor_le_ownNeverAlternative`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalRaw.lean`).
The advancing specialization uses `rawChild_future_delta`, `rawChild_future_base`,
`rawChild_joining_delta`, and `rawChild_joining_base`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockOriginalCoalitionRows.lean`).

The matrix/core comparison declarations include
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`),
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse`
(`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`),
`IsSupportwiseBalancedQuittingPremiumTable`
(`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`),
`HasWeakJoiningAttractivePremiumCore`
(`UniformEquilibrium/Quitting/Classification/JoiningAttractiveCorePassivePerturbation.lean`), and
`HasWeakMixedSignTripleJoining`
(`UniformEquilibrium/Quitting/Classification/MixedSignTripleCorePassivePerturbation.lean`).
These existing interfaces are distinguished from the new producer, which
has not been checked in Lean.

Formalization requires finite linear/quadratic root selection, the exact
three-owner Bellman equations, finite solo wash/return identities, and the
rational interval certificate. Its five-date probabilities remain literal;
negative annotations cannot be separated from their scheduled joint roots
by empty dates. The new construction removes a reward region whose two-owner
quiet-player guard fails strictly. It does not eliminate every residual
singleton cell or global source case, and it does not solve arbitrary Fin4.
