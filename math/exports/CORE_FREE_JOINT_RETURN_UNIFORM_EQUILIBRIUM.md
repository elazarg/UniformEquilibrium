# Uniform equilibrium from a joint quitting step and a direct finite return

This theorem constructs exact periodic equilibria from explicit reward tests.
It covers a complete unbounded positive joining-excess region, including an
exact five-date example. It is ordinary mathematics, not checked in Lean.
Arbitrary four-player quitting games remain open.

## 1. Raw theorem

Players0,1,2,3 independently choose Continue or Quit at each live date.
The first nonempty quitting coalition D absorbs at the finite vector r(D),
paid thereafter. Live play and literal Never pay zero. Strategies use private
independent randomization; a deviation may replace the entire behavioral law.
Put kappa_i=r_i({i}), Z_i(D)=r_i(D)-kappa_i on nonempty coalitions, and
Gamma_ij=Z_i({j}), Gamma_ii=0. Own levels kappa are arbitrary independently.

Assume the six strictly positive singleton coefficients

    beta=-Gamma02, e=Gamma32, f=Gamma20,
    k=Gamma03, h=-Gamma23, g=-Gamma13.

Put d=-Gamma30, n=Gamma10 and ell=Gamma12; these and all other singleton
entries are arbitrary real numbers. Require

    A=-Z1(13)>g, c=Z2(23)>0,
    Z0(02)=-s with s<beta, Z2(02)=f+eta with eta>0,
    zeta0=Z0(03)<k.

Let w=Z3(02), v=Z3(23). There is no sign assumption on w,v or Z3(13).
For a variable b define

    D=d-b*(w+d-e), T0=k-b*(k+beta-s),
    F=f*e*T0-h*(beta-s*b)*D,
    P_eta(b)=F*(D-e*b)-eta*e*b*((beta-s*b)*D+e*T0).     (1)

Require P_eta to be a nonzero polynomial with a real root b satisfying

    0<b<1, D>0, x=e*b/D in(0,1),
    C=b*(beta-s)/(1-b) in(0,k), T=x*eta/(1-x).         (2)

The root need not be simple. Define the raw rational quantities

    P1=x*(1-b)*n+(1-x)*b*ell+x*b*Z1(02),
    L=k*(1-x)*(1-b)/(k+s*b),
    A10=(k*P1-s*b*g)/(k+s*b),
    j=[g*C-A10*(k-C)]/[k-L*(k-C)],
    X1=P1-(1-x)*(1-b)*j, X2=x*(f+eta), B=max(s*b,0).

Require

    j<g*C/k, T>=c*max(j,0)/A,                        (3)
    X1>0, H=k-max(zeta0,0)>0,
    L_a=B/(H+B)<U_a=min((C+s*b)/(k+s*b),
                         X1/(X1+g),X2/(X2+h+c)),     (4)
    x*(1-b)*Z3(03)+(1-x)*b*v+x*b*Z3(023)<=0.           (5)

All displayed denominators are positive. Indeed k+s*b>b*(k+beta)>0 and

    (k+s*b)*[k-L*(k-C)]
      =k{b*(k+beta)+x[k-b*(k+beta-s)]}>0.

Choose Z1(12)=-K with the explicit bound

    K>=K_*:=1+[x*(1-b)*max(Z1(01),0)+x*b*max(Z1(012),0)]
                      /[(1-x)*b].                   (6)

Every other higher reward is arbitrary finite, including Z2(12)=p with no
restriction on its sign or magnitude. Then there is an exact finite-period
terminal-payoff Nash equilibrium, and its payoff is an original uniform-
equilibrium payoff against all complete behavioral deviations. Only one
joint02 date and finitely many solo3 dates are used; player1 always Continues.

This is a finite raw test: a nonzero cubic has at most three real roots.
Testing all roots and the displayed inequalities produces a witness when
the class is satisfied. No strategy, continuation value, or cycle is assumed.
The construction below supplies every such object.

## 2. The joint root and exact affine return

Let

    X=(-s*b,X1,X2,0), U=(C,-j,T,0),
    tau=(C+s*b)/(k+s*b) in(0,1), G=(k,-g,-h,0).

Equation(1) is precisely the row2 identity in

    U=tau*G+(1-tau)*X.                               (7)

The definition of j gives its row1 identity; row0 is immediate. Also
0<tau<1, since C+s*b=b*(beta-s*b)/(1-b)>0 and C<k.
At a joint02 root with hazards(x,0,b,0) and successor U, owner0's Quit
and Continue values both equal -s*b. Owner2's values both equal x*(f+eta),
because T=x*eta/(1-x). The current quiet3 value is zero since x=e*b/D;
its Quit offer is the left side of(5). Quiet1's current value is X1>0.
Its Quit offer is

    x*(1-b)*Z1(01)-(1-x)*b*K+x*b*Z1(012)<0

by(6). Thus this root satisfies every immediate deviation comparison.

The interval in(4) is computed entirely from the raw rewards and the selected
cubic root. Select its midpoint
a=(L_a+U_a)/2. The solo3 root of hazard a and successor X has current

    Y=a*G+(1-a)*X.

Its coordinates Y0,Y1,Y2 are strictly positive, Y3=0 and Y2>c*a. Quiet0's
Quit offer is strictly below Y0: for s*b>0 this follows from a>L_a;
for s*b<=0 the difference from a*max(zeta0,0) is
-(1-a)*s*b+a*H>0. Quiet1's offer is -A*a<0 and quiet2's is c*a.
Owner3 is indifferent. This legal finite prefix is adjacent to the joint02
root; no empty date is inserted at X0 when that coordinate is negative.

## 3. The exhaustive return construction

If j<=0, all quiet coordinates of U are nonnegative, with U0,U2>0. By(7)
and a<tau, solo3 total mass (tau-a)/(1-a) connects U to Y. Its row0,row2
annotations interpolate between positive endpoints; row1 annotations are
nonnegative. Subdivide the aggregate into finitely many sufficiently small
hazards q with c*q<min(U2,Y2). All root comparisons are exact: joining
reward for quiet1 is -A<0; quiet0 has current value at least k*q>zeta0*q
since its successor is nonnegative; and owner3 has value zero.

Suppose j>0. By(3),

    0<j<g, C>k*j/g, T>=c*j/A.

Here is an explicit finite wash from U. At current(s0,-v0,z0,0) satisfying
0<v0<g, s0>k*v0/g and z0>=c*v0/A, use solo3 hazard v0/A. Quiet1's offer
is exactly -v0, quiet2's is c*v0/A<=z0, quiet0 has positive value and a
offer zeta0*v0/A<k*v0/A<s0, and owner3 is indifferent. Exact affine inverse transport
gives a successor obeying the same conditions. With r0=1-g/A in(0,1), after
m regular roots the survival and values are

    S_m=1-j/g+(j/g)*r0^m,
    v_m=j*r0^m/S_m,
    s_m=[C-k*(1-S_m)]/S_m,
    z_m=[T+h*(1-S_m)]/S_m.

Choose the least nonnegative integer m such that

    r0^m<=[g*T+h*j]/[(c+h)*j],

and then use final hazard v_m/g. This is a finite raw recipe: the positive
right side is fixed and r0^m tends to zero. The final hazard is legal because
z_m>=c*v_m/g and s_m>k*v_m/g>zeta0*v_m/g. It reaches

    V=((C-k*j/g)/(1-j/g),0,(T+h*j/g)/(1-j/g),0).

Equation(7) implies V=tau1*G+(1-tau1)*X, where tau1=X1/(X1+g)>a.
Thus solo3 total mass (tau1-a)/(1-a) connects V to Y. Subdivide it so that
every c*q<min(V2,Y2). Its quiet0,row2 values are positive, quiet1 values
nonnegative; quiet0 again has current value at least k*q>zeta0*q. All
comparisons are exact. The initial weak wash guard
T=c*j/A causes no problem; a subsequent regular root makes it strict.

In both cases the period is the finite prefix3, the joint02 root, the return
from U (including its wash when needed), and back to Y. Every probability
is produced from the raw table and every finite root is legal.

## 4. Complete deviations and the original uniform-payoff conclusion

At the joint02 date, each player faces opponent absorption at least
rho=min(x,b)>0. Under any complete unilateral behavioral deviation this
bound holds each period. Therefore policy and all deviating laws absorb
properly, with expected absorption time at most L_period/rho+1.

The exact first-action comparisons are full Bellman inequalities. Unrolling
over a period makes the supremum D of the complete deviation gain satisfy
D<=(1-rho)*D, hence D=0. This includes literal Never and arbitrary
history-dependent behavioral replacements. The displayed annotations equal
actual terminal payoffs by proper absorption. The resulting target is Y.

Adding original own levels kappa shifts both prescribed and deviating terminal
payoffs because opponents absorb under every deviation. If original rewards
are bounded by R, the discrepancy between terminal payoffs and T-horizon
average payoffs is at most2R*(L_period/rho+2)/T uniformly over deviations.
The fixed profile and fixed target kappa+Y consequently satisfy the uniform-
equilibrium contract.

## 5. A complete unbounded joining-excess region

Fix

    Gamma=[0,3,-1,3;2,0,1/2,-3;2,-2,0,-1;-1,-2,1,0],
    Z0(02)=-1/10, Z1(02)=5, Z3(02)=-219/29,
    Z1(13)=-100, Z2(23)=3, Z3(23)=-100,
    Z3(03)=1, Z3(023)=15/2, Z0(03)<=0.

All other higher rewards are arbitrary finite. Write Z2(02)=2+eta,
Z1(12)=-K and Z2(12)=p. Then EVERY

    eta>=305713711170/4725703339153,
    K>=1+max(Z1(01),0)+max(Z1(012),0), p in R          (8)

has the equilibrium just constructed. The eta threshold is approximately
0.06469168486. No relation between p,K,eta is imposed beyond(8).

For an exact verification, parametrize b in(0,1/3) by

    eta=-(3b-1)(73b-1450)(190b+29)
             /[29b(219b^2-1030b-1160)],
    x=29b/(29+219b), C=9b/[10(1-b)],
    T=-(3b-1)(73b-1450)/(219b^2-1030b-1160),
    j=-3(4294b^2+2567b-870)/[2(b-1)(7629b+2030)],
    X1=(1504b^2-161b+2610)/[2(7629b+2030)],
    X2=-(132b^2-3553b+1450)/(219b^2-1030b-1160).

The eta map decreases bijectively from infinity to zero. Its derivative is
-N(b)/[b^2(219b^2-1030b-1160)^2], where

    N=4820409b^4-5552526b^3+37637420b^2+2987000b+1682000>0.

Positivity follows by combining the cubic and quadratic terms on b<=1/3.
Here zeta0<=0, so H=k and L_a=B/(k+B)<tau. The remaining
interval bounds and strict guards follow from

    C-j=-3(13b-10)(109b-435)/[10(b-1)(7629b+2030)]>0,
    3X2-4b/10=-(438b^3-80b^2-55615b+21750)
                  /[5(219b^2-1030b-1160)]>0,
    Q3_join=-3b(12541b+1914)/[2(219b+29)]<0,
    j'=3(43625749b^2+4159180b+10082140)
                  /[2(b-1)^2(7629b+2030)^2]>0,
    T'=-783(949b^2-1460b+8460)/(219b^2-1030b-1160)^2<0.

The numerator in the second line decreases and is positive at1/3. The other
signs are immediate on(0,1/3). At b=331/1000,
j-100T/3=-5546944652414753/1500285581257994157<0. Thus condition(3) holds throughout b<=331/1000, exactly the
eta tail(8). Finally x/[(1-x)b]<=1 and x/(1-x)<=1, so the bound on K in(8)
makes the quiet1 joint offer strictly negative uniformly in eta.

## 6. An exact five-date instance and full-dimensional stability

Use the following complete native table, with eta=12281660/12608823,
K>=1 and arbitrary p. Original own levels kappa remain arbitrary.

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
|23|-6|9|3|-100|
|012|-20|6|-100|11|
|013|-20|8|10|-10|
|023|-20|-8|-100|15/2|
|123|-8|11|2|1|
|0123|-5|-9|-100|21/2|

Here b=3/10 and x=87/947. Repeat the exact hazards

    (0,0,0,1/20), (87/947,0,3/10,0), (0,0,0,3/100),
    (0,0,0,525873/29323973), (0,0,0,22221/476821).

The corresponding current values are

    Y=(243/2000,66663/454600,607433/2898580,0),
    X=(-3/100,134853/431870,39598/144929,0),
    U=(27/70,-42984/302309,14281/144929,0),
    B=(207/679,-1577619/29323973,1862887/14058113,0),
    V=(12069/47210,0,104816681/684209809,0).

At each solo3 date, next=(current-q*(3,-3,-1,0))/(1-q) exactly. The quiet
row0,1,2 margins over their Quit offers -20q,-100q,3q are respectively

| current | row0 | row1 | row2 |
|---|---:|---:|---:|
|Y|2243/2000|2339663/454600|86323/1449290|
|U|69/70|863943/302309|123739/14492900|
|B|19457169/29323973|525873/302309|334524762032/4249894082917|
|V|5663169/4768210|2222100/476821|925082854/69105190709|

All are strictly positive. At the joint date, owners0,2 are exactly indifferent
by(2), quiet3's offer is -510867/18940, and quiet1's margin at K=1 is
98899146/204490445>0, increasing with K. Every equality and inequality is
therefore checkable by rational arithmetic. No unknown threshold is used.
The exact original uniform-equilibrium payoff is kappa+Y.

An open neighborhood in all60 original terminal rewards has five-date exact
periodic equilibria. To prove this, the cubic root is simple because the
eta derivative displayed above is nonzero at b=3/10, and the coefficient
of eta in(1) is nonzero under(2). The implicit function
theorem selects nearby b,x,U,X from nearby raw rewards. Keep prefix hazard
1/20 and first wash hazard d0=3/100 fixed. Set the second wash hazard to
(j-g*d0)/(g*(1-d0)), making its successor row1 value zero; set the final
return hazard to(V0-Y0)/(k-Y0). All probabilities remain proper, all active
equalities hold by the affine construction, and every quiet comparison
persists by the strict margin table. The original-to-native change is affine
in all60 rewards; own-level changes are permitted by opponent absorption.

## 7. Exact separation from previous existence producers

### Stationary and sure-root exclusions on 0<=eta<=2

Use the complete canonical native table, with p=0, K>=1000,
Z2(02)=2+eta and original own levels all1. Every native entry is fixed
except the indicated K,eta coordinates. For independent hazards q define

    H_i=product_(j!=i)(1-q_j),
    P_i=sum_(nonempty S subset opponents) w_q(S)Z_i(S),
    Q_i=sum_(S subset opponents) w_q(S)Z_i(S union{i}),
    w_q(S)=product_(j in S)q_j product_(j outside S,i)(1-q_j),
    F_i=(1-H_i)Q_i-P_i,
    L_i=min({-1} union {Z_i(S): nonempty S excludes i}),
    G_i=Q_i-P_i-H_i L_i.

Here L=(-12,-8,-10,-12). Stationary Nash requires signs <=0,=0,>=0
for F_i according as q_i=0, q_i is proper mixed, or q_i=1. AllNever is
not Nash because each own singleton is1. Every actual continuation
best-response cap, after native row subtraction, is at least L_i: playing
Never averages passive rewards and original Never0, whose native value is
-1. At a root with one sure quitter only that quitter has possibly positive
H_i, and lowering its continuation to L_i weakens its necessary Quit
comparison. With multiple sure quitters every H_i=0. Thus the same sign
system for G is necessary for every sure-quitter full-response Nash root with actual
continuation best-response caps, including arbitrary punishment tails.

The following fully rational finite calculation excludes these systems.
Set eta=2t, t in[0,1], and construct F,G at K=1000 by the displayed finite
coalition formulas. Enumerate all80 nonzero patterns in{0,1,*}^4 for F and
all65 patterns containing1 for G. The only K dependence is

    F1(K)=F1(1000)-(K-1000)(1-H1)(1-q0)q2(1-q3),
    G1(K)=G1(1000)-(K-1000)(1-q0)q2(1-q3).

If q2=0, q0=1 or q3=1, retain the baseline signs. Otherwise replace the
mixed/sure row1 condition by baseline >=0, and omit row1 when quiet.
These are weaker necessary conditions at every K>=1000.

For F discard immediately q0=0, q2 proper mixed, and q1 or q3 positive:
Q2=q3(3-q1)>=0 while P2=-2q1-q3+2q1q3<0. A lone mixed owner j with no
sure owner is excluded by a quiet i with Gamma_ij<min(0,Z_i(ij)); choose
respectively i=3,2,0,2 for j=0,1,2,3. Its F_i=q_j[q_jZ_i(ij)-Gamma_ij]>0.
The relaxed row1 is not used in this shortcut.

For each remaining mixed set S of size at least2, set A=Gamma_SS and
V=A^-1. Add the V linear combinations of the mixed baseline polynomials.
They have equality signs unless row1 was relaxed, in which case their
signs are those of that row's coefficients. Without a sure owner the
mixed vector equals -Aq+R(q,t), with every term of R of player-degree at
least2. Then q=VR, or q<=VR if row1 is relaxed; the latter uses the
nonnegative relevant inverse column V[:,1]. If c_i is the absolute sum of
coefficients of R_i, including its t powers, then

    D=max_i sum_j |V_ij|c_j,
    nonzero solution => ||q||_infinity>=1/D.

The exact constants and excluded closed origin cubes are:

| Mixed S | D | E with 2^-E<1/D |
|---|---:|---:|
|01|1/2|1|
|02|2|2|
|03|20/3|3|
|13|100/3|6|
|012|192287/35|13|
|013|1695|11|
|023|690532/725|10|
|0123|157713489/5075|15|

The other no-sure mixed sets12,23,123 were directly excluded.

After fixed-coordinate substitution, every retained polynomial has degree
at most2 in each remaining coordinate, including t. For p(x)=sum_m a_m x^m
use tensor degree2 Bernstein coefficients

    B_k=sum_(m<=k) a_m product_i binom(k_i,m_i)/binom(2,m_i),
    k in{0,1,2}^d.

Clear a common positive denominator. Reject a box if an equality has a
strictly common coefficient sign, or an inequality has its forbidden strict
coefficient sign. Also reject a box inside its excluded origin cube.
Otherwise bisect the player coordinate subdivided least often, resolving
ties by player index, and process the left child first. Keep t in[0,1];
if no mixed player remains, subdivide t. Exact one-coordinate subdivision,
with common positive scaling, is

    (a,b,c) -> left(4a,2(a+b),a+2b+c),
                right(a+2b+c,2(b+c),4c).

A shortcut counts as one node. This specified calculation terminates with
1486 nodes for all80 stationary patterns and209 nodes for all65 sure-root
patterns. No box survives. The data, origin bounds and arithmetic rules
suffice to reproduce it; no numerical search is a logical premise.

For each fixed table a stationary approximate-equilibrium sequence would
have a convergent hazard subsequence. A nonzero limit satisfies the excluded
F signs. At a zero limit normalize hazards by their sum to obtain x>=0,
sum x_i=1. Immediate quitting gives Gamma x>=0; the Never comparison gives
x_i(Gamma x)_i=0 whenever both i and an opponent have positive limiting
weight. A singleton support violates the negative entry in every column;
a larger support S would satisfy Gamma_SS x_S=0, impossible because all
principal determinants are nonzero. Thus each fixed table has a positive
stationary regret floor as well. This does not exclude nonstationary UE.

For the explicit five-date example eta=12281660/12608823 lies in(0,2).
At its unique admissible cubic root b=3/10,

    j-100T/3=-413038598492/131440023183<0.

The preceding finite-positive-entrance producer requires the opposite
strict inequality, and therefore fails on the whole K ray. It has no
alternative root: admissibility requires0<b<10/13, and eta>0 then forces
b<1/3; eta(b) decreases strictly there. Its eight singleton signs permit
only the identity among24 player labelings. Even omitting its Gamma30 sign
adds only labeling(0,3,2,1), where the required positive c becomes
Z2(12)=0 and fails. Positive recipient scalings
preserve the sign of j-A*T/c. The earlier nonpositive-excess return also
fails because eta>0. 
The remaining comparisons below hold for every eta>0, with p=0 and K>=1000.
They cover the full finite or weighted selection domains of the named raw
criteria, not unspecified maximal neighborhoods of older local theorems or
every possible nonstationary verifier.

For any nonnegative weight define

    H_S=sum_i w_i Z_i(S),
    J_S=sum_(i notin S) w_i[Z_i(S union{i})-Z_i(S)].

All full-proper-payoff ledgers fail: H_12+H_1 has coefficient vector
(-9,-K,-2,-8), strictly negative for every nonzero nonnegative weight.
All support-filtered ledgers requiring singleton H>=0 and joining J<=0
fail: J_02=w1+(873/58)w3, and4H_2+H_1-3J_02 has coefficients
(-1,-1,-2,2-2619/58), all negative. Arbitrary numbers of weights or
support filters cannot change this obstruction. Universal forced-Quit-floor
weights fail because, with k(S)_i=Z_i(S union{i}),
k(01)+k(2)=(-1/10,-K-1,-100,-110).

The unique mutually negative reciprocal pair is13 and the unique mutually
positive pair is01. They intersect. This excludes the no-negative-pair,
two-disjoint-positive-pair, two-negative-pair and signed-four-cycle templates.
Every pair partition fails a required positive joining increment:
01|23 at Z0(01)-Gamma01=-3; 02|13 at Z1(13)-Gamma13=-97;
03|12 at Z0(03)-Gamma03=-23. Every triple contains one such failing pair.
No invariant-cone weight or good-subset selection repairs these prerequisites.
The attached-negative-pair template has only labeling(3,1,0,2); its joint
premium condition fails at Z1(13)=-100. Its variant allowing arbitrary joint
premiums requires an unused singleton to be nonnegative, here Gamma21=-2.

The principal determinants in pair order01,02,03,12,13,23 are
(-6,2,3,1,-6,1), in triple order012,013,023,123 are(7,-3,5,7), and the
full determinant is35/2. Exact inversion gives

    Gamma^-1=[2/5,2/7,12/35,9/35;
               1/5,2/7,-9/35,2/35;
               4/5,6/7,-6/35,48/35;
               2/5,0,1/5,2/5].

Only principal triple023 has nonnegative inverse, and its outside inverse
row is(-7/10,9/10,-1/5). All passive-inverse child choices fail. The full
inverse has a mixed column, excluding nonnegative-inverse and all-positive
signed-column criteria. The sole inverse-positive child's incoming pivot
column is(3,-2,-2), defeating the raw cyclic-child templates requiring that
column to be all negative. These are exact selector comparisons, not claims
about unspecified maximal neighborhoods of local theorems.

The premium trap123 has positive participant vector(11,2,1). No player is
protected: witnesses below own level are Z0(02),Z1(13),Z2(012),Z3(23).
The greatest premium core is exactly123. Its weak joining-attractive test
fails at Z1(12)-Gamma12=-K-1/2; its three triple joining gaps are(2,3,7),
so the weak mixed-sign triple test's two zero gaps fail under all labelings.
The mixed-trap leave sum at12 is Z3(123)-Z3(12)=7>0. Supportwise participant
balance and product-low fail at123. The positive singleton graph is strongly
connected, so predecessor-closed nonempty marked sets are all four players;
the first ordered block meeting123 then has positive participant sum. This
also defeats the two-marked calendar-polytope criterion, since every such
marked set meets123. A scalar singular circuit requires three distinct
recipients with positive pair premiums at negatively valued singleton mates;
only players2,3 can qualify here.

### Every proper child in the five withdrawal families

The following exact Farkas witnesses cover all14 nonempty proper children,
including advancing-only capped-clock specializations. For child C, outsider o
and nonempty A subset C, every such raw certificate implies the relaxed rows

    F_A: -Z_o(A) <= sum_(i in C) lambda_i[-Z_i(A)]
                      +sum_(i in C) mu_i max(W_i(A),0),
    J_A: Z_o(A+o)-Z_o(A)
             <=sum_(i in C) lambda_i[Z_i(A+i)-Z_i(A)]
                      +sum_(i in C) mu_i W_i(A),

where lambda,mu>=0 and W_i(A)=0 if i notin A or A={i}, otherwise
W_i(A)=Z_i(A-i)-Z_i(A). For all five kinds, the singleton withdrawal gain
is <=0: its relevant floor is at most own singleton1 (the patient own-Never
alternative is also1; cancellation and evaluated-security floors are
nonpositive). Non-singleton gains equal W. A future coefficient is either
the gain or0 and is bounded by max(W,0). Hence these relaxed rows enlarge
every feasible set. Sum the listed rows with the indicated positive weights:

| Child | Outsider | Combination | Positive left side |
|---|---:|---|---:|
|0|2|J_0|eta|
|1|2|J_1|2|
|2|0|J_2|9/10|
|3|1|F_3|3|
|01|2|J_0|eta|
|02|1|J_02|1|
|03|1|F_3|3|
|12|0|F_2|1|
|13|2|J_3|4|
|23|0|J_2|9/10|
|012|3|3F_0+3F_1+10J_2+67J_02|433/58|
|013|2|J_3|4|
|023|1|F_0+F_2+2F_3|7/2|
|123|0|J_123|3|

Every right-side coefficient is nonpositive, a contradiction. For child012
its advance coefficients are(0,56-10K,0) and withdrawal coefficients
(-603/10,0,-67eta). For023 they are(-5,0,0) and(0,0,0); for123 they
are(0,0,0) and(-2,-3,-7). All other rows are direct singleton/pair
substitutions. This tests every child and every nonnegative proof weight;
it does not exclude an arbitrary child-specific strategic lift.

The source definitions are `WithdrawalFutureJoinKind.gain`,
`WithdrawalFutureJoinKind.futureWeight`, and
`WithdrawalFutureJoinRewardCertificate.future_row` and `.join_row`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`),
with `patientWithdrawalFloor_le_ownNeverAlternative`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalRaw.lean`).
The advancing specialization is `rawChild_future_delta`,
`rawChild_future_base`, `rawChild_joining_delta`, `rawChild_joining_base`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockOriginalCoalitionRows.lean`).

The matrix and premium comparisons use
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
These comparisons and the complete exclusions above establish new raw-table
coverage; they do not claim that every conceivable nonstationary mechanism
fails on the example.



## 8. Source correspondence and formalization

The raw cubic and interval tests produce all probabilities and continuation
values. The sign and size split in Section3 is exhaustive for this class;
no strategic certificate is assumed. In particular the p coordinate is
absent from every executed root and every unilateral deviation comparison.

The full Bellman interface is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`). The exact terminal
profile is consumed by
`quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
Its hypotheses are supplied in Section4, including arbitrary complete
behavioral deviations and the fixed target. These citations identify existing
interfaces; the new reward producer is ordinary mathematics, not Lean-checked.

Formalization needs finite rational root selection, the direct wash and
return identities, literal periodic Bellman inequalities, and the displayed
five-date rational certificate. No infinite-core limit or interval-arithmetic
existence computation is required. Negative annotations must remain adjacent
to their scheduled roots; a compiler that inserts empty dates or demands a
singleton floor throughout does not apply. The theorem removes a reward region,
including an entire unbounded joining-excess tail, rather than a complete
arbitrary-game residual source case. Arbitrary Fin4 remains open.
