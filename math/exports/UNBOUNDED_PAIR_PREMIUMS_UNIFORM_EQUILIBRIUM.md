# Uniform equilibrium with two unbounded pair premiums

This packet constructs uniform equilibria in two unbounded regions of a
two-parameter reward family. The proof allows independent private choices
and every unilateral behavioral deviation. It is ordinary mathematics;
arbitrary signed four-player quitting games remain open.

## 1. Raw family and conclusion

There are four players 0,1,2,3. At each live date they independently choose
Continue or Quit. The first nonempty quitting coalition D absorbs and pays
r(D); live play and literal AllNever pay zero. Write kappa_i=r_i({i}) and
Z_i(D)=r_i(D)-kappa_i for nonempty D only. Thus native own-singleton rewards
are zero. A string such as 123 denotes the coalition {1,2,3}.

Fix the following entries, with real parameters K and p:

| D | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
| 0 | 0 | 2 | 2 | -1 |
| 1 | 3 | 0 | -2 | -2 |
| 2 | -1 | 1 | 0 | 1 |
| 3 | 3 | -3 | -1 | 0 |
| 12 | -12 | -K | p | -6 |
| 13 | 2 | -100 | -1 | 0 |
| 23 | -6 | 9 | 3 | -100 |
| 123 | -8 | 11 | 2 | 1 |

Require Z0(D)<=0 for the seven nonsingleton coalitions containing0. The
21 entries Z_i(D), i=1,2,3, on those seven coalitions are arbitrary independent
real numbers. All four kappa_i are arbitrary real numbers. These conditions
specify every coordinate: 30 fixed native entries, two variable parameters,
seven independent upper bounds, and 21 other unrestricted native entries.

**Theorem.** Every such game has a uniform-equilibrium payoff whenever
either of the following raw inequalities holds:

    K>=100 and p>=2K;
    K>=0 and p<=-max(200,2K).

These are two-dimensional regions; both rewards can vary independently
without a finite bound, subject to the displayed inequalities. The theorem
does not cover the whole parameter plane. For each given game it constructs
one target W, fixed before accuracy, and for every positive accuracy one
behavioral profile satisfying the payoff and unilateral-deviation bounds
at all sufficiently large finite horizons.

In the negative region every profile delivers its target exactly in
terminal payoff. In the positive region finite calendars converge to their
fixed target. Every constructed profile is periodic with a finite period,
and each deviator faces opponents that absorb almost surely. Period length
and the horizon threshold may depend on accuracy.

## 2. Common finite calendar and complete response control

At a product root q let Q_i be the payoff from Quit now, P_i the passive
payoff from nonempty opponent coalitions, and H_i=product_(j!=i)(1-q_j).
For a successor value v, Continue gives P_i+H_i v_i. A reference annotation
u obeys the Continue identity when u_i=P_i+H_i v_i. If every owner who quits
with positive probability also has Q_i=u_i, the prescribed payoff identity
holds. The full behavioral cap obeys

    B_i=max(Q_i,P_i+H_i B_i(next)).                    (2.1)

Before absorption there is only one surviving public history. A private
behavioral deviation is therefore a law on finite quitting dates and Never;
its payoff cannot exceed their supremum. Equation (2.1) prices that complete
menu, including its infinite-horizon limit.

The outer calendar connects

    A=(0,A1,A2,0) --solo0--> B=(0,B1,0,B3)
      --solo2--> C=(C0,C1,0,C3) --core--> E=(E0,-x,E2,0)
      --solo3 repair--> V=(V0,0,V2,0) --solo3--> A.

Given C and E, set

    b=C0/(1+C0), B1=b+(1-b)C1, B3=b+(1-b)C3,
    a=B3/(1+B3), A1=2a+(1-a)B1, A2=2a,
    R=1-x/3, V0=(E0-x)/R, V2=(E2+x/3)/R, h=V0/3.

The core producers below ensure

    C0>0, B1>0, B3>0, 0<x<3, E0>x, E2>=3x/100,
    0<h<1,
    A1(1-h)=3h, A2(1-h)=V2+h.                       (2.2)

These give 0<a,b<1 and V2>0. The core has the exact active comparisons and
positive row0 annotations, either exactly or in the specified finite limit.
Its row0 forced-Quit offers are nonpositive by the seven raw upper bounds.

For solo0, at cumulative quitting probability u in[0,a] the annotation is

    (0,(A1-2u)/(1-u),(2a-2u)/(1-u),u/(1-u)).

All observer coordinates are nonnegative. Choose 0<delta<1/2 and subdivide
the aggregate a into finitely many conditional hazards at most delta. For
J_i=Z_i({0,i}), the forced-Quit surplus of observer i is at most delta J_i^+.
Every Continue identity and every prescribed identity is exact. There is
no restriction on J_i. At the solo2 root b, its owner is indifferent; row0
has a nonpositive joining offer, while rows1 and3 have offers -Kb and -100b below
their positive annotations B1 and B3, since K>=0.

The repair is finite. At state (s,-v,z,0), a solo3 root q gives successor

    ((s-3q)/(1-q),(-v+3q)/(1-q),(z+q)/(1-q),0).

If 0<v<3, s>=v and z>=3v/100, choose q=v/100. Its quiet comparisons are
legal: row0's offer is nonpositive, row1's is -100q=-v, and row2's is3q<=z.
The successor obeys

    v'=97v/(100-v), z'=(z+v/100)/(1-v/100),
    s'-v'=(s-v)/(1-v/100).

The guards persist. With r=97/100, after n regular roots,

    S_n=1-x/3+(x/3)r^n,
    v_n=x r^n/S_n, z_n=(E2+1-S_n)/S_n.

Take 43 regular roots and then q=v_43/3. The exact inequality
`(97/100)^43<109/400<=(3E2+x)/(4x)` gives z_43>=v_43,
so the last root is legal and sets row1 to zero. Total survival is1-x/3,
and its endpoint is exactly V above. This remains valid at wash equality
E2=3x/100, which is needed at the support transitions.

The final solo3 aggregate h closes the return by (2.2). Its annotations at
cumulative quitting probability u in[0,h] are

    ((V0-3u)/(1-u),3u/(1-u),(V2+u)/(1-u),0).

They are nonnegative. Subdivide h into conditional hazards at most
min(1/2,V2/6). Row2's joining comparison3q<=current2 holds, while all other
quiet joining offers are nonpositive. Every block is finite.

Here is the full error bound used by all the producers. Let the reference
Continue identities fail at at most one root per period, by at most eta in
each coordinate, and let its prescribed identity have residual at most eta.
Every immediate Quit surplus is at most e=delta max(0,J1,J2,J3). Put
rho=min(a,b)>0. Deleted-opponent period survival is at most1-rho: a deviator0
faces solo2, and every other deviator faces the complete solo0 block.
Prescribed survival has the same bound. Subtracting reference annotations
from (2.1), then unrolling the maximum over a period, gives

    B_i-u_i<=e+eta/rho, |U_i-u_i|<=eta/rho,
    B_i-U_i<=e+2eta/rho.                             (2.3)

For the first inequality, if B_i-u_i<=0 there is nothing to prove; otherwise
one period bounds it by max(e+eta,eta+(1-rho)(B_i-u_i)). Quit surpluses
enter a maximum, not a sum. In particular with eta=0 the sharper coordinate
bound is delta(0,J1^+,J2^+,J3^+), irrespective of the number of small roots.

For each selected finite period of length L, the absorption time against any
unilateral replacement is bounded by the opponents-only absorption time,
whose expectation is at most L/rho+1. If M bounds absolute original rewards,
terminal and horizon-N payoffs differ by at most2M(L/rho+2)/N uniformly over
all deviations. Proper opponents also ensure the native translation adds
exactly kappa_i to every terminal payoff, prescribed or deviating. Choose
the core accuracy and delta first, and then a horizon threshold. This proves
the asserted uniform contract at W=kappa+A whenever the core construction
has fixed A and eta tends to zero.

## 3. Positive region: an explicit return and a finite pair approximation

### 3.1. Constructing the return

Compactify the raw parameters by

    u=100/K in(0,1], t=p/(p+K/50) in[100/101,1),
    1/250 <= w <= 11/2500,
    y=u(1−t)/25, zbar=2(1−t)/(2525−106u(1−t)), z=u zbar.

Then Kz=100zbar and py=2t/25. For a free terminal coordinate E set

    L=100zbar+100w−(100zbar+111z)w,
    X=2t/25+3w−(2t/25+y)w,
    T3=−z(100−101y),
    x=[100zbar+z+97w−(100zbar+100z)w]/[(1−z)(1−w)],
    E2=[2t/25+2y+4w−(2t/25+3y)w]/[(1−y)(1−w)],
    ellT=(1−y)(1−z)(1−w),
    baseT=3y−z+3w−14yz−4yw−8zw+13yzw,
    T0=ellT E+baseT.

The triple123 root (0,y,z,w) is actively indifferent with current
T=(T0,−L,X,T3) and successor (E,−x,E2,0). To verify row1, its current Quit
value is −Kz−100w+(K+111)zw, and subtracting its passive numerator
z−3w+11zw gives the stated −x successor. The unchanged row2 and row3
calculations give E2 and0; the latter is equivalent to z=2y/(101−106y).

Put

    S=2/[(2+X)(1+L)], D=100−99t+u(1−t),
    Kchi=50(1−t)SLX/D, pchi=tSLX/D, chi=u Kchi/100,
    pi1=(pchi+SX)/2, pi2=Kchi+SL,
    C3=−2pi1+pi2−6chi+S T3,
    ell=S ellT, base=3pi1−pi2−12chi+S baseT,
    C0(E)=ell E+base,
    K0=−9/2+6x+27E2/2,
    alpha=K0 ell+7C3/4−3/4,
    beta=K0 base+(−15/2+3x+27E2/4)C3+3x+27E2/4,
    E0=−beta/alpha.

In all remaining expressions use E=E0, and write C0=C0(E0), T0=T0(E0).
Define

    F1=(9+6x−9E0)C0+(6+3x−5E0)C3+3x−3E0,
    F2=(6−6E2−4E0)C0+(6−3E2−3E0)C3−3E2−E0.

Direct expansion gives F1−9F2/4=alpha E0+beta=0.

The rational interval algorithm in Section 5.1 checks on
EVERY (u,t,w) in [0,1]×[100/101,1]×[1/250,11/2500]:

    alpha<0, E0>x, C0>0, 0<C3<1, T0>0, L>0, X>0,
    0<x<3, E2>3x/100, 2L>X,
    C0(2+X)/2−3X/2>0,
    C3+[(C3/2+1)X+(C3−1+u)L]/2>0,
    100w−(100+111u)zbar w+101u(1−t)zbar/25
            −101u(1−t)XL/(200t)>0.                  (1)

It also checks F2>0 on w=1/250 and F2<0 on w=11/2500 for the entire
(u,t) rectangle. All formula denominators are positive except alpha,
whose strict negative sign is certified. The interval certificates use
only9,16 and4 accepted boxes for the two endpoint signs and the whole-box
guards respectively, with depths4,4,2. Thus continuity and the intermediate
value theorem produce a root w in the open interval for EVERY physical
K,p. Choose the least such root to fix all parameters before accuracy.
The endpoints u=0 and t=1 serve only as compact proof devices.

At this root set

    b=C0/(1+C0), B1=b, B3=(C0+C3)/(1+C0),
    a=B3/(1+B3), A1=2a+(1−a)b, A2=2a,
    R=1−x/3, V0=(E0−x)/R, V2=(E2+x/3)/R, h=V0/3.

Then F1=F2=0 is precisely

    A1(3−E0)=3(E0−x), A2(3−E0)=3E2+E0.

Since C3<1, A2<1. The second equation gives E0<3/2, so all outer guards
0<a,b,h<1, B1,B3>0, E0>x, V2>0 hold. This constructs the outer return
rather than assuming one.

### 3.2. Every finite pair word is legal

At pair12 hazards (0,c,d,0), the two active current/successor values are

    current1=−Kd, successor1=−(K+1)d/(1−d),
    current2=pc, successor2=(p+2)c/(1−c).

Starting with c0=X/p,d0=L/K, define

    c_n=c_(n−1)/(1+2/p+c_(n−1)),
    d_n=d_(n−1)/(1+1/K+d_(n−1)).

The physical word (c_n,d_n),...,(c_1,d_1) is actively indifferent at every
root and has successor T. For n>=1 both hazards lie in(0,1). Put A=pc_n,
B=Kd_n and D0=(2+X)(1+L). Its exact survival and first-coalition masses are

    S_n=(2+A)(1+B)/D0,
    chi_n=(S_n LX−AB)/(2K+2+p),
    pi1_n=(p chi_n+S_n X−A)/2,
    pi2_n=K chi_n+S_n L−B.

These identities follow from the two active payoff equations and total
probability; they concern actual nonnegative coalition probabilities.
They converge to S,chi,pi1,pi2 above. The two quiet current values are

    U0=3pi1_n−pi2_n−12chi_n+S_n T0,
    U3=−2pi1_n+pi2_n−6chi_n+S_n T3.

Their forced-Quit offers satisfy Q0<=0 and Q3=−100d_n+101c_n d_n.

The actual pair points lie in the triangle

    0<=A<=X, 0<=B<=(L/X)A.                         (2)

Indeed, writing v=(1+2/p)^(-n), zeta=(1+1/K)^(-n),

    A/X=2v/[2+X−Xv], B/L=zeta/[1+L−Lzeta].

The condition p>=2K gives v>=zeta. The first fraction is increasing in v,
and2L>=X gives its value at v=zeta at least the second fraction. This
proves (2), including every intermediate suffix of every finite word.

U0 is bilinear in(A,B). Its four full-rectangle corner values are

    C0, C0(2+X)/2−3X/2, C0(1+L)+L, T0.

All are positive by(1), so U0>0 throughout the rectangle and hence the
triangle. This prices the quiet pivot regardless of the seven allowed
nonpositive joining entries.

For player3 put

    lambda=C3/2, V=(K−p−6)/(2K+2+p), H=101/(pK).

Exact substitution gives

    U3−Q3=lambda(2+A)(1+B)+A−(1−u)B−(V+H)AB.       (3)

At fixed A it is affine in B, so it suffices to check the two boundary
edges of triangle(2). At B=0 it is lambda(2+A)+A>0. At B=(L/X)A,
write s=A/X in[0,1]. The quadratic has Bernstein coefficients

    C3,
    C3+[(lambda+1)X+(C3−1+u)L]/2,
    T3+uL−HXL.

The first two are positive by(1). The last is u times the last expression
in(1), hence is positive for every physical u>0. The equality uses
z=u zbar, y=u(1−t)/25 and H=101u²(1−t)/(200t).
A polynomial with positive Bernstein coefficients is positive on[0,1].
Thus every quiet comparison at every pair root holds, with no bound on
word length and no numerical sampling argument. At the triple root,
T0>0 and Q0<=0 supply its sole quiet comparison.

### 3.3. Realizing the limit with a fixed target

The limiting entrance is C=(C0,0,0,C3). Use the finite n-root pair word
followed by the triple root as the core in Section 2. Let eta_n be the
sup-norm difference between its entrance and C. The exact probability
formulas give eta_n->0. Retain the limiting outer annotations and the exact
finite-core annotations. The only Continue and prescribed residual is at
the solo2 interface, bounded by eta_n in each coordinate. The solo2
row1 Quit offer is -Kb<=0, so its comparison remains valid.

Section 2 now gives full terminal debt at most

    delta max(0,J1,J2,J3)+2eta_n/rho,
    |U_i-A_i|<=eta_n/rho,   rho=min(a,b)>0.

Choose n and delta for accuracy, then the horizon threshold. The target
is W=kappa+A and was fixed when the least return root was selected.

## 4. Negative region: three exact core roots

Put k=-p, s=1/k, u=K/k. The raw assumptions give

    0<s<=1/200,    0<=u<=1/2.

The producer is certified on the larger compact rectangle
[0,1/200] x [0,1/2]. Its s=0 edge is algebraic auxiliary data only.
For scaled core hazards (C,D,w), the physical root is (0,sC,sD,w).
Let c=sC and d=sD. Its active Quit values and required Continue-successor
values are (Q1,Q2,sq3) and (F1,F2,sf3), where

    Q1=-uD-100w+(u+111s)Dw,
    Q2=-C+3w+(1-s)Cw,
    q3=-D(100-101c),
    F1=[-(u+s)D-97w+(u+100s)Dw]/[(1-d)(1-w)],
    F2=[-C+2c+4w+(1-3s)Cw]/[(1-c)(1-w)],
    f3=[2C-101D+106cD]/[(1-c)(1-d)].

These are direct substitutions into the raw product-root formula. The
coefficient u=Ks retains the potentially unbounded raw reward K without taking an
uncontrolled limit.

For variables v=(C,D,U,V,w,Y,t,E0), put

    e=C/[3+(1-s)C],     Z=2Y/[101-106sY],
    roots=(C,D,e), (U,V,w), (Y,Z,t).

The first current row2 is identically zero, and the last successor row3
is identically zero. Impose the six interface equations
(F1,F2,f3)=(nextQ1,nextQ2,nextq3) at both interfaces.
Set x=-F1(last), E2=F2(last). Propagate the row0 value backward from E0 by

    G(c,d,w;r)=3c-d+3w-14cd-4cw-8dw+13cdw
               +(1-c)(1-d)(1-w)r.

Let C0 be its initial value, C1=firstQ1, C3=s firstq3. Set

    b=C0/(1+C0), B1=b+(1-b)C1, B3=b+(1-b)C3,
    a=B3/(1+B3), A1=2a+(1-a)B1, A2=2a,
    R=1-x/3, V0=(E0-x)/R, V2=(E2+x/3)/R, h=V0/3.

The remaining two equations are A1(1-h)=3h and A2(1-h)=V2+h.
Thus F(v;s,u)=0 is an explicit eight-variable rational system.

Section 5.2 constructs a zero of this system for every physical (s,u).
It simultaneously proves strict physical hazards, positive row0 annotations,
and all guards in (2.2), including E0>x and E2>3x/100. Every active core
comparison is an equality; its only quiet player is0, with nonpositive
Quit offer below a positive annotation. The outer solo2 offer -Kb<=0 is
legal even at K=0. Thus the common finite calendar has no interface error,
and Section 2 proves UE with fixed target kappa+A.

## 5. Complete finite arithmetic certificates

All inputs and algorithms are specified here; no external root search or
stored center table is assumed. Every decimal used in this section denotes
its exact rational value. Printed floating-point diagnostics are unnecessary
for acceptance. These calculations certify the displayed rational systems,
not merely finitely many sampled games.

### 5.1. Positive region: rational interval signs

Use exact rational interval addition and negation. For multiplication take
the minimum and maximum of the four endpoint products. For division take
the reciprocal interval and multiply, rejecting a denominator interval
containing zero. Evaluate the formulas of Section 3.1 in their displayed
order, including E0=-beta/alpha and then F2.

Start with the box

    u in [0,1], t in [100/101,1], w in [1/250,11/2500].

For the left endpoint replace the w interval by its left endpoint and test
F2>0. For the right endpoint use its right endpoint and test -F2>0. For
the full box test all fifteen quantities in (1) strictly positive, with
-alpha replacing alpha and 1-C3 replacing C3<1. Specifically the ordered
guard list is

    -alpha, E0-x, C0, C3, T0, L, X, x, 3-x, E2-3x/100,
    1-C3, 2L-X, C0(2+X)/2-3X/2,
    C3+[(C3/2+1)X+(C3-1+u)L]/2,
    100w-(100+111u)zbar w+101u(1-t)zbar/25
                       -101u(1-t)XL/(200t).

A box is accepted only when every tested interval has strictly positive
lower endpoint. Otherwise bisect at the rational midpoint: at depth d
choose dimension d modulo2 for endpoint tests, and d modulo3 for the
full-box test, in the order u,t,w. A rejected division also requires
bisection. Reject the certificate if an unaccepted box reaches depth30.

This complete deterministic procedure accepts9 left-endpoint boxes,16
right-endpoint boxes and4 guard boxes, at maximal depths4,4,2 respectively.
It is a finite rational sign certificate. Every formula denominator is
nonzero on every accepted box, and all boxes cover the initial domains.
Consequently the strict signs used in Section 3 hold for every parameter.

### 5.2. Negative region: one weighted contraction box

Use the eight variables and eight equations in Section 4 in their displayed
order. The parameter rectangle is

    s in [0,1/200], u in [0,1/2], midpoint (1/400,1/4).

The initial rational vector is

    (9/397, 54296564078592426/63070111151171990729,
     573/39409, 654500574858/1572938403151657, 291/39700,
     25581/3912673, 28227/3940900, 4738019/3912673).

For this certificate use outward dyadic interval arithmetic at precision
2^-80: round each lower endpoint down and upper endpoint up after each
operation, with all four endpoint products or quotients, and reject any
division whose denominator contains zero. Differentiate the same rational
expressions by the sum, product and quotient rules in this interval
arithmetic. This encloses values and derivatives on every evaluated box.

At a rational point take interval midpoints of the residual F, its state
Jacobian J and its parameter Jacobian D to obtain rational proposals. Apply
three steps

    c <- round_60(c-J^(-1)F),
    round_60(x)=2^-60 floor(2^60 x+1/2),

starting from the stated seed at the parameter midpoint. Compute matrix
inverses by exact rational Gauss-Jordan elimination, using the first
nonzero available pivot in each column. At the final center c recompute
J,D and put R=J^(-1), z=-RD. Define the rational radii

    rho_i=max((3/2)(|z_i,s|/200+|z_i,u|/2),
              |c_i|/100000, 1/10^10).

These proposal operations select rational data only. Every following
acceptance inequality uses outward intervals, never the midpoint estimates
as exact residuals or derivatives. Let X be the outward enclosure of
c+[-rho,rho], and let P be the entire parameter rectangle.

Enclose the state Jacobian F_v on X times P and put B=I-R F_v. Enclose
F(c;p0) and the parameter derivative F_p(c;P). Form the interval vector

    b=-R F(c;p0)-R F_p(c;P)([-1/400,1/400] times [-1/4,1/4]),
    image_i=b_i+SUM_j B_ij[-rho_j,rho_j].

The parameter segment from p0 to any parameter in P remains in P, so the
mean-value integral justifies the first enclosure. State segments from c
to X remain in X. Thus these intervals enclose T(v)-c for T(v)=v-RF(v;p).
The exact acceptance tests are

    image_i is strictly inside [-rho_i/2,rho_i/2] for every i,
    SUM_j sup|B_ij| rho_j/rho_i < 1/10 for every i.

Also evaluate the model guards on the entire X times P. Require every
quantity below to exceed1/10000:

    a,1-a,b,1-b,h,1-h,B1,B3,x,3-x,E0-x,E2-3x/100,V2;
    all four row0 annotations (E0 and the three preceding core values);
    Cj,Dj,wj,1-sCj,1-sDj,1-wj at all three scaled roots.

All these exact tests pass on the ONE box, without parameter subdivision.
Outward rounding of the proposal center and radii is included in the
evaluations; in the strict tests the radius lower endpoints are used
on the right, making the inequalities conservative. The radius box with
exact rational radii is therefore invariant under T and T is a contraction
in the weighted sup norm. Banach's theorem supplies a unique fixed point
for each parameter. The exact rational R is invertible, so its fixed point
solves F=0. This proves existence, uniqueness in this box, and every stated
guard throughout the rectangle. Only physical s>0 defines strategies;
the algebraic s=0 edge is a compact proof device.

## 6. Coverage and semantic correspondence

The scalar parameter construction fixed Z1(12)=-100. This theorem permits
Z1(12)=-K and Z2(12)=p to vary independently in the two stated unbounded
regions, while retaining the other30 displayed native coordinates and the
free-coordinate conditions. It supplies all strategic data from the raw
rewards. It does not claim arbitrary-table coverage or eliminate either
remaining global-minimum branch.

Here is an exact separating completion of the free entries:

| D | (Z0,Z1,Z2,Z3) |
|---|---|
| 01 | (0,-1,-10,-12) |
| 02 | (0,5,-10,7) |
| 012 | (-13,6,-9,11) |
| 03 | (-3,3,-5,1) |
| 013 | (-7,8,10,-10) |
| 023 | (-7,-8,-3,15/2) |
| 0123 | (-5,-9,8,21/2) |

Take kappa=(1,1,1,1). The points (K,p)=(200,400) and (150,-300)
belong to the positive and negative regions respectively, and both lie
outside the scalar K=100 family, even after relabeling and independent
positive row scaling. Indeed row0 is the unique singleton row with two
equal positive off-diagonal entries, fixing its label; its negative entry
then fixes label2, and the remaining singleton signs fix labels1 and3.
The nonzero singleton entries then force every row scale to be1.
Exact rational exclusion rejects all80
nonzero stationary patterns and all65 sure-root patterns against any actual
continuation cap. Their respective node totals are (5672,729) and (1448,331).
These are two separating examples, not stationary exclusions for the whole
parameter regions. The theorem constructs uniform equilibria for both.

Here is the finite exclusion calculation behind those counts. Write
Gamma_ij=Z_i({j}), Gamma_ii=0, and, for q in[0,1]^4, set

    H_i=product_(j!=i)(1-q_j),
    P_i=SUM_(S subset opponents) weight_q(S) Z_i(S), Z_i(empty)=0,
    Q_i=SUM_(S subset opponents) weight_q(S) Z_i(S union {i}),
    F_i=(1-H_i)Q_i-P_i,
    L_i=min({-1} union {Z_i(S): nonempty S excludes i}),
    G_i=Q_i-P_i-H_i L_i.

Here weight_q(S)=product_(j in S)q_j product_(j outside S,i)(1-q_j).
For this completion L=(-12,-8,-10,-12), at both tested parameter pairs.
Every nonzero stationary equilibrium satisfies F_i<=0 if q_i=0,
F_i=0 if0<q_i<1, and F_i>=0 if q_i=1. These follow by comparing immediate
Quit with Never against stationary opponents. When opponents never quit,
F_i=0 automatically remains a necessary condition. AllNever itself is
excluded by the original own-singleton payoff1.

A root with some q_j=1 that is Nash against any actual continuation cap
also satisfies the same sign conditions for G. Indeed that cap, in native
coordinates, is at least L by its Never option. For every i different
from a sure owner j, H_i=0, so the continuation cap does not affect its
root comparison. For the sole sure owner, lowering its continuation cap
to L can only improve its already optimal Quit action. Thus it is Nash
also at L. This justifies the65-pattern necessary-condition calculation.

Enumerate patterns in{0,1,*}^4, excluding all-zero for F and retaining only
patterns containing1 for G. Substitute fixed coordinates. A pattern with
one free coordinate j and no sure owner is immediately excluded using an
i different from j with Gamma_ij<0 and Z_i({i,j})>=0. Such an i exists
for every j in this completion, including i=3 when j=1 and p<0.
For at least two free coordinates S, the principal singleton matrix
A=Gamma_SS is invertible. Add A^(-1) times the active equalities to the
polynomial list, as additional equalities. If no owner is sure, active
polynomials have form -Aq+R(q), with every term of R of degree at least2.
Let C_i be the sum of absolute coefficients of those terms and
K=max_i SUM_j |(A^(-1))_ij| C_j. The active equalities imply
||q||_infinity<=K||q||_infinity^2. Thus if K=0 the pattern is impossible;
otherwise choose the smallest positive integer E with2^-E<1/K and
exclude every nonzero point in the cube[0,2^-E]^S.

All remaining polynomials have coordinate degree at most2. Convert them
exactly to tensor Bernstein coefficients of degree2 on the unit cube.
Reject a box when any equality polynomial has all coefficients strictly
of one sign, or an inequality polynomial has all coefficients of the
forbidden sign. Otherwise bisect the least-subdivided coordinate, breaking
ties by its increasing player index, by exact de Casteljau subdivision.
Also discard boxes inside the just-proved origin cube. This finite procedure
exhausts every listed pattern with the reported node totals; no branch is
left unresolved. The rational table, coefficient rule and subdivision rule
specify the calculation completely. The claim concerns exact stationary
and sure-root exclusions; they are not counterexamples to behavioral UE.

The singleton matrix is unchanged across K,p. Its positive graph is strongly
connected, and the participant vector on123 is(11,2,1)>0. Hence complete
ordered nonpositive anchor selection fails: any admissible marked set must
be all players, and its first block meeting123 has positive weighted
participant sum. The same positive vector defeats every upper-average
weight on the core. Its upper-face joining charge at12 is still
Z3(123)-Z3(12)=1-(-6)=7>0, so a negative singleton charge when p<0 does not
supply the required mixed-trap criterion. The only inverse-positive
principal triple is023, whose outside inverse row is(-3,6,2)/5. Thus full
passive-child selection fails too. The remaining finite selectors fail as follows. The unique mutually negative
singleton pair is13. Its only labeling satisfying the attached-pair sign
template is(3,1,0,2), where the required nonnegative participant premium is
Z1(13)=-100; the both-premiums-arbitrary alternative instead requires
m=Gamma21=-2 to be nonnegative. For the three invariant-cone pair partitions,
the necessary positive difference Z_i({i,mate})-Gamma_i,mate fails:
01|23 has value-3 at i=0, 02|13 has value-12 at i=2, and03|12 has value-6
at i=0. Hence no proof-weight matrix can repair those prerequisites.
Column2 of Gamma inverse is(9,-6,-3,5)/25, defeating the all-signed-positive
inverse-column criterion under every relabeling and sign choice. Finally,
the unique mutually positive pair01 intersects the unique mutually negative
pair13; the signed four-cycle templates require them disjoint. These
complete finite-choice obstructions establish the coverage increment among
the named mechanisms. They are not an assertion about every conceivable
sufficient equilibrium theorem.

The intended semantic endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
The full response recursion corresponds to
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`). The proof above
also gives its own direct fixed-target finite-horizon argument. These named
sources were inspected; this packet makes no claim of new Lean compilation,
integration, or formal verification. Fin4 for arbitrary tables remains open.

The formalization handoff is the raw-table theorem in Section1. Its proof
factors into the common finite-calendar/full-cap consumer, the positive
region's exact pair entrance and return, and the negative region's three
finite roots. The rational identities, interval signs, dyadic automatic
differentiation and strict acceptance inequalities are finite lemmas to
certify. The intermediate value and Banach arguments then produce roots
for every parameter. No strategic hypothesis remains to be supplied, and
no new Lean compilation or integration is claimed.
