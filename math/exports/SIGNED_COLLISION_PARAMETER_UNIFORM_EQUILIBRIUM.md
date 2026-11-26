# Uniform equilibrium across a signed collision parameter

This packet proves a reward-table class, not the four-player conjecture for
arbitrary rewards. The parameter p below is unrestricted: it may be positive,
zero, or negative. The proof uses independent private choices and prices every
unilateral behavioral deviation. It is ordinary mathematics, not a new Lean
result.

## 1. Raw family and conclusion

There are four players 0,1,2,3. At each live date they independently choose
Continue or Quit. The first nonempty quitting coalition D absorbs and pays
r(D); live play and literal AllNever pay zero. Write kappa_i=r_i({i}) and
Z_i(D)=r_i(D)-kappa_i for nonempty D only. Thus native own-singleton rewards
are zero. A string such as 123 denotes the coalition {1,2,3}.

Fix the following entries, with ANY real p:

| D | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
| 0 | 0 | 2 | 2 | -1 |
| 1 | 3 | 0 | -2 | -2 |
| 2 | -1 | 1 | 0 | 1 |
| 3 | 3 | -3 | -1 | 0 |
| 12 | -12 | -100 | p | -6 |
| 13 | 2 | -100 | -1 | 0 |
| 23 | -6 | 9 | 3 | -100 |
| 123 | -8 | 11 | 2 | 1 |

Require Z0(D)<=0 for the seven nonsingleton coalitions containing0. The
21 entries Z_i(D), i=1,2,3, on those seven coalitions are arbitrary independent
real numbers. All four kappa_i are arbitrary real numbers. These conditions
specify every coordinate: 31 fixed native entries, one unrestricted parameter,
seven independent upper bounds, and 21 other unrestricted native entries.

**Theorem.** Every game in this class has a uniform-equilibrium payoff. For
its given table there is one target W, fixed before accuracy, such that every
positive accuracy admits one behavioral profile satisfying the payoff and
unilateral-deviation bounds at all sufficiently large finite horizons.

For p<=0 the construction delivers its chosen target exactly in terminal
payoff, at every accuracy. For p>0 finite calendars approach a fixed target.
In both cases each profile is periodic with a finite period, and each player
faces opponents that absorb almost surely even if that player never quits.
The period and horizon threshold may depend on accuracy. No finite bound on
period length is imposed uniformly over accuracies.

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
has a nonpositive joining offer, while rows1 and3 have offer -100b below
their positive annotations B1 and B3.

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

## 3. The positive half-line: a growing pair block

At a pair12 root with hazards `(0,c,d,0)`, active indifference prescribes

    current1=-100d,       successor1=-101d/(1-d),
    current2=pc,          successor2=(p+2)c/(1-c).

Fix a successor T with `T1=-L<0<T2=X`. Put

    c_0=X/p, d_0=L/100,
    c_k=c_(k-1)/(1+2/p+c_(k-1)),
    d_k=d_(k-1)/(101/100+d_(k-1)).

For `k>=1` both hazards lie strictly between zero and one. The finite word
`(c_n,d_n),...,(c_1,d_1)` has successor T and exact active indifferences.
Both starting hazards tend geometrically to zero as n tends to infinity.
Its owner survivals and joint survival are exactly

    S1_n=(2+p c_n)/(2+X),
    S2_n=(1+100d_n)/(1+L),
    S_n=S1_n S2_n.

Write `pi1,pi2,chi` for the probabilities of outcomes 1, 2, 12 inside this
finite block. The active payoff identities and total mass give

    chi=(S_n L X-100p c_n d_n)/(202+p),
    pi1=(p chi+S_n X-p c_n)/2,
    pi2=100chi+S_n L-100d_n.                         (1)

In particular these are actual nonnegative probabilities. They converge to

    S=2/[(2+X)(1+L)], chi=S L X/(202+p),
    pi1=(p chi+S X)/2, pi2=100chi+S L.              (2)

The limiting initial value is `C=(C0,0,0,C3)`, where

    C0=3pi1-pi2-12chi+S T0,
    C3=-2pi1+pi2-6chi+S T3.                        (3)

This limit is used only to choose the target and fixed macro parameters.
Every actual strategy below uses a finite n.

### 3.1. A root exists over the whole positive half-line

Set `t=p/(p+2)`, so `0<t<1`, and choose

    y=(1-t)/25, z=2y/(101-106y),
    7/2000 <= w <= 9/2000.

For an auxiliary variable E define

    T1=-100z-100w+211zw, L=-T1,
    T2=py+3w-(p+1)yw = [2t+(74-t)w]/25,
    T3=-z(100-101y),
    x=(101z+97w-200zw)/[(1-z)(1-w)],
    E2=[(p+2)y+4w-(p+3)yw]/[(1-y)(1-w)],
    T0=3y-z+3w-14yz-4yw-8zw+13yzw
       +(1-y)(1-z)(1-w)E.

The triple123 root `(0,y,z,w)` is actively indifferent with current T and
successor `(E,-x,E2,0)`. This follows by direct expansion of all three
forced-Quit and Continue offers.

Compute (2)--(3) using these T values and write `C0=ell E+N`.
The quantity C3 is independent of E. Define

    K0=-9/2+6x+27E2/2,
    alpha=K0 ell+7C3/4-3/4,
    beta=K0 N+(-15/2+3x+27E2/4)C3+3x+27E2/4,
    E0=-beta/alpha.

In the remainder C0 and T0 mean their values at `E=E0`. Put

    F1=(9+6x-9E0)C0+(6+3x-5E0)C3+3x-3E0,
    F2=(6-6E2-4E0)C0+(6-3E2-3E0)C3-3E2-E0.

The identity `F1-(9/4)F2=0` holds by construction. Exact tensor Bernstein conversion establishes the following rational statements on the ENTIRE rectangle
`0<=t<=1, 7/2000<=w<=9/2000`:

    alpha<0, E0>29/50, C0>1/4, 3/20<C3<1, T0>29/50;
    1/3<x<53/100, 9/100<E2<11/100;
    0<L<27/50, 0<T2<1/10, T3+L>1/3.                (4)

After rational cancellation, the numerator of F2 has degrees 11 in t and
7 in w. At `w=7/2000` all its degree-11 Bernstein coefficients in t are
negative; at `w=9/2000` all are positive. Its denominators are nonzero:
the defining elementary denominators are positive and alpha is negative.
Thus the intermediate value theorem gives a root in the open w interval
for EVERY t in `[0,1]`. Choose the least such root. This is a construction
from p, not an assumed return witness. The compact endpoints t=0,1 serve
the certificate only; no infinite reward is used.

At this root define

    b=C0/(1+C0), B3=(C0+C3)/(1+C0),
    a=B3/(1+B3), A1=2a+(1-a)b, A2=2a,
    A=(0,A1,A2,0), B=(0,b,0,B3).

Both a and b lie strictly between zero and one. Since C3<1, `A2<1`.
The two equations F1=F2=0 are precisely

    A1(3-E0)=3(E0-x),
    A2(3-E0)=3E2+E0.                               (5)

The second equation gives `E0=3(A2-E2)/(1+A2)<3/2`.
In particular `0<x<E0<3` and `E2>3x/100`.

The certificate uses exact rational arithmetic. For a polynomial on a
rectangle it converts to the tensor Bernstein basis; strictly positive
coefficients prove positivity. When needed, it bisects that rectangle by
the exact de Casteljau identity. The hardest inequalities above require
only four leaves and depth three. No sampled or floating-point claim is
used in (4) or in the root-existence argument.

### 3.2. Every intermediate pair root passes its quiet comparisons

Consider any finite pair tail in Section 3, and write c,d,S_n,pi1,pi2,chi
for its current quantities. Its two quiet values are given by (3) with
these finite probabilities. We have

    S_n>=S>=1000/1617,
    pi1<=1-S1_n<=X/(2+X)<1/21,
    pi2<=1-S2_n<=L/(1+L)<27/77,
    0<=chi<=L X/(202+p)<27/101000,
    c<=c_1=X/(p+2+X)<1/21,
    d<=d_1=L/(101+L)<27/5050.

Player0's current value is bounded below by

    (29/50)(1000/1617)-27/77-12(27/101000)
      =197273/40829250 >0.

Its forced-Quit offer is nonpositive throughout the raw family. For player3
the forced-Quit offer is `-100d+101cd`. Substituting (1), its current value
minus this offer equals

    S_n(T3+L)-2pi1+94chi-101cd.

It therefore exceeds

    1000/4851-2/21-27/1050=20663/242550>0.

These bounds cover EVERY root and every truncation length, not a bounded
numerical search. At the triple root the only quiet player is0, whose
prescribed T0 is positive and whose joining offer is nonpositive.

### 3.3. Finite realization of the limiting core

Fix the root w and all macro parameters just constructed. Use the common
outer calendar with core given by the finite n-root pair word followed by
the triple123 root. Let C^(n) be its starting value with fixed successor E.
The probability identities prove eta_n=max_i|C_i^(n)-C_i| tends to zero.
Every core root has exact active and quiet comparisons and exact reference
Continue identities. Outside the core retain all limiting annotations.

There is exactly one reference Continue residual, at the solo2 root.
For i different from2 it is (1-b)(C_i^(n)-C_i); for i=2 it is C_2^(n).
Every coordinate and the prescribed residual have magnitude at most eta_n.
The immediate Quit offers at solo2 remain unchanged. Thus (2.3) proves
full terminal debts at most e+2eta_n/rho, while the initial payoff tends
to the fixed A. The factor rho=min(a,b)>0 does not depend on n or delta.
The common finite-horizon argument proves the theorem for every p>0.

## 4. The one-triple branch for nonpositive p

Put k=-p>=0, y=q/(k+3/10), z=2y/(101-106y), and w=ky/[3+(k-1)y].
For an auxiliary E define the full macro as follows:

    x=(101z+97w-200zw)/[(1-z)(1-w)],
    E2=[(2-k)y+4w-(3-k)yw]/[(1-y)(1-w)],
    C0(E)=3y-z+3w-14yz-4yw-8zw+13yzw
           +(1-y)(1-z)(1-w)E,
    C1=-100z-100w+211zw, C3=-z(100-101y).

The triple root has current C=(C0,C1,0,C3) and successor (E,-x,E2,0).
The definitions of w and z respectively force its current row2 and successor
row3 to be zero. All three active indifference identities hold exactly.

Write C0(E)=ell E+N and put

    K0=-9/2+6x+27E2/2,
    alpha=K0 ell+7C3/4-3/4-C1,
    beta=K0 N+(-15/2+3x+27E2/4)C3+3x+27E2/4+3C1,
    E0=-beta/alpha.

The two return equations, before substituting E=E0, are

    F1=(9+6x-9E)C0(E)+(6+3x-5E)C3+3x-3E+(3-E)C1,
    F2=(6-6E2-4E)C0(E)+(6-3E2-3E)C3-3E2-E.

Direct algebra gives F1-(9/4)F2=alpha E+beta. Define P(k,y) to be the unique
degree-(3,8) irreducible factor of the reduced numerator of F2(E0), normalized
with positive leading coefficient. This factor is constructed from
these formulas by rational polynomial factorization. The other factors have degrees (0,1) and (1,3); no external
coefficient file is an input. A root of P is sufficient to make F2(E0)=0.

At such a root set C0=C0(E0), b=C0/(1+C0),
B1=(C0+C1)/(1+C0), B3=(C0+C3)/(1+C0), a=B3/(1+B3),
A1=2a+(1-a)B1, A2=2a. Then F1=F2=0 are exactly
A1(3-E0)=3(E0-x) and A2(3-E0)=3E2+E0, the required return identities.

**Certified domain.** Every k in [0,31/10] has a unique root with
11/500 < q < 3/125. After substitution and clearing the positive denominator,
the polynomial has degrees (8,8) in (k,q). On the WHOLE rectangle:

- all Bernstein coefficients at q=11/500 are positive;
- all at q=3/125 are negative;
- all Bernstein coefficients of the q derivative are negative.

Each test succeeds without subdivision. Hence IVT and strict monotonicity give
one root, and the implicit-function theorem gives a continuous differentiable
root q(k), including a one-sided derivative at the two outer endpoints.

The global q rectangle contains irrelevant poles of the E0 formula. Therefore
its guards were certified on the polynomial root set, not on the whole rectangle.
Jointly subdivide the rectangle for P and the rational guard
numerators and denominators. Any box on which P has a strict sign contains no
root and is discarded. A remaining box is accepted only when every guard has a
strictly positive numerator/denominator ratio. Otherwise the box is bisected by
exact tensor de Casteljau subdivision, alternating k and q.

This procedure terminates with only five accepted root-containing boxes and
seven discarded boxes, depth at most six. It proves at every root:

    alpha<0, E0>x, C0>0, C0+C1>0, C0+C3>0, E2>0, 0<x<3.

In particular the E0 elimination denominator is nonzero on the whole root
branch. The elementary hazard denominators are positive throughout the initial
rectangle; y,z are positive and below one, and 0<=w<1 (w=0 exactly when k=0).
Consequently b=C0/(1+C0) is in (0,1), B1 and B3 are positive, and a is in (0,1).
Since C3<0<1, A2=2a<1. The second return equation then implies
E0=3(A2-E2)/(1+A2)<3/2. These inequalities provide the entire one-triple macro
except the wash-entry comparison.

**Unique wash boundary.** Direct rational simplification gives

    E2-3x/100 = y H(k,y) / [100(y-3)(y-1)(108y-101)],

    H(k,y)=k(31440y^2-50031y+19291)-20994y^2+82576y-58782.

The displayed denominator is strictly negative throughout the rectangle.
Exact Bernstein certificates give H<0 on 0<=k<=3, and H>0 at k=31/10,
for every q in the whole q interval. On 3<=k<=31/10 the same method gives

    P_y<0, P_k<0, H_y<0, H_k>0.

Thus y'(k)=-P_k/P_y<0 along the root and
(d/dk)H(k,y(k))=H_k+H_y y'(k)>0. There is exactly one k* in (3,31/10)
with H(k*,y(k*))=0. The actual wash gap has strictly NEGATIVE derivative there.
The one-triple macro is legal for every k in [0,k*], including equality:
the wash construction only needs E2>=3x/100, and its final43-step comparison
remains strict since (97/100)^43<109/400.

At k=0 the third hazard is w=0. Players1 and2 remain active; player3 is
quiet but its forced-Quit offer equals C3 exactly, by the same z equation.
Hence every local comparison still holds. This directly includes p=0 in
the unified construction, without importing the old zero-premium export.

Rational bisection of the unique polynomial root at two fixed parameters gives

    61441/20000 < k* < 153603/50000,
    i.e. 3.07205 < k* < 3.07206.

At the left endpoint the certified q bracket is
(394595192429/17179869184000,39459519243/1717986918400),
and H is negative throughout it. At the right endpoint it is
(394595178129/17179869184000,39459517813/1717986918400),
and H is positive throughout it. Monotonic H_y supplies the interval sign.
In particular k*>500/163, the overlap bound used below.


## 5. Two and three core roots and their support transitions

For p<0 use s=−1/p>0. At a triple123 root with hazards(0,sC,sD,w), put

```
Q1=−100sD−100w+211sDw,
Q2=−C+3w+(1−s)Cw,
q3=−D(100−101sC),
F1=(−101sD−97w+200sDw)/[(1−sD)(1−w)],
F2=[−C+2sC+4w+(1−3s)Cw]/[(1−sC)(1−w)],
f3=[2C−101D+106sCD]/[(1−sC)(1−sD)].
```

The active current values are(Q1,Q2,sq3) and the required successors are
(F1,F2,sf3). These are direct product-root calculations in the displayed
raw table. The scaled row3 equations extend regularly to s=0; this endpoint
is a proof device and never an infinite reward table.

The N-root systems use the following variables and root lists:

- N=1: variables(C,E0), e=C/[3+(1−s)C], Z=2C/(101−106sC), root(C,Z,e).
- N=2: variables(C,Y,t,E0), e=C/[3+(1−s)C], Z=2Y/(101−106sY),
  T3=−Z(100−101sY), D=[2C−T3(1−sC)]/[101−106sC−sT3(1−sC)],
  roots(C,D,e),(Y,Z,t).
- N=3: variables(C,D,U,V,w,Y,t,E0), e=C/[3+(1−s)C],
  Z=2Y/(101−106sY), roots(C,D,e),(U,V,w),(Y,Z,t).

The entrance current row2 is identically0, and the last successor row3 is
identically0. For N=2 impose F1=nextQ1 and F2=nextQ2; its row3 matching is
already enforced by D. For N=3 impose all three matches
(F1,F2,f3)=(nextQ1,nextQ2,nextq3) at both interfaces.

Set x=−F1(last), E2=F2(last). Starting at terminal row0 value E0, propagate
backward through the roots using

```
G(c,d,w;r)=3c−d+3w−14cd−4cw−8dw+13cdw
             +(1−c)(1−d)(1−w)r.
```

Here c=sC,d=sD. Let C0 be the first row0 value, C1=firstQ1, C3=s firstq3.
Define

```
b=C0/(1+C0), B1=b+(1−b)C1, B3=b+(1−b)C3,
a=B3/(1+B3), A1=2a+(1−a)B1, A2=2a,
R=1−x/3, V0=(E0−x)/R, V2=(E2+x/3)/R, h=V0/3.
```

The two remaining equations are
`A1(1−h)=3h` and `A2(1−h)=V2+h`.
Thus the N=1,2,3 rational systems have respectively2,4,8 equations and
unknowns. A supplied root is useful only after the following guards hold:

```
0<a,b,h<1; B1,B3>0; 0<x<3; E0>x; E2>=3x/100; V2>0;
every row0 annotation>0; every prescribed hazard in[0,1).
```

All nonzero core hazards are positive in direct regimes. A zero last q1,q2
at a support switch is allowed; the equations then make those quiet owners
indifferent. No payoff or tail is supplied as a hypothesis: the exact finite
certificates below produce a root for every parameter.

### 5.1. Complete parameter cover

The following five regions cover all p≤0. Endpoints overlap.

|Parameter region|Producer|
|---|---|
|k=−p∈[0,500/163]|one-root Bernstein producer|
|s∈[13/40,163/500]|one/two-root support switch|
|s∈[101/1000,13/40]|two-root interval producer|
|s∈[1/10,101/1000]|two/three-root support switch|
|s∈(0,1/10]|three-root interval producer|

The first region is supplied by Section 4. The four other regions follow
from the finite rational certificate described next. It checks 1000 equal
rational cells in each direct interval and one rational state box for each
branch at each switch. Every direct-cell guard and physical hazard is checked,
including the wash gap. No direct-regime comparison is omitted.

### 5.2. Why the finite interval certificate proves existence

All interval endpoints are integer multiples of2^-80. Each arithmetic
operation rounds its lower endpoint down and its upper endpoint up; division
rejects any denominator interval containing0. The derivative class applies
exact interval sum, product and quotient rules.

Centers are proposed deterministically: three rational Newton steps use
exact rational Gauss–Jordan elimination and round each center coordinate to
2^-60. Jacobian and residual midpoint estimates are only proposals. Their
accuracy is not assumed. The rational inverse R of the final proposed
Jacobian and a rational radius vector are then checked independently.
For cell S=[sl,sr], mid=(sl+sr)/2, and rational center c, define the outer
box X by outward rounding c±r. The interval expression is

```
−R F(c,mid) − R F_s(c,S)(S−mid)
       + [I−R F_x(X,S)] [-r,r].
```

The parameter mean-value theorem shows that this encloses the image of
T_s(z)=z−R F(z,s), relative to c, for every s∈S and z in the inner cube.
Strict inclusion in the inner radii is checked. Exact weighted row norms
of I−R F_x(X,S) are also checked below 1. This makes R nonsingular and
T_s a contraction throughout the OUTER convex box; in particular any two
zeros there coincide. The strict inclusion gives a zero in the inner cube
for every s∈S. The larger outer box is used for all guard and derivative
checks. No cross-cell branch identification is needed: each fixed game may
choose any produced legal root.

For direct cells the radius formula is
`r_i=max((11/10)|v_i|(sr−sl), |c_i|/10000,10^-9)`, where v is the
proposed implicit derivative. The proposal starts from one explicit rational
seed and continues from the preceding center; all 1000 checks must pass.
At switches the same formula is used, with the new branch radii multiplied
by 3; for the upper switch its q3-radius is multiplied by an additional 11/10.
All cells and both switches must satisfy every stated check.

Implicit derivative enclosures solve the exact interval linear equation
`z=−R F_s+(I−R F_x)z`. A rational proposed box is accepted only when its
image lies strictly inside itself. Since F_x is nonsingular throughout X,
this enclosure contains the actual implicit derivative. Differentiating a
guard then uses its interval gradient and this enclosed derivative.

### 5.3. Exact support-switch identification

At either switch, write E=(E0,−x,E2,0) for the old N-root endpoint and
ω=E2−3x/100 for its wash gap. Both old and new systems have a unique zero
in their certified outer state box at every parameter in the switch interval.
The certificate proves:

1. Every old guard exceptω is strictly valid, with all old hazards physical.
2. ω has strictly positive s-derivative; exact endpoint root enclosures give
   ω(sl)<0<ω(sr). Thus there is one s* withω(s*)=0.
3. Every new guard is strictly valid except possibly the sign of its last
   scaled q1-coordinate Y. That coordinate has strictly negative s-derivative.
   The last scaled q2 equals2Y/(101−106sY), whose denominator is asserted
   positive throughout the box; the other new hazards are physical.
4. The exact insertion map of the ENTIRE old outer box times the parameter
   interval lies strictly inside the new outer uniqueness box.

Here is that insertion, which identifies the zeros and prevents an inferred
branch match. At ω=0 append a solo3 root of hazard q=x/100. Its current
values satisfy row1=−100q, row2=3q, row3=0, exactly the new core's Q values
when q1=q2=0. Its successor is

```
E0new=(E0−3q)/(1−q),
xnew=97q/(1−q),
E2new=(E2+q)/(1−q), E3new=0.
```

All earlier roots retain their current values. The wash endpoint V0,V2 is
unchanged, since new total wash survival is R/(1−q). Thus the two closure
equations are preserved exactly. In coordinates, the insertion is

```
N1 -> N2: (C,E0) -> (C,0,q,(E0−3q)/(1−q)),
N2 -> N3: (C,Y,t,E0) -> (C,D,Y,Z,t,0,q,(E0−3q)/(1−q)),
```

with D,Z from the old model. The checked containment and new outer-box
uniqueness show that the new branch has Y(s*)=0. Its negative derivative
then gives Y>0 for s<s*. The old wash gap is positive for s>s*. Consequently
use the new macro to the left, the old one to the right, and the old macro
with weak wash equality at s*. These exhaust the whole switch interval.

For orientation only, the lower boundary is approximatelys=.1002083955662
and the upper approximatelys=.3255154427973. Neither numerical value is used
in the certificate. The new wash gap is strictly positive at insertion:
`109x/[100(100−x)]>0`.


### 5.4. Reproducible finite certificate data

This subsection specifies the finite arithmetic in Section 5.2, so the proof
does not depend on an external center list or root search. Every terminating
decimal below denotes its exact rational value. Use the rational systems of
Section 5 with their displayed variable and equation orders.

For a rational input, form its outward interval at precision2^-80. For
interval addition, multiplication and division, round down the exact lower
endpoint and up the exact upper endpoint; compute all four endpoint products
or quotients. Reject division if the denominator contains zero. Differentiate
these same rational expressions by the sum, product and quotient rules.

At a point (c,s), evaluate residuals and derivatives by that interval
arithmetic, then take each interval midpoint to obtain rational estimates
f,J,f_s. A proposal consists of three iterations

    c <- round_60(c-J^(-1)f),

where `round_60(t)=2^-60 floor(2^60 t+1/2)` coordinatewise. At the final
point recompute these estimates and set R=J^(-1), v=-R f_s. These estimates
only propose the center, inverse and slope; they are not used as exact
residuals or derivatives in any acceptance test. All acceptance calculations
use outward intervals on the whole indicated boxes.

The initial centers are:

| Use | Initial vector |
|---|---|
| N3 direct cover | (9/397, 54296564078592426/63070111151171990729, 573/39409, 654500574858/1572938403151657, 291/39700, 25581/3912673, 28227/3940900, 4738019/3912673) |
| N2 direct cover and old lower switch | (.02187,.0097,.00712,1.2093) |
| New N3 lower switch | (.02187,.000625,.00973,.000193,.00712,0,.006977,1.1967) |
| Old N1 upper switch | (.02093,1.20475) |
| New N2 upper switch | (.0214,0,.006919,1.1923) |

For each direct interval in Section 5.1 divide into 1000 equal cells, in
increasing order. Apply the proposal at the cell midpoint, starting with
the preceding cell's final center after the first cell. Use the radius
formula in Section 5.2. Form the strict inclusion and weighted contraction
bounds there, and check every guard and physical hazard on the outer box.
These tests succeed for all 1000 N3 cells and all 1000 N2 cells.

For each switch apply the same proposal to the whole parameter interval,
using its two listed initial centers. Enlarge the new branch's radii as
specified in Section 5.2 and check both contractions and inclusions. To
bound implicit derivatives, try in order the five boxes centered at v with
coordinate radii

    f(|v_i|+1/10000), f in {1/100,1/10,1/2,1,2}.

Accept the first box mapped strictly into itself by the interval affine
equation in Section 5.2. Check positive derivative of the old wash gap and
negative derivative of the new last scaled q1. Check all old guards except
the wash gap and all new guards except the last q1,q2 lower bounds; also
check `101-106sY>0`. At both parameter endpoints, use three further proposal
steps starting from the old center and radii10^-10 in every coordinate.
Their certified state boxes lie inside the old uniqueness box and give the
strict opposite wash signs. Finally evaluate the insertion formulas on the
ENTIRE old outer box and require their image strictly inside the new outer
box. All these tests succeed at both switches.

This is a finite certificate consisting of rational arithmetic, specified
rounding, and strict inequalities. It proves existence for every parameter
in the intervals, not only for the finitely many cell midpoints. The seed
at s=0 is used only in this finite proof; no strategy uses an infinite reward.

## 6. Polynomial certificates and conclusion

For completeness the polynomial computations in Sections 3 and4 use the
following exact rule. Map each rectangle affinely to the unit square. For
power coefficients a_(i,j) and coordinate degrees d,e, its tensor Bernstein
coefficients are

    b_(u,v)=SUM_(i<=u,j<=v) a_(i,j)
               binom(u,i) binom(v,j)/[binom(d,i) binom(e,j)].

The polynomial is a convex combination of these coefficients at every point
of the rectangle. Strictly positive or negative coefficients certify the
corresponding strict sign. Bisect by the de Casteljau rule, replacing adjacent
coefficients by their arithmetic means; alternate the two coordinate axes
at successive depths. For a rational guard, certify nonzero numerator and
denominator with the same sign. In Section4, first discard every box where
the root polynomial has a strict sign. Only the remaining boxes need all
guards. Thus irrelevant poles off the root set cause no loss of coverage.
The stated finite leaf counts and sign tests follow by this rational rule
from the displayed formulas. No floating-point root or guard estimate is
used by these polynomial certificates.

Sections 3--5 produce a legal core for every real p. The five negative
regions meet at their closed endpoints, and Section4 includes p=0. Fix one
produced root for the given table, hence one target A. The common consumer
in Section2 supplies the required profiles for every accuracy. For p<=0
it has eta=0 and exact terminal target A; for p>0 its only residual eta_n
tends to zero while the deleted-survival bound rho stays fixed. This proves
the theorem with all its quantifiers.

## 7. Coverage and semantic correspondence

The theorem removes the former restriction Z2(12)=0 entirely, while keeping
the other 31 displayed native entries fixed. It also permits arbitrary solo0
joining rewards in all three other rows. It is a reward-table producer;
it assumes no strategic return, tail, clock law, or favorable continuum
branch. It does not claim coverage of arbitrary four-player reward tables.

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

Take kappa=(1,1,1,1) and p=1, -10, or -100. Exact rational support
exclusion checks reject all 80 nonzero stationary support patterns and all 65
sure-root patterns against any actual continuation cap in each case. The
respective Bernstein node counts are(978,371), (1028,353), and(962,331).
These are concrete witnesses, not a stationary exclusion for the entire
parameter family. The new theorem nevertheless constructs their equilibria.

Here is the finite exclusion calculation behind those counts. Write
Gamma_ij=Z_i({j}), Gamma_ii=0, and, for q in[0,1]^4, set

    H_i=product_(j!=i)(1-q_j),
    P_i=SUM_(S subset opponents) weight_q(S) Z_i(S), Z_i(empty)=0,
    Q_i=SUM_(S subset opponents) weight_q(S) Z_i(S union {i}),
    F_i=(1-H_i)Q_i-P_i,
    L_i=min({-1} union {Z_i(S): nonempty S excludes i}),
    G_i=Q_i-P_i-H_i L_i.

Here weight_q(S)=product_(j in S)q_j product_(j outside S,i)(1-q_j).
For this completion L=(-12,-8,-10,-12), for all three tested p values.
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

The singleton matrix is unchanged across p. Its positive graph is strongly
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

The formalization handoff is the raw-table existence theorem in Section1.
Its proof factors into the common finite calendar and full-cap consumer,
the explicit positive pair entrance and polynomial return, the one-triple
polynomial producer, and the two finite interval covers with exact support
insertion. The rational identities, Bernstein sign calculations, outward
interval arithmetic and finite acceptance inequalities are finite lemmas
to certify; the Banach and implicit-derivative arguments turn them into
roots for every parameter. The downstream result is a fixed uniform payoff
with unrestricted unilateral deviations. No strategic hypothesis remains
for a formalization agent to produce, and no claim is made that these
finite certificates have already been checked by Lean.
