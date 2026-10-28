# Complete scalar solo3 returns and a positive-continuation raw producer

Owner: CODEX_COORDINATOR. Ordinary mathematics, not checked in Lean. The scalar result completely
classifies this finite solo3 architecture. The raw producer broadens one
higher-reward class; it does not solve arbitrary Fin4 or establish separation
from every existing producer.

Section7 retains a finite approximation mechanism with two distinct joint
pairs, arbitrary signed own levels, and unrestricted behavioral deviation
bounds. Its benchmark overlaps the passive-threshold theorem, so this is an
internal constructive record. The exact section has an independent
[consumer review](../feedback/CODEX_COORDINATOR__COMPLETE_SOLO_RETURN_GEOMETRY__BY_RESET_CONSUMER_REVIEW.md).
Run `python math/experiments/CODEX_COORDINATOR__TWO_PAIR_RESET_CHECK.py`
from the repository root for its rational quadratic and interval checks
(requires SymPy).

## 1. Exact scalar classification

Let

    U=(C,-j,T,0), G=(k,-g,-h,0), Y=(Y0,Y1,Y2,0),
    U=t*G+(1-t)*Y, 0<t<1,
    C>0, T>0, Y0>0, Y1>0, Y2>0.

All coefficients k,g,h,j and the quiet joining rewards

    J=(zeta,-A,c)

may otherwise be arbitrary real numbers. A solo3 root with hazard q in
[0,1) has current W, successor W', and the exact conditions

    W=q*G+(1-q)*W', W_i>=q*J_i for i=0,1,2.

Owner3 has current and successor value zero and is indifferent. We seek a
finite word with aggregate quitting probability t taking U to Y.

Such a word exists exactly in the following cases:

| Initial row1 | Necessary and sufficient condition |
|---|---|
| j<0 | None beyond the displayed endpoint assumptions |
| j=0 | A>=0 |
| j>0 | A>=max(j/t, zeta*j/C, c*j/T) |

In the last row A is automatically strictly positive. Equivalently the first
legal hazard `q*=j/A` must satisfy

    q*<=t, zeta*q*<=C, c*q*<=T.                    (S1)

Negative c or zeta simply make their respective inequalities automatic.
In particular neither h>0 nor A>g is necessary. For j>=0 the endpoint
identity itself forces `g*t=j+(1-t)*Y1>0`, hence g>0.

### Proof and finite recipe

Let m be cumulative quitting probability before a date, and put
`delta=(1-m)*q`. The current value is

    W(m)=(U-m*G)/(1-m), 0<=m<=t.

Thus every legal positive step `m -> m+delta<=t` is characterized exactly by

    zeta*delta <= C-k*m,
    A*delta >= j-g*m,
    c*delta <= T+h*m.                              (S2)

The first and third right sides are strictly positive on [0,t], since they
are affine and positive at both endpoints. The same is true of `-j+g*m`
when j<0. Therefore for j<0 sufficiently small equal cumulative increments
satisfy every comparison for arbitrary J. If j=0, the first positive step
requires A>=0; when A>=0 the middle inequality then holds everywhere and
the other two again allow sufficiently small increments. Zero hazards do
not bypass either obstruction, because they leave the current state fixed.

For j>0, the first positive step requires A>0 and delta>=j/A. Applying the
remaining inequalities and the total-mass bound gives (S1), proving
necessity. Put r=j/g. Positive Y1 implies `0<r<t<1`.

If `0<A<=g`, take the first increment delta=j/A. It is legal by (S1) and
reaches or overshoots r. The remaining row1 values are nonnegative, with
nonpositive joining reward -A; the other two coordinates remain positive.
Subdivide the remaining mass into finitely many small increments.

If `A>g`, put lambda=1-g/A in (0,1) and

    m_n=r*(1-lambda^n),
    delta_n=(j-g*m_n)/A=m_(n+1)-m_n.

These minimal steps are legal for every m_n<r. For either of the outer rows,
the upper-bound-minus-minimal-step margin is affine in m. At m=0 it is
nonnegative by (S1); at m=r it is strictly positive because the outer
budgets are positive. The total-mass margin is likewise nonnegative
between 0 and r. Thus no intermediate barrier can appear.

After finitely many minimal steps, jump exactly to r. More explicitly,
choose n so that

    r*lambda^n*max(zeta-k,0) <= C-k*r,
    r*lambda^n*max(c+h,0) <= T+h*r.                 (S3)

Both right sides are strictly positive, so such finite n exists. These are
exactly the outer-row tests for the final increment `r-m_n=r*lambda^n`;
the middle row is legal because A>g. Subsequent sufficiently small steps
reach t. All inequalities are weak where required, so the initial wash
equality and all threshold equalities are included.

For completeness, the final subdivision is fully explicit. Starting at
m0>=r, take N equal cumulative increments `(t-m0)/N`. The positive minimum
outer budgets on [m0,t] dominate their joining coefficients times those
increments for all sufficiently large integers N. The middle row is
nonnegative and its joining coefficient is -A<0. For j<0 use the positive
minimum of all three budgets and the positive parts of J in the same way.
For j=0,A>=0 only the outer budgets are needed. This proves sufficiency.

For example, choose

    G=(1,-1,1,0), U=(3/4,-1/4,1,0), Y=(1/2,1/2,1,0),
    t=1/2, A=1/2, c=1, zeta=3/2.

The single root q=1/2 is legal: row0 and row1 bind, row2 is strict. Here
A<g, h=-1<0, and zeta>k, all outside the old wash sign assumptions.

The old row2 wash boundary is genuine: when j>0 and c>0, `A*T>=c*j`
is necessary before any positive solo3 step. For instance
`G=(1,-1,0,0), t=1/2, U=(3/4,-1/4,1/10,0), Y=(1/2,1/2,1/5,0)`
with A=c=1 and zeta=0 satisfies every endpoint assumption, but its first
step would require both q>=1/4 and q<=1/10. No finite solo3 word exists.
The classification therefore does not eliminate the need for a non-solo
core on the old positive-debt region where the wash-entry inequality fails.

## 2. A positive-continuation raw producer with arbitrary singleton signs

Use the native four-player model and full behavioral-deviation semantics of
`CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`. Every singleton entry may
have either sign. Write

    alpha=Gamma02, f=Gamma20, k=Gamma03,
    e=Gamma32, d=-Gamma30, w=Z3(02),
    R0=Z0(02), R2=Z2(02), G=Gamma[:,3].

For the variable b define

    D=d-b*(w+d-e), E=D-e*b,
    B=b*R0-alpha, T0=k-b*(k+R0-alpha),
    P(b)=[f*e*T0+G2*B*D]*E
             -(R2-f)*e*b*(B*D+e*T0).              (P1)

This polynomial has degree at most three. Require it to be nonzero and
select a real root b satisfying the following finite raw tests:

    0<b<1, D!=0, x=e*b/D in(0,1),
    X0=b*R0, X2=x*R2,
    U0=b*(R0-alpha)/(1-b), U2=x*(R2-f)/(1-x),
    k-X0!=0, tau=(U0-X0)/(k-X0) in(0,1).           (P2)

Put

    S=(1-x)*(1-b),
    P1=x*(1-b)*Gamma10+(1-x)*b*Gamma12+x*b*Z1(02),
    U1=[tau*G1+(1-tau)*P1]/[1-(1-tau)*S],
    X1=P1+S*U1,
    U=(U0,U1,U2,0), X=(X0,X1,X2,0).

The denominator of U1 is strictly positive by (P2). Require all three
quiet coordinates of both U and X to be strictly positive. Finally require

    x*(1-b)*Z1(01)+(1-x)*b*Z1(12)+x*b*Z1(012)<=X1,
    x*(1-b)*Z3(03)+(1-x)*b*Z3(23)+x*b*Z3(023)<=0.   (P3)

These are raw algebraic tests on at most three roots; no strategy or
continuation object is assumed. The quiet1 inequality may equivalently be
solved as an upper bound on Z1(12). Every other higher entry is arbitrary
finite, including p=Z2(12) and the three solo3 joining rewards

    J_i=Z_i({i,3}), i=0,1,2.

The tests produce an exact finite-period terminal Nash equilibrium and an
original uniform-equilibrium payoff for arbitrary own levels kappa. No
singleton-sign pattern is assumed. The particular elimination (P2) excludes
its zero denominators; it does not silently cover those degenerate cases.

### Construction and proof

Direct algebra gives

    tau*G2+(1-tau)*X2-U2
      = b*P(b)/[(1-b)*(k-b*R0)*D*(D-e*b)].         (P4)

Every denominator is nonzero; in particular `D*(D-e*b)=D^2*(1-x)>0`.
Thus (P1), the definition of tau, and the definition of U1 give exactly

    U=tau*G+(1-tau)*X.                            (P5)

At a joint02 root with hazards `(x,0,b,0)` and successor U, owner0 has
Quit=Continue=X0 and owner2 has Quit=Continue=X2. Quiet1 has current X1
and passes (P3). Quiet3 has current `e*b-x*D=0` and also passes (P3).

Choose a strictly positive prefix probability a sufficiently small that
`a<tau` and `Y=a*G+(1-a)*X` has positive quiet coordinates and
`Y_i>a*J_i` for i=0,1,2. This needs no signs on G or J because X is strictly
positive. An explicit choice is

    m=min(X0,X1,X2),
    M=max_(i=0,1,2)(abs(G_i-X_i)+abs(J_i)),
    a=min(tau/2,1/2,m/[2*(1+M)]).                 (P6)

Then every Y_i and every prefix quiet margin is at least m/2. Owner3 is
indifferent. This legal solo3 prefix is followed immediately by the joint02
root.

Put `t=(tau-a)/(1-a)` in (0,1). Equation (P5) gives
`U=t*G+(1-t)*Y`. Both U and Y have strictly positive quiet coordinates,
so Section 1 gives a finite solo3 return without any sign restriction on
their singleton or joining rewards. More explicitly, set
`m_i=min(U_i,Y_i)>0` and choose an integer

    N>=1, N>max_i t*max(J_i,0)/[(1-t)*m_i].

The N return hazards `q_l=t/(N-l*t)`, l=0,...,N-1, have total survival
1-t and obey every quiet comparison. All return annotations lie on the
segment joining U and Y, and owner3 remains indifferent.

The complete period is prefix3, joint02, then these N solo3 return roots.
Every unilateral deviator faces opponent absorption at least min(x,b)>0
per period. Bounded Bellman unrolling proves exact Nash against all complete
behavioral replacements, including Never. The same absorption estimate
justifies arbitrary own-level row shifts and gives the fixed original
uniform-equilibrium target `kappa+Y` exactly as in the frozen direct theorem.

## 3. A three-date example with no opposite-sign reciprocal pair

Start with the singleton matrix

    H=[0,3,-1,-1;2,0,-1,-1;-1,-1,0,2;-1,-1,2,0].

Under `(new0,new1,new2,new3)=(old0,old3,old1,old2)` it becomes

    Gamma=[0,-1,3,-1;-1,0,-1,2;2,-1,0,-1;-1,2,-1,0].

Choose

    Z(02)=(6,9,7/2,6),
    Z0(03)=Z1(13)=Z2(23)=0,
    Z1(01)=Z1(12)=Z1(012)=0,
    Z3(03)=Z3(23)=Z3(023)=-1.

Every other higher reward is arbitrary fixed finite. Original rewards are
`r(D)=kappa+Z(D)` for arbitrary own levels kappa, with live/Never still zero.
The raw polynomial and selected values are

    P(b)=-(4*b-1)*(102*b^2-44*b+5),
    b=x=1/4, D=-1, tau=1/5,
    G=(-1,2,-1,0), U=(1,1,1/2,0), X=(3/2,3/4,7/8,0).

The selected root is simple, with P'(1/4)=-3/2. The three exact hazards are

    (0,0,0,1/10), (1/4,0,1/4,0), (0,0,0,1/9).

Their current values are, respectively,

    Y=(5/4,7/8,11/16,0), X, U.

Exact transport is `U=(G+4X)/5`, `Y=(G+9X)/10`, and `U=(G+8Y)/9`.
At the joint date the active values are X0=3/2 and X2=7/8; both owners
are indifferent. The quiet margins are X1=3/4 for player1 and 7/16 for
player3. At the two solo3 dates all joining offers are zero, so their quiet
margins are exactly the positive first three coordinates of Y and U.
Every comparison is therefore checked by rational arithmetic.

Every unilateral deviator faces opponent absorption at least 1/4 per
three-date period. Thus this profile is exact full behavioral terminal Nash
with fixed original uniform-payoff target `kappa+Y`; the standard terminal
versus finite-horizon discrepancy bound is `28R/T_horizon` when original
rewards are bounded by R.

The reciprocal products, in pair order01,02,03,12,13,23, are
`(1,6,1,1,4,1)`. Every reciprocal pair has matching signs. This example
therefore lies outside architectures requiring even one opposite-sign
reciprocal pair, under every relabeling. It still has two disjoint positive
reciprocal pairs; no exclusion of all other existence producers is claimed.

## 4. Overlap and remaining boundary

The narrow source search inspected the two frozen joint-return exports,
`SIGNED_COLLISION_PARAMETER_UNIFORM_EQUILIBRIUM.md` (finite wash and final
subdivision), `SIGNED_COLLISION_BRIDGE_UNIFORM_EQUILIBRIUM.md` (Section 4
cumulative solo3 coordinates), `EXPLICIT_SINGLETON_CHAMBER_UNIFORM_EQUILIBRIUM.md`
(Section 6), and the retained coordinator axis and root-geometry notes.
They already use cumulative survival and prove finite washes under sufficient
sign guards. The results here add the exact necessary-and-sufficient scalar
partition, arbitrary signed positive-arc subdivision, and the resulting
explicit raw positive-continuation producer without singleton-sign assumptions.
No broad literature novelty or
new Lean theorem is asserted.

The scalar criterion isolates a real first-root barrier. Progress beyond
it requires another support or another continuation geometry; subdivision,
overshooting, and longer solo3 words cannot change that obstruction.

## 5. No exact separated-joint calendar at the middle point

Status: ordinary mathematics, not Lean checked. An architecture obstruction,
not a counterexample or an obstruction to vanishing-error equilibria.

Use the complete native table in Section3 of the
[three-owner theorem](../exports/THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md),
with eta=12281660/12608823, R=Z0(23)=-25,
t=Z3(023)=987, and arbitrary K,p. Only its rows0,2,3 enter this proof;
player1 never quits, so its penalty K and the row2 reward p at coalition12
are unused.
Consider a deterministic live-state calendar whose nonempty dates are either
proper joint02 hazards (x,0,b,0), proper joint023 hazards (x,0,b,z), or proper
solo3 hazards (0,0,0,q). Here every displayed active probability lies strictly
between zero and one. Require every two successive joint dates to be separated
by at least one positive solo3 date; consecutive solo3 dates are allowed.

THEOREM. No almost-surely absorbing calendar of this form has exact Bellman
Nash comparisons at every date. Consequently no nonempty finite-period calendar in
this class is an exact terminal Nash profile. If original own levels are all
strictly positive, no finite or infinite exact terminal Nash profile of this
calendar form exists, even without assuming absorption in advance.

This rules out arbitrary lengths and nonperiodic separated-joint schedules.
It does not rule out adjacent joint dates, different active sets, arbitrary
behavioral profiles, or approximate Nash profiles with errors tending to zero.

### 5.1 A scalar quantity and exact joint drift

Use actual conditional native continuation vectors V. Under almost-sure
prescribed absorption these are legitimate row shifts of original payoffs.
They are bounded by the finite reward ranges. Finite activity with proper
hazards cannot absorb almost surely. If there are only finitely many joint
dates, an almost-surely absorbing tail consists only of solo3 dates; its
actual native row2 value is -1, contradicting the positive quiet2 Quit
offer at any positive solo3 date. Thus it suffices to consider infinitely
many joints and discard a finite initial partial block. At a positive solo3 date,
owner3 indifference forces its continuation and current value to be zero.
For the other rows, current V and successor U satisfy

    V=q*(3,-3,-1,0)+(1-q)*U.

Quiet2's offer is 3q, so V2>=3q>0 and U2=(V2+q)/(1-q)>0.
Thus all annotations adjacent to solo3 dates have positive row2. Every joint
is bracketed by such dates (discard an initial partial block in an infinite
calendar). Throughout the remaining calendar, 0<V2<=3: player1 never quits
and every possible prescribed row2 absorbing reward is at most3.
Likewise -25<=V0<=3. Define

    Phi(V)=(V0-3)/(V2+1),     -28<=Phi(V)<=0.

It is unchanged across every solo3 date.

A separated joint has current X3=0 and successor U3=0. Put

    b*=319/1066, eta=12281660/12608823.

For a joint02 date, row3's passive equality forces
x=b/[1+(219/29)b]. Its quiet3 Quit comparison then forces b<=b*<3/10.
Active0,2 indifference gives

    X0=-b/10, X2=x*(2+eta),
    U0=9b/[10(1-b)], U2=x*eta/(1-x).

Writing W=(U0-3)(X2+1)-(U2+1)(X0-3), direct expansion gives

    W=29b(10b-3)(71659209b^2-1272539233b-210147050)
        /[4347870(b-1)(190b+29)(219b+29)] <0.       (1)

Moreover, on 0<b<=b*,

    -W >= (1682/1306383)*b > b/1000.              (2)

To verify this bound, use 3-10b>=4/533, the absolute value of the quadratic
factor at least210147050, and
(1-b)(190b+29)(219b+29)<=86*95. All inequalities include endpoints.
Since both row2 annotations are at most3,

    Phi(U)-Phi(X)=W/[(U2+1)(X2+1)] <=-b/16000.

The date's prescribed absorption probability alpha=x+b-xb satisfies
alpha<=2b. Thus Phi falls by at least alpha/32000.

For a joint023 date, its active3 indifference and both zero annotations force

    b=b*, x=319/3475.

Set lambda=z/(1-z)>0. Current and successor outer rows are

    X0=(-b/10-20lambda)/(1+lambda),
    X2=[x*(2+eta)+lambda*(3-103x)]/(1+lambda),
    U0=9b/[10(1-b)]+lambda*[-23+5b/(1-b)],
    U2=x*eta/(1-x)+lambda*[4-95x/(1-x)].

Positivity of X2 implies lambda<206246183/4876570992<1/20.
Now W=(1+lambda)*[(U0-3)(X2+1)-(U2+1)(X0-3)] is exactly

    -319*(596387876039319780lambda^2
          +158797459367088077lambda+61079706181272)
          /12656828795288418000.                 (3)

Every coefficient inside parentheses is positive, and
-W>=811851094659407/527367866470350750>1/1000.
The denominator (1+lambda)(U2+1)(X2+1) is less than17.
Therefore Phi falls by more than1/17000, hence by at least alpha/17000.
Combining the two joint types, every joint decreases Phi by at least
alpha/40000, while every solo3 date leaves it unchanged.

### 5.2 Infinite calendars cannot absorb almost surely

The bounded range of Phi implies that the sum of joint absorption
probabilities is finite. More explicitly it is at most28*40000 after any
initial partial block. At a solo3 date,

    U2-V2=q*(U2+1)>=q.

At a joint date, write V2=P2+(1-alpha)U2. The current prescribed coalition
rewards lie between-100 and3, and U2<=3. Hence

    U2-V2 >= -103*alpha.

Telescoping the row2 values over any finite initial interval now yields

    sum_solo q <= 3+103*sum_joint alpha.

Thus the sum of ALL prescribed datewise absorption probabilities is finite.
Every individual probability is less than1 because all active hazards are
proper. Their survival product is strictly positive, contradicting the
assumed almost-sure absorption. In a periodic calendar the strict scalar
decrease already gives an immediate contradiction after one period.

### 5.3 Removing the absorption assumption for positive original own levels

For completeness, suppose an exact original terminal Nash calendar with
strictly positive kappa_i had positive probability of Never. Then all four
sums of datewise hazards are finite. In particular, opponents' current
quitting probabilities tend to zero, and conditional probabilities of any
future prescribed absorption tend to zero. At sufficiently late live dates,
the prescribed original conditional payoff tends to zero, while the immediate
Quit payoff of each player tends to its kappa_i>0. The live history has
positive probability. Deviating only there gives a strict improvement, a
contradiction. Hence every such exact original Nash calendar must absorb
almost surely; the preceding obstruction applies.

This last argument uses complete deviation agency and actual conditional
payoffs, not assumed continuation annotations. It is not uniform in the
approximation error and supplies no unrestricted positive exploitability gap.

## 6. Two adjacent triple dates do not repair the middle point

Ordinary mathematics with an exact rational elimination certificate, not Lean
checked. This is an architecture exclusion, not a UE counterexample or a new
conjecture-facing export. Use the complete table of Section3 in
`math/exports/THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`, replacing
R=Z0(23) by -25, with t=Z3(023)=987 and eta=12281660/12608823. K,p and original
own levels may be arbitrary: the exclusion does not use row1 or coalition12.

**Claim.** No exact terminal Nash period consists of two adjacent dates at
which precisely owners0,2,3 mix properly, followed by a nonempty finite word
of proper solo3 dates. Cyclic rotations and inserted all-Continue dates do not
change the statement. This leaves three or more adjacent joint dates, different
active supports, sure phases and arbitrary nonperiodic strategies open.

### 6.1 Necessary equations and exact elimination

Let the two joint dates have hazards (x,0,a,z1) and (y,0,b,z2), with all six
nonzero coordinates strictly between zero and one. Write l=z1/(1-z1)>0 and
m=z2/(1-z2)>0. A proper solo3 date forces native value3 to zero at both its
ends, so the first joint input and second joint output have row3 value zero.
At a joint date with hazards (u,0,v,z), the native player3 offers are

    P3=v-u-(219/29)*u*v,
    Q3=u-100*v+1086*u*v,
    H3=(1-u)*(1-v).

The first Q3 must vanish; the second P3=Q3. Thus necessarily

    x=100*a/(1+1086*a),
    y=2929*b/(58+31713*b).

The intervening value is P3 at the second date, so the remaining row3 equation
is P3(x,a)+H3(x,a)*P3(y,b)=0. Up to its nonzero factor this is p(a,b)=0, where

    p=30481204*a^2*b^2-42927544*a^2*b-61828*a^2
      -30450290*a*b^2+19228682*a*b+18502*a
      -30914*b^2+9251*b.

For an arbitrary joint hazard pair(u,v), define

    C(v)=9*v/[10*(1-v)], T(u)=eta*u/(1-u),
    A0(v)=-23+5*v/(1-v), A2(u)=4-95*u/(1-u).

Owner0/2 indifference requires successor values C(v)+A0(v)*odds and
T(u)+A2(u)*odds. Their current values are

    Q0(v,odds)=(-v/10-20*odds)/(1+odds),
    Q2(u,odds)=[u*(2+eta)+(3-103*u)*odds]/(1+odds).

Set V=l*(1+m). The first-date successor equals the second-date input, giving
an exact linear system for V,m:

    M [V,m]^T = [-b/10-C(a), y*(2+eta)-T(x)]^T,
    M = [[A0(a), C(a)+20],
         [A2(x), T(x)-3+103*y]].                 (A)

All its coefficients are explicit rational functions of a,b. Where M is
invertible solve (A), then l=V/(1+m). Define

    X0=Q0(a,l), X2=Q2(x,l),
    U0=C(b)+A0(b)*m, U2=T(y)+A2(y)*m.

The solo3 return, with any number of dates, lies on an affine line parallel
to G=(3,-3,-1,0). Therefore the second necessary equation is

    (U0-3)*(X2+1)-(U2+1)*(X0-3)=0.              (B)

The current value U2 before the first positive solo3 hazard must be positive:
its Quit offer equals3q>0. We show that (A),(B),p=0 never supply this.

### 6.2 Complete finite algebraic certificate

All polynomial operations in this paragraph are over the rationals. Cancel
each rational function before taking its numerator. For an explicit convention,
use the rational expressions (A) and Cramer's rule, without primitive-part
normalization, then cancel as usual; global nonzero scalar factors do not
change any root or Sturm variation difference.

The common polynomial denominator of the Cramer solutions V,m, up to constants,
is

    D=76393665241525179*a^2*b-340455325400506*a^2
      -38551100718248691*a*b+323433727449644*a
      -229721533207530*b-20111072685.

In fact det(M)=-2D/[63044115*(a-1)*(986a+1)*(31713b+58)].
Let NV,Nm denote the reduced polynomial numerators of V,m. Exact resultants give

    gcd(Res_a(D,p), Res_a(D,NV), Res_a(D,Nm))
       = nonzero constant * (31713b+58).

Thus no singular compatible system exists with 0<b<1. This handles the case
that would otherwise be lost by Cramer's rule.

Let r be the reduced numerator of the left side of (B). Its bidegree in(a,b)
is(6,6). The resultant Res_a(p,r) is a nonzero constant times

    b*(31713b+58)^2*h(b),

where h has degree19. These definitions specify h without retaining its large
integer coefficient list. The subresultant chain of r,p in the variable a has
degrees6,2,1,0. Its linear member is L1(b)*a+L0(b), with

    gcd(h,L1)=1.

Every candidate in the physical interval therefore has
`a=-L0(b)/L1(b)`. The rational function has reduced numerator and denominator
of degree16. Sturm's sequence of h has variations V(0)=13,V(1)=5. There are
exactly eight roots in(0,1), one in each of the following rational intervals;
N means the interval(N/10^8,(N+1)/10^8).

| N | Variations at its two ends | Certified failure |
|---:|---:|---|
|1433|13,12|a<0|
|139241|12,11|l<0 and m<0|
|756524|11,10|l<0 and m<0|
|1649695|10,9|a<0|
|42078231|9,8|-94/1000<U2<-93/1000|
|60087710|8,7|-447/1000<U2<-446/1000|
|66721526|7,6|a<0|
|73975975|6,5|a<0|

The sign checks use rational root isolation refined to width below10^-50,
Horner interval evaluation of -L0/L1, and literal rational interval evaluation
of the Cramer expressions and U2. Reciprocal is used only when its denominator
interval excludes zero. These instructions give a finite reproducible exact
certificate from the small formulas (A),(B),p and eta; no numerical optimizer
or floating sign decision is an input. Each listed h root is simple. The two
remaining probability/odds candidates have positive l,m but strictly negative
U2, contradicting the first positive solo3 comparison. This proves the claim.

### 6.3 Scope and source audit

The argument only uses necessary active indifferences, payoff transport and one
quiet2 comparison; quiet1 can only further restrict the candidate set. Under
this proper periodic architecture every unilateral replacement faces positive
opponents-only absorption per period, so subtracting the original own levels
is valid. Thus the same exclusion applies to arbitrary original own levels.

The full root/continuation cap interface inspected was
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`). No Lean command
was run. The mathematical definitions here give only an exclusion of the
stated finite grammar; they do not estimate unrestricted terminal exploitability.

This settles the most immediate adjacent-pair extension of the failed
single-joint return. A concrete next question is whether changing the active
support inside the adjacent block, or using three adjacent joint dates, can
produce a positive exit at this same raw table.

## 7. A two-pair reset with a produced quadratic macro

Ordinary mathematics, not Lean checked. A joint02 date, ten solo3 dates,
and a finite truncation of a contracting joint03 reset produce arbitrarily
accurate finite periodic profiles. The period may grow with accuracy.
The [passive-payoff threshold theorem](../exports/PASSIVE_THRESHOLD_UNIFORM_EQUILIBRIUM.md)
separately covers the old benchmark with
nonnegative own levels; this section is retained as a distinct construction,
not counted or exported as an additional counterexample-class exclusion.

### Raw criterion and finite selection

Write Z_i(D)=r_i(D)-r_i({i}), Gamma_ij=Z_i({j}), and kappa_i=r_i({i}).
Native own singletons are zero. Original own levels may have either sign.
Fix the labeling0,1,2,3 and b=2/5. Require

    k=Gamma03>0, d=-Gamma30>0, A=-Z0(03)>0, B=Z3(03)>0,
    Z0(02)<0, Z0(02)-Gamma02>0,
    r2=Z2(02)>0, r2-Gamma20>0.

Define u=-b Z0(02), Y0=b[Z0(02)-Gamma02]/(1-b), tau=Y0/k, and require
0<tau<1. For i=1,2 put

    c_i=-[Z_i(03)+A Gamma_i3/k+B Gamma_i0/d]/[1+A/k+B/d],
    a_i=(c_i+Gamma_i3)/k, h_i=(c_i+Gamma_i0)/d.

For one variable x form

    w=Gamma30 x(1-b)+Gamma32(1-x)b+Z3(02)xb,
    X2=x r2, D=(1+u/k)(1+w/d),
    L2=(X2+a_2 u+h_2 w+c_2)/D-c_2,
    Y2=x(r2-Gamma20)/(1-x).

After cancelling denominators, the equation

    Y2=tau Gamma23+(1-tau)L2                         (Q)

has a polynomial numerator of degree at most2. Require it not identically
zero. Test its finitely many real roots, retaining any x with0<x<1,w>0
and all the following guards. Put

    S=(1-x)(1-b),
    P1=Gamma10 x(1-b)+Gamma12(1-x)b+Z1(02)xb,
    L1=[P1+S tau Gamma13+a_1 u+h_1 w+c_1-c_1 D]
                                      /[D-S(1-tau)],
    Y1=tau Gamma13+(1-tau)L1, X1=P1+S Y1,
    X=(-u,X1,X2,w), Y=(Y0,Y1,Y2,0), L=(0,L1,L2,0).

The denominator defining L1 is positive because D>1>S(1-tau). Require

    X1 >= Z1(01)x(1-b)+Z1(12)(1-x)b+Z1(012)xb,
    w  >= Z3(03)x(1-b)+Z3(23)(1-x)b+Z3(023)xb.     (J)

Produce q=1-(1-tau)^(1/10) and require, for i=0,1,2,

    min(Y_i,L_i) >= q Z_i({i,3}).                  (S)

The row0 comparison is automatic. Finally for i=1,2 define

    alpha_i=[Gamma_i0-Z_i({i,0})]/(B+d),
    beta_i=[Gamma_i3-Z_i({i,3})]/(A+k),
    gamma_i=[Z_i(03)-Z_i({i,0,3})]/[(B+d)(A+k)],
    U_i=(L_i-Gamma_i3)/k+beta_i,
    W_i=(L_i-Gamma_i0)/d+alpha_i,
    T_i=(L_i+c_i)/(kd)+gamma_i,

and require

    L_i>0, U_i>=0, T_i>=0, L_i+min(W_i,0)w>0.      (R)

These are finite raw-table calculations and a quadratic root selection.
No strategy, continuation vector or favorable return is supplied as input.
Every table passing them has a fixed uniform-equilibrium payoff kappa+L.

### Exact roots, limiting endpoint and finite error

At joint02 with hazards(x,0,b,0) and successor Y, owners0,2 are indifferent
by the definitions of Y0,Y2. Its current annotation is X; (J) supplies the
two quiet comparisons. Equation(Q) and the L1 equation give

    Y=tau Gamma[:,3]+(1-tau)L.

Ten equal solo3 hazards q therefore take Y chronologically to L. All values
lie on the segment from Y to L. Owner3 is indifferent, and(S) bounds every
quiet offer at each of those ten dates.

Starting with continuation X, repeatedly PREPEND joint03 roots. If the
current continuation is(-u_n,v1_n,v2_n,w_n), use

    q0=w_n/(B+d+w_n), q3=u_n/(A+k+u_n), q1=q2=0.

Active indifference is literal: -A q3=k q3-(1-q3)u_n and
B q0=-d q0+(1-q0)w_n. Thus

    u_(n+1)=A u_n/(A+k+u_n), w_(n+1)=B w_n/(B+d+w_n).

Put r=A/(A+k)<1 and h=B/(B+d)<1. Then u_n<=u r^n and w_n<=w h^n.
For D_n=(1+u_n/k)(1+w_n/d), substitution in passive Bellman recursion gives

    [v_i,n+a_i u_n+h_i w_n+c_i]/D_n=L_i+c_i.

Its three coefficient identities are

    a_i k-c_i=Gamma_i3, h_i d-c_i=Gamma_i0,
    -a_i(A+k)-h_i(B+d)+c_i=Z_i(03)-Gamma_i0-Gamma_i3.

Hence the N-step initial annotation X_N converges to L, with

    |v_i,n-L_i| <= |L_i-Gamma_i3|u r^n/k
                 +|L_i-Gamma_i0|w h^n/d
                 +|L_i+c_i|uw(rh)^n/(kd).           (E)

Together with the active-coordinate bounds this explicitly bounds
 delta_N=||X_N-L||_infinity by a geometrically vanishing quantity.
After division by positive opponent survival, a quiet owner's exact
Continue-minus-Quit margin at a reset root is

    L_i+U_i u_n+W_i w_n+T_i u_n w_n.

Since u_n>=0 and0<=w_n<=w, (R) proves strict positivity at EVERY reset
step. Thus no infinite list of comparisons remains unverified.

### All behavioral deviations and one fixed uniform target

For each N, execute the N reset roots in reverse prepending order, then the
joint02 macro, then the ten solo3 dates, and repeat this FINITE period.
Use annotations X_N through the reset to X, then Y through the solo return.
At the last solo date its nominal successor L is replaced by X_N. This is
the only seam; its Bellman error and each action-endpoint excess are at most
 delta_N. A forced Quit payoff is unaffected by successor values; a forced
Continue payoff changes by opponent survival times the coordinate change.

At the macro date, every player has an opponent who quits with probability
at least g=min(x,b)>0. Under ANY complete unilateral behavioral replacement,
including nonperiodic stopping rules, survival through k periods is at most
(1-g)^k. Opponents retain their prescribed private product hazards. Unrolling
the exact endpoint inequalities, the seam error is charged at most once per
period, so every deviator's native terminal payoff is at most
 (X_N)_i+delta_N/g. The bounded terminal annotation remainder vanishes.
Prescribed Bellman recursion gives |U_i^N-(X_N)_i|<=delta_N/g. Consequently

    full MAX terminal regret <=2 delta_N/g,
    ||U^N-L||_infinity <=delta_N(1+1/g).

These bounds do not grow with the number of reset dates. Every unilateral
replacement absorbs almost surely, so arbitrary original own levels add
exactly kappa_i to every terminal comparison. The fixed target is kappa+L.
If M bounds this fixed game's original rewards, expected absorption time
is at most(N+12)/g under every replacement. Terminal and T-date-average
payoffs differ by at most2M(N+12)/(gT). Choose N for the desired terminal
accuracy, then a horizon threshold; that SAME profile works for every larger
horizon and the SAME target. No infinite reset is executed before another
date, and no exact finite-period equilibrium is asserted.

### One exact example and independent-coordinate scope

Use the canonical native table from Sections5–6, with
 e=12281660/12608823, K>=1 and arbitrary R=Z0(23), p=Z2(12).
Let x be the unique root in[78295/10^6,78296/10^6] of

    P(x)=31906921688093 x^2-21898290083611 x+1518934471518.

P has opposite signs at the endpoints and P'<0 throughout that interval.
With b=2/5 the raw formulas give u=1/25, tau=1/5,
 w=(58-583x)/145, X2=(2+e)x, Y2=e x/(1-x). The closure identity is

    (1-tau)L2-tau-Y2
          =P(x)/[31143792810(x-1)(583x-203)]=0.

Exact rational bounds throughout the stated bracket are

    85/1000<w<86/1000, 35/100<L1,L2<36/100,
    25/100<X1<27/100, 8/100<Y2<9/100.

For each bound, cancel its rational difference and substitute
x=78295/10^6+y/10^6. Numerator and denominator have strictly positive
Bernstein coefficients on[0,1] after a common sign change; their degrees are
at most2 and1. This finite exact test proves the bounds. They imply(S):
tau/10<=q<=1/40, 3q<Y2, Y1=(4/5)L1-3/5>-3/5>-100q, and row0 is
nonnegative. For(R), the specialized coefficients are

    U1=(L1+3)/3+97/23, W1=L1-1/2,
    T1=(L1+45/26)/3-5/46,
    U2=(L2+1)/3-4/23, W2=L2-2-e/2,
    T2=(L2+29/26)/3+95/46.

The interval bounds prove U_i,T_i>0 and L_i+min(W_i,0)w>0. Quiet1's
joint offer is negative for K>=1 while X1>0. Quiet3's joint comparison is
exactly t=Z3(023)<=Tstar, where Tstar=101/x-104-219/29>1178.
Thus t=987 is strictly inside this producer, for arbitrary own levels.
The simple selected root and strict guards persist in an open neighborhood
of this example in all60 original reward coordinates.

Thirty native coordinates are invisible to this construction and every
unilateral deviation: all24 Z_j(D) with j in{0,2,3} and1 in D;
Z0(23),Z0(023); and Z1(23),Z1(023),Z1(123),Z1(0123). They may vary
independently without bound. Prescribed coalitions lie in{0,2,3,02,03}; a
player1 deviation can add1 only to the empty set or0,2,3,02,03, giving its six
possible payoff cells1,01,12,13,012,013. This checks the complete agency
scope. These properties describe this producer; no separate coverage
increment over the newer passive-payoff threshold theorem is asserted.
