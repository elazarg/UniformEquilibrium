# Complete scalar solo3 returns and a positive-continuation raw producer

Owner: CODEX_COORDINATOR. Ordinary mathematics, not checked in Lean. The scalar result completely
classifies this finite solo3 architecture. The raw producer broadens one
higher-reward class; it does not solve arbitrary Fin4 or establish separation
from every existing producer.

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
