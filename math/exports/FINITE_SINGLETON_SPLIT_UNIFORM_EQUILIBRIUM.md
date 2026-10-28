# Uniform equilibrium by a finite singleton step at a negative return boundary

This theorem replaces a positive return-value requirement by an explicit
one-variable joining test. It produces uniform equilibria on the stated raw
reward class. It is ordinary mathematics, not checked in Lean; arbitrary
Fin4 remains open.

## 1. Exact raw statement

There are four players 0,1,2,3. At every live date each independently chooses
Continue or Quit. The first nonempty quitting coalition D absorbs at the
fixed real payoff vector r(D), paid thereafter. Live play and literal
AllNever pay zero. A unilateral deviation may replace the complete
behavioral strategy. Put

    kappa_i=r_i({i}), Z_i(D)=r_i(D)-kappa_i,
    Gamma_ij=Z_i({j}), Gamma_ii=0.

Literal Never and live play pay zero. No same-table affine invariance of
Never is assumed. The proof constructs opponent-absorbing periodic laws,
where the passage from Z to r is valid against every complete deviation.
All randomization is independent and private.

Require the eight strictly positive singleton parameters

    beta0=-Gamma02, d=-Gamma30, e=Gamma32, f=Gamma20,
    k=Gamma03, h0=-Gamma23, g=-Gamma13, d1=-Gamma31.

Gamma01 and Gamma21 are arbitrary finite numbers. Set ell=Gamma12,
n0=Gamma10 and define the explicit rational quantities

    C=(f e k-h0 d beta0)/(f e+h0(e+d)),
    b=C/(C+beta0),
    a=e C/[C(e+d)+d beta0],
    L0=(1-a)(1-b),
    A10=a n0+(1-a)b ell,
    J=[g C-A10(k-C)]/[k-L0(k-C)].                    (1)

Assume

    C>0, 0<J<g C/k.                                 (2)

Then 0<C<k and 0<a,b<1. Put

    B1=b ell-(1-b)J, B3=b e,
    A1=a n0+(1-a)B1=(g C-kJ)/(k-C)>0,
    A2=a f>0.

No sign condition is imposed on B1.

Define the three joining coordinates

    zeta_j=Z_j({0,j}), j=1,2,3.

Require zeta_2<=f and nonemptiness of the following open affine interval:

    0<x<a,
    X1=B1+x(n0-B1)>0,
    X1>x zeta_1,
    X3=B3-x(B3+d)>x zeta_3.                         (3)

This is a finite one-variable interval test, not a supplied strategic object.
The strict inequalities determine open half-lines. Their intersection with
(0,a), if nonempty, has finite endpoints L<U and an internally selected
midpoint x=(L+U)/2. The inequality X3>0 follows from x<a and is retained
in the proof. For example, a convenient entirely explicit sufficient test is

    H=n0-max(zeta_1,0)>0,
    zeta_2<=f,
    B3 H > max(-B1,0)[d+max(zeta_3,0)].              (4)

Under (4), choose x strictly between

    L=max(-B1,0)/(H+max(-B1,0)),
    U=B3/[B3+d+max(zeta_3,0)].                       (5)

One may use the midpoint. The displayed strict condition ensures L<U;
U<=a. Condition (4) is sufficient; the complete criterion is the interval (3)
together with zeta_2<=f.

Assume also

    A=-Z1(13)>g, c=Z2(23)>0,
    u=Z3(13)>=0, v=Z3(23)<e;
    Z0(D)<=0 for each nonsingleton D containing 0.

The ten other core coordinates are the four row 0 entries on12,13,23,123,
Z1(23),Z1(123),Z2(13),Z2(123),Z3(12),Z3(123). They remain arbitrary
finite numbers. Choose q0>=0 with
q0>(c/h0)Gamma21. Then there is finite M such that every

    Z1(12)=-K, Z2(12)=p,
    p<=-q0, K>=M(1+|p|)                              (6)

has a uniform-equilibrium payoff against all complete behavioral deviations.
The constant M may depend on Gamma, A,c,u,v,q0, the ten core remainders,
and the three zeta values. The other eighteen nonpivot joining coordinates on
nonsingleton coalitions containing 0, and all four original own levels, are arbitrary.
M can be chosen uniformly on compact sets satisfying the displayed guards,
including the weak condition zeta_2<=f. The interval and the other strict
conditions must remain separated from failure.


## 2. Production of the finite core and every sufficiently large K

We construct the required finite roots, continuation values and return
from the raw data in Section 1. No sign of B1 is used.

Write

    a0=c/h0, delta=c/(c+h0), r=1/delta,
    B0=A+a0 g, m=e/d1, q=-p,
    h=1/(1+q), hmax=1/(1+q0).

Fix N large and t=delta^(N-1). Use variables J_* near J, terminal phase
vartheta near [delta J/B0,J/B0], and Lambda>0; set

    alpha=t h Lambda=1/K,
    beta=-t(1-h)Lambda=alpha p.

The h=0 endpoint is only a compactified parameter for uniform estimates.
All physical games have h>0. A core root has independent hazards
(0,alpha Y,alpha Z,w). Its Quit values for players 1,2 are exactly

    Q1=-Z(1-w)-A w+alpha(A+Z1(123))Zw,
    Q2=beta Y(1-w)+c w+alpha(Z2(123)-c)Yw.

Its passive contributions and Continue survival coefficients are

    P1=alpha ell Z(1-w)-g w(1-alpha Z)+alpha Z1(23)Zw,
    P2=alpha Gamma21 Y(1-w)-h0 w(1-alpha Y)+alpha Z2(13)Yw,
    H1=(1-alpha Z)(1-w), H2=(1-alpha Y)(1-w).

Define required successor coordinates F_i=(Q_i-P_i)/H_i for i=1,2.
Introduce coordinates

    theta=w/(1+a0 w),
    Jcore=[(1-w)Z+B0 w]/(1+a0 w),
    w=theta/(1-a0 theta),
    Z=[Jcore-B0 theta]/[1-(a0+1)theta].               (C1)

Given the next Y, the next w,Z that make owners 1,2 indifferent satisfy

    wnext=(F2-beta Ynext)
           /[c-beta Ynext+alpha(Z2(123)-c)Ynext],
    Znext=(-F1-A wnext)
           /[1-wnext-alpha(A+Z1(123))wnext].         (C2)

All denominators are uniformly nonzero near the reference arrays below.
In the coordinates(C1), substitution into(C2) gives analytic maps

    theta_next=r theta+t fcore,
    Jcore_next=Jcore+t gcore.                        (C3)

The quotients defining fcore,gcore extend analytically through t=0 because
(C2) becomes exactly theta_next=r theta,Jcore_next=Jcore there.
They and any fixed finite number of derivatives are uniformly bounded on
small compact neighborhoods of the reference data, including h=0.

For the row 3 equation put z3=Z3(12), w3=Z3(123),

    D3=(w3-u-v)-(z3-Gamma31-e),
    R=u Ynext+v Znext+alpha(w3-u-v)Ynext Znext.

Its exact backward equation is

    Y=[R(1-alpha Z)-(v-e)Z]
        /[(u+d1)+alpha D3 Z+alpha R(1-alpha Z)].     (C4)

At the last root set R=0; its required successor row 3 is then zero.
The derivative in next Y at t=0 is rho=u/(u+d1)<1.

Prescribe Jcore_0=J_* and theta_(N-1)=vartheta. Reference arrays are

    J_j^0=J_*, theta_j^0=delta^(N-1-j)vartheta.

Because A>g and J<gC/k<g, one has B0>(a0+1)J. The denominators in(C1)
stay positive near the closed phase interval. The reference Z_j decrease
and are nonnegative. At t=0, equation(C4) reads

    (u+d1)Y_j=uY_(j+1)+vZ_(j+1)+(e-v)Z_j,
    (u+d1)Y_(N-1)=(e-v)Z_(N-1).                    (C5)

Its right side is nonnegative: if v>=0 both displayed Z coefficients are
nonnegative, and if v<0 rewrite them as
 e Z_j+(-v)(Z_j-Z_(j+1)). Nonterminal Y_j,Z_j are bounded positively away
from zero on the reference interval. Terminal Y has the sign of terminal Z.
The early steady value is Y=mJ_*.

For small t, solve(C4) backward. Its array derivatives in sup norm are
uniformly bounded by geometric series with any fixed rho1 in(rho,1).
On arrays with J radius C1 Nt and theta radius C2 t, iterate

    J_j(new)=J_*+t sum_(l<j)gcore_l,
    theta_j(new)=delta theta_(j+1)-delta t fcore_j  (j<N-1),
    theta_(N-1)(new)=vartheta.

Choose C1,C2 from the uniform bounds. This map preserves its box and has
sup-norm derivative at most max(C Nt,delta+C t)<1 for large N. The
contraction theorem gives a unique exact orbit in this neighborhood, with

    |J_j-J_*|<=C jt, |theta_j-theta_j^0|<=C t.        (C6)

The same estimates hold for first parameter derivatives. To control the
scaled entrance, choose eta with max(delta,rho1)<eta<1. Convolving the
forward delta and backward rho1 bounds gives, also in first derivatives,

    |Y_j-mJ_*|<=C[eta^(N-1-j)+(j+1)t].               (C7)

At t=theta=0, Y=Ynext=mJ_*, direct substitution gives
fcore=-h Lambda Gamma21 mJ_*/c. Multiplying(C7) by delta^(j+1), summing,
and using sum_(j>=0)delta^(j+1)=a0 yields

    sum_(j=0)^(N-2)delta^(j+1)fcore_j
        -> -a0 h Lambda Gamma21 mJ_*/c              (C8)

in C1. All errors are bounded by polynomial factors in N times a geometric
sequence and tend to zero uniformly in the compact h interval. This also
proves compact uniformity in the fixed raw coefficients.

Impose Q2(first)=0. Its exact entrance equation is

    theta_0/t=(1-h)Lambda Y_0
       /[c+t Lambda((a0+1)(1-h)+h(Z2(123)-c))Y_0].

Combining(C3),(C8), the limiting equation is

    vartheta-Lambda(mJ_*/c)[1-h-a0 Gamma21 h]=0.      (C9)

The coefficient of Lambda is uniformly positive because q0>a0 Gamma21.
For Gamma21<0,q0=0 is permitted.

Let the last successor be E_N=(E0_N,-x_N,E2_N,0), where x_N=-F1(last),
E2_N=F2(last), and propagate row 0 backward. The entrance C_N has the C1
limit

    D=1-(a0+1)vartheta,
    C0=k(1-D)+D E0, C1=-J_*, C2=0, C3=0,
    x=[J_*-g(a0+1)vartheta]/D,
    E2=(c+h0)vartheta/D.                            (C10)

Indeed the limiting pure3 survival telescopes to
D/[1-a0 t vartheta], and the summed nonsolo3 perturbations and derivatives
are O(N^2 t). The exact entrance has C2_N=0; its C3_N need not be zero but
tends to zero. Define exactly

    b_N=C0_N/(C0_N+beta0),
    B1_N=b_N ell+(1-b_N)C1_N,
    B3_N=b_N e+(1-b_N)C3_N,
    a_N=B3_N/(B3_N+d),
    A1_N=a_N n0+(1-a_N)B1_N, A2_N=a_N f,
    C_N=(C0_N,C1_N,0,C3_N),
    B_N=(0,B1_N,0,B3_N), A_N=(0,A1_N,A2_N,0).

Impose the two outer equations

    A1_N(k-E0_N)=g E0_N-k x_N,
    A2_N(k-E0_N)=k E2_N+h0 E0_N.                    (C11)

At t=0 multiply by D to eliminate vartheta. The equations become

    A1(k-C)=gC-kJ_*, A2(k-C)=h0 C.

The second, divided by C>0, has numerator
 f e k-h0 d beta0-[f e+h0(e+d)]C,
so selects exactly the value C in(1), with nonzero derivative. The first is
linear in J_* with positive coefficient k-(1-a)(1-b)(k-C), selecting exactly
J in(1). The change between C and E0 has positive derivative D. Together
with(C9), the Jacobian in(J_*,E0,Lambda) is uniformly invertible.
The implicit function theorem therefore gives actual branches with

    J_N->J,
    E0_N->[C-k(a0+1)vartheta]/[1-(a0+1)vartheta],
    Lambda_N->vartheta/[(mJ/c)(1-h-a0 Gamma21 h)].    (C12)

Lambda_N is positive and strictly increasing in vartheta for all large N.

The terminal legality tests have limits

    Z_last=[J-B0 vartheta]/D,
    E2-cx/A=(c/A)[rB0 vartheta-J]/D.                 (C13)

Their simple zeros give exact transverse boundaries vartheta_N^+ and
vartheta_N^- tending to J/B0 and delta J/B0. Between them the last Z and
the wash margin are nonnegative; terminal Y has the sign of terminal Z.
The nonterminal entries remain positive by(C5)--(C7).

All physical w are nonnegative, including when Gamma21>0. Write y=alpha Y,
s=Z2(123),z=Z2(13). At a root,

    Q2=-q y+[c+y(s-c+q)]w,
    P2=Gamma21 y+[-h0+y(z-Gamma21+h0)]w.

For y small, the Q2 bracket is positive and the coefficient of w in P2
is negative. From Q2>=0 one obtains

    P2<=y[c Gamma21-q h0
           +y(Gamma21(s-c)+q(z+h0))]/[c+y(s-c+q)]<0 (C14)

when y>0: q-a0 Gamma21 has a positive lower bound proportional to 1+q.
The first Q2 is zero by(C9), hence its F2 is positive, and(C2) inducts
strictly positive subsequent w. The zero terminal-y cases follow directly.
All hazards are less than one by the compact limiting bounds and small t.
Core owners 1,2,3 are therefore exactly indifferent; absent terminal hazards
also obey equality. Row0 annotations stay positive because their limiting
pure3 recursion joins positive E0 and C. Its Quit offers are nonpositive
by the stated seven row 0 caps. No sign of B1 is used in these arguments.

For the finite wash, from(s0,-v0,z0,0) use solo 3 hazard v0/A while
0<v0<g,s0>kv0/g,z0>=cv0/A. All root comparisons are legal. Put
r0=1-g/A in(0,1). After n regular roots the survival and values satisfy

    S_n=1-x/g+(x/g)r0^n,
    v_n=x r0^n/S_n,
    z_n=[E2+h0(1-S_n)]/S_n.

A final hazard v_n/g sets row 1 exactly zero and is legal once

    r0^n<=[gE2+h0x]/[(c+h0)x].

The right side is at least(gc/A+h0)/(c+h0)>0, so a uniformly finite n
suffices. The resulting endpoint is

    V0=(E0-kx/g)/(1-x/g), V1=0,
    V2=(E2+h0x/g)/(1-x/g), V3=0.

Here 0<V0<k, and one solo 3 aggregate V0/k connects V to A_N exactly by(C11).
The altered solo 0 execution in the theorem leaves(C11) unchanged.

Finally the phase intervals cover ALL sufficiently large K/(1+|p|).
At vartheta_N^+, the last core Y=Z=0 and the last root is pure solo 3,
with current coordinates(-Aw,cw) in rows 1,2. Deleting it gives the shorter
core exactly at its wash boundary. The wash and return equations change
only by their common survival factor; the entrance alpha,beta are unchanged.
Uniqueness of the nearby finite branch identifies this with the N-1 lower
boundary at the identical K,p. Since Lambda_N increases strictly with phase,
each phase interval gives one full closed K interval and successive intervals
join with no gaps. Its hK endpoints equal1/(t Lambda_N) and tend to infinity.
For one sufficiently large N0 the lower hK endpoint is continuous on the
compact h interval and has finite maximum M. Thus all K>=M/h are produced,
which is (6). The three new finite-step strict guards are open conditions
on the convergent outer data, so increasing N0 ensures them as well and does
not affect this endpoint identity or interval coverage.

## 3. Execution across the negative return boundary

Select one x satisfying (3), before choosing a sufficiently large core.
For every resulting sufficiently large N define

    X_N=x Gamma[:,0]+(1-x)B_N,
    theta_N=(a_N-x)/(1-x).

By (C12) and strictness, 0<x<a_N, 0<theta_N<1 and

    X_N0=0, X_N1>0, X_N2=x f>0, X_N3>0,
    X_Nj>x zeta_j for j=1,3; X_N2>=x zeta_2.        (9)

The exact identity

    A_N=theta_N Gamma[:,0]+(1-theta_N)X_N             (10)

holds because (1-theta_N)(1-x)=1-a_N. Thus execute the selected aggregate as

    A_N --diffuse solo 0 of total mass theta_N--> X_N
        --one finite solo 0 root of hazard x--> B_N.

This changes no return value, no total absorption, no core equation, and no
selected target. The diffuse prefix has nonnegative annotations for all
quiet players: its coordinate numerators interpolate affinely between A_N
and X_N, whose quiet coordinates are nonnegative. The active0 value is
zero throughout. Its fine subdivision has the
vanishing cap error established in Section 4.

At the finite root, owner 0 is exactly indifferent because its singleton
reward and B_N0 both vanish. A quiet player's immediate Quit offer is
exactly x zeta_j, while its Continue payoff is X_Nj. Equation(9) proves the
complete root comparison. Row2 may tie: C_N2=B_N2=0 exactly, so
X_N2=x f>=x zeta_2 for every finite N, without a limiting error. Only singleton0 and pairs
{0,j} occur under one unilateral replacement at this date.

The following finite 2 root is also legal for all sufficiently large K.
Its row 1 Quit offer is -K b_N, whereas its Continue value B1_N stays
bounded and b_N stays bounded away from zero. Its row 3 Quit offer is
v b_N, below B3_N=b_N e+(1-b_N)C_N3 by v<e and C_N3->0.
Its row 0 offer is nonpositive, with value zero, and owner 2 is indifferent
because C_N2=0. These are the full immediate root comparisons.

B1_N may be negative. No empty test is inserted
between the finite 0 root and the finite 2 root. Player1 cannot obtain its
zero singleton there without joining one of the prescribed root hazards.
Its comparisons are the actual x zeta_1 and -K b_N, not an artificial zero.

## 4. Fixed payoff and all behavioral replacements

The complete selected period is now

    A_N -> diffuse 0 -> X_N -> finite 0 -> B_N -> finite 2 -> C_N
        -> core -> finite 3 wash -> V_N -> diffuse 3 -> A_N.

Choose this finite core and its reference annotations once for the fixed
game, before accuracy. Refine only the indicated diffuse blocks. Conditional
subdivision preserves their total survival, hence every prescribed payoff
identity and the initial target A_N remain exact.

All finite roots have exact Continue/policy equations and nonprofitable Quit
comparisons, including the new root checked in(9). The diffuse 0 block has
immediate deviation gain at most

    err=mesh max(0,zeta_1,zeta_2,zeta_3).

On the final diffuse 3 block, row 0 and row 1 annotations are nonnegative,
and their joining rewards are nonpositive. Row2 annotations stay above
min(V_N2,A_N2)>0; choose every refined hazard q so that c q is below that
minimum. This makes all comparisons on that block exact.
Deleting player 0 leaves opponent absorption at the finite 2 root, with mass
at least b_N per period. Deleting any other player leaves the total solo 0
mass a_N, split but unchanged. Thus opponents-only period absorption is at
least rho_N=min(a_N,b_N)>0 for every deviator.

Unroll the complete Bellman cap over this literal finite period, including
all dates and Never. The largest excess cap D satisfies

    D<=max(err,(1-rho_N)D),

so D<=err. This is a bound against every complete private stopping law,
not only responses inside a prescribed menu. Opponent absorption is uniform
under a deviation, and policy absorption is proper; prescribed terminal
payoffs are exactly A_N in native coordinates. Passing to original rewards
adds kappa_i to every prescribed and deviating terminal payoff.

For period length L and original reward bound R, opponents-only expected
absorption time is at most L/rho_N+1. The terminal-versus-T-horizon error is
at most 2R(L/rho_N+2)/T, uniformly over deviations. Choose mesh and then T
for any requested accuracy. The same target kappa+A_N precedes that choice.
This proves the original uniform-equilibrium contract.


## 5. An explicit newly covered interval

Let ell be a real parameter and use

    Gamma=[0,3,-1,3; 2,0,ell,-3; 2,-2,0,-1; -1,-2,1,0].

Set zeta=(-1,-10,1), A=100,c=3,u=10,v=-100 and q0=0. The formulas give

    C=5/4, J=1-ell/4, a=5/14, b=5/9,
    B1=(6ell-4)/9, B3=5/9, A1=(3/7)(1+ell), A2=5/7.

The singleton conditions require -1<ell<4. In the sufficient split test,
H=2 and d+max(zeta_3,0)=2; hence that test holds precisely when ell>-1/6.
Consequently every fixed

    -1/6<ell<4, p<=0, K>=M(ell)(1+|p|)

in the following full native table has UE. The threshold may also depend
on any fixed higher coefficients being varied. Here kappa_i may be arbitrary;
the displayed table specifies Z, and the actual terminal reward is kappa+Z.

| D | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
|0|0|2|2|-1|
|1|3|0|-2|-2|
|2|-1|ell|0|1|
|3|3|-3|-1|0|
|01|0|-1|-10|-12|
|02|0|5|-10|7|
|12|-12|-K|p|-6|
|03|-3|3|-5|1|
|13|2|-100|-1|10|
|23|-6|9|3|-100|
|012|-13|6|-9|11|
|013|-7|8|10|-10|
|023|-7|-8|-3|15/2|
|123|-8|11|2|1|
|0123|-5|-9|8|21/2|

For ell=1/2 one has J=7/8, B1=-1/9 and A1=9/14. The exact interval
in (3) is (1/19,5/23). Choose x=1/10. The limiting outer chain is

    V=(9/17,0,7/17,0)
      --diffuse 3 mass 3/17--> A=(0,9/14,5/7,0)
      --diffuse 0 mass 2/7--> X=(0,1/10,1/5,2/5)
      --finite 0 mass 1/10--> B=(0,-1/9,0,5/9)
      --finite 2 mass 5/9--> Cvec=(5/4,-7/8,0,0).

At finite 0, the quiet Quit offers are (-1/10,-1,1/10); their exact margins
below X are (1/5,6/5,3/10). At finite 2 the offers for players 0,1,3 are
0,-5K/9,-500/9, at most their values 0,-1/9,5/9 for K>=1/5.
The finite-core perturbations preserve the strict margins for sufficiently
large K. This does not give a numerical bound on the full threshold M,
and in particular does not assert UE for the displayed K=100 by this proof.

For comparison, nonnegativity of the entire diffuse 0 arc requires B1>=0,
which here means ell>=2/3; strict positive-endpoint methods require ell>2/3.
The finite step covers the additional interval (-1/6,2/3), including ell=0.
At ell=-1/6 the strict split interval collapses to x=5/23. For smaller ell
it is empty: the lower bound that keeps X1 positive exceeds the upper bound
from player 3's joining comparison. This is a boundary of this construction,
not evidence of nonexistence of equilibrium. No threshold uniform up to
that boundary is asserted.

## 6. Complete coverage comparison

For the table in Section 5 with ell=1/2, p=0 and kappa_i=1, consider every
K>=100. The construction applies for sufficiently large K; the following
exclusions hold throughout this whole ray.

Its singleton matrix and inverse are

    Gamma=[0,3,-1,3; 2,0,1/2,-3; 2,-2,0,-1; -1,-2,1,0],
    det Gamma=35/2,
    Gamma^-1=[2/5,2/7,12/35,9/35;
               1/5,2/7,-9/35,2/35;
               4/5,6/7,-6/35,48/35;
               2/5,0,1/5,2/5].

The eight required singleton signs admit only the identity among all
24 relabelings. Thus the fully diffuse outer return fails its B1>0
requirement for every labeling, and the alternative return requiring
Gamma10<0 also fails: the only labeling has Gamma10=2. Positive playerwise
row scaling preserves these failures. For the fully diffuse return the
sign of B1 is the sign of an actual normalized phase payoff; for the
alternative it preserves the raw singleton sign.

### Exact stationary and sure-root exclusions for the entire ray

For independent root hazards q in [0,1]^4 define

    H_i=product_(j!=i)(1-q_j),
    P_i=sum_(nonempty S subset opponents) weight_q(S) Z_i(S),
    Q_i=sum_(S subset opponents) weight_q(S) Z_i(S union{i}),
    F_i=(1-H_i)Q_i-P_i,
    L_i=min({-1} union {Z_i(S): nonempty S excludes i}),
    G_i=Q_i-P_i-H_i L_i.

Here weight_q(S)=product_(j in S)q_j product_(j outside S,i)(1-q_j).
For this complete table L=(-12,-8,-10,-12), independently of K.
A nonzero stationary Nash profile must have F_i<=0 at q_i=0, F_i=0
at 0<q_i<1, and F_i>=0 at q_i=1. AllNever is not an original-game
stationary Nash profile because each own singleton is one.

At any root with a sure quitter, every actual native continuation cap is
at least L_i: its pure-Never response averages nonempty opponent rewards
and the original AllNever value, which becomes -1 in that comparison.
If there is a unique sure quitter, substituting L_i only improves its
Quit comparison; every other owner has H_i=0. With two sure quitters,
every H_i is zero. Therefore every such Nash root satisfies the same
quiet/mixed/sure signs for G. This covers arbitrary actual continuations,
not just stationary or prescribed finite tails.

Only row 1 varies with K, and its exact dependence is

    F1(K)=F1(100)-(K-100)(1-H1)(1-q0)q2(1-q3),
    G1(K)=G1(100)-(K-100)(1-q0)q2(1-q3).

The following finite rational certificate excludes all these necessary
systems uniformly for K>=100. Enumerate the 80 nonzero patterns in
{0,1,*}^4 for F, and the 65 patterns containing a sure owner for G.
If q2=0, q0=1, or q3=1, retain every baseline sign. Otherwise retain
rows 0,2,3; replace row 1 by its baseline inequality >=0 when mixed or
sure, and omit it when quiet. These are weaker necessary conditions.

For F one direct exclusion is q0=0, player 2 mixed, and q1 or q3 positive:

    Q2=q3(3-q1)>=0,
    P2=-2q1-q3+2q1q3<0,

so F2>0. A pattern with just one mixed owner j and no sure owner is
excluded by a retained quiet recipient i with Gamma_ij<0 and
Z_i({i,j})>=0. For j=0,1,2,3 choose respectively i=3,2,0,2.
The omitted row 1 is never used for this exclusion.

For every remaining pattern with at least two mixed coordinates S, put
A=Gamma_SS and V=A^-1; all these principal matrices are invertible.
Add the V linear combinations of the mixed baseline polynomials. Their
signs are equality, except when mixed row 1 was relaxed: the combination
has sign >=0, <=0, or =0 according to the coefficient of that row.

For a pattern without a sure owner, write the mixed baseline vector as
-Aq+R(q), where R has only terms of total degree at least two. If row 1
was not relaxed then q=VR. If it was relaxed, the direct exclusions above
leave principal inverses with nonnegative column1, so q<=VR. Set

    c_i=sum of absolute coefficients in R_i,
    D=max_i sum_j |V_ij| c_j.

Every nonzero solution must satisfy ||q||_infinity>=1/D. The following
exact constants therefore exclude the indicated closed origin cubes:

| Mixed set S | D | E, with 2^-E<1/D |
|---|---:|---:|
|01|1/2|1|
|02|5|3|
|03|1|1|
|13|100/3|6|
|012|587|10|
|013|1609|11|
|023|3869/5|10|
|0123|315709/35|14|

The other no-sure sets 12,23,123 were directly excluded. All these bounds
use only the baseline K=100 polynomials and remain necessary at every K.

After substituting the fixed coordinates of a pattern, every retained
polynomial has degree at most two in each remaining variable. For a
polynomial sum_m a_m x^m in d variables its tensor degree-two Bernstein
coefficient indexed by k in {0,1,2}^d is

    b_k=sum_(m<=k) a_m product_i[binom(k_i,m_i)/binom(2,m_i)].

Clear a common positive denominator. Reject a box if an equality has all
coefficients strictly positive or strictly negative, or an inequality has
all coefficients of its forbidden strict sign. Also reject every box
contained in its excluded origin cube. Otherwise bisect the coordinate
subdivided least often, resolving ties by player index, and process the
left child first. The scaled one-coordinate degree-two subdivision is

    (a,b,c) -> left (4a,2(a+b),a+2b+c),
                right (a+2b+c,2(b+c),4c).

Direct and fixed-coordinate exclusions count as one node. The prescribed
exact calculation terminates with 862 nodes for all 80 stationary patterns
and 365 nodes for all 65 sure-root patterns. No unresolved box remains.
The complete input table, relaxed systems, origin estimates and arithmetic
rules are specified here; no numerical root search or external payload
is a premise.

There is also a positive stationary regret floor for each fixed table in
this ray. A sequence of stationary profiles with full regret tending to
zero has a convergent hazard subsequence. Every nonzero limit satisfies the
excluded F sign system, so the hazards would have to tend to zero. Normalize
q by sum_i q_i and pass to a limit x>=0 with sum_i x_i=1. Quitting immediately
gives Gamma x>=0. If x_i>0 and sum_(j!=i)x_j>0, the Never response gives
x_i(Gamma x)_i=0 by comparing the limiting prescribed native payoff
(Gamma x)_i with the Never payoff (Gamma x)_i/(1-x_i). A singleton support
already violates Gamma x>=0, since every column has a negative entry.
A support S of size at least two would give Gamma_SS x_S=0, impossible
because all its principal matrices are invertible. Thus no such sequence
exists. No stationary approximation is hidden at the zero-hazard boundary.

Consequently no stationary equilibrium exists on this ray for K>=100,
and no full Nash root with a sure quitter can have any actual continuation
cap. This also excludes stationary producers and sure-first punishment
producers over their complete selection sets. It does not exclude arbitrary
nonstationary approximate equilibria, which are supplied by the new theorem
above its finite threshold.

### Other complete raw-selector comparisons

The positive singleton graph is strongly connected. In an ordered
nonpositive-anchor criterion, the passive inequalities make the marked set
closed under positive singleton predecessors; consequently that marked set
must be all four players. At coalition123 the participant vector is
(11,2,1)>0, so the first block meeting123 has positive participant sum
for every strictly positive block weighting. No ordered partition works.
The same coalition defeats every supportwise participant balance on123,
and, by continuity near the all-Quit root on that triple, every product-low
criterion imposed on that support.

There is no nonzero nonnegative weight with nonnegative native weighted
payoff on every proper coalition: coalition12=(-12,-K,0,-6) forces
w0=w1=w3=0, and singleton1 then forces w2=0. Thus every member of a
full-proper-payoff ledger family fails before any odds-cover selection.
For a nonnegative weight w define

    H_S(w)=sum_i w_i Z_i(S),
    J_S(w)=sum_(i notin S) w_i[Z_i(S union{i})-Z_i(S)].

Any support-filtered ledger requiring nonnegative singleton H and
nonpositive J at the indicated coalition fails. Its joining inequality at 02 is

    J_02(w)=w1+w3/2<=0,

so w1=w3=0; their mandatory singleton inequalities at 2 and1 then give
-w0>=0 and -2w2>=0. Hence they have no nonzero ledger, regardless of
which support filters or how many weights are selected.

Only principal triple023 has nonnegative inverse. Its outside inverse row
is (-7/10,9/10,-1/5), so the complete passive-child inverse test fails.
The full inverse has mixed column2=(12,-9,-6,7)/35. No permutation or
column-sign choice can make every full inverse column positive.

The unique mutually negative reciprocal singleton pair is13; the unique
mutually positive pair is01. They intersect. A signed four-cycle requires
all non-opposed reciprocal pairs to be disjoint opposite pairs, so no
relabeling supplies its singleton data. Strict matching/favorite classes,
which require two disjoint positive reciprocal pairs, fail for the same
reason. Pair-funded boundary classes requiring two negative reciprocal
pairs also fail.

For alternating-pair criteria requiring nonnegative participant increments,
each of the three pair partitions fails a raw necessary inequality:
01|23 has Z0(01)-Gamma01=-3;
02|13 has Z2(02)-Gamma20=-12;
03|12 has Z0(03)-Gamma03=-6.
Thus arbitrary invariant-cone proof weights cannot repair that premise.
The attached-negative-pair singleton template admits exactly one of the
24 labelings, (3,1,0,2), and its required nonnegative participant premium
fails at Z1(13)=-100. Its alternative retaining unrestricted participant
premiums requires the unused singleton Gamma21=-2 to be nonnegative.
The mixed-trap charge Z3(123)-Z3(12)=7 is positive.

These tests concern the named raw producers and their entire finite or
weighted selection domains. They do not assert that every conceivable
nonstationary certificate fails. In particular they are not a positive
full-strategy regret lower bound.

### Correspondence with checked interfaces

The child comparison uses the hypotheses of
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
The full inverse comparison uses
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse`
in `UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`.
The participant comparison uses `IsSupportwiseBalancedQuittingPremiumTable`
in `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`
and its consumer `exists_uniformEquilibriumPayoff_of_supportwiseBalance`
in `UniformEquilibrium/Quitting/Classification/Existence/SupportwisePremiumUniformPayoff.lean`.
The signed-cycle test uses the literal successor/opposite/predecessor fields
of `SignedFourCycleSingletonData` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`, which
are also required by the larger-eigenvalue consumer
`exists_uniformEquilibriumPayoff_of_reindexedLargerSignedFourCycleSingletonTable`
in `UniformEquilibrium/Quitting/Classification/Existence/SignedFourCycleLargerUniformPayoff.lean`.
These are source-scope comparisons; no new Lean check is asserted.

## 7. Strategic production, source correspondence and formalization

All strategic data are produced from the raw table. The affine interval
selects x; the contraction and implicit selection construct the finite
core and its annotations; exact deletion covers every sufficiently large
K; the finite wash and split return close the period. Section 4 proves the
fixed-target uniform contract against every complete behavioral deviation.
No continuation profile or successful return is an additional hypothesis.

The root-cap identity agrees with
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`). The positive
semantic endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
These are existing declarations; the raw producer proved here is ordinary
mathematics and has not been checked in Lean.

The retained finite roots must remain adjacent where an annotation is below
its own singleton. In particular, inserting empty dates between finite 0,
finite 2 and the core would create extra profitable quitting opportunities.
The generic `MixedCycleSoloMesh.SourceCertificate`
(`UniformEquilibrium/Quitting/Cycles/MixedCycleSourceCertificate.lean`)
requires a singleton floor at every block; that stronger requirement is
not supplied here. Formalization should instead build the literal variable-
length period used in Section 4 and apply the full Bellman recursion.
The primary new obligations are the finite-core producer of Section 2,
the raw interval-to-split calculation, and this refinement with no padding
at negative annotations.

The result excludes a previously surviving raw reward region. It does not
prove arbitrary Fin4, exclude an entire global-source case for arbitrary
higher rewards, or construct an unrestricted positive-gap counterexample.
