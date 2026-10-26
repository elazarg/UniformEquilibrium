# Uniform equilibrium in an explicit singleton chamber

This theorem gives a long-core equilibrium construction under explicit
singleton inequalities, with four unbounded core parameters and ten arbitrary
finite core collision coordinates. It is ordinary mathematics, not checked
in Lean. Fin4 for arbitrary tables remains open.

## 1. Exact raw theorem

There are four players 0,1,2,3. Each live date has independent private Boolean
Continue/Quit choices. The first nonempty coalition D absorbs at r(D), paid
thereafter; live play and literal AllNever pay zero. Put kappa_i=r_i({i}) and
Z_i(D)=r_i(D)-kappa_i for nonempty D, and Gamma_ij=Z_i({j}). Thus Gamma_ii=0.
Every unilateral behavioral replacement is allowed. A uniform-equilibrium
payoff means one target fixed before accuracy, with one profile for that
accuracy valid at every sufficiently long finite horizon.

Define positive singleton parameters

    beta0=-Gamma02, d=-Gamma30, e=Gamma32, f=Gamma20,
    k=Gamma03, h0=-Gamma23, g=-Gamma13, d1=-Gamma31.

All eight displayed parameters must be strictly positive. Gamma01 and
Gamma21 are arbitrary finite numbers. Put ell=Gamma12 and n0=Gamma10 and set

    C=(f e k-h0 d beta0)/(f e+h0(e+d)),
    b=C/(C+beta0),
    a=e C/[C(e+d)+d beta0],
    L0=(1-a)(1-b),
    A10=a n0+(1-a)b ell,
    J=[g C-A10(k-C)]/[k-L0(k-C)].

The additional raw singleton conditions are

    C>0,       0<J<g C/k,       b ell-(1-b)J>0.        (1)

They imply C<k, 0<a,b<1 and ell>0. These formulas are finite rational tests
on the singleton table, not strategic witnesses. They do not assume a
positive inverse column, and some tables they cover may also satisfy older
stationary or child criteria.

Fix four core coefficients satisfying

    A=-Z1(13)>g,       c=Z2(23)>0,
    u=Z3(13)>=0,       v=Z3(23)<e.                    (2)

The ten other coordinates on coalitions 12,13,23,123, excluding
Z1(12),Z2(12) and these four entries, are arbitrary finite numbers. These ten
are the four row0 entries, Z1(23),Z1(123), Z2(13),Z2(123), Z3(12),Z3(123).
Every row0 reward on a nonsingleton coalition containing0 is <=0. The other
21 coordinates on coalitions containing0 and all four kappa_i are arbitrary.

Choose any real q0>=0 satisfying

    q0 > (c/h0) Gamma21.                              (3)

There is a finite constant M, depending only on Gamma, A,c,u,v,q0 and the ten
finite core remainders, such that every game in this family with

    Z1(12)=-K,       Z2(12)=p,
    p<=-q0,         K>=M(1+|p|)                       (4)

has a uniform-equilibrium payoff against all unilateral behavioral deviations.
M is independent of the 21 unrestricted joining coordinates and of all kappa.
It can be chosen uniformly on compact sets of the displayed fixed raw data
satisfying the strict inequalities (1)--(3), with u>=0. No numerical bound on
M is asserted. If Gamma21<0, q0=0 is allowed, covering every p<=0.

## 2. Exact root equations and the singular transfer

At a product root q, let Q_i be Quit now, P_i the payoff contribution from
nonempty opponent coalitions when i continues, and H_i their all-Continue
probability. For continuation value F, the equality Q_i=P_i+H_i F_i makes
owner i indifferent. Write

    r=(c+h0)/c, delta=1/r, a0=c/h0, B0=A+a0 g.

For N core roots put t=delta^(N-1). Compactify q=-p>=q0 by

    h=1/(1+q),   0<h<=hmax=1/(1+q0),
    alpha=t h Lambda=1/K,
    beta=-t(1-h)Lambda=alpha p.

h=0 is only an auxiliary compactification. All fixed-data constants below
may depend on the raw data, and are uniform in h in[0,hmax]. A triple123
root has hazards (0,alpha Y,alpha Z,w). The current values for owners1,2 are

    Q1=-Z(1-w)-A w+alpha(A+Z1(123))Zw,
    Q2=beta Y(1-w)+c w+alpha(Z2(123)-c)Yw.

Their passive numerators are

    P1=alpha Gamma12 Z(1-w)+Gamma13 w(1-alpha Z)
           +alpha Z1(23)Zw,
    P2=alpha Gamma21 Y(1-w)+Gamma23 w(1-alpha Y)
           +alpha Z2(13)Yw.

Set F1=(Q1-P1)/[(1-alpha Z)(1-w)] and similarly
F2=(Q2-P2)/[(1-alpha Y)(1-w)]. Introduce

    theta=w/(1+a0 w),
    Jcore=[(1-w)Z+B0 w]/(1+a0 w),
    w=theta/(1-a0 theta),
    Z=[Jcore-B0 theta]/[1-(a0+1)theta].

Given the next Y, the exact next w,Z are

    wnext=(F2-beta Ynext)
           /[c-beta Ynext+alpha(Z2(123)-c)Ynext],
    Znext=(-F1-A wnext)
           /[1-wnext-alpha(A+Z1(123))wnext].

Converting these to (Jbar,thetabar), at t=0 gives exactly

    Jbar=Jcore,       thetabar=r theta.

Therefore fcore=(thetabar-r theta)/t and gcore=(Jbar-Jcore)/t have removable
analytic extensions. They and every fixed finite number of their derivatives
are bounded on fixed compact neighborhoods of the reference arrays below.
The interfaces are exactly

    theta_next=r theta+t fcore,
    Jcore_next=Jcore+t gcore.                         (5)

For row3 put z3=Z3(12), w3=Z3(123) and

    D3=(w3-u-v)-(z3-Gamma31-e),
    R=u Ynext+v Znext+alpha(w3-u-v)Ynext Znext.

The exact row3 backwards equality is

    Y=[R(1-alpha Z)-(v-e)Z]
        /[(u+d1)+alpha D3 Z+alpha R(1-alpha Z)].       (6)

At the last root use R=0, so its required row3 successor is0. The backwards
next-Y derivative at t=0 is

    rho=u/(u+d1),       0<=rho<1.                    (7)

There is no requirement rho<delta. This is essential when u is large.

## 3. Uniform finite orbits for all large N

Prescribe Jcore_0=J_* near J and terminal phase theta_(N-1)=theta_* near

    I=[delta J/B0,J/B0].

The reference arrays are

    J_j^0=J_*,       theta_j^0=delta^(N-1-j)theta_*.

Because A>g and J<gC/k<g,

    B0>(a0+1)g>(a0+1)J.

All denominators 1-(a0+1)theta_j are bounded positively on a small
neighborhood of I. The reference Z_j are decreasing and nonnegative on I;
for j<N-1 they have a positive lower bound independent of N. At t=0 (6) is

    (u+d1)Y_j=u Y_(j+1)+v Z_(j+1)+(e-v)Z_j,
    (u+d1)Y_(N-1)=(e-v)Z_(N-1).                     (8)

Its right side is nonnegative. If v>=0 both coefficients v,e-v are
nonnegative; if v<0 rewrite the last two terms as
 e Z_j+(-v)(Z_j-Z_(j+1)). Thus every nonterminal Y_j has a positive lower
bound independent of N, while terminal Y has exactly terminal Z's sign.
The steady early value is Y=m J_* with m=e/d1>0.

For small t, (6) defines the whole Y array backwards. Its derivatives in
sup norm are bounded independently of N, by geometric series with ratio
rho1 in(rho,1). The same holds through second derivatives; all coefficients
are finite, and the arbitrary ten remainders occur only multiplied by alpha.

On arrays with J-radius C1 Nt and theta-radius C2 t about the reference,
iterate

    J_j(new)=J_*+t sum_(k<j)gcore_k,
    theta_j(new)=delta theta_(j+1)-delta t fcore_j (j<N-1),
    theta_(N-1)(new)=theta_*.

Choose C1,C2 from the uniform gcore,fcore bounds. The map preserves this box
and its sup-norm derivative is at most max(C Nt,delta+C t)<1 for N large.
Banach gives a unique actual finite orbit in a fixed surrounding neighborhood.
It satisfies, together with first derivatives in (J_*,theta_*,Lambda,h),

    |J_j-J_*|<=C jt,       |theta_j-theta_j^0|<=C t.  (9)

The backwards tail does not invalidate the scaled entrance. To verify this
without assuming rho<delta, choose eta with max(delta,rho1)<eta<1.
Convolution of the reference theta and backwards rho1 sequences yields

    |Y_j-m J_*|<=C[eta^(N-1-j)+(j+1)t],             (10)

and the same estimate for first derivatives after subtracting the derivative
of mJ_*. One may enlarge eta to absorb polynomial factors from parameter
derivatives. At theta=t=0,Y=Ynext=mJ_* direct substitution gives

    fcore=-h Lambda Gamma21 mJ_*/c.

Multiply the resulting estimate for fcore_j by delta^(j+1) and sum. Since
sum delta^(j+1)=a0+o(1), and
sum delta^(j+1) eta^(N-2-j)=O(eta^N), one obtains in C1

    sum_(j=0)^(N-2)delta^(j+1)fcore_j
         --> -a0 h Lambda Gamma21 mJ_*/c.           (11)

All errors tend to0 uniformly in h. On compact sets of fixed coefficients,
choose common delta_max,rho1_max<eta<1; coefficient derivatives add only
polynomial factors in N, which eta^N absorbs after one enlargement. This
also proves the claimed compact uniformity.

## 4. Entrance, explicit outer return, and nonsingular selection

Impose Q2(first)=0. In theta coordinates this is exactly

    theta_0/t=(1-h)Lambda Y_0
        /[c+t Lambda((a0+1)(1-h)+h(Z2(123)-c))Y_0].

By backwards summation in (5), theta_0/t=theta_*−sum delta^(j+1)fcore_j.
The resulting exact entrance equation has C1 limit

    theta_*-Lambda (mJ_*/c)[1-h-a0 Gamma21 h]=0.      (12)

Condition (3) makes its Lambda coefficient positive uniformly on[0,hmax].

Let the last successor be E=(E0,-x,E2,0), where x=-F1(last),E2=F2(last),
and propagate row0 backwards through the actual roots. Its entrance C0
has limiting relation

    D=1-(a0+1)theta_*,
    C0=k(1-D)+D E0,
    C1=-J_*, C2=0,C3=0,
    x=[J_*-g(a0+1)theta_*]/D,
    E2=(c+h0)theta_*/D.                              (13)

This is uniform C1: the pure3 survival telescopes to
D/[1-a0 t theta_*], and all nonsolo3 row0 terms are O(alpha). Equation(9)
and its derivatives control their total errors by O(N^2 t), which tends0.
No sign on any of the four row0 core collision remainders is needed.

For the exact finite entrance define

    b_N=C0/(C0+beta0),
    B1=b_N Gamma12+(1-b_N)C1,
    B3=b_N e+(1-b_N)C3,
    a_N=B3/(B3+d),
    A1=a_N Gamma10+(1-a_N)B1,
    A2=a_N f.

The exact two outer return equations are

    A1(k-E0)=g E0-k x,
    A2(k-E0)=k E2+h0 E0.                            (14)

At the limit, multiplying by D eliminates theta and gives

    A1(k-C0)=g C0-k J_*,
    A2(k-C0)=h0 C0.                                 (15)

The second equation selects exactly C0=C in Section1: dividing by C0>0,
its numerator is
 f e k-h0 d beta0-[f e+h0(e+d)]C0.
Its derivative at the root is nonzero. The first equation is linear in J_*
with positive coefficient k-L0(k-C), and selects exactly J. Thus the
Jacobian in (J_*,C0) is triangular and invertible. The change between C0
and E0 has positive derivative D. Together with (12), the full Jacobian
in (J_*,E0,Lambda) is uniformly invertible throughout the compact phase and
h rectangle. Finite-dimensional implicit selection gives unique C1 branches
for all sufficiently large N, with

    J_N -> J,
    E_N -> [C-k(a0+1)theta]/[1-(a0+1)theta],
    Lambda_N -> theta/[(mJ/c)(1-h-a0 Gamma21 h)].     (16)

In particular Lambda_N is positive and strictly increasing in theta.
Each physical branch supplies the raw K=1/(t h Lambda_N) and p=-(1-h)/h.

## 5. Legal guards including arbitrary Gamma21 and remainders

The terminal sign and wash margins have limits

    Z_last=[J-B0 theta]/D,
    E2-cx/A=(c/A)[r B0 theta-J]/D.                  (17)

Their simple zeros are theta_plus=J/B0 and theta_minus=delta theta_plus.
They yield exact transverse finite-branch boundaries theta_N^+,theta_N^-;
between them both expressions are nonnegative. Nonterminal Y,Z stay positive
by (8),(9). Final Y has precisely final Z's sign by (6) with R=0.

All physical w are nonnegative, even when Gamma21 is positive. Here is the
exact inequality replacing a small-neighborhood sign argument. At any core
root write y=alpha Y,q=-p>=q0,s=Z2(123),z=Z2(13),a1=Gamma21,b1=Gamma23=-h0.
Then

    Q2=-q y+[c+y(s-c+q)]w,
    P2=a1 y+[b1+y(z-a1-b1)]w.

For y sufficiently small, the first bracket is positive and the coefficient
of w in P2 is negative. If Q2>=0, the positive coefficient in its exact
formula already gives w>=q y/[c+y(s-c+q)]>=0; nonnegativity of w is not
assumed to prove this implication. Consequently

    P2 <= y [c a1+q b1+y(a1(s-c)+q(z-b1))]
                 /[c+y(s-c+q)].                    (18)

By (3), there is eta0>0 with q-(c/h0)a1>=eta0(1+q) for all q>=q0.
The bracket in (18) is therefore <=-h0 eta0(1+q)+O(y(1+q))<0 for small t.
Thus P2<0 if y>0. At the first root Q2=0 and y>0, so F2>0. The next root
has Q2=previous F2>0 and
wnext=(F2-beta Ynext)/[c-beta Ynext+alpha(s-c)Ynext]>0.
This inducts through the core. If a terminal y vanishes, w>0 still gives
P2=b1 w<0. If p=0 the first w=0, and player3 is quiet but indifferent by
its exact row3 interface. All upper hazard bounds follow from small t and
the compact limiting phase interval.

The limiting outer B1 is positive by (1), and B3=be>0. Also
A1=(gC-kJ)/(k-C)>0, A2=af>0. On the phase interval, x>0 and x<g,
E0>kx/g, and E0<k; these follow respectively from A>g, J<g and J<gC/k.
Hence E0>0. Row0 annotations stay positive because their limiting pure3
recursion connects positive E0 and C; arbitrary finite core remainders only
cause vanishing perturbations. At the solo2 root, row3's Quit offer is
v b_N and its annotation is b_N e+(1-b_N)C3; the strict v<e ensures legality
for large N. Row1's offer -K b_N is below positive B1. Every row0 joining
offer is nonpositive by the seven unchanged caps.

## 6. Finite wash and exact gluing of all large K

At state (s0,-v0,z0,0), a solo3 root q has successor

    ((s0-kq)/(1-q),(-v0+gq)/(1-q),(z0+h0q)/(1-q),0).

If 0<v0<g, s0>k v0/g, z0>=c v0/A, choose q=v0/A. The comparisons are
legal, and both s0-kv0/g and z0-cv0/A remain nonnegative after the step.
Writing r0=1-g/A in(0,1), after n regular roots

    S_n=1-x/g+(x/g)r0^n,
    v_n=x r0^n/S_n,
    z_n=[E2+h0(1-S_n)]/S_n.

A final q=v_n/g is legal and sets row1 to zero provided

    r0^n <= [g E2+h0 x]/[(c+h0)x].

The right side is at least (gc/A+h0)/(c+h0)>0 on the whole legal phase
interval. Thus one finite n suffices for the fixed raw coefficients; a common
n works on each compact coefficient set. Total repair survival is1-x/g and
its endpoint is

    V0=(E0-kx/g)/(1-x/g), V1=0,
    V2=(E2+h0x/g)/(1-x/g), V3=0.

The final solo3 aggregate V0/k lies in(0,1), and (14) closes the return.

At theta_N^+, terminal Y=Z=0 and the last core root is pure solo3 with
current coordinates (-A w,cw) for players1,2. Delete it. The shortened core
now has x_old=A w,E2_old=cw, exactly the wash boundary. The affine repair
and return equations are unchanged: total survival is preserved, and each
outer equation is multiplied by1-w. The entrance and raw alpha,beta are
unchanged. Its terminal phase tends to delta theta_plus=theta_minus,
and its new Lambda equals delta times the old Lambda. Local uniqueness of
the finite-orbit and outer branches therefore identifies it with the N-1
lower-boundary branch at the identical K,p.

Since Lambda_N increases strictly with theta, each legal phase interval maps
onto one complete closed K interval. The exact deletion identity joins
successive intervals with no gaps. Their endpoints satisfy

    h K=1/(t_N Lambda_N) -> infinity.

For one sufficiently large N0, the lower endpoint of hK extends continuously
to h=0 on[0,hmax] and has a finite maximum M. Therefore every K>=M/h is
covered. As 1/h=1+|p|, this proves the raw region (4).

## 7. Fixed target and full behavioral consumer

For each fixed game choose one finite core and all annotations once, before
accuracy. Its complete calendar is

    A=(0,A1,A2,0) --solo0--> B=(0,B1,0,B3)
      --solo2--> C --core--> E --solo3 repair--> V --solo3--> A.

All prescribed and Continue identities are exact. Every active owner is
indifferent. During solo0 the observer annotations remain nonnegative:
their numerators are affine between nonnegative endpoint numerators. Split
this aggregate into conditional hazards <=mesh. If J_i=Z_i({0,i}), each
immediate Quit gain is then at most mesh max(0,J_i). No bound on the three
J_i is assumed. The solo2, core and wash comparisons were proved above.
Split the final solo3 aggregate finely enough that its row2 joining offer
c q remains below its positive annotation; other quiet joining offers there
are nonpositive. Every selected period is finite.

Before absorption there is one surviving public history, so a unilateral
behavioral replacement is a law on finite stopping dates and Never. Its cap
obeys B_i=max(Q_i,P_i+H_i B_i(next)). Let

    err=mesh max(0,J_1,J_2,J_3), rho0=min(a_N,b_N)>0.

Every deviator faces opponents-only absorption probability at least rho0 per
period: deviator0 faces solo2, every other deviator faces solo0. Unrolling the
cap recursion bounds the largest adjusted cap D by
D<=max(err,(1-rho0)D), hence D<=err. Exact prescribed identities and proper
period survival make prescribed terminal payoffs equal the reference target
A, independent of mesh. Thus all complete behavioral gains are <=err.

For period length L and maximum absolute original reward R, opponents-only
expected absorption time is at most L/rho0+1. Every unilateral replacement
therefore has terminal versus T-horizon payoff discrepancy at most
2R(L/rho0+2)/T. Proper opponents add exactly kappa_i to every terminal native
payoff, prescribed or deviating. Choose mesh for accuracy, then a horizon
threshold. The one target is kappa+A, fixed before mesh. This proves UE.

## 8. Exact tests and scope

For the reference singleton matrix

    Gamma=[0,3,-1,3; 2,0,1,-3; 2,-2,0,-1; -1,-2,1,0],

one gets C=5/4,J=3/4,a=5/14,b=5/9,B1=2/9. Thus the theorem permits ALL
A>3,c>0,u>=0,v<1, all ten remaining core collision entries arbitrary finite,
and all p<=0 with sufficiently large K/(1+|p|). These are unbounded raw
coefficient freedoms; the threshold may depend on those finite coefficients.

Changing only Gamma21 to1/2 keeps the same C,J and all outer guards.
Its determinant is10 and inverse column0 is(1,6,13,5)/20>0. With c=3,h0=1,
choose any q0>3/2. The theorem covers all p<=-q0, K>=M(1+|p|), crossing the
Gamma21<0 entrance restriction.

The raw singleton chamber is not exhaustive. For example

    Gamma=[0,1,-5,5; 4,0,-5,-2; 5,-2,0,-4; -2,4,3,0]

has determinant382 and strict positive inverse columns, but the only
geometric labeling compatible with the eight sign conditions has
C=1/2,J=19/14 and gC/k=5/6, violating (1); its B1=-2/7 is negative.
A different outer return is needed there. No claim of arbitrary Fin4 closure
or of an unrestricted counterexample is made.

The named semantic source interfaces are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
This proof supplies the complete behavioral consumer. No new Lean
compilation or formal verification is asserted.

## 9. A complete separating ray

The following native table, with kappa_i=1 for every i, lies in the new
class for all sufficiently large K. Here p=0 and u=10. The backward ratio is
rho=10/(10+2)=5/6, larger than delta=3/4; the new rho<1 tail argument is
needed. This is not a claim obtained by taking a small coefficient
neighborhood. Both the arbitrary remainder freedoms and the explicit raw
singleton chamber are additional scope of the producer.

| D | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
|0|0|2|2|-1|
|1|3|0|-2|-2|
|2|-1|1|0|1|
|3|3|-3|-1|0|
|01|0|-1|-10|-12|
|02|0|5|-10|7|
|12|-12|-K|0|-6|
|03|-3|3|-5|1|
|13|2|-100|-1|10|
|23|-6|9|3|-100|
|012|-13|6|-9|11|
|013|-7|8|10|-10|
|023|-7|-8|-3|15/2|
|123|-8|11|2|1|
|0123|-5|-9|8|21/2|

For EVERY K>=100 this table has no stationary equilibrium and no root with
a sure quitter that is Nash against any actual continuation cap. A finite
exact certificate follows. Since the theorem supplies UE above its finite
threshold, these are exclusions of methods, not counterexamples to Fin4.

For product hazards q, define

    H_i=product_(j!=i)(1-q_j),
    P_i=sum_(nonempty S subset opponents) weight_q(S) Z_i(S),
    Q_i=sum_(S subset opponents) weight_q(S) Z_i(S union{i}),
    F_i=(1-H_i)Q_i-P_i,
    L_i=min({-1} union {Z_i(S): nonempty S excludes i}),
    G_i=Q_i-P_i-H_i L_i.

Here weight_q(S)=product_(j in S)q_j product_(j outside S,i)(1-q_j).
For the table, L=(-12,-8,-10,-12), independent of K. Every nonzero stationary
equilibrium requires F_i<=0 at q_i=0, F_i=0 at0<q_i<1 and F_i>=0 at q_i=1.
These signs compare Quit now with Never. AllNever is excluded by original
own-singleton payoff1. For any root with a sure quitter, an actual native
continuation cap is at least L_i by the pure-Never response. Replacing that
cap by L_i only improves the sole sure owner's Quit comparison; all other
players then have H_i=0. Multiple sure owners give H_i=0 for every i. Thus
all such Nash roots satisfy the corresponding signs for G.

Only row1 depends on K, and exactly

    F1(K)=F1(100)-(K-100)(1-H1)(1-q0)q2(1-q3),
    G1(K)=G1(100)-(K-100)(1-q0)q2(1-q3).

Enumerate patterns in{0,1,*}^4, where * is strictly mixed: 80 nonzero patterns
for F, 65 containing a sure owner for G. If q2=0,q0=1 or q3=1, keep the
baseline signs unchanged. Otherwise retain rows0,2,3 and relax row1: require
its baseline polynomial>=0 if mixed or sure, and omit it if quiet. These
conditions are necessary for every K>=100.

One direct F exclusion is valid when q0=0, player2 is mixed, and q1 or q3
is positive:

    Q2=q3(3-q1)>=0, P2=-2q1-q3+2q1q3<0, hence F2>0.

A pattern with one mixed coordinate j and no sure owner is excluded by a
retained outsider with Gamma_ij<0 and Z_i({i,j})>=0. Such an outsider exists
for each j: respectively i=3, i=2, i=0, i=2 for j=0,1,2,3. At j=2 the
omitted row1 condition is not used.

For at least two mixed coordinates S put A=Gamma_SS,V=A^(-1). Every such
principal matrix is invertible. Add each V combination of the mixed baseline
polynomials. It is an equality unless mixed row1 was relaxed; in that event
its sign is >=0,<=0 or=0 according to the coefficient of row1 being positive,
negative or zero.

For patterns with no sure owner, the mixed baseline vector is -Aq+R(q),
where R has only degree>=2 terms. If row1 was not relaxed then q=VR. If it
was relaxed, the direct q0=0 exclusions above leave only principal inverses
with nonnegative column1; therefore VF>=0 and q<=VR. In either case define

    c_i=sum of absolute coefficients in R_i,
    D=max_i sum_j |V_ij|c_j.

Then ||q||_infinity<=D||q||_infinity^2. Thus no nonzero solution lies in
[0,2^-E]^S when 2^-E<1/D. The exact values for the remaining patterns are

| S | D | E |
|---|---:|---:|
|01|1/2|1|
|02|5|3|
|03|1|1|
|13|100/3|6|
|012|2053/5|9|
|013|1609|11|
|023|3869/5|10|
|0123|157832/25|13|

The patterns12,23,123 were directly excluded. These origin bounds use the
baseline table only and are uniform in K.

Substitute each pattern's fixed coordinates into its retained polynomials
and the V combinations. Each coordinate degree is at most2. For
sum_m a_m x^m in d mixed variables, its tensor degree2 Bernstein coefficient
at k in{0,1,2}^d is

    b_k=sum_(m<=k) a_m product_i[binom(k_i,m_i)/binom(2,m_i)].

Clear a common positive denominator in each pattern. Reject a box if an
equality has all coefficients strictly positive or all strictly negative,
or an inequality has all coefficients of its forbidden strict sign. Ignore
omitted conditions. Also reject a box wholly in the proved origin cube.
Otherwise bisect the coordinate subdivided least often, breaking ties by
player index. For each degree2 triple (a,b,c), positively scaled children are

    left=(4a,2(a+b),a+2b+c),
    right=(a+2b+c,2(b+c),4c).

Process left before right. Direct and zero-dimensional exclusions count as
one node each. These prescribed rational calculations terminate with
864 nodes for the80 stationary patterns and371 nodes for the65 sure-root
patterns; no box remains unresolved. All input data and exact rules have
been given, so no external computed payload is a premise.

The other named raw selectors fail on the same full ray. Its singleton
matrix has determinant25 and inverse column0=(8,3,14,10)/25>0. The positive
graph is strongly connected and the participant vector on123 is(11,2,1)>0.
Thus every admissible marked set for ordered nonpositive anchors must be all
players, and its first block meeting123 has positive participant sum. The
same vector defeats every upper-average weight on the core. The trap charge
Z3(123)-Z3(12)=7>0 fails the mixed-trap sign. The only inverse-positive
principal triple is023, with outside inverse row(-3,6,2)/5, so complete
passive-child selection fails.

The unique mutually negative singleton pair is13. Its only attached-pair
labeling is(3,1,0,2), which requires a nonnegative participant premium where
Z1(13)=-100; the alternative allowing both premiums arbitrary instead requires
Gamma21=-2 to be nonnegative. All three invariant-cone pair partitions fail
a necessary positive difference:01|23 gives-3 at player0,02|13 gives-12 at
player2,03|12 gives-6 at player0. The inverse column2 is(9,-6,-3,5)/25, so
no relabeling or column sign choice makes every signed inverse column
positive. The unique mutually positive pair01 meets the unique mutually
negative pair13, whereas the signed four-cycle templates require disjoint
pairs. Every triple contains a core pair with a negative participant reward.
All these failures are unchanged when Z3(13) rises from0 to10.

A player relabeling or positive row scaling cannot identify this ray with
fixed core coefficients: the singleton matrix's unique row with two equal
positive entries fixes player0, its sign fixes player2, and the remaining
sign pattern fixes players1,3. Its nonzero entries then force all row scales
to1, so the changed collision reward10 cannot disappear.

## 10. Strategic production and formalization target

All strategic objects used by the theorem are produced: equations(1) give
the limiting return, the finite-array contraction gives actual core roots,
the nonsingular three-equation selection chooses their entrance and exit,
exact endpoint deletion covers every sufficiently large raw K, and the finite
wash and split singleton blocks produce complete periodic profiles. No
continuation, cap, return orbit or response optimizer is assumed. Section7
fixes the target before mesh and treats all behavioral replacements.

The main new proof obligations for formalization are the backward-map
convolution when rho may exceed delta, the exact inequality(18) with arbitrary
finite remainders, the explicit singleton outer root, and the complete
finite-orbit/gluing theorem uniform in the compactified negative premium.
Root identities and finite arithmetic tests can be checked separately before
the full behavioral consumer. The exact Bernstein certificate is needed only
for the coverage comparison, not for equilibrium production. The result
settles a larger explicit raw-table class; neither global-minimum branch
for arbitrary Fin4 is eliminated.
