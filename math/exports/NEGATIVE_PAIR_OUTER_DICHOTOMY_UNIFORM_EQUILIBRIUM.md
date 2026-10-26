# Uniform equilibrium from two exhaustive negative-pair returns

This theorem closes one explicit singleton-geometry branch through two
complementary outer returns and their exact boundary switch. The core
estimates are proved in Section5. It is ordinary mathematics, not checked
in Lean. Arbitrary Fin4 remains open.

## 1. Raw class and the exhaustive statement

Use native own-zero rewards Z_i(D)=r_i(D)-r_i({i}) on nonempty coalitions;
live and literal Never remain zero. Players are0,1,2,3 and Gamma_ij=Z_i({j}).
Write the singleton matrix as

    Gamma=[ 0    kappa  -beta   k
           -n      0    ell   -g
            f      s      0   -h
           -d    -d1      e    0 ],                  (1)

where beta,kappa,k,n,ell,g,f,h,d,d1,e are strictly positive, while s is any
finite real. Assume

    Delta=e f k-beta d h>0,
    det Gamma>0,
    Gamma^(-1)e_0>0 entrywise.                      (2)

These are explicit raw matrix tests. Delta is the determinant of child023;
that child has positive inverse. Conditions(1)--(2) are not asserted for every
remaining Fin4 singleton matrix.

Fix

    A=-Z1(13)>g, c=Z2(23)>0,
    u=Z3(13)>=0, v=Z3(23)<e.                       (3)

Every other core collision entry on12,13,23,123 is arbitrary finite except
Z1(12)=-K,Z2(12)=p, which vary. Thus ten core remainders are completely free.
All seven row0 rewards on nonsingleton coalitions containing0 are <=0; the
other21 joining coordinates and all four original own-singleton levels are
arbitrary. Choose q0>=0 with

    q0>(c/h)s.                                      (4)

**Theorem.** There is finite M such that every p<=-q0,K>=M(1+|p|) has a
uniform-equilibrium payoff against all unilateral behavioral replacements.
M depends on the fixed data in(1)--(4) and the ten core remainders, but not
on the21 free joining coordinates or original own levels. It is uniform on
compact sets of the fixed raw data satisfying(1)--(4).

In particular this covers EVERY sign of the outside inverse weight

    W2=d(k ell-beta g)-e k n,                        (5)

including W2=0. The outer architecture is produced by an exhaustive
three-case choice: W2>0 uses a solo3 return, W2<0 a solo1 return, and W2=0
uses an exact switch between their finite versions. No successful return
profile is assumed.

## 2. Exact singleton algebra and the old positive-weight case

Put X=k ell-beta g. The outside row of the inverse-positive child023 has,
before division by Delta, entries

    W0=d h ell-e f g-e h n,
    W2=d X-e k n,
    W3=f X-beta h n.                                (6)

The strict inverse-column hypothesis gives the following positive cofactors:

    a00=d1 h ell-e g s>0,
    a10=-d h ell+e f g+e h n=-W0>0,
    a20=-d g s+d1 f g+d1 h n>0,
    a30=-d ell s+d1 f ell+e n s>0.                 (7)

Also

    det Gamma=kappa a10-beta a20+k a30.             (8)

For W2>0 define

    D0=d h+e f+e h,
    C=Delta/D0, J=-W0/D0.                          (9)

Then 0<C<k, J>0. The outer values computed from a solo0,solo2 return are

    A1=W2/(beta d+d k+e k),
    B1=W3/(beta f+beta h+f k).                      (10)

Since W2>0 gives X>e k n/d, and Delta>0,

    W3>n(e f k/d-beta h)=n Delta/d>0.

Thus A1,B1>0 and C>kJ/g. The exact limiting return is

    core -> solo3 wash -> V=(V0,0,V2,0)
         -> solo3 until coordinate0 is zero
         -> solo0 until coordinate2 is zero
         -> one solo2 root -> core,

with

    V0=(gC-kJ)/(g-J), V2=hJ/(g-J).                 (11)

Here C>kJ/g and C<k imply 0<J<g,0<V0<k. Every aggregate hazard lies in(0,1).
The row0 and all quiet coordinates along the diffuse blocks are nonnegative.
The final solo2 root has b=C/(C+beta); its current B1 is positive. The limiting return equations are nonsingular: in the usual backwards
solo2/solo0 variables, the row2 equation divided by C has a linear numerator
Delta-D0 C; after solving C, the row1 equation is linear in J with positive
coefficient k-(1-a0)(1-b)(k-C). All denominators are positive. These strict
statements persist under the finite-core perturbations in Section5.

For W2=0, formulas(9)--(11) instead give V0=A1=0, J=gC/k, B1>0. The solo3
aggregate has zero length; all remaining comparisons are still legal, with
strict margins away from that one aggregate.

## 3. The complementary negative-weight case has a unique legal return

Assume W2<0. The new outer calendar is

    core -> solo3 wash -> V=(V0,0,V2,0)
         -> solo1 until coordinate0 is zero
         -> solo0 until coordinate2 is zero
         -> one solo2 root -> core.                 (12)

Let z=J/C and define affine functions

    U(z)=(g-kz)/kappa,
    T(z)=h z-s U(z),
    L(z)=ell-beta z,
    M(z)=d1 f U(z)+d T(z),
    W(z)=f(z+U(z))+T(z),
    N(z)=e f g-beta M(z).

The return reduces to the single quadratic equation

    F(z)=n e T(z)-L(z)M(z)=0,                      (13)

followed by

    C=N(z)/[M(z)+e W(z)], J=z C.                   (14)

This is an actual raw-data producer: the following argument proves one unique
root in the legal interval and proves C>0, rather than assuming a root.

Consider the interval I defined by

    z>0, U(z)>0, T(z)>0, L(z)>0.                   (15)

If s<=0 its lower endpoint is0; if s>0 it is
zlo=s g/(kappa h+s k). Its upper endpoint is min(g/k,ell/beta).
The interval is nonempty. Only the s>0 case needs proof. The inequality
zlo<ell/beta is equivalent to

    A03=h kappa ell+s X>0.                          (16)

If X>=0 this is immediate. If X<0 and A03<=0, then
kappa<=-sX/(h ell). Since a10>0, equation(8) bounds det Gamma above by
its value at that endpoint, which by direct substitution is

    a00 W3/(h ell)<0,

because W3=fX-beta h n<0. This contradicts(2).

On I,

    F/T=n e-L(d+d1 f U/T).

Since

    (U/T)'=-h g/[kappa T^2]<0,

both positive factors in L(d+d1 f U/T) strictly decrease. Thus F/T is
strictly increasing. At the lower endpoint it is negative: when T tends0
it tends minus infinity; when s<0 and z tends0, its numerator is

    F(0)=-(g/kappa)a30<0.                           (17)

At the upper endpoint it is positive. If L tends0, its limit is n e>0.
If U tends0, its limit is

    n e-d(ell-beta g/k)=-W2/k>0.

The intermediate value theorem therefore produces exactly one z_* in I;
F'(z_*)>0. This remains a uniformly transverse root on compact fixed-data
sets inside W2<0.

It remains to prove N(z_*)>0, which is essential for positive C. First

    N(g/k)=g Delta/k>0.

If N has nonpositive slope, it is already positive for every z<g/k. Suppose
its slope is positive and N(z_*)<=0. Its unique zero zN then satisfies
z_*<=zN<g/k. Direct substitution gives

    F(zN)=e f g det Gamma/[beta D1],
    D1=d h kappa+d k s-d1 f k.                      (18)

The slope of N is -beta D1/kappa, so D1<0 and F(zN)<0. But T(zN)>0. If
L(zN)<=0, equation(13) gives F(zN)>0 directly. If L(zN)>0, zN is in I and
the strict increase of F/T gives F(zN)>=0. Both alternatives contradict(18).
Thus C>0 in(14).

The resulting hazards and intermediate values are explicit. Put

    a1= C U/[g-zC],
    A2=C T/[g-C(z+U)],
    A3=d1 C U/[g-C(z+U)],
    a0=A2/f,
    B1=n C T/[f g-C W],
    B3=C M/[f g-C W],
    b=C/(C+beta).

The second return equation is exactly

    f g-C W=M(C+beta)/e>0.                          (19)

Therefore g-zC>0, 0<a1,a0<1, and J=zC<g. All V0,V2,A2,A3,B1,B3 are
positive. Equation(13) gives B1=b ell-(1-b)J; (14) gives B3=b e.
Also z<g/k gives C>kJ/g, so the wash is legal. The solo1 and solo0 blocks
have nonnegative observer annotations throughout, since their affine
numerators have nonnegative endpoints. The only zero observers at their
starts move into the positive orthant: Gamma31=-d1<0 during solo1 and
Gamma10=-n<0 during solo0. The final solo2 comparisons use -K and v<e.

The limiting two-equation Jacobian is nonsingular. In variables(C,z), use
(13) and C(M+eW)-N=0: their triangular determinant is
F'(z_*)[M+eW]>0. Thus this return is stable under the actual finite core,
not merely an algebraic limiting picture.

The actual finite return equations, used for both branches, are explicit.
Given exact core entrance(C0,C1,0,C3) and exact wash endpoint(V0,0,V2,0),
the old branch takes q3=V0/k and sets

    A1=gq3/(1-q3), A2=(V2+hq3)/(1-q3), A3=0.

The new branch takes q1=V0/kappa and sets

    A1=0, A2=(V2-sq1)/(1-q1), A3=d1q1/(1-q1).

In either branch put a0=A2/f, b=C0/(C0+beta),

    B1=(A1+n a0)/(1-a0), B3=(A3+d a0)/(1-a0),
    H1=B1-[b ell+(1-b)C1],
    H3=B3-[b e+(1-b)C3].

The finite return is precisely H1=H3=0. These rational equations converge
in C1 to the limiting systems just proved nonsingular.

## 4. The exact boundary switch covers W2=0

At a W2=0 table one has X>0 and

    Gamma10=-n0, n0=dX/(e k)>0.

For the argument vary the single raw coefficient tau=Gamma10 in a small
interval about tau0=-dX/(e k). This is only an auxiliary parameter used to
prove existence for the ORIGINAL fixed value tau0. It is not a payoff
normalization or a replacement of the game.

Both limiting return systems extend analytically across tau0 if their
extra solo3 or solo1 aggregate is allowed formally to be negative. The old
branch remains nonsingular by(9)--(10). The new branch remains nonsingular:
at tau0 its root is z=g/k, U=0, while T,L,N,M+eW are strictly positive,
and F'(z)>0 still holds. Every guard except the sign of the extra aggregate
is strict at the common limiting point.

The old branch's V0 has positive derivative in tau at tau0. Indeed C is
constant, J_tau=-e h/D0 and

    (V0)_tau= k e h/[D0(g-J)]>0.                    (20)

For the new branch, n=-tau and F_tau=-eT, so

    z_tau=eT/F'>0,
    (V0)_tau=-k C z_tau/[g-zC]<0                    (21)

at U=0. The uniform finite-core implicit-function theorem preserves these
opposite derivative signs for every sufficiently large N and the whole
compact phase/h rectangle.

For each N,phase,h the old branch therefore has one nearby zero of V0,
say tau_N. At this exact zero the extra solo3 block is absent. The same
finite core and outer roots solve the new equations with its solo1 block
absent, because the two calendars then coincide exactly. Local uniqueness
of the new finite branch identifies the same zero tau_N there. Consequently

    tau>=tau_N: use the old branch, whose V0>=0;
    tau<=tau_N: use the new branch, whose V0>=0.      (22)

At equality they give the identical full calendar. All other guards retain
uniform strict margins. This proves existence at tau=tau0 and uniformly on
an entire neighborhood of the W2=0 hypersurface.

The selected finite branch is continuous, though no differentiability across
the switch is claimed. Its compactification parameter Lambda is strictly
increasing in terminal phase on each constituent branch, with one common
positive lower derivative bound. The pieces agree whenever the selection
changes. Thus the selected Lambda is strictly increasing globally: between
two points assigned different branches, insert any switch point and use the
two separate strict inequalities. The same argument gives the needed
monotonic signs for the terminal Z and wash margins. Hence there is one
complete legal closed phase interval, and its K image is a complete interval.

Deleting a terminal pure3 core root leaves V, the entrance C and every outer
block unchanged. Therefore deletion preserves whichever branch is selected,
including the identical boundary calendar. The exact gluing of consecutive
core lengths survives this switch. Compactness now yields one large-K
threshold on compact sets even when they cross W2=0.

## 5. The common finite-core producer

Here are the analytic data and estimates needed to turn the preceding
returns into actual profiles. Set a=c/h, delta=c/(c+h), B=A+a g,
t=delta^(N-1), eta=1/(1-p) in(0,1/(1+q0)],
alpha=t eta Lambda=1/K and betaP=-t(1-eta)Lambda=alpha p.
A core root has hazards(0,alpha Y,alpha Z,w). Set

    theta=w/(1+a w),
    Jcore=[(1-w)Z+B w]/(1+a w).

At t=0 its first two active interfaces preserve Jcore and multiply theta
by1/delta. Their exact analytic forms follow from

    Q1=-Z(1-w)-A w+alpha(A+Z1(123))Zw,
    Q2=betaP Y(1-w)+c w+alpha(Z2(123)-c)Yw,
    P1=alpha ell Z(1-w)-g w(1-alpha Z)+alpha Z1(23)Zw,
    P2=alpha s Y(1-w)-h w(1-alpha Y)+alpha Z2(13)Yw,
    F1=(Q1-P1)/[(1-alpha Z)(1-w)],
    F2=(Q2-P2)/[(1-alpha Y)(1-w)].

Given Ynext, solve

    wnext=(F2-betaP Ynext)
           /[c-betaP Ynext+alpha(Z2(123)-c)Ynext],
    Znext=(-F1-A wnext)/[1-wnext-alpha(A+Z1(123))wnext].

Converting back gives exact equations

    theta_next=theta/delta+t fcore,
    Jcore_next=Jcore+t gcore,                        (23)

where fcore,gcore are analytic divided differences with removable t=0
singularities and bounded derivatives on the fixed compact neighborhoods.

For row3 let z3=Z3(12),w3=Z3(123),
D3=(w3-u-v)-(z3+d1-e), and
R=uYnext+vZnext+alpha(w3-u-v)Ynext Znext. Its exact backwards equation is

    Y=[R(1-alpha Z)-(v-e)Z]
        /[(u+d1)+alpha D3 Z+alpha R(1-alpha Z)].     (24)

At the last root use R=0, ensuring row3 successor0. Its limiting next-Y
ratio is rho=u/(u+d1)<1, with no rho<delta restriction. For reference arrays

    J_j=J_*, theta_j=delta^(N-1-j)theta_*,
    Z_j=[J_*-B theta_j]/[1-(a+1)theta_j],

the Z sequence is decreasing and positive except its permitted terminal
zero. The backwards recurrence

    (u+d1)Y_j=uYnext+vZnext+(e-v)Z_j

is positive: for v>=0 all coefficients are nonnegative; for v<0 its last
two terms are eZ_j+(-v)(Z_j-Znext). Nonterminal Y,Z have uniform positive
margins; terminal Y has exactly terminal Z's sign.

Compute Y backwards, then iterate on the remaining arrays

    J_j(new)=J_*+t sum_(k<j)gcore_k,
    theta_j(new)=delta theta_(j+1)-delta t fcore_j,
    theta_last(new)=theta_*.

On an O(Nt) by O(t) box about the reference arrays the map preserves the box
and has sup-norm derivative <=max(CNt,delta+Ct)<1. It produces a unique
finite orbit with first-derivative bounds

    |J_j-J_*|<=Cjt, |theta_j-theta_j^0|<=Ct.

Choose rho1 with rho<rho1<1 and zeta>max(delta,rho1),zeta<1. Backwards
geometric convolution gives

    |Y_j-(e/d1)J_*|<=C[zeta^(N-1-j)+(j+1)t],

with the same derivative control. Therefore the weighted entrance sum in
(23) converges in C1 to

    sum delta^(j+1) fcore_j
      -> -(c/h) eta Lambda s(e/d1)J_*/c.

Coefficient derivatives add only polynomial factors in N, absorbed by a
slightly larger zeta<1; the estimates are uniform on compact raw-data sets.

Impose Q2(first)=0. Its exact divided equation is

    theta_*-sum delta^(j+1)fcore_j
     -(1-eta)Lambda Y_0
       /[c+t Lambda((a+1)(1-eta)+eta(Z2(123)-c))Y_0]=0.

Its limiting equation is

    theta_*-Lambda [(e/d1)J_*/c]
                    [1-eta-(c/h)s eta]=0.           (25)

The bracket is uniformly positive by(4). Thus one ordinary scalar implicit
selection produces Lambda, with positive phase derivative. Given any desired
entrance row0 value C, choose its final successor E0 by its exact affine
backwards identity; the survival coefficient stays bounded positively.
The resulting finite-core data converge uniformly in C1 to

    D=1-(a+1)theta_*,
    E0=[C-k(a+1)theta_*]/D,
    C1=-J_*, C2=C3=0,
    x=-F1(last)=[J_*-g(a+1)theta_*]/D,
    E2=F2(last)=(c+h)theta_*/D.                      (26)

The limiting row0 survival D follows by telescoping the reference solo3
survivals; all finite core collision remainders contribute O(alpha), and
aggregate derivative errors O(poly(N)t) tend0. Equations(25)--(26), combined
with either nonsingular outer return, produce the exact finite core and
outer profile by the finite-dimensional implicit-function theorem.

The limiting legal terminal phase interval is

    delta J/B <=theta_*<=J/B.

Its margins are

    Z_last=(J-Btheta_*)/D,
    E2-cx/A=(c/A)[(B/delta)theta_*-J]/D.

Both boundary zeros are transverse and persist. Physical w positivity uses
an exact inequality, not a nonuniform small lower bound. For y=alpha Y,
q=-p>=q0,s2=Z2(123),z2=Z2(13),

    Q2=-q y+[c+y(s2-c+q)]w,
    P2=s y+[-h+y(z2-s+h)]w.

If Q2>=0, its positive w coefficient forces
w>=q y/[c+y(s2-c+q)]>=0; the negative slope in P2 then gives

    P2<=y[cs-qh+y(s(s2-c)+q(z2+h))]/[c+y(s2-c+q)]<0

for y>0 and small t, uniformly in q>=q0, by(4). First Q2=0 yields F2>0,
then the next exact interface yields wnext>0, inductively. All hazards are
<1; nonterminal Y,Z stay positive; permitted zero terminal hazards remain
indifferent. Row0 annotations are positive throughout the core even when
its eventual wash endpoint has V0=0.

The finite solo3 wash starts at(E0,-x,E2,0). Choose repeated hazards vcur/A
while its negative row1 coordinate is -vcur. The inequalities
E0>=kx/g and E2>=cx/A are preserved. If r=1-g/A, after n steps

    S_n=1-x/g+(x/g)r^n,
    v_n=xr^n/S_n, z_n=[E2+h(1-S_n)]/S_n.

Choose n with r^n<=(gc/A+h)/(c+h), then final hazard v_n/g is legal and
ends at

    V0=(E0-kx/g)/(1-x/g), V2=(E2+hx/g)/(1-x/g),
    V1=V3=0.                                      (27)

At the limit these equal(11). The strictness needed away from V0 is uniform;
V0=0 is allowed exactly and produces no negative row0 annotation.

At the upper terminal phase Y=Z=0, the final root is solo3 with current
row1,row2=(-Aw,cw). Delete it. The shortened core exit is exactly at the wash
boundary x_old=Aw,E2_old=cw. The complete wash endpoint V is identical,
and all outer equations and the original raw alpha,betaP are preserved.
Local uniqueness identifies this with the N-1 lower phase branch.
Consequently all consecutive K intervals join exactly. Their endpoints
satisfy eta K=1/(t Lambda)->infinity. A fixed starting length's lower
endpoint has a finite maximum on the compact eta interval, including eta=0.
This proves all K>=M/eta=M(1+|p|), with the hybrid argument in Section4
supplying the same conclusion on W2=0.

## 6. Full behavioral and fixed-target consumer

For the chosen fixed raw game choose one finite core, exact outer blocks and
all annotations before accuracy. Split each diffuse solo0 block into small
conditional hazards. Its observer annotations are nonnegative in both
calendars; arbitrary joining rewards therefore cause at most mesh times
their positive parts as immediate Quit surplus. In the new calendar split
solo1 similarly; its only potentially positive joining surplus at a zero
annotation is bounded by mesh*u. Its row2 joining reward p is nonpositive
and row0 joining reward is nonpositive. The old solo3 aggregate is split
finely enough that row2's offer c q stays below its positive annotation.
The core, wash and final solo2 comparisons are exact. In the latter B1>0
and B3-bv has positive limiting margin b(e-v).

Every prescribed and Continue payoff identity is exact. Before absorption,
a unilateral strategy is a law on finite stopping dates and Never. Its full
cap recursion is B_i=max(Q_i,P_i+H_i B_i(next)). There is one fixed positive
opponents-only absorption chance per period: deviator0 faces the solo2 root,
and every other deviator faces the solo0 aggregate. Unrolling the recursion
therefore bounds the largest excess cap by the largest immediate mesh error;
errors enter a maximum, not a sum. Prescribed terminal payoffs equal the
fixed annotations because period survival decays geometrically.

For period length L and opponents survival gap rho>0, expected absorption
time under every unilateral replacement is <=L/rho+1. If R bounds absolute
original rewards, the terminal versus T-horizon discrepancy is at most
2R(L/rho+2)/T. Proper opponents add exactly the original own-singleton levels
to all native terminal payoffs, prescribed or deviating. Choosing the mesh
and then T proves the uniform contract at the single fixed target.

## 7. Exact positive control and remaining branches

For

    Gamma=[ 0,4,-2,3;
           -2,0,4,-5;
            5,1,0,-5;
           -4,-2,5,0 ],

the old return has C=1/2,J=19/14 and B1=-2/7, so is illegal. The new equation
is

    F(z)=(62z^2+21z-85)/2,
    z=(sqrt(21521)-21)/124 in(1,21/20),
    C=2(110-31z)/(65+101z), J=zC.

These rational bounds give every strict new guard. Numerically only for
orientation, C is about.938853,J about.951727; the aggregate solo1,solo0,solo2
hazards are about.113572,.239591,.319462. The exact polynomial and interval,
not these decimals, certify the return. It has determinant382, inverse column0=(15,95,50,34)/382>0, and Delta35>0.

For the same displayed matrix with Gamma10 changed to -8/15, one has
W2=0 exactly, det Gamma=728/3 and inverse-column0 cofactors
(15,175/3,106/3,80/3)>0. The common limiting return is

    C=1/2, J=5/6, V=(0,0,1,0),
    solo0 hazard=1/5, solo2 hazard=1/5,
    B1=2/15, B3=1.

At this boundary the two derivatives(20)--(21) are exactly 9/35 and -9/43.
Thus the switch's transversality is visible in a rational test, not only a
formal sign argument.

The assumption Gamma10<0 is substantive. The matrix

    [0,3,-1,3; 2,0,1/2,-3; 2,-2,0,-1; -1,-2,1,0]

has determinant35/2, strict inverse column0=(2/5,1/5,4/5,2/5), and its only
positive-inverse child is023, with outside inverse row(-7/10,9/10,-1/5).
It is R0 of degree1 and fails the passive-child criterion, but Gamma10>0
prevents the new solo0 block from leaving a zero row1 annotation legally.
The old B1 is negative. For completeness, R0 follows because every column
has a negative entry and every principal matrix of size at least2 is
invertible. At offset -e0 the only strict complementarity root is the full
positive inverse column. The candidate triple roots on012,013,023 are,
respectively,(1,1,-4)/7,(2,-1,4/3),(1,1,2)/5; the first two have a negative
coordinate, and the third has outside slack-7/10. Pairs containing0 force its own coordinate zero. Supports excluding0 with
size at least2 force zero by their invertible active principal matrix and
then fail the pivot inequality; singleton supports fail a negative entry of
their singleton column.
Thus the root-index sum is sign(det Gamma)=+1. The triple determinants are
7,-3,5,7, so the claimed nonsingularity and degree assertions are exact.
Thus the two architectures above do not exhaust all cyclic-child matrices. There are also residual matrices with no positive
inverse child. Neither branch is hidden inside the theorem's hypotheses.

## 8. A full-game separating ray and its exact certificate

The following native table, with original own levels all1, satisfies the new
raw theorem for p=-1, q0=1 and every sufficiently large K. Its singleton
matrix is the negative-W2 matrix in Section7, A=100,c=3,u=10,v=-100. It has
rho=5/6>delta=3/8. All four selected core coefficients and the ten free core remainders meet
the stated hypotheses.

| D | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
|0|0|-2|5|-4|
|1|4|0|1|-2|
|2|-2|4|0|5|
|3|3|-5|-5|0|
|01|0|-1|-10|-12|
|02|0|5|-10|7|
|12|-12|-K|-1|-6|
|03|-3|3|-5|1|
|13|2|-100|-1|10|
|23|-6|9|3|-100|
|012|-13|6|-9|11|
|013|-7|8|10|-10|
|023|-7|-8|-3|15/2|
|123|-8|11|2|1|
|0123|-5|-9|8|21/2|

For EVERY K>=100, this table has no stationary equilibrium and no root with
a sure quitter that is Nash against any actual continuation cap. The following
finite rational certificate proves both uniform exclusions. Its scope is
only those strategy classes; Section1 supplies the actual UE above its finite
threshold, so the table is not a counterexample.

For product hazards q define

    H_i=product_(j!=i)(1-q_j),
    P_i=sum_(nonempty S subset opponents)weight_q(S)Z_i(S),
    Q_i=sum_(S subset opponents)weight_q(S)Z_i(S union{i}),
    F_i=(1-H_i)Q_i-P_i,
    L_i=min({-1} union {Z_i(S):nonempty S excludes i}),
    G_i=Q_i-P_i-H_i L_i.

Here weight_q(S)=product_(j in S)q_j product_(j outside S,i)(1-q_j), and
L=(-12,-8,-10,-12). A nonzero stationary Nash point requires F_i<=0 for
q_i=0,F_i=0 for0<q_i<1,F_i>=0 forq_i=1. These compare Quit now and Never.
AllNever is excluded by original own-singleton reward1. For a sure-quitter
root, every actual native continuation cap is at least L_i by Never.
Replacing that cap by L_i improves the sole sure owner's Quit comparison;
all other players have H_i=0. With multiple sure owners every H_i=0. Thus
such a root requires the corresponding signs for G.

The exact K dependence is

    F1(K)=F1(100)-(K-100)(1-H1)(1-q0)q2(1-q3),
    G1(K)=G1(100)-(K-100)(1-q0)q2(1-q3).

Enumerate patterns in{0,1,*}^4:80 nonzero patterns for F and65 containing
a sure owner for G. If q2=0,q0=1 orq3=1, retain all baseline signs. Otherwise
retain rows0,2,3 and relax row1 to its baseline polynomial>=0 if mixed or
sure; omit row1 if quiet. These are necessary conditions for EVERY K>=100.

A one-mixed-owner pattern with no sure owner is directly excluded by a
retained outsider i with Gamma_ij<0 and Z_i({i,j})>=0. Choose i=3,3,0,2 for
j=0,1,2,3 respectively. No other direct support exclusion is used.

For at least two mixed owners S, put A=Gamma_SS,V=A^(-1). Every such
principal matrix is invertible. Add each V combination of mixed baseline
polynomials. These are equalities unless mixed row1 was relaxed; then each
has sign>=0,<=0 or=0 according to its row1 coefficient being positive,
negative or zero.

An origin bound is needed for patterns with no sure owner. Their baseline
mixed vector has form -Aq+R(q), with R containing only terms of degree>=2.
Define

    c_i=sum of absolute coefficients in R_i,
    D_i=sum_j |V_ij|c_j, Dmax=max_i D_i.

If row1 is not both mixed and relaxed, q=VR and D=Dmax suffices. If it is, write
v=V e_1 and F=lambda e_1 with lambda>=0; thus q=VR-lambda v. Every relevant
v has at least one positive entry. If v>=0, q<=VR again gives D=Dmax.
Otherwise, for each v_k>0,

    lambda v_k=(VR)_k-q_k <=D_k ||q||_infinity^2,

so

    ||q||_infinity <=D ||q||_infinity^2,
    D=Dmax+min_(v_k>0)(D_k/v_k) max_i|v_i|.           (28)

This handles mixed-sign inverse columns without treating them as nonnegative.
Choose E with2^-E<1/D. The exact constants are

| S | D | E |
|---|---:|---:|
|01|1/2|1|
|02|2|2|
|03|1|1|
|12|25|5|
|13|20|5|
|23|20|5|
|012|6455/21|9|
|013|2778/23|7|
|023|20191/70|9|
|123|8476/3|12|
|0123|771268/191|12|

No nonzero solution lies in[0,2^-E]^S. All constants use only the K=100
baseline and remain valid uniformly in K.

Substitute the fixed coordinates of each pattern into its retained baseline
polynomials and V combinations. Each coordinate degree is at most2. The
tensor degree2 Bernstein coefficient of sum_m a_m x^m at k in{0,1,2}^d is

    b_k=sum_(m<=k)a_m product_i[binom(k_i,m_i)/binom(2,m_i)].

Clear a common positive denominator within a pattern. Reject a box if an
equality has all coefficients strictly positive or strictly negative, or an
inequality has all coefficients of the forbidden strict sign. Ignore omitted
conditions. Also reject any box contained in its proved origin cube. Otherwise
bisect the least-subdivided coordinate, breaking ties by player index. For
each degree2 coefficient triple(a,b,c), positively scaled children are

    left=(4a,2(a+b),a+2b+c),
    right=(a+2b+c,2(b+c),4c).

Process left before right; each direct or zero-dimensional exclusion counts
as one node. These exact rules terminate with1002 nodes across all80
stationary patterns and359 nodes across all65 sure-root patterns, with no
box unresolved. The full data and rules are given here; no numerical root
search or saved payload is a premise.

The singleton positive graph is strongly connected, while the participant
vector on123 is(11,2,1)>0. Hence complete ordered nonpositive-anchor selection
fails: its admissible marked set must be all four players, and the first block
meeting123 has a positive participant sum. The same positive vector defeats
every upper-average weight on the core. The upper-face joining charge at12
is Z3(123)-Z3(12)=7>0, failing the mixed-trap sign.

The only inverse-positive child is023. Its outside inverse row is
(-19/7,-22/35,-2/7), so complete passive-child selection fails. The unique
mutually negative pair is13; neither endpoint has two positive outside
singleton entries, excluding every attached-pair labeling, including the
arbitrary-joint-premium alternatives. The invariant-cone pair partitions
01|23,02|13,03|12 fail respectively at participant-premium differences
-4 at player0,-15 at player2,-6 at player0. No choice of proof weights repairs
these necessary signs.

The full inverse matrix is

    (1/382)[15,-95,104,82;
             95,35,22,10;
             50,-62,92,146;
             34,-88,32,84].

Its mixed-sign column1 defeats the all-signed-positive inverse-column
criterion and both signs of the growing recipient1 large-pole criterion.
All other rewards on the ray are bounded. The unique mutually positive pair12
meets the unique mutually negative pair13, excluding signed four-cycle
selectors requiring disjoint pairs. Every triple contains a core pair with
a negative participant reward. These checks use complete finite label choices
for the stated selectors, not one selected unsuccessful witness.

The matrix itself is outside the earlier single-return chamber: its only
compatible labeling has negative A1 and B1 under that return, as shown in
Section7. It cannot be obtained from the reference equal-positive-row matrix
by relabeling and positive row scaling: that matrix has a row with two equal
positive off-diagonal entries, whereas this one has none. The new equilibrium
producer is therefore needed on a previously surviving large-K ray.

## 9. Source scope and formalization target

The named semantic sources are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
Section6 supplies the complete behavioral and fixed-target argument directly.
No new Lean compilation or formal verification is asserted.

The new structural content is the exhaustive outside-weight sign partition
within the raw geometry(1)--(2), the monotone quadratic return with positivity
forced by the strict inverse pivot and full determinant, and the exact finite
switch across the zero-weight hypersurface. Finite-core equations, endpoint
deletion and a common calendar give the actual-data adapter and consumer.
The Bernstein certificate is used only to separate prior strategy-class
coverage. The positive-Gamma10 and no-positive-inverse-child branches remain
open; this theorem does not settle either arbitrary-game global-minimum case.
