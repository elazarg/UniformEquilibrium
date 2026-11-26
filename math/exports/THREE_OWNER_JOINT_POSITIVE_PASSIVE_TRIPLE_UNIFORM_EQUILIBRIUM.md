# A three-owner joint equilibrium from a positive passive triple reward

## 1. Raw finite theorem

Players are I={0,1,2,3}. The first nonempty quitting coalition S absorbs
at finite original reward r(S); live dates and literal Never pay zero.
Randomization is private and independent, and deviations are arbitrary
complete behavioral replacements. Put s_i=r_i({i}) and
Z_i(S)=r_i(S)-s_i for nonempty S only. Own levels s_i are arbitrary
signed numbers.

Let C={0,1,3}. Prescribe the following six singleton comparisons, with
a,c,d,f,l>0 and m arbitrary real:

    Z0(1)=-a, Z0(3)=c,
    Z1(0)=-d, Z1(3)=f,
    Z3(0)=-l, Z3(1)=m.

Write the actual participant rewards within C as

    p01=Z0(01), p03=Z0(03), p0C=Z0(C),
    p10=Z1(01), p13=Z1(13), p1C=Z1(C),
    p30=Z3(03), p31=Z3(13), p3C=Z3(C),

and the passive pair rewards as K0=Z0(13), K1=Z1(03), J=Z3(01).
Require the finite raw guards

    p03>c, K0>p0C,
    p13<f, p10>-d, K1<p1C,
    p30>-l; p31,p3C are arbitrary finite reals.       (G1)

Put zc=c/p03 in(0,1), and define the polynomials

    A(t,z)=t+z-tz,
    Q0(w,z)=p01*w*(1-z)+p03*(1-w)*z+p0C*w*z,
    E0(w,z)=-a*w*(1-z)+c*(1-w)*z+K0*w*z-A(w,z)*Q0(w,z),
    Q1(x,z)=p10*x*(1-z)+p13*(1-x)*z+p1C*x*z,
    E1(x,z)=-d*x*(1-z)+f*(1-x)*z+K1*x*z-A(x,z)*Q1(x,z).

Two more raw guards are

    E0(1,zc)>0, (partial_w E0)(0,zc)>0.              (G2)

These are explicit rational inequalities in the original rewards, with
positive denominator p03; no strategic rate or root is supplied. Define

    wr=(p03-c)/(K0-c-p0C+p03),
    xr=(f-p13)/(f-K1+p1C-p13).

Both numbers lie strictly between0 and1 by(G1). Put

    Q3(x,w)=p30*x*(1-w)+p31*(1-x)*w+p3C*x*w,
    E3(x,w)=-l*x*(1-w)+m*(1-x)*w+J*x*w
                                             -A(x,w)*Q3(x,w).

The last child guard is

    E3(xr,wr)>0.                                    (G3)

For the observer compute raw positive constants

    P1=max(|p10|,|p13|,|p1C|),
    L1=d+f+|K1|+4P1,
    bx=zc*min(f,f-p13)/L1,
    eta=l+min(p30,0)>0,
    P3=max(|p30|,|p31|,|p3C|),
    L3=l+|m|+|J|+4P3>0,
    bw=eta*bx/L3,
    alpha=zc*bx*bw>0.                               (B)

Choose R>=0 such that, for EVERY nonempty S subset C with S!=C,
Z2(S)>=-R, and for EVERY T containing2, Z2(T)<=R. Finally require

    M=Z2(C)>=2R/alpha.                              (O)

No other original reward coordinate is constrained. In particular all
coordinates of recipients0,1,3 at coalitions containing2 are arbitrary.

THEOREM. Every such original table has an exact stationary terminal Nash
profile with 0<q0,q1,q3<1 and q2=0, against every complete unilateral
behavioral deviation. Its actual payoff is one fixed original uniform-
equilibrium payoff, with the SAME profile at every accuracy. The owner3
participant coordinates may all be strictly positive or all negative,
and its actual native payoff need not be nonnegative. The theorem
produces the rates and target; they are not supplied as inputs.

## 2. Produce the two continuous quadratic branches

For each fixed z in(zc,1], E0 is a polynomial of degree at most two in w.
Its endpoint values are

    E0(0,z)=z(c-p03*z)<0,
    E0(1,z)=-(a+p01)(1-z)+(K0-p0C)z>0.

The second expression is affine in z and positive at zc by(G2) and at1
by(G1), so it is positive on the entire interval. A polynomial of degree
at most two with opposite endpoint signs has exactly one interior root,
which is simple: two distinct interior roots would give equal endpoint
signs, and a double root cannot reverse sign. Thus w(z) is uniquely
produced in(0,1) and continuous by fixed local brackets at its simple root.

At z=zc the polynomial has constant coefficient zero. Write
E0(w,zc)=w(b+aw), with b>0 by(G2). Also a+b=E0(1,zc)>0. Therefore
b+aw>0 on[0,1], and there is no positive root at that endpoint. Every
limit point of w(z) as z decreases to zc must consequently be zero.
Set w(zc)=0; this extends the branch continuously. At z=1 the equation is
linear and its root is exactly wr.

For z in[zc,1], E1 is a polynomial of degree at most two in x, with

    E1(0,z)=z(f-p13*z)>0,
    E1(1,z)=-(d+p10)(1-z)+(K1-p1C)z<0.

All signs are strict by(G1) and zc>0. The same quadratic argument gives
a unique simple root x(z) in(0,1), continuous on the entire closed
interval. Its endpoint at z=1 is xr. This proof includes linear or
degree-degenerate cases; no quadratic coefficient is divided out.

## 3. Produce the enlarged-cohort root

The continuous scalar function E3(x(z),w(z)) is strictly negative at
z=zc, since w(zc)=0 and

    E3(x(zc),0)=-x(zc)[l+p30*x(zc)]<=-eta*x(zc)<0.

Here 0<x(zc)<1 and p30>-l give the asserted bound even when p30<0.

It is strictly positive at z=1 by(G3). The intermediate value theorem
therefore supplies z* in(zc,1) with E3=0. Set
x=x(z*), w=w(z*) and q=(x,w,0,z*). Every active hazard is strictly
between0 and1, and E0=E1=E3=0. Choose such a root once and for all from
the fixed reward table; no accuracy has yet been requested.

For an active owner i, let hi be the probability that neither active
opponent quits, Qi its forced-Quit native reward, and Bi its one-date
passive absorption reward. The three equations just proved say exactly

    Bi=(1-hi)Qi.

The actual stationary payoff is consequently

    Ui=[qi*Qi+(1-qi)*Bi]/[1-(1-qi)hi]=Qi.

Thus both pure endpoints at every stationary date equal the actual Ui.
No independent annotation or unverified continuation is being used.

## 4. A fully raw lower bound on the triple event

The derivative of E1 in x is bounded in absolute value by L1 throughout
the unit square. Indeed the passive derivative has magnitude at most
d+f+|K1|. Also |Q1|<=P1 because it is a subprobability mixture of
0,p10,p13,p1C; |partial_x Q1|<=3P1, |A|<=1 and
|partial_x A|<=1. The product derivative adds at most4P1.

Since E1(x(z),z)=0, the mean-value estimate gives

    x(z)>=E1(0,z)/L1>=zc*min(f,f-p13)/L1=bx>0.

The derivative of E3 in w has absolute value at most L3 throughout the
unit square. Its passive derivative is l*x+m*(1-x)+J*x and has magnitude
at most l+|m|+|J|. Also |Q3|<=P3 because it is a subprobability mixture
of0,p30,p31,p3C, and |partial_w Q3|<=3P3. The A*Q3 derivative adds
at most4P3. At the selected root E3(x,w)=0, while
E3(x,0)=-x(l+p30*x)<=-eta*x. The mean-value inequality therefore gives

    L3*w>=-E3(x,0)>=eta*x>=eta*bx,
    w>=eta*bx/L3=bw.

This estimate permits negative participant rewards and a negative Q3.
In particular the actual triple event has probability

    Pr(S=C)=x*w*z*>=bx*bw*zc=alpha.                 (P)

The constants are computed solely from finite raw coordinates before
any root selection. They do not depend on the observer pole M or on the
accuracy. Existence of the selected root also confirms alpha<1.

## 5. The observer and every complete deviation

Let H=(1-x)(1-w)(1-z*)<1. The observer always Continues and its actual
native payoff is the passive absorption average. By(O) and(P),

    U2>=-R+(M+R)*Pr(S=C)/(1-H)
       >=-R+(M+R)*alpha>=R.

Its forced-Quit reward is at most R, being an average of its actual
participant coordinates, including own native zero. Continue attains U2.
Thus both pure endpoints are capped by the actual prescribed payoff for
every owner, with equality for every active owner.

Every deleted-owner clock contracts geometrically: an active owner faces
the other two positive active hazards, and the observer faces all three.
Bellman iteration therefore shows that every finite deadline and Never
is capped by the corresponding Ui. Every behavioral replacement along
the unique live history is a mixture of these stopping laws, so the same
cap holds for arbitrary complete deviations. This proves exact terminal
Nash, including all simultaneous quitting coalitions.

All prescribed and unilaterally replaced laws absorb almost surely.
Original rewards therefore add exactly s_i to each player's terminal
value; live and Never were never shifted. The common geometric opponent
tail bounds all finite-horizon payoff errors uniformly over deviations.
The fixed original target is s+U, and the same stationary profile witnesses
it at every accuracy once the horizon is sufficiently large.

## 6. A full sixty-coordinate positive passive ray

For EVERY M>=2000000, give each original own singleton reward1 and
set r_i(S)=1+Z_i(S) on every nonempty coalition, with the following
complete native table. Live and Never stay zero.

| S | Z(S) |
| --- | --- |
| 0 | (0,-9,5,-6) |
| 1 | (-5,0,2,3) |
| 2 | (-2,6,0,7) |
| 3 | (3,4,-3,0) |
| 01 | (1/10,1/10,-25,2) |
| 02 | (-1/100,27,-1/100,0) |
| 03 | (4,-100,0,1) |
| 12 | (28,-1/100,-1/100,0) |
| 13 | (10,1,0,1) |
| 23 | (0,11,-1,-1/100) |
| 012 | (9/100,9/100,-1/100,2) |
| 013 | (4,1,M,1) |
| 023 | (1,32,-301/100,-1/100) |
| 123 | (0,49/50,-1/100,-1/100) |
| I | (1,27/25,1,1) |

The child parameters are

    a=5,c=3,d=9,f=4,l=6,m=3,
    p01=p10=1/10, p03=p0C=4, p13=p1C=1,
    p30=p31=p3C=1, K0=10,K1=-100,J=2.

Thus zc=3/4, wr=1/7, xr=3/104 and the three nontrivial raw guards are

    E0(1,zc)=129/40,
    partial_w E0(0,zc)=517/160,
    E3(xr,wr)=32861/132496.

Constants(B) give bx=1/52, eta=6, P3=1, L3=15, bw=1/130 and
alpha=3/27040.
Every observer participant reward is at most100 and every nonselected
observer passive reward is at least-100. The explicit threshold at R=100
is 200/alpha=5408000/3<2000000. Hence the theorem admits the ENTIRE
displayed ray, and all child guards and observer bounds are strict with
room to perturb every one of the sixty coordinates.

All three owner3 participant premiums at03,13,013 are positive. A
joint01 phase with prescribed native owner3 value zero would have a
strictly positive forced-Quit endpoint. This is the enlarged-cohort
case that the joint-pair/solo raw cap class does not cover.

## 7. Complete old-admission comparisons on the entire ray

### 7.1 Matrix, sign and raw phase families

The literal singleton matrix is

    G=[0,-5,-2,3; -9,0,6,4; 5,2,0,-3; -6,3,7,0].

All eleven principal minors of size at least two are nonzero, and every
column has a negative coordinate. Thus no nonzero homogeneous
complementary vector exists: a support of size at least two would be a
principal kernel, and a singleton support fails an exterior inequality.
G is R0. At offset -1 the only complementary solution is

    support023, x=(16/23,0,17/23,19/23),
    Gx-1=(0,11/23,0,0), active determinant69.

The exact support census gives degree1 and standard Q, using
`r0Degree_eq_sum_admissible_inverse_supports` in
`MathUE/LinearProgramming/FiniteSupportDegree.lean` and
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`. This calibration is not removed
by the non-Q or degree-not-one source exits.

The triple determinants are(-114,39,69,2). Only023 has nonnegative
inverse, and its exterior inverse row is(59/69,-11/23,76/69), so ALL
passive-positive-inverse child selections fail. The full inverse is

    G^-1=[  2  45  62  -38 ]/133.
         [-59  69  33  -76 ]
         [ 27   9  39   19 ]
         [-36 121  81 -114 ]

Its mixed first column excludes full inverse positivity and every
full-column signable family, under all relabelings. In particular the
nonmatching positive-passive-pair class requires a positive full inverse
already at its constant matrix, and fails that necessary raw test.
The positive-passive full-inverse cone and full-positive-inverse coalition
jackpot families fail for the same reason.

The distinct one-column participant jackpot DOES pass its matrix premise
at columns1 and2. No isolated finite-table threshold exclusion is claimed.
Its pole must be a PARTICIPANT coordinate, with other data in a fixed
bounded box or controlled by a power of that pole. Every participant
coordinate is fixed on this entire passive M ray. Its existential
threshold therefore supplies no uniform guarantee for this ray; changing
the residual box separately with M gives no diagonal bound. This is only
a family-level nonimplication. The earlier signed passive-column
small-hazard argument also does not imply the ray: a positive G^-1 e2
requires a NEGATIVE passive pole for its leading cancellation. Indeed
H=(1-h)Q-B has leading field -Gq, and +M in a passive coordinate adds
another negative term. Reversing that pole sign would be invalid.

The mutual-negative block01 is neither standard Q nor homogeneous, so
projective Q-bar fails, including the homogeneous alternative in
`isProjectiveQMatrix_iff_standard_or_homogeneous`
(`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`).
There is only one mutually negative pair01, while mutual-positive pairs12
and13 share a vertex. This excludes no-mutual-negative, reciprocal-sign,
favorite/matching and opposite-sign matching raw families under every
role assignment. The negative-pair-funded class needs TWO distinct
mutual-negative pairs at its pivot and also fails. There is no negative
Hamiltonian cycle. The cyclic-child joint class would need the only
inverse-positive child023 and an allnegative pivot column into it;
that column is(-5,2,3), so no role works.

For the two-pair joining-cap family, all three partitions fail a required
joining increment: 01|23 at receiver3 against2 is -701/100; 02|13 at
receiver2 against0 is -501/100; 03|12 at receiver1 against2 is -601/100.
The joint negative-pair/solo classes, including the coarse arbitrary-one-
premium extension, require the owner3 caps at03,13,013 to be nonpositive.
All three are1 here. Their canonical labeling is unique: the negative
pair fixes01, owner1 has two positive outside singleton entries while
owner0 has one negative and one positive, and these fix the solo labels.
No relabeling repairs those raw cap failures. The passive-triple cap
chamber has its prescribed cyclic singleton sign pattern with several
mutually negative pairs, so it also fails before any pole comparison.

### 7.2 Every quiet-child selection

For child C and outsider o, nonnegative weights must satisfy for every
nonempty S subset C the rows

    F_S: sum_i w_i[-Z_i(S)]>=-Z_o(S),
    J_S: sum_i w_i[Z_i(S+i)-Z_i(S)]>=Z_o(S+o)-Z_o(S).

These are the fields of `CappedClockParentRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`.
The following positive row combinations have nonpositive coefficient
vectors and positive lower bounds. Every one of the fourteen nonempty
proper children has a blocked outside owner. No Never-row assumption is
used, so slack in that row does not help.

| C | o | Rows | Coefficients in increasing C | Lower bound |
| --- | --- | --- | --- | --- |
| 0 | 1 | F0 | (0) | 9 |
| 1 | 0 | F1 | (0) | 5 |
| 2 | 0 | F2 | (0) | 2 |
| 3 | 2 | F3 | (0) | 3 |
| 01 | 2 | J01 | (0,0) | 2499/100 |
| 02 | 1 | F0 | (0,-5) | 9 |
| 03 | 2 | F3 | (-3,0) | 3 |
| 12 | 0 | F1 | (0,-2) | 5 |
| 13 | 0 | F1 | (0,-3) | 5 |
| 23 | 0 | F2 | (0,-7) | 2 |
| 012 | 3 | 299F0+100J02 | (0,0,-1495) | 1793 |
| 013 | 2 | F3 | (-3,-4,0) | 3 |
| 023 | 1 | 7F0+6F2+4F3 | (0,-23,0) | 11 |
| 123 | 0 | F1 | (0,-2,-3) | 5 |

In particular the produced stationary child013 is not obtained from a
pointwise nonnegative-weight quiet extension: its singleton3 pays child
coordinates(3,4,0), while the observer receives-3. The selected mixed
child law and the triple-event lower bound are essential.

### 7.3 Every sure-owner complementary Nash point

Let Fi be the literal native zero-continuation Quit-minus-Continue field.
The complete table gives, with q=(q0,q1,q2,q3),

    F0=42q1q2q3-35q1q2-(121/10)q1q3+(51/10)q1
                                      -(199/100)q2q3+(199/100)q2+q3,
    F1=-(949/10)q0q2q3-30q0q2+(949/10)q0q3+(91/10)q0
                                      -(101/100)q2q3-(601/100)q2-3q3,
    F2=-(M+2599/100)q0q1q3+(3201/100)q0q1
                                      -(501/100)q0-(201/100)q1+2q3,
    F3=-(199/100)q0q1q2-6q0q1+7q0+9q1q2-2q1-(701/100)q2.

With owner j surely quitting, these are the other owners' ORIGINAL
differences too, since their sure opponent removes continuation.
The following analysis exhausts all cube faces, not only a supplied root.

For j=1, the vertex values of F3 over q0,q2 are -2,-1,-1/100,-1,
all negative, so q3=0. The two remaining differences are
F0=51/10-(3301/100)q2 and F2=-201/100+27q0. Opposite monotone
thresholds strictly inside the unit interval force both owners interior;
each endpoint would force a contradictory endpoint for the other. The
unique point is(67/900,1,510/3301,0), and its own gap is
F1=-17710703/29709000<0.

For j=2, every vertex value of F3 over q0,q1 is strictly negative, so
q3=0. Then F1=-601/100-(209/10)q0<0 forces q1=0 and F0=199/100>0
forces q0=1. The unique point is(1,0,1,0), with own gap F2=-501/100.

For j=3, write the three other differences as

    F0=1-7q1(1-q2),
    F1=104q0-(1249/10)q0q2-(351/50)q2-3,
    F2=2-(501/100)q0-(201/100)q1-(M-301/50)q0q1.

If q2>0, complementary optimality requires F2>=0, hence q0<1.
Then F0<=0 implies q1>=1/7. Since q1>0, F1>=0 implies q0>=3/104.
But now F2<=2-(M-301/50)*(3/104)*(1/7)<0, a contradiction.
Thus q2=0. The opposite thresholds F0=1-7q1 and F1=104q0-3 give
the unique point(3/104,1/7,0,1). Its own gap is F3=-79/728<0.

For j=0 set v=q1,t=q2,z=q3 and K=M+2599/100. The other differences are

    F1=[910+9190z-(3601+9591z)t]/100,
    F2=-501/100+2z+v(30-Kz),
    F3=7-(701/100)t-v[8-(701/100)t].

If v=0, F2<0 forces t=0, contradicting F1>0. If v=1, F3=-1 forces
z=0, then F2>0 forces t=1, contradicting F1<0. Therefore v is interior
and F1=0 gives

    t=T(z)=(910+9190z)/(3601+9591z) in(0,1).

Thus F2=0 too. At z=0 it gives v=167/1000, where F3>0, and at z=1
F2=-301/100+v(401/100-M)<0. Both boundary values are excluded, so z
is interior and F3=0 gives

    v=V(z)=[700-701T(z)]/[800-701T(z)].

T is strictly increasing and V strictly decreasing. From F2=0 and
2z-501/100<0 one obtains 0<z<30/K<1/1000. On this entire interval,

    1/4<T(z)<1/3, 4/5<V(z)<9/10.

The scalar equation phi(z)=-501/100+2z+V(z)(30-Kz)=0 has positive
value at0 and negative value at30/K. Its derivative is
2+V'(z)(30-Kz)-KV(z)<0 there, so there is exactly one root. This also
produces the entire forced-owner0 correspondence without radical formulas.
At it,

    F0=v(51/10-35t)+(199/100)t
                  +z[v(42t-121/10)-(199/100)t+1]
       <=(4/5)(51/10-35/4)+199/300+29/10000<-2.       (FLOOR)

This uniform estimate applies to every M on the ray.

### 7.4 Actual punishment values and persistent bases

Let v_j be the actual ORIGINAL punishment value and let
H_j=product_(i!=j)(1-q_i). Its singleton-base floor excess is exactly

    -F_j(q)+H_j(v_j-1).

Owners0,1,3 have every original participant reward at least99/100.
Immediate Quit guarantees that value against every opponent plan; hence
their actual punishment values are at least99/100 by the infimum of
best-response values in `UniformEquilibrium/Quitting/Stationary/MinMax.lean`.
The floor excesses are therefore bounded below respectively by

    2-1/100>0,
    17710703/29709000-1/100>0,
    79/728-1/100=1793/18200>0.

Owner2 has sure opponent0 at its sole complementary point, so H2=0
and its floor excess is501/100. No arbitrary negative continuation is
substituted for an actual punishment value.

Thus every singleton-base selector fails the premise in
`quittingSingletonBaseOwnerFloorExcess_nonpos_iff` and
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
A smaller free set satisfying all outsider conditions extends to one of
the same full complementary points and does not evade the floor. A
persistent base of size at least two satisfying every leave/free/outsider
condition would be a full Nash point with a sure owner. The negative own
gap at every such owner's complementary point excludes it. This covers
`nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
The induced-owner chamber variants in
`UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean` fail
the same full correspondence test; their Never variant also fails because
the original own levels are positive.

### 7.5 Every global weight and passive-pole role

Every grand participant premium is strictly positive,(1,27/25,1,1).
Thus the sure grand product refutes `HasProductLowQuittingPremium`, the
premise of `exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`.
It also excludes every nonzero nonnegative weighted forced-Quit upper
certificate. The greatest premium trap is I, defeating the at-most-two/
three premium-core rules. The mixed-trap charge criterion fails its
penultimate row T=123: outsider0's joining increment is+1.

Writing k(S)_i=Z_i(S union{i}) and h(S)=Z(S), the exact duals are

    401k(2)+k(3)=(-1/100,-301/100,-1,-401/100),
    3h(0)+3h(1)+h(01)=(-149/10,-269/10,-4,-7).

They exclude every nonzero nonnegative global forced-Quit floor weight
and proper-passive-ledger weight, including the two-ledger/graph-free
admissions. Every player has a negative participant pair, so the globally
nonnegative-participant protected-leaver condition also fails. Owner0
has positive joining increment against1 and negative increment against12,
excluding the no-strict-background-reversal condition.

For completeness, the old three-passive-pole finite guards in distinct
ordered roles(i,j,k,l) are

    A=r_i(il)-r_i(l)>0, B=r_i(ikl)-r_i(kl)<0, c=A/(A-B),
    A2=r_k(kl)-r_k(l)<0, B2=r_k(ikl)-r_k(il)<0,
    L0=(1-c)[r_j(jl)-r_j(l)]+c[r_j(jkl)-r_j(kl)]<0,
    L1=(1-c)[r_j(ijl)-r_j(il)]+c[r_j(I)-r_j(ikl)]<0,
    F0=c[(1-c)r_l(l)+c*r_l(kl)-r_l(k)]>0,
    F1=(1-c)[r_l(il)-r_l(i)]+c[r_l(ikl)-r_l(ik)]<0.

Only these nine of the24 roles pass A>0,B<0. Each has the displayed
failed later necessary guard, independent of M:

| Roles | Failed guard |
| --- | --- |
| (0,2,1,3) | B2=101>0 |
| (0,2,3,1) | F0=-2227/1369<0 |
| (0,3,1,2) | F0=-119041601/894010000<0 |
| (0,3,2,1) | B2=2499/100>0 |
| (1,3,2,0) | B2=2499/100>0 |
| (2,0,1,3) | L1=1>0 |
| (2,1,0,3) | A2=1>0 |
| (3,1,2,0) | F1=1>0 |
| (3,2,1,0) | A2=91/10>0 |

No unspecified asymptotic threshold is used for this exclusion. Together
these are complete finite-selector comparisons, with the separately
stated family-level limitation for the one-column participant jackpot.
They do not claim absence of every supplied-profile certificate; the
new raw producer itself supplies such a stationary certificate.

## 8. Exact positive and negative boundary tests

There is also a rational, explicitly produced interior policy. This is
a separate algebraic test of the construction, not the admission-separation
ray of Section6. Start from that complete table and change only

    Z0(13)=14141/2000, Z1(03)=-51059/2000,
    Z3(01)=3061/100, Z2(013)=100000000.

The actual stationary rates are

    (q0,q1,q2,q3)=(1/10,1/10,0,4/5).

Substitution gives E0=E1=E3=0, all raw guards, and the explicit observer
threshold. The native active-owner payoffs are

    U0=1601/500, U1=401/500, U3=19/100.

For every owner, let hi be its opponents' Continue probability. Direct
enumeration of all opponent coalitions gives hi<1,

    Ui=Bi/(1-hi), Qi<=Ui,

with equality Qi=Ui for owners0,1,3 and U2>100>=Q2. Thus a deadline
after t Continue dates has value

    Bi*(1-hi^t)/(1-hi)+hi^t*Qi<=Ui,

and Never has value Bi/(1-hi)=Ui. The calculation checks the entire
deadline family, rather than a finite truncation. Adding signed original
own levels(2,-3,5,-7) gives exactly the same equations with original
target s+U. This stresses the fact that live and Never payoffs stay zero.

A signed-participant stress starts from that same rational test and
changes only owner3's four coordinates

    Z3(03)=-1/10, Z3(13)=-2, Z3(013)=-3,
    Z3(01)=22839/1000.

The same exact hazards still satisfy every active equation and every raw
guard. Here eta=59/10, P3=3 and L3=43839/1000; the observer pole10^8
also satisfies the corresponding threshold. Owner3's actual native
payoff is now U3=-219/1000. Both its Quit and Continue endpoints equal
that negative value, and Never has the same value by opponent contraction.
The full finite-deadline/behavioral cap and the signed original shift
therefore still hold. This test separates exact stationary endpoint
control from an unjustified nonnegative-payoff requirement.

The observer threshold cannot simply be omitted. Retain that exact
child policy and all child-recipient coordinates, but give the observer
native reward-1 on every nonempty proper subset of C, reward0 on C,
and reward0 on every coalition containing2. The child equations and
guards are unchanged. Here H=81/500 and Pr(C)=1/125, so its prescribed
payoff is

    U2=-(1-H-Pr(C))/(1-H)=-415/419<0.

Immediate Quit gives0, a strict full-game deviation. This is a failure
of that proposed lifted profile, not a nonexistence claim for the game.
It demonstrates precisely where the observer assumption enters.

## 9. Source correspondence, handoff and remaining scope

The conjecture-facing change is a raw reward-table class with an enlarged
three-owner simultaneous phase and an explicitly bounded positive
passive-triple reward. The finite guards produce the two continuous
branches, the crossing, all three hazards, the observer cap and the
actual target. There is no assumed root, continuation, equilibrium
profile, quiet-extension weight or strategic witness. Section6 gives
an entire unbounded ray admitted by the producer, with the complete
finite-selector exclusions in Section7 and its explicit limitation for
the one-column jackpot's unspecified threshold.

The applicable existing semantic endpoint is
`isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary` in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
It characterizes complete terminal Nash for a supplied stationary product
profile by endpoint Nash at its actual terminal value and a boundary
inequality when all of an owner's opponents Continue surely. Here every
deleted-owner clock contracts, so the boundary case is absent.

More directly,
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in the same source takes a reward table, a stationary product root and
value, total Continue mass<1, the actual Bellman fixed-point identity,
endpoint Nash at error0, and every deleted-owner Continue mass<1.
Sections2–5 produce all these hypotheses for the ORIGINAL table. Thus
the missing implementation is the raw producer, not a new supplied-root
compiler. This packet is ordinary mathematical evidence; no new Lean
producer or full-conjecture theorem is asserted to be checked here.

A suitable finite theorem shape uses a reward table on nonempty subsets
of Fin4, derives s and Z, assumes precisely(G1)–(G3),(O), and concludes
the existence of rates x,w,z in(0,1), q2=0 and a payoff value satisfying
the existing stationary certificate. Its proof can be decomposed into
degree-at-most-two endpoint uniqueness and continuous root selection,
the E3 intermediate-value crossing, the raw probability bound(B), and
the literal finite-coalition Bellman identities. The final theorem then
applies the existing contracting uniform-payoff consumer. Guards are
finite polynomial or rational reward comparisons with explicitly
positive denominators; no desired strategic conclusion should be a
structure field. The exact arithmetic below supplies regression cases
for signs, all opponent subsets, signed own levels and the failed
observer-bound implication.

The result covers its stated raw chamber, including strictly positive
owner3 participant premiums. It does not remove those chamber assumptions,
make every stationary root valid, or solve unrestricted Fin4. The proof
does not depend on the attached-triangle source reduction or on a
negative-passive-pole asymptotic argument.

## Appendix. Complete exact arithmetic reproduction

Save the following program as `three_owner_passive_pole_check.py` and
run it with Python and SymPy installed. It contains the complete sixty
coordinates, symbolic M=2000000+tau with tau>=0, all fourteen child
obstructions, all twenty-four passive-pole role selections, the full
sure-owner identities and bounds, and all three exact boundary tests. The
continuous root and all-face completeness arguments are proved above;
the program verifies their finite algebra without numerical tolerances.


```python
"""Exact uniform checks for a three-owner positive passive-triple producer.

Run with Python and SymPy. The proof supplies the continuous branches and
complete equilibrium; this program checks its algebra and entire ray audits.
"""
from itertools import combinations, permutations, product
import sympy as s
R=s.Rational
I=tuple(range(4))
COAL=tuple(C for n in range(1,5) for C in combinations(I,n))
tau=s.symbols('tau',nonnegative=True)
M=2000000+tau
q=s.symbols('q0:4')
LITERAL = {
    (0,): (0,-9,5,-6), (1,): (-5,0,2,3),
    (2,): (-2,6,0,7), (3,): (3,4,-3,0),
    (0,1): (R(1,10),R(1,10),-25,2),
    (0,2): (-R(1,100),27,-R(1,100),0),
    (0,3): (4,-100,0,1), (1,2): (28,-R(1,100),-R(1,100),0),
    (1,3): (10,1,0,1), (2,3): (0,11,-1,-R(1,100)),
    (0,1,2): (R(9,100),R(9,100),-R(1,100),2),
    (0,1,3): (4,1,M,1),
    (0,2,3): (1,32,-R(301,100),-R(1,100)),
    (1,2,3): (0,R(49,50),-R(1,100),-R(1,100)),
    I: (1,R(27,25),1,1)}

TABLE={(i,C):s.sympify(LITERAL[C][i]) for C in COAL for i in I}
assert len(TABLE)==60
def native(i,C):
    C=tuple(sorted(set(C)))
    return TABLE[i,C] if C else s.S.Zero
def reward(i,C):
    assert C
    return 1+native(i,C)
def joining(i,C):
    return native(i,set(C)|{i})-native(i,C)
F=[]
for i in I:
    others=[j for j in I if j!=i]
    f=0
    for bits in product((0,1),repeat=3):
        C=[j for j,bit in zip(others,bits) if bit]
        pp=s.prod(q[j] if bit else 1-q[j] for j,bit in zip(others,bits))
        f+=pp*joining(i,C)
    F.append(s.expand(f))

def rows(child, outsider):
    out = {}
    for A in COAL:
        if set(A) <= set(child):
            out['F', A] = ([-native(i, A) for i in child], -native(outsider, A))
            out['J', A] = ([joining(i, A) for i in child], joining(outsider, A))
    return out


BLOCKERS = [
    ((0,), 1, [('F', (0,), 1)]), ((1,), 0, [('F', (1,), 1)]),
    ((2,), 0, [('F', (2,), 1)]), ((3,), 2, [('F', (3,), 1)]),
    ((0, 1), 2, [('J', (0, 1), 1)]),
    ((0, 2), 1, [('F', (0,), 1)]), ((0, 3), 2, [('F', (3,), 1)]),
    ((1, 2), 0, [('F', (1,), 1)]), ((1, 3), 0, [('F', (1,), 1)]),
    ((2, 3), 0, [('F', (2,), 1)]),
    ((0, 1, 2), 3, [('F', (0,), 299), ('J', (0, 2), 100)]),
    ((0, 1, 3), 2, [('F', (3,), 1)]),
    ((0, 2, 3), 1, [('F', (0,), 7), ('F', (2,), 6), ('F', (3,), 4)]),
    ((1, 2, 3), 0, [('F', (1,), 1)])]
assert {C for C, _, _ in BLOCKERS} == {C for C in COAL if len(C) < 4}
BLOCKER_VALUES = []
for C, o, terms in BLOCKERS:
    rr = rows(C, o)
    coeff = [sum(w*rr[k, A][0][j] for k, A, w in terms) for j in range(len(C))]
    rhs = sum(w*rr[k, A][1] for k, A, w in terms)
    assert all(w > 0 for _, _, w in terms)
    assert max(coeff) <= 0 and rhs > 0
    BLOCKER_VALUES.append((C, o, coeff, rhs))

# Exhaust all24 role assignments of the old three-passive-pole raw guards.
passing = []
pole_details = []
for i, j, k, l in permutations(I):
    a, b = joining(i, [l]), joining(i, [k, l])
    if not (a > 0 and b < 0):
        continue
    c = a/(a-b)
    a2, b2 = joining(k, [l]), joining(k, [i, l])
    l0 = (1-c)*joining(j, [l])+c*joining(j, [k, l])
    l1 = (1-c)*joining(j, [i, l])+c*joining(j, [i, k, l])
    f0 = c*((1-c)*reward(l, [l])+c*reward(l, [k, l])-reward(l, [k]))
    f1 = (1-c)*joining(l, [i])+c*joining(l, [i, k])
    flags = [a2 < 0, b2 < 0, l0 < 0, l1 < 0, f0 > 0, f1 < 0]
    pole_details.append(((i, j, k, l), c, (a2, b2, l0, l1, f0, f1), flags))
    if all(flags):
        passing.append((i, j, k, l))
assert passing == []

# Literal raw core and the entire positive passive-pole ray.
x,w,z=s.symbols('x w z',nonnegative=True)
Q0=R(1,10)*w*(1-z)+4*(1-w)*z+4*w*z
Q1=R(1,10)*x*(1-z)+(1-x)*z+x*z
Q3=x*(1-w)+(1-x)*w+x*w
E0=-5*w*(1-z)+3*(1-w)*z+10*w*z-(w+z-w*z)*Q0
E1=-9*x*(1-z)+4*(1-x)*z-100*x*z-(x+z-x*z)*Q1
E3=-6*x*(1-w)+3*(1-x)*w+2*x*w-(x+w-x*w)*Q3
zc,xr,wr=R(3,4),R(3,104),R(1,7)
assert E0.subs({w:1,z:zc})==R(129,40)
assert s.diff(E0,w).subs({w:0,z:zc})==R(517,160)
assert E3.subs({x:xr,w:wr})==R(32861,132496)
bx,bw=R(1,52),R(1,130)
alpha=zc*bx*bw
assert alpha==R(3,27040)
assert M>=200/alpha
assert all(native(2,C)>=-100 for C in COAL if 2 not in C and C!=(0,1,3))
assert all(native(2,C)<=100 for C in COAL if 2 in C)
assert native(2,(0,1,3))==M

# Complete sure-owner correspondence identities; analytic bounds are in text.
K=M+R(2599,100)
T=(910+9190*z)/(3601+9591*z)
V=(700-701*T)/(800-701*T)
assert s.factor(s.diff(T,z))>0
assert s.factor(s.diff(V,z))<0
assert R(1,4)<T.subs(z,0)<T.subs(z,R(1,1000))<R(1,3)
assert R(4,5)<V.subs(z,R(1,1000))<V.subs(z,0)<R(9,10)
phi=-R(501,100)+2*z+V*(30-K*z)
assert phi.subs(z,0)>0
assert s.factor(phi.subs(z,30/K))<0
assert 30/K<R(1,1000)
subs0={q[0]:1,q[1]:V,q[2]:T,q[3]:z}
assert s.factor(F[1].subs(subs0))==0
assert s.factor(F[3].subs(subs0))==0
assert s.factor(F[2].subs(subs0)-phi)==0
own0=F[0].subs(q[0],1)
expected0=q[1]*(R(51,10)-35*q[2])+R(199,100)*q[2]+q[3]*(q[1]*(42*q[2]-R(121,10))-R(199,100)*q[2]+1)
assert s.expand(own0-expected0)==0
upper0=R(4,5)*(R(51,10)-R(35,4))+R(199,300)+R(29,10000)
assert upper0 < -2

points={1:(R(67,900),1,R(510,3301),0),2:(1,0,1,0),3:(R(3,104),R(1,7),0,1)}
for owner,pt in points.items():
    gaps=[s.factor(f.subs(dict(zip(q,pt)))) for f in F]
    assert gaps[owner]<0
    for i in I:
        if i==owner:continue
        assert gaps[i]<=0 if pt[i]==0 else gaps[i]>=0 if pt[i]==1 else gaps[i]==0
    if owner in (1,3):
        assert min(native(owner,C) for C in COAL if owner in C)==-R(1,100)
        assert -gaps[owner]-R(1,100)>0
assert F[3].subs(dict(zip(q,points[3])))==-R(79,728)
assert min(native(0,C) for C in COAL if 0 in C)==-R(1,100)
# Owner1 or2 sure makes player3 strictly prefer Continue on the whole cube.
for owner in (1,2):
    others=[j for j in I if j not in (owner,3)]
    for bits in product((0,1),repeat=2):
        sub={q[owner]:1,**dict(zip([q[j] for j in others],bits))}
        assert F[3].subs(sub)<0
assert s.expand(F[0].subs(q[3],1)-(1-7*q[1]*(1-q[2])))==0
assert s.expand(F[1].subs(q[3],1)-(104*q[0]-R(1249,10)*q[0]*q[2]-R(351,50)*q[2]-3))==0
assert s.expand(F[2].subs(q[3],1)-(2-R(501,100)*q[0]-R(201,100)*q[1]-(M-R(301,50))*q[0]*q[1]))==0
assert 2-(M-R(301,50))*R(3,104)*R(1,7)<0

# Global finite admission obstructions.
assert min(native(i,I) for i in I)>0
assert [401*native(i,{2,i})+native(i,{3,i}) for i in I]==[-R(1,100),-R(301,100),-1,-R(401,100)]
assert [3*native(i,{0})+3*native(i,{1})+native(i,{0,1}) for i in I]==[-R(149,10),-R(269,10),-4,-7]
assert all(any(native(i,C)<0 for C in COAL if i in C) for i in I)
assert joining(0,[1,2,3])==1
assert joining(0,[1])>0 and joining(0,[1,2])<0
G=s.Matrix.hstack(*(s.Matrix(LITERAL[(j,)]) for j in I))
assert G.det()==133
assert all(G.extract(T,T).det()!=0 for n in (2,3,4) for T in combinations(I,n))
assert all(any(G[i,j]<0 for i in I) for j in I)
assert [T for T in combinations(I,3) if min(G.extract(T,T).inv())>=0]==[(0,2,3)]
assert list(G.extract([1],[0,2,3])*G.extract([0,2,3],[0,2,3]).inv())==[R(59,69),-R(11,23),R(76,69)]
assert min(G.inv()[:,0])<0<max(G.inv()[:,0])
assert [j for j in I if min(G.inv()[:,j])>0]==[1,2]
assert [(i,j) for i,j in combinations(I,2) if G[i,j]<0 and G[j,i]<0]==[(0,1)]
assert [(i,j) for i,j in combinations(I,2) if G[i,j]>0 and G[j,i]>0]==[(1,2),(1,3)]
assert not any(all(G[P[(j+1)%4],P[j]]<0 for j in I) for P in permutations(I))
assert joining(3,[2])==-R(701,100)
assert joining(2,[0])==-R(501,100)
assert joining(1,[2])==-R(601,100)
lcp=[]
for size in (2,3,4):
    for T in combinations(I,size):
        xx=s.zeros(4,1)
        for i,value in zip(T,G.extract(T,T).inv()*s.ones(size,1)):xx[i]=value
        rr=G*xx-s.ones(4,1)
        if min(xx)>=0 and min(rr)>=0:lcp.append((T,list(xx),list(rr),G.extract(T,T).det()))
assert lcp==[((0,2,3),[R(16,23),0,R(17,23),R(19,23)],[0,R(11,23),0,0],69)]
print('PASS: whole positive passive ray, branch guards, explicit spectator probability and threshold.')
print('PASS: all14 quiet children, all24 passive-pole roles, complete sure-owner bounds and actual punishment floors.')
print('PASS: matrix supports, weighted/premium and raw phase-family comparisons.')

# A separately produced rational interior policy; this is an algebra/control
# test, not the prior-admission separation ray.
xx,ww,zz=R(1,10),R(1,10),R(4,5)
k0=R(14141,2000)
k1=-R(51059,2000)
j3=R(3061,100)
test={C:[s.sympify(v).subs(tau,0) for v in LITERAL[C]] for C in COAL}
test[(1,3)][0]=k0
test[(0,3)][1]=k1
test[(0,1)][3]=j3
test[(0,1,3)][2]=10**8
e0=E0+(k0-10)*w*z
e1=E1+(k1+100)*x*z
e3=E3+(j3-2)*x*w
assert e0.subs({w:ww,z:zz})==e1.subs({x:xx,z:zz})==e3.subs({x:xx,w:ww})==0
wrtest=(4-3)/(k0-3-4+4)
xrtest=(4-1)/(4-k1+1-1)
assert e0.subs({w:1,z:zc})>0 and s.diff(e0,w).subs({w:0,z:zc})>0
assert e3.subs({x:xrtest,w:wrtest})>0
bxtest=zc*3/(9+4+abs(k1)+4)
bwtest=6*bxtest/(6+3+j3+4)
alphatest=zc*bxtest*bwtest
assert 10**8>=200/alphatest
hz=(xx,ww,0,zz)
own=(2,-3,5,-7)
def verify_profile(data,expected_values):
    for original in (False,True):
        values=[]
        for i in I:
            others=[j for j in I if j!=i]
            qq=bb=0
            hi=s.prod(1-hz[j] for j in others)
            for bits in product((0,1),repeat=3):
                C=tuple(j for j,bit in zip(others,bits) if bit)
                prob=s.prod(hz[j] if bit else 1-hz[j] for j,bit in zip(others,bits))
                T=tuple(sorted(set(C)|{i}))
                qq+=prob*(data[T][i]+(own[i] if original else 0))
                if C:bb+=prob*(data[C][i]+(own[i] if original else 0))
            ui=s.factor((hz[i]*qq+(1-hz[i])*bb)/(1-(1-hz[i])*hi))
            assert 0<=hi<1
            assert ui==s.factor(bb/(1-hi))  # literal Never and every Continue date
            assert qq<=ui
            if i in (0,1,3):assert qq==ui
            else:assert ui>(100+own[i] if original else 100)
            values.append(ui-(own[i] if original else 0))
        assert [values[i] for i in (0,1,3)]==expected_values
verify_profile(test,[R(1601,500),R(401,500),R(19,100)])
print('PASS: rational enlarged-cohort root, all complete stationary caps and signed original target.')

# Exact signed participant stress, including a negative active native payoff.
p30s,p31s,p3Cs=-R(1,10),-s.Integer(2),-s.Integer(3)
js=R(22839,1000)
q3s=p30s*x*(1-w)+p31s*(1-x)*w+p3Cs*x*w
e3s=-6*x*(1-w)+3*(1-x)*w+js*x*w-(x+w-x*w)*q3s
assert p30s>-6
assert e3s.subs({x:xx,w:ww})==0
assert e3s.subs({x:xrtest,w:wrtest})>0
eta=6+min(p30s,0)
L3=6+3+abs(js)+4*max(abs(p30s),abs(p31s),abs(p3Cs))
assert eta==R(59,10) and L3==R(43839,1000)
alpha_signed=zc*bxtest*(eta*bxtest/L3)
assert 10**8>=200/alpha_signed
signed_test={C:list(value) for C,value in test.items()}
signed_test[(0,3)][3]=p30s
signed_test[(1,3)][3]=p31s
signed_test[(0,1,3)][3]=p3Cs
signed_test[(0,1)][3]=js
verify_profile(signed_test,[R(1601,500),R(401,500),-R(219,1000)])
print('PASS: signed participant stress with negative active value and every complete cap.')
# Observer-bound negative test: retain the exact child policy and child
# coordinates, but make every proper passive observer reward -1, the
# triple reward 0, and every observer participant reward 0.
H=(1-xx)*(1-ww)*(1-zz)
pc=xx*ww*zz
negative_observer=-(1-H-pc)/(1-H)
assert H==R(81,500) and pc==R(1,125)
assert negative_observer==-R(415,419)<0
assert 0>negative_observer  # immediate Quit, compared with prescribed Continue
print('PASS: removing the observer pole bound can destroy the full-game cap.')
```
