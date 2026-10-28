# Uniform equilibrium through a joint quitting step with a negative owner value

This packet constructs exact periodic terminal equilibria on a raw four-player
reward class, including a game outside the earlier nonpositive joining-excess
condition. It is ordinary mathematics, not checked in Lean. Arbitrary Fin4
remains open.

## 1. Game and exact conclusions

Players are 0,1,2,3. At each live date they independently choose Continue or
Quit. The first nonempty quitting coalition D absorbs at the real vector
r(D), paid thereafter; live play and literal AllNever pay zero. A deviation
may replace a player's entire behavioral strategy. Randomization is private
and independent. Set kappa_i=r_i({i}), Z_i(D)=r_i(D)-kappa_i and
Gamma_ij=Z_i({j}); Gamma_ii=0. We use this native notation only after proving
that opponents absorb under every deviation, which justifies the row shifts.



Use native own-zero rewards Z_i(D), with original rewards kappa_i+Z_i(D)
and original live/Never zero. Define positive singleton coefficients

    beta=-Gamma02, d=-Gamma30, e=Gamma32, f=Gamma20,
    k=Gamma03, h=-Gamma23, g=-Gamma13, d1=-Gamma31.

Gamma01,Gamma21,n=Gamma10,ell=Gamma12 are arbitrary finite. Assume

    A=-Z1(13)>g, c=Z2(23)>0, u=Z3(13)>=0, v=Z3(23)<e,
    Z0(02)=-s, s<beta,
    Z2(02)=f+eta, eta>0.

All other higher entries are arbitrary fixed finite numbers except
Z1(12)=-K and Z2(12)=p. No additional nonsingleton row0 entry is required to be
nonpositive. The entry Z0(03) is constrained by the explicit tests below.
Put omega=Z3(02)+d-e. For b define the following raw rational functions:

    D=d-b*omega,
    T0=k-b*(k+beta-s),
    F=f*e*T0-h*(beta-s*b)*D,
    P_eta(b)=F*(D-e*b)-eta*e*b*((beta-s*b)*D+e*T0).     (1)

P_eta is a polynomial of degree at most three. Suppose it has a simple root b
for which

    0<b<1, D>0, x=e*b/D in(0,1),
    C=b*(beta-s)/(1-b) in(0,k),
    T=x*eta/(1-x)>0.                                  (2)

Define

    P1=x*(1-b)*n+(1-x)*b*ell+x*b*Z1(02),
    L=k*(1-x)*(1-b)/(k+s*b),
    A10=(k*P1-s*b*g)/(k+s*b),
    j=[g*C-A10*(k-C)]/[k-L*(k-C)].                    (3)

Put

    X1=P1-(1-x)*(1-b)*j, X2=x*(f+eta),
    zeta0=Z0(03), H0=k-max(zeta0,0), B_s=max(s*b,0).

Require

    A*T/c<j<g*C/k,                                    (4)
    H0*X1>g*B_s, H0*X2>(h+c)*B_s,                    (5)
    x*(1-b)*Z3(03)+(1-x)*b*v+x*b*Z3(023)<0.            (6)

Since X2>0, condition(5) implies H0>0 and then X1>0. Thus zeta0<k.
It selects internally one probability a from the nonempty open interval

    B_s/(H0+B_s)<a<min(X1/(X1+g),X2/(X2+h+c));       (5a)

for example use its midpoint. No sign restriction remains on Z0(02), beyond
Z0(02)>Gamma02. The denominator defining j is positive even when s<0:

    (k+s*b)[k-L(k-C)]
      =k{b(k+beta)+x[k-b(k+beta-s)]}>0,

because k+s*b>b(k+beta)>0 and k-b(k+beta-s)=(1-b)(k-C)>0.
When s>0 and zeta0<=0, the first inequality in(5) follows from(4), and the
second reduces to k*x*(f+eta)>(h+c)*s*b.

Then there exists finite M, depending only on these fixed raw entries and the
selected simple root, such that EVERY real p and every

    K>=M*(1+|p|)                                      (7)

has an exact finite-period terminal-payoff Nash equilibrium and hence a
uniform-equilibrium payoff for arbitrary original own levels kappa. No
condition on the sign of p or Gamma21 is needed. Constants can be uniform on
compact sets with a continuous selected root and all displayed strict guards
separated from failure, including resonance cases described below.

No continuation or strategy is assumed: the polynomial root b is a finite
raw test, and every core and return root is produced. A finite union over the
at most three real roots removes any need to preselect a root externally.

A second, fully quantitative conclusion uses the following complete native
table at K=1000 and eta=1/100. For arbitrary kappa in R^4, r(D)=kappa+Z(D)
has an exact terminal equilibrium whose independent private hazards repeat
every 75 dates. Its original uniform-equilibrium payoff belongs to

    kappa + (0, (0.2666973,0.2666976), (0.1755232,0.1755234), 0).

The interval endpoints are exact decimal rationals. Moreover, an open
neighborhood in all 60 original terminal rewards has such a 75-date exact
periodic equilibrium. The neighborhood's radius is existential.

| D | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
|0|0|2|2|-1|
|1|3|0|-2|-2|
|2|-1|1/2|0|1|
|3|3|-3|-1|0|
|01|0|-1|-10|-12|
|02|-1/10|5|2+eta|-219/29|
|12|-12|-K|0|-6|
|03|-20|3|-5|1|
|13|2|-100|-1|10|
|23|-6|9|3|-100|
|012|-20|6|-100|11|
|013|-20|8|10|-10|
|023|-20|-8|-100|15/2|
|123|-8|11|2|1|
|0123|-5|-9|-100|21/2|

For kappa=(1,1,1,1), every table in this displayed family with K>=1000 and
0<=eta<=1/100 has no stationary equilibrium and no full-response Nash root with a sure
quitter and actual continuation best-response caps. Section 6 supplies the exact exclusions
and comparisons with other existing raw producers. These statements do not
exclude arbitrary nonstationary strategies, which this packet constructs.

## 2. Root comparisons, wash, and the unrestricted consumer

For independent root hazards q, define

    H_i=product_(j!=i)(1-q_j),
    P_i=sum_(nonempty S subset opponents) w_q(S) Z_i(S),
    Q_i=sum_(S subset opponents) w_q(S) Z_i(S union{i}),
    w_q(S)=product_(j in S)q_j product_(j outside S,i)(1-q_j).

Given successor V, Continue pays P_i+H_i V_i. A mixed owner must have this
equal to Q_i; a quiet owner needs Q_i<=P_i+H_i V_i. The current prescribed
value is their q_i-mixture. These are full first-action comparisons; the
periodic argument below makes them valid for complete behavioral deviations.
No empty dates may be inserted at a negative annotation.

Here is a finite solo3 wash used in both constructions. Write
Gamma[:,3]=(k,-g,-h,0), A=-Z1(13)>g>0, c=Z2(23)>0 and suppose
zeta0=Z0(03)<k. At current (s,-v,z,0), assume

    0<v<g, s>kv/g, z>=cv/A.

The solo3 hazard v/A is legal: row1's Quit offer equals its current value
-v, row2's offer is cv/A, row0's offer is zeta0*v/A<k*v/A<s, and owner3 is indifferent.
Its successor is the affine inverse transport, with

    v'=v(A-g)/(A-v),
    s'=(s-kv/A)/(1-v/A), z'=(z+hv/A)/(1-v/A).

Thus v'<v, s'>kv'/g, and z'>=cv'/A. Repeating drives v to zero
geometrically while z increases and s-kv/g stays positive. After finitely
many steps z>=cv/g. A final solo3 hazard v/g has successor row1 zero,
positive row0 and row2, and obeys all comparisons; for row0 use
s>kv/g>zeta0*v/g. For j regular steps,
with starting debt v, total survival is exactly

    S_j=1-v/g+(v/g)(1-g/A)^j.

The successor is (s-k(1-S_j),-v(1-g/A)^j,z+h(1-S_j),0)/S_j.

From its final successor V=(V0,0,V2,0), close to
A_*=(A0,A1,A2,0), where 0<=A0<V0<k and A1,A2>0. The required aggregate
mass is t=(V0-A0)/(k-A0). The exact transport identities from the original
wash entrance E are

    A1(k-E0)=(k-A0)E1+g(E0-A0),
    A2(k-E0)=(k-A0)E2+h(E0-A0).                    (R)

For A0=0 these are A1(k-E0)=gE0+kE1 and
A2(k-E0)=hE0+kE2. Subdivide the remaining mass into m literal roots
q_j=t/(m-jt), j=0,...,m-1, whose product survival is1-t. Choose m so that
c max q_j<min(V2,A2). Row2 is safe throughout; row1 is nonnegative with
negative joining reward -A. For row0, at each date its current value is
kq+(1-q)V0_next with V0_next>=0, hence at least kq>zeta0*q.
Owner3 is indifferent. This yields a finite period with exact comparisons.

If each period contains one joint02 root with hazards x,b in (0,1), every
deviator faces opponents-only absorption at least rho=min(x,b)>0 per period.
On survival the only realized public action history is all Continue, so an
arbitrary deviator cannot change the future opponent hazards. After n periods
opponents-only survival is at most (1-rho)^n. Bounded payoff transport then
identifies all annotations with actual terminal payoffs. Unrolling the root
inequalities against any history-dependent behavioral deviation leaves a
bounded remainder times this vanishing survival. Hence the profile is exact
terminal Nash, including against literal Never.

Opponent absorption also justifies adding arbitrary kappa_i to row i. If the
literal period has length L, the expected opponents-only absorption time is
at most L/rho+1, uniformly over deviations. For original reward bound R0,
the terminal payoff and T-horizon average payoff differ by at most
2R0(L/rho+2)/T. Thus this same profile and its fixed payoff satisfy the
uniform-equilibrium contract at every positive accuracy.

## 3. Production from the raw joint-return criterion

### Limiting finite core and the integer chosen from raw data

Set

    a0=c/h, delta=c/(c+h), B0=A+a0*g,
    w0=T/c, theta0=w0/(1+a0*w0),
    J=(j+a0*g*w0)/(1+a0*w0).

By(4), j>0, j<g, and

    0<theta0<J/B0,
    B0>(a0+1)*g>(a0+1)*J.

Choose an integer N>=1 so that

    delta*J/B0 <= delta^(-(N-1))*theta0 <= J/B0.       (8)

Such an N always exists by multiplying theta0 by 1/delta until first reaching
delta*J/B0. At a resonance equality, either neighboring choice is possible.
For the moment assume both inequalities are strict. Put

    theta_l=delta^(-l)*theta0,
    w_l=theta_l/(1-a0*theta_l),
    Z_l=(J-B0*theta_l)/(1-(a0+1)*theta_l), 0<=l<N.

All w_l,Z_l are positive, and w_l<1. Set Y_N=Z_N=0 and solve backward

    (u+d1)*Y_l=u*Y_(l+1)+v*Z_(l+1)+(e-v)*Z_l.         (9)

The Z_l strictly decrease. Since u>=0 and v<e, every Y_l>0: for v<0 rewrite
the last two terms as e*Z_l+(-v)*(Z_l-Z_(l+1)); for v>=0 both coefficients
are nonnegative. This is a finite backward recursion; no contraction bound
or relationship between u/(u+d1) and delta is required.

The core's limiting prescribed survival is

    H=[1-(a0+1)*theta_(N-1)]/[1-a0*theta0] in(0,1).

Choose E0 so that C=k*(1-H)+H*E0. Its other exit coordinates are

    E1=-vexit,
    vexit=[J-g*(a0+1)*theta_(N-1)]/[1-(a0+1)*theta_(N-1)],
    E2=(c+h)*theta_(N-1)/[1-(a0+1)*theta_(N-1)], E3=0.

The first core entrance is exactly (C,-j,T,0). Direct affine transport gives

    E0-k*vexit/g=(C-k*j/g)/H>0,
    0<vexit<g, E0<k,
    A*E2-c*vexit>0.                                  (10)

The last inequality is precisely the strict lower inequality in(8); its
numerator is c*((B0/delta)*theta_(N-1)-J). Thus all finite-wash conditions
hold strictly. In particular E0>0, and every core row0 annotation is positive.

### Exact finite core under small alpha and pi

Let alpha=1/K>0 and pi=p/K; initially regard alpha,pi as two independent small
real analytic parameters. At root l prescribe independent hazards

    q_l=(0,alpha*Y_l,alpha*Z_l,w_l).

Its owner1,2 Quit values and passive terms are

    Q1=-Z*(1-w)-A*w+alpha*(A+Z1(123))*Z*w,
    Q2=pi*Y*(1-w)+c*w+alpha*(Z2(123)-c)*Y*w,
    P1=alpha*ell*Z*(1-w)-g*w*(1-alpha*Z)+alpha*Z1(23)*Z*w,
    P2=alpha*Gamma21*Y*(1-w)-h*w*(1-alpha*Y)+alpha*Z2(13)*Y*w,
    H1=(1-alpha*Z)*(1-w), H2=(1-alpha*Y)*(1-w).

Impose Q_i,l=P_i,l+H_i,l*Q_i,l+1 for i=1,2 and l<N-1.
At the last root define E_i=(Q_i-P_i)/H_i. For owner3 put

    Qhat3=u*Y+v*Z+alpha*(Z3(123)-u-v)*Y*Z,
    Phat3=-d1*Y+e*Z+alpha*(Z3(12)+d1-e)*Y*Z,
    H3=(1-alpha*Y)*(1-alpha*Z).

Impose Qhat3_l=Phat3_l+H3_l*Qhat3_(l+1), with Qhat3_N=0.
These are exactly the owner3 equations divided by alpha; consequently they
remain meaningful analytically at alpha=0. Propagate row0 by its literal
finite expectation from E0.

At alpha=pi=0, in coordinates(theta,J), the forward equations for owners1,2
are exactly theta_(l+1)=theta_l/delta and J_(l+1)=J_l. They do not depend on
Y. The remaining Y system is the invertible finite backward triangular
system(9). Therefore the finite-dimensional implicit function theorem gives
an analytic exact core near the displayed one, parametrized by initial
theta,J,E0 and alpha,pi. Its entrance coordinates C0,-C1,C2 form analytic
local coordinates C,j,T: at zero their diagonal coordinate derivatives are
H, 1/(1-a0*theta0), c/(1-a0*theta0)^2, all positive (after the triangular
coordinate ordering). Thus there is an analytic exact core with entrance

    (C,-j,T,C3(C,j,T,alpha,pi)), C3(C,j,T,0,0)=0.

All strictly positive hazards, all strict core/wash inequalities, and core
row0 positivity persist for sufficiently small |alpha|+|pi|. At each limiting
core root, quiet0 has value k*w_l+(1-w_l)*U0_next>k*w_l and Quit offer
w_l*zeta0<k*w_l, since zeta0<k and U0_next>0. The contributions of every
other joining coalition to that offer are O(alpha), so its strict
comparisons also persist. The five other nonsingleton row0 entries may
therefore be arbitrary fixed finite numbers.
This is why no sign restriction on p is necessary: the first w0 is already strictly positive;
no induction from a zero entrance Q2 is being attempted.

### Four outer equations and the cubic Jacobian

For the exact core entrance set b=C/(C+beta-s), and use one joint02 root
with hazards(x,0,b,0). Owners0,2 are indifferent exactly when

    T=x*eta/(1-x).

Its current values are

    X0=-s*b, X2=x*(f+eta),
    X1=P1-(1-x)*(1-b)*j,
    X3=-d*x*(1-b)+e*(1-x)*b+x*b*Z3(02)
         +(1-x)*(1-b)*C3.

Impose X3=0. For the algebraic closure only, define the auxiliary point
A° using hazard a°=s*b/(k+s*b):

    A°0=A°3=0,
    A°1=(k*X1-s*b*g)/(k+s*b),
    A°2=(k*x*(f+eta)-s*b*h)/(k+s*b).

In equations(11),(12), the symbol A refers to this auxiliary vector A°.
It is solely an algebraic point: a° may be negative when s<0, and no
strategic root with that probability is executed.

The remaining two exact return equations are

    A1*(k-E0)=g*E0-k*vexit,
    A2*(k-E0)=k*E2+h*E0.                              (11)

At alpha=pi=0, affine core transport converts these to

    A1*(k-C)=g*C-k*j,
    A2*(k-C)=k*T+h*C.                                 (12)

The four equations are(11), X3=0 and T=x*eta/(1-x). Their limiting Jacobian
in(C,j,T,x) is nonsingular. Indeed X3=0 selects x=e*b/D with derivative
-D!=0; the entrance equation selects T; the second equation in(12), after
positive-denominator multiplication, is exactly P_eta(b)=0, simple by
hypothesis; and the first equation is linear in j with coefficient
k-L*(k-C)>0. The C-to-b derivative is positive. Consequently the IFT gives
actual exact roots for every sufficiently small alpha,pi, with all strict
prefix guards persisting. Taking M sufficiently large ensures this whenever
alpha=1/K and pi=p/K satisfy(7).

The first equation in(12) and j<g*C/k imply A°1>0; X1>0 is supplied by(5). For actual
execution choose the fixed a from(5a) and prepend one solo3 root to X. Its
current vector is

    A(a)=a*Gamma[:,3]+(1-a)*X.

It satisfies A(a)3=0 and A(a)0,A(a)1,A(a)2>0. Quiet0 has value
k*a-(1-a)*s*b>a*max(zeta0,0), quiet1 has positive value and negative offer -A*a,
and quiet2 has value (1-a)*X2-h*a>c*a. The row0 inequality follows from
(5a) when s*b>0; when s*b<=0 its excess over a*max(zeta0,0) is
-(1-a)*s*b+a*H0>0. The selected a remains legal for all
sufficiently small alpha,pi by the strict limiting guards. At the joint root,
quiet1's offer is

    x*(1-b)*Z1(01)-(1-x)*b*K+x*b*Z1(012),

which is uniformly below X1 for large K. Quiet3's offer is strictly negative
by(6), while its value is zero. Both active owners are exactly indifferent,
including owner0 whose current value is -s*b. No empty date is inserted.

### The resonance boundary is also covered

This is finite endpoint gluing, not a nonuniform limiting argument. Suppose
(8) is at the upper boundary for N. Then N>=2, because theta0<J/B0 is strict.
The N-1 core lies at its lower wash boundary. Regard A as an additional local
raw parameter while holding all other displayed data fixed. The cubic root
b, physical entrance j,T and theta0,J do not depend on A at alpha=pi=0.
The limiting last Z of the N branch has A derivative

    -theta_(N-1)/[1-(a0+1)*theta_(N-1)] < 0.

The limiting wash margin A*E2-c*vexit of the N-1 branch has strictly positive
A derivative. The other strict legality margins remain positive on both
branches. The IFT supplies both unconstrained branches uniformly near this
raw point, even if their single boundary margin has either sign.

The equation Z_last,N=0 is a smooth hypersurface in (A,alpha,pi). At that
hypersurface the terminal owner3 equation forces Y_last,N=0, so the last root
is pure3. Its current row1,2 values are -A*w and c*w. Deleting this root
therefore makes the N-1 exit satisfy A*E2-c*vexit=0 exactly. The entrance,
joint root, prefix and return equations are unchanged: the two return
identities only acquire a common positive survival factor. Local uniqueness
of the shorter IFT branch identifies it with this deleted core. Thus its
wash-zero hypersurface is exactly the same one.

Their opposite nonzero A derivatives persist near zero. On one side the
N-core last Z is positive; on the other the N-1 wash margin is positive.
At the common boundary both are legal. Since all other margins stay strict,
the union supplies a legal finite core throughout a uniform neighborhood of
the resonance, including every sufficiently small physical alpha,pi at the
original A. This gives a uniform M. Compact sets are covered by finitely many
ordinary and resonance neighborhoods; the possible integers N are locally
bounded because eta and all strict margins stay positive on the compact set.

### Literal finite wash, complete deviations, original uniform payoff

From exit(s0,-v0,z0,0), with 0<v0<g, s0>k*v0/g and z0>=c*v0/A, use
regular solo3 hazard v0/A. All immediate comparisons are valid: quiet1
has its exact joining value -v0; owner3 is indifferent; quiet2 obeys its
wash guard; and quiet0 has value

    s0>k*v0/g>k*v0/A>zeta0*v0/A.

The final strict comparison holds also for negative zeta0. The exact
successor is affine inverse transport. With r=1-g/A, after n roots

    S_n=1-v0/g+(v0/g)*r^n,
    v_n=v0*r^n/S_n,
    z_n=(z0+h*(1-S_n))/S_n,
    s_n=(s0-k*(1-S_n))/S_n.

Use a final hazard v_n/g once z_n>=c*v_n/g. A finite uniform n suffices since
r^n <= (g*z0+h*v0)/((c+h)*v0) eventually. Its row0 comparison follows from
s_n>k*v_n/g>zeta0*v_n/g. Then V1=V3=0 and V0,V2>0.

The closure equations imply that V and X lie on the same solo3 affine line:

    V=tau*Gamma[:,3]+(1-tau)*X,
    tau=X1/(X1+g).

Indeed they first give this identity through the auxiliary point A°; no
strategy at A° is used. Since a<tau by(5a), a total solo3 mass

    t'=(tau-a)/(1-a)=(V0-A(a)0)/(k-A(a)0) in(0,1)

connects V to the actual start A(a). Subdivide this total mass into finitely
many small hazards. Quiet0 annotations have positive lower bound
min(V0,A(a)0), and quiet2 annotations have positive lower bound
min(V2,A(a)2); choose each hazard q so that q*max(zeta0,0) and q*c lie below
these bounds. Quiet1 annotations are nonnegative and its joining reward
-A is negative. All immediate comparisons on this final arc are exact.
The complete finite period is the solo3 prefix of mass a, the joint02 root,
the finite core, finite wash, and this final3 arc.

Section2 now proves exact terminal Nash and the original uniform payoff
kappa+A(a), using this literal finite period and its joint02 absorption bound.

For a nonempty exact raw test inside the stationary-exclusion family, take
the displayed table except let eta be the following positive rational and
allow p=Z2(12) to be any real number. Select

    b=333/1000, x=9657/101927, C=2997/6670,
    eta=131548508570/14279857169013,
    T=1425691/1478705309, j=691452549/3048494819.

Substitution into the cubic gives zero, and exact calculation gives

    P_eta'(b)=-6704487620023219289/142798571690130000,
    j-A*T/c=2632742502684155023/13523476419942882213>0,
    g*C/k-j=6783134139/30484948190>0,
    k*x*(f+eta)-(h+c)*s*b=1618753742103/3696763272500>0,
    x*(1-b)*Z3(03)+(1-x)*b*v+x*b*Z3(023)
        =-6084062847/203854000<0.

Here 0<eta<1/100. The theorem supplies every real p once K>=M(1+|p|).
For p=0 and sufficiently large K this lies in the completely audited
nonstationary region of Section6. No explicit M is inferred from this raw
asymptotic calculation; Section4 independently proves the concrete K=1000,
eta=1/100 game.


## 4. Exact 75-date construction at the displayed table

Here alpha=1/1000, eta=1/100. The eight unknowns are

    v=(Y0,Z0,w0,Y1,Z1,w1,E0,x).

The symbols Z0,Z1 in this vector are scalar core variables, not reward rows.
For a root (0,alpha*y,alpha*z,w), direct coalition summation gives

    Q1=-z(1-w)-100w+111alpha*z*w,
    Q2=3w-alpha*y*w,
    P1=(alpha/2)z(1-w)-3w(1-alpha*z)+9alpha*z*w,
    P2=-2alpha*y(1-w)-w,
    H1=(1-alpha*z)(1-w), H2=(1-alpha*y)(1-w),
    Q3hat=10y-100z+91alpha*y*z,
    P3hat=-2y+z-5alpha*y*z,
    H3=(1-alpha*y)(1-alpha*z).

Actual row3 values are alpha times the hatted quantities. Indexing subsets
of players1,2,3 by their three-bit mask, row0's passive reward vector is
(0,3,-1,-12,3,2,-6,-8). This and H0=(1-alpha*y)(1-alpha*z)(1-w)
define its passive affine transport exactly.

A subscript 0 or1 on Q,P,H below selects the corresponding core root.
Set E1=(Q1_1-P1_1)/H1_1, E2=(Q2_1-P2_1)/H2_1 and E3=0.
Propagate row0 from E0 backward through both roots to get C0. Define

    C1=Q1_0, C2=Q2_0, C3=alpha*Q3hat_0,
    b=C0/(C0+9/10), a=b/(30+b),
    X1=2x(1-b)+(1-x)b/2+5xb+(1-x)(1-b)C1,
    X3=-x(1-b)+(1-x)b-(219/29)xb+(1-x)(1-b)C3,
    A1=(3X1-3b/10)/(3+b/10),
    A2=[3x(201/100)-b/10]/(3+b/10).

The following eight rational residuals define f(v):

    Q1_0-P1_0-H1_0 Q1_1,
    Q2_0-P2_0-H2_0 Q2_1,
    Q3hat_0-P3hat_0-H3_0 Q3hat_1,
    Q3hat_1-P3hat_1,
    C2-x eta/(1-x), X3,
    A1(3-E0)-3E0-3E1,
    A2(3-E0)-3E2-E0.                               (F)

The first four impose active continuation equalities; the next two impose
the joint02 comparison and its zero row3 value; the last two are (R).

### Rational existence certificate

Take the exact center, with every displayed numerator divided by 10^12,

    v*=(1360668545571,172768406022,344887196,
        585024731948,69546561222,1369093633,
        430955956301,93726145171)/10^12.

Let B be the closed infinity-norm cube of radius r=10^-9 about v*.
Define M as the exact rational inverse of Df(v*): augment that Jacobian
with the identity, choose the first nonzero pivot row at or below each
successive diagonal, divide the pivot row, and eliminate its column from
all other rows. All eight pivots are nonzero.

The following specifies the complete rational verification. Evaluate (F)
and its derivative on B with interval addition, multiplication by the
minimum/maximum of the four endpoint products, and reciprocal
[l,u] -> [1/u,1/l] only when 0 is outside [l,u]. Track derivative intervals
by the product and quotient rules. At v* every interval degenerates to
an exact rational. With J(B) the resulting derivative interval matrix,
compute the sum of absolute endpoint bounds in each row of I-M J(B).
The exact results obey

    max_i sum_j sup |(I-M J(B))_ij| < 3/100000,
    ||M f(v*)||_infinity + r max_i sum_j sup |(I-M J(B))_ij| < r/1000. (I)

All divisions avoid zero. These checks require only the raw table, (F),
the eight rational center coordinates, and the interval rules just given;
there is no floating-point existence premise. The map v -> v-Mf(v) is
therefore a strict contraction carrying B into itself. Its fixed point
is a zero of f, since M is invertible.

The same interval evaluation gives

    0.09372614<x<0.09372615,
    0.32835439<b<0.32835442,
    0.2666973<A1<0.2666976,
    0.1755232<A2<0.1755234.                         (P)

All six core hazards are strictly between zero and one. Both core row0
annotations, E0, A1,A2,X1 are positive. The additional strict checks are

    A2>3a,
    X1> -x(1-b)-1000(1-x)b+6xb,
    x(1-b)-100(1-x)b+(15/2)xb<0.

They prove the quiet comparisons at the solo3 prefix and joint02 root;
row0's prefix Quit offer is -20a<0, and row1's is -100a<0.
At both core roots row0's Quit offer is nonpositive, below its strictly
positive current value. Every other core comparison is an equality in (F).

### All 75 literal dates

Use, in chronological order, solo3 hazard a; joint02 hazards (x,0,b,0);
the two core roots; 50 regular solo3 wash roots; one final wash root;
and 20 subdivided solo3 return roots. Initially A_*=(0,A1,A2,0), after
the prefix X=(-b/10,X1,(201/100)x,0), and after the core E=(E0,E1,E2,0).
In particular the active0 value at the joint date is strictly negative.

For the wash write v=-E1, s=E0, z=E2. Exact interval evaluation certifies

    0<v<3, s>v, z>3v/100.

For R=(97/100)^50 and S=1-v/3+(v/3)R, set

    s50=[s-3(1-S)]/S, v50=vR/S, z50=[z+1-S]/S.

It certifies s50>v50 and z50>v50. Thus the 50 regular hazards v_j/100
and the final hazard v50/3 are legal by Section 2. Their successor V has
V1=V3=0 and V0,V2>0. With t=V0/3 the final exact checks are

    0<t<1, 3t/(20-19t)<min(V2,A2).

The last20 hazards t/(20-jt) are therefore legal and close exactly to A_*.
The number of dates is 1+1+2+50+1+20=75. Section 2 proves the exact terminal
and uniform equilibrium claims without any unspecified large-K threshold.

## 5. Independent perturbations of all 60 rewards

The 56 off-own native entries and the four original own levels are affine
coordinates on the 60 original rewards. Keep alpha=1/1000 as a construction
constant, even when the pair cost changes. Define the same eight residuals
using literal coalition Q,P,H from the perturbed native table. Put
k=Gamma03, beta=-Gamma02 and t0=Z0(02). The joint substitutions are

    b=C0/(C0+t0+beta),
    C2=x[Z2(02)-Gamma20]/(1-x), X0=b*t0,
    a=-X0/(k-X0), X3=0,
    A_*=a Gamma[:,3]+(1-a)X.

The final residuals are A1(k-E0)-kE1+Gamma13 E0 and
A2(k-E0)-kE2+Gamma23 E0. Divide row3 core residuals by the fixed nonzero
alpha. These analytic equations specialize exactly to (F). The invertible
Jacobian in (I) gives nearby exact roots for every sufficiently small reward
perturbation by the implicit function theorem.

All active hazards are proper. Every quiet comparison is strict except the
50 regular-wash row1 comparisons. Those equalities remain identities when
the hazards are defined as v/[-Z1(13)]. The remaining finite set of strict
comparisons persists by continuity. No sign-face condition on every row0
joining reward is needed locally. The same 75-date architecture, the same
opponents-only absorption argument, and the same fixed-profile consumer
therefore apply throughout an open neighborhood in all60 rewards.

## 6. Exact separation from existing raw producers

The comparisons here concern complete stated raw-selector domains and
stationary/sure-first output classes. They do not concern unspecified maximal
neighborhoods of earlier local theorems or arbitrary nonstationary verifiers.
Set kappa=(1,1,1,1), p=0, K>=1000, and 0<eta<=1/100 in the table of Section1.

### Stationary and sure-root selectors, including their limits

Use Q,P,H from Section2 and set

    F_i=(1-H_i)Q_i-P_i,
    L_i=min({-1} union {Z_i(S): nonempty S excludes i}),
    G_i=Q_i-P_i-H_i L_i.

For this table L=(-12,-8,-10,-12). A nonzero stationary Nash profile must
satisfy F_i<=0, =0, or >=0 according as q_i=0, 0<q_i<1, or q_i=1.
AllNever is not original-game Nash since every own singleton is one.

Every actual continuation best-response cap in native coordinates is at
least L_i: the pure-Never response averages passive rewards and the native
value -1 of original AllNever. At a root with a unique sure quitter,
substituting L_i for that quitter's actual continuation only improves its
Quit comparison; every other player's H_i is zero. With two sure quitters
all H_i are zero. Hence the same quiet/mixed/sure sign system for G is a
necessary condition for any sure-quitter full-response Nash root with actual
continuation best-response caps.
It is not restricted to stationary or prescribed finite tails.

Here is a complete rational exclusion algorithm. Replace eta by t/100 with
t in [0,1], and construct F,G by the finite coalition formulas above at
K=1000. Enumerate all80 nonzero patterns in {0,1,*}^4 for F and all65 patterns
containing1 for G. At every fixed t the dependence on K is

    F1(K)=F1(1000)-(K-1000)(1-H1)(1-q0)q2(1-q3),
    G1(K)=G1(1000)-(K-1000)(1-q0)q2(1-q3).

If q2=0, q0=1, or q3=1, retain all baseline signs. Otherwise replace the
row1 sign by its baseline >=0 when mixed or sure, and omit it when quiet.
These are weaker necessary conditions, uniformly for every K>=1000.

For F, directly discard patterns with q0=0, player2 mixed and q1 or q3
positive: Q2=q3(3-q1)>=0 whereas P2=-2q1-q3+2q1q3<0, so F2>0.
A single mixed owner j with no sure owner is excluded by a quiet recipient
with Gamma_ij<min(0,Z_i(ij)); choose i=3,2,0,2 for j=0,1,2,3 respectively.
Indeed its F_i=q_j[q_j Z_i(ij)-Gamma_ij]>0. The relaxed row1 is not used.

For each remaining pattern with at least two mixed coordinates S, set
A=Gamma_SS and V=A^-1; all these matrices are invertible. Add the V linear
combinations of the mixed baseline polynomials. Their signs are equality
unless row1 was relaxed: a combination then has sign >=0, <=0, or =0
according to its coefficient of row1.

For patterns without a sure owner, the mixed vector is -Aq+R(q,t), where
every term of R has total degree at least two in the player variables.
If row1 is relaxed, the remaining relevant inverse columns V[:,1] are
nonnegative, giving q<=VR; otherwise q=VR. If c_i is the sum of absolute
coefficients of R_i, including its powers of t, put D=max_i sum_j |V_ij|c_j.
Since t in[0,1], a nonzero solution must have ||q||_infinity>=1/D.
The exact constants and excluded closed origin cubes are

| S | D | E with 2^-E<1/D |
|---|---:|---:|
|01|1/2|1|
|02|201/200|1|
|03|20/3|3|
|13|100/3|6|
|012|137092/25|13|
|013|1695|11|
|023|6853381/7250|10|
|0123|788325063/25375|15|

The other no-sure mixed sets12,23,123 were directly discarded. The cube
[0,2^-E]^S contains no nonzero solution of its necessary system.

After substituting fixed player coordinates, all polynomials have degree
at most two in each remaining player variable and in t. For
p(x)=sum_m a_m x^m in d variables, use tensor degree-two Bernstein coefficients

    b_k=sum_(m<=k) a_m product_i binom(k_i,m_i)/binom(2,m_i),
    k in {0,1,2}^d.

Clear a common positive denominator. Discard a box if an equality's
coefficients have one strict sign or an inequality's coefficients all have
its forbidden strict sign. Also discard boxes inside the excluded origin
cube. Otherwise bisect the mixed player coordinate subdivided least often,
resolving ties by player index, and process the left child first. The interval
for t stays [0,1]; if there are no mixed players, subdivide t instead.
The integer-scaled one-coordinate subdivision is

    (a,b,c) -> left(4a,2(a+b),a+2b+c),
                right(a+2b+c,2(b+c),4c).

A direct exclusion counts as one node. The fully specified calculation
terminates with700 nodes for all80 stationary patterns and205 nodes for
all65 sure-root patterns. There are no surviving boxes. The same calculation
also includes eta=0. No numerical optimizer or external payload is a premise.

For each fixed table there is also a positive stationary regret floor.
Otherwise a convergent subsequence of stationary hazards with regret tending
to zero has either a nonzero limit satisfying the excluded F signs, or
hazards tending to zero. In the latter case normalize q by sum_i q_i and
pass to x>=0, sum x_i=1. Immediate quitting gives Gamma x>=0. If x_i>0
and some opponent has positive x, comparison with Never gives
x_i(Gamma x)_i=0: its limiting native payoff is (Gamma x)_i/(1-x_i),
versus the prescribed (Gamma x)_i. A singleton support violates Gamma x>=0
because every column has a negative entry. Any larger support S would
satisfy Gamma_SS x_S=0, impossible since every principal matrix is invertible.
Thus stationary approximation cannot hide at vanishing hazard. The entire
stationary and sure-first output classes are excluded, including weighted
collision producers and sure-root punishment-tail selections.

### All choices in the other raw sufficient criteria

The eight singleton signs beta,d,e,f,k,h,g,d1>0 permit only the identity
among all24 player labelings of this matrix. Its previous solo0/singleton2
return requires Z2(02)<=Gamma20; here the excess is eta>0. The fully diffuse
version requires B1>0, whereas its outer equations give B1=-1/9. The
alternative negative-pair singleton template additionally requires
Gamma10<0, whereas Gamma10=2. These failures survive positive recipient
scaling. The fixed signed/premium families with Gamma12=1 fail at1/2;
Gamma10=2 and Gamma13=-3 pin that row's scaling.

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


## 7. Source correspondence and formalization boundary

All strategies, roots, continuation values and return steps are produced.
The raw tests in Section1 and the rational certificate in Section4 require
no supplied equilibrium or successful strategic continuation.

The full root recursion agrees with
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`). The direct
consumer of the constructed exact terminal Nash profile is
`quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`),
which retains one profile at every positive uniform accuracy and its actual
terminal payoff as the fixed target. These are source correspondences;
the new raw producer and numerical-rational certificate are ordinary
mathematics, not Lean-checked declarations.

Formalization should retain the literal period, with no padding at the
negative active0 value. The hypotheses of a compiler requiring a singleton
floor at every block are not supplied. The new obligations are the finite
raw-return producer, exact rational interval calculations, finite wash and
root comparisons, and periodic realization; their full semantic consumer is
proved directly in Section2. No conclusion is asserted for arbitrary Fin4,
for every table satisfying only the singleton sign pattern, or for the
unrestricted positive-gap counterexample question.
