# Uniform equilibria for every nonnegative premium ratio

This packet proves uniform equilibrium for all nonnegative premium ratios
when K is sufficiently large, and on an explicit outer cone including bounded K. It is ordinary mathematics,
not checked in Lean. Arbitrary signed Fin4 remains open.

## 1. Raw theorem

There are four players0,1,2,3, independently choosing Continue or Quit at
each live date. The first nonempty quitting coalition D absorbs and pays
r(D). Live play and AllNever pay0. Put kappa_i=r_i({i}) and
Z_i(D)=r_i(D)-kappa_i for nonempty D only. Native own-singletons are0.
Fix the table

```
D       Z0     Z1     Z2     Z3
0        0      2      2     -1
1        3      0     -2     -2
2       -1      1      0      1
3        3     -3     -1      0
12     -12     -K      p     -6
13       2   -100     -1      0
23      -6      9      3   -100
123     -8     11      2      1
```

All seven row0 rewards on nonsingleton coalitions containing0 are <=0;
the other21 entries on those coalitions and all four original own levels
are arbitrary independently.

**Theorem.** There is one finite C>=100 such that every game
in this family has a uniform-equilibrium payoff in either raw region

    K>=C, p>=0;
    K>=0, p>=max(1,2K).

The target is fixed before accuracy and all unilateral behavioral
replacements are allowed. No numerical C and no coefficient-perturbation
extension are asserted. The second region is explicit and includes bounded K.

For the first region, beta=p/K lies in[0,1/1650], [3/5000,3/50],
[3/50,2], or[2,infinity). These closed ranges overlap and exhaust allbeta>=0.
The first uses a hybrid backward construction with supports12,23,123; the
second uses a finite saddle core; the third uses one pure3 root; the last
is included in the explicit outer region. The hybrid proof includesbeta0
uniformly and crosses the equal-modulus resonance without a spectral
assumption. Arbitrary signed Fin4 remains open.

## 2. Common exact equations and pair entrance

Put alpha=1/K and beta=p/K when K>0. At a triple123 root with physical
hazards(0,alpha Y,alpha Z,w), the active current and required successor
values are(Q1,Q2,alpha q3) and(F1,F2,alpha f3):

```
Q1=-Z-100w+(1+111alpha)Zw,
Q2=beta Y+3w-(beta+alpha)Yw,
q3=-Z(100-101alpha Y),
F1=[-(1+alpha)Z-97w+(1+100alpha)Zw]/[(1-alpha Z)(1-w)],
F2=[(beta+2alpha)Y+4w-(beta+3alpha)Yw]/[(1-alpha Y)(1-w)],
f3=[2Y-101Z+106alpha YZ]/[(1-alpha Y)(1-alpha Z)].
```

The final successor has third coordinate0 exactly when
Y_last=101Z_last/(2+106alpha Z_last). The first and second interface
equations are F1=nextQ1,F2=nextQ2; the third is f3=nextq3.

A core entrance is T=(T0,-L,X,T3), with L,X>0. Prefix it by pair12 roots.
For p>0,K>0, put c0=X/p,d0=L/K and

    c_n=c_(n-1)/(1+2/p+c_(n-1)),
    d_n=d_(n-1)/(1+1/K+d_(n-1)).

The actual word(c_n,d_n),...,(c1,d1) has current/successor active values
(-Kd,pc) and(-(K+1)d/(1-d),(p+2)c/(1-c)), so its active comparisons
are exact. Its limiting entrance is C=(C0,0,0,C3), where

```
S=2/[(2+X)(1+L)], chi=S L X/(2K+2+p),
pi1=(p chi+S X)/2, pi2=K chi+S L,
C0=3pi1-pi2-12chi+S T0,
C3=-2pi1+pi2-6chi+S T3.
```

For a finite n-prefix put A=pc_n,B=Kd_n. Its exact masses are

```
S_n=(2+A)(1+B)/[(2+X)(1+L)],
chi_n=(S_n L X-A B)/(2K+2+p),
pi1_n=(p chi_n+S_n X-A)/2,
pi2_n=K chi_n+S_n L-B.
```

At p=0 and X=0 take c_n=0 and use only the d recurrence; the same mass
formulas hold with A=0. This is the pureplayer2 prefix. In the hybrid
construction its first pair12 root is included in the finite core if needed,
so all later p=0 prefix roots have X=0.

The mass formulas follow from active payoff identities and total probability,
and converge to the displayed limits. The actual quiet values are
U0=3pi1_n-pi2_n-12chi_n+S_n T0 and
U3=-2pi1_n+pi2_n-6chi_n+S_n T3.

U0 is bilinear in(A,B). On the full rectangle[0,X]x[0,L] its four corner
values are C0,C0(2+X)/2-3X/2,C0(1+L)+L,T0. Positivity of these four
numbers proves every row0 prefix comparison, because row0's Quit offers
are nonpositive by the raw caps.

For p>0,K>0, player3's pair Quit value is Q3(c,d)=-100d+101cd. Its exact
surplus recurrence is

```
e_n=(1-c_n)(1-d_n)e_(n-1)+R_n,
R_n=(1-100/K)d_n-2c_n+D c_n d_n,
D=95+201/K+202/p+202/(pK).
```

The starting formal surplus is e0=T3-Q3(c0,d0); it need not be zero unless
the core starts at w=0. The different producers below prove every e_n>=0.

Define the outer quantities from C and the final successor E=(E0,-x,E2,0):

```
b=C0/(1+C0), B1=b, B3=(C0+C3)/(1+C0),
a=B3/(1+B3), A1=2a+(1-a)b, A2=2a.
```

The two return equations are

    A1(3-E0)=3(E0-x), A2(3-E0)=3E2+E0.             (2.1)

Section9 gives the full behavioral consumer once the core and prefix
comparisons, returns, and wash guard E2>=3x/100 are produced.

## 3. One outer-root lemma for every pure3 construction

Take one pure3 core w=L/100, with current T=(T0,-L,X,0), X=3L/100.
Its successor satisfies x=97w/(1-w),E2=4w/(1-w), and
T0=3w+(1-w)E0. These are exact quiet indifferences for players1,2 and
indifference for player3. Its two outer returns become

    A1(3-T0)=3(T0-L), A2(3-T0)=3X+T0.              (3.1)

Suppose the limiting pair coordinates have form

```
C0=S[T0-L+3X/2+a L X], C3=S[L-X+b L X],
S=2/[(2+X)(1+L)], X=3L/100,
-7/2<=a<=3/2, -7/3<=b<=1/2.
```

Here a,b are coefficient parameters only, unrelated to outer solo hazards.
For EVERY pair in this full rectangle, (3.1) has a unique root with

    33/50<L<7/10, 1<T0<5/4,

and the two-variable Jacobian is nonsingular. The following finite exact
polynomial certificate proves this claim.

Set T=T0. Multiply the two cleared return equations by the common positive
denominator (L+1)(3L+200). The resulting polynomials are

```
f1=36L^3 a+18L^3 b+9L^3-54L^2 T a-30L^2 T b-9L^2 T
   +54L^2 a+36L^2 b+45L^2+1340LT+45L-1800T^2+1200T,
f2=-(108L^3 a+54L^3 b+27L^3+2400L^2 T a+1800L^2 T b
     +300L^2 T-3600L^2 a-3600L^2 b+135L^2+5700LT
     +80000T^2-100000T)/100.
```

Their combination f1-9f2/4 is linear in T. Its coefficient is a positive
multiple of

    d=42L^2 b-9L^2+5873L-4200<0

throughout the box. Its zero is Tsol=N/(100d), where

    N=-9L[1708L^2 a+854L^2 b+427L^2-1200La-2000Lb+2135L+2000].

Substitution into f2 gives a nonzero prefactor times the quartic

```
Q=35868L^4 ab-7686L^4 a+26460L^4 b^2-1092L^4 b-981L^4
 -25200L^3 ab+645046L^3 a-33600L^3 b^2+1542762L^3 b-458857L^3
 -961800L^2 a-662200L^2 b-1874690L^2
 +360000La-240000Lb-696500L+1500000.
```

The nonconstant numerator prefactor is
9L(12L^2 a+6L^2 b+3L^2+15L+1400), which is strictly positive.
The following exact tensor-Bernstein bounds hold on the indicated full boxes:

| Polynomial | Box or fixed endpoint | Bound sufficient for its sign |
|---|---|---:|
|Q|L=33/50, full a,b box|>=7720523937/125000>0|
|Q|L=7/10, full a,b box|<=-9337931/200<0|
|Q_L|full L,a,b box|<=-38440944739/12500<0|
|f2 at T=1|full L,a,b box|>=11844461/100000>0|
|f2 at T=5/4|full L,a,b box|<=-268792821/6250000<0|
|N-100d|L=33/50, full a,b box|>=193868991/125000>0|
|N-(5/4)100d|L=7/10, full a,b box|<=-4917521/500<0|

For completeness the exact certificate rule is this. Substitute each interval
coordinate as lower+(upper-lower)t, expand into monomials sum c_m t^m, and
use its actual coordinate degrees d_i. The tensor Bernstein coefficient at
k is sum_(m<=k)c_m product_i binom(k_i,m_i)/binom(d_i,m_i). Every coefficient
lies between the displayed relevant lower/upper bound. This is a finite
rational calculation on the explicitly supplied polynomials; no subdivision
or floating-point premise is used.

For every L the downward-opening quadratic f2 has one simple larger root
T_+(L) in(1,5/4), continuously in L,a,b. The endpoint Tsol inequalities and
d<0 show that f1(T_+(L)) has opposite signs at L=33/50 and7/10. Thus a common
root exists. Every common root in the stated box satisfies Q=0; strict Q_L
makes it unique. The positive prefactor, f2_T<0 at its larger root, and
Q_L!=0 prove that its outer Jacobian is nonsingular. Thus it depends smoothly
on a,b and all margins are uniform on their compact rectangle.

Every required strict guard follows directly from the box. C0 is positive:
its bracket is at least T-L+3X/2-(7/2)LX>.27. Since S>2/(2.021*1.7),
C0> .15 and C0(2+X)/2-3X/2>0. Also0<C3<1: its bracket lies between
L[.97-(7/3)X]>0 and L[.97+X/2]<L. The remaining two row0 rectangle
corners are positive. Finally

```
(1-w)(E0-x)=T0-L>0,
(1-w)(3-x)=3-L>0,
h=(E0-x)/(3-x)=(T0-L)/(3-L) in(0,1),
E2-3x/100=(109/100)w/(1-w)>0.
```

## 4. Pure3 branches and all their finite prefixes

### 4.1. Explicit outer cone, including K=0

Assume K>=0,p>=max(1,2K). Put
q=K/(2K+2+p), v=1/(2K+2+p), r=p/(2K+2+p)=1-2q-2v.
The exact pair entrance at a pure3 core has the coefficient form of Section3
with a=3r/2-q-12v=3/2-4q-15v and b=q-r-6v=3q-1-4v.
The raw constraints imply a in[-7/2,3/2] and b in[-7/3,1/2]. Thus Section3
produces an exact outer return for every such raw game.

For K>0 the actual pair points(A,B) lie in
0<=A<=X, 0<=B<=(L/X)A. Indeed

    A/X=2s/[(2+X)-Xs], B/L=t/[(1+L)-Lt],
    s=(1+2/p)^(-n), t=(1+1/K)^(-n).

Here p>=2K gives s>=t, and2L>=X gives the first fraction at s=t no smaller
than the second. Row0 is already priced by Section3's full rectangle.

Write lambda=C3/2,V=(K-p-6)/(2K+2+p), H=101/(pK). Exact substitution gives

    U3-Q3=lambda(2+A)(1+B)+A-(1-100/K)B-(V+H)AB.

It is affine in B. At B=0 it is positive. At B=(L/X)A, with A=sX,
its quadratic Bernstein coefficients are

    C3,
    C3+[(lambda+1)X+(C3-1+100/K)L]/2,
    (L/K)(100-101X/p).

The first is positive. The second is at least C3-(1-C3)L/2>0:
from Section3, C3>=S L[.97-(7/3)X]>.34, whereas L<.7, so the lower bound
exceeds .34-.66*.35>0. The last is positive since p>=1 and X<.021.
Thus every finite prefix prices player3. No limit word is used as a strategy.

At K=0 use d1=L/(1+L), d_(n+1)=K d_n/(K+1+K d_n), so d_n=0 for n>=2.
The c recursion is unchanged because p>=1. Every finite prefix, its payoff,
and all quiet comparisons are continuous as K decreases to0, using these
non-singular recursions. The exact pair-limit formula is continuous too,
and the same finite-mass identities prove convergence. This includes K=0.

### 4.2. Moderate ratios, uniformly for large K

Assume beta in[3/50,2] and alpha=1/K sufficiently small. The same exact
coefficient form has

    a=(3beta/2-1-12alpha)/(2+beta+2alpha),
    b=(1-beta-6alpha)/(2+beta+2alpha).

These lie in Section3's rectangle for small alpha. Its root therefore exists
without a new outer shooting argument. All strict core and row0 guards hold
uniformly. It remains to price row3 for every finite prefix.

For beta in[11/100,2], the exact pair formulas and
(1+2/p)^(-n)<=(1+1/K)^(-n) give

    c_n/d_n <=[3/(100beta)](1+L)<21/44<1/2.

For small alpha this is at most(1-100alpha)/2, so each R_n>=0. Also
 e0=100d0-101c0d0>0.

For beta in[3/50,11/100], the c_n/d_n ratios decrease because
2/p-1/K+c_n-d_n>=alpha(200/11-1-L)>0. Their fourth ratio is at most
(1-100alpha)/2 uniformly for small alpha. At alpha=0 it is3/(100beta),
strictly below1/2 except at beta=3/50. At that endpoint its alpha derivative
is2(1+L/2-100/3)<-63, while the comparison's derivative is-50. Use this
strict derivative in a fixed endpoint neighborhood and the strictly positive
zeroth-order margin on the remaining compact beta interval.

For n=0,1,2,3, direct expansion of the exact finite-prefix surplus gives

    e_n/alpha ->100L+n(L-2X/beta)>=100L>0.

Thus these finitely many initial surpluses are positive for small alpha.
The recurrence and nonnegative R_n for n>=4 prove every later comparison.
This proves the whole interval including beta=3/50.

The endpoint3/50 is sharp for this limiting pure3 architecture: the limiting
pair-clock row3 payoff starts at0 and has derivative L-2X/beta=L(1-3/(50beta)).
If beta<3/50 this is negative, while the pair Quit offer is O(alpha). A fixed
small positive pair-clock time therefore violates its quiet comparison for
sufficiently small alpha. This is an architecture obstruction, not a UE
counterexample.

## 5. The middle-ratio center return and its positive connection

First construct the center return for every0<beta<=3/50. The positive
connection below will use the smaller interval I=[3/5000,3/50]. At alpha=0 put
L=Z(1-w)+100w, X=beta Y(1-w)+3w. The active equations imply along every core

    L=3w+(1-w)L_next, X=-w+(1-w)X_next.

Hence(L-3)/(X+1) is exactly invariant. Its fixed-line coordinate is

    J=(L+3X)/[1+X+(beta/2)(3-L)].                   (5.1)

At the fixed line(Z,Y,w)=(J,J/2,0), L=J and X=beta J/2.
For an infinite core approaching this line at its entrance, let S_core be
its total solo3 survival. Then

    J=3(1-S_core)+S_core x,
    beta J/2=-(1-S_core)+S_core E2,
    T0=3(1-S_core)+S_core E0.

The outer returns reduce, independently of core phase, to

    A1(3-T0)=3(T0-J), A2(3-T0)=3beta J/2+T0.        (5.2)

The pair limit uses alpha=0,L=J,X=beta J/2,T3=0. Clearing its two equations
and eliminating T0 yields the quartic

```
P(J,beta)=170J^4 beta^4+22J^4 beta^3-48J^4 beta^2
 +475J^3 beta^4+1432J^3 beta^3+1220J^3 beta^2+512J^3 beta
 +305J^2 beta^4+2119J^2 beta^3+4290J^2 beta^2+3184J^2 beta+1280J^2
 +655J beta^3+2564J beta^2+2828J beta+640J
 -300beta^2-1200beta-1200.
```

It has exactly one root J(beta) in[17/25,3/4] for every beta in[0,3/50].
P_J is strictly positive there: group its coefficients by powers of beta;
only its beta^2 coefficient has a negative term, and
-192J^3+3660J^2+8580J+2564>0 on this interval. Also

    P(3/4,beta)=3beta(18165beta^3+97889beta^2+193520beta+124928)/128>0

for beta>0. P(17/25,beta) has positive nonconstant beta coefficients, and
its value at beta=3/50 is -4261958051213/244140625000<0. At beta=0 the root
is J=3/4.

For clarity the two cleared polynomials, with T=T0, are

```
f1=15J^3 beta^2-20J^2 T beta^2+2J^2 T beta+30J^2 beta^2+24J^2 beta
 -20JT beta^2-12JT beta+56JT+15J beta^2+30J beta
 -36T^2 beta-72T^2+24T beta+48T,
f2=-15J^3 beta^3-14J^2 T beta^2-15J^2 beta^3-18J^2 beta^2
 -38JT beta^2-76JT beta-32T^2 beta-64T^2+40T beta+80T.
```

Their resultant in T is
48J beta(beta+2)(5J^2 beta^2+5J beta^2+10J beta+28beta+56)P.
Thus the only zero factor on the selected rectangle is P.

The second cleared return equation is a downward quadratic in T0. Its
larger root lies in(1,5/4), its smaller root in(0,1/100) for every
0<beta<=3/50.
Direct endpoint substitution using J in[.68,.75], beta<=.06 proves these
bounds. The first cleared return polynomial is positive for0<=T0<=.01:
its constant is positive and its linear coefficient exceeds85, whereas the
negative quadratic term is at most36(beta+2)T0^2. Thus the common root
selected by P is the larger root. As in Section3, the simple resultant root
and simple quadratic root prove the outer Jacobian nonsingular. Denote the
unique smooth root by(J_*(beta),T_*(beta)).

All outer guards are strict. In the pair formula,
C0=S[T0-J+3X/2+((3beta/2-1)/(2+beta))JX]>0,
C3=S[J-X+((1-beta)/(2+beta))JX] lies in(0,1), and the row0 rectangle corners
are positive. These bounds follow from J in[.68,.75],T0>1 and X<=.0225.
The core identities give E0>x,0<x<3 and
h=(E0-x)/(3-x)=(T0-J)/(3-J) in(0,1).

Here is an explicit positive core connection for every selected J, and also
for a compact neighboring J interval. Put

```
u=w/(1-w), e=Y-Z/2, d0=1+3beta/2,
P0=[109-4J+(97/2)beta J]/d0, Q0=beta(3-J)/d0.
```

Equation(5.1) is equivalent to Z=J-P0u-Q0e. The exact alpha=0 forward map is

```
D=100-J+(P0-97)u+Q0e,
u_next=(97u+e/50)/D,
e_next=(P0/Q0)(u-u_next)+(1+1/(50Q0))e.
```

The physical region before the last root is u>0,e>0,Z>0,e<50Z.
The identities

```
P0-97=(3-J)(8-97beta)/(2d0)>0,
(Q0+1/50)(100-J)-P0/50
    =(3-J)[beta(101-J)-3/50]/d0>0
```

hold throughout I and J in a small neighborhood of[.68,.75]. They show
that the numerator of e_next is a polynomial with positive coefficients
in u,e. Both coordinates are positive until the terminal surface e=50Z.
The map has positive partial derivatives on the physical triangle:
0<partial_u u_next<97/(100-J)<1,
partial_e u_next=1/(50D)-Q0(97u+e/50)/D^2>0,
partial_u e_next=(P0/Q0)(1-partial_u u_next)>0,
and partial_e e_next>=((Q0+1/50)-P0/[50(100-J)])/Q0>0.
For the remaining strict inequality use u<=J/P0<.008,e<=50J<38,
Q0<.17 and the displayed positive denominator; its numerator is at least
(100-J)/50-97Q0u>1.8.

At the fixed line the forward normal eigenvalues are d>1 and k in(-1,1),
uniformly on the compact parameter set. This follows either from the exact
2x2 derivative above or from its trace and determinant:

    d+k=[9900-50J-3/beta]/[50(100-J)],
    dk=[9797/2-4/beta]/[50(100-J)].

The characteristic polynomial at1 is
-(1+3beta/2)/[50beta(100-J)]<0, so one eigenvalue exceeds1 and the other
is below1. The characteristic polynomial at-1 is positive on I: its numerator is
19798.5-100J-7/beta>=48341/6>0. Thus the
other exceeds-1. Positive derivatives give a strictly positive unstable
eigenvector. A local unstable graph is constructed in Section6; its positive
branch extends by the displayed map, with a strictly positive tangent.

Let R=P0u+Q0e=J-Z. Exactly R_next=R+e/50. Any positive orbit which failed
to reach e=50Z would have increasing bounded R, hence e->0 and
u->R_infty/P0>0. But at e=0 its limiting update is
u_next=97u/[100-J+(P0-97)u]<u, a contradiction. Thus the positive unstable
curve reaches the terminal equation e=50Z. Along that curve u,e both increase
with its scalar parameter, so J-P0u-(Q0+1/50)e crosses0 strictly. This gives
one transverse terminal point with u,e,Z positive. Compactness gives uniform
finite connections from one small local section to these terminal points.

At the terminal point Y=101Z/2 and the wash margin is

    E2-3x/100=(101beta/2-3/100)Z+(109/100)u>0,

because beta>=3/5000>3/5050. The entire limiting connection is strictly
physical. Its row0 annotations are positive since the terminal E0>x>0 and
all its backward row0 updates are convex combinations with singleton payoff3.

## 6. Uniform finite shooting through the middle saddle

For the normal eigenvalues write d=1/delta>1 and k in(-1,1); k may be0.
The physical particular shift, computed by differentiating the exact core
map at the fixed line, is

    h_w=-B, B=J[4-beta(J+2)]/[2(3beta+2)]>0,
    h_e=-5J[20J^2 beta-77J beta-118J+320]/[4(3beta+2)].

Normalize both normal eigenvectors to have physical w coordinate1. Their
e coordinates are E_u=50(100-J)d-4850 and E_s=50(100-J)k-4850.
The next construction supplies actual finite core roots; no strategic
continuation is assumed.

### 6.1. Local coordinates

Work on one compact (beta,J) rectangle on which the alpha=0 FORWARD core map
has the exact invariant J supplied by its rational formula. Its fixed line
has two simple normal eigenvalues

    d=1/delta>1, k=1/kappa in(-1,1),

uniformly separated from the unit circle. Use k as the parameter at the
backward-map pole: it is smooth and may equal zero. No stable inverse is
used. Normalize each normal eigenvector to physical w coordinate one.

Section5 supplies a positive unstable branch meeting f3=0 at one transverse,
strictly physical point, smoothly in(beta,J), with its finite connection
from a small local section strictly physical. Compactness permits one fixed number m of
forward steps between the local terminal section and the terminal equation.
The pullback of that terminal equation is a smooth graph x=Xi(J,y,alpha),
where Xi(J,0,0)=xi(J)>0 is small. This follows by finite-dimensional IFT
from the proved transverse crossing, not from invertibility of the full
forward map. The normal unstable derivative is nonzero even when k=0.

For clarity here is the local normal-form construction. On each J fiber,
write the normal derivative diag(d,k). The ordinary graph transform takes
small graphs y=h(x) forward: the x-coordinate has derivative d+O(epsilon)>1
and is invertible on the local interval, while its normal graph derivative
contracts by |k|+O(epsilon)<1. The differentiated graph transforms contract
as well, with leading factors |k|/d and |k|/d^2. Hence one obtains a C3
unstable graph, uniformly on a smaller neighborhood and in parameters.
Subtract that graph. The scalar map on it has inverse g(x)=delta x+O(x^2).
The sequence delta^(-j) g^j(x) converges in C3 on a smaller neighborhood:
choose q>delta with q^2<delta locally in parameter space; successive
normalized differences are bounded by a polynomial in j times
(q^2/delta)^j. A finite parameter cover gives common bounds. This scalar
coordinate linearizes the forward map on the unstable graph exactly.

In the resulting coordinates (s,x,y), alpha=0 has s'=s, x'=d(s)x on y=0,
and y'=0 on y=0. The off-diagonal linear normal terms vanish at x=y=0.
For alpha small, shift the two normal coordinates by alpha h(s), where

    (I-diag(d,k))h = partial_alpha(normal map)(s,0,0,0).

This is legitimate because d!=1 and k!=1. Changing s by O(alpha) changes
alpha h(s) only by O(alpha^2). The exact shifted equations consequently
have the uniform form

    s' = s+alpha g(s,x,y,alpha),
    x' = d(s)x + R_x,
    y' = a(s,x)y + R_y,

with |a|<=k0<1 and, on the chosen small tube,

    |R_x|<=C(|x y|+y^2+alpha|x|+alpha|y|+alpha^2),
    |R_y|<=C(y^2+alpha|x|+alpha|y|+alpha^2).

The same structural estimates hold for differentiated coefficients. The
shifted physical coordinates are

    w=x+y-alpha B+O((|x|+|y|+alpha)^2),
    e=E_u x+E_s y+alpha h_e+O((|x|+|y|+alpha)^2),
    E_u=50(100-J)d-4850, E_s=50(100-J)k-4850.

Here B,h_e are the explicitly computed particular shift in the displayed
formulas. These local changes retain the eigenvector normalization at the
fixed line; nonlinear linearization changes only the quadratic remainder.

### 6.2. Mixed finite boundary problem

Let n=N-1-m. Fix s_0=J and prescribe

    y_0=alpha(B-r),   alpha=delta(J)^(N-1) Lambda,

where r and Lambda range over fixed compact positive intervals. For any
trial x-array in a small fixed cube, solve (s_j,y_j) FORWARDS using the exact
equations. Since n alpha tends to zero, these recursions remain in their
domains and give

    |s_j-J|<=C j alpha, |y_j|<=C alpha,
    ||D_x s||<=C n alpha, ||D_x y||<=C alpha.

For the last derivative bounds, the stable variation has ratio <=k0<1;
its forcing from x is O(alpha) because y=O(alpha). The center variation
is a sum of n terms O(alpha). Discrete Gronwall introduces only a bounded
factor exp(C n alpha). These bounds include arbitrary trial x-arrays in
the small cube, not merely a proposed solution.

Solve the x equation backwards as a scalar equation,

    x_j=psi(s_j,y_j,x_(j+1),alpha).

Its derivative in x_(j+1) is at most delta1<1 after shrinking the tube.
Its other derivatives are bounded. Define a map on the x-array by this
formula for j<n, using the trial x_(j+1), and by

    x_n(new)=Xi(s_n,y_n,alpha)

at the last index. The forward dependence through s,y contributes at most
C n alpha to the derivative. The complete sup-norm Lipschitz constant is
therefore at most delta1+C n alpha<1. The terminal row has derivative at
most C n alpha. A fixed small cube is invariant: its backward rows contract
strictly and its terminal row lies strictly inside the cube. Banach gives a
unique exact finite orbit near the reference connection. This construction
never iterates an unstable backward fast mode.

Its parameter derivatives exist and are uniform by differentiating the
contraction equation. Factors polynomial in N can arise from differentiating
delta(J)^(N-1); exponential smallness absorbs them.

### 6.3. Scaled entrance estimate

An unweighted O(N alpha) orbit bound alone is insufficient. The following
Green estimate gives the required division by t=delta(J)^(N-1).

The exact backward scalar equation along the solution has

    x_j=delta(J)x_(j+1)+eta_j,
    |eta_j|<=C alpha(j+1)|x_(j+1)|+C alpha^2,
    x_n=xi(J)+O(n alpha).

The terms x y and alpha x are included in the first bound; y^2 and alpha y
are O(alpha^2). The center variation contributes j alpha times x.
Iterating this inequality gives

    |x_j|<=C delta(J)^(n-j) exp(C n^2 alpha)+C alpha^2.

Unrolling the signed error at j=0 then gives

    x_0=delta(J)^n xi(J)
           +O(n^2 alpha delta(J)^n+alpha^2).

Because alpha=t Lambda and m is fixed,

    x_0/t = A(J,beta)+o(1), A=delta(J)^(-m)xi(J)>0.

The same conclusion holds in C1 in J,beta,r,Lambda. Differentiate the exact
Green sums; the factors j and n produced by differentiation are bounded by
one fixed polynomial in N, and their products with t tend to zero uniformly.
Thus the final normalized error is O(poly(N)t), not an uncontrolled error
O(N alpha)/t.

Using the exact y_0 and the physical-coordinate expansion yields

    w_0/t = A-Lambda r+o_C1(1).

Consequently w_0=0 selects Lambda=A/r+o_C1(1), because Section5 gives a uniformly nonsingular limiting outer root. Those outer
equations can be included in the same finite-dimensional IFT. Along the
selected branch, for every fixed j,

    w_j/alpha -> -B+r d^j+(B-r)k^j,
    e_0/alpha -> h_e+r E_u+(B-r)E_s

in C1. This gives the accuracy needed to insert e_0/alpha into the exact
first-pair surplus divided by alpha^2.

All complete finite core sums/products used in row0 transport differ from
the alpha=0 connection by O(poly(N)alpha). Indeed center drift is O(N alpha),
y is O(alpha), and the weighted x estimate controls the unstable part;
summing over N roots adds only a polynomial factor. The finitely many
nonlocal terminal roots have ordinary smooth dependence. Sections2 and5 supply the exact pair limit and the limiting outer returns.

### 6.4. Physical signs and first-prefix boundary

Let

    r_min=B(1-k)/(d-k), r_max=d r_min.

The first scaled next-root hazard is

    w_1/alpha -> (d-k)(r-r_min).

For j>=1 the leading expression increases with r because d^j-k^j>0.
At r=r_min it vanishes for j=1, while its successive differences are

    B(d-1)(1-k)(d^j-k^j)/(d-k)>0, j>=1.

Hence every fixed j>=2 has a strictly positive uniform scaled margin on
[r_min,r_max]. To cover all j rather than only each fixed j, choose one
large fixed j0. The Green estimate gives x_j>=c alpha d^j in the local
tube, while stable iteration gives

    |y_j|<=C alpha k0^j+C alpha|x_j|+C alpha^2.

Thus for j>=j0, w_j>=x_j/2-C alpha>0 until the orbit leaves the tube.
The final fixed number of connection roots have strict physical margins by
hypothesis. This proves positivity for the whole arbitrarily long core.
The only movable core boundary is w_1=0; all Y,Z stay positive by
Section5's strictly interior connection and the positive fixed-line coordinates.

By the exact algebra in Section7, the first pair-prefix quiet3 surplus obeys

    surplus_1/alpha^2
      ->2 C(d-k)(r_max-r), C=50(100-J)>0.

This conclusion needs only the C1 limit of e_0/alpha above, because the
surplus formula itself is exact. The two transverse boundary equations
therefore select r_N^- near r_min and r_N^+ near r_max. Section7's exact
pair recurrence, rather than a stronger unnecessary ratio bound, must be
used to propagate this first surplus to every finite prefix length.


## 7. First-prefix guard, exact entrance gluing, and coverage

At the first core root w0=0, so L=Z0,X=beta Y0 and
T3=-alpha Z0(100-101alpha Y0)=Q3(alpha Y0,alpha Z0). Thus e0=0 for the
canonical pair prefix. Let E=(Y0-Z0/2)/alpha. Exact substitution in the first
prefix root gives the uniform expansion

    e1/alpha^2 -> -2E+47J^2-101J+2J/beta.

Inserting Section6's C1 limit E=h_e+r E_u+(B-r)E_s gives

    e1/alpha^2 ->2C0n(d-k)(r_max-r),
    C0n=50(100-J), r_min=B(1-k)/(d-k), r_max=d r_min.

Here C0n is a normal-matrix constant, not the payoff coordinate C0. To verify
the equality exactly, use

    C0n(d+k-dk)=10003/2-50J+1/beta,
    -h_e+(47J^2-101J+2J/beta)/2
        =B(303/2-50J+1/beta).

The first is the trace/determinant identity of Section5; the second follows
by substituting the displayed rational B,h_e. No approximate equality is
used to join phase boundaries.

It is sufficient to enforce this FIRST prefix surplus. Indeed define

    Dp=95+201alpha+202alpha/beta+202alpha^2/beta,
    F_n=R_n/(c_n d_n)=(1-100alpha)/c_n-2/d_n+Dp.

The reciprocal pair recurrences give exactly

    F_(n+1)=(1+2alpha/beta)F_n
       +2alpha(2/beta-1)/d_n-1-100alpha-(2alpha/beta)Dp.

Since1/d_n>=1/(alpha L), the final forcing is at least
(4/beta-2)/L-1-O(alpha), uniformly on I. Its limiting value is strictly
positive because L approaches J and beta(J+2)<4. Consequently F1>=0
implies every F_n>=0 for sufficiently small alpha, hence every R_n>=0 and
every e_n>=0. The full row0 rectangle remains strictly positive by Section5
and uniform convergence. This proves every finite-prefix comparison.

Solve the two finite outer returns simultaneously with w0=0. The limiting
outer root(J_*(beta),T_*(beta)) is independent of r, and its Jacobian is
nonsingular. Section6 gives w0/t=A-Lambda r+o_C1(1), whose Lambda derivative
is-r<0. Uniform IFT therefore supplies unique finite branches
J_N(r,beta),T_N(r,beta),Lambda_N(r,beta), with

    Lambda_N -> A(J_*,beta)/r,
    J_N-J_*=O(poly(N)t), partial_r J_N=O(poly(N)t).

All quantities here arise from the actual finite boundary problem. No
infinite core is played. The simple zeros of w1/alpha and e1/alpha^2 define
nearby exact endpoints r_N^- and r_N^+, respectively. Between them w1>=0,
e1>=0, and every other guard is strict.

At r_N^- the first two core roots both have w=0. The first is exactly the
canonical pair12 predecessor of the shortened core. Move it into the
infinite pair prefix. Dropping or adding finitely many predecessor iterates
does not change their limit C, so the outer target and all return equations
stay unchanged. The moved root's exact row3 indifference says that the
shortened core's first-prefix quiet3 surplus is zero. Conversely a
surplus-zero first pair predecessor can be promoted to a triple core root
with w=0, retaining all three indifferences.

This identifies neighboring N and N-1 branches at the SAME actual alpha,beta
and target. Reparameterizing the shortened branch changes its center J and
row0 entrance by O(alpha), which is permitted. Its limiting entrance
parameter is d r_min=r_max. Uniform uniqueness of the boundary problem and
outer IFT therefore gives exact equality of the two physical K endpoints.
One must not assume an exact equality of the auxiliary rescaled Lambdas.

On each legal branch

    K_N=1/[delta(beta,J_N)^(N-1)Lambda_N].

Its logarithmic r derivative tends uniformly to1/r>0: the derivative of the
delta factor is O(poly(N)t), because the limiting J is independent of r.
Thus each legal r interval maps onto a full closed K interval. The exact
endpoint identification joins the lower endpoint for N to the upper
endpoint for N-1 without a gap. These intervals tend to infinity uniformly
in beta, since delta stays uniformly below1 and Lambda stays positive and
bounded. One fixed sufficiently large starting N and compactness of I give
one finite threshold C covering every K>=C and beta in I.

This proves the middle closed ratio range[3/5000,3/50]. Section8 supplies
the remaining small ratios includingzero. Section4 supplies all larger
ratios and the explicit second raw region.

## 8. Hybrid closure of all small nonnegative ratios

### 8.1. A finite-alpha hybrid predecessor

Assume

    0<=beta<=1/1650, 0<alpha<=1/1000000,
    K=1/alpha, p=beta/alpha.

A supplied successor has native coordinates

    (T0,-L,X,alpha W),
    L>0, X>=0, L+3X<=1, 97X<=4L, W>=-100L.          (C1)

Row0 is transported but not constrained in this lemma. There is a unique
continuous complementarity choice among triple123, pair12 and pair23 below.
Its predecessor again satisfies(C1). Every hazard is proper. Iteration gives
summable hazards and L_n,X_n tending to0. After finitely many iterations
only pair12 is selected. All rows1,2,3 have exact Continue identities and
legal full immediate Quit comparisons. No continuation is executed after
an infinite calendar: all constructed chronological words are finite,
and their entrance annotations have a limit.

### 8.2. The exact support selector

For0<=u<=X/4 put

    Dz=1+alpha(1+L-99u), Dy=beta+alpha(2+X-u),
    Z(u)=(L-97u)/Dz, Y(u)=(X-4u)/Dy,
    f(u)=[2Y-101Z+106alpha YZ]/[(1-alpha Y)(1-alpha Z)]. (C2)

The cone gives u<=L/97, Dz>=1 and Dy>=alpha(2+X-u)>0. Thus Z,Y>=0,
q2=alpha Z<=alpha, and

    q1=alpha Y<=X/(2+X-u)<=4/197<1/40,
    w=u/(1+u)<=1/98.

The scalar f is strictly decreasing, uniformly even at beta=0. Put
Ay=beta+alpha(2+3u), Az=1+alpha(1-2u). Then

    1-alpha Y=Ay/Dy, 1-alpha Z=Az/Dz,
    Y_u=-(4beta+8alpha+3alpha X)/Dy^2,
    Z_u=-(97+97alpha-2alpha L)/Dz^2,
    f_Y=(2+5alpha Z)/[(1-alpha Y)^2(1-alpha Z)],
    f_Z=(-101+108alpha Y)/[(1-alpha Y)(1-alpha Z)^2].

The negative term f_Y Y_u has magnitude at least
8(beta+2alpha)/Ay^2. Since u<=1/97,
Ay<=(33/32)(beta+2alpha), and beta+2alpha<1/1500. Its magnitude is
therefore greater than8(32/33)^2*1500>11283. The positive term f_Z Z_u is
at most101*98*40/39<10152: use Dy/Ay=1/(1-q1)<40/39, Az>=1 and
97+97alpha-2alpha L<98. Consequently f_u<-1000 throughout the cone.
This proof uses no division by beta. When X=0 the allowed u interval is a
single point; the pair12 rule below applies automatically, as shown later.

If W>=f(0), choose pair12: u=0,Y=Y(0),Z=Z(0). Its row3 Continue value is

    W'=(1-alpha Y)(1-alpha Z)W-2Y+Z-5alpha YZ.

The row3 Quit value divided by alpha is -100Z+101alpha YZ, and their
surplus is exactly(1-alpha Y)(1-alpha Z)[W-f(0)]>=0.

If f(X/4)<=W<=f(0), choose the unique u with f(u)=W, using(C2), and
w=u/(1+u). This is triple123, with boundary zero hazards permitted.
All three active comparisons are equalities, and

    W'=-100Z+101alpha YZ.

If W<=f(X/4), choose pair23:

    u=X/4, Y=0, Z=-W/(101-alpha W), w=u/(1+u), W'=-100Z. (C3)

Here f(X/4)<=0, so W<=0. The zero case is a permissible boundary root.
At the upper endpoint of(C2), f=-101Z12/(1-alpha Z12). Since that expression
is strictly decreasing in Z12, (C3) has Z>=Z12. Row1's Quit-minus-Continue
gap is exactly

    -{[1+alpha(1+L-99u)]Z-(L-97u)}/(1+u)<=0.         (C4)

The two branch definitions agree at either switch. All coordinates and
hazards consequently depend continuously on the supplied data. No smooth
choice across a switch is asserted or needed for this lemma.

### 8.3. The invariant cone

In all three branches the exact current values are

    L'=[L+3u-alpha Z(1+L+12u)]/(1+u),
    X'=[X-u-alpha Y(2+X)]/(1+u).                     (C5)

For triple/pair12, their forced-Quit forms are

    L'=[Z+100u-111alpha Zu]/(1+u),
    X'=[beta Y+3u-alpha Yu]/(1+u),

The first is positive because Z,u are not both zero and
111alpha Z<100. The second is nonnegative because alpha Y<1/40.
It is positive unless u=0 and beta Y=0; the zero value is allowed by(C1).
For pair23, W>=-100L gives

    0<=Z<=100L/(101+100alpha L)<=L,
    L-Z>=L/101.

Therefore

    (1+u)(L'-Z)
      =(L-Z)+u(3-Z)-alpha Z(1+L+12u)
      >=L[1/101-alpha(2+12/97)]>0.

Also X'=3u/(1+u)>0 on a nontrivial pair23 branch. In every branch Z<=L and

    L'+3X'
     =[L+3X-alpha Z(1+L+12u)-3alpha Y(2+X)]/(1+u)
     <=L+3X<=1.                                      (C6)

For triple,

    W'+100L'
      =100w[100-Z(1+111alpha)]+101alpha YZ>=0.

For pair12 its quiet row3 guard gives W'>=-100Z+101alpha YZ>=-100L'.
For pair23 the preceding L'>=Z gives W'=-100Z>=-100L'. Thus the lower
W guard is invariant. There is deliberately NO W<=0 hypothesis: pair12
may create positive W, as its eventual entrance should permit.

It remains to prove97X'<=4L'. For triple/pair12 its numerator is

    F=4L-97X+109u-4alpha Z(1+L+12u)+97alpha Y(2+X).   (C7)

At fixed L,u, its exact derivative is

    F_X=97(alpha u-beta)(3alpha u+2alpha+beta)/Dy^2.

Its sign is constant as X varies between4u and4L/97. If F_X>=0, use the
lower endpoint X=4u, where Y=0 and

    F>=109L/97-4alpha L(2+12/97)>0.

If F_X<=0, use the upper endpoint X=4L/97. When u>=alpha L/10, the
positive term109u is at least10.9alpha L, whereas the negative term has
magnitude at most4alpha L(2+12/97)<8.5alpha L. When u<alpha L/10,

    X-4u>=L(4/97-2/5000)>L/25,
    Dy<=beta+alpha(2+X)<1/250,

so Y>10L. Its positive term97alpha Y(2+X)>1940alpha L again exceeds the
negative term. These bounds use only alpha,beta<=1/1000. Thus F>=0.
For pair23, u=X/4 and Z<=L give the same direct bound

    (1+u)(4L'-97X')
      >=109L/97-4alpha L(1+L+3X)>0.

The entire cone(C1) is preserved. Apart from an initial pure3 boundary,
Z is positive after entering the strict ratio cone; this strictness is not
needed for the comparisons.

### 8.4. Convergence and the permanent pair tail

Writing w=u/(1+u), (C5) gives

    X-X'=w(1+X)+alpha Y(1-w)(2+X)>=w+q1,
    L-L'=w(L-3)+q2[1+L+(11-L)w]>=-3w+q2.

Consequently every finite initial segment satisfies

    sum(w+q1)<=X_initial,
    sum q2<=L_initial+3 sum w,
    sum(q1+q2+w)<=L_initial+4X_initial.              (C8)

All three hazard sequences are summable. They are uniformly bounded below1,
so their combined survival product has a strictly positive limit. At every
constructed root row1's legal Quit comparison gives
L'<=K q2+100w; row2's exact comparison gives X'<=p q1+3w.
For fixed positive alpha both right sides tend to0. Hence L_n,X_n->0.

The third current coordinate obeys the exact Continue identity

    alpha W'=P3+(1-q1)(1-q2)alpha W,
    P3=-2q1+q2-5q1q2.

Equation(C8) bounds the coordinates and makes their successive differences
absolutely summable. Therefore alpha W has a finite limit C3. The invariant
lower bound W>=-100L and L->0 give C3>=0. The same elementary affine
transport proves that row0 has a finite entrance limit C0. Positivity of C0
and every row0 annotation is proved below.

There is in fact a permanent pair12 suffix in backward time. If u>=X/8,
then X-X'>=X/9. If u<X/8, then
Y>=X/[2(beta+3alpha)], and(C5) gives
X-X'>=alpha X/[4(beta+alpha)]. Both cases imply the uniform bound

    X'<=(1-alpha/[10(beta+alpha)])X.

Also(C5), Z<=L and L<=1 give L'>=(1-3alpha)L. Since beta+alpha<1/30,
X/L decreases geometrically to0. Eventually X/L<=(beta+alpha)/4, and
remains so. At u=0 then Y<=L/4 and Z>=L(1-2alpha). The numerator of
f(0)+100L is

    2Y-101Z+100L
      +alpha[106YZ-100LY-100LZ]+100alpha^2 LYZ
    <=[-1/2+(457/2)alpha+25alpha^2]L<0.

Since W>=-100L, the pair12 condition W>=f(0) holds. Its scalar ratio also
keeps decreasing, because beta(1+L)<2+X; for beta=0 the first such step
sends X' to0 exactly. Thus every subsequent root is pair12. Its explicit
recursions and limiting entrance formula apply at this finite switch point,
including p=0 by the nonsingular hazard recursions. In particular X=0 is
already in this permanent pair region.

All finite backward words are played in reverse construction order before
the supplied successor. Truncating the initial segment in backward time
changes their entrance values by a quantity tending to zero. The bounded
hazard sums and affine transport justify that limit directly, without an
infinite chronological prehistory. On compact data with alpha bounded away
from zero, the geometric X/L estimate bounds the switching time uniformly;
the explicit pair tail then gives continuity of the entrance limit. The uniform singular-alpha limit is proved next.


### 8.5. Scope and exact starting data

The final range is 0<=beta<=1/1650. Sections8.6--8.8 first work on any compact
subinterval I of(0,1/1650]; Section8.9 treats the joint boundaryalpha,beta->0.
Fix a compact J interval inside(0,1), containing the selected center roots
J_*(beta), and small enough that the strict outer guards remain valid. Put

    w=J(1+3beta/2)/(109+J(50beta-3)), u=w/(1-w),
    L_t=100w, X_t=3w, W_t=0,
    x=97u, E2=4u, E3=0.

The pure3 root w has exact native current coordinates
(T_t,-L_t,X_t,0) and successor(E0,-x,E2,0), where
T_t=3w+(1-w)E0. Players1,2 are indifferent and player3 is indifferent.
Its quiet row0 comparison is strict when T_t>0. The wash guard is strict:
E2-(3/100)x=(109/100)u>0.

Define E0 in terms of an outer unknown T by

    E0=3+(T-3)(3-x)/(3-J).                          (T1)

The supplied input satisfies L_t+3X_t<1,97X_t<4L_t,W_t>=-100L_t.
Apply the construction in Sections8.1--8.4, with alpha>0 small.
Every resulting root has legal rows1,2,3. Its limiting entrance is
(C0(alpha,J,T,beta),0,0,C3(alpha,J,beta)), with C3>=0.

The claim proved below is uniform convergence, on compact J,T,beta sets,
to the ordinary pair12 entrance applied to core data

    (T,-J,beta J/2,0),                             (T2)

at alpha=0, uniformly for the FULL closed beta interval. The two entrance
maps are continuous for every fixedalpha>0, includingbeta0.
This supplies a topological outer-root argument.

### 8.6. The alpha-zero hybrid orbit

The invariant J is

    J=(L+3X)/[1+X+(beta/2)(3-L)].

Set h=2X/beta-L and v=W+100L. Write A=8/beta-9797 and B=3+2/beta.
At alpha=0 the unconstrained triple choice is u=(h-v)/A. The actual choice
is clamped to[0,X/4]. On pair12, L'=L,X'=X,W'=W-h. On triple,
Z=L-97u,Y=(X-4u)/beta,W'=-100Z. On pair23,
u=X/4,Y=0,Z=-W/101,W'=-100Z. In all branches

    L'=(L+3u)/(1+u), X'=(X-u)/(1+u),
    h'=(h-Bu)/(1+u).                               (T3)

The invariant region is h>=0,v>=0,W<=0,97X<=4L,L+3X<=1.
The last two inequalities are preserved by increasingL and decreasingX.
On an active branch u<=h/A. Since beta<3/4900 gives A>B, (T3) preservesh>=0.
On pair12 its selection gives v>=h, so v'=v-h>=0. On triple,

    v'=u[9700+100(3-L)/(1+u)]>=0.

On pair23,

    v'=(100/101)v+(100/101)L+100(L'-L)>=0.

All active branches have W'<=0; on pair12 W'=W-h<=0.
Also Z,Y>=0: on triple u<=X/4<=L/97; pair23 uses W<=0.
The initial data are in this region and J is unchanged by every branch.
Solving the invariant forX gives

    X=beta J/2+[(1+beta J/2)/(3-J)](J-L),
    h=[(2+3beta)/(beta(3-J))](J-L).                  (T4)

Thus L increases bounded above byJ and X decreases bounded below bybeta J/2.
The total sumu is finite, because L'-L=(3-L)u/(1+u) and L<=1.
Pair23 occurs only finitely often because there u=X/4>=beta J/8>0.
If h had positive limit, infinitely many triple steps would haveu->0 and
therefore v'->0. At the following step the unconstrainedu would be bounded
away fromzero, a contradiction. If only finitely many triple steps occurred,
eventually all steps would be pair12, decrementingv by a positive amount
forever, also impossible. Hence h->0,L->J,X->beta J/2. Triple resets and
pair12 decrements also givev->0, so W->-100J.

The convergenceh_n->0 is uniform on compact parameter sets: every finite
iterate is continuous, h_n is nonincreasing and nonnegative, and its limit
is the continuous zero function. The elementary compact monotone-convergence
argument (or Dini's theorem) applies. From(T3), sum of allu afterdepthM is
at most h_M/B. Thus all remaining solo3 survival approaches1 uniformly.
At alpha0 row0 obeys the same affine recursion asL; (T1) makes its entrance
limit exactlyT. Every alpha0 row0 value lies betweenT andE0 and is positive.

### 8.7. Uniform tail control at positivealpha

Assume alpha<=min(.001,beta/16), reducing its uniform upper bound whenever
needed. The cone proof above gives L<=1,X<=4L/97,v>=0,Z<=L andu<=X/4.
Forh=2X/beta-L the exact update is

 (1+u)(h-h')
   =u(h+3+2/beta)
      +alpha[(2/beta)Y(2+X)-Z(1+L+12u)].            (T5)

As long ash>=0, this implies h-h'>=u/beta. To check it, ifu<=X/8 then
Y>=(X/2)/(beta+3alpha)>=4L/19, so the alpha bracket is positive, since
beta<.001 and1+L+12u<=2+12/97<17/8. The u term alone is sufficient.
Ifu>X/8, thenu>beta L/16. The negative part of the alpha bracket is at
most(17/8)alpha L<=(17/8)u, whereas the u term is at least
u(3+2/beta); division by1+u still leaves at leastu/beta.
This argument includes pair23, whereu=X/4 andY=0.

Onceh<=0, pair12 is legal and remains selected forever. Indeed f(0)
increases withX. AtX=beta L/2 an exact simplification gives

 f(0)+100L
   =L alpha(7Lbeta+400alpha+202beta-4)
      /[2(alpha+1)(2alpha+beta)]<0.                 (T6)

SinceW>=-100L, W>=f(0). The pair12 scalar maps are

    L'=f_alpha(L)=L/[1+alpha(1+L)],
    X'=g_alpha,beta(X)=beta X/[beta+alpha(2+X)].     (T7)

Their ratioX'/L' is smaller thanX/L forbeta<.001 andL<=1, so h remains
nonpositive and (T6) applies at every later root.

At the first crossing fromh>=0 toh'<0 the overshoot satisfiesh'>=-C alpha,
uniformly on our compact beta interval. Here is a direct compactness proof.
On any active branch W is bounded above byf(0) and below by-100L, and
L,X lie in a compact set. The finite-alpha complementarity map is uniformly
O(alpha)-close to the alpha0 clamped map on this bounded set: its strictly
monotone scalar equation has derivative bounded away fromzero, its two
endpoints are smooth, and the pair23 formula is smooth. At alpha0,
u<=h/A andA>B implyh'>=0. On a pair12 step the exact scalar formulas(T7)
are likewiseO(alpha)-close to their identity limits. This proves the bound.

Summing(T5) until the crossing, or forever if there is no crossing, gives

    sum_(n>=M) w_n <= sum_(n>=M) u_n
                    <= beta(max(h_M,0)+C alpha).  (T8)

For each fixedM the positive-alpha finite orbit converges to its alpha0
orbit. Combining(T8) with the uniformh_M->0 in Section8.6 shows

    lim_(M->infinity) limsup_(alpha->0)
         sup_parameters sum_(n>=M) w_n =0.         (T9)

This is a uniform tail estimate across all support switches and the spectral
resonance; it uses no derivative of the orbit with respect to parameters.

### 8.8. Comparison of the tail with the exact pair12 prefix

Start at backwarddepthM. Compare the subsequent hybrid word with the pure
pair12 word having the same currentL_M,X_M and row0,row3 annotations.
Write its scalar states asbarL_n,barX_n. Uniformly on the cone,

 |L'-f_alpha(L)|+|X'-g_alpha,beta(X)| <= C u,
 |Z-L/[1+alpha(1+L)]|
   +|Y-X/[beta+alpha(2+X)]| <= C u.                (T10)

For triple and pair12 these estimates follow directly from the rational
formulas and uniform denominator bounds. For pair23,Y=0 andX=4u, giving
theY bound. Its Z is at most the pair12 value because
100L/(101+100alpha L)<=L/[1+alpha(1+L)] foralpha<=.01. Its quiet1 guard
placesZ above(L-97u)/[1+alpha(1+L-99u)], which differs from the pair12
value byO(u). This proves the remaining bound.

The derivatives of the scalar maps satisfy

    0<f_alpha'(L)<=1/(1+alpha),
    0<g_alpha,beta'(X)<=beta/(beta+2alpha).

Consequently the scalar error recursions and a geometric-series sum imply

 alpha sum_n(|L_n-barL_n|+|X_n-barX_n|)
       <=C sum_n u_n.                             (T11)

Together with(T10), this bounds the sum of differences of the actualq1,q2
hazards from the pair reference byC sumu. The totalq3 hazard is itself at
mostsumu. Couple the independent root decisions coordinatewise. The total
variation distance between any finite-prefix terminal distributions is
therefore at mostC sumu, uniformly in its length. Only rows0,3 are compared:
their rewards on coalitions contained in123 are bounded independently ofK,p.
Their continuation annotations are also bounded. Thus their actual values,
at every finite backwarddepth and at the limiting entrance, differ from the
pair reference by at mostC sumu. No comparison involving the unbounded
row1 orrow2 coalition premiums is used.

For fixedM letalpha->0, thenM->infinity. By(T9), the hybrid tail and its pair
reference have the same limit. The pair limiting entrance formula is an
explicit continuous rational function ofalpha,beta,L,X,T0,T3, with a
continuous limit atalpha0 forbeta inI. BySection8.6,

    (L_M,X_M,T0_M,alpha W_M)->(J,beta J/2,T,0).

This proves the claimed uniform entrance convergence to(T2).

The same coupling estimate proves all row0 guards. ChooseM large so the
alpha0 state atdepthM is near(T2) and the total remainingu is small. The pair
reference has strictly positive row0 values at every prefix because its
four rectangle corners are uniformly positive by the center outer-root
lemma in Section5. The hybrid tail remains uniformly close to those values.
The firstM
row0 values are positive by continuity from their positivealpha0 limits.

### 8.9. The joint boundary alpha,beta->0

Here no lower bound onbeta and no bound onalpha/beta is imposed. Use the
cone proof above on0<=beta<=1/1650,0<alpha<=1e-6. It gives
all comparisons, the same summability bound, and a continuous entrance.
The formulas withY=(X-4u)/[beta+alpha(2+X-u)] are nonsingular foralpha>0,
even whenbeta0. A pair12 step atbeta0 simply hasX'=0, and every later root
is a pureplayer2 step. Zero hazards are legal boundaries of the selectors.

On every fixed finite backward segment, the selectedY is uniformly bounded
asalpha,beta->0. Indeed W>=-100L>=-100 and the exact Continue identity gives
W'<=max(W,0)+L, so W_n<=n fromW_0=0. For a triple step, solvef=W forY:

 Y=[W(1-alpha Z)+101Z]
      /[2+106alpha Z+alpha W(1-alpha Z)].           (T12)

Its denominator exceeds1 foralpha<=1e-6 on any fixed finite segment once
alpha is small enough. Pair12 hasW>=f(0); sincef increases withY, itsY
is at most the same expression(T12), and pair23 hasY=0. HenceY is bounded
on that segment. The physical hazardsq1=alphaY,q2=alphaZ tend tozero.
For triple and pair12, the exact row2 equation says

    X-4u=[beta+alpha(2+X-u)]Y;

for pair23,u=X/4 identically. Thusu->X/4 at every fixed step. The limiting
finite-state map is

    L'=(L+3X/4)/(1+X/4), X'=3X/(4+X),              (T13)

with invariant(L+3X)/(1+X)=J. ItsX iterates decrease geometrically tozero,
andL->J. These convergences are uniform on the compact initialJ interval.
Every finite-depthrow0 value has the corresponding solo3 limit, and its
limit asdepthM->infinity isT by the same identity(T1). AlsoalphaW_M->0.

There is a beta-independent tail comparison. Start atdepthM and compare the
actual hybrid tail with the PUREplayer2 prefix fromthe sameL_M and passive
annotations. Its scalar states obeybarL'=f_alpha(barL), and its hazards are
q2=alpha barL/[1+alpha(1+barL)], q1=w=0. The exact estimates

    |L'-f_alpha(L)|<=C u,
    |Z-L/[1+alpha(1+L)]|<=C u                     (T14)

hold with an absolute constant independent ofbeta. For triple they involve
onlyL,u,alpha. For pair23 the sameZ sandwich used inSection8.8 applies.
The f_alpha contraction therefore yields

 alpha sum|L_n-barL_n|<=C sumu_n.

The cone hasu<=1/97, so sumu<=2sumw. The general summability identity gives
sum(q1+w)<=X_M. Hence the sum of differences of all three physical hazards
fromthis pureplayer2 reference is at mostC X_M. Coupling bounded rows0,3
asbefore gives a uniformO(X_M) error for every finite-prefix value and the
limiting entrance. This comparison uses no1/beta factor.

The pureplayer2 entrance from(L,T0,T3) is exactly

    C0=(T0-L)/(1+L), C3=(T3+L)/(1+L),              (T15)

because its absorption mass isL/(1+L). Its row0 values at all finite prefixes
lie between its terminalT0 and entranceC0. First letalpha,beta->0 atfixedM,
using(T13); thenletM->infinity. SinceX_M->0, the coupling error vanishes, and
(T15) converges to

    C0=(T-J)/(1+J), C3=J/(1+J).

This is exactly the beta0 limit of the center pair-entrance formula of Section5. The
argument is uniform on the compactJ,T set. It also proves uniform positive
row0 margins nearbeta0: the pureplayer2 endpoint values are strictly
positive, the late hybrid values stay close, and the finite initialsegment
converges to positive solo3 mixtures.

Combining this joint boundarylimit with the uniform interior convergence of
Sections8.6--8.8 proves uniform entrance convergence asalpha->0 over the ENTIRE
closed interval0<=beta<=1/1650. Formally, any contrary sequence has a
convergentbeta subsequence; a positive limit is handled by the interior proof,
and a zero limit by this section. The same compactness argument establishes
uniform row0 positivity. No rate or differentiability atbeta0 is claimed.

### 8.10. Continuous outer roots and the behavioral consumer

For fixedalpha>0 the limiting hybrid entrance is continuous inJ,T,beta.
One can either use its eventual pair12 tail locally, or use the uniform
hazard tail bounds on compact initial data and affine transport. At a switch,
the adjacent formulas agree exactly. No differentiability across a switch
is required.

InsertC0,C3 and the suppliedE0,x,E2 into the two exact outer returns

    A1(3-E0)=3(E0-x), A2(3-E0)=3E2+E0,

whereb=C0/(1+C0), B3=(C0+C3)/(1+C0), a=B3/(1+B3),
A1=2a+(1-a)b,A2=2a. Atalpha0 these are a nonzero common scalar multiple
of the center-return equations(5.2) of Section5. Their selected
root(J_*(beta),T_*(beta)) is nonsingular. On a small neighborhood of this
root their boundary map has nonzero local degree. Uniform convergence of
the two return maps preserves that degree for all sufficiently smallalpha;
therefore an exact root exists. The limiting outer root is also simple at
beta0. ThereC0=(T-J)/(1+J),C3=J/(1+J), the second return reduces to
T(5-4T)/(1+2T), and the selected root isJ=3/4,T=5/4. The Jacobian of
the two center returns in(J,T) there is

    [[5/2,-45/14],[0,-10/7]],

whose determinant is-25/7. Compactness of the full closedbeta interval
makes thealpha threshold uniform. This uses finite-dimensional degree
(equivalently the
local stability of an isolated simple zero under continuous uniform
perturbations), not an implicit-function claim about the hybrid map.

All strict outer and row0 guards persist, and every hybrid row1,2,3 guard is
exact. For each fixed raw game select one such outer root and its limiting
entranceC. The finite-calendar consumer in Section9 applies: truncate the
backward prefix until its entrance differs fromC byeta, attach the exact solo0,
solo2, pure3 and wash stages, and use the strictly absorbing tail of Section9.
Only the finite-prefix junction has a residual, tending tozero. Its local
comparison proof treats quiet1 pair23 roots just like every other legal
quiet root. The fixed limiting target is chosen from this one outer root
before the requested accuracy. All deviations are unrestricted behavioral
deviations and all sufficiently long horizons use the same accuracy profile.

Consequently one finite threshold covers everyK above it and every
0<=beta<=1/1650. This overlaps the middle range because3/5000<1/1650.
Together with Sections4--7 it proves K>=C,p>=0 after taking the maximum
of the finitely many uniform thresholds. The explicit outer cone was
already proved in Section4.1.

## 9. Complete behavioral and fixed-target consumer

At a product root q let Q_i be the payoff from Quit now, P_i the passive
payoff from nonempty opponent coalitions, and H_i=product_(j!=i)(1-q_j).
For a successor value v, Continue gives P_i+H_i v_i. A reference annotation
u obeys the Continue identity when u_i=P_i+H_i v_i. If every owner who quits
with positive probability also has Q_i=u_i, the prescribed payoff identity
holds. The full behavioral cap obeys

    B_i=max(Q_i,P_i+H_i B_i(next)).                    (9.1)

Before absorption there is only one surviving public history. A private
behavioral deviation is therefore a law on finite quitting dates and Never;
its payoff cannot exceed their supremum. Equation (9.1) prices that complete
menu, including its infinite-horizon limit.

The outer calendar connects

    A=(0,A1,A2,0) --solo0--> B=(0,B1,0,B3)
      --solo2--> C_n --finite pair12 word--> T
      --finite core (supports12,23,123, or pure3)--> E=(E0,-x,E2,0)
      --solo3 repair--> V=(V0,0,V2,0) --solo3--> A.

Here C=(C0,0,0,C3) is the limiting pair entrance, and C_n is its exact
finite-n approximation. Fix the selected finite core, limiting C, and
A,B,E,V before accuracy. Give every finite-pair root its exact annotation.
The only Continue and prescribed-identity error occurs at solo2, because
its actual successor C_n differs from the reference C. Its norm is at most
eta_n=||C_n-C||_infinity, which tends to0 by Section2. The solo2 immediate
Quit comparisons depend on B and its hazards and are unchanged.

Given C and E, set

    b=C0/(1+C0), B1=b+(1-b)C1, B3=b+(1-b)C3,
    a=B3/(1+B3), A1=2a+(1-a)B1, A2=2a,
    R=1-x/3, V0=(E0-x)/R, V2=(E2+x/3)/R, h=V0/3.

The constructions above ensure

    C0>0, B1>0, B3>0, 0<x<3, E0>x, E2>=3x/100,
    0<h<1,
    A1(1-h)=3h, A2(1-h)=V2+h.                       (9.2)

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

The final solo3 aggregate h closes the return by (9.2). Its annotations at
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
from (9.1), then unrolling the maximum over a period, gives

    B_i-u_i<=e+eta/rho, |U_i-u_i|<=eta/rho,
    B_i-U_i<=e+2eta/rho.                             (9.3)

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
the asserted uniform contract at W=kappa+A, because the selected core and limiting entrance fix A
before accuracy while its finite pair approximations have eta tending to zero.




## 10. Coverage and scope

The ray p=K/1000 with the following completion is covered by the new
producer for every K>=C. It lies outside the earlier raw positive cone
p>=2K and the negative regions p<=0, and cannot be reduced to the fixed
K=100 scalar family by relabeling or positive row rescaling. The singleton
matrix has a unique row with two equal positive off-diagonal entries, fixing
player0; its sign fixes player2, and the remaining signs fix players1 and3.
Its nonzero entries then force every row scale to1.

It also exceeds the actual construction range of the small-positive-ratio
backward-contraction mechanism. That mechanism requires
D=4-9797beta/2>0 and a secondary normal eigenvalue smaller in modulus than
the leading contraction; beta=1/1000 already has D<0. The new mixed
forward/backward boundary problem removes that mechanism's restriction.
The following stronger wedge certificate excludes every stationary and
sure-root selection on this ray, despite the uncomputed large-K threshold.

Players are 0,1,2,3. Nonempty absorbing rewards are `r_i(D)=1+Z_i(D)`;
the live reward and the payoff on Never are zero. Columns below are coalition
masks 0,...,15 (the mask-zero entry is only a polynomial placeholder):

```
Z0: 0  0  3   0  -1   0  -12 -13   3 -3    2  -7   -6  -7  -8   -5
Z1: 0  2  0  -1   1   5   -K   6  -3  3 -100   8    9  -8  11   -9
Z2: 0  2 -2 -10   0 -10    p  -9  -1 -5   -1  10    3  -3   2    8
Z3: 0 -1 -2 -12   1   7   -6  11   0  1    0 -10 -100 15/2  1 21/2
```

For every `K>=100` and `0<=p<=K/100`, this table has:

1. no exact stationary terminal Nash equilibrium;
2. no exact terminal Nash equilibrium whose first live round has any player
   quitting surely, even when its continuation after all Continue is arbitrary.

These are strategy-class exclusion claims; they are not counterexamples to
uniform equilibrium. The no-sure-root claim allows all behavioral continuations
and all behavioral unilateral deviations. Proving necessary conditions
infeasible suffices, so no strategy-class completeness is assumed.

### Necessary polynomial systems

For independent root quitting probabilities `q in [0,1]^4`, put

```
H_i = product_{j!=i}(1-q_j),
P_i = sum_{nonempty S subset opponents} Pr(S) Z_i(S),
Q_i = sum_{S subset opponents} Pr(S) Z_i(S union {i}),
F_i = (1-H_i) Q_i - P_i.
```

For a stationary terminal Nash profile the necessary sign of `F_i` is
nonpositive at `q_i=0`, nonnegative at `q_i=1`, and zero for `0<q_i<1`.
Indeed, where the opponents stop with positive probability, the payoff from
never quitting is `1+P_i/(1-H_i)` and quitting now gives `1+Q_i`.
When the opponents never quit, `P_i=0,H_i=1`, so the displayed signs are
still necessary (though deliberately weaker). All Continue itself is excluded
because a player can quit alone for reward 1 instead of Never payoff 0.

For a root with a sure quitter define

```
L=(-12,-8,-10,-12),   G_i=Q_i-P_i-H_i L_i.
```

`L_i` is the minimum of -1 and all native rewards `Z_i(S)` with `i notin S`.
A player can always never quit in the continuation, securing at least
`1+L_i`; its best-response continuation value therefore has this lower bound.
For each player other than a unique sure quitter, `H_i=0`, so the root
best-response signs of `G_i` are exact. For that sure quitter the replacement
of its continuation value by the lower bound only increases `G_i`, preserving
the necessary nonnegative sign. With multiple sure quitters every `H_i=0`.
Consequently the same three signs are necessary for `G` on every pattern
containing a sure player. This argument imposes no restriction on continuations.

### Eliminating the unbounded parameter without losing its correlation

Write `beta=p/K in [0,1/100]`, `Delta=K-100>=0`, and use superscript `b`
for the finite baseline `K=100,p=100 beta`. Direct expansion gives

```
F1 = F1b - Delta (1-H1)(1-q0)q2(1-q3),
F2 = F2b + beta Delta (1-H2)(1-q0)q1(1-q3),
G1 = G1b - Delta (1-q0)q2(1-q3),
G2 = G2b + beta Delta (1-q0)q1(1-q3).
```

Rows 0 and 3 do not change. When the decreasing row-1 coefficient is not
identically zero on a pattern, retain `F1b>=0` (or `G1b>=0`) for an active
or sure player 1 and drop its quiet inequality. For the increasing row 2,
retain the baseline nonpositive inequality for an active or quiet player 2
and drop its sure inequality. If the coefficient vanishes identically, retain
the original sign. These relaxations are necessary also at beta=0.

The following exact identities retain the shared-parameter constraint:

```
CF = beta(1-H2)q1 F1b + (1-H1)q2 F2b
   = beta(1-H2)q1 F1  + (1-H1)q2 F2,
CG = beta q1 G1b + q2 G2b = beta q1 G1 + q2 G2.
```

All multipliers are nonnegative. A combination has the nonnegative sign if
all its nonzero terms originally have nonnegative or zero signs, the
nonpositive sign in the opposite case, and equality if all terms are zero.
Mixed positive/negative requirements give no useful constraint and are dropped.
A multiplier identically zero on the pattern contributes no sign. Using its
possible sign when beta=0 only weakens the conclusion and is safe.

Every baseline and both correlated polynomials are affine in beta. The
checker adds `s=100 beta in [0,1]` as an extra polynomial variable by exact
endpoint interpolation. It treats s by Bernstein coefficients on its full
interval, so its success proves the entire wedge simultaneously.

### Analytic boundary rules and the origin

A pattern records each player as quiet, sure, or strictly mixed. There are
80 nonzero patterns and 65 containing a sure player. Their free coordinates
are the mixed players; the checker uses their closed unit cube, which is a
safe enlargement.

If `q0=0`, player 2 is mixed, and either player 1 or player 3 is nonquiet,
write `y=q1,w=q3`. Then

```
Q2=p y(1-w)+w(3-y)>=0,
P2=-2y-w+2yw<0,
```

so `F2>0`, contradicting mixing. If precisely one coordinate j is mixed
and none is sure, the table has an outsider i with `Gamma_ij<0` and
`Z_i({i,j})>=0` throughout the wedge. Its quiet inequality fails since
`F_i=q_j(q_j Z_i({i,j})-Gamma_ij)>0`.

For a no-sure pattern with at least two free coordinates S, the baseline
active equations have

```
F_S^b(q,s)=-Aq+R(q,s),   A=Gamma_SS,
```

where every monomial of R has q-degree at least two; s-degree is at most one.
All involved A are invertible. Put `V=A^{-1}`. The checker finds an integer
vector `ell>0` (entries in 1,...,8) such that `a=ell^T V` has a nonnegative
coefficient on the relaxed row 1 and a nonpositive coefficient on the relaxed
row 2. Unrelaxed mixed equations have zero left side and place no sign restriction on a.
Thus `a.F_S^b>=0` at any feasible point, and

```
min(ell)||q||infty <= ell.q <= a.R
                   <= sum_j |a_j| C_j ||q||infty^2,
```

where `C_j` is the sum of absolute coefficients of `R_j` as a polynomial
in `(q,s)`. This bound holds uniformly for `s in [0,1]`. If the right-hand
coefficient is zero, there is no nonzero feasible q. Otherwise, defining
`D=sum_j|a_j|C_j/min(ell)`, every nonzero feasible q satisfies
`||q||infty>=1/D`. The checker removes a dyadic origin cube with side strictly
less than `1/D`. It explicitly checks every coefficient of q-degree below two.

The checker also adds those linear combinations given by rows of V whose
necessary sign follows from the retained row signs. No mixed-sign combination
is asserted. This accelerates exclusion without strengthening the system.

### Exact finite box verification

For every remaining restricted polynomial `P(x)=sum_m a_m x^m`, choose
coordinate degrees `d_i` at least all appearing exponents. Its tensor
Bernstein coefficients on the unit cube are

```
b_k=sum_{m<=k} a_m product_i binom(k_i,m_i)/binom(d_i,m_i).
```

They are rational. Clearing one positive denominator gives integer
coefficients with identical signs. Bernstein basis functions are nonnegative
and sum to one; hence strictly positive (negative) coefficients force a
strictly positive (negative) polynomial throughout the closed box. This
refutes an opposite weak inequality or an asserted equality.

If necessary, the checker bisects a q coordinate. On a degree-d fiber with
old coefficients `b_0,...,b_d`, left and right coefficients multiplied by the
common positive factor `2^d` are

```
left_r  = 2^(d-r) sum_{j=0}^r binom(r,j)b_j,
right_r = 2^r sum_{j=0}^{d-r} binom(d-r,j)b_(r+j).
```

Thus all subsequent arithmetic is integer. The two child boxes cover their
parent. The parameter s stays unsplit except in zero-q-dimensional patterns,
where it is the sole coordinate. A leaf is discarded only by a strict sign
contradiction or the proved uniform origin bound. Depth/node limits abort
without asserting success. Every box is exhausted for every pattern.

For deterministic reproduction, enumerate patterns and free players in
ascending lexicographic order with quiet=0, sure=1, mixed=2. Choose the first
admissible ell in lexicographic `{1,...,8}^d`. Keep original polynomials in
player order, append CF or CG, then valid V-row combinations in row order.
Use the maximum appearing exponent per coordinate across these polynomials,
with minimum degree 1, including rows whose constraint is ignored. Tensor
indices are lexicographic. Clear the least common multiple of all initial
Bernstein denominators in one pattern. Start E at 1 and increment until the
strict origin inequality holds. Traverse boxes depth first, left child first;
split a q coordinate with minimum subdivision depth, breaking ties by ascending
player order. For no q coordinates, split s. Test signs before the origin rule;
before each subdivision require at most 100000 visited boxes and coordinate
depths at most 35. Analytic shortcuts each contribute one node to the totals.

The prescribed finite rational calculation terminates with all80 nonzero
stationary patterns excluded in1046 nodes and all65 sure-root patterns
excluded in371 nodes. No unresolved box remains. The node totals include
one for every analytic shortcut. No floating-point rootfinding or stored
subdivision payload is a premise.

The following finite-choice checks exclude the other named existing
selectors on the separating ray. They concern concrete sufficient mechanisms,
not an assertion that every conceivable equilibrium theorem has been surveyed.
The singleton matrix Gamma has determinant25 and inverse column0
(8,3,14,10)/25>0. Its positive graph is strongly connected, while the
participant vector on123 is(11,2,1)>0. Thus complete ordered nonpositive
anchor selection fails: an admissible marked set must be all players, and
its first block meeting123 has positive weighted participant sum. The same
positive vector defeats every upper-average weight on the core.

The upper-face joining charge at12 is Z3(123)-Z3(12)=7>0, so the required
mixed-trap sign fails. The only inverse-positive principal triple is023,
whose outside inverse row is(-3,6,2)/5; full passive-child selection fails.
The unique mutually negative singleton pair is13. Its only labeling meeting
the attached-pair sign template is(3,1,0,2), where the required nonnegative
participant premium is Z1(13)=-100. The both-premiums-arbitrary alternative
instead requires m=Gamma21=-2 to be nonnegative.

For the three invariant-cone pair partitions, the necessary positive
difference Z_i({i,mate})-Gamma_i,mate fails:01|23 gives-3 at i=0,02|13
gives-12 at i=2, and03|12 gives-6 at i=0. No proof-weight matrix repairs
those prerequisites. Inverse column2 is(9,-6,-3,5)/25, defeating the
all-signed-positive inverse-column criterion under all relabelings and
sign choices. The unique mutually positive pair01 intersects the unique
mutually negative pair13, whereas the signed four-cycle templates require
them disjoint. Every three-player subset also contains a core pair with a
negative participant reward. These raw obstructions are unchanged as K
increases along p=K/1000.



The proper-active-support weighted-column alternative does not supply this
ray either. Its only growing coordinates are the negative pole(1,12) and
the positive pole(2,12). No relevant principal inverse has a strictly
positive negative column1. Positive column2 is eligible only on support023,
which excludes player1 from the growing coalition12. Thus neither growing
coordinate is eligible on any active support that contains its required
coalition. All favorable rewards remain bounded while the adverse envelope
grows at least as K. The stationary certificate independently excludes any
exact stationary producer on the entire separating ray.

The semantic sources inspected are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
The proof above supplies its own full behavioral and fixed-target consumer.
No new Lean checking or formalization is claimed. The new formalization
targets are the explicit limiting first integral, the hybrid support selector
and its uniform singular transport, the cooperative positive connection,
the mixed saddle boundary problem with scaled derivatives, and exact
entrance support gluing. Arbitrary Fin4 remains open.
