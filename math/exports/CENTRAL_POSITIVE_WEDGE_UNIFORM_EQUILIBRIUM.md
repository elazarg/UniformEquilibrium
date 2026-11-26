# Uniform equilibrium on a central positive wedge

This packet constructs uniform equilibria in an unbounded positive reward
wedge. It is ordinary mathematics, not checked in Lean. Arbitrary signed
four-player quitting games remain open.

## 1. Raw statement

There are four players0,1,2,3. At each live date they independently choose
Continue or Quit. The first nonempty quitting coalition D absorbs and pays
r(D); live play and literal AllNever pay zero. Put kappa_i=r_i({i}) and
Z_i(D)=r_i(D)-kappa_i for nonempty D only. Thus native own-singletons are0.
A string such as123 denotes{1,2,3}. Fix

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

All seven row0 entries on nonsingleton coalitions containing0 are <=0.
The other21 entries on those coalitions and the four original own-singleton
levels are arbitrary independently.

**Theorem.** There are finite constants C>=100 and beta0>0 such
that every game in this family with K>=C and 0<=p<=beta0 K has a
uniform-equilibrium payoff against unrestricted behavioral deviations.
The constants do not depend on the unrestricted entries or singleton levels.
No numerical bound on either constant is asserted. Arbitrary Fin4 remains open.

## 2. Exact core and its backward dynamics

Put alpha=1/K and beta=p/K. At triple123 hazards(0,alpha Y,alpha Z,w),
the active current values are(Q1,Q2,alpha q3), and the required active
successor values are(F1,F2,alpha f3), where

```
Q1=-Z-100w+(1+111alpha)Zw,
Q2=beta Y+3w-(beta+alpha)Yw,
q3=-Z(100-101alpha Y),
F1=[-(1+alpha)Z-97w+(1+100alpha)Zw]/[(1-alpha Z)(1-w)],
F2=[(beta+2alpha)Y+4w-(beta+3alpha)Yw]/[(1-alpha Y)(1-w)],
f3=[2Y-101Z+106alpha YZ]/[(1-alpha Y)(1-alpha Z)].
```

The last successor has third coordinate0 exactly when
Y_last=101Z_last/(2+106alpha Z_last). Each preceding root is obtained by
solving F1=nextQ1,F2=nextQ2,f3=nextq3 backwards. This gives an analytic
map T_(alpha,beta) on the compact neighborhoods used below. To see directly
why beta=0 causes no singularity, at alpha=0 write the next root as(Z',Y',v)
and set

```
L=Z'(1-v)+100v, X=beta Y'(1-v)+3v,
D=4-9797beta/2,
u=[X-beta(101L-100Z')/2]/D,
w=u/(1+u), Z=L-97u, Y=(101Z-100Z')/2.
```

For beta sufficiently small D>0. These formulas solve the three equations
uniquely. The Jacobian in the three current variables is invertible there,
so the same backward map exists analytically for alpha of either sign
sufficiently small, uniformly on the compact set. Only alpha>0 is physical.

At alpha=0 the map fixes the line e(J)=(J,J/2,0). In transverse coordinates
(w,e) with e=Y-Z/2 its linearization at e(J) is

```
M_beta(J)=[ A/D                        beta/D
            50(100-J)-4850A/D       -4850beta/D ],
A=3-5050beta+50beta J.
```

At beta=0 its eigenvalues are3/4 and0. For beta in one small closed interval
[0,beta0], J near3/4, the eigenvalues delta_beta(J),kappa_beta(J) are real,
simple, and satisfy 0<delta_min<=delta_beta(J)<=delta_max<1 and
|kappa_beta(J)|<delta_min^2. The leading eigenvector has nonzero w
coordinate. The center eigenvalue is1. All these statements follow from
the displayed2x2 matrix by continuity, including the one-sided endpoint0.

## 3. Uniform long-core lemma

The required conclusion is the following. The alpha=0 iterates have a C2
invariant projection pi_beta onto e(J), and a C2 leading stable amplitude
A_beta, normalized so A_0 on the terminal surface is theta=w/(1+3w).
Parameterize that terminal surface by

    pi_beta(Z,101Z/2,w)=J,     theta=w/(1+3w).

At beta=0 this is explicitly

    pi_0=[(1-w)Z+109w]/(1+3w),
    Z=(J-109theta)/(1-4theta).

The derivative pi_0 with respect to Z at fixed w on that section is
(1-w)/(1+3w)>0. The implicit-function theorem therefore selects one smooth
Z=Z_beta(J,theta) for all sufficiently small beta. This Z and w stay fixed
when alpha is introduced, and the physical terminal Y is replaced by
101Z/(2+106alpha Z). This specifies the terminal section completely.

The terminal phase varies in a fixed small neighborhood of
I=[9/1744,3/436]. Given N, set

    t=delta_beta(J)^(N-1), alpha=t Lambda,
    Y_last=101Z_last/(2+106alpha Z_last),

and iterate T_(alpha,beta) backwards N-1 times. For Lambda in a compact
positive interval and J near3/4 the following hold uniformly in C1 as N→infinity:

```
Z_first -> J,  Y_first -> J/2,
w_first/t -> A_beta(J,theta)-Lambda b_beta(J),
b_0(J)=J, A_0(J,theta)=theta,
```

where b_beta is smooth and positive. The unscaled entrance coordinates and aggregate quantities differ from
their complete alpha=0 infinite-orbit limits by O(poly(N)t). This does not
assert that a fixed terminal-index state approaches the center line. The
same estimates apply to the parameter derivatives, with possibly a larger
fixed polynomial in N.
In particular, after imposing w_first=0,

    |Y_first-Z_first/2|<=C1 alpha,

and every later w is strictly positive, uniformly for beta small and N large.
All other core hazards have their required signs whenever terminal Z>=0;
only the last Y,Z may vanish, together. At the limiting endpoints the
terminal Z and wash-margin zeros are simple. Their nearby exact zeros
therefore define a legal phase interval.

### 3.1. Normal coordinates and invariant projection

For this proof only, write a=alpha and b=beta; n=N-1.

Write an initial transverse coordinate z=(Y-Z/2,w). Direct differentiation
of the displayed a=0 interface map gives its normal derivative at l(J):

    D=4-9797b/2,       L=3-5050b+50bJ,
    M=[-4850b/D, 50(100-J-97L/D); b/D, L/D].          (4)

At b=0 its eigenvalues are 0 and 3/4. For b,J in compact sufficiently small
neighborhoods they remain real, simple and separated. Choose one q with

    max delta < q < 1,       q^2 < min delta,
    max |kappa| < q^2.                               (5)

For instance these strict inequalities are possible at b=0 since
3/4 < sqrt(3/4). Smooth linear normal coordinates and a fixed adapted norm
make transverse contraction at most q on a sufficiently small tube.

The exact fixed line and this transverse contraction imply that unperturbed
iterates converge to a unique point l(pi_b(x)). Here is the elementary
construction: each normal distance is O(q^j), the increment of the tangent
coordinate is O(q^j), and the increments are summable. Differentiating the
recursions a fixed finite number of times gives bounds C(1+j)^m q^j for the
differences between successive tangent limits; thus pi_b is C^k, uniformly
on a slightly smaller tube. It obeys

    pi_b(T_{0,b}x)=pi_b(x),       pi_b(l(J))=J.

Consequently s=pi_b(x), together with the two transverse coordinates, gives
local coordinates in which the unperturbed map fixes s EXACTLY. A smooth
linear change on each fiber diagonalizes its transverse derivative:

    s'=s,
    z'=diag(delta(b,s),kappa(b,s)) z + R_b(s,z),
    |R_b(s,z)|<=C|z|^2.                              (6)

The coordinate changes and remainders have all the bounded derivatives used
below. The leading normal coordinate is normalized so that physical w is
z_1 plus a linear multiple of z_2 plus O(|z|^2).

For the particular terminal section, existence of the required basin is not
an extra hypothesis to be guessed. At b=0 the explicit theta recurrence is
backward multiplication by 3/4, while J is invariant and the other normal
coordinate decays. A fixed number j0 of backward iterates sends the whole
compact terminal section into the chosen tube. Continuity preserves this
property for sufficiently small b. Define pi and all later coordinates on
the section by pulling them back through these j0 forward applications of
the backward map; no inversion is involved.

### 3.2. Leading amplitude

For fixed s=J, write the first transverse coordinate as v_j. Equation (6)
gives

    v_{j+1}=delta v_j+r_j,      |r_j|<=C q^(2j).

Hence

    A=v_0+sum_{j>=0} delta^(-j-1) r_j

converges by (5), and v_n=delta^n A+O(q^(2n)). The fast coordinate is
O(q^(2n)), because |kappa|<q^2. The same conclusion holds for physical w.
Parameter differentiation only inserts fixed powers of j into this
convergent geometric series. Therefore

    w(T_{0,b}^n x)/delta(b,J)^n -> A(b,J,theta)

in C^k on the compact parameter set. Its error is bounded by
C(1+n)^m (q^2/min delta)^n. At b=0 the exact formula

    w_n=(3/4)^n theta/[1-3(3/4)^n theta]

gives A=theta, so A_theta stays strictly positive for b sufficiently small.
A is not necessarily the raw terminal theta when b is nonzero.

### 3.3. First variation and uniform remainder

Use the SAME coordinates built for a=0. Analyticity gives

    s'=s+a f_b(s,z)+O(a^2),
    z'=D_b(s)z+R_b(s,z)+a g_b(s,z)+O(a^2).            (7)

All coefficients and their required derivatives are uniformly bounded.
For |a|<=C t and 0<=j<=n, elementary induction gives

    |s_j-J|<=C(1+j)|a|,
    |z_j|<=C(q^j+|a|),                               (8)

after allowing the O(a) change of the terminal section itself. These bounds
hold because n|a| tends to zero and the normal multiplier stays below a
fixed constant smaller than one.

At a=0 let dot denote derivative in a. The tangent variation is O(1+j).
The normal variation satisfies a stable affine recurrence. Terms involving
dot{s}_j are O((1+j)q^j), because D_s times z_j and R_s both vanish at z=0.
Its limiting forcing is g_b(J,0). Thus

    dot z_n -> h_b(J):=(I-D_b(J))^(-1)g_b(J,0),
    dot w_n -> h_w(b,J),                             (9)

in C^1 in the remaining parameters, at rate bounded by a polynomial times
q^n. Any a-derivative of the terminal section has only a decaying normal
contribution; its bounded center component also enters physical w through
a factor O(q^n). The limit is therefore independent of theta.

For completeness, the nonlinear Taylor remainder in this argument is
uniform over the growing number of iterates. Differentiate (7) twice in a.
The tangent first derivative is O(1+j); its second derivative is O((1+j)^2).
The normal first derivative is bounded by a constant times 1+j|a|, and its
second derivative is O((1+j)^2). The latter follows by stable summation of
forcing terms involving tangent derivatives, using (8). Further fixed
parameter derivatives add fixed polynomial factors only. As physical
w(s,0)=0 for every s, the terms involving a pure tangent derivative also
carry a normal factor. Consequently, for some fixed m,

    w_n(a)=w_n(0)+a dot w_n(0)+O(a^2(1+n)^m)          (10)

uniformly in C^1 in (b,J,theta). The analogous differentiated estimate in a
controls the Lambda derivative after substitution. These bounds also hold
for small negative a, as needed for an ordinary open-set implicit-function
theorem; only the final selected profiles require positive a.

Substitute a=t Lambda into (10), divide by t, and combine (9) with the leading-amplitude estimate.
The remainder becomes O(t(1+n)^m). Derivatives of t in b or J cost only one
additional factor n since D log t=n D log delta. This proves the scaled entrance formula with
B=-h_w. At b=0 the exact backward theta equation at the fixed line has
first-order forcing -aJ/4, its multiplier is 3/4, so h_w=-J and B=J.


The aggregate estimates used below follow from the same bounds, rather
than from an unscaled convergence claim. At alpha=0, the omitted tail of
the infinite backward orbit has sum of w coordinates O(delta^n)=O(t),
with derivatives bounded by a fixed polynomial in n times t. The finite
perturbed states differ from their unperturbed states by O(poly(n)alpha),
uniformly over the first n iterates, from the first- and second-variation
bounds. The extra physical hazards alpha Y and alpha Z contribute the
same bound. Affine payoff recursions and finite survival products have
bounded local derivatives on this compact domain. Summing their differences
over n roots therefore costs only another polynomial factor. This gives
O(poly(n)t), including first parameter derivatives, between finite-core
entrance and aggregate quantities and their complete alpha=0 infinite-orbit
limits. The infinite survival product is positive uniformly: at beta=0 it
equals1-4theta, and summable geometric tails give uniform continuity for
small beta.

### 3.4. Physical signs

At b>0 the determinant of the normal matrix (4) is negative, so kappa<0.
This is harmless, but plain continuity in b at each fixed n would NOT prove
the required uniform positivity for unbounded n.

Assume theta ranges in a fixed compact positive interval and that the
unperturbed terminal orbit has positive w at every finite backward index.
At b=0 this is explicit; it persists uniformly for small b, using the positive
leading amplitude for all large indices and compact finite continuity for
the remaining ones. Let the selected branch satisfy w_n=0, with Lambda
bounded away from zero. For each 0<=m<=n, the proof above gives

    w_m=delta^m A-alpha B+E_m,
    |E_m|<=C(1+m)^k q^(2m)
            +C|alpha|(1+m)^k q^m
            +C alpha^2(1+n)^k.                       (11)

The first term in (11), divided by delta^m, tends uniformly to zero. The
second, divided by |alpha|, does too; the last is o(alpha), uniformly in m.
The terminal section's O(alpha) change is already included in the first
variation; it has a vanishing normal transient and therefore does not alter B.

Fix epsilon>0 small compared with delta_max^(-1)-1. Choose M so large that
the first two terms in (11) are at most epsilon(delta^m+alpha) for every
m>=M, and next take n large enough for the last term to be at most
 epsilon alpha. At m=n the exact boundary w_n=0 gives

    alpha B=delta^n A+o(alpha).

Since A and B have fixed positive lower bounds, for M<=m<=n-1,

    w_m >= (1-C epsilon)delta^m A
               -(1+C epsilon)delta^n A >0,

where the final inequality uses delta^m>=delta^(n-1) and the fixed gap
1-delta_max>0. More precisely w_m>=c delta^m>=c' alpha delta^(m-n).
For 0<=m<M, the finitely many unperturbed orbit coordinates have a common
positive lower bound and the selected alpha tends to zero; ordinary uniform
continuity proves positivity there. Thus the first chronological core root
has w=0 exactly and EVERY later chronological core root has w>0.

No positivity of the fast eigenvalue, no monotonicity of that fast mode, and
no uncontrolled iteration of a singular forward inverse is used.


The fast component at the first point is O(alpha)+o(t), by its fast normal
recurrence and the same stable variation estimate. When w_first=0, physical
w is the slow component plus a bounded multiple of the fast component and
a quadratic error. Both normal components are therefore O(alpha), since
alpha and t are comparable on the positive compact Lambda range. This
proves |Y_first-Z_first/2|<=C1 alpha.

At beta=0 every nonterminal scaled Z is bounded below positively on the
whole phase interval, and its backward Y is
(101Z-100Z_next)/2>=Z/2 because the reference Z values decrease in
chronological order. The last Y has exactly the last Z's sign. A fixed
finite number of initial backward iterates remains in a compact set where
these nonterminal signs are strict. The remaining iterates lie near the
positive fixed line. Thus small beta, followed by uniformly small alpha,
preserves every nonterminal Y,Z sign. The analytic last formula preserves
the terminal signs exactly. All hazards are below1 for small alpha, and
w remains in a small neighborhood of the displayed reference phases.


## 4. Limiting pair entrance and outer return

At w_first=0 the exact first core annotation is

    T=(T0,-L,X,T3),
    L=Z_first, X=beta Y_first,
    T3=-alpha Z_first(100-101alpha Y_first).

Its row0 value T0 is obtained by the exact backwards affine recurrence

    G(y,z,w;r)=3y-z+3w-14yz-4yw-8zw+13yzw
                       +(1-y)(1-z)(1-w)r,
    y=alpha Y,z=alpha Z,

starting at a free terminal coordinate E0. The terminal annotation is
E=(E0,-x,E2,0), where x=-F1(last), E2=F2(last).

For p>0, arbitrarily long finite pair12 words before T have limiting
entrance C=(C0,0,0,C3). It is given EXACTLY by

```
S=2/[(2+X)(1+L)],
chi=alpha S L X/(2+beta+2alpha),
pi1=[beta S L X/(2+beta+2alpha)+S X]/2,
pi2=S L X/(2+beta+2alpha)+S L,
C0=3pi1-pi2-12chi+S T0,
C3=-2pi1+pi2-6chi+S T3.
```

These are analytic also at beta=0; there X=0 and the pair word consists
only of solo2 roots. Section6 proves convergence and every quiet guard.

Define the outer parameters

```
b=C0/(1+C0), B1=b, B3=(C0+C3)/(1+C0),
a=B3/(1+B3), A1=2a+(1-a)b, A2=2a.
```

The two exact return equations are

    H1=A1(3-E0)-3(E0-x)=0,
    H2=A2(3-E0)-3E2-E0=0.                           (4.1)

In the alpha=0 limit only solo3 absorption remains along the core. If its
aggregate survival is S_core, the exact passive recursions give

```
J=3(1-S_core)+S_core x,
beta J/2=-(1-S_core)+S_core E2,
T0=3(1-S_core)+S_core E0.
```

Consequently the two equations after multiplication by S_core become

    H1_lim=A1(3-T0)-3(T0-J)=0,
    H2_lim=A2(3-T0)-3beta J/2-T0=0.                 (4.2)

These equations are INDEPENDENT of the terminal phase. In the formulas for
C,A use alpha=0,L=J,X=beta J/2,T3=0. At beta=0 their exact root is

```
J=3/4, T0=5/4, C0=2/7, C3=3/7,
b=2/9, B3=5/9, a=5/14, A1=6/7, A2=5/7.
```

The Jacobian of(H1_lim,H2_lim) in(J,T0) at this root is

    [5/2  -45/14]
    [ 0    -10/7],       determinant=-25/7.

Thus unique smooth functions J_*(beta),T_*(beta) solve(4.2) for every
beta in one sufficiently small closed interval. They do not depend on
phase. At beta=0 their derivatives are J_*'=-183/160,T_*'=-57/64.

Combining the scaled entrance equation w_first/t=0 with(4.1), the uniform
C1 lemma and this nonsingular Jacobian give unique finite-N branches
J_N(theta,beta), E_N(theta,beta), Lambda_N(theta,beta). At beta=0 the
limiting branch is

    J_*=3/4, E0=(5-48theta)/[4(1-4theta)],
    Lambda=theta/(3/4).

For beta sufficiently small the positive derivative of limiting Lambda in
theta persists. The unscaled branch estimates give
J_N-J_*=O(poly(N)t) and partial_theta J_N=O(poly(N)t). Therefore

    alpha_N=delta_beta(J_N)^(N-1)Lambda_N

is strictly increasing in theta for all large N: the extra logarithmic
term (N-1)(partial_J log delta) partial_theta J_N tends uniformly to0.
Thus K_N=1/alpha_N is strictly decreasing.

## 5. Exact phase boundaries and unbounded raw coverage

At beta=0 the limiting final scaled hazard and wash margin are

```
Z_last=(3/4-109theta)/(1-4theta),
E2-3x/100=(436theta-9/4)/[100(1-4theta)].
```

Their zeros are simple, at theta_plus=3/436 and theta_minus=9/1744.
Small beta and then small alpha preserve two distinct smooth boundary
phases theta_N^-(beta)<theta_N^+(beta), where respectively the wash
margin vanishes and Z_last vanishes. Both quantities are nonnegative
between them. The core lemma gives every other physical core guard.
All row0 core annotations stay positive. The other outer guards
C0>0,B1>0,B3>0,0<x<3,E0>x,0<h<1 are strict at beta=0 and persist uniformly.
Here h=(E0-x)/(3-x), and E2>=3x/100 is exactly the wash guard.

At theta_N^+ the final root has Z=Y=0 and is solo3 of hazard w. Its
current coordinates1,2 are(-100w,3w) and its successor coordinates are
(-97w/(1-w),4w/(1-w)). Deleting this root gives an N-1 core whose exit
has x_old=100w and E2_old=3w, exactly the wash equality. Row0 transforms
by E0_old=3w+(1-w)E0. Both outer returns are multiplied by the same
positive factor1-w, so remain zero. The first core root, its pair entrance,
and the raw alpha,beta are unchanged. At alpha=0 the projection pi_beta is invariant under deletion, and the
leading amplitude satisfies A_beta(T_(0,beta)x)=delta_beta(J)A_beta(x).
At small alpha the shortened terminal parameter changes by O(alpha); the
rescaled Lambda changes by a factor delta_beta(J)+O(poly(N)t). Thus the
shortened sequence lies in the unique N-1 branch neighborhood at its lower
wash boundary. The finite-core uniqueness identifies the two solutions. Hence

    K_N(theta_N^+(beta),beta)
      =K_(N-1)(theta_(N-1)^-(beta),beta).            (5.1)

For each fixed beta, the legal phase intervals map to closed K intervals.
They meet exactly by(5.1), and their endpoints tend to infinity uniformly
in beta because delta<=delta_max<1 and Lambda stays in a compact positive
interval. One sufficiently large starting N0 gives a continuous finite
lower endpoint on the compact beta interval. Its maximum, enlarged to100,
is a finite constant C. The joined intervals cover every K>=C for every
beta in[0,beta0]. Since p=beta K, this is the region in Section1.

## 6. Every finite pair prefix is legal

At pair12 hazards(0,c,d,0), the two active current and successor values are

    current1=-Kd, successor1=-(K+1)d/(1-d),
    current2=pc, successor2=(p+2)c/(1-c).

For p>0 start c0=X/p=alpha Y_first,d0=L/K=alpha Z_first and define

    c_n=c_(n-1)/(1+2/p+c_(n-1)),
    d_n=d_(n-1)/(1+1/K+d_(n-1)).                    (6.1)

The physical word(c_n,d_n),...,(c_1,d_1) is actively indifferent and has
successor T. Both hazards are strictly between0 and1 for n>=1. For p=0
define c_n=0 for n>=1 and use the same d recursion. All row2 active
comparisons then hold because its own singleton and T2 are0.

For p>0 put A=pc_n,B=Kd_n,D0=(2+X)(1+L). Its exact survival and
first-coalition masses are

```
S_n=(2+A)(1+B)/D0,
chi_n=(S_n L X-A B)/(2K+2+p),
pi1_n=(p chi_n+S_n X-A)/2,
pi2_n=K chi_n+S_n L-B.
```

These follow from the two active payoff identities and total probability.
They converge to S,chi,pi1,pi2 of Section4 as n tends to infinity. At p=0
the same formulas hold with A=X=chi_n=pi1_n=0. Thus every finite entrance
converges to the fixed C of Section4.

Player0's actual value U0=3pi1_n-pi2_n-12chi_n+S_n T0 is bilinear in(A,B).
The full rectangle0<=A<=X,0<=B<=L has corner values

    C0, C0(2+X)/2-3X/2, C0(1+L)+L, T0.

At beta=alpha=0 these are respectively2/7,2/7,5/4,5/4. They therefore
stay uniformly positive for small beta and alpha. Every pair prefix lies
in the rectangle, so U0>0. Its Quit offers are nonpositive by the raw caps.

It remains to price player3. Put e_n=U3_n-Q3(c_n,d_n), where
Q3(c,d)=-100d+101cd. The formal starting surplus is e0=0 because
T3=Q3(c0,d0) exactly. Substituting(6.1) in the passive recursion gives

```
e_n=(1-c_n)(1-d_n)e_(n-1)+(1-100/K)d_n-2c_n
    +c_n d_n[95+201/K+202/p+202/(pK)].              (6.2)
```

All terms in brackets are positive. We prove the stronger sufficient
bound c_n/d_n<=(1-100alpha)/2 for all n>=1.

The core lemma supplies |Y_first/Z_first-1/2|<=B alpha with Z_first in a
compact positive interval. Choose C_z>=1+Z_first uniformly. Then

    c1/d1 <= (1/2+B alpha) beta(1+C_z alpha)/(beta+2alpha).

The desired inequality follows because twice the right numerator subtracted
from (1-100alpha)(beta+2alpha) equals

    alpha[2-beta(100+2B+C_z)-200alpha-2B C_z beta alpha],

which is positive for one sufficiently small beta0 and alpha0. No division
by beta is used, so the estimate is uniform as beta tends to0. Moreover

    2/p-1/K+c_n-d_n
      >=alpha[2/beta-1-Z_max]>0

for p>0 and sufficiently small beta0. The quotient of consecutive ratios
is(1+1/K+d_n)/(1+2/p+c_n)<1. Thus every later ratio is no larger than the
first. Equation(6.2) and induction now give e_n>=0 for all n.

At p=0 the word is solo2. Start the induction with
T3>=-100d0, since T3=-100d0+101alpha^2 Y_first Z_first. Its exact surplus
recurrence is e_n=(1-d_n)e_(n-1)+(1-100/K)d_n, also nonnegative forK>=100.
This proves all finite-prefix quiet comparisons, without a word-length bound.

## 7. Complete behavioral consumer

At a product root q let Q_i be the payoff from Quit now, P_i the passive
payoff from nonempty opponent coalitions, and H_i=product_(j!=i)(1-q_j).
For a successor value v, Continue gives P_i+H_i v_i. A reference annotation
u obeys the Continue identity when u_i=P_i+H_i v_i. If every owner who quits
with positive probability also has Q_i=u_i, the prescribed payoff identity
holds. The full behavioral cap obeys

    B_i=max(Q_i,P_i+H_i B_i(next)).                    (7.1)

Before absorption there is only one surviving public history. A private
behavioral deviation is therefore a law on finite quitting dates and Never;
its payoff cannot exceed their supremum. Equation (7.1) prices that complete
menu, including its infinite-horizon limit.

The outer calendar connects

    A=(0,A1,A2,0) --solo0--> B=(0,B1,0,B3)
      --solo2--> C_n --finite pair12 word--> T
      --finite triple123 core--> E=(E0,-x,E2,0)
      --solo3 repair--> V=(V0,0,V2,0) --solo3--> A.

Here C=(C0,0,0,C3) is the limiting pair entrance, and C_n is its exact
finite-n approximation. Fix the selected triple core, limiting C, and
A,B,E,V before accuracy. Give every finite-pair root its exact annotation.
The only Continue and prescribed-identity error occurs at solo2, because
its actual successor C_n differs from the reference C. Its norm is at most
eta_n=||C_n-C||_infinity, which tends to0 by Section6. The solo2 immediate
Quit comparisons depend on B and its hazards and are unchanged.

Given C and E, set

    b=C0/(1+C0), B1=b+(1-b)C1, B3=b+(1-b)C3,
    a=B3/(1+B3), A1=2a+(1-a)B1, A2=2a,
    R=1-x/3, V0=(E0-x)/R, V2=(E2+x/3)/R, h=V0/3.

The constructions above ensure

    C0>0, B1>0, B3>0, 0<x<3, E0>x, E2>=3x/100,
    0<h<1,
    A1(1-h)=3h, A2(1-h)=V2+h.                       (7.2)

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

The final solo3 aggregate h closes the return by (7.2). Its annotations at
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
from (7.1), then unrolling the maximum over a period, gives

    B_i-u_i<=e+eta/rho, |U_i-u_i|<=eta/rho,
    B_i-U_i<=e+2eta/rho.                             (7.3)

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



## 8. Coverage and formalization scope

The positive wedge is not covered by the earlier scalar family K=100,
by the central negative region p<=0, or by the outer positive cone p>=2K.
The p=1 ray belongs to this theorem for every sufficiently large K and
separates it from all these reward conditions. Positive row rescaling and
player relabeling cannot remove K: the singleton matrix has a unique row
with two equal positive off-diagonal entries, fixing player0; its sign fixes
player2, and the remaining signs fix players1 and3. The nonzero entries then
force every row scale to1, leaving both parameters unchanged.

The following fixed completion of the unrestricted entries, with all
kappa_i=1, separates the new region from stationary and sure-root methods:

| D | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
|01|0|-1|-10|-12|
|02|0|5|-10|7|
|012|-13|6|-9|11|
|03|-3|3|-5|1|
|013|-7|8|10|-10|
|023|-7|-8|-3|15/2|
|0123|-5|-9|8|21/2|

For EVERY K>=100 at p=1 this completion has no stationary equilibrium and
no root with a sure quitter that is Nash against any actual continuation
cap. Consequently every K>=max(C,1/beta0) at p=1 supplies a separating game inside the
new existence theorem, even though no numerical upper bound on C is given.
The following finite exact certificate proves the two uniform exclusions.

For product hazards q write

```
H_i=product_(j!=i)(1-q_j),
P_i=sum_(nonempty S subset opponents) weight_q(S) Z_i(S),
Q_i=sum_(S subset opponents) weight_q(S) Z_i(S union{i}),
F_i=(1-H_i)Q_i-P_i,
L_i=min({-1} union {Z_i(S): nonempty S excludes i}),
G_i=Q_i-P_i-H_i L_i.
```

Here weight_q(S)=product_(j in S)q_j product_(j outside S,i)(1-q_j).
The displayed completion has L=(-12,-8,-10,-12), independent of K.
Every nonzero stationary equilibrium satisfies F_i<=0 for q_i=0, F_i=0
for0<q_i<1, and F_i>=0 for q_i=1, by comparing Quit now with Never.
AllNever is excluded separately by each original own-singleton payoff1.
A root with a sure quitter that is Nash at an actual continuation cap must
satisfy the same signs for G: the continuation cap is at least L by Never,
and replacing it by L can only improve the sole sure owner's Quit action;
all other players have H_i=0. With multiple sure owners all H_i are zero.

Only row1 varies with K. Its exact dependence is

```
F1(K)=F1(100)-(K-100)(1-H1)(1-q0)q2(1-q3),
G1(K)=G1(100)-(K-100)(1-q0)q2(1-q3).
```

Thus all K>=100 can be excluded by one necessary-condition relaxation
using only the rational table at K=100,p=1. Enumerate support patterns in
{0,1,*}^4; for F retain the80 nonzero patterns, and for G retain the65
patterns containing a sure owner. If a pattern has q2=0, q0=1, or q3=1,
keep all original signs because the K term vanishes. In every other
pattern, keep rows0,2,3 unchanged and replace row1's condition as follows:
for mixed or sure row1 require its baseline polynomial>=0; for quiet row1
omit its condition. These are necessary for every K>=100, and do not
assume that row1's active equality persists at K=100.

One direct exclusion simplifies F: if q0=0, player2 is mixed, and q1 or q3
is positive, then at p=1

    Q2=q1(1-q3)+q3(3-q1)>=0,
    P2=-2q1-q3+2q1q3<0,

so F2>0, contradicting its active equality. A pattern with one mixed
coordinate j and no sure owner is excluded by an outsider i with
Gamma_ij<0 and Z_i({i,j})>=0; such an outsider exists for every j. Choose
an outsider whose comparison was retained. For j=2 one can choose i=0.
The other single-owner cases have an identically vanishing K term.

For at least two mixed coordinates S, form A=Gamma_SS and V=A^(-1), where

    Gamma=[ 0  3 -1  3
            2  0  1 -3
            2 -2  0 -1
           -1 -2  1  0 ].

Every such principal matrix is invertible. Add the V combinations of the
mixed-row baseline polynomials. They are equalities unless mixed row1 was
relaxed. In that case each combination has the sign of its coefficient
in column1 of V: >=0 for a positive coefficient, <=0 for a negative one,
and =0 for zero. All other mixed rows remain exact equalities.

For a pattern with no sure owner, these baseline mixed polynomials have
form -Aq+R(q), with R containing only terms of degree at least2. If row1
was not relaxed they imply q=V R. If row1 was relaxed, the directly excluded
q0=0 cases have already been removed. Every remaining relevant principal
inverse has column1 entrywise nonnegative, so V F>=0 and q<=V R. In either
case put

    c_i=sum of absolute coefficients in R_i,
    D=max_i sum_j |V_ij| c_j.

Then ||q||_infinity<=D||q||_infinity^2. If D=0 the pattern is impossible;
otherwise choose the least positive integer E with2^-E<1/D and discard
all nonzero points in[0,2^-E]^S. All the constants use only the baseline
rational polynomials; the origin exclusion is uniform in K.

Here are the remaining exact finite certificate rules. Substitute the fixed
coordinates of each pattern, retain the signs just described, and append
the V combinations. Every coordinate degree is at most2. If a polynomial
is sum_m a_m x^m in d mixed variables, its tensor degree2 Bernstein
coefficient at index k in{0,1,2}^d is

    b_k=sum_(m<=k) a_m product_i [binom(k_i,m_i)/binom(2,m_i)].

Clear one common positive denominator for all coefficients in a pattern.
Reject a box if an equality has coefficients all strictly positive or all
strictly negative, or if an inequality has all coefficients of its forbidden
strict sign. Omitted conditions are ignored. Also reject a box contained
in the proved origin cube. Otherwise bisect the coordinate subdivided the
fewest times, breaking ties by increasing player index. For each degree2
coefficient triple (u,v,w) along that coordinate, integer-scaled left and
right children are

    left=(4u,2(u+v),u+2v+w),
    right=(u+2v+w,2(v+w),4w).

Scaling is positive and preserves every sign. Process left before right.
A zero-dimensional pattern is checked directly, and each direct exclusion
above counts as one node. These prescribed finite rational calculations
terminate with exactly862 nodes for the80 stationary patterns and371 nodes
for the65 sure-root patterns. No box is left unresolved. This supplies
uniform exclusions for all K>=100 at p=1; it is not a behavioral
counterexample, since Section1 supplies UE for the large-K tail.


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
increases along p=1.

The semantic sources inspected are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
The full behavioral and fixed-target finite-horizon argument is supplied in
Section7; these declarations identify the intended Lean consumers. No Lean
compilation or formalization is claimed.

The proposed formalization targets are the analytic backward-map formula,
the uniform long-iterate lemma with its scaled parameter derivatives, the
phase-independent outer return, the all-length pair guard, and exact support
deletion. The equilibrium producer is analytic and has no numerical
rootfinding premise. Only the explicit coverage certificate uses finite
rational Bernstein arithmetic. Arbitrary Fin4 remains open.

