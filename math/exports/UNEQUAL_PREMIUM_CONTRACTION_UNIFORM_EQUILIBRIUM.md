# Unequal participant premiums: a cone and a closed-wedge equilibrium theorem

Fin4 remains open. The results here produce uniform equilibria on two explicit
regions of independently unequal participant-premium ratios. The second region
includes its neutral switching boundary and has one scale threshold on every
compact parameter set. The mathematics is not yet formalized in Lean.

## Exact reward-table statement and semantics

There are four players I={0,1,2,3}, one live state, and independent private
Continue/Quit choices at each live date. The first nonempty quitting coalition
A absorbs at its finite reward vector r(A). Live and literal Never pay zero.
There is no public correlation device. A unilateral deviation may replace a
player's entire behavioral strategy, including its Never probability. On the
unique live history this is equivalent to replacing its private law on finite
dates and Never; the four laws are independent.

Put ell_i=r_i({i}) and Z_i(A)=r_i(A)-ell_i for nonempty A only. The levels ell
are arbitrary signed numbers. This notation shifts neither live nor Never.
The native singleton matrix is

    Gamma=[0,3,-1,3; 2,0,1,-3; 2,-2,0,-1; -1,-2,1,0].

For every nonempty A not containing i, require the additive passive reward
Z_i(A)=sum_(j in A) Gamma_ij. On every proper nonsingleton coalition containing
its owner, rows1,2,3 have native participant rewards a beta, beta, c beta,
respectively. The SIX proper participant entries in row0 vary independently
over all finite values at most1, with no lower bounds. Its native grand reward
is any finite value at most10. The three other grand rewards are arbitrary
finite numbers. These requirements specify the class directly from rewards.

**Theorem.** Suppose (a,c) belongs to either of the following regions:

    cone region: a>0, 0<c<5/9, 8a<15(1-c);             (C1)
    closed wedge: 1<c<2, 3c/2<=a<3.                   (W1)

For each such (a,c) there is beta0(a,c)>0 such that every game above with
0<beta<beta0 has a uniform-equilibrium payoff. One positive beta0 works for
all parameters in any fixed compact subset of either stated region, including
compact subsets meeting 2a=3c. It is independent of the freely lowered row0
rewards, ell, and the three unqueried grand coordinates.

A uniform-equilibrium payoff is one vector fixed before accuracy: for every
epsilon>0 there are one behavioral profile and one finite horizon threshold
such that every longer finite-horizon average payoff is within epsilon of that
vector and every unilateral behavioral gain is at most epsilon. The construction
below supplies finite periodic approximate profiles with this property.

No continuation, invariant set, root selector, return, or strategy is an input.
The cone is given by explicit linear inequalities. In the closed wedge, two
contracting operators produce the invariant graph and its switching extension.
An intermediate-value argument produces the macro return. The final finite-word
estimate prices all behavioral deviations. The exact calibrations below show
that each region adds reward tables outside the compared existing criteria.

## 1. The closed wedge: exact maps and the produced triple graph

Assume (W1) throughout Sections 1-5.

Write x=(u,v) for owners1 and3's continuation caps and t for owner2's cap.
For triple hazards q=(y,z,w) on owners1,2,3, the indifference input is

    I_beta(q)_1=[a beta(z+w-zw)-z+3w]/[(1-z)(1-w)],
    I_beta(q)_2=[beta(y+w-yw)+2y+w]/[(1-y)(1-w)],
    I_beta(q)_3=[c beta(y+z-yz)-z+2y]/[(1-y)(1-z)].    (W2)

Its output is Q_beta(q)=beta(a(z+w-zw),y+w-yw,c(y+z-yz)). These formulas
are exact endpoint equalities. At beta0, DI_beta(0) is

    G=[0,-1,3;2,0,1;2,-1,0].

Put P=[0,a,a;1,0,1;c,c,0]. The exact map of continuation caps is
F_beta=Q_beta o I_beta^{-1}; it is analytic locally, F_beta/beta extends
analytically through beta0, and

    DF_beta(0)=beta PG^{-1}(Id+beta PG^{-1})^{-1}.      (W3)

The characteristic polynomial of PG^{-1}, multiplied by8, is

    p(X)=8X^3+5(c-1)X^2-(3ac+a+2c)X+2ac.             (W4)

It has exactly one negative root -r. Indeed p(-X) has one sign change;
p(-c)=3c(a-c)(c+1)>0 and p(-a)=-4a(a-c)(2a+1)<0, so c<r<a.
The other two roots have positive real part: their product is positive,
and r>5(c-1)/8 makes their sum positive. The latter follows immediately
from r>c>1. In particular the negative root is simple and separated from
the remaining spectrum, including when the latter is a double root.

The positive spectral plane in continuation coordinates is

    t=A u+B v,
    A=(1+r)/(a+3r), B=(1+2r)/(c+2r).                 (W5)

The left normal (-A,1,-B) is an eigenvector of PG^{-1} for -r. Put

    m=3A-1>0, n=1-B>0.

The identities aA-1=-rm and cB-1=2rn will be used repeatedly. Also
aA>1/2, aA<1 and 1<cB<2 throughout (W1).

For all small beta>0 there is a produced local invariant graph

    t=T_beta(u,v), T_beta(0)=0,
    DT_beta(0)=(A,B), ||D^2 T_beta||<=C.              (W6)

The radius and C can be chosen uniformly on a compact parameter subset.
Here is the required regularity argument. Split into the positive plane
and the negative eigendirection; remove the linear tangent-normal coupling
by the invertible tangential operator L+r Id. In these coordinates

    s'=L_beta s+O(beta |(s,n)|^2),
    n'=-nu_beta n+R_beta(s,n),
    nu_beta=beta r/(1-beta r), R_beta=O(beta |(s,n)|^2),
    D_n s'=O(beta |(s,n)|).

On a fixed small ball use C^{2,1} graph functions h with h(0)=Dh(0)=0,
bounded second derivative and bounded Lipschitz constant of that derivative.
The complete metric on differences g is
max(sup |g(s)|/|s|^2, sup |Dg(s)|/|s|, sup |D^2g(s)|). The transform is

    (Th)(s)=[R_beta(s,h(s))-h(s'(s,h(s)))]/nu_beta.

The chain rule gives a contraction factor C(rho+beta) in this metric.
The first term contributes O(rho) to differences because D_n R_beta is
O(beta rho); the second contributes O(beta), since two tangential derivatives
carry beta^2 before division by nu_beta. Differences in the evaluation
points of D^2h use the common Lipschitz bound on D^2h. The C2 bound is at
most C0+C1(rho+beta)K2. The Lipschitz bound on D^2Th is at most
C2(1+K2)^3+C3(rho+beta)K3. Choose K2, then K3, then rho,beta small.
These estimates prove preservation of the closed C^{2,1} class and Banach
contraction, and prove continuous dependence in C2 on the raw parameters.
Transform back to (u,v,t), using the graph's nonvertical tangent. This gives
(W6), with no smooth invariant surface assumed as an input.

The same construction gives the exact local factorization

    H_beta(F_beta(u,t,v))=K_beta(u,t,v) H_beta(u,t,v),
    H_beta(u,t,v)=t-T_beta(u,v), K_beta<0.             (W7)

Indeed the left side vanishes on H_beta=0; the fundamental theorem of
calculus factors it by H_beta. Its transverse derivative at the origin is
-beta r/(1-beta r), so it remains negative on a common small neighborhood.
After division by beta, this negativity is uniform on compact parameters.

## 2. A strictly concave physical boundary

For fixed u,v>=0, the virtual triple hazards are obtained by choosing z and
then

    y=[v(1-z)+(1-c beta)z]/[2+(v+c beta)(1-z)],
    w=[u(1-z)+(1-a beta)z]/[3+(u+a beta)(1-z)].         (W8)

The corresponding t=I_beta(q)_2 is strictly increasing in z, with derivative
4/3 at the zero-parameter origin. For small positive beta it follows that
the graph root is physical exactly when

    T_beta(u,v)>=tcrit_beta(u,v),

where tcrit is (W2)'s second input at z=0. On this region y,z,w>=0 and
all are O(u+v).

Use cap odds

    xi=u/(3+u), upsilon=v/(2+v).                     (W9)

The physical graph region is locally

    Omega_beta={xi,upsilon>=0: upsilon<=k_beta(xi)},
    k_beta(0)=0,
    k_beta'(0)=m/(2n) * (1+c beta/2)/(1+a beta/3).    (W10)

Most importantly k_beta is strictly concave. To prove this, parameterize
the zero-hazard graph boundary by its pair hazards y,w. Invariance and (W7)
give the EXACT boundary equation

    y+w-yw=T_beta(a beta w,c beta y)/beta.            (W11)

By (W6), its right side is aA w+cB y+O(beta(y+w)^2), with the same estimate
in C2. Thus as beta tends to zero the equation converges in C2 to

    rmw-2rny-yw=0,
    y=rmw/(2rn+w).                                  (W12)

This has strictly negative second derivative near the origin. The analytic
change from pair hazards to the odds (W9) tends to the identity in C2:

    xi=(1+a beta/3)w/(1+(a beta/3)w),
    upsilon=(1+c beta/2)y/(1+(c beta/2)y).

The implicit-function theorem and (W11)-(W12) prove k_beta''<0 on a common
small interval. All inequalities have uniform margins on compact subsets
of (W1). This is a quadratic inward boundary, even where the linearized
projective boundary is neutral; no simple-eigenvalue assumption on the
positive spectral plane is needed.

## 3. Exact pair contraction and invariance of the physical triple region

For a pair13 root, owners1 and3 have hazards

    w=u/(3+a beta+u), y=v/(2+c beta+v).

The outer caps update to u'=a beta w, v'=c beta y. In the odds (W9), this is
the EXACT diagonal map

    Pi_beta(xi,upsilon)=(rho1 xi,rho3 upsilon),
    rho1=a beta/(3+a beta), rho3=c beta/(2+c beta),
    rho3<=rho1.                                     (W13)

At a point of the zero-hazard boundary, pair and triple roots agree. The
outer image lies strictly inside the physical graph region because

    rho3 k_beta(xi)<=rho1 k_beta(xi)<k_beta(rho1 xi)

for xi>0; the last inequality is strict concavity and k_beta(0)=0.

The whole sufficiently small physical graph region is invariant under the
triple map. Boundary inwardness alone would not prove this. For the interior
check fix xi>0 and parameterize the input by R=upsilon/xi. Write R' for
the triple output's odds ratio and xi' for its first odds coordinate. The
leading tangential projective map has positive derivative: its denominator
is positive on the physical interval and its determinant is the product of
the two positive-plane eigenvalues, hence positive. This derivative is
bounded away from zero on compact parameter sets and physical ratios.
The exact maps and the C2 graph give the same lower derivative bound for
all small beta and radius. Moreover xi'=O(beta xi) and d_R xi'=O(beta xi).
Since k_beta(s)/s=k_beta'(0)+O(s), its derivative in s is uniformly bounded.
Consequently the boundary defect

    R' - k_beta(xi')/xi'

has strictly positive derivative in R. At the input boundary it is strictly
negative by (W13) and concavity. It is therefore negative throughout the
physical interval. The coordinate axis v=0 maps into the positive interior,
and the origin maps to itself. This works uniformly across 2a=3c and the
possible double positive eigenvalue; no diagonalization of that plane is
used. Every resulting triple core step contracts by C beta.

## 4. A Banach operator produces every missing pair prefix at once

Let D={xi,upsilon>=0:xi+upsilon<=rho} for a sufficiently small radius. Write
T_beta(x) for the graph in odds coordinates. For the pair root at x put

    H(x)=(1-y)(1-w), b(x)=2y+w, d(x)=beta(y+w-yw).

Choose beta so Pi_beta(D) is contained in D and
max(rho1,rho3)/min_D H<1/2. On the complete space of continuous real V
on D with V(0)=0 and finite weighted norm sup_(x!=0)|V(x)|/|x|, define

    (UV)(x)=max(T_beta(x), [V(Pi_beta x)+b(x)]/H(x)). (W14)

This is a continuous operator on that space. Its weighted contraction factor
is at most max(rho1,rho3)/min H<1/2, since taking the maximum with a fixed
real number is 1-Lipschitz. The raw graph T_beta has a finite weighted norm,
so Banach's theorem produces a unique continuous Vhat_beta in odds
coordinates. No stopping index or switch sequence is input.

Here is why this algebraic fixed point selects legal roots. First Pi_beta
maps the WHOLE physical region Omega_beta into itself: if upsilon<=k_beta(xi),
then rho3 upsilon<=rho3 k_beta(xi)<=k_beta(rho1 xi).
Evaluate (W7) at the owner2-indifference input t=tcrit(x). The root has z=0,
so its outer output is Pi_beta x and its spectator output is d(x). Hence

    d(x)-T_beta(Pi_beta x)
       =K_beta(x,tcrit(x)) [tcrit(x)-T_beta(x)].      (W15)

On Omega_beta, tcrit<=T_beta and K_beta<0, so T_beta(Pi_beta x)<=d(x).
Also H T_beta-b>=d(x). Thus the pair branch of U T_beta is at most T_beta
there. Starting the Picard iteration at T_beta, every iterate remains exactly
T_beta on Omega_beta, using its Pi_beta-invariance. Outside Omega_beta,
(W15) instead gives T_beta(Pi_beta x)>d(x)>H T_beta(x)-b(x).
Therefore U T_beta>=T_beta everywhere, strictly outside Omega_beta.
Monotonicity of U shows that its fixed point satisfies Vhat_beta>=T_beta,
equals T_beta on Omega_beta, and uses the pair branch strictly outside.

Inside Omega_beta choose the physical triple root on the invariant graph.
Outside choose the pair root with spectator input Vhat_beta(x). Its output
is Vhat_beta(Pi_beta x), and

    Vhat_beta(Pi_beta x)>=T_beta(Pi_beta x)>d(x),

exactly its owner2 Continue-versus-Quit guard. All core output caps are
O(beta |x|). This constructs an actual physical contracting chain from
every sufficiently small nonnegative pair (u,v).

At a switching boundary, pair and triple agree because z=0; their cap
annotations agree because Vhat_beta=T_beta there and at its pair image.
Their passive outputs consequently agree too. There may be arbitrarily
many pair roots, including an infinite pair chain. Only finite approximations
of this backward chain will be used as strategies; no later date is scheduled
after an infinite prefix.

Joint parameter continuity follows directly from the continuous maximum in
(W14), finite Picard iterates, and uniform geometric convergence in weighted
norm. All constants can be common on compact parameter sets, including
2a=3c. For the rest of the proof use continuation-cap coordinates:

    V_beta(u,v)=Vhat_beta(u/(3+u),v/(2+v)).

As beta tends to zero, its small-scale tangent is

    V_beta(beta u,beta v)/beta
          -> V0(u,v)=max(Au+Bv,u/3+v)               (W16)

uniformly for (u,v) in fixed compact positive sets and parameters in a
compact subset. On the physical graph this follows from (W6). Outside,
(W14) gives V_beta(u,v)=(2y+w)/H+O(beta(u+v))
=u/3+v+O(beta(u+v)+(u+v)^2). The limiting physical boundary is exactly
Au+Bv=u/3+v, and the two expressions agree there. The weighted fixed-point
bound used here is uniform because T_beta has a uniform weighted bound.

## 5. Passive values and a continuous macro return

Against any positive passive0 cap p in a fixed compact interval, the local
root selected above updates

    p'=3y-z+3w+(1-y)(1-z)(1-w)p,

using z=0 on a pair step. Its forced-Quit value is O(y+z+w), with a uniform
upper bound from the row0 assumptions, while its Continue value stays away
from zero. Thus every local root is fully Nash for small enough beta and
radius. The passive increments have magnitude O(|x|), and all core outputs
contract by C beta. They have a continuous axis limit S=p+O(|x|).

For precision about continuity, the selected hazards and full annotations
are continuous at the switching boundary: there z=0, V_beta=T_beta, and
pair and triple roots are identical. Every finite passive iteration is
therefore continuous, and its tail error is bounded by C(C beta)^N|x|.
Uniform convergence proves continuity of S in the initial data and all
parameters. No smoothness of the hybrid graph is asserted or needed.

Use one exact macro parameter theta in [-1,1/8], and put

    z=max(theta,0), sigma=max(-theta,0),
    D=y+w-yw, U=z+w-zw, V=y+z-yz.                   (W17)

For z>0 use the triple root (W2). For z=0 use the pair root and prescribe
its spectator output to be beta(D+sigma). Its owner2 guard is then exactly
beta sigma>=0. In both cases impose the solo0 seam t=2(u-v)/3. This equation
is linear in y after clearing positive denominators. For the pair arm,

    y=[(3+(2a-3)beta)w-3beta sigma]
       /[10+2c beta+2(1+(a-c)beta)w+3beta(1-w)].     (W18)

For the triple arm, y=N/L with

    N=w(z+3)+beta[-2awz+2aw+2az+2cwz-2cz+3wz-3w],
    L=10+2w-8z
       +beta[-2awz+2aw+2az+2cwz-2cw-2cz+2c
              +3wz-3w-3z+3].                       (W19)

The arms agree at theta0. Uniformly in theta and parameters on a compact
set, as beta tends to zero,

    y -> y0=w(3+z)/(10+2w-8z).                      (W20)

All macro hazards are physical for small beta on the rectangle
1/5<=w<=1/4, 0<=z<=1/8; their remaining guards are verified in Section 7. Define a0=(u-v)/3 and r0=(u+2v)/(3-u+v); these lie strictly between
zero and1 there. The local core output is

    (a beta U, beta(D+sigma), c beta V).

Project its spectator coordinate to the produced hybrid graph for the
auxiliary passive-axis evaluation, and shoot the two continuous residuals

    E_beta=D+sigma-V_beta(a beta U,c beta V)/beta,
    R_beta=S-r0/(1-r0).                            (W21)

At E_beta=0 the auxiliary continuation is the actual continuation.

At beta0 the return equation has the common unique curve w=w0(z) in
(1/5,1/4), with nonzero derivative in w. Its cleared polynomial is

    P=6w^3z^2-12w^3z-30w^3-23w^2z^3+115w^2z^2-145w^2z-7w^2
      +8wz^4-141wz^3+863wz^2-1803wz+1205w
      +40z^4-250z^3+354z^2+70z-250.

Here is a self-contained exact sign certificate. On [1/5,1/4] times
[0,1/8], the Bernstein coefficients obey

    998667/1024 <= coefficients(P_w) <= 5993/5,
    -390 <= coefficients(P_z) <= -705771/4000.

Rescale the rectangle to [0,1]^2. For power coefficients d_pq of a polynomial
of bidegree(n,m), its (i,j) Bernstein coefficient is
sum_(p<=i,q<=j) d_pq binom(i,p)/binom(n,p) binom(j,q)/binom(m,q).
Direct rational substitution gives the bounds displayed; Bernstein weights
are nonnegative and sum to one. Thus P_w>960 and P_z<-150.
Also P(1/5,0)=-238/25<0 and P(1/4,1/8)=82413/8192>0. Monotonicity in z gives
opposite w-face signs for every z in the interval. Hence w0(z) exists,
is unique and continuous, and the return residual has a fixed nonzero
transverse derivative. More explicitly, at beta0 the return residual is

    p-r0/(1-r0)=-w P(w,z)/[2(-w+4z-5) J(w,z)],
    J=w^2 z^2-2w^2 z-5w^2+5w z^2-30wz+33w+8z-10.

Its denominator is nonzero on the rectangle: the original denominators
are positive and 3-2u-v>0 by the bounds in Section 7. Thus the factor
multiplying P is continuous, nonzero and has a fixed sign. A thin fixed tube therefore has
opposite return signs on its two transverse faces. For theta<0 set w0(theta)=w0(0). The beta0 shooting limit is

    E0=D+sigma-max(aA U+cB V, aU/3+cV).              (W22)

At theta=-1, z0 and sigma1, both expressions in the maximum are at most
w+2y<1/2 on the rectangle, so E0>1/2. At theta=1/8, sigma0, aA>1/2 and
cB>1 give

    E0<=D-U/2-V
       =w/2-yw+zw/2+yz-3z/2 <= -7/192,

using w<=1/4 and y<=1/12. These strict signs persist on a small return
tube and for all small positive beta by (W16). Poincare-Miranda supplies
an exact simultaneous zero of (W21). This single slack chart handles the
macro pair/triple transition without a case split or an assumed switching
orientation. Every constructed datum is fixed before the accuracy target.


## 6. The strict-cone alternative

Now assume (C1); the graph and switching construction in Sections 1-5 are
not needed in this region. The following cone directly produces the wash.

For x=(u,t,v), use the same exact cap map F_beta=Q_beta o I_beta^{-1}
from (W2)-(W3), now under (C1). Put

    N=P G^(-1)
     =[0,a,-a; 1/8,5/8,-1/8; -3c/8,9c/8,-5c/8].

Then

    D F_beta(0)=beta N(I+beta N)^(-1),
    F_beta(x)=beta N x+O(beta(beta+|x|)|x|).          (C2)

The error and its first derivative are bounded on a fixed neighborhood
for fixed a,c. All these formulas follow from the analytic inverse
function theorem and the displayed rational map.

### The cone is produced by two explicit linear forms

Define

    L(u,v)=u/3+v, H(u,v)=u/a+v/c,
    K={u,v>=0, L(u,v)<=t<=H(u,v)}.

Condition(C1) implies a<15/8<3 and c<1, so H>L on every nonzero positive
quadrant vector. The leading triple hazards are

    y=(-u+3t+v)/8, z=(-u+3t-3v)/4, w=(u+t-v)/4.

They are nonnegative throughout K. For x'=Nx,

    H(u',v')-t'=3(t-L(u,v))/2.                     (C3)

The lower slack t'-L(u',v') is linear in t. Its values at the two
boundary planes are

    t=L: (3-a)u/9+(1-c)v/2,

    t=H: (3-a)(5-9c)u/(24a)
           +(1-c)(15(1-c)-8a)v/(24c).              (C4)

Both are strictly positive when u+v>0, by(C1). These identities prove
invariance, including the entire range of v/u; no sampled trajectories
or unproduced invariant graph are used.

For a sufficiently small fixed e>0, replace K by

    K_e={u,v>=0, L(u,v)+e(u+v)<=t<=H(u,v)}.

The positive margins in(C4) persist. Equation(C3) is now also strict.
Furthermore u'=a(t-v)>0 and
v'=c(-3u+9t-5v)/8>0 for every nonzero x in K_e. Thus N sends the
compact normalized section of K_e strictly into its interior, with all
three leading hazards positive. The exact map(C2) preserves this cone
for sufficiently small beta and |x|, and satisfies

    |F_beta(x)|<=C beta |x|, C beta<=1/2.            (C5)

This proves a physical infinite backward triple chain from every small
nonzero x in K_e. It also proves summability of its hazards.

### Actual macroscopic entrance and return

At the first, macroscopic pair13 root, use w in[1/5,1/4] and

    y_beta(w)=w[3+(2a-3)beta]
      /[10+(2c+3)beta+w(2+(2a-2c-3)beta)].          (C6)

This is the exact solo0 seam t=2(u-v)/3, with

    u=(3+a beta)w/(1-w),
    v=(2+c beta)y/(1-y),
    t=[beta(y+w-yw)+2y+w]/[(1-y)(1-w)].

Owners1,3 are indifferent. Owner2 is also indifferent at its Continue
boundary. The root outputs

    (p,x)=(3(y+w), beta(a w,D,c y)),
    D=y+w-yw.

The normalized core vector is strictly inside K. Indeed

    H(a w,c y)-D=yw>0,
    D-L(a w,c y)=(1-a/3)w+(1-c)y-yw>0.            (C7)

For the second inequality, a<15/8 gives 1-a/3>3/8, while y<1/10 on
this macro interval for small beta. The first margin is uniformly positive
on the interval. Choose the e in K_e still smaller so the whole macro
input belongs to K_e, then choose beta small enough for(C5).

At a small triple root the passive coordinate obeys

    p_next=3y-z+3w+(1-y)(1-z)(1-w)p.

If |p|<=B then |p_next-p|<=(3+B)(y+z+w). Geometric contraction(C5)
bounds the sum of hazards by O(beta) for the macroscopic initial data.
A first-exit estimate therefore keeps p in a fixed positive compact
interval. The summable increments give a continuous limit
(S_beta(w),0,0,0), with

    S_beta(w)=3(y_0(w)+w)+O(beta),
    y_0(w)=3w/(10+2w),

uniformly on[1/5,1/4]. The solo0 parameters are

    a0=(u-v)/3, r=(u+2v)/(3-u+v),

with 0<a0,r<1 and u,v>0 there. The return residual
S_beta(w)-r/(1-r) has opposite strict endpoint signs for small beta.
At beta0 its cleared zero is

    -30w^3-7w^2+1205w-250=0,

whose derivative is positive on the interval and whose endpoint signs
are opposite. The intermediate value theorem therefore produces an
actual return. Fix one such root before choosing any approximation error.


## 7. Full-game guards, the second wash, and unrestricted deviations

In both regions, the macro root has input V=(0,u,2a0,v), where

    a0=(u-v)/3, r=(u+2v)/(3-u+v).

It outputs P0=(p,core), with p=3y-z+3w and core on the constructed
contracting chain. That chain tends to Q=(S,0,0,0), and the selected
return is S=r/(1-r). The core is the exact cone chain in Section 6 or
the exact hybrid chain in Sections 1-5. The following proof is common.

At beta0 on the macro rectangle, u lies in[19/28,1], and

    2y-z=(6w-10z+8z^2)/(10+2w-8z)>=1/140,
    0<v<=2/13, a0>=191/1092, a0<=1/3,
    2u+v<=28/13<3.

For the bound v<=2/13, multiply its positive denominator: the difference
is 20-80w+94z-(88-2w)z^2>=0 on the rectangle. These bounds give positive
uniform margins for u,v,a0,r and 1-r, and persist for small beta.

At any macro root, player0's forced-Quit endpoint is at most
1-(1-y)(1-z)(1-w)+9yzw. Its Continue endpoint is p. For
w in[1/5,1/4], z in[0,1/8], 0<=y<=1/12, their difference is at least

    2y-2z+2w+yz+yw+zw-10yzw>=119/960>0.

The small-beta perturbations preserve a strict margin. On the cone's
macro pair this is also immediate from 3(y+w)>y+w-yw. At every small
core root, the positive passive value and summable hazard bound proved
above give the same full-game guard: the forced-Quit endpoint is at most
y+z+w+10yzw and is below the Continue value. The active owners are
indifferent; the hybrid pair's inactive owner2 is safe by (W15). Thus every
macro and small core root is exact Nash against its displayed annotation.

Write r=r0 for the wedge return, and use the cone return r in the other
region. Let L=(0,r,0,r) and V=(0,u,2a0,v). The solo0 root with hazard a0
outputs V because u=(1-a0)r+2a0 and v=(1-a0)r-a0. Player0 is
indifferent at zero. Owners1,2,3 Continue if respectively

    u>=a0 a beta, 2a0>=a0 beta, v>=a0 c beta.

They do so for small beta, uniformly on the compact macro interval,
because u,v,a0 stay in positive compact intervals there.

### The second contracting block is explicit

Write alpha=Z0({0,2})<=1 and alpha_plus=max(alpha,0). Starting at
Q=(S,0,0,0), use solo2 roots at continuation(B,h,0,h), with hazard

    k=B/(1+alpha_plus+B).

Their output is

    (alpha_plus k, k+(1-k)h, 0, k+(1-k)h).

Owner2 is indifferent. Owner0's Continue value equals alpha_plus k and
is at least its actual Quit value alpha k. Owners1,3 Continue because
max(a beta,c beta)<=1. With rho=alpha_plus/(1+alpha_plus)<=1/2,
iteration gives the exact formulas

    B_m=S rho^m/[1+S(1-rho^m)],
    h_m=(S-B_m)/(1+S).

The limit is L because S=r/(1-r). The first backwards solo2 hazard is
S/(1+alpha_plus+S)>0. Thus both washes and their common return have been
produced from raw rewards.

### Finite strategies and the full behavioral cap

For finite lengths M,N>=1, execute and repeat the finite chronological
word

    solo0, solo2_(M-1),...,solo2_0,
    core_(N-1),...,core_0, macro-root.

Each root is exact Nash against its displayed next annotation. There
are only two mismatches: solo0 expects L rather than the finite solo2
output Q_M, and solo2_0 expects Q rather than the finite core output
P_N. Put

    E=||Q_M-L||_infty+||P_N-Q||_infty.

Then E tends to zero as M,N tend to infinity. In every period, the
opponents of any one player absorb with probability at least

    delta_abs=min(a0,S/(1+alpha_plus+S))>0:

use the designated solo2 root for player0, and solo0 for every other
player. These are independent behavioral coins scheduled at deterministic
dates, so the bound holds after any complete unilateral replacement.

For clarity, the two-seam estimate follows directly from finite Bellman
telescoping. At each non-seam root, the prescribed action value equals
its annotation, and either pure action has value at most that annotation
when its Continue branch is assigned the next annotation. At a seam,
replacing that continuation annotation costs at most its sup norm error.
Multiply each one-step equality or upper inequality by the probability
that the game is still live under the profile or replacement strategy,
then sum. Each seam's total survival weight over all repeated periods
is at most sum_(k>=0)(1-delta_abs)^k=1/delta_abs. The final continuation
term tends to zero because all annotations are bounded and opponents
absorb geometrically. Thus prescribed terminal payoff differs from V
by at most E/delta_abs, while every unilateral terminal payoff is at
most V_i+E/delta_abs. Every complete behavioral deviation gain is at
most 2E/delta_abs. This includes finite deadlines, Never and arbitrary
mixtures; no bounded-memory restriction is imposed.

Every unilateral replacement absorbs surely, so original terminal
payoffs and caps are ell_i plus their native values. Fix the target
ell+V, independent of accuracy. For an accuracy, choose M,N to make
the seam bound small and then keep that finite word fixed. Its opponent
absorption time has a finite expectation uniformly over all unilateral
replacements. If original finite rewards have absolute bound R, the
expected discrepancy between finite-horizon average and terminal payoff
is at most 2R E[min(tau,T)]/T, where tau counts the stages before the first absorbed-reward stage. It tends
uniformly to zero as T tends to infinity. This proves the original
uniform-equilibrium contract with target ell+V.

The queried rewards are exhausted by this check. A macro root or small
core root uses subcoalitions of{1,2,3}, and player0's deviation adds0;
only its own grand coordinate can appear. Solo0 and solo2 roots query
only singleton rewards and two-player participant rewards. The three
other grand coordinates are never queried, even under their owner's
unilateral replacement. Freely lowering row0 rewards only improves its
Quit inequalities. Its solo2 rule uses alpha_plus in[0,1]. Therefore
all claimed scale thresholds are independent of these unconstrained
values and of ell; the eventual horizon threshold may depend on the
finite original reward magnitudes.

All strict margins and analytic bounds are uniform on compact subsets of
the respective parameter regions. In the cone case choose a common positive
e and cone margin. In the wedge case the C2 graph, concavity bounds, and
hybrid contraction have common constants, including at 2a=3c. The macro
return signs and the common finite-word consumer then give the asserted
compact-parameter uniformity. No infinite calendar is
executed: the infinite washes only produce the limiting annotations;
each strategy used for an accuracy is finite periodic.

## 8. Exact calibration and comparison with existing mechanisms

The constructions above exclude actual reward tables beyond the previously
available small-relative-premium, pure pair-contraction, and equal-premium
criteria. The following complete family gives exact comparisons, including
the full stationary and sure-owner/punishment selections.

Take original own singleton rewards all equal to1, original live and Never
rewards zero, native singleton matrix

    Gamma=[0,3,-1,3; 2,0,1,-3; 2,-2,0,-1; -1,-2,1,0],

and every passive native reward equal to the sum of its singleton entries.
Every proper nonsingleton participant reward in rows0,1,2,3 is respectively

    e,h1,e,h3,  0<e<=1/100, 0<h1,h3<=1/2000.

The native grand reward is(10,-2,-e,-1). Adding1 to these native values
specifies all sixty original rewards. Put h=max(h1,h3). Two exact rays are

    (e,h1,h3)=(beta,(29/10)beta,(11/10)beta),
    (e,h1,h3)=(beta,beta,beta/10),
    0<beta<=1/6000.                                    (E1)

The first ray belongs to the closed wedge and the second to the
positive-cone region: for(a,c)=(1,1/10), c<5/9 and
8a<15(1-c). For either ray choose any positive rational beta below its
produced existence threshold and1/6000. This does not assert that an
arbitrary displayed beta lies below a threshold produced nonnumerically.

### Every sure-owner root, including every feasible punishment tail

Write q=(x,y,z,w), H_i=product_(j!=i)(1-q_j), D_i=1-H_i,
J_i=D_i product_(j!=i)q_j. The native forced-Quit and passive endpoints are

    Q0=eD0+(10-e)yzw, Q1=h1 D1-(2+h1)xzw,
    Q2=eD2-2exyw,    Q3=h3 D3-(1+h3)xyz,
    P=Gamma q, g_i=Q_i-P_i.                            (E2)

If owner i is sure, every other owner compares exactly Q_j and P_j,
independently of the tail. The sure owner's gap is g_i-H_i v_i, where
v_i is its original continuation minus1. Every original row2 reward is
at least-2, so every actual continuation, full response cap and punishment
value has v2>=-3. That is the only tail bound needed below.

If x=1, then

    g3=1+2y-z(1+y)+h3(1-yz)>=y+h3(1-y)>0,

so w=1. The remaining free equations force y=1/2 and
z=(1+h1)/(3+h1); the boundary y=0 instead forces z=0 and then y=1,
and y=1 is excluded by the next case. At this free solution the sure0 gap
is e-9/2+(6-e/2)z<0. If y=1, g2>=e>0 forces z=1,
g3=1+h3(1-x)>0 forces w=1, and g0=5 forces x=1; but then g1=-2.
Thus x,y<1 in all remaining sure cases.

If z=w=1, their free equations force

    x=(2+h1)/(4+h1), y=(2-e)/(7-e).

The endpoints x=0 or y=0 cannot be equilibria: x=0 gives g1>0 and
forces y=1; y=0 has g0=e-2<0, forcing x=0. Over the positive denominator
(4+h1)(7-e), the numerator of g3 at the free solution is

    -e h1-2e h3-4e+5h1h3+2h1+24h3-2<0.               (E3)

Its positive part is at most26/2000+5/4000000<2.

For z=1 alone, w=0 forces y=0 and then x=1, already excluded.
Thus 0<w<1, and g3=0 gives

    y=(1-h3-x)/(2-(1+h3)x).

If y=0, the free solution is x=1-h3,w=(1+e)/3. Even at v2=-3,

    g2+3H2=(4e-5)/3+h3(4-5e/3+e^2/3)<0.

If y>0, then g1=0 gives w=(2x+1-h1)/(3-(2+h1)x), so
0<=x<(2+h1)/(4+h1)<51/100. Both denominators are positive.
Multiplying g0 by them gives N=N0+h1 A+h3 B+h1h3 C, where

    N0=4ex^2-8ex+5e-18x^2+9x+1,
    A=ex^2-3ex+e-2x^2+8x-4,
    B=2ex^2-ex+e+8x^2-26x-1,
    C=ex^2-e+x^2-6x+10.

Here N0>=4541/5000 on the stated interval. For 0<=x,e<=1,
the absolute coefficient sums give |A|<=19, |B|<=39, |C|<=19.
Consequently N>=4541/5000-58/2000-19/4000000>0, contradicting x<1.

For w=1 alone, z=0 forces x=0 and then z=1, impossible. Hence
0<z<1, and g2=0 gives y=(2x-1-e)/(2(1-ex)), so x>1/2.
If y=0, g0=e+z-3<0. Otherwise g1=0 gives
z=(3+h1-2x)/(1+(2+h1)x). Multiplying g0 by the two positive
denominators gives

    N3=-52x^2+64x-27
       +e(20x^2+22x-22)+e^2(-4x^2-4x+3)
       +h1(-2e^2x^2+e^2+6ex^2+ex-9e-6x^2+17x-8).

On1/2<=x<=1, N3<=-95/13+20e+32h1<0, contradicting x>0.
This exhausts all sure-owner faces and all feasible punishment tails.

In particular it rejects the complete selection in
`HasQuittingPunishmentVectorNashRootWithSureQuitter` in
`UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean`.
No joint profile realizing a coordinatewise punishment vector is assumed.

### Every stationary support

Against positive opponent activity, a stationary best response has endpoint
sign F_i=D_i Q_i-P_i: proper positive hazards require F_i=0 and zero
hazards require F_i<=0. AllContinue fails because original own singletons
are1. Sure hazards have already been excluded. Define

    E=D2^2-2J2, E1=h1(D1^2-J1), E3=h3(D3^2-J3).

Then E1,E3>=0 and

    F0=eD0^2+(10-e)J0-3y+z-3w,
    F1=-2J1+E1-2x-z+3w,
    F2=eE-2x+2y+w,
    F3=-J3+E3+x+2y-z.                                  (E4)

If x=0, F2>0 unless y=w=0; in that case F0>0 unless all hazards
vanish. Thus x>0. If z=0, F3>0, so z>0. If w=0, then
F1<=h1(x+z)-2x-z<0, forcing y=0; now F0>0. Therefore x,z,w>0.
If y=0, their active equalities imply

    z>=(3-e)w/(1+e), x<=(1+e)w/(2-e),
    z<=(1+h3)x/(1-h3),

which are incompatible already for e<=1/4,h3<=1/10. All remaining
stationary candidates are fully mixed.

Put t=y/x and b=z/x. Equations(E4) give

    w<=2x-2(1-e)y,
    (3+h)w>=(2-h)x+(1-h)z.

Hence t<(4+3h)/(2(3+h)(1-e))<3/4. The row3 equation gives
b<=((1+h)+(2+h)t)/(1-h)<3, and w/x<=2. It follows that

    D0^2/x<6, E1/x<6h, |E|/x<6.

Set A=4-6t-b, C=6-3t-b, k=(10-e)/2. The first two equalities imply

    xA=2J1-E1+3eE,
    xC=(10-e)J0+eD0^2+3eE.

Since x>y, D1>D0 and J0<tJ1. Therefore

    C-ktA < kt E1/x+e[D0^2+3(1-kt)E]/x
           <=(45/2)h+60e.                             (E5)

On the other hand C-5tA=30t^2-23t+6+(5t-1)b.
For t>=1/5 this is at least191/120 by completing the square.
For t<1/5, the formula for A gives b<=4-6t+6h+18e, hence
C-5tA>=2-6h-18e>191/120. Since |A|<=5,

    C-ktA>=191/120-(5/2)e>=47/30,

contradicting(E5). Thus no stationary terminal Nash profile exists.
This is a complete stationary exclusion, not a positive unrestricted gap.

### Protected sets and every nonnegative weight selection

Only player0 has nonnegative participant premiums at every coalition;
the other three grand premiums are negative. The pair13 is a premium
trap disjoint from{0}, and the full four-player set is a premium trap.
Thus every protected-player selection fails the strict or weak leaver test,
and a greatest-core-of-size-at-most-two criterion cannot apply. These are
the predicates `HasProtectedParticipantPremiums`,
`HasSupportSpecificQuittingLeavers`, and `quittingMaximalProtectedPlayers`
in `UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`.

No nonzero nonnegative weight vector k can have k dot Z(A)>=0 at every
proper nonempty coalition. Coalitions013,01,{2},03 respectively imply

    k2<=e k0+h(k1+k3), 3k3<=e k0+h k1,
    k0<=k1+k3, k1<=e k0+k2+h k3.

Combining these gives
(1-h-2h^2/3)k1<=e(2+2h/3)k0, hence k1<=3e k0 and
k3<=e k0/2. Then k0<=7e k0/2 forces all weights to vanish.

The support-filtered joining tests also fail for every nonnegative weight.
Their sums

    J_k(A)=sum_(i notin A) k_i[Z_i(A union{i})-Z_i(A)]<=0

at A=123,013,012 force k0=k2=k3=0: the missing-owner joining gaps
are respectively5,1-e,1. Nonnegative weighted payoff at singleton3
then requires -3k1>=0. No calendar or orientation selection rescues these
necessary weight inequalities.

### Every proper child, with unrestricted child debts

For every proper nonempty child there are actual child profiles whose full
unilateral debts vanish while a quiet outsider's debt stays positive.
For each singleton child use its owner geometrically with hazard1/2.
Every column of Gamma has a negative outsider, whose native Quit-now
payoff is nonnegative. For the other children, j means the sole geometric
owner j, while13 means both owners quit surely:

| Child | Child profile | Violating outsider |
| --- | --- | --- |
| 01,02,012 | 0 | 3 |
| 03 | 3 | 1 |
| 12,23 | 2 | 0 |
| 13,013 | 13 | 2 |

Every quiet child member in a sole-owner row receives at least1 natively,
above its joining premium. With sure13, child owner0 receives6 rather than
joining for e, while outsider2 gains3+e. These are exact child equilibria
against arbitrary complete stopping laws.

For child123 use one root

    q1=(1-h3)/2, q2=1, q3=(1-h1)/3,

followed by Never. Owners1,3 are indifferent; owner2 strictly prefers
Quit to every delay. Outsider0's joining gain is

    [1+5e+(e-4)h1+(e-1)h3+(10-e)h1h3]/6>0,            (E6)

whose numerator is at least1-4h1-h3>0.

For the remaining child023, repeat solo owners3,0,2 with cumulative
hazards5/12,5/14,5/9. In coordinate order0,2,3, the values before the
three phases are respectively

    (5/4,0,0), (0,5/7,0), (0,0,5/9).

These solve the Bellman equalities exactly. Subdivide each solo phase,
preserving its cumulative survival, until every hazard is at most delta.
All intermediate values are nonnegative and equal their Continue branches;
an active owner's value stays zero. Every native forced-Quit endpoint is
at most M delta, M=max(e,h1,h3). Adding M delta to every value coordinate
is therefore a full-cap supersolution. Each player's opponents absorb
with positive probability per period, so geometric telescoping removes
the remainder and every child debt is at most M delta.

The terminal singleton probabilities at0,2,3 are exactly1/4,1/4,1/2.
Quiet outsider1 consequently receives native payoff-3/4. Prepend an empty
date. Child debts keep their bound, while outsider1 can Quit there for
native zero, retaining gap at least3/4. Adding the original own levels is
exact here because prescribed play and the relevant unilateral replacements
absorb surely.

This exhausts all fourteen nonempty proper children. Hence no selection of
a child and finite debt weights can give a universal bound of outsider debt
by child debts. In particular all five kinds of
`WithdrawalFutureJoinRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`
fail to supply
`quittingLiftDeletedProfile_outsideDebt_le_of_withdrawalFutureJoin` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`.
This excludes the all-child-profile consumer; it does not exclude a different
method selecting a specially favorable child profile.

### Additional complete finite selections

The only mutually negative singleton pair is13. A perfect matching whose
every participant has positive joining displacement is impossible: for
01|23,02|13,03|12, respectively use the negative displacements
e-3 at(row0,01), e-2 at(row2,02), e-3 at(row0,03).
Strictly positive proper participant premiums also reject any raw criterion
requiring a nonpositive participant premium on a selected proper coalition.

There is no exact finite periodic terminal Nash profile all of whose roots
have support of size at most two. Before a first sure root, every phase
is reached with positive survival, so exact Nash passes to its conditional
tail. The sure-root census excludes such a first sure root. Consequently
every phase is reached and has an exact Nash tail. Its native Quit-now payoff
is nonnegative because any simultaneous coalition formed by that deviation
is proper. Thus every phase's native Nash payoff is nonnegative. Every
pair except13 has a participant whose passive singleton reward is at least1,
strictly above its positive joining premium; that participant cannot Quit
with positive probability against a nonnegative continuation. The sure-owner census above excludes every reachable sure root, so all
positive hazards in such an exact profile are proper. A solo phase
of owner j forces its next native continuation value to zero. Until the
first later phase involving another owner, repeated solo-j or empty phases
preserve that zero. At that first other-owner phase, j's Quit-now endpoint
is strictly positive, a contradiction. If no other owner ever acts, a
negative singleton outsider violates Nash. Only13 phases therefore remain,
but quiet owner2 then has strictly negative native payoff and a nonnegative
Quit-now endpoint. This excludes that entire exact finite architecture,
without asserting anything about its approximate variants.

The principal minors of Gamma at sizes2,3,4 are respectively

    (-6,2,3,2,-6,1), (10,-3,5,8), 25,

in lexicographic support order. All are nonzero. Hence a homogeneous
complementary solution cannot have support of size at least two; every
singleton support has a negative outside column entry and is impossible
as well. Thus Gamma is R0. At LCP offset+(1,1,1,1), the only solution is
the empty support: every support of size at least two except13 has a negative active coordinate
in -Gamma_SS^{-1}1, while support13 gives active coordinates(1/2,1/3)
and outside slack -1/3 in row2. Singletons cannot solve their active
equation. The empty root is strict with index+1, so the R0 degree is+1.
No negative-degree or homogeneous-root exit applies.

The only principal triple with nonnegative inverse is023:

    Gamma_023^{-1}=(1/5)[1,3,1; 1,3,6; 2,1,2].

The other triples012,013,123 have negative inverse entries -1/5,-1,-3/8,
respectively.
Its exterior inverse row is
Gamma_{1,023} Gamma_023^{-1}=(-3,6,2)/5, which is not nonnegative.
This rejects the complete selection in
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
The omitted-owner column(3,-2,-2) separately fails an all-negative pivot
condition. The principal13 matrix is neither standard Q nor homogeneous
complementary: offset(-1,-1) has no solution, and nonnegative x with
Gamma_13 x>=0 must be zero. Thus a projective-Q-bar principal criterion
also fails.

Every nondiscrete response-invariant quotient fails already in the linear
part -Gamma q of(E4), even allowing positive constant row rescalings.
For each partition below, merge the first pair in its first nonsingleton
block and take its first two block coordinates. The two row-sum vectors
have the following nonzero determinant:

| Partition | Determinant |
| --- | --- |
| 01\|2\|3 | 5 |
| 1\|02\|3 | 4 |
| 1\|2\|03 | 1 |
| 0\|12\|3 | -6 |
| 012\|3 | -15 |
| 12\|03 | -1 |
| 0\|2\|13 | 3 |
| 02\|13 | -9 |
| 2\|013 | -5 |
| 0\|1\|23 | -6 |
| 01\|23 | -10 |
| 1\|023 | 7 |
| 0\|123 | -2 |

The one-block row sums(5,0,-1,-2) are not positive rescalings either.
This exhausts every nondiscrete partition.

### Why both new rays add raw coverage

For both rays(E1), max(h1,h3)>e/250, rejecting the quantitative
small-relative-premium test. The signed-chamber small-premium test at this
background requires max(h1,h3)<=3e/11200, also false. The pair-contraction
test requires both e<=h3 and e<=h1/3; its second requirement fails on both
rays. The equal-premium independent-scale rectangle requires h1=h3.

There is no untested relabeling for the signed-chamber tests. Their required
singleton pattern is

    [0,g1,-g2,g3; k,0,1,-c0; A,-h0,0,-h3; -l,-d,1,0],

where g2,g3,k,A,h3,l,c0,d>0. Its role3 must be original2 or original3,
since it needs two negative entries. If role3=2, its positive target forces
role2=0 and the remaining two-positive role1 is original1; its entry toward
original2 has the wrong sign. If role3=3, its positive target forces role2=2,
and role1's negative entry toward3 forces role1=1, leaving role0=0.
Thus the identity is the only embedding. It is also the only embedding
of the literal fixed-matrix tests.

Positive row rescaling does not evade these inequalities. Rows1,3 are
normalized by their positive singleton entry, restoring their displayed
premiums. The small-premium constants here are K=7, xi0=1/100,
H0=4/3 and kappa=min(1,xi0/(4H0 K))=3/11200.
Scaling row2 by s>0 changes H0 to4s/3 and gives
kappa<=3/(11200s), while its minimum participant premium
is s e. Thus its allowed kappa b remains at most3e/11200. The pair
inequalities scale on both sides equally. The two new rays therefore
exclude additional actual tables rather than reproducing these raw classes.

These comparisons exhaust the indicated selectors, not every conceivable
equilibrium certificate. They do not identify any calibration as a
counterexample: the constructions above produce its uniform equilibrium.

## 9. Source correspondence and formalization handoff

The target is `quittingUniformEquilibriumPayoffConjecture` in
`UniformEquilibrium/Quitting/Conjecture/Basic.lean`. Its arbitrary-table
four-player instance remains open. The named source is a proposition,
not a proof of that target.

The checked semantic endpoint
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
consumes terminal approximate Nash profiles at every positive error.
Section 7 constructs those profiles and also proves the stronger fixed-target
uniform-horizon conclusion directly. The source's quantification over complete
behavioral replacements agrees with the finite-word cap argument here.
No new Lean declaration is asserted by this mathematical proof.

A formalization can separate the exact core maps and cone identities,
the finite-dimensional C2 graph transform, the concave physical boundary,
the weighted-sup contraction producing the hybrid cap graph, the two-variable
macro return, and the two-seam consumer. Its main theorem should take only
the displayed finite reward equalities/inequalities, positive scale and raw
ratio conditions; it should conclude the existence of a uniform-equilibrium
payoff. The invariant graph, root calendar and return must be constructed
in the proof, not included as hypotheses or structure fields. Finite algebraic
boundary checks are (C3)-(C4), (W11)-(W13), and the Bernstein macro signs.
The all-deviation consumer is the bridge to the existing semantic endpoint.

These two regions do not cover arbitrary premium ratios or arbitrary four-player
reward tables. The thresholds are uniform on compact subsets of the stated
regions, not one asserted global threshold over their entire union. The
construction gives approximate finite periodic profiles; the comparison above
shows why exact short-support periodic Nash profiles are insufficient even
on the calibration family.
