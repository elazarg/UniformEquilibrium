# Uniform physical cores across switching boundaries

Owner: CODEX_UNIFORM_JOINS.

**Complete internal ordinary-mathematics argument.** Independent review status
is recorded in the accompanying feedback. This is not an export or a Lean
theorem.
Fin4 remains open. Uniformity on every compact positive ratio set is proved
below only for the original additive calibration. No threshold on the whole
positive three-premium cube or arbitrary-table closure is claimed.

The contribution is uniformity through the switching boundaries, together
with a compact-cover theorem for the original additive calibration; separate
fixed-ratio thresholds do not supply these conclusions. This note is the
canonical combined record: it retains the core proofs and applies the existing exact return and
behavioral consumer, without copying their complete geometry again.

## 1. Raw data and uniform conclusions

There are four players0,1,2,3, one live state, and independent private
Continue/Quit choices at each live date. The first nonempty quitting coalition
A absorbs at its finite reward vector r(A). Live and literal Never pay zero.
A unilateral deviation may replace its player's complete behavioral law,
including arbitrary stopping dates and Never. There is no public correlation.

Put ell_i=r_i({i}) and Z_i(A)=r_i(A)-ell_i for nonempty A only. The levels
ell are arbitrary signed numbers; neither live nor Never is shifted. Require

    Gamma=[0,3,-1,3;2,0,1,-3;2,-2,0,-1;-1,-2,1,0]

as the native singleton matrix, and exactly these seven passive nonsingletons:

    Z0(12)=2,Z0(13)=6,Z0(23)=2,Z0(123)=5,
    Z1(23)=-2,Z2(13)=-3,Z3(12)=-1.

The nine core participant entries are

    Z1(12)=Z1(13)=Z1(123)=a beta,
    Z2(12)=Z2(23)=Z2(123)=beta,
    Z3(13)=Z3(23)=Z3(123)=c beta.

The six proper participant entries in row0 are arbitrary finite numbers at
most1. Its native grand reward is any finite number at most10. Every unlisted
nonsingleton coordinate is arbitrary finite data, including participant
entries containing0 in rows1,2,3 and their grand rewards.

**Corner theorem.** There exist epsilon,beta0>0 such that every table above
with

    |a-3|<=epsilon, |c-1|<=epsilon, 0<beta<beta0                 (C1)

has a uniform-equilibrium payoff. These are single constants for the entire
closed box, including both sides of a=3 and c=1. The ratios may depend
arbitrarily on beta within that box.

**Two-sided a=3 theorem.** For every 0<c_-<=c_+<infinity, there exist eta,beta1>0
such that every table above with

    3-eta<=a<=3+eta, c_-<=c<=c_+, 0<beta<beta1                  (R1)

has a uniform-equilibrium payoff. Neither beta1 nor the core radius depends
on the number of triple steps on the right, which may diverge as a
decreases to3. Below c=1 the left side uses an analytic graph; above c=1
the dynamic region below supplies it.

**Two-sided c=1 theorem.** For every 0<a_-<=a_+<infinity, there exist eta,beta2>0
such that every table above with

    a_-<=a<=a_+, 1-eta<=c<=1+eta, 0<beta<beta2                  (R2)

has a uniform-equilibrium payoff. One threshold and one core radius work
on both sides of c=1. The upper-side producer permits arbitrary pair/triple
switchbacks and assumes no eventual invariant pair tail.

**Dynamic-region theorem.** For every compact subset K of

    0<a<=3, c>1,                                               (N0)

one positive beta_K works for every table above with(a,c) in K and
0<beta<beta_K. The compact set may meet a=3. Pair steps may return to
triples; no invariant pair-tail premise or sign restriction on2a-3c is used.

These thresholds are independent of ell and of all free reward coordinates.
The flow mesh and finite-horizon threshold may depend on the magnitudes of
those finite rewards. The conclusion is one fixed payoff target for each
game before accuracy is chosen: for every positive accuracy there is one
behavioral profile delivering that target and bounding every full unilateral
deviation over all sufficiently long finite horizons.

**Original-calibration corollary.** For the narrower fully specified additive
calibration in Section9, every compact K contained in(0,infinity)^2 has one
beta_K>0 valid for all(a,c) in K. This corollary does not inherit the free
reward coordinates allowed in the four local statements above.

## 2. Common core data and the consumer required

For hazards q=(y,z,w) of players1,2,3, the exact triple input and output are

    I1=[a beta(z+w-zw)-z+3w]/[(1-z)(1-w)],
    I2=[beta(y+w-yw)+2y+w]/[(1-y)(1-w)],
    I3=[c beta(y+z-yz)-z+2y]/[(1-y)(1-z)],
    Q=beta(a(z+w-zw),y+w-yw,c(y+z-yz)).

Here input caps are(u,t,v). Put

    G=[0,-1,3;2,0,1;2,-1,0],
    P=[0,a,a;1,0,1;c,c,0], N=P G^-1.

The exact pair surface is

    Psi_beta(u,v)=u/3+v+k_beta uv,
    k_beta=(9+a beta+3c beta)/(3(6+2a beta+3c beta)).             (C2)

Each proof below produces a continuous graph t=T_beta(u,v) on one fixed
small quadrant u,v>=0,u+v<=rho, with

    Psi_beta<=T_beta<=C(u+v).

Each graph point has an actual selected pair13 or triple123 root, allowing
zero hazards, whose output is on the graph again. The roots are continuous
in their inputs, outer caps contract by C beta, and hazards are O(u+v),
with constants common on the relevant parameter set. For passive0 cap p
in a fixed positive compact interval, all roots are fully Nash and have a
continuous positive axis limit satisfying

    S_beta(p,u,v)=p+O(u+v).                                     (C3)

The exact return geometry and the unrestricted behavioral consumer are
already proved in Sections2--4 of
[CROSSED_PREMIUM_HYBRID_DIFFUSE_FLOW_UNIFORM_EQUILIBRIUM.md](../exports/CROSSED_PREMIUM_HYBRID_DIFFUSE_FLOW_UNIFORM_EQUILIBRIUM.md).
Section8 below checks every new uniform input to that consumer explicitly.
Only its supplied data interface is reused; all graphs here are constructed
from the raw rewards.

## 3. A dynamic pair/triple graph on the full corner box

A pair step in this construction may return to a triple step. It is not
required to start an infinite pair wash. We produce the common core interface
on(C1), with T_beta=Psi_beta at exactly(a,c)=(3,1).

### Exact one-step complementarity

For input outer caps x=(u,v) and trial z>=0, solve the player1 and3
indifference equations by

    y=[v(1-z)+(1-c beta)z]/[2+(v+c beta)(1-z)],
    w=[u(1-z)+(1-a beta)z]/[3+(u+a beta)(1-z)].                   (C4)

Write q_x(z)=(y,z,w), and define

    K1=a(z+w-zw), K3=c(y+z-yz), W=y+w-yw,
    J=[beta W+2y+w]/[(1-y)(1-w)].                               (C5)

Thus the outer output is beta K=(beta K1,beta K3), the triple player2
output is beta W, and the triple input height is J. All these maps are
smooth on a common small real neighborhood. Their formulas remain smooth
at beta0.

At z=0, put P=(1-y)(1-w). The exact pair identity is

    P Psi_beta(u,v)-2y-w=Psi_beta(beta K1,beta K3).               (C6)

For a candidate nonnegative correction h, put T=Psi_beta+h and

    R_h(x,z)=W-Psi_beta(beta K)/beta-h(beta K)/beta.              (C7)

The smooth part R_0 has the exact boundary value

    R_0(x,0)=-g,
    g=(c-1)y-(1-a/3)w+(1+k_beta ac beta)yw.                     (C8)

If R_h(x,0)<=0, choose z_h=0 and use the pair root with input height

    J+[T(beta K)-beta W]/P.

Its quiet2 guard is exactly T(beta K)>=beta W, and its player2 output
is T(beta K). If R_h(x,0)>0, choose the unique positive solution of
R_h(x,z_h)=0 and use the triple root with input height J. Existence and
uniqueness are established below.

Both formulas agree at contact. A single formula for the new height is

    T_new(x)=J(x,z_h)+beta[-R_h(x,0)]_+/P(x,0),
    (Uh)(x)=T_new(x)-Psi_beta(x).                               (C9)

The pair branch may therefore switch into any subsequent branch chosen
by this same graph. No invariance of the pair-legal region is assumed.

### Uniform estimates at the corner

Set r_x=u+v and theta=epsilon+rho+beta. Constants hidden in O(theta) are
common on a fixed initial compact neighborhood of(a,c)=(3,1), beta=0,
x=0,z=0. The exact first derivatives there are

                   partial_u  partial_v  partial_z
    K1                 1          0          4
    K3                 0         1/2        3/2
    J                 1/3         1         4/3
    R_0                0          0         -2.                (C10)

For R_0 the normalized expression is explicitly

    W-K1/3-K3-k_beta beta K1 K3,

so no differentiability of a divided candidate function at beta0 is used.
All entries in(C10) have O(theta) errors on the small domain considered.
The partial_u and partial_v derivatives of J-Psi_beta are O(theta) at
fixed z, and partial_z J=4/3+O(theta).

Choose a small fixed delta>0, and consider functions h on
D_rho={u,v>=0,u+v<=rho} satisfying

    h>=0, h(0)=0,
    |h(u',v)-h(u,v)|<=delta|u'-u|,
    |h(u,v')-h(u,v)|<=delta|v'-v|.                              (C11)

In particular 0<=h(x)<=delta r_x. All future arguments beta K lie in
D_rho after a common small choice of beta. The derivative estimates for K
and the coordinate Lipschitz inequalities imply, directly by finite
increments, that R_h is strictly decreasing in z with downward slope
at least

    m=2-C theta-6 delta>0.                                     (C12)

Indeed the smooth part has slope -2+O(theta), while the candidate term
has absolute slope at most delta(11/2+O(theta)). No chain rule for a
possibly nonsmooth h is needed.

Since h>=0, (C8) gives

    [R_h(x,0)]_+ <= [R_0(x,0)]_+ <= C epsilon r_x.              (C13)

The last inequality uses the nonpositive term
-(1+k_beta ac beta)yw in R_0. Thus if the residual is positive, its unique
positive zero exists with

    0<z_h<=C epsilon r_x.                                      (C14)

Choose a fixed trial interval 0<=z<=C' epsilon rho large enough for these
zeros; all trial maps are defined there and their future arguments remain
in D_rho. Their monotonicity also proves existence by the intermediate
value theorem. Formula(C4) is nonnegative, and all selected hazards are
O(r_x). On selected roots, (C10) and(C14) give

    |K|_1<= (1+C theta)r_x,
    partial_z J<=4/3+C theta,
    P(x,0)^-1<=1+C rho.                                        (C15)

The clipped-root construction is continuous and Lipschitz. Comparing its
residuals at two inputs, including the case where one root is0, gives the
coordinate bounds

    Lip_u z_h <= [delta(1+C theta)+C theta]/m,
    Lip_v z_h <= [delta(1/2+C theta)+C theta]/m.                 (C16)

Here the direct-coordinate bounds for K at fixed z come from(C10), and
those for R_0 are O(theta). The same monotone comparison proves(C16)
without presuming differentiability or any regularity of the contact set.

### The operator preserves a closed Lipschitz class

First, Uh>=0 exactly. On the pair branch, (C6) gives

    Uh=h(beta K(x,0))/P(x,0)>=0.                               (C17)

On the triple branch, R_h(x,0)>0 and h>=0 imply
Psi_beta(beta K(x,0))<beta W(x,0). By(C6), this is equivalent to
Psi_beta(x)<J(x,0). Since J is increasing in z, T_new>=Psi_beta there
as well. At0 the new correction vanishes.

The globally valid formula(C9), the finite-increment bounds(C16), and
(C10) imply

    max(Lip_u Uh,Lip_v Uh)
       <= [(4/3+C theta)(1+C theta)/m+C beta]delta+C theta.      (C18)

For the last term in(C9), note that R_h(x,0) has coordinate Lipschitz
constant at most C theta+C delta, while its magnitude is at most
C(theta+delta)r_x. The positive-part map is1-Lipschitz and P is smooth
and bounded away from0. Its entire contribution to(C18) is therefore
O(beta(theta+delta)). This also gives continuity across arbitrary contact
sets, without assumptions on the number or shape of switching curves.

Choose delta small first. At theta=0 the coefficient of delta in(C18)
is arbitrarily close to2/3 as delta tends0. Then choose common epsilon,
rho,beta0 sufficiently small that this coefficient is less than3/4 and
C theta<delta/4 for beta<beta0. Thus(C18) preserves(C11). The nonnegative
class(C11) is closed and complete in the metric

    d(h1,h2)=sup_(x!=0)|h1(x)-h2(x)|/r_x.                       (C19)

Zero belongs to it.

### Uniform contraction and the produced graph

Let d=d(h1,h2). At the same input x, the monotone clipped-root comparison
and(C15) give

    |z_h1-z_h2| <= (1+C theta)d r_x/m.                          (C20)

Indeed the residual difference at any selected root is
|h1(beta K)-h2(beta K)|/beta <= d|K|_1; the same argument applies when
one root is0 by its complementary residual inequality.

The first term in(C9) consequently contributes at most
(4/3+C theta)(1+C theta)d r_x/m. The positive-part term contributes at
most C beta d r_x. Therefore

    d(Uh1,Uh2)<=kappa d(h1,h2),
    kappa=(4/3+C theta)(1+C theta)/m+C beta<3/4.                (C21)

The same choices used in(C18) suffice, after shrinking if necessary.
Banach's theorem constructs a unique fixed point h_beta in(C11).
The desired graph is T_beta=Psi_beta+h_beta. The estimate(C2) follows
from(C11), with a common C. For each beta>0 the operator varies
continuously with(a,c,beta) in(C19): the formulas are smooth and its
candidate functions have the common Lipschitz bound. Uniform contraction
then gives continuous parameter dependence of the fixed point. No
extension of h(beta K)/beta to beta0 is asserted or needed.

At exactly(a,c)=(3,1), (C8) gives g=(1+3k_beta beta)yw>=0. Thus all h>=0
use the pair branch, and U0=0. Uniqueness proves h_beta=0 at the corner.

### Exact continuation, passive guard, and continuous axis

At a fixed point, the pair rule(C9) has exact continuing player2 output
T_beta(beta K), dominating its Quit endpoint. On the triple branch,
R_h=0 makes its player2 output beta W equal to that same graph height.
Players1 and3 satisfy their indifference equations by(C4). This remains
valid for zero hazards on any axis. At the switch, all formulas coincide.
Thus every selected step is an exact legal core root and its successor
is again on the graph. Formula(C15) shows contraction of the outer caps
by beta(1+C theta), which is uniformly less than1.

The passive0 recurrence is

    p_next=3y-z+3w+(1-y)(1-z)(1-w)p.                            (C22)

Its forced-Quit endpoint is at most
1-(1-y)(1-z)(1-w)+10yzw=O(r_x) under the stated row0 bounds. For p in a
fixed positive compact interval, choosing rho small makes the Continue
value positive with a fixed margin. Geometrically summable hazards keep
all later p in a slightly larger positive compact interval, so every
quiet0 guard is legal. Each step is fully Nash, the positive axis limit
exists, and |S-p|<=C r_x. Finite iterates are continuous; the uniform
geometric tail bound makes S continuous. This proves(C3).


## 4. A uniform core as a decreases to3 from the right

Fix 0<c_-<=c_+<1. We prove one eta,rho,beta0,C>0 for
3<a<=3+eta,c_-<=c<=c_+,0<beta<beta0. The finite number of sheets may diverge
as a decreases to3; every radius and bound below is independent of that
number. No negative-eigenvalue modulus dominance is used, including when
c<5/11. The key is full analytic linearization followed by one cone-order
comparison valid for all inverse iterates.

### Uniform analytic linearization and its vanishing-axis factor

Use cap coordinates x=(u,v,z), where z=3(t-u/3-v)/4. The coordinate z here
is a linear cap height, not the exact player2 hazard. Let F_beta be the exact
triple cap map Q_beta o I_beta^-1 in these coordinates. It has the form

    F_beta(x)=L_beta x+g_beta(x),
    L_beta=beta N(I+beta N)^-1,
    g_beta=O(beta |x|^2),                         (U1)

after the same linear change of coordinates on N=PG^-1. Uniformly near
a=3 and c in the stated interval, ||L_beta||<=C beta and
||L_beta^-1||<=C/beta. All estimates extend analytically to a fixed complex
parameter neighborhood and small complex x polydisc.

There is a uniform analytic change K_beta(x)=x+h_beta(x), h=O(|x|^2), with

    K_beta o F_beta=L_beta K_beta.               (U2)

Indeed on holomorphic quadratic remainders the operator

    h |-> L_beta^-1[g_beta+h o F_beta]

preserves a fixed weighted-quadratic ball and contracts by C beta. Its
apparent beta0 singularity is removable. Uniform convergence and Cauchy
estimates give bounded analytic derivatives; a fixed small radius makes K
a diffeomorphism. This is a full linearization, not merely an invariant
surface construction.

Put epsilon=a-3. At epsilon0 the exact solo3 line (u,v,z)=(u,0,0) is
invariant for F_beta and L_beta. The displayed iteration preserves that
line, so K and K^-1 preserve it exactly. Analytic dependence on epsilon
therefore gives the useful transverse bound

    |(K-Id)_v|+|(K-Id)_z| <= C|x| J_epsilon(x),
    J_epsilon(x)=epsilon|u|+|v|+|z|,              (U3)

and the same estimate for K^-1. Their first derivatives have the corresponding
product-rule bounds. Their u corrections are O(|x|^2). Also
J_epsilon(L_beta x)<=C beta J_epsilon(x), because at epsilon0 the u-axis
is invariant. These statements follow from analytic factorization, rather
than division by epsilon.

### One cone for arbitrarily many reverse steps

Write

    alpha=(a-3)/(3a), delta=(1-c)/c,
    R_beta=beta L_beta^-1=N^-1+beta Id.

The reverse map is exactly

    u'=(1-alpha+beta)u-2delta v+8z/3,
    v'=3alpha u/2+(2+delta/2+beta)v+2z,
    z'=-alpha u/2+delta v/2+(beta-2/3)z.          (U4)

Let delta lie in its fixed positive compact interval. Choose constants

    2<Lambda<2/c_+,
    3/8<k<(3/4)(1-1/Lambda),
    M>4 max(delta)+4.

Choose h>0 small, then eta and beta0 small. The closed polyhedral cone

    v>=0, u+Mv>=0, delta v>=Lambda alpha u,
    -h delta v<=z<=k delta v                    (U5)

is invariant under R_beta. Moreover v'>=(2+d+beta)v for a common d>0, and
every nonzero cone point satisfies z'>=m delta v>0 for common m>0.

Here are the explicit checks, including the singular-looking upper u bound.
The lower v bound follows from u>=-Mv and z>=-h delta v after choosing
alpha M and h small. For z', use alpha u<=delta v/Lambda and z<=k delta v:

    z'>=delta v[1/2-1/(2Lambda)-2k/3]>0.

Its upper bound uses u>=-Mv,z>=-h delta v; since 2k>3/4>1/2, shrinking
alpha,h ensures z'<=k delta v'. For the upper u constraint put
U=alpha u/v, Z=z/v. At alpha=beta=0 the expression
(delta v'-Lambda alpha u')/v has minimum at least delta on
0<=U<=delta/Lambda, -h delta<=Z<=k delta, when h is small. Explicitly it is

    (3delta/2-Lambda)U+delta(2+delta/2)+2delta Z.

For positive alpha the lower endpoint becomes U=-alpha M, and the remaining
terms are uniformly small. Thus the constraint persists with a strict
margin. Finally u'+Mv' is minimized at u=-Mv,z=-h delta v; at alpha0
it is at least

    v[M(1+delta/2)-2delta-h delta(8/3+2M)]>0.

The small-alpha perturbation preserves that margin. These calculations
prove cone invariance uniformly even as alpha tends0.

For u>=0, put tau=u/v and zeta=z/v. Whenever the next u is nonnegative,

    tau' <= [(1+beta)tau-b delta]/(2+beta),
    b=2-8k/3>0.                                (U6)

Hence tau-tau'>=(tau+b delta)/(2+beta). If u' is negative, splitting
tau into a fixed small interval and its complement gives a positive gap
as well. By continuity there are common kappa,q>0 such that, while
tau>=-kappa,

    tau-tau'>=q(1+max(tau,0)).                   (U7)

The cone bounds keep tau'>=-M and bound v'/v above. Consequently after
one reverse step zeta is bounded above and below by fixed positive constants.

### Linear seam planes have uniformly bounded slopes

The exact pair-contact tangent has vector

    e0=(1,r_beta,0),
    r_beta=(a-3)(2+c beta)/[3(1-c)(3+a beta)].

Its ratio delta r_beta/alpha tends to2/c as a tends3 and beta tends0.
Thus e0 lies strictly in(U5), with transverse facet margins proportional
to epsilon, uniformly in the parameters. Set e_n=R_beta^n e0. Stop at the
first n=N with tau_n=u_n/v_n<=-kappa. For every epsilon>0 this N is finite
by(U7); it may diverge as epsilon tends0. The last ray has a fixed negative
u/v margin. The linear nth pair-preimage plane is spanned by e_(n-1),e_n.

Write it as z=A_n u+B_n v. Its slopes satisfy

    A_n=(zeta_(n-1)-zeta_n)/(tau_(n-1)-tau_n),
    B_n=zeta_(n-1)-A_n tau_(n-1).

Equations(U5),(U7) prove, with constants independent of n and epsilon,

    |A_n|(1+max(tau_(n-1),0))+|B_n|<=C.          (U8)

In particular every needed plane has an outer projection angle bounded
away from vertical. On every physical sector with n>=2 it has z>=q1 v
for a common q1>0, since both bounding rays have that property. The first
sheet instead has its exact zero-height contact boundary.

### Exact inverse contact curves remain ordered at every depth

In linearizing coordinates, parameterize the exact contact curve by its
u coordinate s. It has

    gamma(s)=s e0+(0,O(epsilon s^2),O(epsilon s^2)),
    gamma'(s)=e0+(0,O(epsilon s),O(epsilon s)).    (U9)

The first estimate uses the explicit pair guard and(U3); the second follows
by analyticity. Because e0 has the uniformly positive rescaled cone margins
just noted, there is a common C such that BOTH gamma(s)/s and gamma'(s)
lie between (1-Cs)e0 and (1+Cs)e0 in the order defined by cone(U5).
Applying the cone-positive map R_beta^n preserves these inequalities for
every n, without a factor depending on n.

Choose M1>M+1 and the positive radial functional ell=u+M1 v. The exact
nth inverse contact curve in linearizing coordinates is

    gamma_n(s)=beta^-n R_beta^n gamma(s).

The cone comparison implies relative O(s) errors in BOTH positive linear
functionals v and ell, for points and tangents. Thus ell increases strictly
along every curve. For ell<=rho, the tail parameter satisfies
s<=C(C beta)^n rho, because gamma(s)=L_beta^n gamma_n(s).
Conversely these curves cover a common small ell interval: the inverse
bound ||L_beta^n||<=(C beta)^n gives ell(e_n)>=C^-n/C, so their radial
derivative is at least C^-1(C beta)^-n. A fixed contact-curve parameter
interval therefore covers the required radius for every n.

Passing back through K^-1 changes v by relative O(rho) and ell by relative
O(rho), uniformly in n. This also holds for their tangent values: from(U3),
the error is bounded by
C[|x|J_epsilon(t)+|t|J_epsilon(x)], and the point and tangent cone comparisons
to the SAME ray e_n give |t|J_epsilon(x)<=C|x|v(t). Hence no factor
1/epsilon enters the derivative estimate.

At fixed physical ell, the exact angular coordinate theta=v/ell therefore
satisfies

    theta_n(ell)=theta_n^lin(1+O(rho)),
    theta_n^lin=1/(tau_n+M1).                    (U10)

The errors and the strictly positive radial derivatives are uniform in n.
By(U7), consecutive linear angles have a uniform multiplicative gap:
theta_n^lin>=(1+q2)theta_(n-1)^lin for common q2>0. Taking rho small makes
the exact curves strictly ordered. The last one lies strictly beyond the
physical u=0 boundary theta=1/M1. Thus the exact curves partition the whole
small physical quadrant into consecutive sectors, however many are needed.

### All-depth exact sheet graphs and physicality

In linearizing coordinates, an equation of the exact pair surface is

    Ctilde(x)=l x+Rtilde(x), l x=z,
    |Rtilde(x)|<=C|x|J_epsilon(x).

Its nth inverse sheet is Ctilde(L_beta^n x)=0. The normalized linear normal
l L_beta^n has size at least (beta/C)^n. Since both |x| and J_epsilon are
contracted by C beta under L_beta,

    |Rtilde(L_beta^n x)|/|l L_beta^n|
       <=C(C3 beta)^n |x|J_epsilon(x).           (U11)

The unweighted second derivative has the analogous bound C(C3 beta)^n.
Choose beta0 so C3 beta0<1/2. The uniform projection angle(U8) now gives
one common implicit-function radius for EVERY needed sheet. After K^-1,
these remain analytic graphs, uniformly bounded in C1. Their value error
from the corresponding linear plane in LINEARIZING coordinates is
O(rho J_epsilon), uniformly in n. We only need, and next prove, the
stronger transverse estimate in original coordinates on the active sectors.

On active sectors epsilon u<=Cv and the linear cap height is O(v).
Here(U8) also gives |A_n|u<=Cv. The original-coordinate longitudinal error
Delta u=O(rho(|u|+|v|+|z|)) therefore contributes

    |A_n Delta u|<=C rho(v+|z|),

while all transverse errors from(U3),(U11) are bounded by
C rho(epsilon u+v+|z|). The graph equation consequently gives
|z|<=Cv+C rho|z|. Absorbing the last term first proves the uniform bound
|z|<=Cv; substituting back gives the required original-coordinate value
error O(rho v). No weighted value claim is made off the active sectors.
At the exact sector endpoints,
(U10) perturbs tau by O(rho)(1+|tau|). The stronger slope bound in(U8)
then keeps the linear height at least(q1-O(rho))v on every sector n>=2.
The exact player2 hazard differs from the linear cap height by
O((beta+rho)J_epsilon), again by the exact a3 solo3 axis and analyticity.
Thus all these later sheets have strictly positive player2 hazard. The
other hazards are nonnegative from their exact rational formulas at fixed
nonnegative outer caps and nonnegative player2 hazard.

For the first sheet use its exact contact factor. Its player2 hazard
vanishes exactly at the pair-contact curve and factors as a positive unit
times v-v_contact(u). At a=3,beta0 and the origin, the unit is
(1-c)/(1+3c), uniformly positive on the fixed c interval. Hence this factor
is positive on a common neighborhood, and the first sheet is physical
right up to its boundary. This avoids a nonuniform additive perturbation
near a shrinking seam.

Exact descent follows directly from the sheet equations:
Ctilde(L_beta^n x)=0 maps into the(n-1)st equation, and each inverse
contact curve maps to its preceding curve. There are no extra adjacent-sheet
intersections: after applying L_beta^n, such an intersection is the local
intersection of the pair surface and its first preimage. After dividing the
first-preimage equation by beta, the two equations are uniformly transverse
near a=3,c in[c_-,c_+]; at beta0 the first-sheet
factor just computed is strictly positive. Their only local intersection
is the exact contact curve. The ordered physical boundaries and positive
outer output therefore put the image of each sector in the preceding
sector. Sheet1 enters the legal pair sector.

For completeness, that pair sector is uniformly invariant. At z=0 the
quiet2 guard divided by beta is g from(C8). Write

    A=a/3-1, B=1-c, L=1+k_beta ac beta,
    g=Aw-By+Lyw.

On g>=0, y/w<=A/(B-Lw). The next pair hazard ratio satisfies

    (y_next/w_next)/(y/w)
       =(c/a)(3+a beta+a beta w)/(2+c beta+c beta y)<=q<1

with one q independent of a-3. Since B is bounded below, choose a common
radius with q/(1-Lw/B)<1. The next ratio is then at most A/B, which
makes the next guard nonnegative. Zero axes are checked directly, without
division. Identity(C6) proves the exact pair continuation on Psi_beta.

Outside that legal sector the pair guard is negative, equivalently
Psi_beta<tcrit_beta at the same outer caps by(C6). Monotonicity of the
triple input height in its hazard then gives T_beta>=Psi_beta on every
physical triple sheet. Adjacent graphs agree on their exact contact
curves, and their selected roots agree there: at the first contact the
triple hazard is0, and at later contacts both descriptions use the same
first triple. All radii, root bounds and contraction constants above are
independent of N.

Finally the uniform bound T_beta<=C(u+v) makes every selected hazard O(u+v)
and every successor outer cap O(beta(u+v)). The passive0 guard and geometric
tail argument therefore have common constants. They give the claimed
continuous axis with S_beta=p+O(u+v), and hence Section8 applies with one
positive beta threshold throughout this right-hand band. The endpoint a=3 is supplied next.

## 5. A uniform analytic graph on the left, including a=3

The full analytic linearization in Section4 exists on a neighborhood of
a=3 on both sides; its construction precedes the right-side cone argument.
In the original cap coordinates(u,t,v), the characteristic polynomial of N,
multiplied by8, is

    p(X)=8X^3+5(c-1)X^2-(3ac+a+2c)X+2ac.

At a=3 it factors as

    (X-1)[8X^2+(5c+3)X-6c].

Its simple negative root-r and complementary real invariant plane therefore
continue analytically for a near3, uniformly for c in[c_-,c_+]. Direct
multiplication gives that plane as

    t=A u+Bv,
    A=(1+r)/(a+3r), B=(1+2r)/(c+2r),
    A-1/3=(3-a)/[3(a+3r)], B-1=(1-c)/(c+2r).

Pull the plane back by the full linearizing change K_beta. This gives an
analytic invariant graph t=T_beta(u,v), with common C2 bounds, common
parameter derivatives of those bounds, and tangent(A,B). At a=3 the
exact solo3 line is

    (u,t,v)=(u,u/3,0),
    (y,z,w)=(0,0,u/(3+3 beta+u)),
    Q=(3 beta w,beta w,0).

The change K_beta preserves that line, so T_beta(u,0)=u/3 exactly at a=3.
For every nearby a, the function T_beta(u,0)-A u vanishes to second order
in u. Analytic parameter dependence and the exact a=3 identity give

    T_beta(u,0)-A u=O((3-a)u^2),

uniformly for a<=3. This is a parameter factor, not division by3-a.

For fixed u,v, the virtual triple is given by(C4); its input height J is
increasing in its hazard z, with derivative4/3+o(1). Put
tcrit_beta(u,v)=J(u,v,0). Exactly

    tcrit_beta(u,0)=u(1+beta)/(3+a beta),
    partial_v tcrit_beta(0,0)=(2+beta)/(2+c beta).

For 3-eta<=a<=3, subtraction gives

    T_beta(u,0)-tcrit_beta(u,0)
      =(3-a)u[1/(3(a+3r))-beta/(3(3+a beta))+O(u)],
    T_beta(u,0)-Psi_beta(u,0)
      =(3-a)u[1/(3(a+3r))+O(u)].

Both brackets are uniformly positive after choosing beta and the radius
small. The v derivatives of T_beta-tcrit_beta and T_beta-Psi_beta at the
origin are, respectively,

    (1-c)[1/(c+2r)-beta/(2+c beta)],
    (1-c)/(c+2r).

These are uniformly positive for the compact c-interval. The common C2
bounds and integration in v therefore yield a common kappa>0 with

    T_beta-Psi_beta>=kappa[(3-a)u+v],
    T_beta-tcrit_beta>=kappa[(3-a)u+v].

Every nonzero graph point thus has a positive triple hazard z, except
at a=3,v=0 where it is the exact solo3 root. Formula(C4) supplies
nonnegative y,w; all hazards are O(u+v). At the solo axis, the zero-hazard
core players still satisfy their indifference equations. Invariance makes
the nonnegative outer output a new graph point, with contraction C beta.
The passive guard and geometric-tail argument from Section3 have common
constants. This supplies(C3) on the entire left strip including a=3.

Taking common smaller eta and radius, and the minimum of the left and right
thresholds, proves the local producer on(R1) when c_+<1. Section7 extends
that conclusion to every compact positive c interval.
No continuity across a=3 is inferred merely from two existence constructions;
the consumer needs continuous roots and axis values in the inputs of each
game, together with the common bounds just proved.

## 6. A uniform core crossing c=1 on every compact positive a interval

Begin with 0<a_-<=a_+<3; intervals above3 and the finite cover follow
below. First restrict to 1<=c<=1+eta. Use the exact dynamic
complementarity operator(C4)--(C9), with T=Psi_beta+h. Here K1 is independent
of v and K3 is independent of u; their respective direct-coordinate and z
derivatives are positive on a common small domain. A pair step may return
to a triple step. We prove uniformity on the upper side using a different
closed function class and the weighted metric with denominator u.

### The closed function class and exact scalar margins

For each a put

    B(a)=(3-a)/[3(1+a)],
    f(a)=(3-a)/9,
    m0(a)=2(3+2a)/9,
    k1(a)=3a/(3+2a).

Choose a small fixed D>0. The candidate class consists of continuous h
with h(0,v)=0 and the coordinate increment bounds

    0<=h(u2,v)-h(u1,v)<=B(a)(u2-u1)  (u2>=u1),
    |h(u,v2)-h(u,v1)|<=D|v2-v1|.                 (J5)

Thus 0<=h(u,v)<=B(a)u. Zero belongs to the class. It is complete in

    d_u(h1,h2)=sup_(u>0,v>=0) |h1-h2|/u.         (J6)

All increments are restricted to the fixed triangle u+v<=rho. Choose beta
so all future arguments lie in u'+v'<=rho/4. The coordinatewise intermediate
points used in finite-increment comparisons then lie in u'+v'<=rho/2,
so every comparison stays inside the candidate's domain.

Let theta=eta+rho+beta. At c=1,beta=0 and the origin, direct calculation
gives the following derivatives at fixed trial z:

    R_0,u=f(a), R_0,v=0, R_0,z=-m0(a),
    K1,u=a/3, K1,z=4a/3,
    K3,v=1/2, K3,z=3/2,
    J_z=4/3, (J-Psi_beta)_u=(J-Psi_beta)_v=0.    (J7)

All smooth coefficients have uniform O(theta) errors. At general c near1,
R_0,v=-(c-1)/2+O(rho+beta) and K3,v=c/2+O(rho+beta).

Because h is nondecreasing in its first coordinate, increasing z cannot
create a negative contribution through K1. The second-coordinate bound D
therefore makes R_h strictly decreasing in z, with downward slope at least

    m(a)=m0(a)-C(D+theta)>0.                     (J8)

This is a finite-increment assertion, not a chain rule for a nonsmooth
candidate. At fixed z the same comparison gives

    R_h,u >= f(a)-aB(a)/3-C theta=B(a)/3-C theta,
    R_h,u <= f(a)+C theta,
    |R_h,v| <= (c/2+C theta)D+C theta.            (J9)

In particular R_h(x,0) strictly increases with u at fixed v.

Since c>=1, the exact boundary formula(C6)--(C8) and h>=0 give

    [R_h(x,0)]_+ <= f(a)u.

Thus a positive residual has exactly one positive zero, with

    0<z_h<=f(a)u/m(a).                          (J10)

All arguments remain on a common small domain, and the formulas in(C4)--(C5)
give nonnegative hazards. Their total is O(u+v). Since w<=(u+z)/3,

    K1(x,z_h)<= [k1(a)+C(D+theta)]u.             (J11)

The clipped-root comparison also gives coordinate Lipschitz bounds

    Lip_u z_h <= [f(a)+C theta]/m(a),
    Lip_v z_h <= [(c/2+C theta)D+C theta]/m(a).   (J12)

On intervals where both roots are positive its u increment has a common
positive lower bound, from the first inequality in(J9) and a common upper
bound on the downward residual slope. All these statements follow directly
by comparing monotone residuals, including when one clipped root is zero.

### Preservation of the class

Uh is nonnegative exactly. This follows from(C6)--(C8) on the pair branch.
On the triple branch, R_h(x,0)>0 implies Psi_beta(x)<J(x,0), while J
increases in z, so J(x,z_h)>=Psi_beta(x). At u=0 the candidate future
correction vanishes and R_h((0,v),0)=-(c-1)y<=0. Therefore Uh(0,v)=0
exactly. This boundary argument is the reason we restrict this operator
to c>=1.

The output is nondecreasing in u. On the pair branch this follows directly
from h(beta K)/P: K1 increases, K3 stays fixed, P decreases, and h>=0.
On the triple branch the positive lower increment from(J9),(J12), multiplied
by J_z=4/3+O(theta), dominates the O(theta) direct u increment of J-Psi.
There is at most one branch switch along a fixed-v u interval, by(J9),
and both formulas agree at that switch. Thus monotonicity is global.

The upper u-Lipschitz bound obtained from(C9),(J12) is

    Lip_u Uh <= 2(3-a)/[3(3+2a)]+C(D+theta).     (J13)

It lies strictly below B(a) after common small choices, because exactly

    B(a)-2(3-a)/[3(3+2a)]
       =(3-a)/[3(1+a)(3+2a)]>0.                 (J14)

These margins have a positive lower bound on the fixed a interval.
The positive-part term in(C9) contributes only O(beta) to these estimates:
its residual is Lipschitz with bounded constants, while P stays positive.

Likewise the v-Lipschitz bound is

    Lip_v Uh <= [3/(3+2a)]D+C(D^2+theta).        (J15)

The coefficient 3/(3+2a) is uniformly less than1 because a>=a_->0.
Choose D small first, then eta,rho,beta0 small enough to absorb the remaining
terms in(J13),(J15). These choices preserve the entire class(J5).

### A contraction without monotone pair tails

For d=d_u(h1,h2), differences in future corrections obey

    |h1(beta K)-h2(beta K)|/beta<=d K1.

The clipped-root comparison, including pair/triple comparisons, and(J11)
therefore give

    |z_h1-z_h2|<= [k1(a)+C(D+theta)]d u/m(a).

Using(C9), the height difference divided by u is at most

    {18a/(3+2a)^2+C(D+theta)}d.                  (J16)

The positive-part pair term contributes O(beta)d. The exact inequality

    18a/(3+2a)^2<=3/4

follows from (2a-3)^2>=0. The choices above can therefore make(J16) at most
(4/5)d, uniformly throughout the parameter band. Banach's theorem produces
a unique fixed point in(J5). At that point each selected root is an actual
Nash root and its successor is on T_beta=Psi_beta+h_beta. The outer caps
contract by C beta, and every selected hazard is O(u+v). The usual passive0
guard and geometric-tail argument give the claimed continuous axis with
common constants. No spectral assumption or pair-region invariance enters.

The metric(J6) need not give parameter continuity at c=1: arbitrarily thin
pair sectors can prevent it. This causes no defect in uniform thresholds.
If ordinary C0 parameter continuity is wanted, start Picard iteration at0.
Each finite iterate is jointly continuous by the smooth formulas and the
strict monotone clipped root; its sup-norm error is at most C rho(4/5)^n.
The uniform limit is therefore jointly continuous in the ordinary C0 sense.

### The lower analytic side and agreement at c=1

The full analytic linearization argument of Section4 applies uniformly to a
in[a_-,a_+] and c near1: N is uniformly invertible, and the weighted quadratic
contraction uses only ||L_beta||=O(beta), ||L_beta^-1||=O(1/beta). Its simple
negative eigenvalue-r is separated on this compact parameter set. At c=1,

    p(X)=(2X-1)(4X^2+2X-2a),

so r=k+1/2 with k=(sqrt(1+8a)-1)/4 in(0,1). The negative spectral subspace
and its complementary plane continue analytically for c near1. Pulling the
latter plane back by the full linearizing map gives an analytic invariant
graph with common C2 and parameter-derivative bounds, tangent to

    t=A u+Bv,
    A=(1+r)/(a+3r), B=(1+2r)/(c+2r).

At c=1 the exact solo1 line u=0,t=v is invariant: its root is

    y=v/(2+beta+v), z=w=0,
    Q=(0,beta y,beta y).

The linearizing map preserves that line, so T_beta(0,v)=v exactly.
The graph is tangent to(A,B) for every parameter. Analytic factorization
therefore yields

    T_beta(0,v)-Bv=O((1-c)v^2).

The virtual triple threshold satisfies

    tcrit_beta(0,v)=v(2+beta)/(2+c beta),

and hence on 1-eta<=c<=1,

    T_beta(0,v)-tcrit_beta(0,v)
      =(1-c)v[1/(c+2r)-beta/(2+c beta)+O(v)].

The bracket is uniformly positive. Also A-1/3=(3-a)/[3(a+3r)] has a
uniform positive lower bound on the fixed a interval. The u derivative
of T_beta-tcrit_beta stays positive after a common choice of radius and
beta. Integration in u gives the uniform physicality bound

    T_beta-tcrit_beta>=kappa[u+(1-c)v].

Thus every nonzero point has a physical triple root except the c=1,u=0
axis, where it is the exact solo1 root. The same invariance and positive
outer-output argument supplies contraction and the passive axis bound.

The comparison T_beta>=Psi_beta is also uniform. On the pair surface,
(C8) and c<=1 give

    g<=(c-1)y-[(1-a/3)-(1+k_beta ac beta)y]w<=0

once the radius is small, because 1-a/3 has a positive lower bound.
By(C6), this is tcrit_beta>=Psi_beta. The analytic graph therefore
satisfies the same common core interface as the upper construction.
Taking the minimum of the upper and lower thresholds proves(R2) when a_+<3.

The two selected graphs agree at c=1 as well. There
A=1/(1+2k), a=k(1+2k),0<k<1. The analytic correction h=T-Psi vanishes
on u=0, and its u slope at the origin is b=A-1/3 with 0<b<B(a).
The inequality is strict uniformly on the compact a interval; after
clearing positive denominators, B(a)-b has numerator(1-k)(6k+1).
Its v slope is O(u), so a common small radius puts it in(J5).
Its physical roots make it a fixed point of(C9); uniqueness identifies
it with the upper construction. This agreement is not required merely
to take the minimum of the two existence thresholds.

### Compact a intervals above3

Now fix 3<a_-<=a_+<infinity. For c<1 the active triple wedge has
u=O((1-c)v). Scaling this wedge gives an exact analytic map at c=1 and a
uniform finite sheet count. Thus no diverging-depth estimate is needed in
this case. The c>=1 side will be the invariant pair surface everywhere.

#### A pair surface with a uniform invariant legal side

Use the reference singleton/core data with premiums(a beta,beta,c beta),
and put

    Psi_beta(u,v)=u/3+v+k_beta uv,
    k_beta=(9+a beta+3c beta)/[3(6+2a beta+3c beta)].
    A=a/3-1>0, B=1-c, L=1+k_beta ac beta.

At pair13 hazards

    w=u/(3+a beta+u), y=v/(2+c beta+v),

the exact quiet2 guard divided by beta is

    g=A w-B y+L yw=w(A+Ly)-By.                    (H1)

The pair surface is exactly invariant, with outer output
(a beta w,c beta y). For c<1, a legal nonzero pair satisfies
y/w<=(A+Ly)/B. The next hazard ratio is multiplied by

    (c/a)*(3+a beta+a beta w)/(2+c beta+c beta y).

It is at most a common q<1 because 3c/(2a)<1 uniformly. Choose rho and
beta0 so q(1+L rho/A_min)<1, where A_min=a_-/3-1>0. Then

    y_next/w_next <= q(A+Ly)/B <= A/B,

which implies the next guard. This proves pair legality forever with a
radius independent of B decreasing to zero. No division of the radius by
1-c is used. When B=0 or B<0 every pair guard is nonnegative directly.

#### The exact scaled problem is regular at c=1

For c<1 set

    delta=(1-c)/c, c=1/(1+delta),
    u=delta U, v=V,
    z_cap=3(t-u/3-v)/4=delta Z.                  (H2)

The coordinate z_cap is a linear cap height, not the exact player2 hazard.
Let F_beta be the exact triple cap map Q_beta o I_beta^-1. At c=1 the
entire line (u,t,v)=(0,V,V) is exactly invariant: its root is

    y=V/(2+beta+V), z=w=0,
    Q=(0,beta y,beta y).

Consequently the u and z_cap coordinates of
F_beta(delta U,V,delta Z) vanish identically at delta0, for all small V
and beta. Division by delta therefore gives an analytic scaled map

    Fhat_beta,delta(U,V,Z)
       =(F_u/delta,F_v,F_zcap/delta),            (H3)

on one fixed small neighborhood, including delta=0. It still factors as
beta times an analytic map vanishing at0. The same exact-axis argument
makes the virtual player2 hazard divided by delta analytic there.

The pair surface becomes

    Z=(3/4)k_beta UV,                            (H4)

with no degenerating coefficient. Its contact guard, divided by delta, is

    g/delta=(A+Ly) U/(3+a beta+delta U)-c y,
    y=V/(2+c beta+V).                            (H5)

Hence its nonzero contact curve is analytic and uniformly transverse:
at beta0 and the origin its tangent is

    (U,V,Z)=(tau0,1,0),
    tau0=9c/[2(a-3)].                            (H6)

The exact contact curve satisfies U<=C V uniformly on the common domain.
The pair-legal side has larger U/V; the entire remaining triple wedge
therefore has U<=C V.

#### Uniformly finite leading reverse seams

Put alpha=(a-3)/(3a). In the scaled cap coordinates the inverse of the
leading normalized triple matrix is exactly

    U'=(1-alpha)U-2V+8Z/3,
    V'=3alpha delta U/2+(2+delta/2)V+2delta Z,
    Z'=-alpha U/2+V/2-2Z/3.                      (H7)

This is analytic at delta0 and has determinant -4(1+delta)/a, bounded
away from0 on the parameter rectangle. Starting at the contact ray(H6),
the cone

    V>=2alpha U, 0<=Z<=3V/8, U>=0               (H8)

holds with a strict initial margin because
2alpha tau0=3c/a<1 uniformly. As long as the next U is nonnegative,

    Z'>=V/4-2Z/3>=0,
    Z'<=V/2<=V'/4,
    V'>=2V,
    U'<=(1-alpha)U-V<U.

The cone is preserved. With tau=U/V, every consecutive positive-U step
satisfies

    tau_next<=(tau-1)/2.                         (H9)

The initial tau is at most tau_max=9/[2(a_--3)]. Thus a crossing U<=0
occurs within 1+ceil(log2(1+tau_max)) steps. If a seam lands exactly on
U=0, one further virtual seam has strictly negative U, while V,Z remain
positive. One extra sheet suffices locally at such a parameter value.

Let e_n be the successive inverse contact rays and e_-1 their first forward
image. The ray e_-1 has Z=0 and U/V=(2a/(3c))tau0>tau0, strictly pair-legal.
The nth sheet is the cone spanned by e_(n-1),e_n. The ratios U/V strictly
decrease, so its outer projection is nonsingular. The last sheet is
truncated at U=0. Even if its virtual endpoint has negative U, every point
up to that truncation has nonnegative leading hazards. Its successors are
earlier positive seam cones, and after n steps it lies in cone(e_-1,e0),
inside the legal pair sector.

These finite pair-preimage cones now lie on a genuinely compact,
nondegenerate parameter rectangle including delta0,
with a proved common finite depth bound. Projection and intersection
transversality persist on a finite parameter cover. In particular no
uncontrolled count of implicit-function estimates is being hidden.

#### Exact finite sheets with common domains

Write Fhat=beta Rhat. For each of the finitely many needed n, the normalized
forward iterate

    H_n=Fhat^n/beta^n

is analytic through beta0 on a fixed neighborhood. Recursively
H_0(x)=x and H_(n+1)=Rhat(beta^n H_n)/beta^n; removability follows from
Rhat(0)=0. The exact nth pair-preimage sheet has equation

    H_n,Z-(3/4)k_beta beta^n H_n,U H_n,V=0.       (H10)

The tangent equations are precisely the leading reverse-seam planes just
constructed.
Their nonsingular outer projections give exact analytic sheet graphs
Z=Z_n,beta,delta(U,V), with common radius and derivative bounds.
Only sheets used for the physical prefix need these graph representations.
The last seam may use the next normalized sheet equation without requiring
that extra sheet itself to have a graph representation.

Adjacent sheets meet in the exact inverse contact curves. These may be
defined by their two normalized forward equations, rather than evaluating
inverse iterates on a fixed domain. Three consecutive leading seam rays
are independent: e_-1 and e0 are distinct rays in Z=0, and e1 has Z>0;
invertibility propagates that independence. Thus the seam equations are
uniformly transverse. Their ordered outer curves persist. Choose a final
strictly negative-U virtual seam on each parameter patch, retaining an
extra sheet when needed; the finite cover gives common constants.

Select the pair surface on its legal side and the nth exact sheet on the
sector between its two neighboring contact curves. The functions agree
exactly at seams. For n>=2, the leading first player2 hazard divided by
delta has a strict positive margin on the closed physical sector. For
n=1, that scaled hazard vanishes exactly at the contact curve and has
positive inward transverse derivative. Analytic factorization there,
and ordinary strict-margin persistence on later sectors, give physical
hazards uniformly down to delta0. The other hazards follow from the exact
formulas

    w/delta=[U(1-delta ztilde)+(1-a beta)ztilde]
                 /[3+(delta U+a beta)(1-delta ztilde)],
    y=[V(1-delta ztilde)+(1-c beta)delta ztilde]
                 /[2+(V+c beta)(1-delta ztilde)],

where the actual player2 hazard is delta ztilde>=0.

The exact map sends each selected sheet to the preceding sector, by its
forward defining equation and the ordered shared boundaries; sheet1 enters
the invariant legal pair region. The roots match exactly at contact. Thus
every continuation is produced, not merely supplied as a feasible surface.

The resulting original height is at least Psi_beta exactly. Outside the
pair-legal sector its pair guard is negative, so tcrit_beta>Psi_beta; the
physical triple input is increasing in its player2 hazard and hence lies
above tcrit_beta. On the pair sector equality holds.

#### Returning to the full original quadrant and crossing c=1

The scaled construction is only needed where U<=C V. This implication
from original pair illegality does not presume scaled-domain membership:
(H5) gives A U<cy(3+a beta+u)<=C V using u<=rho and A>=A_min.
Choose the original radius so u+v<=rho and this inequality place U+V in
the common scaled domain. Everywhere else select the pair surface, whose
legal wash has the common radius proved above.

On every active sector the scaled sheet height is O(V). Therefore

    0<=T_beta(u,v)-Psi_beta(u,v)<=C delta v.       (H11)

All selected hazards are O(u+v), with common constants. Scaled outer caps
contract by C beta on the active wedge, and the original outer caps do so
on both triple and pair sectors. The passive0 guard and geometrically
summable tails give a continuous positive axis p+O(u+v) with uniform bounds.

For c>=1 use the exact pair surface everywhere. Formula(H1) makes every
guard legal because A>0 and B<=0. At c=1 this also handles the entire
original quadrant. Bound(H11) shows uniform convergence of the lower-side
graphs to that pair surface. On the active wedge, the extra player2 hazard
and the change of the other hazards from the pair root are O(delta v);
outside it the roots already agree. Thus selected roots and the axis also
join continuously at c=1.

### A finite cover gives the full horizontal theorem

Fix any compact interval 0<a_-<=a_+<infinity. Let epsilon0>0 be the corner
radius from(C1), shrunk below1/4. If nonempty, apply the below3 construction
to

    [a_-,min(a_+,3-epsilon0/2)]

and the above3 construction to

    [max(a_-,3+epsilon0/2),a_+].

The corner box covers the middle interval [3-epsilon0,3+epsilon0]. These
three pieces cover the whole a interval, with overlap. Ignore empty pieces.
Take the minimum of their positive c-widths, beta thresholds, and core
radii, and the maximum of their core bounds. This gives a single positive
eta,beta2,rho,C for(R2), also after requiring eta<=1/4.

For each raw game, choose any producer from a piece containing its a value.
Each produces a graph and selected roots continuous in the cap inputs and
satisfying the common estimates. A jointly continuous choice across the
finite cover is neither inferred nor needed. Section8 consequently applies
with one shared return ribbon, one finite pair slack bound, and one beta
threshold for the entire compact positive a interval. This proves the full
horizontal theorem.

## 7. A dynamic core throughout 0<a<=3,c>1

Fix a compact subset K of(N0). Use exactly the rational roots, pair identity,
residual and dynamic operator(C4)--(C9), now with the following candidate
class. K1 is independent of v and K3 is independent of u, and their direct
coordinate and z derivatives are positive on the common small domain.
The proof retains the same finite-difference candidate v slope in two
coupled terms; discarding that coupling would give a smaller region.
The a=3 endpoint is included by keeping every u error proportional to3-a.

### Uniform parameter choices and the closed candidate class

Put

    f=(3-a)/9>=0, d=(c-1)/2,
    m=(8a+27c-15)/18,
    D_min=4d/(3m), M_*=m-(3c/2)D_min
                       =m-c(c-1)/m.             (N3)

The lower v bound must exceed D_min, while downward residual monotonicity
requires a positive M=m-(3c/2)D. We choose these constants together rather
than prescribe D independently of a.

First D_min<2d/c: since d>0, this is equivalent to3m>2c, or
8a+15c>15, which holds throughout(N0). Next write
s=4a/9-5/6, so m=3c/2+s. Direct differentiation gives

    m^2 partial_c M_*
      =P(c)=15c^2/8+(5/2)cs+(3/2)s^2+s,
    P(1)=(8a^2+12a)/27>=0,
    P(c)-P(1)=(c-1)[15(c+1)/8+5s/2]>=0.

The last bracket is at least5/3 for c>=1 and s>=-5/6. Thus M_* is
nondecreasing in c, and

    M_*>=M_*(a,1)=m(a,1)=(4a+6)/9>4a/9.        (N5)

For f>=0 define q(M)=4a/(9M)+16af/(9M^2), a decreasing function of M.
Consequently

    q(M_*)<=q(m(a,1))=18a/(3+2a)^2<=3/4.

By compactness choose one epsilon_D>0, common on K, and set

    D=D_min+epsilon_D, M=m-(3c/2)D,
    B=(f/2)[4/(3M)+3/a],

so that D<2d/c, M>4a/9+1/3 and q(M)<39/50 everywhere on K. Such a
choice exists: the first gap is continuous and strictly positive on K,
the second has at least1/3 slack before the perturbation, and q(M_*)<=3/4 has
uniform slack below39/50. All these quantities are bounded on K; in
particular B is a bounded positive multiple of f and vanishes exactly
when a=3.

Choose a small fixed tau>0. Candidates have h(0,v)=0 and coordinate
increment bounds

    0<=h(u2,v)-h(u1,v)<=B(u2-u1)             (u2>=u1),
    -D(v2-v1)<=h(u,v2)-h(u,v1)<=tau(v2-v1)   (v2>=v1).        (N4)

Thus 0<=h<=Bu. Zero belongs to this closed class, which is complete in

    d_u(h1,h2)=sup_(u>0)|h1-h2|/u.

Work on a fixed triangle u+v<=rho; all future arguments are placed in
u'+v'<=rho/4 by a common small beta choice. Coordinatewise intermediate
comparisons therefore remain in the candidate's domain.

### Exact scalar margins on the full closed region

The smooth leading derivatives at fixed z are

    R_0,u=f, R_0,v=-d, R_0,z=-m,
    K1,u=a/3, K1,z=4a/3,
    K3,v=c/2, K3,z=3c/2,
    J_z=4/3, (J-Psi)_u=(J-Psi)_v=0.             (N6)

The relevant exact margins are

    f-aB/3=f(9M-4a)/(18M),
    B-4f/(3M)=f(9M-4a)/(6aM),
    D-4d/(3m)=epsilon_D>0,
    d-(c/2)D>0.                                (N7)

The first two u margins are proportional to f; their coefficients stay
strictly positive on K. The active-wedge estimates below retain that factor
in every u error. The v margins stay strictly positive even at a=3.

The selected first outer output will satisfy, at the limiting constants,

    K1/u<=a/3+(4a/3)f/M.

The resulting metric contraction factor is

    q(M)=4a/(9M)+16af/(9M^2)<39/50.             (N8)

None of these choices or bounds uses a positive lower bound on f.

### Clipped roots and the exact active-wedge factor

Let theta=rho+beta. Uniform smooth errors from(N6) are O(theta).
Since h is nondecreasing in its first coordinate, its K1 contribution
favors downward monotonicity in z. Its most adverse K3 contribution uses
v slope -D. Finite-increment comparison therefore gives downward residual
slope at least M-C theta>0. At fixed z,

    R_h,v<=-d+(c/2)D+C theta<0.                 (N9)

A common upper bound on the downward z slope also holds. Because c>1
and h>=0, the exact boundary identity implies

    [R_h(x,0)]_+<=f u.

Every positive residual thus has a unique positive zero, with

    0<z_h<=f u/(M-C theta),
    K1(x,z_h)<=[a/3+(4a/3)f/(M-C theta)]u.        (N10)

The rational hazard formulas are nonnegative there and O(u+v). Monotone
comparison gives continuous clipped roots and common coordinate Lipschitz
bounds, including across z_h=0.

For f>0, every active input and every contact also satisfy a stronger
localization. From R_h(x,0)>=0 and h>=0, formula(C8) gives

    (c-1)y0+(1+k_beta ac beta)y0 w0<=3f w0,
    y0<=C f u, v<=C f u.                        (N11)

Consequently selected z, y and K3 are O(fu). At fixed z, exact differentiation
of the smooth residual gives

    R_0,u=w_u[3f-y+(a/3)z-a beta k_beta K3(1-z)].

Since w_u=1/3+O(theta), throughout a slightly enlarged active wedge,

    R_0,u=f+O(f theta), K1,u=a/3+O(theta),
    f(9M-4a)/(18M)-C f theta<=R_h,u<=f+C f theta. (N12)

The candidate comparison uses K3's EXACT independence of u; no unscaled
cross term is present.

The direct u increment of J-Psi also carries f. At z=0,

    J(x,0)-Psi_beta(x)=beta R_0(x,0)/P.

On the wedge, R_0=O(fu) and R_0,u=O(f), so its u derivative is O(beta f).
Changing z from0 to O(fu) contributes O(f rho) through a bounded mixed
u,z derivative. Hence

    (J-Psi)_u=O(f theta)                        (N13)

on every selected triple. This exact localization replaces a nonuniform
generic O(theta) estimate as a tends3.

### Class preservation, including the coupled lower-v estimate

Nonnegativity of Uh is exact. On a pair it is h(beta K)/P. On a triple,
R_h(x,0)>0 implies Psi_beta(x)<J(x,0), and J increases with z.
At u=0, R_h((0,v),0)=-(c-1)y<=0, so Uh(0,v)=0.

For f>0, the u output increment on a triple is positive and at most

    4f/(3M)+C f theta.

This lies below B by the RELATIVE second margin in(N7), with common
choices independent of f. On a pair, the exact formula h(beta K)/P is
nondecreasing in u, with u slope O(beta f). It too lies in[0,B].
One must use this exact pair cancellation: separately estimating the
positive-part correction in(C9) would lose the necessary factor f.

Every residual zero for f>0 lies in(N11), and(N12) is strictly positive
on a neighborhood of that zero. Every zero therefore crosses upward
as u increases, so there is at most one switch on a fixed-v u interval.
The branch formulas agree there, giving the global u increment bounds.

For the lower-v bound it is essential to retain the SAME candidate
v slope in the residual numerator and denominator. Take two active roots
at fixed u and write their differences as Delta v, Delta z. Decompose the
future correction along a coordinate path:

    Delta h/beta=p Delta K1+q Delta K3,
    p in[0,B], q in[-D,tau].

This is an exact finite-difference decomposition; no differentiability of
h or nonsingularity of its evaluation map is presumed. K1's independence
of v gives

    Delta K1=(4a/3+O(theta))Delta z,
    Delta K3=(c/2+O(theta))Delta v
                       +(3c/2+O(theta))Delta z.

The SAME q therefore appears in both coefficients of the residual
difference. The coarse clipped-root Lipschitz bound controls the errors
after division by Delta v. The triple output quotient is

    phi(p,q)+O(theta),
    phi(p,q)=-(4/3)[d+(c/2)q]
                  /[m+(4a/3)p+(3c/2)q].        (N14)

Its numerator is positive, since d-(c/2)D>0, and its denominator
is at least M>0. Phi increases with p, so its minimum has p=0. There

    (c/2)m-(3c/2)d=c(2a+3)/9>0,

which makes phi decrease with q. The minimum is therefore at q=tau:

    triple v quotient>=-4d/(3m)-C(tau+theta).    (N15)

Choose tau first and theta next, using the strictly positive third
margin in(N7), to make this greater than -D. Its upper bound is strictly
negative by(N9), up to a small smooth error, so it is below tau.

On a pair the v quotient of h(beta K)/P lies between -C beta D and
C beta(tau+B rho). These lie in[-D,tau] after shrinking beta. The positive
allowance tau handles the denominator derivative without assuming exact
monotonicity on the pair branch. Since(N9) is globally strict, there is at
most one branch switch along a fixed-u v interval. Exact contact agreement
then proves the global v increment bounds.

At f=0 the class has B=0 and h=0 identically. The guard is
g=(c-1)y+(1+3c beta k_beta)yw>=0, so U0=0 and the pair root is selected
everywhere. No positive u derivative is asserted at this endpoint.
This proves preservation of the entire closed class on K.

### Uniform contraction and actual continuation

For e=d_u(h1,h2),

    |h1(beta K)-h2(beta K)|/beta<=e K1.

Monotone clipped-root comparison and(N10) give

    |z_h1-z_h2|
       <=e u[a/3+(4a/3)f/(M-C theta)]/(M-C theta).

Using(C9), the metric contraction is at most

    (4/3+O(theta))
       [a/3+(4a/3)f/(M-C theta)]/(M-C theta)+C beta
       =q(M)+O(theta)<=4/5.

The positive-part correction costs only O(beta)e in this VALUE comparison;
no u-derivative estimate without the f factor is used. Banach's theorem
produces the unique fixed graph.

At the fixed point the pair's player2 output is T_beta(beta K), dominating
its Quit endpoint, and the triple equation gives beta W=T_beta(beta K).
Players1 and3 satisfy their exact indifference equations. At contact the
roots and outputs coincide. The selected roots are continuous, their
outer caps contract by C beta, and every hazard is O(u+v). Passive0's
small-hazard guard and uniformly geometric tails therefore give a continuous
positive axis S_beta=p+O(u+v), with common constants.

The graph satisfies 0<=T-Psi<=Bu<=Cfu and its extra triple hazard is O(fu).
Thus it joins the exact pair producer at a=3. Finally c>1 and T>=u/3+v
give the shared macro's strict endpoint bound
D_macro-aU_macro/3-cV_macro<D_macro-V_macro<0. A bounded pair slack gives
the opposite sign. Section8 verifies the continuous ribbon/Miranda return
and finite behavioral consumer with one common UE threshold on K.

### The exact pair quadrant and the full vertical join

For a>=3,c>=1, the exact pair surface Psi_beta itself supplies a local
producer. Its guard from(C8) is

    g=(c-1)y+(a/3-1)w+(1+k_beta ac beta)yw>=0.

Identity(C6) preserves the surface. The outer output(a beta w,c beta y)
contracts by C beta uniformly on every bounded parameter set, while hazards
are O(u+v). The passive guard and continuous axis have the same uniform
bounds as before. The macro entry is strictly negative since
D_macro-aU_macro/3-cV_macro<=D_macro-U_macro<0. This is a direct uniform
producer on compact subsets of the closed pair quadrant.

Fix a compact c interval[c_-,c_+] contained in(1,infinity). Choose eta>0
with3-eta>0. The entire closed left band
[3-eta,3]x[c_-,c_+] lies in(N0), so the dynamic-region theorem gives one
threshold. The right band[3,3+eta]x[c_-,c_+] is in the pair quadrant.
Their minimum threshold gives(R1) throughout this upper c interval.

For an arbitrary compact positive c interval, let epsilon0 be the corner
radius. Apply the lower-c result of Sections4--5 to
[c_-,min(c_+,1-epsilon0/2)] when nonempty, the just-proved upper result to
[max(c_-,1+epsilon0/2),c_+] when nonempty, and use the corner box for the
middle. Ignore empty pieces. The intervals overlap and cover the original
interval. Take the minimum
of the positive a-widths, beta thresholds and core radii, and the maximum
of the core bounds. This proves the full vertical theorem(R1). As in the
horizontal cover, only input-continuity for each fixed table is needed;
a jointly continuous selection across parameter overlaps is not asserted.

Every point with0<a<3,c>1 now has an open neighborhood with a common
threshold, without dividing at the upper neutral wall2a=3c. The compact-cover
argument below uses these actual uniform neighborhoods; a mere union of
pointwise thresholds would not suffice.

## 8. Actual return, uniform constants, and full behavioral deviations

The cited frozen export's return geometry is independent of a,c at beta0.
It consists of a pair13 macro with spectator slack sigma, a direct macro
arc, and a diffuse3 macro arc, joined continuously at their exact contact.
Its physical ribbon has two opposite strict return signs, a fixed positive
opponents' absorption lower bound x per loop, and strict quiet0 guards.
The positive-beta charts depend continuously on a,c,beta, with perturbation
bounds uniform on bounded parameter sets once a finite slack bound M is fixed.
Each fixed parameter set(C1),(R1),(R2), or compact K in(N0), is bounded.

At the fixed diffuse endpoint, put

    z_L=153/1000, w_L=16351075/247762329, y_L=z_L/2,
    U=z_L+w_L-z_L w_L,
    D=y_L+w_L-y_L w_L,
    V=y_L+z_L-y_L z_L.

The exact reference identities are

    D-2V/3=-1920310952813/247762329000000<0,
    D-U=-z_L(1-w_L)/2<0.

For the corner box choose epsilon<1/4, and for the c=1 band shrink eta
to at most1/4. In both cases c>=3/4>2/3 and a>0, so the graph-entry residual
obeys the common strict bound

    E_beta=D-T_beta(a beta U,c beta V)/beta
          <=D-aU/3-cV<0.

For a compact subset of(N0), c>1 gives the same uniform margin through
D-aU/3-cV<D-V<0. The exact pair quadrant uses D-aU/3-cV<=D-U<0.

For the two-sided band, c>=c_->0 and a>=3-eta. The second identity gives

    E_beta<=D-U+eta U/3.

Shrink eta so eta U/3<-(D-U)/2 at this fixed endpoint. This gives the same
common strict negative margin, including the left side. These margins persist
on a single sufficiently narrow transverse endpoint face and at small beta,
uniformly on the respective parameter sets.

At the pair endpoint U=w,V=y and the macro output has player2 cap
beta(D+sigma). The common upper height bound gives

    E_beta>=D+M-C(aw+cy)

when sigma=M. Choose one finite M large enough for a strict positive margin
throughout the endpoint face. The beta0 return is independent of sigma.
Only after fixing M do we shrink the common beta threshold for the exact
macro perturbations. No bound involving the variable number of core sheets
enters this choice.

The continuous axis estimate(C3) gives

    S_beta(P,a beta U,c beta V)=P+O(beta)

uniformly on the full ribbon, with P in a fixed positive compact interval.
It preserves the two strict return signs. The graph-entry signs just proved
supply the other two faces. The frozen export's two-dimensional
intermediate-value argument therefore produces an actual simultaneous
return and graph entrance for every raw table in any of the stated uniform regions.
It needs no C1 axis, normalized graph limit, or continuous selection of
return roots. Fix one returned loop for each game before choosing accuracy.

All exact core roots query only the seven passive and nine participant
entries listed in Section1, together with row0's bounded joining entries.
The three singleton flows2,0,3 query only singleton columns in prescribed
play; a deviator can add only itself and queries one pair reward. Unlisted
finite rewards enter only a finite mesh constant. Their magnitudes do not
change the graph, ribbon, or common beta thresholds.

For completeness, the cited consumer truncates the exact wash at axis error
E_N and discretizes the three flows with maximum one-date hazard d_max.
The periodic finite word contains those three flow pieces, one empty wash
seam, the reversed finite wash, and the fixed macro. A deviator faces at
least x>0 opponents' absorption per word, independently of its own behavior.
If C_join is the largest positive pair-joining reward used by the flows,
full regret and payoff error are bounded by

    regret <= C_join d_max+2E_N/x,
    payoff error <= E_N/x.

The flow gain is charged only when the deviator quits; seam errors sum over
at most1/x expected visits. Geometric absorption removes the residual for
arbitrary stopping laws and Never. Signed singleton levels cancel exactly
on sure absorption. For a word of length L and reward bound M_r, the
finite-horizon comparison error is at most2M_r L/(x H) at horizon H.
Choosing N and the mesh for each accuracy, then H sufficiently large,
proves the fixed-target uniform-equilibrium conclusion. This proves the four
raw-table statements, rather than leaving a continuation or profile supplied.

## 9. Every compact positive ratio set for the original additive calibration

The following corollary has a narrower raw scope than Sections1--8. Define
the original sixty-entry calibration by ell_i=1 and the displayed Gamma,
with

    Z_i(A)=sum_(j in A) Gamma_ij whenever i is not in A,

on every nonempty passive coalition. For every proper nonsingleton coalition
containing its owner, take the four participant rows to be

    (beta,a beta,beta,c beta),

and set the native grand reward vector to

    (10,-2,-beta,-1).

Original absorbing rewards are r_i(A)=1+Z_i(A); live and Never remain zero.
No entries in this calibration are left free. It satisfies the raw scope of
each local theorem above when beta is small, and it also satisfies the
stronger passive/additional-participant hypotheses of the older strict-cone
result. This explicit common calibration is essential to the synthesis.

**Compact-ratio theorem.** For every compact K contained in(0,infinity)^2
there is beta_K>0 such that every game in this calibration with(a,c) in K
and0<beta<beta_K has a uniform-equilibrium payoff.

Here are the exact incoming results used, with their scopes kept distinct:

- [CROSSED_PREMIUM_HYBRID_DIFFUSE_FLOW_UNIFORM_EQUILIBRIUM.md](../exports/CROSSED_PREMIUM_HYBRID_DIFFUSE_FLOW_UNIFORM_EQUILIBRIUM.md)
  has compact-uniform thresholds on the open region L={a>3,0<c<1}.
- [THREE_DIFFUSE_FLOWS_UNEQUAL_PREMIUM_UNIFORM_EQUILIBRIUM.md](../exports/THREE_DIFFUSE_FLOWS_UNEQUAL_PREMIUM_UNIFORM_EQUILIBRIUM.md)
  has compact-uniform thresholds on0<=a<3,0<c<=1 with
  Delta(a,c)=21c-6+8a(19c+1)>=0.
- [UNEQUAL_PREMIUM_CONTRACTION_UNIFORM_EQUILIBRIUM.md](../exports/UNEQUAL_PREMIUM_CONTRACTION_UNIFORM_EQUILIBRIUM.md)
  has compact-uniform thresholds on the strict cone
  a>0,0<c<5/9,8a<15(1-c). It requires all additive passive rewards and
  the homogeneous proper participant rows, including entries containing0.
  Its larger restrictions are why this corollary does not claim the free
  coordinates of the newer packets.

We verify that every point of the positive ratio plane has an OPEN
neighborhood with one threshold, rather than assuming that pointwise
thresholds admit a common lower bound.

If c=1, theorem(R2), applied to a small compact a interval about the point,
supplies a neighborhood with a common threshold. If a=3, theorem(R1),
applied to a small compact positive c interval, does the same. These
statements cover their intersection and provide actual neighborhoods on
both sides of the interfaces.

Away from those interfaces, use the following strict open regions:

1. If a>3,c>1, take a compact small neighborhood inside the pair quadrant
   and use its direct uniform producer from Section7.
2. If a>3,c<1, take a compact small neighborhood inside L.
3. If a<3,c>1, the point is in the INTERIOR of(N0), so the dynamic
   theorem gives a compact neighborhood throughout this entire region.
4. If a<3,c<1 and Delta>0, take a compact small neighborhood in that
   strict lower-diffuse region. If Delta<=0, then c<2/7 and a<=3/4.
   Thus c<5/9 and

       8a<=6<75/7<15(1-c).

   The point is strictly inside the old cone, including every point where
   Delta=0. This supplies the required open overlap at that boundary.

Each neighborhood carries a common positive threshold from its stated
compact-uniform producer. Cover the given compact K by finitely many such
open neighborhoods and take the minimum of those thresholds and1. Every
parameter in K belongs to at least one neighborhood, and beta below this
minimum meets its producer's hypotheses. All tables are in the exact common
calibration just specified. This proves the compact-ratio theorem without
assuming continuity of any choice of producer or target across the cover.

## 10. Scope and the remaining ratio degenerations

The local broad-scope theorems now give uniform horizontal and vertical
joins for every compact positive interval, and the dynamic region covers
the entire strip0<a<=3,c>1. The finite-cover
conclusion for ALL compact positive ratio sets is asserted only for the
original additive calibration in Section9. It is not silently promoted to
the newer packets' free-coordinate raw scope.

For example, suppose a sequence of games in that calibration has
beta_n tending to0 and none of the games has UE. Then(a_n,c_n) must leave
every compact subset of(0,infinity)^2: infinitely many points in one such
compact set would eventually have beta_n below its positive threshold.
After passing to a subsequence, at least one of a_n,c_n must approach0 or
grow without bound. This is a necessary condition for such a counterexample
sequence, not a reduction of every game to a sequence of this form.

No common threshold as ratios degenerate, no existence claim at all premium
scales, and no arbitrary-table Fin4 closure follows. The next concrete
question is whether one of these ratio degenerations admits a uniform
producer after a suitable change of scale.

Semantic declarations inspected for the consumer are
`quittingUniformEquilibriumPayoffConjecture` in
`UniformEquilibrium/Quitting/Conjecture/Basic.lean`,
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
`CompatibleFiniteJumpFlowWord.execute_error_and_debt_le` and
`repeatedSingletonProfile_error_and_debt_le` in
`UniformEquilibrium/Quitting/EssentialAPS/FiniteJumpFlowCompiler.lean`, and
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
They consume supplied data; this note produces the local cores and verifies
their uniform application to the already proved return. No Lean build or
new formalization claim is made.
