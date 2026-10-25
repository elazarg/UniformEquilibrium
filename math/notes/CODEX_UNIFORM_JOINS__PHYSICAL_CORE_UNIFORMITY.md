# Uniform physical cores across switching boundaries

Owner: CODEX_UNIFORM_JOINS.

**Complete internal ordinary-mathematics argument.** Independent review status
is recorded in the accompanying feedback. This is not an export or a Lean
theorem.
Fin4 remains open. No uniform theorem for all positive ratio boxes or for the
whole positive three-premium cube is claimed.

The contribution is uniformity through three joins where separate fixed-ratio
existence thresholds do not supply it. This note is the canonical combined
record: it retains the core proofs and applies the existing exact return and
behavioral consumer, without copying their complete geometry again.

## 1. Raw data and the three uniform conclusions

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

**Two-sided a=3 theorem.** For every 0<c_-<=c_+<1, there exist eta,beta1>0
such that every table above with

    3-eta<=a<=3+eta, c_-<=c<=c_+, 0<beta<beta1                  (R1)

has a uniform-equilibrium payoff. Neither beta1 nor the core radius depends
on the number of triple steps on the right, which may diverge as a
decreases to3. The left side uses a uniform analytic graph.

**Two-sided c=1 theorem.** For every 0<a_-<=a_+<3, there exist eta,beta2>0
such that every table above with

    a_-<=a<=a_+, 1-eta<=c<=1+eta, 0<beta<beta2                  (R2)

has a uniform-equilibrium payoff. One threshold and one core radius work
on both sides of c=1. The upper-side producer permits arbitrary pair/triple
switchbacks and assumes no eventual invariant pair tail.

All three thresholds are independent of ell and of all free reward coordinates.
The flow mesh and finite-horizon threshold may depend on the magnitudes of
those finite rewards. The conclusion is one fixed payoff target for each
game before accuracy is chosen: for every positive accuracy there is one
behavioral profile delivering that target and bounding every full unilateral
deviation over all sufficiently long finite horizons.

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
Section7 below checks every new uniform input to that consumer explicitly.
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
continuous axis with S_beta=p+O(u+v), and hence Section7 applies with one
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
thresholds, proves the local producer on the full two-sided band(R1).
No continuity across a=3 is inferred merely from two existence constructions;
the consumer needs continuous roots and axis values in the inputs of each
game, together with the common bounds just proved.

## 6. A uniform core crossing c=1 away from a=0,3

Fix 0<a_-<=a_+<3. First restrict to 1<=c<=1+eta. Use the exact dynamic
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
Taking the minimum of the upper and lower thresholds proves(R2).

The two selected graphs agree at c=1 as well. There
A=1/(1+2k), a=k(1+2k),0<k<1. The analytic correction h=T-Psi vanishes
on u=0, and its u slope at the origin is b=A-1/3 with 0<b<B(a).
The inequality is strict uniformly on the compact a interval; after
clearing positive denominators, B(a)-b has numerator(1-k)(6k+1).
Its v slope is O(u), so a common small radius puts it in(J5).
Its physical roots make it a fixed point of(C9); uniqueness identifies
it with the upper construction. This agreement is not required merely
to take the minimum of the two existence thresholds.

## 7. Actual return, uniform constants, and full behavioral deviations

The cited frozen export's return geometry is independent of a,c at beta0.
It consists of a pair13 macro with spectator slack sigma, a direct macro
arc, and a diffuse3 macro arc, joined continuously at their exact contact.
Its physical ribbon has two opposite strict return signs, a fixed positive
opponents' absorption lower bound x per loop, and strict quiet0 guards.
The positive-beta charts depend continuously on a,c,beta, with perturbation
bounds uniform on bounded parameter sets once a finite slack bound M is fixed.
Each of the parameter sets(C1),(R1),(R2) is bounded.

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
return and graph entrance for every raw table in any of the three uniform regions.
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
proves the fixed-target uniform-equilibrium conclusion. This proves all three
raw-table theorems, rather than leaving a continuation or profile supplied.

## 8. Scope and the next uniformity question

Pointwise existence of beta0(a,c)>0 does not imply the uniform theorems above.
The corner result covers arbitrary beta-dependent ratio paths converging
to(3,1). The two-sided band excludes deterioration caused by either approach
to a=3 with c in a fixed compact subset of(0,1), including the unbounded
right-side sheet count. The third theorem supplies a common threshold across
c=1 for every fixed compact a interval inside(0,3). These claims do not give
a common threshold as c tends0, as ratios grow unbounded, or on every
positive ratio rectangle crossing other joins.

The concrete next question is to obtain one produced threshold on every
compact subset of positive(a,c), including remaining regime boundaries such
as2a=3c away from the neighborhoods treated here. Such a general uniformity
theorem is not assumed, and it would still not supply a uniform threshold
as ratios approach0 or grow without bound.

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
