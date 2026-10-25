# Three diffuse singleton flows close a region of unequal quitting premiums

Fin4 remains open. This theorem produces uniform equilibria on an explicit
unequal-premium band, including the reference direction(a,c)=(1/10,1).
The mathematics is ordinary mathematics, not yet formalized in Lean.

## Exact raw-table statement

There are four players I={0,1,2,3}, one live state and independent private
Continue/Quit choices at each live date. The first nonempty quitting coalition
A absorbs at its finite reward vector r(A). Live and literal Never pay zero.
A unilateral deviation may replace its player's entire behavioral law,
including arbitrary stopping dates and Never. There is no public correlation.

Put ell_i=r_i({i}) and Z_i(A)=r_i(A)-ell_i for nonempty A only. The levels
ell are arbitrary signed numbers; this notation shifts neither live nor Never.
Require the native singleton matrix

    Gamma=[0,3,-1,3;2,0,1,-3;2,-2,0,-1;-1,-2,1,0].

Require exactly these seven passive nonsingleton entries:

    Z0(12)=2, Z0(13)=6, Z0(23)=2, Z0(123)=5,
    Z1(23)=-2, Z2(13)=-3, Z3(12)=-1.

The nine core participant entries are

    Z1(12)=Z1(13)=Z1(123)=a beta,
    Z2(12)=Z2(23)=Z2(123)=beta,
    Z3(13)=Z3(23)=Z3(123)=c beta.

The six proper participant entries in row0 vary independently over all finite
values at most1, without lower bounds. Its native grand reward is any finite
value at most10. Every unlisted nonsingleton coordinate is arbitrary finite
data, including participant entries containing0 in rows1,2,3 and their grand
rewards. The requirements above are direct tests on the original reward table.

**Theorem.** Suppose

    0<=a<3, 0<c<=1,
    Delta(a,c)=21c-6+8a(19c+1)>=0.                (T)

For each such(a,c), there is beta0(a,c)>0 such that every table above with
0<beta<beta0 has a uniform-equilibrium payoff. One positive beta0 works on
every compact subset of(T), including subsets meeting a=0 or c=1.
In particular one threshold works on the entire closed rectangle

    0<=a<=2, 2/7<=c<=1.

It is independent of ell and all free reward coordinates. The flow mesh
and finite-horizon threshold may depend on their magnitudes.

The conclusion is one fixed target before accuracy: for each epsilon>0,
one behavioral profile delivers that target within epsilon and bounds every
complete unilateral deviation's gain by epsilon over all sufficiently long
finite horizons. The producer below constructs its invariant graph, return
and profiles entirely from the raw reward table. Its three diffuse singleton
flows are implemented by finite meshes; no continuous-time game is assumed.

## 1. A physical core graph, including the boundary c=1

Write core continuation coordinates as(u,t,v), for players1,2,3, and
core hazards as(y,z,w). All constants in this section can be uniform on a
fixed compact subset of0<=a<3,0<c<=1. The construction produces a C2 graph
t=T_beta(u,v) on u,v>=0,u+v<=rho for one fixed rho>0, with a common
C2 bound C. Enlarge the parameter compact set to its vertical hull up to
c=1 when using parameter estimates below; that hull is still compact in
0<=a<3,0<c<=1.

### Exact map and the negative normal direction

For core hazards q=(y,z,w), the indifference input and output are

    I_beta(q)_1=[a beta(z+w-zw)-z+3w]/[(1-z)(1-w)],
    I_beta(q)_2=[beta(y+w-yw)+2y+w]/[(1-y)(1-w)],
    I_beta(q)_3=[c beta(y+z-yz)-z+2y]/[(1-y)(1-z)],
    Q_beta(q)=beta(a(z+w-zw),y+w-yw,c(y+z-yz)).

The map F_beta=Q_beta o I_beta^-1 is analytic near0, uniformly on the fixed compact ratio subset of(T). Put

    G=[0,-1,3;2,0,1;2,-1,0], P=[0,a,a;1,0,1;c,c,0], N=PG^-1.

Then DF_beta(0)=beta N(Id+beta N)^-1. The characteristic polynomial of N,
multiplied by8, is

    p(X)=8X^3+5(c-1)X^2-(3ac+a+2c)X+2ac.

For a>0, Descartes' rule applied to p(-X) gives exactly one negative
eigenvalue-r, counted with multiplicity, hence simple. At a=0 the polynomial
factors as X[8X^2+5(c-1)X-2c], with one simple negative root, one zero root,
and one positive root. Thus r stays positive and separated from zero on the
fixed compact ratio subset of(T). For a>0 the other eigenvalues have positive real
part: their product is ac/(4r)>0 and their sum is r+5(1-c)/8>0. At a=0
one is zero and one positive. The left normal to their real invariant plane
is(-A,1,-B), where A=(1+r)/(a+3r), B=(1+2r)/(c+2r). In particular

    A-1/3=(3-a)/[3(a+3r)], B-1=(1-c)/(c+2r).        (3)

No dominance of the negative modulus over the remaining eigenvalues is
needed below. No eigenbasis for the remaining block is assumed.

### Parametric analytic construction

Use analytic coordinates(s,n) separating that plane from the simple negative
eigenvector. Locally in parameters the map has the form

    s'=L s+f(s,n), n'=-nu n+g(s,n),
    L=O(beta), nu=beta r/(1-beta r),
    f,g=O(beta|(s,n)|^2).

These estimates, including finitely many derivatives and nu/beta bounded
away from0, hold uniformly on a complex parameter neighborhood of each
compact real parameter patch. A finite parameter cover suffices.

On holomorphic functions h(s) with h(0)=Dh(0)=0, use the weighted norm
sup_(s!=0)|h(s)|/|s|^2 on a small complex polydisc. On a ball of norm<=C,
define

    (Th)(s)=[g(s,h(s))-h(Ls+f(s,h(s)))]/nu.         (4)

The first term has norm bounded independently of beta, and the second has
norm O(beta C), because its argument is O(beta|s|). Choose C large and
then the polydisc radius and beta small. This preserves the ball.

For two graphs, the difference in g contributes at most O(radius) times
the graph distance: D_n g=O(beta|s|). The direct difference in h at the
contracted argument contributes O(beta). For the change in that argument,
Cauchy's estimate gives |Dh(s')|<=O(C|s'|) when |s'|<=O(beta|s|), while
D_n f=O(beta|s|). After division by nu, its contribution is O(beta radius^2).
Thus(4) is a contraction with factor O(radius+beta).

Starting at h=0, its iterates and uniform limit are jointly holomorphic in
s and parameters. The apparent beta0 singularity is removable: g/beta is
analytic, and h(beta psi)/beta is analytic because h vanishes to second
order. Cauchy estimates on smaller fixed polydiscs give a uniform C2 bound
in s and a uniform parameter derivative of this C2 bound. Graph invariance
is exactly(4). Transforming back, the remaining plane is nonvertical in t,
so the analytic inverse-function theorem yields t=T_beta(u,v), with
DT_beta(0)=(A,B). The constructions on overlapping parameter patches agree
by uniqueness of the small analytic graph tangent to the same plane.

At c=1 the line u=0,t=v is EXACTLY invariant: its root is

    y=v/(2+beta+v), z=w=0,

and its output is(0,beta v/(2+beta+v),beta v/(2+beta+v)). This line lies
in the tangent plane. In the spectral coordinates it has n=0, g=0, and
s' on the same line. Consequently the graph transform starting at0 preserves
h=0 on that line. Thus T_beta(0,v)=v exactly when c=1.

### Physicality on the entire nonnegative quadrant

For fixed small u,v>=0, solve the virtual triple using z:

    y=[v(1-z)+(1-c beta)z]/[2+(v+c beta)(1-z)],
    w=[u(1-z)+(1-a beta)z]/[3+(u+a beta)(1-z)].

The remaining input t(z) is strictly increasing, its derivative tending
uniformly to4/3 at zero. Write tcrit_beta(u,v)=t(0). Then

    tcrit_beta(0,v)=v(2+beta)/(2+c beta).            (5)

Parameter regularity and the exact c=1 axis give

    T_beta(0,v)-Bv=O((1-c)v^2).

Indeed this remainder is identically0 at c=1, vanishes to second order in v
for every c, and has a uniformly bounded c derivative in the same weighted
norm. Therefore, by the displayed identities,

    T_beta(0,v)-tcrit_beta(0,v)
       =(1-c)v[1/(c+2r)-beta/(2+c beta)+O(v)].      (6)

Its bracket is uniformly positive. Also
partial_u(T_beta-tcrit_beta)=A-1/3+O(beta+u+v), uniformly positive by the displayed formula for A-1/3.
Integrating in u gives a uniform lower bound kappa[u+(1-c)v].

The unique graph root thus has z>0 unless c=1,u=0 (or the origin). The
rational formulas give nonnegative y,w, strictly positive for every nonzero
root except w=0 on that exceptional axis. Every hazard is O(u+v).
Exact invariance and Q_beta's formula produce another graph point with
nonnegative outer caps, bounded by C beta(u+v). Choose C beta<1. This
produces an infinite physical chain on the entire quadrant, including
arbitrarily large ratios v/u.

### Passive value and axis limit

The passive update is

    p'=3y-z+3w+(1-y)(1-z)(1-w)p.

The row0 upper bounds imply its Quit endpoint is at most
[1-(1-y)(1-z)(1-w)]+10yzw=O(y+z+w). For p in a positive compact interval,
p' remains separated from0 and the Quit endpoint is small when rho is small.
The summed hazards are O(u+v), because core caps contract geometrically.
Thus every later p remains in a slightly larger positive compact interval,
all quiet0 guards hold, and |p_(n+1)-p_n|<=C|q_n|. The positive limit S
exists and satisfies S=p+O(u+v). Finite iterates are continuous; their
remaining tails are uniformly O((C beta)^n(u+v)). Hence S is jointly
continuous in the inputs and parameters. Every root is fully Nash.


## 2. A continuous family of three-flow returns

Assume0<=a<3,0<c<=1 and

    Delta(a,c)=21c-6+8a(19c+1)>=0.                (A1)

The core graph from Section1 is physical throughout the nonnegative quadrant.
Put k=aA,l=cB. Its negative eigenvalue-r satisfies

    0<=k<1, 0<l<=1,
    8r=8k+9l-5,
    p(-1/8)=Delta(a,c)/64.

Thus r>=1/8 and8k+9l>=6. The normal identity follows from the t-coordinate
of(-A,1,-B)N=-r(-A,1,-B). All constants can be uniform on each compact
subset of(A1), including a=0. In particular one beta threshold works on
0<=a<=2,2/7<=c<=1. No positive eigenvalue simplicity is needed.

The passive-axis function produced by the graph wash will be written
Axis_beta(p,u,v). It is analytic and satisfies Axis_beta(p,u,v)=p+O(u+v).
To justify the derivative information used below, use the same complex
neighborhood as the graph construction. The outer iterates contract by C beta,
and the increments of p are O((C beta)^n(|u|+|v|)). Their sum converges uniformly
on a fixed complex neighborhood. Hence Axis is holomorphic there; Cauchy
estimates imply

    Axis_beta(P(z,w),a beta U(z,w),c beta V(z,w))
        =P(z,w)+O(beta) in C1                     (A2)

on each analytic branch of every compact macro chart. This is a produced
function, not a supplied tail.

### General three-flow seam

Allow v>=0 and alpha>=0 with alpha v=0, and impose

    alpha=t-2(u-v)/3.

Put

    U0=(u+3alpha)/(1-alpha), V0=v/(1-alpha),
    x=(U0-V0)/3,
    R=(U0+2V0)/(3-U0+V0),
    K=R/(1-R)=(u+2v+3alpha)/(3-2u-v-9alpha).       (A3)

When the denominators and the displayed values are physical, the three
backward singleton flows are

    (K,0,0,0) --2,R--> (0,R,0,R)
       --0,x--> (0,U0,2x,V0)
       --3,alpha--> (3alpha,u,t,v).                (A4)

If alpha>0 then V0=0, so flow3 has owner cap zero. If alpha=0, omit that
flow and its input need not have owner3 cap zero. All flow segments are
nonnegative whenever their endpoints are. Nonnegativity of V0 gives R>=x;
the compact charts below have0<x<R<1 and0<=alpha<1.

### Exact positive-beta macro charts

For a triple macro q=(0,y,z,w), use the exact input functions I_beta of the
core lemma. Set

    yzero_beta(z)=z(1-c beta)/[2+c beta(1-z)].

This is the unique zero of v. The zero of alpha=t-2(u-v)/3 is explicit:

    yseam_beta=N/L,
    N=w(z+3)+beta[-2awz+2aw+2az+2cwz-2cz+3wz-3w],
    L=10+2w-8z
       +beta[-2awz+2aw+2az+2cwz-2cw-2cz+2c
              +3wz-3w-3z+3].

At beta0 these become yzero=z/2 and
 yseam=w(3+z)/(10+2w-8z). All displayed denominators are positive on a
fixed neighborhood of the compact arc below. There are exact factorizations

    v=[2+c beta(1-z)](y-yzero_beta)/[(1-y)(1-z)],
    alpha=L(y-yseam_beta)/[3(1-y)(1-z)(1-w)].      (A5)

Hence y=max(yzero_beta,yseam_beta) satisfies v>=0,alpha>=0,alpha v=0
exactly. This is a continuous piecewise analytic prescription, with no
approximate complementarity step.

Write U=z+w-zw,D=y+w-yw,V=y+z-yz and H=(1-y)(1-z)(1-w). The passive macro
output is P0=3y-z+3w+3alpha H. Define the AUXILIARY return residual

    F_beta(z,w)=Axis_beta(P0,a beta U,c beta V)-K,  (A6)

and the graph-entry residual

    E_beta(z,w)=D-T_beta(a beta U,c beta V)/beta.   (A7)

In(A6), the core output2 is projected to T_beta(a beta U,c beta V) before
the axis function is evaluated. Only at E_beta=0 is this the actual macro
output. This projection is explicit and continuous; it assumes no strategic
continuation. Both branch functions F_beta converge in C1 to F0 by(A2).

There is also a pair chart z=0 with quiet2 output beta(D+sigma),0<=sigma<=2.
Its t input is[beta(D+sigma)+2y+w]/[(1-y)(1-w)]. Its zero-seam
value is yseam_beta=[N-3beta sigma(1-z)]/L at z=0; this is strictly positive
on the pair chart. Choose y by alpha=0, and
use the same formulas(A3),(A6), now with E_beta=D+sigma-T_beta(a beta w,c beta y)/beta.
The inactive2 guard is exactly beta sigma>=0. Its other equations coincide
with the triple chart at z=sigma=0, including the chosen y and axis projection.

## 3. Exact return geometry and the graph entrance

At beta0, on the y=yseam branch, alpha=0. The return factor is

    F0=-w P(w,z)/[2(-w+4z-5)J(w,z)],
    J=w^2z^2-2w^2z-5w^2+5wz^2-30wz+33w+8z-10,
    P=6w^3z^2-12w^3z-30w^3-23w^2z^3+115w^2z^2-145w^2z-7w^2
        +8wz^4-141wz^3+863wz^2-1803wz+1205w
        +40z^4-250z^3+354z^2+70z-250.             (A8)

On0<=z<=9/50,1/5<=w<=13/50, exact Bernstein coefficient bounds are

    min P_w=2768063849/3125000,
    max P_z=-20532303/156250,
    min(P_w+P_z)=4131300547/6250000,
    max J=-10637661/6250000.

Moreover P(1/5,0)=-238/25 and
P(13/50,9/50)=1898408563/312500000>0. Thus P=0 has one continuous smooth
curve w_d(z) in(1/5,13/50); it increases, and w_d'(z)<1.

Let z_star be the unique root in(1761/10000,881/5000) of

    f_star(z)=32z^3-148z^2+167z-25.

Its derivative is positive on[0,9/50], with minimum Bernstein coefficient
73019/625. Its endpoint values on the displayed isolating interval are
-193897169/31250000000 and10896733/1953125000. The exact identity

    P(z(5-4z)/3,z)
      =-(z-2)(z-1)(z+3)^2(4z-5)f_star(z)/9       (A9)

shows that yseam>=z/2 precisely along the part0<=z<=z_star of this return
curve. At the endpoint w_star=z_star(5-4z_star)/3, both v and alpha vanish.
On this direct arc, u,t>0,v>=0,2u+v<3, and0<x<R<1. For example
u<=39/37,v<=2/9 gives2u+v<3; u-v=3t/2>0. Its passive output is at least
3w+z/2>=3/5. All these bounds have positive margins except the intended v0
boundary. The exact corner joins the next arc.

### The limiting diffuse3 return arc

On y=z/2, v=0, direct algebra gives

    P0=z(11-8z)/2,
    F0=-z P_f(w,z)/(2D_f(w,z)),
    P_f=24wz^3-153wz^2+165wz+6w-200z^3+555z^2-419z+50,
    D_f=3wz^2-15wz-25z^2+35z-6.

Hence the return curve is explicitly

    w_f(z)=(200z^3-555z^2+419z-50)
                     /[3(8z^3-51z^2+55z+2)].     (A10)

The denominator polynomial8z^3-51z^2+55z+2 is greater than8 on
[3/20,9/50], directly from2+55(3/20)-51(9/50)^2>8.
Use the interval z_L=153/1000<=z<=z_star. Its endpoint at z_star is
exactly w_star. On this curve,

    alpha=f_star(z)/(88z^3-201z^2+127z-28),
    x=P0/(1+2P0),
    3w_f-z=-(z-1)(8z^3-243z^2+367z-50)
                              /(8z^3-51z^2+55z+2). (A11)

The cubic in the last numerator has positive derivative on[3/20,9/50],
with minimum Bernstein coefficient175186/625; its value at z_L is
30704101/62500000>0. Thus u>0 on the entire arc. The denominator of alpha
is negative on[3/20,9/50], and f_star<=0, so alpha>=0. Also1-alpha>0:
subtracting its numerator from its denominator gives
56z^3-53z^2-40z-3<0 on that interval. Therefore all flow probabilities in(A3)
are physical, with positive margins for x,R,1-R,1-alpha and u. The only zero
is alpha at the shared corner. One has0<w_f<=w_star<13/50 and P0>=147/200.

For the derivative, w_f'-1 has denominator
3(8z^3-51z^2+55z+2)^2 and numerator

    -192z^6+2448z^5-16203z^4+32030z^3
                           -15219z^2-7980z+3576.

Its minimum Bernstein coefficient on[3/20,9/50] is
7096680213357/3906250000>0. Thus w_f'>1. Along the return,

    D_f=-2(z-2)(z-1)(7z+3)/(8z^3-51z^2+55z+2)<0. (A12)

### One continuous positive-beta return through the corner

Parameterize the joined arc by d=w-z, oriented from the pair endpoint
(z=0,w=w_d(0)), through(z_star,w_star), to(z_L,w_f(z_L)). On the direct arm
d decreases with increasing z because w_d'<1. On the diffuse arm d decreases
with decreasing z because w_f'>1. Thus this is one continuous graph z=z0(d).

At every direct return point, the directional derivative of F0 at fixed d
is negative: it is the negative factor in(A8) times P_w+P_z. At every diffuse
return point it is also negative: P_f,w>0 and w_f'>1 imply
P_f,z+P_f,w<0, while the factor-z/(2D_f) is positive. At the corner the two
branches have equal values and both directional derivatives are strictly
negative. Compactness gives one common negative derivative bound on a
sufficiently small neighborhood of the whole joined arc, branch by branch.

Use coordinates(d,z), so w=z+d. Extend the compact arc a little at each
endpoint, temporarily allowing virtual z near zero. On a thin tube around
z0(d), F0 has opposite strict signs on the two z faces. The same holds for
F_beta, and its derivative in z stays strictly negative on each of its two
analytic branches. Their values agree where the maximum in(A5) switches.
Consequently F_beta is strictly decreasing through that switch as well.
For each d the IVT gives a unique root z_beta(d), and this root is continuous
in d and parameters. This is the elementary monotone implicit-function
argument; no differentiability across the maximum is required.

Truncate the virtual curve at its actual z=0 and z=z_L endpoints. The first
is obtained by the ordinary transverse return equation at z=0; the second
by the transverse diffuse return equation at z=z_L. These two moving d
endpoints converge to the displayed limiting endpoints. Near the first endpoint, partial_w F_beta<0 and partial_z F_beta|d<0 give
dz_beta/dd=-partial_w F_beta/(partial_z F_beta|d)<0. Thus z_beta(d)>=0
on the retained side; farther away z has a positive compact margin. Thus z>=0 on the actual joined curve. Its u,t,x,R and flow bounds persist; v,alpha remain
nonnegative and complementary by the exact maximum construction.

For the pair chart, F_beta(w,sigma)=0 has one continuous solution w_beta(sigma)
near w_d(0), uniformly on0<=sigma<=2, because the beta0 return is independent
of sigma and has nonzero w derivative. At sigma0 this is exactly the z0
endpoint just constructed, by uniqueness. Append this pair segment to the
joined curve. We have produced one continuous physical return family.

### The graph-entry signs and full guards

At the pair endpoint sigma2, the beta0 residual satisfies

    E0=D+2-kw-ly>=2-yw>1,

since0<=k<1,0<l<=1. At the opposite endpoint z_L=153/1000, let w_L=w_f(z_L).
It is exactly16351075/247762329. Direct arithmetic gives

    U/8-V/9=947800254229/495524658000000>0,
    D-2V/3=-1920310952813/247762329000000<0.

Since8k+9l>=6, we have kU+lV>=2V/3, so E0<=D-2V/3<0. These endpoint
signs persist on the selected positive-beta return family, uniformly on
compact raw parameter sets. The IVT produces an actual simultaneous return
and graph entrance. At that point the projection in(A6) is the identity.

The macro guards have uniform margins. At beta0, every point on the family
has y<=1/10,z<=1/5,w<=13/50. Player0's Quit endpoint is at most257/500.
Its Continue output is at least3/5 on the direct and pair parts, and at least
147/200 on the diffuse part. Thus its Continue guard persists for small beta.
All core owners are indifferent, except inactive2 on a pair where its guard
is exactly beta sigma. The local graph wash has its verified passive0 guard.

This is the complete reward-query census. At a core123 root, player0's
Continue branch uses its four listed passive core entries; its Quit branch
uses only its own participant entries and grand reward. A core owner uses
its three listed participant entries, its singleton comparisons and its
one listed passive pair. At a solo flow the prescribed payoff uses only a
singleton column, and a deviator can add only itself, querying one pair
reward in its own row. Pair rewards containing0 may be arbitrary and enter
only the finite mesh constant below. No other nonsingleton coordinate or
nonzero-owner grand reward occurs in a prescribed payoff or in that player's
unilateral deviation. Thus the unlisted coordinates need no restriction.

Fix the resulting return before choosing accuracy. Section4's finite periodic
consumer applies with the general endpoints(A3)--(A4), omitting flow3 when
alpha0. Every deviator still faces opponent absorption at least x>0 per word,
and its target is the fixed original vector ell+(3alpha,u,t,v).

### Exact arithmetic reproduction

For any displayed polynomial, substitute z=zlo+(zhi-zlo)s and
w=wlo+(whi-wlo)t. If the resulting coefficients are d_pq and bidegree(n,m),
the Bernstein coefficient(i,j) is sum_(p<=i,q<=j)
d_pq binom(i,p)/binom(n,p) binom(j,q)/binom(m,q). The univariate version is
the same formula with the second factor omitted. Every polynomial and interval
needed for the certificates is given above; no numerical trajectory is used.

## 4. Finite flows, one seam, and all behavioral deviations

At the selected return write V=(3alpha,u,t,v), B for the macro output,
and Q=(S,0,0,0). For each N the exact backward wash from B ends at Q_N,
with E_N=||Q_N-Q||_infinity tending to zero. Its roots and annotations are
uniformly bounded. The following proof compiles those already produced data.

The singleton columns of Gamma are

    col2=(-1,1,0,1), col0=(0,2,2,-1), col3=(3,-3,-1,0).

Backward singleton prefixing with aggregate hazard rho maps an input C to
rho colj+(1-rho)C. The following three arcs therefore close the return:

    Q --owner2, aggregate R--> L=(0,R,0,R),
    L --owner0, aggregate x--> M=(0,U0,2x,V0),
    M --owner3, aggregate alpha--> V when alpha>0.

Here U0,V0,x,R are(A3). If alpha=0, M=V and the final flow is omitted.
If alpha>0, complementarity gives V0=0, so the final owner has zero cap.

At partial aggregate hazards rho, their values are explicitly

    owner2: ((1-rho)S-rho, rho, 0, rho), 0<=rho<=R;
    owner0: (0, R+(2-R)rho, 2rho, R-(1+R)rho), 0<=rho<=x;
    owner3: (3rho, (1-rho)U0-3rho, 2x(1-rho)-rho, 0),
             0<=rho<=alpha, when alpha>0.

Every coordinate is nonnegative throughout: these are straight segments
between the displayed nonnegative endpoints. In a positive flow3 block its
input V0 is zero, as required. The current solo owner's
coordinate is identically zero, so its policy mixing and Continue equation
are exact. Every other player Continues, with its endpoint exactly equal
to the displayed value.

Replace a solo-j aggregate hazard h by n equal hazards

    delta_j=1-(1-h)^(1/n).

Their aggregate hazard remains h exactly, and every within-block value
belongs to the same segment. For an inactive player i, its forced-Quit
native payoff is delta_j Z_i({i,j}). Let

    C=max(0, Z_i({i,j}): j in{0,2,3}, i!=j),
    eta_n=C max(delta_0,delta_2,delta_3).

Because the displayed native value is nonnegative, this Quit endpoint is
at most the displayed value plus eta_n. The owner itself has zero Quit
error. Thus all flow guards are verified and eta_n tends to zero. Only the
finite positive maximum of the queried pair rewards enters C. For an omitted
flow3 block set delta_3=0.

### The finite periodic word

Repeat the following finite word forever:

    diffuse3: V to M, omitted when alpha=0,
    diffuse0: M to L,
    diffuse2: L to Q,
    one empty row: annotation Q to annotation Q_N,
    the N exact wash roots in chronological reverse order: Q_N to B,
    the fixed macro: B to V.

The empty row has all prescribed hazards zero. Its Quit endpoint is native
zero, bounded by Q coordinatewise. Its Continue and policy annotation
defect is exactly Q_N-Q, with absolute value at most E_N in each coordinate.
Every other policy and Continue equation is exact. Every other Quit
endpoint is at most its annotation plus eta_n. All words start at the
same fixed value V, independent of N and n.

For any deviator i, the opponents' absorption probability over a complete
word is at least x. If i=0, use owner2's aggregate hazard R>=x. If i!=0,
use owner0's aggregate hazard x. Extra wash and macro hazards only improve
these bounds. This estimate is independent of the deviator's whole law,
including Never, and of N and n. Hence the expected number of reached
copies of the empty seam is at most sum_(k>=0)(1-x)^k=1/x.

Policy telescoping now gives

    |actual terminal payoff_i-(ell_i+V_i)|<=E_N/x.

For an arbitrary complete unilateral replacement, Continue is exact except
at the same seam, and the error eta_n is charged only if the deviator
Quits while still live. That event happens at most once. Its expected
terminal payoff is therefore at most

    ell_i+V_i+eta_n+E_N/x.

Equivalently add eta_n to every annotation: every nonseam Continue endpoint
still lies below the lifted annotation, because it transports at most the
same added constant. Seam error is then summed over its expected visits.
Bounded surviving remainders vanish by geometric opponent absorption.
Consequently the prescribed profile's full terminal exploitability is at
most

    eta_n+2E_N/x.

This bound covers arbitrary behavioral deviations, not just periodic laws
or one-step deviations. No Nash tail is assumed at the empty seam.

For each positive accuracy choose N and n so both errors are small. The
payoff target is the fixed vector ell+V. If L is the finite word length,
the expected absorption date under every unilateral replacement is at
most L/x. With an original absolute reward bound M_r, the difference
between its finite-horizon average payoff and terminal payoff is at most
2M_r L/(x H) at horizon H. Thus one chosen profile works against every
complete deviation over every sufficiently long horizon, proving the
uniform-equilibrium contract directly.


## 5. Exact nonredundancy calibration

Take ell_i=1, the displayed Gamma, and additive passive native rewards.
Set proper nonsingleton participant rows to(e,h1,e,h3) and the native grand
reward to(10,-2,-e,-1), where0<e<=1/100 and0<h1,h3<=1/2000.
Put h=max(h1,h3). The complete finite tests below hold on this box.
The new theorem includes
its particular direction

    e=beta, h1=beta/10, h3=beta, 0<beta<=1/2000,     (N1)

when beta is also below the produced existence threshold. This last
restriction is essential; no numerical value of that threshold is asserted.
The following comparisons exhaust the specified selectors, not every
conceivable equilibrium certificate.

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

### Separation from the prior premium constructions

On(N1), max(h1,h3)=e. The quantitative relative-premium criterion requires
max(h1,h3)<=e/250. The signed-chamber criterion at this background requires
max(h1,h3)<=3e/11200. The pair-contraction criterion requires e<=h1/3 and
e<=h3, and its first inequality fails. The equal-premium independent-scale
rectangle requires h1=h3. The cone ratio criterion requires c<5/9, while
the closed-wedge criterion requires1<c<2 and3c/2<=a<3. Thus(a,c)=(1/10,1)
fails both. The three-flow construction proves UE on that previously
surviving direction and on the band(T), rather than merely strengthening a
conclusion on an already covered class.

The complete signed-chamber role pattern is

    [0,g1,-g2,g3; k0,0,1,-c0; A0,-h0,0,-h3; -l0,-d,1,0],

with every displayed parameter except g1,h0 positive. Role3 must be original2
or3, since it needs two negative entries. If role3=2, its positive target
forces role2=0 and the remaining two-positive role1 is original1; its entry
toward original2 has the wrong sign. If role3=3, its positive target forces
role2=2; role1's negative entry toward3 forces role1=1 and then role0=0.
The identity is the only embedding, including the literal fixed-matrix tests.

Positive row rescaling does not evade the tests. Rows1,3 are normalized by
their positive singleton entry, restoring their premiums. At this background
the signed-chamber constants are K=7,xi0=1/100,H0=4/3 and
kappa=min(1,xi0/(4H0K))=3/11200. Scaling row2 by s>0 gives H0=4s/3 and
kappa<=3/(11200s), while its minimum premium becomes se. The permitted
kappa b remains at most3e/11200. Pair inequalities scale on both sides.

## 6. Source correspondence and formalization handoff

The target is `quittingUniformEquilibriumPayoffConjecture` in
`UniformEquilibrium/Quitting/Conjecture/Basic.lean`; its arbitrary Fin4 case
remains open. The terminal endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Section4 also proves the fixed-target finite-horizon conclusion directly.

The finite-flow interfaces are `CompatibleFiniteJumpFlowWord.execute_error_and_debt_le`
and `repeatedSingletonProfile_error_and_debt_le` in
`UniformEquilibrium/Quitting/EssentialAPS/FiniteJumpFlowCompiler.lean`.
They price a supplied viable flow; Sections1--3 produce all flows, the graph
and the return from the raw table. The infinite-path endpoint comparison is
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
The one-seam periodic bound above has its own full proof, so no infinite
semantic tail is assumed supplied or executable after infinitely many dates.

A Lean implementation can separate the parametric analytic graph, exact
rational interval certificates, raw-table macro producer, and periodic
behavioral consumer. Every producer witness must be constructed from(T),
not assumed as a structure field. The graph and new return are ordinary
mathematics here. No new checked Lean theorem, arbitrary-table closure, or
unrestricted counterexample is claimed.
