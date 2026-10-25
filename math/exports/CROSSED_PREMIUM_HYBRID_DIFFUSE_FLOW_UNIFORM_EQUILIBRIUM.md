# Hybrid cores and three diffuse flows for both crossed premium regions

Fin4 remains open. This theorem produces uniform equilibria in two crossed
premium regions and their a=3 boundary. It includes the reference directions
(a,c)=(1/10,2), (4,1/2), and (3,1/2).
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

**Theorem.** Suppose (a,c) belongs to one of the following sets:

    U: 0<a<3, c>1, 2a<3c;
    L: a>3, 0<c<1;
    B: a=3, 0<c<1.                              (T)

For each such(a,c), there is beta0(a,c)>0 such that every table above with
0<beta<beta0 has a uniform-equilibrium payoff. One positive beta0 works on
every compact subset of U, on every compact subset of L, and on every compact
subset of B separately. No uniformity across their boundaries or joins is
asserted; in particular, the finite-prefix bound in L may diverge as a tends
to3. The threshold is independent of ell and all free reward coordinates.
The flow mesh and finite-horizon threshold may depend on their magnitudes.

The conclusion is one fixed target before accuracy: for each epsilon>0,
one behavioral profile delivers that target within epsilon and bounds every
complete unilateral deviation's gain by epsilon over all sufficiently long
finite horizons. The producer below constructs its hybrid graph, return
and profiles entirely from the raw reward table. Its three diffuse singleton
flows are implemented by finite meshes; no continuous-time game is assumed.

## 1. A produced continuous hybrid core

Write core inputs as(u,t,v), for players1,2,3, and core hazards as(y,z,w).
The exact triple input and output maps are

    I_beta(q)_1=[a beta(z+w-zw)-z+3w]/[(1-z)(1-w)],
    I_beta(q)_2=[beta(y+w-yw)+2y+w]/[(1-y)(1-w)],
    I_beta(q)_3=[c beta(y+z-yz)-z+2y]/[(1-y)(1-z)],
    Q_beta(q)=beta(a(z+w-zw),y+w-yw,c(y+z-yz)).

Only the seven listed passive entries and nine listed core participant
entries are used in these maps and the passive0 recurrence. All bounds below
can be common on a fixed compact subset of any one of U,L,B.

**Local producer.** For all sufficiently small beta>0 there is a produced
continuous Lipschitz function T_beta on a fixed small quadrant u,v>=0,u+v<=rho, with

    Psi_beta(u,v)<=T_beta(u,v)<=C(u+v),
    Psi_beta(u,v)=u/3+v+C_pair*u*v,
    C_pair=(9+a beta+3c beta)/[3(6+2a beta+3c beta)]. (2)

Every point(u,T_beta(u,v),v) has a selected full core Nash root, using
triple123 or pair13 and permitting zero hazards, whose output lies on the same
graph and whose outer coordinates contract by C beta. Root selection is continuous where the two
supports meet. Every stopped pair continuation remains legal forever.
For passive0 input p in a positive compact interval, the full roots are Nash
and have a continuous positive axis limit S_beta=p+O(u+v), uniformly.
The graph and axis function depend continuously on parameters within each
of U,L,B. Subsections1.1--1.5 construct it on U without a finite stopping
bound. Subsection1.6 constructs finitely many analytic sheets on L, each
feeding a finite triple prefix into the legal pair wash. Subsection1.7
constructs an analytic graph on B, with an exact solo3 axis.

### 1.1. Leading spectral coordinates and exact inequalities on U

Throughout Subsections1.1--1.5 assume (a,c) is in U. Let

    G=[0,-1,3;2,0,1;2,-1,0], P=[0,a,a;1,0,1;c,c,0].

The leading hazard map is B=G^-1 P. Its characteristic polynomial times8 is
p(X)=8X^3+5(c-1)X^2-(3ac+a+2c)X+2ac. The coefficients of p(-X) have
exactly one sign change, so Descartes' rule gives one negative root-r,
counted with multiplicity; it is therefore simple. The root identity gives
r>5(c-1)/8. The other eigenvalues have positive real parts. Their sum is
r-5(c-1)/8 in(0,r), and their product is ac/(4r). If they are complex, their
modulus is less than r because p(-r)=0 gives8r^3>2ac. Hence their spectral
radius is strictly less than r in every case.

Normalize the negative right eigenvector of B as

    E=(ey,1,ew), ey=(r-c)/(c+2r), ew=(r-a)/(a+3r).

For q=(y,z,w), put s=(Y,W)=(y-ey*z,w-ew*z). Then the leading map is

    s'=A s, z'=f(s)-r z,
    f=FW*W-FY*Y, FY=3(c-1)/4, FW=(3-a)/4,
    xi=1-3ew=4a/(a+3r), eta=1-2ey=3c/(c+2r),
    k=a(1+r)/(a+3r), delta=FY*eta/2,
    A=[c/2-delta, eta*FW/2; -xi*FY/3, k].         (3)

Write A11=c/2-delta. The exact dissipation identity is

    f(A s)=theta*f(s)-C0*Y,
    theta=k-delta=r-(9c-5)/8<r,
    C0=(c-1)(3c-2a)/8>0.                         (4)

The active cone is Y,W>=0,f>=0. Its boundary ray W=FY*Y/FW maps to

    (Y',W')=(cY/2,a(c-1)Y/(3-a)),

and its W-axis maps to(A12 W,kW). Thus A maps every nonzero point of that
cone into the strictly positive quadrant, with a uniform linear margin on
compact parameter sets.

The following useful inequalities are exact. Since
p(-c/2)=c(6ac+10a+c^2-c)/4>0, r>c/2 and eta<3/2. In addition

    A11>0, 0<k<r,
    delta<9(c-1)/16,
    r-k-delta=1/2+9(c-1)(2r-c)/[8(c+2r)]>1/2.    (5)

For A11, use r>5(c-1)/8 and
A11=c(8r+9-5c)/[8(c+2r)]. Define derivative bounds

    P0=FY/r, Q0=FW/r*(1+delta/r).

They satisfy

    Q0*k<FW, xi*Q0<3,
    1-A11/r-xi*Q0/3
        >[(c-1)/16+a/3]/r>0.                    (6)

Indeed xi*FW/3=k-a/3 in(0,k), and (5) gives k(1+delta/r)<r.

### 1.2. A complete leading obstacle construction

On the positive s quadrant consider continuous homogeneous functions G with

    0<=G<=max(f,0)/r,
    -P0<=G_Y<=0, 0<=G_W<=Q0                     (7)

in the Lipschitz/difference-quotient sense. Zero belongs to this closed class.
Use the explicit norm ||s||=P0|Y|+Q0|W| and distance
sup|G1-G2|/||s||. Its first column bound is strictly below r by(6); its
second is k+delta/(1+delta/r)<k+delta<r. Thus ||A||<r. Set

    UG=0 when f<=0,
    UG=[f-G(A s)]/r when f>0.                    (8)

The argument A s is in the positive quadrant when needed. By (4),
G(A s)<=max(theta,0)f/r<f, so UG is strictly positive on the active set and
lies below f/r. Its zero extension is continuous and Lipschitz.
At differentiability points, writing(p,q)=DG(A s), its derivatives are

    (UG)_Y=(-FY-p*A11+q*xi*FY/3)/r,
    (UG)_W=(FW-p*A12-q*k)/r.                     (9)

Bounds(6) imply preservation of(7); the upper Y and lower W bounds are
strict on the active set. The lower Y bound is -P0, and the upper W bound
is Q0 by definition. These derivative statements also hold as coordinate
increment bounds; A is invertible, so the ordinary a.e. Lipschitz chain rule
suffices, followed by integration on lines. The factor ||A||/r<1 makes(8)
a contraction. Its fixed point is therefore a produced continuous homogeneous
function, with no supplied phase itinerary.

Its outer-cap map is

    u=3W-xi*G(Y,W), v=2Y-eta*G(Y,W).              (10)

It covers the entire nonnegative(u,v) quadrant uniquely. Indeed u is strictly
increasing in W, with derivative at least3-xi*Q0>0, and nondecreasing in Y.
For fixed u>0 solve uniquely for W(Y). At Y=0 one has G>0, hence v<0.
For large Y, f<=0, G=0, W=u/3 and v=2Y tends to infinity. Along this curve
v strictly increases, because v_Y>=2,v_W<=0 and W_Y<=0. Thus every v>=0
has exactly one solution. The u=0 boundary is W=0,G=0,Y=v/2. These facts
hold using finite difference quotients as well as derivatives. The inverse
is locally uniformly Lipschitz, since

    det D(u,v)/D(W,Y)=6-3eta*G_Y-2xi*G_W>0.

When the outer caps are nonnegative, the corresponding hazards are physical:
y=(v+z)/2,w=(u+z)/3, with z=G>=0. Equation(8) supplies a triple continuation
on the active part; the stopped part is the leading pair wash.

### 1.3. Exact pair wash and exact contact identity

Put alpha=a beta,gamma=c beta. The exact pair hazards at(u,v) are

    w=u/(3+alpha+u), y=v/(2+gamma+v).

Their outer outputs are(alpha*w,gamma*y). Direct expansion of(2) gives

    H*Psi_beta(u,v)-2y-w=Psi_beta(alpha*w,gamma*y),
    H=(1-y)(1-w).

On this surface the quiet2 guard, divided by beta, is

    g/beta=(c-1)y-(1-a/3)w+(1+C_pair*a*c*beta)yw.  (11)

Its legal region is invariant for all small beta and radius. To see this,
write A0=c-1,B0=1-a/3,L0=1+C_pair*a*c*beta. On g>=0,

    w/y<=A0/(B0-L0*y).

The next hazard ratio is

    (w_next/y_next)/(w/y)
       =(a/c)*(2+c beta+c beta*y)/(3+a beta+a beta*w).

It is at most q<1 uniformly, since2a<3c. Choose the radius so
q/(1-L0*y/B0)<=1. Then w_next/y_next<=A0/B0, which is sufficient for the
next guard. Both hazards decrease. The axis y=0 permits only w=0; no division
is used there. This proves every later pair guard.

For a triple, use the exact rational maps I_beta,Q_beta displayed above, and F_beta=I_beta^-1 o Q_beta in hazard coordinates.
Use the same linear coordinates q=(Y+ey*z,z,W+ew*z). Let C=t-Psi_beta(u,v).
There is a unique analytic critical height z=h_beta(s) solving C(I_beta)=0.
At beta=0,z=0 solves this identity for every s, so h_beta/beta is analytic.
Put f_beta=-h_beta/beta. Uniformly near0,

    f_beta=f+O((beta+|s|)|s|).

Write F_s,F_z for the exact output in these coordinates, and define

    K_beta(s,z)=[F_z(s,z)-h_beta(F_s(s,z))]/beta.   (12)

All normalized maps extend analytically through beta0. At the origin their
leading derivatives are

    F_s/beta=A s+O((beta+|s|+|z|)(|s|+|z|)),
    K_beta=f(s)-r z+O((beta+|s|+|z|)(|s|+|z|)).    (13)

The same estimates hold for first derivatives. In particular D_z(F_s/beta)
is arbitrarily small on a small neighborhood.

There is an EXACT positive contact factor b_beta(s), tending to1, such that

    K_beta(s,0)=b_beta(s)f_beta(s).                (14)

Indeed at physical z=0, C(Q_beta)=H C(I_beta) by the pair identity. Factor
C(I_beta(s,z))=J_beta(s,z)(z-h_beta(s)), with J_beta>0 near4/3. Substituting
input and output gives b=H*J_input/J_output. This exact identity prevents an
uncontrolled additive error at the stopping boundary.

### 1.4. The exact obstacle operator

Fix a compact parameter patch and freeze the preceding weighted norm at
its center, shrinking the patch so ||A||<r uniformly.
Choose small positive enlargements P1>P0,Q1>Q0 with
Q1-Q0>(P1-P0)A12/r. They can be chosen so that every strict inequality in
(6),(9) remains strict for p in[-P1,0],q in[0,Q1], and xi*Q1<3.
Choose L>1/r sufficiently close to1/r that L*max(theta,0)<1.

On the quadrant ball D={s>=0,||s||<=rho}, use Lipschitz functions satisfying

    G=0 if f_beta<=0, 0<=G<=L*max(f_beta,0),
    -P1<=G_Y<=0, 0<=G_W<=Q1.                     (15)

This is a nonempty closed class in the weighted norm; zero belongs to it.
On f_beta>0, define z_G(s) as the root of

    K_beta(s,z)=G(F_s(s,z))/beta,                 (16)

and set UG=z_G+beta*f_beta. On f_beta<=0 set UG=0.

Here are all needed uniform local estimates. Choose the gradient enlargement
first, then shrink beta and rho. For0<=z<=L_z*f_beta, with1/r<L_z<L,
F_s is in the positive quadrant and contracts its adapted norm by
beta(||A||+epsilon). Positivity follows from the strict active-cone image
margin in Subsection1.1. The dissipation identity(4), the first derivative estimates
in(13), and |s|<=C(f_beta+Y) on the active set give

    f_beta(F_s)/beta<=theta1*f_beta-C1*Y,
    theta1<r, C1>0, L*max(theta1,0)<1.            (17)

The error terms are at most epsilon|s|. The negative Y term absorbs their
Y component, while the strict gap r-theta absorbs their f_beta component.
These are ordinary Taylor estimates from the displayed analytic maps.

At z=0, (14),(15),(17) give a strictly positive left-minus-right side of(16),
bounded below by a positive multiple of f_beta. At z=L_z*f_beta it is
negative, by K_z close to-r. Every z difference quotient is strictly negative,
since D_z(F_s/beta) is small and G has bounded Lipschitz constant. Thus z_G
exists uniquely, is Lipschitz, and satisfies

    m*f_beta<=z_G< L_z*f_beta

for a common m>0. Taking beta small ensures UG<=L*f_beta and actual z_G>0.

For derivative bounds, implicit differentiation gives(9), with p,q evaluated
at F_s, up to arbitrarily small uniform errors. The lower Y bound has slack
P1-P0, the upper W bound has slack
Q1-Q0-(P1-P0)A12/r, and the other two bounds have strict slack from(6).
Thus(15) is preserved. This calculation is valid a.e.: the root is Lipschitz,
and s -> F_s(s,z_G(s)) is a small Lipschitz perturbation of the invertible
linear map beta A, hence locally bi-Lipschitz. Its inverse preserves null
sets, so the Lipschitz chain rule applies. The zero extension is continuous
and locally Lipschitz because UG<=L*f_beta^+; integration of the a.e. bounds
gives the global coordinate increment bounds in(15).

For two graphs the implicit slope estimate gives

    ||UG1-UG2||_* <= (||A||+epsilon)/(r-epsilon) ||G1-G2||_* < ||G1-G2||_*.

This produces a unique exact fixed graph G_beta. On its active part the
physical hazard is z=G_beta+h_beta=z_G>0. On its stopped part z=h_beta>=0
is the virtual triple hazard at the critical pair surface. At contact
f_beta=0, z=0, and (17) places the next base strictly in the stopped region.
Pair and triple roots agree there exactly. Picard convergence gives joint
continuity in parameters. Overlapping local parameter patches agree by
uniqueness after restricting to a common small invariant neighborhood.

### 1.5. The exact graph covers all small outer caps

For fixed u,v>=0 and z>=0, the outer input equations give

    y=[v(1-z)+(1-c beta)z]/[2+(v+c beta)(1-z)],
    w=[u(1-z)+(1-a beta)z]/[3+(u+a beta)(1-z)].

Let s(u,v,z)=(y-ey*z,w-ew*z). In a small common neighborhood this is in the
positive quadrant and

    partial_z s_Y=eta/2+o(1)>0,
    partial_z s_W=xi/3+o(1)>0.

Solve the scalar equation

    z=h_beta(s(u,v,z))+G_beta(s(u,v,z)).           (18)

At z=0 its left-minus-right side is nonpositive: G_beta+h_beta>=0 on both
the active and stopped regions. Its z derivative in the Lipschitz sense is
at least1-xi*Q1/3-o(1)>0, since G_Y<=0 and Dh_beta=O(beta).
The initial deficit is O(u+v). Hence there is exactly one nonnegative root,
bounded by C(u+v), depending continuously and Lipschitzly on the inputs.
Taking u+v small keeps the whole root bracket inside D.

Define T_beta(u,v)=I_beta(q)_2 at this root. Since
C(I_beta)=J_beta(z-h_beta)=J_beta G_beta>=0, it satisfies(2).
On the active part select the physical triple root. Equation(16) puts its
output on the same graph. On the stopped part select the pair root. Its
quiet2 guard is nonnegative: the virtual triple height h_beta>=0 means
Psi_beta>=tcrit_beta at the same u,v, since the virtual t(z) is increasing.
The next pair guard remains legal by Subsection1.3; its output lies on the same
stopped graph by uniqueness in(18). Thus the selected roots are actual and
all their continuations are produced. At the contact the two roots coincide,
so root selection is continuous.

Every outer output is O(beta(u+v)). All selected hazards are O(u+v), including
the stopped pair. This gives the asserted contraction. For passive0 input p
in a fixed positive compact interval, its Continue value stays away from0,
while its Quit value is O(u+v) under the row0 upper bounds. Summed hazards
are finite and geometric, so every later root remains fully Nash. The passive
axis limit exists, is p+O(u+v), and is continuous by uniform geometric tails.
The whole-graph bound T_beta>=Psi_beta is exact, not merely a tangent estimate.

### 1.6. A finite-sheet producer on L

Now fix a compact subset of a>3,0<c<1. All constants and the number of
needed sheets may be common on this compact set.

#### The exact pair surface and its legal side

Write alpha=a beta,gamma=c beta and

    Psi_beta(u,v)=u/3+v+C_pair uv,
    C_pair=(9+alpha+3gamma)/[3(6+2alpha+3gamma)].

The pair hazards are w=u/(3+alpha+u), y=v/(2+gamma+v), z=0. Their outer
outputs are(alpha w,gamma y), and, with H=(1-y)(1-w),

    H Psi_beta(u,v)-2y-w=Psi_beta(alpha w,gamma y).

The quiet2 guard divided by beta is exactly

    g=(a/3-1)w-(1-c)y+(1+C_pair ac beta)yw.        (P1)

Its zero set on the pair surface is an analytic contact curve through0.
The legal side is the sector of smaller v/u. Its exact tangent ratio is
(a-3)(2+c beta)/[3(1-c)(3+a beta)], whose beta0 limit is

    R0=2(a-3)/[9(1-c)].                          (P2)

This pair-legal region is invariant. Put A=a/3-1>0, B=1-c>0,
L=1+C_pair ac beta. On g>=0 and a sufficiently small neighborhood,
y/w<=A/(B-Lw). The next hazard ratio is

    (y_next/w_next)/(y/w)
       =(c/a)*(3+a beta+a beta w)/(2+c beta+c beta y).

It is at most q<1, uniformly, since 3c<2a. Shrink the radius so that
q/(1-Lw/B)<1. Then the next ratio is strictly below A/B at any nonzero
contact point, hence the next guard is strictly positive. Both hazards
contract by C beta. The zero axes follow directly without division.

#### Leading reverse seams give finitely many genuine graphs

In the beta0 linearization at the origin, write the core cap as (u,t,v),
and its hazard coordinates as

    y=(v+z)/2, w=(u+z)/3,
    t=u/3+v+4z/3.

Let

    G=[0,-1,3;2,0,1;2,-1,0],
    P=[0,a,a;1,0,1;c,c,0], B0=G^-1 P.

The leading triple map in hazards is B0. Put

    A0=(a-3)/(3a)>0, D0=(1-c)/c>0.

The inverse map in coordinates(u,v,z) is exactly

    u'=(1-A0)u-2D0 v+8z/3,
    v'=[3A0 u+(3+1/c)v+4z]/2,
    z'=-A0 u/2+D0 v/2-2z/3.                     (P3)

Start with the contact ray e0=(u,v,z)=(1,R0,0), and define
e_n=B0^-n e0, interpreting B0 in these coordinates. The starting ray lies
strictly inside D0 v>=2A0 u because D0 R0/(2A0)=a/(3c)>1.

As long as u>=0, the cone

    D0 v>=2A0 u, 0<=z<=3D0 v/8                  (P4)

is invariant under(P3), whenever the next u is nonnegative. Indeed

    z'>=D0 v/4-2z/3>=0,
    z'<=D0 v/2<=D0 v'/4,
    v'>=2v,
    u'<=(1-A0)u-D0 v<u.

Also D0 v'>=2D0 v>=4A0 u>=2A0 u'. Thus consecutive rays have strictly
increasing v/u until they cross u=0. The crossing occurs after finitely many
steps: u decreases, whereas D0 v at least doubles and eventually makes
the upper bound for u' negative. This bound is uniform on parameter compacts.
The same inequalities give z'>=0,v'>0 on the first ray with u'<0.

Put e_(-1)=B0 e0. It has z=0 and strictly positive y,w, and its ratio is
(3c/(2a))R0<R0. The pair sheet is z=0, 0<=v/u<=R0. For n>=1 the nth triple sheet is the
cone spanned by e_(n-1),e_n. Its outer projection is nonsingular because
the projected rays have strictly increasing ratios. The last sheet is
truncated at u=0 if e_n has negative u. On this truncated cone u,v,z>=0,
so y,w>=0. Even if the last virtual endpoint has negative w, every point
up to the u=0 truncation has w=(u+z)/3>=0. The successor of the nth cone
is the preceding cone, and after n steps it lies in cone(e_(-1),e0),
entirely in the legal pair sector. Every earlier successor uses the earlier
physical seam endpoints.

Therefore these finitely many cones tile the entire nonnegative outer
quadrant exactly once. Every point is a nonnegative core height, with the
displayed finite physical triple prefix and legal pair tail. The associated
height is a continuous piecewise linear graph. This proves projection
transversality only for the needed physical sheets; no assertion about all
iterated preimage planes is made.

There is no last-ray ambiguity. If a ray hits u=0 exactly, retain one further
virtual ray. Formula(P3) then makes its u strictly negative, while v,z stay
positive. The extra adjacent plane still has nonsingular outer projection.
On a parameter neighborhood, fix this finite set of planes and choose a last
ray with strictly negative u. Some of the last sectors may be empty after
restriction to u>=0. A finite cover gives compact-uniform choices.

#### Normalized forward equations

For exact hazards q=(y,z,w), the indifference input is

    I1=[a beta(z+w-zw)-z+3w]/[(1-z)(1-w)],
    I2=[beta(y+w-yw)+2y+w]/[(1-y)(1-w)],
    I3=[c beta(y+z-yz)-z+2y]/[(1-y)(1-z)].

The output is Q=beta(a(z+w-zw),y+w-yw,c(y+z-yz)). Define the analytic cap
map F_beta=Q o I^-1 near0. It factors as beta R_beta, with R_beta(0)=0,
and its normalized derivative tends to N=P G^-1.

For each of the finitely many needed n, the normalized forward iterate

    H_n,beta(x)=F_beta^n(x)/beta^n

extends analytically to beta=0 on a fixed neighborhood of x=0. For n=0
it is x; for n>=1 use

    H_(n+1),beta(x)=R_beta(beta^n H_n,beta(x))/beta^n.

The apparent division is removable because R_beta vanishes at0. These maps
and their derivatives are bounded on common small neighborhoods, and

    D_x H_n,0(0)=N^n.

The exact nth pair-preimage sheet is defined by the analytic equation

    E_n,beta(x)=H_n,2-H_n,1/3-H_n,3
                  -C_pair beta^n H_n,1 H_n,3=0. (P5)

For beta>0 this is precisely
beta^-n [F_beta^n(x)_2-Psi_beta(F_beta^n(x)_1,F_beta^n(x)_3)]=0.
Thus no inverse iterate is evaluated on a fixed domain while beta tends0.

The needed leading sheet planes have nonsingular outer projection by
the leading construction above. The ordinary analytic IFT applied to(P5) consequently produces
graphs t=T_n,beta(u,v), on a common small neighborhood, for every needed n.
They are uniformly close in first derivatives to their leading planes as
beta and the radius tend0. T_0,beta is exactly Psi_beta.

#### Exact seams and actual physical sectors

Let C0,beta be the exact pair-contact curve from(P1). At contact the pair
root has z=0 and quiet2 equality, so it is also the virtual triple root;
its output lies on Psi_beta. Hence C0,beta is exactly the local intersection
of E_0=0 and E_1=0. Its inverse images Cn,beta are equivalently the local
intersections E_n=E_(n+1)=0; define them by these normalized forward equations.

These intersections are analytic curves with leading rays e_n. To verify
transversality, e0 and B0 e0 are distinct rays in the plane z=0, whereas
e1 has z>0. Their determinant is nonzero. Applying powers of the invertible
B0 shows that every three consecutive seam rays are independent. Thus
adjacent sheet planes meet in exactly their stated seam ray. Its v coordinate
is positive, so the two equations solve analytically for u,t as functions
of v. Write the outer seam as

    u=c_n,beta(v), c_n,beta(0)=0.

For the final seam, E_N and E_(N+1) define the curve, but E_(N+1) need not
itself have a nonvertical graph. The transverse intersection just established
is sufficient; only the actually used sheets require graph projection.

The tangent slopes c_n,beta'(0) approach the strictly descending ratios
u_n/v_n. Finitely many curves therefore remain strictly ordered for all
small v>0, beta>0 and the chosen parameter neighborhood. The final curve
has negative u. They split the entire small nonnegative outer quadrant
into the pair sector u>=c_0,beta(v), and the consecutive sectors

    c_n,beta(v)<=u<=c_(n-1),beta(v), u>=0.        (P6)

Put T_beta=Psi_beta on the first sector and T_n,beta on the nth sector.
The graphs agree exactly on their shared curves by(P5), so T_beta is
continuous and piecewise analytic, with a uniform linear bound at0.

Each triple selected from a sector is physical. For n>=2, all three leading
first hazards are bounded below by a positive multiple of u+v on each
nonempty closed physical sector, including its u=0 endpoint. These strict
margins persist. On the first triple sector, y,w have such margins and z vanishes
exactly on C0,beta; its inward transverse derivative is positive at beta0.
Analytic factorization along the exact contact curve therefore gives z>=0
throughout the first sector. Thus no O(beta) perturbation is substituted for
a required zero-hazard boundary equality.

The exact map sends the nth sheet to the (n-1)st sheet. Restricted to these
surfaces it is a local diffeomorphism after dividing output by beta, and
maps Cn to C_(n-1) and C_(n-1) to C_(n-2). The checked leading orientation
and the exact ordered boundaries put its sector image between those two
curves. For n=1, the image lies in the legal pair sector between F_beta(C0)
and C0; the first boundary is strictly pair-legal by the pair calculation above. The image
outer caps are positive and contract by C beta, so remain within the common
local domains. This proves the claimed finite physical triple prefix.

The lower bound by Psi_beta is exact. Outside the pair-legal sector, the
pair guard on Psi_beta is negative. It equals (1-y)(1-w) times
Psi_beta-tcrit_beta, where tcrit_beta is the input t of the virtual triple
with z=0 at the same outer caps. Hence tcrit_beta>Psi_beta there. For fixed
u,v, the virtual triple input t is strictly increasing in z near0. The
physical z>=0 just proved therefore gives T_beta>=tcrit_beta>Psi_beta.
On the pair sector equality holds, and on the shared contact curve both
equalities hold. All native caps are nonnegative.

At C0 the pair and triple roots agree exactly. At any later seam both
descriptions select the same first triple, and eventually reach that same
pair/triple contact. Thus the one-step selected root and successor graph
point are continuous across every seam.

#### Passive guard and the consumer requirements

Every selected hazard is O(u+v), and every successor outer cap is at most
C beta(u+v). The passive recurrence is

    p_next=3y-z+3w+(1-y)(1-z)(1-w)p.

For p in a fixed positive compact interval, small radius makes its Continue
value positive with a fixed margin while its force-Quit endpoint is O(u+v)
under the row0 reward bounds. Geometrically summable hazards keep every
later p in a slightly larger positive interval. Every root is fully Nash.

Finite prefixes depend continuously on their input, and the uniform geometric
tail bound gives a continuous positive limit S_beta with
|S_beta(p,u,v)-p|<=C'(u+v). Thus this producer supplies precisely the continuous
core hypotheses needed by Sections2--4. The return construction below
uses the endpoint inequality a>=3 on this region.

### 1.7. The exact a=3 boundary core on B

Fix a compact set K of 0<c<1 and put a=3. All constants below can be common
on that set, with no uniformity across its endpoints asserted.

**Boundary producer.** There are common rho,C>0 and continuous, indeed analytic,
functions T_beta(u,v) on u,v>=0,u+v<=rho such that

    u/3+v <= Psi_beta(u,v) <= T_beta(u,v) <= C(u+v),
    Psi_beta(u,v)=u/3+v+Cpair uv,
    Cpair=(9+3 beta+3c beta)/(3(6+6 beta+3c beta)).       (B1)

Every point (u,T_beta(u,v),v) has a physical full core root whose output
is again on the graph; the outer caps contract by C beta. The root has
support123 when v>0 and support3 when v=0,u>0. It varies continuously
through the axis. For a passive0 cap p in a fixed positive compact interval,
the entire resulting chain consists of full Nash roots and converges to
an axis point (S,0,0,0), where S is continuous and S=p+O(u+v).

#### Analytic invariant graph

For hazards q=(y,z,w), exact indifference input and output are

    I1=[3 beta(z+w-zw)-z+3w]/[(1-z)(1-w)],
    I2=[beta(y+w-yw)+2y+w]/[(1-y)(1-w)],
    I3=[c beta(y+z-yz)-z+2y]/[(1-y)(1-z)],
    Q=beta(3(z+w-zw),y+w-yw,c(y+z-yz)).                (B2)

Let

    G=[0,-1,3;2,0,1;2,-1,0],
    P=[0,3,3;1,0,1;c,c,0], N=P G^-1.

Since G is invertible, F_beta=Q o I^-1 is analytic near0. Its derivative
is beta N(Id+beta N)^-1. The characteristic polynomial of N, multiplied
by8, is

    p(X)=8X^3+5(c-1)X^2-(11c+3)X+6c.                (B3)

Descartes' rule applied to p(-X) gives exactly one negative root -r,
counting multiplicities; it is simple. The other two eigenvalues have
positive real part: their product is 3c/(4r)>0 and their sum is
r+5(1-c)/8>0. The complementary real invariant plane has left normal

    (-1/3,1,-B), B=(1+2r)/(c+2r)>1.                 (B4)

The simple negative eigendirection and its complementary plane vary
analytically locally in c. Spectral coordinates (s,n) put F_beta in the
form

    s'=L s+f(s,n), n'=-nu n+g(s,n),
    L=O(beta), nu=beta r/(1-beta r),
    f,g=O(beta |(s,n)|^2).                          (B5)

These analytic estimates, and a positive lower bound on nu/beta, are
uniform on a finite collection of complex parameter neighborhoods covering
K. No dominance over the two remaining eigenvalues is needed.

For holomorphic h with h(0)=Dh(0)=0 on a small complex polydisc, use the
norm sup |h(s)|/|s|^2. The graph transform is

    (Th)(s)=[g(s,h(s))-h(Ls+f(s,h(s)))]/nu.          (B6)

On a sufficiently large fixed ball in this norm, the first term is
bounded independently of beta, and the second has norm O(beta ||h||).
Choose the radius and beta small. Differences coming from g have norm
O(radius) times the graph distance. Differences in h at the contracted
argument contribute O(beta); changes in that argument contribute
O(beta radius^2), by the Cauchy derivative estimate |Dh(s')|=O(|s'|).
Thus (B6) is a contraction, preserving the ball. Its fixed point gives
an invariant graph tangent to the plane (B4). The removable beta0
singularity follows from g/beta analytic and h(beta psi)/beta analytic
for functions vanishing to second order. Uniform holomorphic convergence
and Cauchy estimates give a common C2 bound and analytic parameter
regularity. The graph is nonvertical in t, so it has the form

    t=T_beta(u,v), DT_beta(0)=(1/3,B).              (B7)

Patchwise constructions agree by uniqueness in the weighted analytic
class.

There is an exact invariant line, for every beta and c:

    (u,t,v)=(u,u/3,0),
    (y,z,w)=(0,0,u/(3+3 beta+u)),
    Q=(3 beta w,beta w,0).                         (B8)

It lies in the plane (B4). In spectral coordinates it has n=0; g vanishes
on it and s' remains on the same line. The graph transform starting at
h=0 therefore vanishes there at every iterate. Consequently

    T_beta(u,0)=u/3                                 (B9)

exactly, not merely to first order.

#### Physicality and comparison with the pair surface

For fixed small u,v and a trial z, the other two hazards are

    y=[v(1-z)+(1-c beta)z]/[2+(v+c beta)(1-z)],
    w=[u(1-z)+(1-3 beta)z]/[3+(u+3 beta)(1-z)].       (B10)

Substitution in I2 gives t(z), whose derivative tends uniformly to4/3
at the origin. Hence t(z) is strictly increasing on a fixed small
neighborhood. Its threshold tcrit_beta(u,v)=t(0) is analytic and satisfies

    tcrit_beta(u,0)=u/3,
    partial_v tcrit_beta(0,0)=(2+beta)/(2+c beta).   (B11)

By (B7), (B9), and (B11), both T_beta-tcrit_beta and T_beta-Psi_beta vanish
identically on v=0. Their derivatives in v at the origin are respectively

    (1-c)[1/(c+2r)-beta/(2+c beta)],
    B-1=(1-c)/(c+2r).                              (B12)

They have a common positive lower bound for c in K after choosing beta
small. Uniform C2 bounds then give a common kappa>0 and smaller rho with

    T_beta-tcrit_beta >= kappa v,
    T_beta-Psi_beta >= kappa v                     (B13)

throughout the nonnegative triangle. This proves the lower bounds in
(B1); its upper bound follows from T_beta(0)=0 and the C1 bound.

For v>0, (B13) and monotonicity in z give a unique positive z. Formula
(B10) gives positive y,w if beta<min(1/3,1/max K). For v=0, (B8) is the
unique local root. All hazards are O(u+v), and they depend continuously
on u,v. Exact graph invariance and (B2) put the nonnegative output back
on the same graph, with outer coordinates at most C beta(u+v).
Choose C beta<1. At the axis, zero-hazard players1 and2 satisfy their
indifference equations by (B8), so the root remains legal there.

#### Passive coordinate and infinite chain

The passive0 update is

    p'=3y-z+3w+(1-y)(1-z)(1-w)p.                   (B14)

The row0 upper bounds put its Quit endpoint at most
1-(1-y)(1-z)(1-w)+10yzw=O(y+z+w). Its cap p' remains in a positive
compact interval if rho is small. Summed hazards along the chain are
O(u+v), because the outer caps contract by C beta. Thus every passive0
guard is legal, every root is fully Nash, and the passive caps converge
with |S-p|<=C(u+v). The geometric tail bound is uniform on the local
domain. Finite iterates are continuous and their tails converge uniformly,
so S is continuous. In particular, uniformly on compact macro domains,

    S(P,beta U,beta V)=P+O(beta).                   (B15)

This supplies the same continuous core interface as the two open regions.
The macro return in Sections2--3 uses a=3 and the strict inequality D-U<0
at its diffuse endpoint. No uniformity with the L producer as a tends to3
is inferred.

## 2. Exact macro charts and compatible diffuse flows

Write Axis_beta(p,u,v) for the continuous axis value produced in Section1.
Uniformly on bounded macro inputs with p in a fixed positive interval,

    Axis_beta(P,a beta U,c beta V)=P+O(beta).      (A2)

The hybrid graph may have corners. The return below uses only this uniform
C0 estimate and the exact height bound T_beta>=u/3+v.
Choose a fixed finite pair slack bound M after the height constant is known;
its choice is specified in Section3, before beta is made small.

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
continuation. Both branch functions F_beta converge uniformly to F0 by the produced
axis bound in Section1. No derivative of the hybrid axis value is used.

There is also a pair chart z=0 with quiet2 output beta(D+sigma),0<=sigma<=M.
Its t input is[beta(D+sigma)+2y+w]/[(1-y)(1-w)]. Its zero-seam
value is yseam_beta=[N-3beta sigma(1-z)]/L at z=0; this is strictly positive
on the pair chart. Choose y by alpha=0, and
use the same formulas(A3),(A6), now with E_beta=D+sigma-T_beta(a beta w,c beta y)/beta.
The inactive2 guard is exactly beta sigma>=0. Its other equations coincide
with the triple chart at z=sigma=0, including the chosen y and axis projection.

## 3. A physical return ribbon and simultaneous graph entrance

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

### A fixed physical ribbon replaces implicit return selection

Use the beta0 return geometry just proved:

* pair arm z=0, w=w_d(0), sigma from M down to0;
* direct arm z from0 to z_star, w=w_d(z);
* diffuse arm z from z_star down to z_L=153/1000, w=w_f(z).

Its reference return is F0=0. On the direct arm both partial_w F0<0 and
(partial_z+partial_w)F0<0. On the diffuse arm the latter is negative.
At the max corner it is negative for BOTH analytic branches. The exact
polynomial certificates for these strict signs are independent of a,c.

Parameterize this compact path continuously by s from its pair-M endpoint
to its diffuse-z_L endpoint. Choose lambda(s) continuous with values[0,1],
equal to0 on the pair arm and a short initial direct segment, equal to1
before the max corner and throughout the diffuse arm. Blend only inside
the direct arm. For a small transverse coordinate n set

    z(s,n)=z_ref(s)+lambda(s)n,
    w(s,n)=w_ref(s)+n,
    sigma(s,n)=sigma_ref(s).                       (H4)

This is a physical ribbon: on the pair arm z stays0, and near the direct
endpoint z is unchanged. Elsewhere z has a positive compact margin, so
z>=0 for small |n|. Also z sigma=0 everywhere. All other strict physical
inequalities of the reference return persist on the ribbon and at small
positive beta. Nonnegative alpha,v and their complementarity are supplied
exactly by the maximum formula, not by perturbing an equality argument.

On the direct arm the transverse derivative is

    partial_w F0+lambda partial_z F0
      =(1-lambda)partial_w F0
         +lambda(partial_w+partial_z)F0<0.

The pair derivative is partial_w F0<0, independent of sigma. The diffuse
derivative is the diagonal derivative. Near the corner both active branch
derivatives have the same strict sign. Compactness therefore gives delta>0
and eta>0 such that on the two full transverse faces

    F0(s,-delta)>eta, F0(s,+delta)<-eta.           (H5)

Uniform C0 convergence from Section1, together with the explicit macro formulas,
preserves these signs for F_beta. Derivatives of Axis_beta are never used.
There is no need to select a return root continuously as s varies.

### The graph-entry signs use the produced obstacle

At the diffuse endpoint z_L the reference values satisfy

    D-2V/3=-1920310952813/247762329000000<0,
    V>0.

The exact bound T_beta>=u/3+v gives

    E_beta <= D-aU/3-cV<0                        (H6)

on the whole endpoint face after shrinking delta and beta. On U, c>1
and a>0, while D_L-V_L=(w_L-z_L)(1-y_L)<0. On L and B, a>=3 and c>0,
and exactly

    D_L-U_L=(y_L-z_L)(1-w_L)=-z_L(1-w_L)/2<0.

Thus the limiting upper bound is strictly negative in every region of(T).
It persists on the whole narrow transverse endpoint face. No normalized
graph limit is needed.

On the pair endpoint U=w,V=y. The upper bound in Section1 gives

    E_beta >= D+M-C(aw+cy).

Choose one fixed finite M large enough to make this >1 throughout a small
endpoint neighborhood, uniformly on the chosen parameter compact set.
The beta0 return is independent of sigma, so increasing the pair slack
changes neither its reference geometry nor any beta0 physical inequality.
After fixing M, choose beta small enough for the macro perturbation bounds.
Thus E_beta is positive on the complete pair endpoint face and negative
on the complete diffuse endpoint face.

### Two-dimensional intermediate value argument

Rescale s to[0,1]. On the rectangle[0,1]x[-delta,delta], F_beta has opposite
strict signs on the n faces, and E_beta has opposite strict signs on the
s faces. Poincare-Miranda supplies a simultaneous zero.

For completeness, apply Brouwer to the continuous rectangle self-map

    (s,n) |-> (clip_[0,1](s+E_beta(s,n)),
              clip_[-delta,delta](n+F_beta(s,n))).

The strict inward signs prohibit a fixed point on any boundary face. At
an interior fixed point neither clipping operation can hide a nonzero
increment, so E_beta=F_beta=0. This elementary proof avoids any claim that
the zero set of F_beta is a curve or connected; it may have many branches.

The actual simultaneous return now feeds the finite-flow consumer in Section4:
one fixed target, every full behavioral deviation, one charged flow-Quit
error, and vanishing finite wash seam error. The positive opponent absorption
bound x persists on the compact physical ribbon.


The macro guards have uniform margins. At beta0, every point on the
reference family has y<=1/10,z<=1/5,w<=13/50. Player0's Quit endpoint is at most257/500.
Its Continue output is at least3/5 on the direct and pair parts, and at least
147/200 on the diffuse part. Choose the ribbon sufficiently narrow; its
Continue guard then persists throughout the ribbon for small beta.
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
The new theorem includes the three directions

    e=beta, h1=beta/10, h3=2beta, 0<beta<=1/4000,     (N1)
    e=beta, h1=4beta, h3=beta/2, 0<beta<=1/8000,      (N2)
    e=beta, h1=3beta, h3=beta/2, 0<beta<=1/6000,      (N3)

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

On(N1), max(h1,h3)=2e. The quantitative relative-premium criterion requires
max(h1,h3)<=e/250. The signed-chamber criterion at this background requires
max(h1,h3)<=3e/11200. The pair-contraction criterion requires e<=h1/3 and
e<=h3, and its first inequality fails. The equal-premium independent-scale
rectangle requires h1=h3. The cone ratio criterion requires c<5/9; the
closed-wedge criterion requires1<c<2 and3c/2<=a<3; the preceding diffuse-flow
raw region requires c<=1. Thus(a,c)=(1/10,2) fails every one of these tests.
On(N2), the pair criterion fails e<=h3, the equal-premium condition fails,
and the earlier lower diffuse region fails a<3. The cone criterion
8a<15(1-c) fails, and the closed wedge requires c>1. Its premium maximum
4e also fails both quantitative relative bounds. The same reasons exclude
(N3), with maximum premium3e and boundary a=3. Thus both new crossed sides
and the added boundary have exact separating directions. The present producer
proves UE on(N1)--(N3) and throughout(T); it supplies actual raw-table coverage.

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

A Lean implementation can separate the leading derivative-cone inequalities,
exact Lipschitz obstacle graph, finite normalized sheets and their ordered
seams, analytic boundary graph, rational interval certificates, continuous
ribbon return, and periodic behavioral consumer. Every producer witness must be constructed from(T),
not assumed as a structure field. The hybrid graph and ribbon return are ordinary
mathematics here. No new checked Lean theorem, arbitrary-table closure, or
unrestricted counterexample is claimed.
