# Unequal participant premiums: the reverse-switch wedge

**Owned internal research note — CODEX_PERIODIC_ADVERSARY, 2026-10-25.**
This continues the consolidated deadlock packet; it is outside that packet's
current publication scope. The proof below is awaiting independent review
of the finite-entry and macro switching joins. It does not settle Fin4.

## Statement and shared construction

Use the fixed native singleton matrix

    Gamma=[0,3,-1,3; 2,0,1,-3; 2,-2,0,-1; -1,-2,1,0],

additive passive native rewards, proper participant native rewards
(alpha,a beta,beta,c beta), and player0 native grand reward10. Here
0<=alpha<=1 and the other three grand coordinates are arbitrary finite
numbers. Original nonempty rewards are ell_i+Z_i(A), with arbitrary
own-singleton levels ell_i; original live/Never rewards remain zero.

**Candidate theorem.** For each fixed

    1<c<2,                 3c/2<a<3,                 (W)

there is beta_0(a,c)>0 such that every 0<beta<beta_0(a,c) in this family
has a uniform-equilibrium payoff. The threshold is uniform in alpha in[0,1]
and independent of ell and the three unqueried grand coordinates.

The construction uses a macroscopic pair13 or triple123 root, then a
finite pair prefix when necessary, an infinite backward triple wash,
the solo2 wash, and the solo0 seam. It supplies each root from the raw
reward formulas. Finite truncations, rather than infinite calendars, are
executed. The common graph lemma and the final two-seam/full-behavioral-cap
consumer are the ones in the [consolidated packet](../exports/TWO_CONTRACTING_BLOCKS_UNIFORM_EQUILIBRIUM.md).
They are not copied here.

## 1. A produced invariant graph with a physical cone

For q=(y,z,w), the triple indifference map I_beta(q)=(u,t,v) is

    u=[a beta(z+w-zw)-z+3w]/[(1-z)(1-w)],
    t=[beta(y+w-yw)+2y+w]/[(1-y)(1-w)],
    v=[c beta(y+z-yz)-z+2y]/[(1-y)(1-z)].              (1)

Its output is beta(a(z+w-zw),y+w-yw,c(y+z-yz)). Thus the exact next-root
map F_beta is analytic and F_beta/beta extends analytically to beta0.
Put G=[0,-1,3;2,0,1;2,-1,0] and P=[0,a,a;1,0,1;c,c,0]. Then

    M=G^(-1)P,  DF_beta(0)=beta M(I+beta M)^(-1).       (2)

The characteristic polynomial of M, multiplied by8, is

    p(x)=8x^3+5(c-1)x^2-(3ac+a+2c)x+2ac.              (3)

Descartes' rule gives exactly one negative root, -r. Since

    p(-c)=3c(a-c)(c+1)>0,
    p(-a)=-4a(a-c)(2a+1)<0,

one has c<r<a. The remaining pair has positive real part: factoring out
x+r leaves a quadratic with positive constant and negative linear
coefficient. For the latter sign, if c>1 put s=5(c-1)/8; p(-s)>0 gives
r>s. These facts also show that A_tangent+rI is invertible.

In continuation-cap coordinates the positive-spectrum plane is

    t=A u+B v,
    A=(1+r)/(a+3r),  B=(1+2r)/(c+2r).                (4)

Indeed (-A,1,-B) is a left eigenvector of PG^(-1) for -r. Direct
substitution reduces its three eigen-equations to p(-r)=0.

By (W), A>1/3 and 5/6<B<1. The normalized triple hazard on this plane is

    z_plane(u,v)=[(3A-1)u-3(1-B)v]/4.                (5)

Thus its physical positive-cap cone is

    u>0, 0<=R=v/u<=R_*=(3A-1)/[3(1-B)].              (6)

Whenever z>=0, the other leading hazards satisfy y>=v/2 and w>=u/3.
The cone therefore has only one exit face, z=0.

The restricted projective map is strictly inward at both endpoints.
At R=R_* its image is gamma R_*, where gamma=3c/(2a)<1. At R=0 its image
is 3c(3A-1)/(8aA), smaller than R_* because

    9c(1-B)<3c/2<4c<8aA.

The projective map is increasing: its determinant is the product of the
two positive-spectrum eigenvalues, hence positive, and its denominator
is positive throughout the physical interval. Consequently it maps the
whole closed interval strictly inside itself. Any strictly interior
entrance belongs to a compact positive invariant subcone.

Apply the packet's weighted C1,1 graph construction in plane/normal
coordinates. First remove any linear tangent-normal coupling by a linear
change using (A_tangent+rI)^(-1). Equation(2) preserves the same splitting
for every small beta. The normal eigenvalue is -r beta/(1-r beta), and
the nonlinear remainder has the required factor beta and vanishing first
derivatives. The graph lemma gives an actual invariant graph, tangent to
(4), with quadratic error and continuous parameter dependence. The strict
projective cone margins persist on it. All triple hazards in the cone
are positive and contract by O(beta). This supplies the infinite triple
wash and its continuous C1 passive axis limit S=p+O(beta).

## 2. A finite pair prefix enters the graph

Let w_* be the unique root in(1/5,1/4) of

    -30w^3-7w^2+1205w-250=0,

and put y_*=3w_*/(10+2w_*), D_*=y_*+w_*-y_*w_*.
This is the common zero-premium solo0/solo2 return calibration.

After k pair roots, the leading active caps, normalized by beta^k, are

    U_k=a^k w_*/3^(k-1), V_k=c^k y_*/2^(k-1),
    R_k=V_k/U_k=R_1 gamma^(k-1), R_1=c y_*/(a w_*).  (7)

The final spectator2 cap is chosen as t_k=A U_k+B V_k, on the invariant
plane. Its last pair guard has the exact leading identity

    t_k-U_k/a-V_k/c
       =-(4r/3) z_plane(U_{k-1},V_{k-1}).             (8)

This follows immediately from

    aA-1=-r(3A-1),  cB-1=-2r(B-1).

Suppose R_1>R_*. Choose the first k>=2 with R_k<=R_*. The entry is finite
because gamma<1. All previous R_j exceed R_*. Moreover

    R_* > R_c=c(3-a)/[3a(c-1)],                       (9)

because R_*/R_c=a(c+2r)/[c(a+3r)]>1 is equivalent to2a>3c.
Thus every earlier small pair guard is strictly positive; its sign is the
sign of R_j-R_c. The last guard is strictly positive by(8), since the
previous state lies outside the plane's physical cone. The macroscopic
first pair guard is also strict: its leading value is

    U_1/3+V_1-D_*
      =(a/3-1)w_*+(c-1)y_*+y_*w_*>0,

where R_1>R_*>R_c supplies the strict linear part.

For an actual fixed k, u_j and v_j under the pair operation are explicit
scalar contractions, independent of spectator t. Place the final state
on the exact invariant graph and solve spectator values backwards using

    t_j=(t_{j+1}+2y_j+w_j)/[(1-y_j)(1-w_j)].           (10)

The initial solo0 condition is t_0=2(u_0-v_0)/3. Together with the axis
return S=r_0/(1-r_0), r_0=(u_0+2v_0)/(3-u_0+v_0), this is a two-variable
C1 system in the macroscopic pair hazards. At beta0 its first equation
is the ordinary pair critical equation, which eliminates y; its second
has the nonzero derivative of the cubic above. The parameter implicit
function theorem therefore produces the actual prefix and return. Every
strict leading guard persists after its beta-power normalization.

If R_1<=R_* and tau_*=A a w_*+B c y_*>=D_*, a single macroscopic pair
root suffices. Its exact convenient coordinates are

    y=[(3+2a beta)w-3beta tau]
        /[10+2c beta+2(1+(a-c)beta)w],                (11)

giving output (3(y+w),beta a w,beta tau,beta c y). The owner2 gap is
beta(tau-y-w+yw). The graph equation has a nonzero tau derivative, while
the return equation has the same nonzero w derivative. This is the same
parameter-IFT construction, including the strict case tau_*>D_*.

### Reviewed complete subcase

For (a,c)=(29/10,11/10), no phase or macro join is needed. Exact rational
bounds give 1.5626<r<1.5627 and .2079<w_*<.2080. Substitution into(4),(7)
gives R_1<R_*, .26790<tau_*<.26809 and tau_*-D_*>.0124. The next normalized
triple hazards lie strictly in the physical cone; their y/w ratio is
between .165 and .167. Therefore the single-pair construction(11), followed
by the produced triple graph, is a complete actual-beta proof for this ray.
Every inequality is strict, so it also covers an unspecified open
neighborhood of this unequal direction. CODEX_ZERO_CAP_CLASSIFICATION
independently checked the rational spectral, cone, entrance, guard, and
return calculations and the original-game semantics. The regularity claim
is C1,1 for the graph and parameter C1 implicit-function closure, rather
than an unproved analyticity claim. This reviewed subcase is preserved as
a finished result; it is not being used to certify the unreviewed joins.

## 3. The remaining entrance uses a macroscopic triple

It remains to treat R_1<=R_* and tau_*<D_*. Use the packet's macroscopic
triple return rectangle 0<=z<=1/8, 1/5<=w<=1/4. At beta0 its solo0 seam
eliminates y exactly as

    y=w(3+z)/(10+2w-8z).

The zero-premium return curve w=w_0(z) is unique, has P_w>960 and
P_z<-150 for the packet's cleared return polynomial P, and stays in the
rectangle. Define

    Bu=z+w-zw, Bv=y+z-yz, D=y+w-yw,
    E=D-aA Bu-cB Bv.                                 (12)

At z=0 on the return curve, E=D_*-tau_*>0. At z=1/8, E<0 uniformly:
aA>1/2 and cB>5/6 imply

    E < y/6+w/2-yw+zw/2+5yz/6-4z/3 <= -1/288,

using y<=1/12 and w<=1/4. Thus there is a plane hit.

Every such hit is automatically physical. Put m=3A-1>0,n=1-B>0.
The identities aA=1-rm, cB=1+2rn turn E=0 into

    r(m Bu-2n Bv)=z(2-w-y)+yw>0.

The output's next triple hazard is

    z_next=[m a Bu-3n c Bv]/4
      =[a(m Bu-2n Bv)+(2a-3c)n Bv]/4>0.              (13)

Its other hazards are positive as well. Hence every limiting shooting
zero enters the strict invariant cone, rather than merely the algebraic
plane. The actual graph and its passive limit are continuous perturbations.
Project vertically onto that graph off the shooting set, keep passive p
unchanged, and use a thin rectangle around w_0(z). Opposite shooting signs
on the z faces and opposite return signs on the transverse faces persist.
Poincare-Miranda gives an actual positive-beta triple entrance and return.
This is the packet's graph-return argument, with the explicit new physicality
identity(13).

## 4. The joins and unrestricted deviations

The phase boundaries in Section2 are R_k=R_*. For fixed(a,c) there are only
finitely many relevant k. They are regular because gamma<1. Let H define
the exact invariant triple graph in continuation coordinates, with H_t>0.
Near a zero-hazard contact, its exact invariance and transverse sign give

    H(Tx)=K(x)H(x), K<0,
    H(Px)=K(x)H(x)+z J(x), J>0.                      (14)

The second identity follows because P=T at z=0; at contact J>0 follows
from H(Px)_t=(1-y)(1-w)>0, H(Tx)_t<0, and z_t>0.

Write g for the signed triple hazard restricted to H=0. The immediate
triple-graph sheet is admissible on g>=0. The one-extra-pair preimage
H(Px)=0 is admissible on g<=0: solving the two transverse scalar equations
in(14) gives precisely these complementary signs. They agree at g=0,
where P=T and the invariant-graph passive limit is the same. The next
triple state is strictly inside the cone because gamma<1. This joins the
k and k+1 constructions without assuming a favorable perturbation sign.
Backward composition preserves the join and all earlier strict guards.

At the macroscopic pair/triple switch tau_*=D_*, the same complementary
sheet argument applies to the outputs of the first root. Its transverse
triple derivative is negative: with u,v fixed, at z0 one has

    y_z=(1-y)(1-2y)/2, w_z=(1-w)(1-3w)/3,

and differentiating (12) gives a strictly negative result since cB>1
and aA>1/2. The return orientation is also explicit. On the solo0 surface,
at a contact z0,

    E_w=6w(cB-6)/(10+2w)^2<0, E_z<0.

Therefore the physical triple arm has z'(w)=-E_w/E_z<0 and lies at w<w_*;
the pair arm lies at w>w_*. The return polynomial increases on both arms:
its derivatives are P_w+P_z z'(w)>0 and P_w>0. The return residual decreases
through the join. Fixed endpoints around w_* retain opposite return signs
for small beta, and IVT completes the equality case.

Player0 is strict at every macroscopic root by the packet's alpha<=1
bounds; throughout the small prefix/wash its positive passive value
stays away from zero and its Quit endpoint is O(total hazard). The solo0
and solo2 guards hold for small beta. Truncate the triple and solo2 washes,
repeat the finite physical word, and apply the packet's two-seam full-cap
bound. The fixed macroscopic solo0 and solo2 hazards give uniform opponent
absorption under every behavioral replacement. This also justifies the
arbitrary signed ell shift and the original uniform-average-payoff limit.
Only player0's grand coordinate is queried.

## Current status and remaining frontier

The isolated strict ray (a,c)=(2.9,1.1) has independently passed review,
including the actual graph, strict cone, macro equations, and original-game
semantics. The systematic wedge proof above replaces that example and is
pending an independent check of Section4's phase and macro joins. No numerical
search is used as a proof. No per-example code or repeated review record is
part of this note.

The missing unequal directions include the boundary 3c=2a, the regions
where the positive-spectrum-plane dynamics leaves its physical cone, and
compatibility of the other macro entrance choices there. These are specific
remaining production questions; a general positive-spectrum plane alone
is not a uniform-equilibrium certificate. The unrestricted Fin4 conjecture
remains open.
