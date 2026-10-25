# Nine independent core premiums produce uniform equilibria

Fin4 remains open. The proof below produces uniform equilibria on an explicit
box of independently varying core participant rewards. The mathematics is
ordinary mathematics, not yet formalized in Lean. The order condition on
two pair premiums is part of the theorem; the unordered box is not claimed.

## Exact raw-table statement

There are four players and one live state. At each live date every player
privately chooses Continue or Quit, with independent randomization and no
public correlation. The first nonempty quitting coalition A absorbs at r(A).
Original live and literal Never pay zero. A unilateral deviation may replace
the player's complete behavioral law, including arbitrary stopping dates and
Never. The own-singleton levels ell_i=r_i({i}) are arbitrary signed numbers.
Write Z_i(A)=r_i(A)-ell_i on nonempty coalitions only.
Require the native singleton matrix

    Gamma=[0,3,-1,3;2,0,1,-3;2,-2,0,-1;-1,-2,1,0]

and precisely these seven passive nonsingleton entries:

    Z0(12)=2, Z0(13)=6, Z0(23)=2, Z0(123)=5,
    Z1(23)=-2, Z2(13)=-3, Z3(12)=-1.

The nine core participant entries, in the indicated order, are

    (Z1(12),Z1(13),Z1(123))=beta(a,b,f),
    (Z2(12),Z2(23),Z2(123))=beta(d,e,g),
    (Z3(13),Z3(23),Z3(123))=beta(h,k,l),

where all nine normalized entries belong to[1,2], independently except
for d>=h. The six proper participant entries of row0 are independently
at most1; its grand reward is at most10. Every unlisted nonsingleton
entry is arbitrary finite data, with no lower or upper bounds.

**Theorem.** One beta0>0 works uniformly over this entire compact normalized
box: every such table with0<beta<beta0 has a uniform-equilibrium payoff,
against all complete unilateral behavioral replacements. The target is
fixed before accuracy. beta0 is independent of ell and the free rewards.

In particular this includes the literal nine-dimensional rectangular box
d in[3/2,2], h in[1,3/2], and all seven other coordinates independently
in[1,2]. This is a specified finite raw class, not an unspecified continuity
neighborhood of equal row premiums.

## 1. The general core map and its negative normal

For hazards(y,z,w) of owners1,2,3 put

    F1=a z(1-w)+b w(1-z)+f zw,
    F2=d y(1-w)+e w(1-y)+g yw,
    F3=h y(1-z)+k z(1-y)+l yz.

The exact indifference input I_beta and output Q_beta are

    I1=[beta F1-z+3w]/[(1-z)(1-w)],
    I2=[beta F2+2y+w]/[(1-y)(1-w)],
    I3=[beta F3-z+2y]/[(1-y)(1-z)],
    Q_beta=beta(F1,F2,F3).

Let G=[0,-1,3;2,0,1;2,-1,0], P=[0,a,b;d,0,e;h,k,0], N=PG^-1.
The map Q_beta o I_beta^-1 is analytic near zero and has derivative
beta N(Id+beta N)^-1. Eight times the characteristic polynomial of N is

    p(X)=8X^3+T X^2+L X+C,
    T=2a-2b-3d-2e-h+6k,
    L=-2ae-ah+bd-2bk-3dk+eh,
    C=aeh+bdk>0.

On the entire pair cube[1,2]^6, L<=-6. Indeed d-2k<=0, h-2<=0, so

    L<=-2e-h+d-2k-3dk+eh
      <=-2+d-2k-3dk<=-1-5k<=-6.

Descartes' rule gives exactly one negative eigenvalue-r, counted with
multiplicity; it is simple. The other eigenvalues have positive real
parts: their product is C/(8r)>0, and their sum is r-T/8>0. For T>0,
p(-T/8)=-LT/8+C>0 proves the latter inequality; for T<=0 it is immediate.

Its left normal is(-A,1,-B), where

    A=(e+r)/(b+3r), B=(d+2r)/(h+2r).               (1)

The remaining eigenvector equation is

    (a-r)(e+r)(h+2r)+(k-r)(d+2r)(b+3r)=p(-r)=0.

Its signs show min(a,k)<=r<=max(a,k), hence1<=r<=2. Consequently

    3/8<=A<=3/4, 1<=B<=4/3,
    A-1/3=(3e-b)/[3(b+3r)]>=1/24,
    B-1=(d-h)/(h+2r), Ab<e<=2, Bh<=d<=2.         (2)

The negative eigenvalue is uniformly separated from the remaining block.
All estimates below can therefore be uniform on the full normalized box.

## 2. A produced physical graph on the whole nonnegative quadrant

There is a produced C2 invariant graph t=T_beta(u,v), with

    T_beta(0,0)=0, DT_beta(0,0)=(A,B),
    ||D^2 T_beta||<=M,

on a fixed neighborhood of zero, uniformly in the nine parameters. Here
is the construction and the boundary detail needed for uniformity at d=h.

Use analytic coordinates(s,n) separating the remaining invariant plane
from the simple negative normal direction. The map becomes

    s'=L_beta s+F(s,n), n'=-nu n+G(s,n),
    L_beta=O(beta), nu=beta r/(1-beta r),
    F,G=O(beta|(s,n)|^2).

On holomorphic h(s) vanishing to second order use the norm
sup|h(s)|/|s|^2 on a small complex polydisc, and the transform

    Th=[G(s,h(s))-h(L_beta s+F(s,h(s)))]/nu.

A sufficiently large fixed norm ball is preserved. The first difference
term has Lipschitz factor O(radius), and the composed h term has factor
O(beta), since its argument contracts by O(beta). Cauchy estimates control
the change in that argument by O(beta radius^2). Thus the transform is a
contraction on a common small polydisc for small beta. Its iterates are
jointly holomorphic in s and parameters. At beta0 the apparent quotient
singularity is removable because h vanishes to second order. Cauchy
estimates on a smaller polydisc give the stated C2 bound and a uniform
parameter derivative of that bound. Finite parameter patches cover the
compact box, and uniqueness identifies the resulting local graphs.

At d=h, the line u=0,t=v is exactly invariant: its core root is
y=v/(2+beta h+v), z=w=0, and Q2=Q3=beta h y, Q1=0. It lies in the
normal plane. The graph transform starting at zero preserves that line,
so T_beta(0,v)=v exactly at d=h. Parameter regularity therefore gives

    T_beta(0,v)-Bv=O((d-h)v^2).                    (3)

For fixed u,v and a virtual hazard z, the other two hazards are exactly

    w=[u(1-z)+z(1-beta a)]
       /[3+beta b+beta(f-a-b)z+u(1-z)],
    y=[v(1-z)+z(1-beta k)]
       /[2+beta h+beta(l-h-k)z+v(1-z)].             (4)

The remaining input t(z)=I2 is strictly increasing near zero, with
derivative tending uniformly to4/3. Its value at z=0 is tcrit_beta(u,v),
and tcrit_beta(0,v)=v(2+beta d)/(2+beta h). Equations(2),(3) imply

    T_beta(0,v)-tcrit_beta(0,v)
      =(d-h)v[1/(h+2r)-beta/(2+beta h)+O(v)],
    partial_u(T_beta-tcrit_beta)>=1/24+O(beta+u+v).

Their brackets are uniformly positive. Thus the graph is physical for
every sufficiently small u,v>=0, including arbitrary v/u ratios and d=h.
Its root has z>=0 and the rational formulas(4) give y,w>=0. All hazards
are O(u+v). Since all nine premiums are positive, its next outer values
beta F1,beta F3 are nonnegative and O(beta(u+v)). Exact graph invariance
therefore gives an infinite physical contracting chain.

For passive player0, iterate

    p'=3y-z+3w+(1-y)(1-z)(1-w)p.

Starting in a fixed positive compact p interval, summability of the hazards
keeps p positive and produces an axis limit Axis_beta(p,u,v), with
Axis_beta=p+O(u+v), uniformly and continuously. Its forced-Quit endpoint
is at most D0+10yzw=O(y+z+w), so the passive0 Nash guard holds for small
outer inputs. No axis derivative is used below.

## 3. Exact macro charts for independent premiums

For a triple macro q=(0,y,z,w), let(u,t,v)=I_beta(y,z,w) and
alpha=t-2(u-v)/3. The zero of v is

    yzero=z(1-beta k)/[2+beta h+beta(l-h-k)z].       (5)

The numerator3H alpha, H=(1-y)(1-z)(1-w), is

    3(1-z)(beta F2+2y+w)
      -2(1-y)(beta F1-z+3w)
      +2(1-w)(beta F3-z+2y).                      (6)

It is affine in y. Write it L_beta(y-yseam), where L_beta stays positive.
At beta0, L0=10+2w-8z and yseam=w(3+z)/(10+2w-8z).
Choose y=max(yzero,yseam). Then v>=0,alpha>=0 and alpha v=0 exactly.

On the pair chart z=0 introduce0<=sigma<=2, give quiet2 output
beta(F2+sigma), and replace t by[beta(F2+sigma)+2y+w]/[(1-y)(1-w)].
Choose y by alpha=0 in(6), whose numerator gains3beta sigma. It remains
positive near the fixed pair chart. The inactive2 guard is beta sigma,
and the pair chart agrees exactly with the triple chart at z=sigma=0.

Set

    U0=(u+3alpha)/(1-alpha), V0=v/(1-alpha),
    x=(U0-V0)/3,
    R=(U0+2V0)/(3-U0+V0),
    K=R/(1-R)=(u+2v+3alpha)/(3-2u-v-9alpha),
    P0=3y-z+3w+3alpha H.

The flow return is

    (K,0,0,0) --2,R--> (0,R,0,R)
       --0,x--> (0,U0,2x,V0)
       --3,alpha--> (3alpha,u,t,v).                (7)

When alpha=0, omit the last flow. Otherwise V0=0 makes its owner3
coordinate zero. Every flow is viable whenever these endpoints are
nonnegative and0<x<R<1,0<=alpha<1.

Define the two continuous residuals

    Return_beta=Axis_beta(P0,beta F1,beta F3)-K,
    Entry_beta=F2+sigma-T_beta(beta F1,beta F3)/beta. (8)

Here sigma=0 on a triple. The axis function uses the projected middle
coordinate T_beta before Entry_beta vanishes; this is explicit auxiliary
evaluation, not an assumed continuation. At a common zero it is the
actual macro output. Uniformly on every fixed compact macro chart,

    Return_beta -> P0-K,
    Entry_beta -> F2+sigma-AF1-BF3.                (9)

Only uniform continuity, not differentiability of the axis, is required.

## 4. One raw-independent limiting return tube

All return geometry at beta0 is independent of the nine premiums.
On alpha=0, y=w(3+z)/(10+2w-8z), the return factors as

    Return0=-w P(w,z)/[2(-w+4z-5)J(w,z)],
    J=w^2z^2-2w^2z-5w^2+5wz^2-30wz+33w+8z-10,
    P=6w^3z^2-12w^3z-30w^3-23w^2z^3+115w^2z^2-145w^2z-7w^2
      +8wz^4-141wz^3+863wz^2-1803wz+1205w
      +40z^4-250z^3+354z^2+70z-250.

On0<=z<=9/50,1/5<=w<=13/50, exact Bernstein bounds are

    min P_w=2768063849/3125000,
    max P_z=-20532303/156250,
    min(P_w+P_z)=4131300547/6250000,
    max J=-10637661/6250000.

Also P(1/5,0)=-238/25 and P(13/50,9/50)=1898408563/312500000>0.
Thus one smooth return curve w_d(z) lies between those w bounds, with
0<w_d'<1. Let z_star be the unique root in(1761/10000,881/5000) of

    f_star=32z^3-148z^2+167z-25.

Its derivative has minimum Bernstein coefficient73019/625 on[0,9/50].
At the isolating endpoints its values are-193897169/31250000000 and
10896733/1953125000. The identity

    P(z(5-4z)/3,z)=-(z-2)(z-1)(z+3)^2(4z-5)f_star/9

shows that yseam>=z/2 on the direct return arm0<=z<=z_star, with equality
only at its upper end. Its values satisfy u,t>0,v>=0,2u+v<3 and0<x<R<1.
For example u<=39/37, y<=1/10 and v<=100/369 give2u+v<3. Its passive
output is at least3w+z/2>=3/5.

On the v=0 arm y=z/2, the return is

    Return0=-z P_f/(2D_f),
    P_f=24wz^3-153wz^2+165wz+6w-200z^3+555z^2-419z+50,
    D_f=3wz^2-15wz-25z^2+35z-6,
    w_f(z)=(200z^3-555z^2+419z-50)
             /[3(8z^3-51z^2+55z+2)].

Use z_L=153/1000<=z<=z_star. At the upper endpoint this joins the direct
arm. Along this return

    P0=z(11-8z)/2, x=P0/(1+2P0),
    alpha=f_star/(88z^3-201z^2+127z-28),
    3w_f-z=-(z-1)(8z^3-243z^2+367z-50)
                       /(8z^3-51z^2+55z+2),
    D_f=-2(z-2)(z-1)(7z+3)/(8z^3-51z^2+55z+2)<0.

The denominator polynomial8z^3-51z^2+55z+2 exceeds8 on[3/20,9/50].
The cubic in the numerator of3w_f-z has positive derivative there,
with minimum Bernstein coefficient175186/625, and value30704101/62500000
at z_L. Thus u>0. The denominator of alpha is negative and f_star<=0;
subtracting its numerator from its denominator gives
56z^3-53z^2-40z-3<0. Hence0<=alpha<1. All remaining flow probabilities
are physical and positive, and P0>=147/200.

The numerator of w_f'-1, over its positive denominator
3(8z^3-51z^2+55z+2)^2, is

    -192z^6+2448z^5-16203z^4+32030z^3-15219z^2-7980z+3576.

Its minimum Bernstein coefficient on[3/20,9/50] is
7096680213357/3906250000>0, so w_f'>1.

These certificates are reproducible by affine substitution to[0,1] or
[0,1]^2 and the Bernstein conversion
b_ij=sum_(p<=i,q<=j) d_pq binom(i,p)/binom(n,p) binom(j,q)/binom(m,q).

## 5. A C0 Miranda producer, including both corners

Parameterize one center path by s in[0,3]: first traverse the pair chart
at z=0,w=w_d(0) with sigma decreasing from2 to0; then traverse the direct
arm to z_star; finally traverse the diffuse arm to z_L. Define

    chi(z)=min(1,max(0,16z-1)).

For a transverse parameter rho replace its center(z,w) by
(z+rho chi(z),w+rho). Keep sigma fixed. The inequality chi(z)<=8z makes
every such hazard z nonnegative when |rho|<1/16, including near the pair
junction. On the pair leg z remains identically zero. On the entire
diffuse arm and near the shared corner chi=1.

The directional derivative of Return0 along this transverse displacement
is uniformly negative at all centers, branch by branch. On the direct
arm its sign is that of the negative return factor times
P_w+chi P_z>=P_w+P_z>0. On the diffuse arm its positive return factor
multiplies P_f,z+P_f,w<0, because w_f'>1. The pair arm uses the negative
w derivative of the direct formula. At the corner the two branches agree
and both directional derivatives are negative. Thus one thin common
rectangle(s,rho) has Return0>0 on its lower rho face and Return0<0 on
its upper rho face. Uniform convergence in(9) preserves these signs for
all small beta, without any derivative estimate for Axis_beta.

The two longitudinal entry signs are also uniform over the full raw box.
At the pair endpoint sigma2, F1=bw,F3=hy and F2>=0. Equations(2) and
y<=1/10,w<=13/50 give

    Entry0>=2-Abw-Bhy>=2-2(y+w)>1.

At the diffuse endpoint, y=z_L/2 and
w=w_L=16351075/247762329. Put U=z+w-zw, D=y+w-yw,V=y+z-yz. Since
F1>=U,F3>=V,F2<=2D and A>1/3,B>=1,

    Entry0<=2D-U/3-V
      =-18634684506317/1486573974000000<0.        (10)

Choose the tube thin enough that both endpoint signs persist on the entire
end faces s=0 and s=3, uniformly in the compact box. Equation(9) then preserves them
for small beta. The two-dimensional Poincare--Miranda theorem applied to
(-Entry_beta,-Return_beta), in coordinates(s,rho), produces a common zero.
All interior tube points have physical flows; v and alpha are nonnegative
and complementary by their exact maximum definition. Thus the zero is an
actual macro, actual physical graph entrance and actual return.

At every macro on the tube the passive0 guard is strict. At beta0 one has
y<=1/10,z<=1/5,w<=13/50, so its Quit endpoint is at most257/500, whereas
its Continue output is at least3/5 on the direct/pair arm and147/200 on
the diffuse arm. The strict margins persist on a small tube and at small
positive beta. Core owners are indifferent except quiet2 on a pair, whose
guard is exactly beta sigma. The local wash's passive0 guard was proved
in Section2. No strategic witness remains an input.

## 6. Finite periodic execution and the fixed target

Fix the produced macro and return before accuracy. Let V=(3alpha,u,t,v),
let B be the macro output, and let Q_N be the output after N backward
graph roots from B. Then Q_N tends to Q=(K,0,0,0); put E_N=||Q_N-Q||.
Refine each nontrivial solo flow of aggregate hazard h into n equal hazards
delta=1-(1-h)^(1/n). All intermediate values lie on its nonnegative endpoint
segment, and its active owner's native coordinate stays zero. Every Continue
and policy equation is exact; an outsider's Quit endpoint exceeds its value
by at most C delta, where C is the largest positive queried pair premium.
All such rewards are finite, even the otherwise unrestricted entries.

Repeat chronologically: refined flow3 if present, refined flow0, refined
flow2, one empty seam from annotation Q to Q_N, the N wash roots reversed,
then the macro. The sole policy/Continue defect is E_N at the empty seam.
Every deviator's opponents absorb per word with probability at least x>0:
for deviator0 use owner2's aggregate R>=x, and otherwise use owner0's x.

Policy telescoping gives payoff error at most E_N/x from the fixed target
ell+V. An arbitrary complete deviator pays a mesh error only when it first
Quits while live, at most once, and a seam error on at most1/x expected
visits. Its gain is therefore at most C max(delta)+2E_N/x. Bounded surviving
remainders vanish by geometric opponent absorption, including for Never
deviations. Choose N and n to make these errors arbitrarily small.

If the word has length L, every unilateral replacement has expected
absorption time at most L/x. Thus the finite-horizon-to-terminal payoff
error is uniformly at most2M L/(xH), for a finite original reward bound M.
The same selected profile therefore works for all sufficiently long
horizons. The target ell+V is independent of the requested accuracy.

## 7. Exact boundary control and nonhomogeneous calibration

The order d>=h cannot simply be omitted from the produced full-quadrant
core graph. For the unordered-box point a=b=d=e=k=1,h=2,f=g=l=1,
the negative eigenvalue is-r=-1 and the tangent plane is

    t=u/2+3v/4.

On the axis u=0,v>0 this is below the physical threshold tcrit=v at
beta0. For all sufficiently small positive beta and v, the graph root
there has negative z. Its leading outer map is
[1/2,-1/4;1/4,5/8]; on the physical slope cone0<=v/u<=2/3 its slope
map sends every point to at least1/2 and a second physical step to at
least3/2, outside the cone. This is a limitation
of that triple-graph construction, not a counterexample to UE existence.
The equality boundary d=h is included in the theorem by the exact axis
and parameter-factor argument in Section2.

### Complete separating table

Take original own singleton levels1 and literal live/Never0. Let native
singletons be Gamma=[0,3,-1,3;2,0,1,-3;2,-2,0,-1;-1,-2,1,0].
All passive nonsingletons are additive. Every proper nonsingleton participant
entry is e, EXCEPT Z1(123)=2e. The native grand reward is(10,-2,-e,-1).
Assume0<e<=1/4000. These rules specify all60 rewards. This belongs to the
ordered nine-premium box at scale e, with normalized tuple
(a,b,f,d,e,g,h,k,l)=(1,1,2,1,1,1,1,1,1). In this section only, the symbol e
denotes the small calibration scale. The own-value shift is bookkeeping
only on absorbing coalitions. Choose e also below the produced beta0 to
obtain an actual covered table; no numerical beta0 is asserted.

The comparison below exhausts the named existing criteria, not every
conceivable UE construction. Write h=2e as an upper bound for every proper
participant premium and for the row1 error term used below.

### Every sure-owner root, including every feasible punishment tail

Write q=(x,y,z,w), H_i=product_(j!=i)(1-q_j), D_i=1-H_i,
J_i=D_i product_(j!=i)q_j. The native forced-Quit and passive endpoints are

    Q0=eD0+(10-e)yzw, Q1=e D1-(2+e)xzw+e(1-x)zw,
    Q2=eD2-2exyw,    Q3=e D3-(1+e)xyz,
    P=Gamma q, g_i=Q_i-P_i.                            (E2)

If owner i is sure, every other owner compares exactly Q_j and P_j,
independently of the tail. The sure owner's gap is g_i-H_i v_i, where
v_i is its original continuation minus1. Every original row2 reward is
at least-2, so every actual continuation, full response cap and punishment
value has v2>=-3. That is the only tail bound needed below.

If x=1, then

    g3=1+2y-z(1+y)+e(1-yz)>=y+e(1-y)>0,

so w=1. The remaining free equations force y=1/2 and
z=(1+e)/(3+e); the boundary y=0 instead forces z=0 and then y=1,
and y=1 is excluded by the next case. At this free solution the sure0 gap
is e-9/2+(6-e/2)z<0. If y=1, g2>=e>0 forces z=1,
g3=1+e(1-x)>0 forces w=1, and g0=5 forces x=1; but then g1=-2.
Thus x,y<1 in all remaining sure cases.

If z=w=1, the free equations force

    x=(1+e)/(2+e), y=(2-e)/(7-e).

The endpoints x=0 or y=0 cannot be equilibria: x=0 gives g1>0 and
forces y=1; y=0 has g0=e-2<0, forcing x=0. Over the positive denominator
(2+e)(7-e), the numerator of g3 at the free solution is

    3e^2+12e-1<0.

For e<=1/4000 this is bounded above by -1+15e<0.

For z=1 alone, w=0 forces y=0 and then x=1, already excluded.
Thus 0<w<1, and g3=0 gives

    y=(1-e-x)/(2-(1+e)x).

If y=0, the free solution is x=1-e,w=(1+e)/3. Even at v2=-3,

    g2+3H2=(4e-5)/3+e(4-5e/3+e^2/3)<0.

If y>0, then g1=0 gives

    w=(2x+1-e)/[3+e-(2+2e)x],

so0<=x<(1+e)/(2+e)<51/100. Both denominators are positive.
Multiplying g0 by [2-(1+e)x][3+e-(2+2e)x] gives

    Nz=-18x^2+9x+1
       +e(8x^2-23x-1)+e^2(6x^2-17x+17)
       +e^3(2x^2-x-1).

Its constant part is at least4541/5000 on[0,51/100]. The absolute
coefficient sum of (Nz-Nz|e=0)/e is76, hence
Nz>=4541/5000-76e>0 for e<=1/4000, contradicting x<1.

For w=1 alone, z=0 forces x=0 and then z=1, impossible. Hence0<z<1.
The equation g2=0 gives y=(2x-1-e)/(2(1-ex)), so x>1/2.
If y=0, g0=e+z-3<0. Otherwise g1=0 gives

    z=(3+e-2x)/[1-e+(2+2e)x].

Multiplying g0 by2(1-ex)[1-e+(2+2e)x] gives

    Nw=-52x^2+64x-27
       +e(8x^2+42x-27)+e^2(8x^2-4x-11)
       +e^3(-4x^2+2x+1).

The constant part is at most-95/13, and the absolute coefficient sum
of (Nw-Nw|e=0)/e is107. Thus Nw<=-95/13+107e<0,
contradicting x>0.
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

    E=D2^2-2J2, E1=e(D1^2-J1)+e D1 zw(1-x),
    E3=e(D3^2-J3), h=2e.

Then0<=E1<=h D1^2 and0<=E3<=h D3^2, because zw<=D1. Also Q1<=h D1. Thus

    F0=eD0^2+(10-e)J0-3y+z-3w,
    F1=-2J1+E1-2x-z+3w,
    F2=eE-2x+2y+w,
    F3=-J3+E3+x+2y-z.                                  (E4)

If x=0, F2>0 unless y=w=0; in that case F0>0 unless all hazards
vanish. Thus x>0. If z=0, F3>0, so z>0. If w=0, then
F1<=e(x+z)-2x-z<0, forcing y=0; now F0>0. Therefore x,z,w>0.
If y=0, their active equalities imply

    z>=(3-e)w/(1+e), x<=(1+e)w/(2-e),
    z<=(1+e)x/(1-e),

which are incompatible already for e<=1/4,e<=1/10. All remaining
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

    q1=(1-e)/2, q2=1, q3=(1-e)/(3+e),

followed by Never. Owner1's Quit endpoint is e(1+q3) and its Continue
endpoint is1-3q3, equal by construction. Owner3's endpoints are e and
1-2q1, also equal. Owner2 strictly prefers Quit to every delay. Outsider0's
joining gain is exactly

    (1-e+17e^2-e^3)/[2(3+e)]>0.

For the remaining child023, repeat solo owners3,0,2 with cumulative
hazards5/12,5/14,5/9. In coordinate order0,2,3, the values before the
three phases are respectively

    (5/4,0,0), (0,5/7,0), (0,0,5/9).

These solve the Bellman equalities exactly. Subdivide each solo phase,
preserving its cumulative survival, until every hazard is at most delta.
All intermediate values are nonnegative and equal their Continue branches;
an active owner's value stays zero. Every native forced-Quit endpoint is
at most e delta. Adding e delta to every value coordinate
is therefore a full-cap supersolution. Each player's opponents absorb
with positive probability per period, so geometric telescoping removes
the remainder and every child debt is at most e delta.

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

The quantitative criterion requires every row1 core participant premium
at most eta<=e/250, whereas this table has entries e and2e. The general
signed-chamber criterion at this background requires at most3e/11200.
The pair-contraction criterion requires e<=Z1(13)/3=e/3, which fails.
The equal-premium rectangle, cone, closed wedge, lower diffuse and crossed
classes each require equality of the three participant entries in row1
within core123. Here Z1(12)=Z1(13)=e while Z1(123)=2e, so all fail exactly.
Positive row rescaling cannot restore equality of two unequal entries.

The complete signed-chamber role pattern is

    [0,g1,-g2,g3; k0,0,1,-c0; A0,-h0,0,-g4; -l0,-d0,1,0],

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


## 8. Source correspondence and formalization handoff

Inspected `Math.Topology.exists_rectangular_zero_of_strict_face_signs` in
`MathUE/Topology/RectangularPoincareMiranda.lean` and
`repeatedSingletonProfile_error_and_debt_le` in
`UniformEquilibrium/Quitting/EssentialAPS/FiniteJumpFlowCompiler.lean`.
The terminal target endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
No Lean commands ran. The new ordinary argument supplies the raw-data
graph and common-zero producer; the finite execution proof is explicit.

The raw reward conditions are the only inputs. Sections1--5
produce the graph, macro, return and every guard; Section6 constructs the
profiles and prices all complete deviations. Section7 supplies a complete
nonhomogeneous calibration and compares the stated existing selectors.
A formalization can separate the analytic graph and rectangular common-zero
argument from the exact finite reward identities and behavioral consumer.
