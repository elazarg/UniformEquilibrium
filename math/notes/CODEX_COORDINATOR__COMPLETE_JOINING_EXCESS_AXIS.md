# Complete positive joining-excess axis and the remaining joint-return boundary

Owner: CODEX_COORDINATOR. Ordinary mathematics, not checked in Lean. The
positive joining-excess axis below is completely covered. Arbitrary Fin4
remains open; this is a family with a fixed singleton matrix and specified
higher entries, not an arbitrary-table theorem.

## 1. Exact raw family

Fix the native singleton matrix

    Gamma=[0,3,-1,3;2,0,1/2,-3;2,-2,0,-1;-1,-2,1,0]

and the higher native entries

    Z0(02)=-1/10, Z1(02)=5, Z3(02)=-219/29,
    Z1(13)=-100, Z2(23)=3, Z3(13)=10, Z3(23)=-100,
    Z3(03)=1, Z3(023)=15/2.

Let Z0(03) be any fixed nonpositive number. Every unspecified higher entry
is arbitrary fixed finite, except

    Z1(12)=-K, Z2(12)=p, Z2(02)=2+eta.

For every eta>0 there is finite M_eta such that every real p and every
K>=M_eta(1+|p|) has an exact periodic terminal Nash equilibrium and an original
uniform-equilibrium payoff. Original own levels kappa are arbitrary, with
r_i(D)=kappa_i+Z_i(D) on nonempty coalitions; live/Never remain zero.

Moreover, throughout the whole unbounded tail

    eta>=305713711170/4725703339153,

one only needs K>=1+max(Z1(01),0)+max(Z1(012),0), independently of p and eta.
There is no missing middle interval. No uniform M_eta as eta decreases to
zero, and no positive-p conclusion at eta=0, is asserted here.

## 2. Exhaustive proof by the two raw producers

The rational parametrization in Section5 of the
[direct-return theorem](../exports/CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md)
selects one b in(0,1/3) for every eta>0. Explicitly,

    eta(b)=-(3b-1)(73b-1450)(190b+29)
                /[29b(219b^2-1030b-1160)].

Its proved strictly negative derivative and endpoint limits give a unique
simple root. The same section supplies C,T,j,X1,X2 and proves throughout
this entire interval, not merely its tail,

    0<C<3, T>0, X1>0, X2>0,
    C-j>0, 3X2>4b/10, Q3_join<0.

These are all the common strict return guards. There are exactly two cases.

1. If j>100T/3, all assumptions of the
   [finite-core theorem](../exports/JOINT_QUITTING_NEGATIVE_VALUE_UNIFORM_EQUILIBRIUM.md)
   hold, including j<C and the raw prefix interval. Its finite core and
   adjacent-length gluing give every real p once K>=M_eta(1+|p|).
2. If j<=100T/3, the direct-return theorem applies. When j>0, the raw
   continuation (C,-j,T,0) already satisfies its wash inequality
   T>=3j/100. When j<=0 it has no negative quiet coordinate and needs no
   wash. Both cases give exact finite returns and the displayed explicit
   K bound; p never occurs in any root or unilateral comparison.

The direct theorem's larger generic bound on K can be sharpened uniformly
here: x/[(1-x)b]<=1 and x/(1-x)<=1, so the stated K bound makes the quiet1
joint offer strictly negative for every b. Taking the larger of that bound
and the finite-core threshold in the first case supplies M_eta.

The function j increases and T decreases with b. At b=331/1000,

    j-100T/3=-5546944652414753/1500285581257994157<0.

The strictly decreasing eta map therefore identifies the stated entire tail
as a subset of the direct-return case. The actual transition is a single
algebraic point; neither its numerical approximation nor a guessed threshold
is used to cover the two cases. This proves the full axis claim.

The direct theorem also gives an exact five-date example at
eta=12281660/12608823, valid for every K>=1 and arbitrary p. At p=0 and
K>=1000 it lies in a rigorously stationary-free region. Its failure of the
finite-core guard is strict, so the second producer closes a surviving
region rather than merely shortening an already-covered strategy.

## 3. One removable sign and a real topology limitation

The finite-core proof also permits arbitrary d=-Gamma30, keeping its other
hypotheses and explicit D>0 test. This follows by auditing its equations:
d occurs only in

    X3=e*b-x[d-b(Z3(02)+d-e)]+(1-x)(1-b)C3.

Its limiting x derivative is -D, supplied by the retained raw guard.
Neither the core, wash, return nor resonance arguments use d's sign.
The cubic remains the exact elimination equation. Thus no negative
Gamma30 hypothesis is needed for that extension. The direct theorem already
states this more general sign scope.

This does not make the finite-core architecture universal in the singleton
matrix. The existing pointed witness3 in the
[residual partition](CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md) is

    [0,3,-3,1;2,0,-1,-1;-1,-1,0,2;-1,-2,3,0].

It has determinant7, mixed inverse, positive inverse columns0,1,3, R0 degree+1,
negative columns, a negative reciprocal pair, and no inverse-positive child.
Its only opposite-sign reciprocal pair is03. The finite-core architecture
still requires two distinct opposite-sign pairs02 and23, so every labeling
fails before higher rewards are tested. These are already established matrix
facts, not a new no-UE example. The all-completion nonnegative-inverse theorem
also requires negative determinant; a positive inverse by itself must not
be treated as that theorem's full hypothesis.

The next substantial obligation is a producer for arbitrary higher rewards
on the remaining matrix patterns, or a true global-source exclusion. The
completed eta axis and the sign extension do not supply either one.

## 4. Direct returns beyond that singleton architecture

The direct-return theorem also admits the signed reciprocal entry below.
This extension does not claim separation from every existing UE producer.

### 4.1. Removing the sign of e

In the direct-return raw theorem, replace `e>0,D>0` by

    e!=0, D!=0, 0<x=e*b/D<1.

Keep every other hypothesis and definition, including the nonzero polynomial
test. The theorem and its complete behavioral-deviation conclusion remain
valid. The joint root's current row3 value is `e*b-x*D=0`. All other root
comparisons use the resulting physical probability x and the raw rewards.
Writing `tau=(C+s*b)/(k+s*b)`, exact elimination gives

    T+h*tau-(1-tau)*x*(f+eta)
      =-b*P_eta(b)/[(1-b)(k+s*b)*D*(D-e*b)].

The denominator is nonzero: `k+s*b>0` follows from the retained C guard, and
`D*(D-e*b)=D^2*(1-x)>0`. Thus the cubic still gives exactly the required
row2 affine-return identity. The row1 identity and positivity of its j
denominator are unchanged. The prefix, wash, final return, and absorption
arguments use no sign of e or D. This proves the extension, including both
signs of j and the equality wash boundary, without a simple-root requirement.

On the no-wash branch `j<=0`, h may additionally be any real number. Retain
the other assumptions and require a raw prefix probability a satisfying

    B/(H+B)<a<min(tau,X1/(X1+g)),
    (1-a)*X2>(h+c)*a.

This is still an explicit interval test: additionally impose `a<u2`, where
`u2=X2/(X2+h+c)` if `h+c>0`, and `u2=1` otherwise; select the midpoint of
the resulting interval. The second inequality says precisely `Y2>c*a`.
The continuation U has nonnegative quiet coordinates, with `U0,U2>0`;
Y has strictly positive quiet coordinates. Their exact solo3 return stays
on the segment between these endpoints. Subdivide the total mass so that
`c*q<min(T,Y2)` at every root. Quiet1's joining reward is negative, quiet0 has
current value at least `k*q>zeta0*q`, and owner3 is indifferent. No step of
this no-wash proof needs `h>0`. This extension leaves g,c,A unchanged.

### 4.2. An exact three-date example on pointed witness3

The previously identified singleton matrix is

    H=[0,3,-3,1;2,0,-1,-1;-1,-1,0,2;-1,-2,3,0].

Relabel by `(new0,new1,new2,new3)=(old3,old1,old0,old2)`. Its new matrix is

    Gamma=[0,-2,-1,3;-1,0,2,-1;1,3,0,-3;2,-1,-1,0].

Thus `beta=1,e=-1,d=-2,f=1,k=3,h=3,g=1,n=-1,ell=2`.
Choose the higher entries

    Z0(02)=0, Z1(02)=5, Z2(02)=9/5, Z3(02)=-10,
    Z0(03)=0, Z1(13)=-2, Z2(23)=1,
    Z3(03),Z3(23),Z3(023)<=0.

Let `Z1(12)=-K`. Every other higher entry is arbitrary fixed finite,
including `p=Z2(12)`, provided

    K >= [7*Z1(01)+Z1(012)-14]/4.                    (8)

For a complete concrete table, set K=1, set the three displayed nonpositive
row3 entries to -1, and set every otherwise unspecified higher entry to zero.
Original rewards are `r(D)=kappa+Z(D)` with arbitrary original own levels
kappa; original live/Never payoffs remain zero.

Here `s=0,eta=4/5,A=2,c=1,zeta0=0`, and the raw polynomial is

    P_eta(b)=-6*(7b-1)*(8b-1).

Select

    b=1/8, D=-5/8, x=1/5, C=1/7, T=1/5,
    P1=3/20, j=-2/7, X1=7/20, X2=9/25, tau=1/21.

Repeat the three independent hazard vectors

    (0,0,0,1/42), (1/5,0,1/8,0), (0,0,0,1/41).

Their current values are, respectively,

    Y=(1/14,89/280,7/25,0),
    X=(0,7/20,9/25,0),
    U=(1/7,2/7,1/5,0).

With `G=(3,-1,-3,0)`, exact transport gives
`Y=(G+41X)/42` and `U=(G+40Y)/41`. At the joint date owner0 has
Quit=Continue=0, while owner2 has Quit=Continue=9/25. Quiet1's margin is

    [4K-7*Z1(01)-Z1(012)+14]/40 >= 0.

Quiet3 has current value zero and Quit offer

    [7*Z3(03)+4*Z3(23)+Z3(023)]/40 <= 0.

The quiet0,1,2 margins at the two solo3 dates are

| Current value | Quiet0 | Quiet1 | Quiet2 |
|---|---:|---:|---:|
| Y | 1/14 | 307/840 | 269/1050 |
| U | 1/7 | 96/287 | 36/205 |

Owner3 is indifferent at both dates. Thus all first-action comparisons hold
exactly. Condition (8) is the exact quiet1 threshold; a convenient sufficient
bound is `K>=1+(7/4)*max(Z1(01),0)+(1/4)*max(Z1(012),0)`.

Every unilateral deviator faces opponents-only absorption at least 1/8 per
three-date period, independent of that player's behavior. Bounded Bellman
unrolling proves exact terminal Nash against every complete behavioral
replacement, including Never. It also justifies arbitrary native row shifts.
The same profile has fixed original uniform-equilibrium target `kappa+Y`;
the standard bound is `52R/T_horizon` for the discrepancy between terminal
and finite-horizon average payoffs when original rewards are bounded by R.
Apart from the two entries bounded in (8), the remaining unspecified higher
entries, including p, occur in no executed comparison.

The singleton topology obstruction in the axis note is therefore specific
to its finite-core architecture: the signed-e direct construction handles
this H for the stated higher-reward family. Producing equilibria for arbitrary
higher rewards on the remaining singleton patterns remains an open obligation.

## 5. The entire penalty axis on a parameter strip

This section fixes the complete table displayed below. It combines an exact
stationary bridge with the finite direct return to cover every real K.

### Exact table and conclusion

Use arbitrary original own levels kappa_i and r_i(D)=kappa_i+Z_i(D) on nonempty
coalitions, with live and literal Never rewards zero. The complete native table is

| D | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
|0|0|2|2|-1|
|1|3|0|-2|-2|
|2|-1|1/2|0|1|
|3|3|-3|-1|0|
|01|0|-1|-10|-12|
|02|-1/10|5|2+eta|-219/29|
|12|-12|-K|p|-6|
|03|-20|3|-5|1|
|13|2|-100|-1|10|
|23|-6|9|3|-100|
|012|-20|6|-100|11|
|013|-20|8|10|-10|
|023|-20|-8|-100|15/2|
|123|-8|11|2|1|
|0123|-5|-9|-100|21/2|

Put eta_min=305713711170/4725703339153. Every table with

    eta_min <= eta <= 1,       -8 <= p <= 1,       K in R

has an exact proper terminal Nash profile and its original uniform-equilibrium
payoff, against every complete behavioral replacement. The profile is stationary
when K<=-1/2 and is the existing finite core-free return when K>=-1/2. Both
branches include the split boundary. In particular this closes the entire K
axis at eta=1,p=0 and at eta=12281660/12608823,p=0.

The stationary assertion is stronger in eta: it holds for every 0<eta<=1,
-8<=p<=1 and K<=-1/2. The core-free assertion is stronger in p and eta: it
holds for every eta>=eta_min, every p in R and K>=-1/2. No all-K conclusion
is claimed below eta_min, above eta=1, or outside the bounded p interval.

### Narrow existing-source comparison

The table and finite return are those of Sections5–6 of
`math/exports/CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`.
Its existing sufficient K bound can be improved by checking its sole
K-dependent comparison; this is done below without altering the construction.

The full singleton inverse is

    [2/5,2/7,12/35,9/35;
     1/5,2/7,-9/35,2/35;
     4/5,6/7,-6/35,48/35;
     2/5,0,1/5,2/5].

Thus `BOUNDARY_INVERSE_COLUMN_UNIFORM_EQUILIBRIUM.md` already covers the
K-to-minus-infinity positive-jackpot tail: its recipient1 inverse column is
nonnegative, has zero set {3}, and the corresponding inverse principal entry
is 2/5>0. It provides an existential tail threshold, not the finite bridge
proved here. On support012 the positive recipient1 inverse column has zero
outside singleton projection, so the strict outside test in
`WEIGHTED_COLLISION_DOMINANCE_UNIFORM_EQUILIBRIUM.md` does not apply on that
support. The construction below explicitly prices the outside quadratic terms.
The separate `SIGNED_COLLISION_PARAMETER_UNIFORM_EQUILIBRIUM.md` fixes different
singleton12 and pair13 entries and is not this table unchanged.
No exhaustive exclusion of every other implemented producer is claimed.

### Stationary construction on K<=-1/2

Write a=2+eta, so 2<a<=3. Seek stationary hazards (x,y,z,0), with z in(0,1].
For each player define H_i as opponent all-Continue probability, Q_i as the
forced-Quit native reward, P_i as the native stopping contribution when that
player Continues, and F_i=(1-H_i)Q_i-P_i. Active indifference is F_i=0;
the quiet player3 needs F3<=0.

Player0's equation is f0(y,z)=0, where

    10 F0 = f0(y,z)
      =199z(z-1)y^2+(-198z^2+139z-30)y+z(10-z).

For z in(0,1], f0 is strictly decreasing in y>=0: its quadratic coefficient
is nonpositive, and the discriminant of -198z^2+139z-30 is -4439<0.
It is positive at y=0, while

    f0(1/4,z)=(-609z^2+517z-120)/16<0

because the discriminant is -25031. Thus there is one simple root y(z) in
(0,1/4), continuous through z=1 and extending to y(0)=0 with y'(0)=1/3.
We also have y(z)<3z/4. Indeed

    f0(3z/4,z)=z*J(z)/16,
    J(z)=1791z^3-4167z^2+1652z-200<0 on[0,1].

For z<=1/3, J(z)<=-3570z^2+1652z-200<0, whose discriminant is -126896.
For z>=1/3, J'(z)=5373z^2-8334z+1652<0: this convex quadratic is negative
at both endpoints 1/3 and1. Finally J(1/3)=-46.

With this y, player2's equation is the quadratic in x

    f2(x,y)=(x+y-xy)*[a*x*(1-y)-100xy+p*y*(1-x)]
              -2x+2y+10xy=0.

At x=0 it is y(2+py)>0, since p>=-8 and y<1/4. It increases with a and p
at a fixed x in(0,1), so at x=1/10,

    f2(1/10,y)<=(-17+233y-846y^2)/100<0,

the last discriminant being -3239. A quadratic with these opposite endpoint
signs has exactly one simple root x(y) in(0,1/10). Its derivative in x is
negative at that root, so these roots form one continuous branch. Near y=0
the branch has x=y+O(y^2), by the IFT at (x,y)=(0,0).

Moreover x<2y. For y>=1/20 this follows from x<1/10. For y<1/20, evaluate
at x=2y and bound a<=3,p<=1 to get

    f2(2y,y)<=y*(-2+41y-638y^2+416y^3)
             <=y*(-2+41y-600y^2)<0.

The last quadratic is negative because its discriminant is -3119. Uniqueness
of the root then gives x<2y. Consequently x<3z/2 and y<3z/4 throughout.

Set h1=x+z-xz and define

    K(z)=[-x+7xz-(2x+z/2+5xz/2)/h1]/[z*(1-x)].

This is exactly player1's indifference equation, because

    Q1=-x+7xz-K*z*(1-x),  P1=2x+z/2+5xz/2.

It is continuous on(0,1]. Since x=z/3+O(z^2), y=z/3+O(z^2),

    K(z)=-7/(8z)+O(1) -> -infinity as z -> 0+.

At z=1, y=9/89 and

    K(1)=(3x-1)/[2(1-x)] > -1/2.

Hence IVT supplies some z in(0,1) for EVERY prescribed K<=-1/2. No monotonicity
of K(z), radical selection or numerical root search is required.

### Exact outside inequality on the entire stationary branch

The own row3 expectations are

    Q3=(1-z)*(x+10y-21xy)
          +z*(-100+(215/2)x+101y-98xy),
    P3=-x-2y+z-9xy-(219/29)xz-5yz+(1002/29)xyz.

Since x<1/10,y<1/4, the second bracket in Q3 is below -64. Therefore

    Q3 <= x+10y-64z <= -55z.

The active equations themselves give

    3y-z <=14yz,
    x-y <=5xy+(x+y)*(3x+y)/2.

For the first, use P0=3y-z-14yz=(y+z-yz)Q0 with
Q0=-z*(1+199y)/10<0. For the second, use f2=0 and the upper bound
Q2<=3x+y. These inequalities imply

    -P3 <=14xy+(x+y)*(3x+y)/2+(219/29)xz+19yz
         <=(43833/928)*z^2 <48z^2.

Here the final estimate uses x<3z/2,y<3z/4; its coefficient is exactly
63/4+189/32+657/58+57/4. Finally 1-H3>=z and Q3<0, so

    F3=(1-H3)Q3-P3 < -55z^2+48z^2 = -7z^2 <0.

Thus the entire constructed branch is legal, including its approach to
z=0 and its finite endpoint. The outside comparison is not a numerical check.

### The existing direct return on K>=-1/2

Section5 of the core-free packet already proves every remaining raw return
guard for eta>=eta_min, parametrized by a unique b in(0,331/1000], with

    eta=-(3b-1)(73b-1450)(190b+29)
               /[29b*(219b^2-1030b-1160)],
    x=29b/(29+219b),
    X1=(1504b^2-161b+2610)/[2*(7629b+2030)].

Player1 always Continues in that finite construction. The only comparison
that contains K is its joint02 Quit offer

    x*(-1+7b)-K*(1-x)*b <= X1.

At K=-1/2 its exact margin is

    H(b)/[2*(219b+29)*(7629b+2030)],
    H(b)=-4217508b^3-980282b^2+625791b+75690.

H is strictly concave on[0,1/3], with H(0)=75690 and H(1/3)=172465/9.
It is therefore strictly positive throughout that interval. Increasing K
only improves this comparison. All other comparisons are independent of K,
and p is invisible because player1 never quits. Thus the same finite return
works for every eta>=eta_min,p in R,K>=-1/2. This rechecks the construction
under a weaker K bound rather than silently invoking its former sufficient
bound outside its stated range.

At the explicit five-date eta=12281660/12608823, Section6's fixed profile
has the EXACT optimal lower bound

    K >= -7197986/9285205 = -0.775210240377... .

Substitution of b=3/10,x=87/947,X1=134853/431870 into the joint comparison
gives this value. Equality is legal; below it a reached joint-date Quit
replacement by player1 is profitable. This provides an explicit overlap
with the stationary K<=-1/2 half-line.

### Complete behavioral and original uniform payoff

For the stationary branch, every player has a proper opponent. Let
U_i=P_i/(1-H_i). The active equalities give Q_i=U_i and quiet3 has Q3<U3.
Each prescribed Bellman equation is exact and both action endpoints are at
most U_i. Against any complete behavioral replacement, opponents-only survival
is bounded by H_i^n. Unrolling the inequalities and letting this bounded
remainder vanish proves exact terminal Nash and identifies U as its native
terminal payoff. Every replacement absorbs almost surely, so restoring the
own level adds exactly kappa_i. The geometric absorption-time bound makes
terminal and N-date-average payoffs uniformly close over every replacement.
The SAME stationary profile consequently yields its fixed original UE target.

The direct-return branch uses the frozen packet's exact finite-root comparisons
and joint02 opponents-only absorption bound. Its unchanged complete behavioral
and original uniform-payoff consumer applies verbatim. These two exact profile
producers cover K<=-1/2 and K>=-1/2 with no gap.

All displayed polynomial formulas, discriminants, rational endpoints and
thresholds were checked by exact symbolic arithmetic. No Lean check was run.
The two half-line producers cover every real K under the displayed strip
hypotheses. The remaining parameter regions are not closed by this argument.
