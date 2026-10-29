# Complete joining-excess axis and collision-plane coverage

Owner: CODEX_COORDINATOR. Ordinary mathematics, not checked in Lean. The
positive joining-excess axis below is completely covered. Section9 closes
the entire p=0 cylinder for all real K, eta, R and t. Section7 closes
the full collision plane for K>=0 and nonnegative own levels; Section8
extends the proof to a specified negative-K region. Arbitrary Fin4
remains open; this is a family with a fixed singleton matrix and specified
higher entries, not an arbitrary-table theorem.

The exact Section8 proof has an independent
[localized-extension review](../feedback/CODEX_COORDINATOR__COMPLETE_JOINING_EXCESS_AXIS__BY_LOCALIZED_EXTENSION_REVIEW.md).

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

## 6. Two collision coordinates: complementary return and punishment regions

This section changes the fixed table, rather than extending Section5's
quantifiers to unspecified higher rewards. Use the complete native table in
Section3 of the [three-owner return theorem](../exports/THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md),
fix eta=12281660/12608823, and vary

    R=Z0(23), t=Z3(023), K=-Z1(12), p=Z2(12).

All other native entries remain exactly those printed there. Original own
levels are arbitrary. The following are rigorous ordinary mathematical
conclusions, not Lean checks or a complete classification of this surface:

| Raw region | Sufficient K | Produced profile |
|---|---:|---|
|t<=28599/29, every real R|K>=1|Five-date joint02 return|
|Every real t, R>=-24669707057411/1265373653200|K>=4|Return or two-date punishment|
|t=987, R<=-4362032648577602898/131342371529720117|K>=2|Finite joint023 return|

Every row permits arbitrary real p and arbitrary original own levels. The
second row closes the entire t axis on the half-plane R>=-19.495986... .
The third row covers the whole left tail R<=-33.211161... at t=987.
No claim that these regions exhaust all existing producers is made.

### 6.1 Complete t axis on the right half-plane

Put t0=28599/29 and Rstar=-24669707057411/1265373653200.
For t<=t0, use the five-date certificate in Section6 of the
[direct-return theorem](../exports/CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md).
Its only joint date has hazards x=87/947,b=3/10 for players0,2. All other
dates have solo player3. R occurs in none of its expectations or deviation
offers. Changing t changes only the quiet3 joint Quit offer, which is

    x*b*(t-t0).

The current player3 value is zero, so this comparison holds exactly when
t<=t0, including equality. All other comparisons and the opponents-only
absorption bound are unchanged. This proves the first row of the table.

For t>=t0 and R>=Rstar define

    x=2929/(29t+3148), z=9/(10R+209).

At date1 prescribe hazards (x,0,1,z). After all Continue, prescribe certain
quitting by players0,1 at date2, while players2,3 Continue. Later play is
irrelevant. Since Rstar>-39/2>-20 and t0>986, both mixed hazards are proper.
Players0 and3 face certain player2 quitting at date1. Their indifferences are

    Quit0-Continue0 = 9/10-(R+209/10)*z = 0,
    Quit3-Continue3 = -101+(t+3148/29)*x = 0.

A player2 deviation reaching date2 faces Continue reward Z2(01)=-10 and
Quit reward Z2(012)=-100. Its exact native FULL continuation cap is -10.
Writing a2=2+eta, its date1 Quit and complete Continue offers are

    Q2=a2*x*(1-z)+3*(1-x)*z-100*x*z,
    C2=2*x*(1-z)-(1-x)*z-5*x*z-10*(1-x)*(1-z).

Their exact difference is

    Q2-C2 = [1260882300*R*t+21926311900*R
             +25671563628*t-646880811457]
               /[434787*(10R+209)*(29t+3148)].       (6.1)

Its numerator vanishes at (Rstar,t0). Its R derivative is positive for
t>=t0. Its t derivative is 1260882300*R+25671563628, already positive at
R=-39/2. Thus (6.1) is nonnegative on the whole closed quadrant.

Quiet player1 faces certain absorption by player2 and has

    P1=(1+9*x+17*z-43*x*z)/2,
    Q1=-K*(1-x)*(1-z)+6*x*(1-z)+11*(1-x)*z-9*x*z.

The Continue-minus-Quit margin increases with K. At K=4 it is exactly

    [1305*R*t-19435*R+25578*t-366281]
       /[(10R+209)*(29t+3148)].                     (6.2)

The numerator increases in R and t throughout R>=-39/2,t>=986 and equals
282749/2>0 at that lower corner. Hence every root comparison holds for K>=4.

Every deviator other than player2 faces sure player2 at date1; a deviating
player2 faces sure players0,1 by date2. Thus every complete behavioral
replacement absorbs by date2. Restoring own levels adds the same kappa_i
to every compared payoff. The prescribed payoff is the fixed target given
by kappa plus the native date1 expectation, and uniform O(1/T) terminal-to-
average error gives the original uniform-equilibrium contract. The punishment
need not itself be an equilibrium: only its actual response cap for player2
is used, and that cap has been computed. This proves the second row.

For a slightly sharper t=987 slice, the same calculation gives

    R>=-24690952489379/1266417142000, K>=3.

Indeed x=2929/31771, and (6.1) becomes

    [126641714200-197462864269*z]/13813617777.

Thus z<=zmax=126641714200/197462864269. Quiet1's necessary and sufficient
bound is K>=(66247*z-11492)/(28842*(1-z)); it increases with z, and its
value at zmax is 3060195202214026/1021311805145049<3. At R=-6 the hazards
are x=2929/31771,z=9/149, and even K>=-223217/807576 suffices.

### 6.2 An automatic left tail with no assumed quadratic root

Fix t=987 and put b=319/1066,x=319/3475. For lambda>0 define

    R(lambda)=-(1714394856543602220*lambda^2
                -698031641881466077*lambda-61079706181272)
                 /[11214320*lambda*
                       (8242257159*lambda-1923377191)].       (6.3)

On 0<lambda<=3/500 the denominator is nonzero, the function tends to
-infinity at zero, and

    R(3/500)=-4362032648577602898/131342371529720117=:Rleft.

Continuity therefore supplies a lambda in that interval for EVERY finite
R<=Rleft; monotonicity is unnecessary. Solving the three-owner theorem's
quadratic for R gives exactly (6.3): only

    a0=-23-b*(R+20)/(1-b)

depends on R, and its coefficient in that equation is nonzero here. Thus
the selected lambda is a genuine physical quadratic root. Its constant
coefficient is nonzero, so the polynomial is never identically zero.

All remaining guards can be checked on a compact lambda interval without
interval-evaluating the unbounded R itself. Put

    z=lambda/(1+lambda), T=x*eta/(1-x),
    X0=(-b/10-20lambda)/(1+lambda),
    X2=[x*(2+eta)+lambda*(3-103x)]/(1+lambda),
    U2=T+lambda*[4-95x/(1-x)],
    tau=(X2-U2)/(X2+1), U0=3tau+(1-tau)X0.

The last expression equals the theorem's C+lambda*a0 at R=R(lambda).
Define H=(1-x)(1-b)(1-z), and the literal passive row1 sum

    P1=(1-z)*[2x(1-b)+(1-x)b/2+5xb]
        +z*[-3(1-x)(1-b)+3x(1-b)+9(1-x)b-8xb],
    X1=(P1-3tau*H)/[1-(1-tau)H],
    j=3tau-(1-tau)X1, a=1/20,
    Y=(3a+(1-a)X0,-3a+(1-a)X1,-a+(1-a)X2,0).

Here is a finite exact verification of every required guard. Partition
[0,3/500] into the100 intervals [3n/50000,3(n+1)/50000], n=0,...,99.
On each interval use exact rational endpoint addition, the minimum and
maximum of the four endpoint products, and reciprocal [l,u] -> [1/u,1/l]
only when zero is excluded. Evaluate the preceding formulas in their printed
order. Every denominator excludes zero; every resulting bound satisfies

    Y0>.0084, Y1>.1434, Y2-3a>.0212,
    U0>.279, U2>.0648, X1>.3089, X2>.2328,
    j>0, U2-3j/100>.0607,
    tau-a>.0859, 1-tau>.8625, X0<0.

All decimals are exact rationals. These are reproducible finite rational
inequalities, not floating-point sampling. They prove the prefix, physical
continuation and wash guards of the three-owner theorem. In particular,
Y0>0 gives the required prefix lower bound, and the positive Y1 and Y2-3a
give its two other upper bounds. At the joint date, the positive quiet1
Quit terms divided by (1-x)b(1-z) are at most

    6x/(1-x)+19lambda < 2/3+57/500 <1.

Hence K>=2 suffices. The theorem now constructs the finite wash and return;
the opponents-only absorption bound proves its full behavioral and original
uniform-payoff conclusions. The finite period length need not be five.
This proves the third row without assuming any strategic witness or root.

### 6.3 Exact limits of the earlier return and punishment mechanisms

At R=-25,t=987,p=0,K>=1000,original own levels all1, neither preceding
tail supplies UE. Section7 closes this table by bounded Nash invariance.
For a period with one proper joint023 date and
otherwise proper solo3 dates, at least one with positive hazard, the
necessary polynomial is, up to positive scale,

    -596387876039319780*lambda^2
      -158797459367088077*lambda-61079706181272.

All coefficients are negative, so there is no positive root. The row3
equations uniquely force b=319/1066,x=319/3475; another root selection
cannot repair this architecture. This is not a no-UE conclusion.

For the same table, apply the exact census algorithm in Section6.1 of the
three-owner theorem. Recompute its coefficient dictionaries and origin
constants after substituting R=-25 in the literal table. The continuation
lower vector is L=(-25,-8,-10,-12); all other algorithmic rules are unchanged.
Exact rational Bernstein subdivision excludes all80 nonzero stationary
patterns in866 nodes and all65 sure-first patterns in197 nodes, with no
unresolved box. AllNever fails because original own rewards are positive.
The complete table and cited algorithm specify this computation without any
temporary checker dependency. Thus a different stationary or sure-first root
cannot repair this particular gap. No all-behavior regret gap is established.

The relevant existing semantic declarations are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
Their full-cap and fixed-target scopes were inspected; no Lean command was run.
These complete architecture exclusions remain valid on a table now known to
have UE. They delimit the earlier methods, not the current existence frontier.

## 7. Complete collision plane for nonnegative own levels

For the literal table of Section6, the
[passive-payoff threshold theorem](../exports/PASSIVE_THRESHOLD_UNIFORM_EQUILIBRIUM.md)
proves UE for every real R,t,p, every K>=0, and nonnegative original own
levels. The three covering regions are:

| Raw region | Mechanism |
|---|---|
|R<=-33/100, every real t|Bounded Nash invariance|
|Every real R, t<=28599/29|Exact five-date return|
|R>=-33/100, t>=28599/29|Two-date punishment profile|

Every row allows K>=0 and arbitrary p. The first row follows from the new
raw inequalities with H=3,a=100,c=11: their nontrivial comparisons are
-67,-1167,33+100R,-778. It also allows every real eta. The two other rows
use eta=12281660/12608823 and explicit profiles whose complete unilateral
comparisons are proved in the linked theorem. Those explicit profiles permit
arbitrary original own levels; the union of all three rows is claimed only
for nonnegative own levels. The earlier Section6 regions with arbitrary
own levels remain useful under their separate hypotheses.

The R=-25,t=987 benchmark is therefore solved. Section8 gives an additional
negative-K region. The next obligation is to cover arbitrary higher rewards
outside these criteria, including the remaining negative-K or negative-own
regions. Section9 now closes every negative-K point on p=0 and two outer
regions for p>=0, allowing arbitrary eta,R,t. No exhaustiveness claim for
the other remaining portions is made.

## 8. A negative-K region from the localized invariant

Use the complete native table in Section7 of
[Passive threshold uniform equilibrium](../exports/PASSIVE_THRESHOLD_UNIFORM_EQUILIBRIUM.md).
Define, for R<-33/100,

    F(R)=639/6700                         if R<=-1,
    F(R)=(609-30R)/[100(-33-100R)]         if -1<R<-33/100.

There is UE whenever

    K<0,  R<-33/100,  p<=K F(R),  kappa_i>=0.             (8.1)

The parameters eta and t are arbitrary finite reals. We prove (8.1) using
Sections3–5 of the linked export: their localized invariant consumer applies
even though its particular raw criterion has a Z1(12)<=0 guard that fails here.

First fix beta in (3/4,100/111) and suppose

    R<=3-3/beta,  p<=K f(beta),
    f(b)=(30+173b)/[100(100-111b)].                        (8.2)

Write a=-K>0 and choose 3<V<beta/(1-beta). All player0 participant rewards
are nonpositive and all row0 rewards are at most3, so every prefix preserves
v0<V. We show that every nonzero Nash root against an input in this domain
has a nonpositive current native payoff coordinate.

If player0 is active, its supported Quit payoff is nonpositive. With0
inactive, a sole active owner has own Quit payoff0. Active pair12 has
Q2=p q1<0; pair13 has Q1=-100q3<0; pair23 has Q3=-100q2<0. Only active
set123 remains. Put y=q1, b=q2, z=q3. Its active Quit offers are

    Q1=a b(1-z)+z(111b-100),
    Q2=p y(1-z)+z(3-y),
    Q3=10y-100b+91yb.

Suppose all are positive and b<=beta. Then Q3>0 gives
y>100b/(10+91b). Neither z=0 nor z=1 is possible: Q2<0 at0 and Q1<0
at1. Since p<0 and every denominator below is positive, Q2>0 and Q1>0 give

    z/(1-z)>-p y/(3-y)>-100pb/(30+173b),
    z/(1-z)<a b/(100-111b).

Consequently -p<a f(b)<=a f(beta), contradicting (8.2). Here
f'(b)=2063/[10(100-111b)^2]>0. Thus b>beta. For player0, replace v0
by V and take the four (y,z) corners. The upper bounds are

    V-(V+1)b,  3+(R-3)b,  3-15b,  2-10b.

All are strictly negative for b>beta under our choices of V and R.
Bilinear interpolation gives current payoff0<0, the remaining contradiction.
Zero root preserves its input. Hence {v0<V,min_i v_i<=0} is Nash invariant.
All fixed-seed prefix closures stay in a strict interior row0 bound, since
V>3. The linked export's local escape and actual least-Never argument give
absorbing native debts tending to zero; its nonnegative-own-level consumer
gives one fixed original UE payoff.

To obtain (8.1), when -1<R<-33/100 take beta=3/(3-R). Then beta is in
the required interval and f(beta)=F(R). When R<=-1 and p<K639/6700,
choose beta>3/4 sufficiently close to3/4, using f(3/4)=639/6700.
At p=K639/6700, apply the strict result to p-epsilon and let epsilon
decrease to0. Only Z2(12) changes: prescribed and deviating expected payoffs
each change by at most epsilon, so total native debt changes by at most
2epsilon. The same profiles remain absorbing. Thus absorbing debt infimum0
and the original UE conclusion also hold at equality.

The p restriction cannot be discarded using this invariant alone. At
eta=12281660/12608823,R=-25,t=987,K=-1/4,p=0, the exact root
q=(0,3/5,1/10,1/10000) is Nash against
v=(0,-13483/359964,60011/19998,143/18). Its output is
(429991/500000,6443/400000,3/12500,73/50), strictly positive in every row.
All v coordinates lie within the literal reward ranges and v1<0. This is an
invariant failure, not a counterexample to UE or a sharpness claim for F.
The exact control and ratio identities are reproduced by
[the rational checker](../experiments/CODEX_COORDINATOR__PASSIVE_THRESHOLD_CHECK.py).

## 9. The complete p=0 cylinder and the opposed-pair remainder

The [passive-bound selected-root theorem](../exports/PASSIVE_BOUND_TRIPLE_SELECTION_UNIFORM_EQUILIBRIUM.md)
applies to the complete table used in Sections7–8 for every real eta,R,t
and nonnegative own levels whenever

    p>=0 and (K>=0 or K<=-1/2 or p=0).

In particular, the entire p=0 cylinder is solved for every real K,eta,R,t.
The same conclusion permits all unlisted rewards in the export's core table
to vary subject only to nonpositive player0 participant rewards and the
player2 passive bound10. Its main theorem gives explicit inequalities in
the core rewards as well, rather than fixing those entries universally.

To check this application, put a=-K and write c_ij=Z_i(ij)-Gamma_ij. The
core has c12=a-1/2, (c21,c23,c31,c13,c32)=(p+2,4,12,-97,-101),
triple differences (b1,b2,b3)=(2,3,7), and passive bound U<=10. Thus the
export's quantities satisfy X<=5,F>=66,G>=95,Y<=10/11 and alpha=190,
with positive affine slope58. Its BLOCK alternative holds for a<=0.
For a>=0 the determinant bound is greater than24719/2; its INDEX alternative
holds for a>=1/2, or for p=0 because pair12 then has zero owner2 reward.
These checks exhaust the displayed union, including all equality boundaries.

The mechanism is selection, not universal invariance. The exact crossing
at the end of Section8 remains a valid positive-output Nash root even though
the table now has UE. A passive bound makes every bad triple regular with
index-1 and gives at most one such triple. Eligible bad pairs also have
index-1. Total Nash degree+1 forces an alternative good root. The export
proves that these selected roots suffice on the closed passive domain,
including local stalls and complete unilateral deviations.

Within p>=0, the only fixed-core strip left outside this raw criterion is

    -1/2<K<0, p>0.

Here the active pair12 has opposite joining signs and may have index+1.
Its continuation equations are v1=(-K-1/2)x2<0 and v2=(p+2)x1>0.
At a generic input, coexistence of a bad pair and a bad triple still forces
a good root: their indices sum to zero. At such a generic input, failure of
selected return requires the bad pair to be its sole Nash root. For the
broader class allowing the unlisted rewards to vary, the
[exact recovery obstruction](CODEX_COORDINATOR__BOUNDED_CROSSING_SELECTION.md)
shows that allowing arbitrarily long Nash words on the entire passive box
cannot close this strip: an interior input has a unique bad pair, followed
by a positive point whose only Nash root is AllContinue. That input lies
outside the actual payoff convex hull. The next task is to exploit actual
joint continuation constraints, or use a construction beyond exact Nash
prefixes. A virtual positive crossing alone proves neither impossibility
of UE nor occurrence at an actual minimum.
Negative p outside the main criterion and signed original own levels are
separate remaining portions; this strip is not the full Fin4 frontier.
