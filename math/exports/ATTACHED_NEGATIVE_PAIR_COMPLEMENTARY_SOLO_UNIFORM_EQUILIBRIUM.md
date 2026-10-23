# An attached negative pair with arbitrary passive rewards

## 1. A raw four-player existence theorem

There are four players. At a live date each independently chooses Continue
or Quit. A nonempty quitting coalition S absorbs forever at the finite
original reward vector r(S); every live reward and literal Never reward is
zero. Private behavioral randomization is independent. A unilateral
replacement may be any behavioral strategy. A uniform-equilibrium payoff
means ONE fixed target such that, for every positive accuracy, a profile
delivers that target and caps every unilateral deviation over every
sufficiently long finite horizon. The profile may depend on accuracy.

Put s_i=r_i({i}) and Z_i(S)=r_i(S)-s_i for NONEMPTY S only. The own
levels s_i are arbitrary signed numbers; no translation of live or Never
is made. After relabeling, suppose the literal singleton differences are

    G=[ 0  -a  -b   c ]
      [-d   0   e   f ]
      [ g   h   0  -k ]
      [-l   m   n   0 ],

where a,b,c,d,e,f,g,k,l,n>0 and h,m are arbitrary real numbers, including
zero. Write Z(01)=(Pi0,Pi1,K,J). Assume Pi0,Pi1>=0 and the six inequalities

    Z2(02),Z2(12),Z2(012)<=0,
    Z3(03),Z3(13),Z3(013)<=0.                        (CAP)

THEOREM. Every such original reward table has a uniform-equilibrium payoff.
K and J range independently over ALL finite real numbers. Every other
higher-coalition reward is arbitrary finite data. No determinant, inverse,
root, spectral vector, continuation law, phase rate, or supplied controller
is a hypothesis. In particular no upper bound on Pi0 or Pi1 is required.

The proof first uses established same-table no-equilibrium consequences
to reduce to a positive inverse-column chamber. It then produces a joint01
phase, a possibly absent solo2 phase, and a solo3 phase. A crossed projection
on a compact rectangle produces the complementary boundary as well as the
interior. All phase choices and one target are fixed before accuracy.
The explicit construction refines only the present solo phases.

This is ordinary mathematical evidence, not a claim that this new theorem
has been formalized. The unrestricted Fin4 conjecture remains open.
The six caps and nonnegative joint participant premiums remain real
restrictions. When h,m are positive the singleton chamber has exactly one
mutually negative pair; the theorem also covers the stated other signs.
Strict caps and positive Pi0,Pi1 give open regions in all sixty rewards.

## 2. The same-table source supplies every numerical singleton guard

### 2.1 Exact source and the old child exit

Suppose, toward contradiction, that the original game has no UE payoff.
The declaration
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`
gives standard Q and absence of a homogeneous simplex solution on its
normal core. The declaration
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`
makes this core all four players. The definitions `StandardQMatrixSide`
in `UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`,
`normalizedSoloMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`, and
`normalizedNormalPlayerMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean` identify
the matrix with the SAME literal G above, up to reindexing the full core.
Thus G is standard Q and R0. Here standard Q means every offset has a
nonnegative complementary solution; R0 means there is no nonzero x>=0
with Gx>=0 and x_i(Gx)_i=0. Homogeneous simplex normalization and R0
are equivalent by
`isR0Matrix_iff_not_singletonLCPFeasible` in
`MathUE/LinearProgramming/CopositiveQ.lean`.
Finally `singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
gives degree(G)=1. No auxiliary normalized game is assumed to lack UE.

The old raw child theorem
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`
produces original UE whenever a principal triple has nonnegative inverse
and its exterior inverse row is nonnegative. This theorem puts no extra
restriction on the own or higher rewards. Such a child is therefore
impossible under the present no-UE assumption.

### 2.2 A complete large-offset support argument

Let B=G_023. Its adjugate is strictly positive and

    Delta=det B=cgn-bkl,
    N=G_1,023 adj(B)=(N0,N2,N3),
    N0=-dkn+ekl+fgn,
    N2=bfl-cdn+cel,
    N3=-bdk+bfg+ceg.

Direct identities give

    N0=(k/c)N2+f Delta/c,
    N3=(bk/(cn))N2+Delta(bf+ce)/(cn).                (S1)

If Delta>0 and N2>=0, B has strictly positive inverse and its exterior
inverse row is nonnegative, giving the excluded child. Assume that exit
does not occur. Fix positive y0,y1,y3 in a compact box and let y2=Y
tend to infinity. A complementary solution at offset -y with support S
satisfies G_SS x_S=y_S and G_(I\S),S x_S>=y_(I\S).

Every proper support containing2 is excluded for all sufficiently large Y.
Singletons and pairs02,23 cannot have strictly positive active targets.
Pair12 and triple012 have respectively an outside or active row0 equal
to -a*x1-b*x2<0. For triple123, the active equation
e*x2+f*x3=y1 bounds x2,x3 uniformly. Its outside inequality
-a*x1-b*x2+c*x3>=y0 then bounds x1. Its active row2 cannot reach Y.
This argument never divides by h or m and covers their zero values.
For triple023, Delta<0 gives a strictly negative inverse. Delta=0 gives
a strictly positive left null vector from a row of adj(B), also excluding
a strictly positive target. If Delta>0, absence of the child and (S1)
force N2<0, and its exterior row1

    (N0*y0+N2*Y+N3*y3)/Delta

falls below y1 for all large Y. These exclusions are uniform on the box.

Supports omitting2 require a different argument, with no proper-minor
assumption. If such solutions x existed along Y tending to infinity,
their sum norms would diverge because row2 is at least Y. Normalize by
that norm and pass to a fixed-support subsequence. The limit v has
v>=0, sum v=1, v2=0 and Gv>=0. On every positive coordinate of v the
active equality gives (Gv)_i=0; coordinate2 is zero. This is a nonzero
homogeneous complementary vector, contradicting R0. Compactness gives
the same uniform exclusion over the bounded positive offset box.

Consequently all solutions at large Y have full support. Standard Q
supplies one for every such y, an open set of targets, so G is invertible.
The sole solution is G^-1 y>>0. Dividing by Y and taking the limit gives
v=G^-1 e2>=0. At any such y the unique full-support root is nonsingular
and there are no inactive inequalities to check. The finite degree
formula gives degree(G)=sign(det G), hence det G>0. This use of
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` requires nonsingularity only
of the actual root's active matrix; no unrealized proper principal is
assumed nonsingular.

### 2.3 Strictness and the produced primitives

If v2=0, Gv=e2 would make v a nonzero homogeneous complementary vector;
thus v2>0. Row0 gives c*v3=a*v1+b*v2>0, and row1 gives
d*v0=e*v2+f*v3>0. Hence v0,v3>0. If v1=0, the positive core vector
(v0,v2,v3) would solve Bv_core=e2_core. Delta<0 contradicts the negative
inverse, and Delta=0 contradicts the positive left null vector. Therefore
Delta>0. The zero row1 residual then gives N2=0, and (S1) gives the
excluded nonnegative exterior inverse row. Thus v1>0 as well.

Define

    A=lf/d-mc/a, H=n-le/d-mb/a,
    u=cH-bA, vstar=fH+eA.

Exact cofactors and the determinant identity are

    adj(G)e2=(a*vstar,d*u,ad*A,ad*H),
    det G=ag*vstar+dh*u-kadH.                       (S2)

The positive determinant and strict inverse column force A,H,u,vstar>0.
In particular the no-UE source supplies precisely the numerical guards
A>0,u>0,det G>0 used below. This completes the algebraic reduction even
when h or m vanishes or a proper principal matrix is singular.

## 3. A global strip of literal joint equations

For 0<z<1 let ymax(z)=cz/(b+cz). For 0<=y<=ymax put eta=(1-y)(1-z)
and define X>0,W>=0 by the unique inverse equations

    (Pi0+a)W-eta Pi0 W/(1+W)=cz(1-y)-by,
    (Pi1+d)X-eta Pi1 X/(1+X)=fz(1-y)+ey.             (3)

Both left sides vanish at zero, diverge to infinity, and have derivatives
at least a,d. Their first right side is nonnegative and the second is
positive. Thus the roots exist and are continuous everywhere on the strip.
They obey

    W<=cz/a, X<=(f+e)/d,

and W>0 except at y=ymax, where W=0. Write

    den=(1+X)(1+W), P=gX+hW+KXW,
    B=P/den, V0=kz/(1-z),
    R=lX-mW-JXW-ny,
    T=ge/d-hb/a, F=B-V0+(T/H)R.                     (4)

The rates x=X/(1+X),w=W/(1+W) will be the owners0,1 joint hazards.
Here V0 is an auxiliary floor, not necessarily the final owner2 target.

## 4. Four exact boundary signs

At the upper strip boundary, W=0 and

    X<=z(bf+ce)/[d(b+cz)],
    R(ymax,z)<=-u z/(b+cz)<0.                       (5)

No sign or magnitude of K,J,Pi0,Pi1,h,m is used in (5), apart from the
stated raw hypotheses.

Uniformly on the entire strip segment as z tends to zero, y=O(z),
X=O(z),W=O(z), since y<=cz/b. Expanding (3), whose inverse derivatives
are bounded below, gives

    aW=cz-by+O(z^2), dX=fz+ey+O(z^2),
    R=Az-Hy+O(z^2),
    B-V0=(gf/d+hc/a-k)z+T y+O(z^2).                (6)

All constants in these estimates depend on the fixed finite raw table,
not on y or a subsequently requested accuracy. Consequently

    F=[det G/(adH)]z+O(z^2)>0                     (7)

on an ENTIRE sufficiently small-z face: the y coefficient cancels.
Also R(0,z)=Az+O(z^2)>0 for sufficiently small z.

As z tends to one, X,W,R stay bounded uniformly over the strip. B is a
convex combination of g,h,K,0, so it is bounded too. Since V0 tends to
positive infinity, F<0 uniformly on a sufficiently large-z face.

Select fixed 0<zL<zR<1 such that F>0 throughout the left face,
R(0,zL)>0, and F<0 throughout the right face. Normalize the strip by
y=s*ymax(z), with 0<=s<=1. We have exactly these four signs:

    left z=zL: F>0;
    right z=zR: F<0;
    top s=1: R<0;
    bottom-left (s,z)=(0,zL): R>0.                 (8)

There is NO assumed sign of R on the rest of the bottom face.

## 5. Crossed projection produces an interior or complementary boundary root

Apply Brouwer's fixed-point theorem to the continuous self-map of the
rectangle [0,1] times[zL,zR]

    Phi(s,z)=(projection_[0,1](s-F),
              projection_[zL,zR](z+R)).             (9)

Every boundary case is explicit. On the left face, F>0 makes the first
fixed-point equality possible only at s=0. At that corner R>0 makes the
second equality impossible. On the right face, F<0 makes the first
equality possible only at s=1, but R<0 there makes the second impossible.
Finally, on the top face R<0 makes the second equality possible only
on the already excluded left face. Thus no fixed point lies on the
left, right, or top face.

At a fixed point, z is interior and s<1, so R=0. If s>0 as well, the
first equality gives F=0. If s=0, that equality gives F>=0. Hence the
produced values satisfy exactly

    0<z<1, 0<=y<ymax, X,W>0, R=0,
    either y>0 and B=V0,
    or     y=0 and B>=V0.                           (10)

This is a finite-dimensional existence argument. It does not select a
continuous zero branch, assume uniqueness, or assume that folds are absent.
Choose one such fixed point once and for all before accuracy.

## 6. The boundary is an actual missing solo phase

Define the ACTUAL owner2 target by the unified formula

    V=[P-(1-y)kz]/[den-(1-y)(1-z)].                 (11)

Its denominator is strictly positive. If y>0, then B=V0, and substitution
gives V=V0. If y=0, (11) becomes

    V=(P-kz)/(den-1+z),
    V-V0=[(1-z)P-kz den]/[(1-z)(den-1+z)]>=0,      (12)

where the inequality is exactly B>=V0 from (10). Therefore in all cases

    V>=V0>0, D2=(1-z)V-kz>=0, y*D2=0.             (13)

Set the native value immediately before the joint phase to

    U=(Pi0*w,Pi1*x,V,0).

Prepending solo3 gives

    U3=((1-z)Pi0*w+cz,(1-z)Pi1*x+fz,D2,0).

Prepending solo2, when present, gives

    U2=((Pi0+a)W,(Pi1+d)X,(1-y)D2,ny).             (14)

The first two coordinates in (14) are exactly (3). All coordinates of
U,U3,U2 are nonnegative. If solo2 is present, its mover's value before
and after that phase is zero by (13). Solo3's mover's value is always
zero. If y=0, simply omit solo2; D2 may then be strictly positive and
player2 chooses Never at every date.

At the joint phase the two participants' Quit endpoints are Pi0*w and
Pi1*x. Their Continue endpoints equal those values because

    U2_0=(Pi0+a)W, U2_1=(Pi1+d)X.

Owner3's prescribed Continue value is

    [-lX+mW+JXW+ny]/den=-R/den=0.

Owner2's Continue value is [P+(1-y)D2]/den=V, exactly by (11).
Their forced-Quit endpoints are weighted averages of own native zero
and the six coordinates capped in (CAP), hence are nonpositive. Thus ALL
joint pure action endpoints are capped by the actual prescribed values.
No auxiliary floor is substituted for the actual boundary payoff.

## 7. Every complete deviation and the fixed original target

For delta>0 split every present solo hazard into finitely many hazards at
most delta, preserving its total Continue product. Its affine payoff map
and boundary values are unchanged. Every intervening vector lies on the
same nonnegative segment and its mover's value is zero.

Let C=max(0,max_(i!=j) Z_i({i,j})). At an inactive singleton microstep of
hazard t<=delta with continued cap excess d_i>=0, the new excess is

    max(t Z_i({i,j})-U'_i,(1-t)d_i)<=max(C delta,d_i).

The mover's excess does not increase. The exact joint endpoint inequalities
also do not increase the maximum excess. Iterating from an arbitrary forced
Quit deadline therefore caps its gain by C delta, without multiplying by
the number of dates or periods.

Owners0,1 have strictly positive proper joint hazards and owner3 has a
strictly positive proper solo hazard. Even if owner2 never quits, EVERY
player's deleted-opponent clock contracts strictly over a period. Thus
opponents absorb almost surely against every unilateral replacement.
The late-deadline limit gives the same bound for literal Never, and the
mixture representation of a behavioral stopping law gives it for every
complete unilateral deviation. The prescribed periodic payoff is exactly
U by Bellman iteration with vanishing survival remainder.

All these unilateral laws absorb surely, so the original finite-terminal
shift adds exactly s_i to each prescribed and deviating value. The target
is s+U; live and Never were never translated. For each fixed delta the
finite period gives a common geometric opponent tail. Splitting at an
early date and then taking the horizon large bounds finite-average errors
uniformly over all deviations. Choose delta first and then the common
horizon threshold. The same profile works for every larger horizon and
s+U was fixed before accuracy. This constructs original UE on the numerical
chamber and contradicts the no-UE source of Section2. The raw theorem follows.

## 8. An entire new passive ray and prior admissions

### 8.1 Every reward and the actual source

For EVERY J>=1 use original own singletons one and the following complete
native table
Z; the original reward at each nonempty coalition is r_i(S)=1+Z_i(S).
Live and Never remain zero. There is no abstract continuation or source
minimizer in these inputs.

| S | Z(S) |
| --- | --- |
| 0 | (0,-9,5,-6) |
| 1 | (-5,0,2,3) |
| 2 | (-2,6,0,7) |
| 3 | (3,4,-3,0) |
| 01 | (1/10,1/10,-25,J) |
| 02 | (-1/100,27,-1/100,0) |
| 03 | (4,0,0,-7) |
| 12 | (28,-1/100,-1/100,0) |
| 13 | (0,-1/100,0,-1) |
| 23 | (0,11,-1,-1) |
| 012 | (9/100,9/100,-1/100,14) |
| 013 | (1,509/100,-2599/100,-5) |
| 023 | (1,32,-301/100,-9) |
| 123 | (0,49/50,-1/100,-12) |
| I | (1,27/25,1,1) |

The fixed matrix is the literal singleton table displayed above. Its
values are det G=133, A=13/15, H=9/5, u=11/3, vstar=62/5.
The participant pair premiums are Pi0=Pi1=1/10, K=-25, and J is free
throughout [1,infinity). The six capped entries are
(-1/100,-1/100,-1/100,-7,-1,-5). The theorem produces absorbing periodic
profiles and a fixed original target for EVERY member of this ray.
Each member has strict raw inequalities, hence also a neighborhood in
all sixty reward coordinates admitted by the theorem.

The earlier arbitrary-K joint-pair producer required J=0 or the strict
bound |J|<theta. At these fixed singleton and participant data its explicit
bound is theta=135/542<1, so it admits no member of this ray. Relabeling
does not evade this comparison: the unique mutual-negative pair is01;
owner1 has positive entries from both outsiders while owner0 has one
negative and one positive entry, fixing the pair roles; those signs also
fix the solo roles. The new proof removes this restriction completely,
along with all upper bounds on participant premiums and all numerical
singleton guards. Its boundary can omit solo2; it is not a larger bound
for the older monotone-root argument.

### 8.2 Matrix and raw sign-family comparisons

All eleven nontrivial principal minors of G are nonzero, and every column
has a negative entry, so G is R0. At offset -1 the unique complementary
solution is

    support023, x=(16/23,0,17/23,19/23),
    Gx-1=(0,11/23,0,0).

Its active determinant is69>0. The exact support census gives degree one
and hence standard Q, using `r0Degree_eq_sum_admissible_inverse_supports`
in `MathUE/LinearProgramming/FiniteSupportDegree.lean` and
`isStandardQ_of_r0Degree_ne_zero` in `MathUE/LinearProgramming/R0Degree.lean`.
This is a genuine Q-side calibration, not an example already settled by
the non-Q source exit. G also maps a strictly positive vector to a strictly
positive vector by a small positive perturbation of x's coordinate1.

The principal triple determinants are (-114,39,69,2). Only023 has a
nonnegative inverse, and its exterior inverse row is

    (59/69,-11/23,76/69).

So every passive-positive-inverse child selection fails. The full inverse is

    G^-1=[  2  45  62  -38 ]/133.
         [-59  69  33  -76 ]
         [ 27   9  39   19 ]
         [-36 121  81 -114 ]

Its mixed first column defeats full inverse positivity and the family
requiring EVERY inverse column to be made strictly positive by its own
sign, under all relabelings. Bounded full-inverse corners, moving
positive-passive full-inverse cones, and full-positive-inverse coalition
jackpot theorems fail their baseline matrix premise as well.

The distinct SINGLE-column jackpot theorem does pass its matrix premise:
columns1 and2 are strictly positive. No isolated-table exclusion from its
unspecified large-pole threshold is claimed. Its guarantee fixes a signed
PARTICIPANT coordinate as the growing pole and bounds the remaining data,
or bounds them by a small power of that pole. In contrast, the present theorem covers
the entire ray obtained by varying ONLY the passive coordinate Z3(01)=J
toward plus infinity in this table, with every participant coordinate
fixed. That coordinate cannot be the older theorem's selected pole, and
no fixed bound on its other data covers this ray. Rechoosing the data box
or pole coefficient separately at each J gives no uniform diagonal
guarantee from its existential threshold. This is a family-level
nonimplication, not a claim that every finite member lies below or outside
all possible thresholds of that theorem.

The mutual-negative pair01 is neither standard Q nor homogeneous: its
negative invertible 2x2 matrix cannot solve offset -1 on any support, and
its zero-offset homogeneous problem has no nonzero nonnegative solution.
Thus projective Q-bar fails, including its homogeneous alternative, as
defined by `isProjectiveQMatrix_iff_standard_or_homogeneous` in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.

There is exactly one mutually negative pair01; the mutually positive
pairs12 and13 share a vertex. This excludes the reciprocal-opposition
and no-mutually-negative classes, the favorite/matching phase families
requiring two disjoint same-sign pairs, and the opposite-sign matching
classes under every role choice. The negative-pair-funded boundary class
requires TWO distinct mutual-negative pairs sharing its pivot, so its
finite raw sign guards also fail under all relabelings. The cyclic-child
one-joint-phase classes require a positive-inverse child and an allnegative
pivot column into it. The only candidate child023 has pivot1's entries
(-5,2,3), so that raw class fails too. There is no negative Hamiltonian
cycle, excluding the named smaller/larger eigenvalue Hamiltonian adapters.

For the two-pair joining-cap family and its positive-participant variants,
each pair partition has a negative required scheduled joining increment:
01|23 fails at receiver3 against2, value -8; 02|13 fails at receiver2
against0, value -501/100; 03|12 fails at receiver3 against0, value -1.
These are literal finite raw-family failures, not claims about arbitrary
supplied controllers or unspecified perturbation neighborhoods.

### 8.3 Every quiet-child choice

For a child C and outside owner o, the capped-clock condition requires
nonnegative weights w_i satisfying, for every nonempty S subset C,

    F_S: sum_i w_i[-Z_i(S)]>=-Z_o(S),
    J_S: sum_i w_i[Z_i(S+i)-Z_i(S)]>=Z_o(S+o)-Z_o(S),

and its Never row. These are the literal fields of
`CappedClockParentRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`.
The following exact positive row combinations have nonpositive coefficients
and positive lower bounds. They are impossible for any nonnegative weights,
even with arbitrary Never-row slack. Every complete child has such an
outside owner; no claim that every individual child/outside pair fails is
needed.

| C | o | Rows | Coefficients in increasing C | Lower bound |
| --- | --- | --- | --- | --- |
| 0 | 1 | F0 | (0) | 9 |
| 1 | 0 | F1 | (0) | 5 |
| 2 | 0 | F2 | (0) | 2 |
| 3 | 2 | F3 | (0) | 3 |
| 01 | 2 | J01 | (0,0) | 2499/100 |
| 02 | 1 | F0 | (0,-5) | 9 |
| 03 | 2 | F3 | (-3,0) | 3 |
| 12 | 0 | F1 | (0,-2) | 5 |
| 13 | 0 | F1 | (0,-3) | 5 |
| 23 | 0 | F2 | (0,-7) | 2 |
| 012 | 3 | 299F0+100J02 | (0,0,-1495) | 894 |
| 013 | 2 | F3 | (-3,-4,0) | 3 |
| 023 | 1 | 7F0+6F2+4F3 | (0,-23,0) | 11 |
| 123 | 0 | F1 | (0,-2,-3) | 5 |

### 8.4 Complete induced Nash census and the ACTUAL punishment floors

The exact native zero-continuation Quit-minus-Continue polynomials are

    F0=(1-q3)[(51/10)q1+(199/100)q2-35q1q2]+q3,
    F1=(91/10)q0-(601/100)q2-30q0q2-(401/100)q3,
    F2=-(501/100)q0-(201/100)q1+(3201/100)q0q1+2q3,
    F3=-q0-4q1-8q2-J*q0*q1*(1-q2).

The program derives these symbolically for J=1+tau, tau>=0, from every actual opponent coalition. The new F3 term is nonpositive throughout the cube, so the following exhaustive argument holds uniformly on the entire ray. Fixing
owner j surely at Quit makes these the other owners' original-game
differences as well, because the sure opponent removes continuation.
The COMPLETE complementary Nash correspondences each contain one point:

| Fixed j | Unique point (q0,q1,q2,q3) |
| --- | --- |
| 0 | (1,167/1000,910/3601,0) |
| 1 | (67/900,1,510/3301,0) |
| 2 | (1,0,1,0) |
| 3 | (1,301/3000,509/3601,1) |

For j=0, F3<=-1 forces q3=0, leaving

    F1=91/10-(3601/100)q2, F2=-501/100+30q1.

The first is decreasing through zero and the second increasing through
zero, with both thresholds strictly inside(0,1). An endpoint for either
variable forces the other to an endpoint inconsistent with the first
best response. Thus both must be interior and the two zeros give the
displayed point. For j=1, F3<=-4 again forces q3=0, leaving

    F0=51/10-(3301/100)q2, F2=-201/100+27q0,

and the same exhaustive argument applies. For j=2, F3<=-8 forces q3=0;
F1=-601/100-(209/10)q0<0 forces q1=0, and F0=199/100>0 forces q0=1.
For j=3, F0 is identically one, forcing q0=1. The remaining two equations
are F1=509/100-(3601/100)q2 and F2=-301/100+30q1, giving the last point
by the same endpoint/interior proof. This includes every face of each cube.

Let v_j be the actual ORIGINAL punishment value and
h_j=product_(i!=j)(1-q_i). The owner's exact floor excess is

    -F_j(q)+h_j(v_j-1).                               (19)

The continuation term cannot be discarded for owners0 and1. Their every
participant reward is at least99/100. Immediate sure Quit therefore
guarantees at least99/100 against every opponent plan, so v_j>=99/100.
This follows directly by taking the supremum of behavioral replies and
then the infimum over opponent profiles, the definitions in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`.

At their unique points F0=-339291/2770000 and
F1=-17710703/29709000. Since h_j<=1, (19) is at least

    311591/2770000>0 for owner0,
    17413613/29709000>0 for owner1.

Owners2 and3 have sure opponent0, so h_j=0. Their floor excesses are
501/100 and
1+4*(301/3000)+8*(509/3601)+J*(301/3000)*(1-509/3601)>1. Thus every singleton-base
selection fails for its ACTUAL punishment value. For owners0 and1 no
claim of immunity to an arbitrary negative continuation is made.

The exact premise is `quittingSingletonBaseOwnerFloorExcess_nonpos_iff`
and the assumption in `nonempty_quittingSingletonBaseCertificate_of_inducedNash`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
Any smaller free set satisfying all its outsider inequalities extends to
one of these same complementary points, so no free-set choice avoids the
floor. A persistent base of size at least two satisfying every leave/free/
outsider condition would yield a full Nash point with a sure owner; each
owner's displayed strictly negative F_j excludes this. This covers
`nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
The induced-owner chamber tests fail for the same reason; their Never
variant separately fails since original own levels are one. Both structures
are in `UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`.

### 8.5 Premium, floor, ledger, and background tests

The premium traps are exactly01 and I. The greatest trap is therefore I,
so the at-most-two/three premium-core rules do not apply. Every grand
participant premium is positive: (1,27/25,1,1). Its sure product refutes
`HasProductLowQuittingPremium`, the raw premise of
`exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`.
It also defeats EVERY nonzero nonnegative weighted forced-Quit upper
average on the full trap. The mixed-trap charge alternative fails at its
penultimate row T=123 because owner0's joining increment is +1, independent
of its magnitude constants.

Put k(S)_i=Z_i(S union{i}) and h(S)=Z(S). The exact identities

    401k(2)+k(3)=(-1/100,-402/100,-1,-401),
    3h(0)+3h(1)+h(01)+J*h(13)=(-149/10,-269/10-J/100,-4,-9)

exclude respectively EVERY nonzero nonnegative global forced-Quit floor
weight and EVERY nonzero nonnegative proper-passive-ledger weight. Thus
both two-ledger and graph-free H/J admissions fail before their other
conditions. Every owner has a below-own participant pair, so there is no
owner with globally nonnegative participant premiums for protected-leaver
variants. Joining against singleton1 gains51/10 for owner0, while joining
against12 loses2791/100. Hence the no-strict-background-reversal condition
fails as well. The positive grand also violates globally capped-participant
and unweighted upper-premium conditions.

### 8.6 Every passive-pole role

The old three-passive-pole finite guards, in ordered distinct roles
(i,j,k,l), are

    A=r_i(il)-r_i(l)>0, B=r_i(ikl)-r_i(kl)<0, c=A/(A-B),
    A2=r_k(kl)-r_k(l)<0, B2=r_k(ikl)-r_k(il)<0,
    L0=(1-c)[r_j(jl)-r_j(l)]+c[r_j(jkl)-r_j(kl)]<0,
    L1=(1-c)[r_j(ijl)-r_j(il)]+c[r_j(I)-r_j(ikl)]<0,
    F0=c[(1-c)r_l(l)+c*r_l(kl)-r_l(k)]>0,
    F1=(1-c)[r_l(il)-r_l(i)]+c[r_l(ikl)-r_l(ik)]<0.

Only five of the twenty-four role choices satisfy the first two guards.
Their later failures are explicit:

| Roles | Failed necessary guard |
| --- | --- |
| (0,3,1,2) | F0=-119041601/894010000<0 |
| (0,3,2,1) | B2=2499/100>0 |
| (1,3,2,0) | B2=2499/100>0 |
| (2,0,1,3) | L0=1>0 |
| (2,1,0,3) | A2=1>0 |

Thus every role fails a literal finite guard; no unknown asymptotic
threshold or alteration of an older theorem's threshold is used.

These comparisons hold uniformly for every J>=1 and establish an entire original-table ray outside the displayed
finite matrix, quiet-child, punishment, premium, weighted, ledger,
matching/joint-phase, and passive-pole admission tests. The single-column
jackpot comparison has the different, explicitly family-level scope just
stated. Every member and an open neighborhood are admitted by the present raw theorem. This
is not a claim that every possible supplied-profile certificate fails,
nor that every stationary profile is impossible. The new theorem produces
its own complementary root, phase choices, solo hazards, complete stopping
laws and fixed payoff. The source assumptions used in Section2 are not
extra raw premises, and the finite matrix checks here are distinguished
from the actual reward-table producer comparisons.

## 9. Exact boundary and negative tests

The following are separate algebra and complete-cap tests, not the coverage
calibration of Section8. Keep its singleton matrix and set the six caps
to -1 and all remaining unspecified higher native rewards to9. Take

    z=1/2, y=0, X=W=1/10,
    Pi0=55/3, Pi1=121/6, K=300, J=30.

The exact equations give x=w=1/11, den=121/100, P=37/10, and

    V0=3, V=220/71, D2=7/142>0,
    U=(5/3,11/6,220/71,0),
    U3=U2=(7/3,35/12,7/142,0).

Thus the actual complementary branch has no solo2, and V is STRICTLY
larger than the auxiliary floor V0. Replacing V by V0 would violate the
actual owner2 Bellman equation. Both participant premiums are large and
J is positive, testing precisely the assumptions removed by this packet.

A second dropped-solo example has negative K and zero participant
premiums:

    z=1/100, y=0, X=1/225, W=3/500,
    Pi0=Pi1=0, K=-25, J=325.

Formula(11) again gives D2>0. In this example pure joint01 is not Nash:
owner2 improves from K=-25 to the capped triple reward -1 by joining.
The periodic complementary construction remains valid. An interior test
with both solos present is

    z=1/10, y=1/20, X=17/225, W=37/1000,
    Pi0=Pi1=0, J=-1725/629,
    K=[(1+X)(1+W)/3-5X-2W]/(XW), V=1/3, D2=0.

The exact program checks all joint equations and every finite deadline
and literal Never for refinements of lengths1,2,7, both natively and with
signed original own levels (2,-3,5,-7). A rational subdivision of total
hazard t into n pieces is t/[n-(n-1-j)t], j=0,...,n-1; its survival
product is exactly1-t and its largest piece tends to zero. The full-cap
calculation is independent of the local endpoint bound: for each owner
it accumulates all opponent absorption rewards B and survival H over one
period. Deadline values in later periods interpolate between the first
period's values and Never=B/(1-H), so their maximum is computed exactly.
The asserted cap is C times the largest microhazard, as proved in Section7.

The signs at the excluded top, left and right faces of the rectangle
are strict for every fixed input table; no uniqueness or nondegeneracy of
the selected fixed point is needed. The genuine bottom boundary above
shows why an interior-zero argument alone would omit a legal outcome.
Negative participant premiums and violations of (CAP) are not silently
included by any of these tests.

## 10. Source correspondence and formalization handoff

The matrix source declarations and the old raw child exit in Section2
are existing results. The new finite-dimensional algebraic alternative,
global crossed projection, complementary target and complete cap invariant
are ordinary proofs supplied here. The relevant exact declarations and
hypotheses were inspected; no new Lean source or build is asserted.

`eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff` in
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` takes exact
cyclic policy equations and contraction of every player's opponents over
one period. Sections3–7 supply these for every refined period, including
when owner2 always chooses Never.
`quittingRootCompanionMap_eq_max_endpoints` in
`UniformEquilibrium/Quitting/Cycles/PeriodicRootResponseSystem.lean`
is the exact maximum of the two root endpoints used in the microstep and
joint recursion. The proof must preserve the maximum-excess invariant;
replacing it by a sum of date errors would lose the needed conclusion.

`quittingHazardStoppingLaw_expect` in
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean` decomposes a
bounded response over finite stopping times and literal Never. This is
the complete-deviation consumer after the Never limit. Original signed
translation is justified by opponent absorption, not by translating
AllNever. Finally
`abs_finiteAveragePayoff_update_sub_terminal_le_opponentLiveCesaro` in
`UniformEquilibrium/Quitting/Cycles/PeriodicFiniteHorizonRate.lean`
bounds every behavioral deviation's horizon error by the common
opponent-live Cesaro term, which tends to zero by periodic contraction.

The intended new theorem takes only a Fin4 reward table and the finite
raw guards of Section1. First prove the algebraic alternative under
standard Q/R0/degree1, with proper supports omitting2 handled by normalized
compactness. Then prove the numerical producer as a separate lemma:
the monotone inverse equations, uniform small-strip expansion, strict
top and large-z signs, crossed rectangle fixed point, the actual V
formula and complementarity y*D2=0, exact joint endpoints, solo
subdivision, maximum-excess recursion, and deleted-opponent contraction.
A rectangle form of Brouwer is the only general topological existence
step. The final theorem combines the existing no-UE source and child
exit with this producer. No strategic root, continuation law, phase
choice, or desired equilibrium may remain as an unproduced field.

The remaining raw frontier here is explicit: outsider caps may fail, or
one of Pi0,Pi1 may be negative. The present source reduction does not
force these higher-reward guards. Enlarging the joint cohort or changing
the phase architecture would require a new producer and full-cap proof.

## Appendix. Complete exact reproduction

Save the following program as a Python file and run with Python and
SymPy installed. There are no local imports or file dependencies.
It verifies the whole J>=1 ray symbolically, the complete table and
admission comparisons, the source identities with unrestricted h,m,
and the exact boundary/interior policies with complete periodic caps.
The analytic support compactness, fixed-point theorem and full behavioral
consumer are proved above; the finite program does not replace them.


```python
"""Exact checks for the complementary joint-pair producer and J>=1 ray.

No equilibrium existence claim is proved by this finite program. It verifies
the complete table, literal quiet-child Farkas obstructions, and the stated
weighted/premium and older passive-pole admission screens.
"""
from itertools import combinations, permutations, product
import sympy as s

R = s.Rational
I = tuple(range(4))
COAL = tuple(A for n in range(1, 5) for A in combinations(I, n))
G = s.Matrix([[0, -5, -2, 3], [-9, 0, 6, 4],
              [5, 2, 0, -3], [-6, 3, 7, 0]])
q = s.symbols('q0:4')
tau = s.symbols('tau', nonnegative=True)
JJ = 1+tau
F = s.Matrix([
    (1-q[3])*(R(51, 10)*q[1]+R(199, 100)*q[2]-35*q[1]*q[2])+q[3],
    R(91, 10)*q[0]-R(601, 100)*q[2]-30*q[0]*q[2]-R(401, 100)*q[3],
    -R(501, 100)*q[0]-R(201, 100)*q[1]+R(3201, 100)*q[0]*q[1]+2*q[3],
    -q[0]-4*q[1]-8*q[2]-JJ*q[0]*q[1]*(1-q[2])])
PASSIVE = {
    (0, (1, 2)): 28, (0, (1, 3)): 0, (0, (2, 3)): 0,
    (1, (0, 2)): 27, (1, (0, 3)): 0, (1, (2, 3)): 11,
    (2, (0, 1)): -25, (2, (0, 3)): 0, (2, (1, 3)): 0,
    (3, (0, 1)): JJ, (3, (0, 2)): 0, (3, (1, 2)): 0,
    (0, (1, 2, 3)): 0, (1, (0, 2, 3)): 32,
    (2, (0, 1, 3)): -R(2599, 100), (3, (0, 1, 2)): 14}


def native(i, A):
    A = tuple(sorted(set(A)))
    if not A:
        return s.S.Zero
    if i in A:
        B = tuple(j for j in A if j != i)
        return native(i, B)+F[i].subs({q[j]: int(j in B) for j in I})
    if len(A) == 1:
        return G[i, A[0]]
    return s.sympify(PASSIVE[i, A])


def reward(i, A):
    assert A
    return 1+native(i, A)


def joining(i, A):
    return native(i, set(A) | {i})-native(i, A)


TABLE = {(i, A): native(i, A) for A in COAL for i in I}
assert len(TABLE) == 60
LITERAL = {
    (0,): (0,-9,5,-6), (1,): (-5,0,2,3),
    (2,): (-2,6,0,7), (3,): (3,4,-3,0),
    (0,1): (R(1,10),R(1,10),-25,JJ),
    (0,2): (-R(1,100),27,-R(1,100),0),
    (0,3): (4,0,0,-7), (1,2): (28,-R(1,100),-R(1,100),0),
    (1,3): (0,-R(1,100),0,-1), (2,3): (0,11,-1,-1),
    (0,1,2): (R(9,100),R(9,100),-R(1,100),14),
    (0,1,3): (1,R(509,100),-R(2599,100),-5),
    (0,2,3): (1,32,-R(301,100),-9),
    (1,2,3): (0,R(49,50),-R(1,100),-12),
    I: (1,R(27,25),1,1)}
assert all(s.expand(TABLE[i,A]-LITERAL[A][i]) == 0 for A in COAL for i in I)
assert G.det() == 133
assert all(native(i, [j]) == G[i, j] for i in I for j in I)
assert [native(i, [0, 1]) for i in I] == [R(1, 10), R(1, 10), -25, JJ]
CAPS = [(2, (0, 2)), (2, (1, 2)), (2, (0, 1, 2)),
        (3, (0, 3)), (3, (1, 3)), (3, (0, 1, 3))]
assert [native(i, A) for i, A in CAPS] == [-R(1, 100)]*3+[-7, -1, -5]
assert all(native(i, A) >= -R(1, 100)
           for i in (0, 1) for A in COAL if i in A)
assert [native(i, I) for i in I] == [1, R(27, 25), 1, 1]
for i in I:
    opponents = [j for j in I if j != i]
    derived = 0
    for bits in product((0, 1), repeat=3):
        A = [j for j, bit in zip(opponents, bits) if bit]
        probability = s.prod(q[j] if bit else 1-q[j]
                             for j, bit in zip(opponents, bits))
        derived += probability*joining(i, A)
    assert s.expand(derived-F[i]) == 0


def rows(child, outsider):
    out = {}
    for A in COAL:
        if set(A) <= set(child):
            out['F', A] = ([-native(i, A) for i in child], -native(outsider, A))
            out['J', A] = ([joining(i, A) for i in child], joining(outsider, A))
    return out


BLOCKERS = [
    ((0,), 1, [('F', (0,), 1)]), ((1,), 0, [('F', (1,), 1)]),
    ((2,), 0, [('F', (2,), 1)]), ((3,), 2, [('F', (3,), 1)]),
    ((0, 1), 2, [('J', (0, 1), 1)]),
    ((0, 2), 1, [('F', (0,), 1)]), ((0, 3), 2, [('F', (3,), 1)]),
    ((1, 2), 0, [('F', (1,), 1)]), ((1, 3), 0, [('F', (1,), 1)]),
    ((2, 3), 0, [('F', (2,), 1)]),
    ((0, 1, 2), 3, [('F', (0,), 299), ('J', (0, 2), 100)]),
    ((0, 1, 3), 2, [('F', (3,), 1)]),
    ((0, 2, 3), 1, [('F', (0,), 7), ('F', (2,), 6), ('F', (3,), 4)]),
    ((1, 2, 3), 0, [('F', (1,), 1)])]
assert {C for C, _, _ in BLOCKERS} == {C for C in COAL if len(C) < 4}
BLOCKER_VALUES = []
for C, o, terms in BLOCKERS:
    rr = rows(C, o)
    coeff = [sum(w*rr[k, A][0][j] for k, A, w in terms) for j in range(len(C))]
    rhs = sum(w*rr[k, A][1] for k, A, w in terms)
    assert all(w > 0 for _, _, w in terms)
    assert max(coeff) <= 0 and rhs > 0
    BLOCKER_VALUES.append((C, o, coeff, rhs))

# A strictly positive grand participant vector defeats ProductLow at allQuit
# and every nonzero nonnegative weighted upper certificate.
assert min(native(i, I) for i in I) > 0
ledger_dual = [(3, (0,)), (3, (1,)), (1, (0, 1)), (JJ, (1, 3))]
assert [sum(w*native(i, A) for w, A in ledger_dual) for i in I] == [
    -R(149, 10), -R(269, 10)-JJ/100, -4, -9]
floor_dual = [(401, (2,)), (1, (3,))]
assert [sum(w*native(i, set(A) | {i}) for w, A in floor_dual) for i in I] == [
    -R(1, 100), -R(402, 100), -1, -401]
assert all(any(native(i, A) < 0 for A in COAL if i in A) for i in I)
assert joining(0, [1, 2, 3]) == 1

traps = [A for A in COAL if all(any(i in B and set(B) <= set(A)
         and native(i, B) > 0 for B in COAL) for i in A)]
assert traps == [(0, 1), I]
assert s.expand(joining(2, [0, 1])+joining(3, [0, 1])) == R(1999, 100)-JJ
assert joining(0, [2]) == R(199, 100)
assert joining(0, [1, 2]) == -R(2791, 100)

# Exhaust all24 role assignments of the old three-passive-pole raw guards.
passing = []
pole_details = []
for i, j, k, l in permutations(I):
    a, b = joining(i, [l]), joining(i, [k, l])
    if not (a > 0 and b < 0):
        continue
    c = a/(a-b)
    a2, b2 = joining(k, [l]), joining(k, [i, l])
    l0 = (1-c)*joining(j, [l])+c*joining(j, [k, l])
    l1 = (1-c)*joining(j, [i, l])+c*joining(j, [i, k, l])
    f0 = c*((1-c)*reward(l, [l])+c*reward(l, [k, l])-reward(l, [k]))
    f1 = (1-c)*joining(l, [i])+c*joining(l, [i, k])
    flags = [a2 < 0, b2 < 0, l0 < 0, l1 < 0, f0 > 0, f1 < 0]
    pole_details.append(((i, j, k, l), c, (a2, b2, l0, l1, f0, f1), flags))
    if all(flags):
        passing.append((i, j, k, l))
assert passing == []

if __name__ == '__main__':
    print('PASS: full60, literal joining polynomials, six caps and punishment floors.')
    print('PASS: all14 quiet-child Farkas obstructions and global weight duals.')
    print('PASS: no passive-pole role permutation passes all strict guards.')
    print('Premium traps:', traps)
    print('Pole roles passing the first two guards:', pole_details)
    print('Quiet-child rows:', BLOCKER_VALUES)


# Actual-punishment owner floors at every complementary Nash root.
POINTS = [(1, R(167, 1000), R(910, 3601), 0),
          (R(67, 900), 1, R(510, 3301), 0),
          (1, 0, 1, 0),
          (1, R(301, 3000), R(509, 3601), 1)]
EXCESS_LOWER = []
for owner, point in enumerate(POINTS):
    differences = F.subs(dict(zip(q, point)))
    for i in I:
        if i == owner:
            continue
        if point[i] == 0:
            assert differences[i] <= 0
        elif point[i] == 1:
            assert differences[i] >= 0
        else:
            assert 0 < point[i] < 1 and differences[i] == 0
    assert differences[owner] < 0
    h = s.prod(1-point[i] for i in I if i != owner)
    if owner in (0, 1):
        # Immediate Quit gives original punishment >= own - 1/100.
        lower = -differences[owner]-R(1, 100)
        assert -differences[owner]-h*R(1, 100) >= lower > 0
    else:
        assert h == 0
        lower = -differences[owner]
    EXCESS_LOWER.append(lower)
assert EXCESS_LOWER[:2] == [R(311591, 2770000), R(17413613, 29709000)]
assert EXCESS_LOWER[2] == R(501, 100)
assert EXCESS_LOWER[3] > 1
print("PASS: all60 reward reconstruction and exact endpoint polynomials")
print("PASS: six strict caps, grand positivity and actual punishment lower bounds")
print("PASS: every displayed complementary root and four strictly positive owner floors")

# Immutable singleton/phase comparisons, distinguished from source conditions.
assert traps == [(0, 1), I]
assert [G.extract(T,T).det() for T in combinations(I,3)] == [-114,39,69,2]
assert all(G.extract(T,T).det() != 0 for n in (2,3,4) for T in combinations(I,n))
assert all(any(G[i,j] < 0 for i in I) for j in I)
assert list(G.inv()[:,0]) == [R(2,133),-R(59,133),R(27,133),-R(36,133)]
assert [T for T in combinations(I,3) if min(G.extract(T,T).inv()) >= 0] == [(0,2,3)]
assert list(G.extract([1],[0,2,3])*G.extract([0,2,3],[0,2,3]).inv()) == [
    R(59,69),-R(11,23),R(76,69)]
lcp = []
for size in (2,3,4):
    for T in combinations(I,size):
        xvec=s.zeros(4,1)
        for i,value in zip(T,G.extract(T,T).inv()*s.ones(size,1)):
            xvec[i]=value
        residual=G*xvec-s.ones(4,1)
        if min(xvec)>=0 and min(residual)>=0:
            lcp.append((T,list(xvec),list(residual),G.extract(T,T).det()))
assert lcp == [((0,2,3),[R(16,23),0,R(17,23),R(19,23)],
               [0,R(11,23),0,0],69)]
negative_pairs=[(i,j) for i,j in combinations(I,2) if G[i,j]<0 and G[j,i]<0]
positive_pairs=[(i,j) for i,j in combinations(I,2) if G[i,j]>0 and G[j,i]>0]
assert negative_pairs == [(0,1)] and positive_pairs == [(1,2),(1,3)]
assert not any(all(G[P[(j+1)%4],P[j]]<0 for j in I) for P in permutations(I))
assert joining(3,[2]) == -8  # scheduled pair23 in partition01|23
assert joining(2,[0]) == -R(501,100)  # scheduled pair02 in02|13
assert joining(3,[0]) == -1  # scheduled pair03 in03|12
assert joining(0,[1]) > 0 and joining(0,[1,2]) < 0
Pi0=Pi1=R(1,10)
Ahat=R(24,1)/(9+Pi1)-R(9,5)
MM=((10+Pi1)*3+10*(5+Pi0))/45
assert Ahat == R(381,455) and MM == R(271,150)
assert min(R(9,5)/(4*MM),Ahat*45/24) == R(135,542)
print('PASS: strict raw admission, all matrix supports and raw phase selections.')


"""Exact identities for an attached-triangle actual-source reduction.

Run with Python and SymPy. No numerical Q or equilibrium inference.
"""
import sympy as s
a,b,c,d,e,f,g,k,l,n=s.symbols('a b c d e f g k l n',positive=True)
h,m=s.symbols('h m',real=True)
G=s.Matrix([[0,-a,-b,c],[-d,0,e,f],[g,h,0,-k],[-l,m,n,0]])
B=G.extract([0,2,3],[0,2,3]);Delta=c*g*n-b*k*l
assert s.expand(B.det()-Delta)==0
assert all(x.is_positive for x in B.adjugate())
N=G.extract([1],[0,2,3])*B.adjugate()
assert N==s.Matrix([[-d*k*n+e*k*l+f*g*n,b*f*l-c*d*n+c*e*l,-b*d*k+b*f*g+c*e*g]])
assert s.simplify(N[0]-k/c*N[1]-f*Delta/c)==0
assert s.simplify(N[2]-b*k/(c*n)*N[1]-Delta*(b*f+c*e)/(c*n))==0
A=l*f/d-m*c/a;H=n-l*e/d-m*b/a;u=c*H-b*A;w=f*H+e*A
T=g*e/d-h*b/a
assert s.factor(g*f/d+h*c/a-k+T*A/H-G.det()/(a*d*H)) == 0
adjcol=s.Matrix([a*w,d*u,a*d*A,a*d*H])
assert (G.adjugate()[:,2]-adjcol).applyfunc(s.simplify)==s.zeros(4,1)
r=s.Matrix([w/(d*H),u/(a*H),A/H,1])
assert (G*r-s.Matrix([0,0,G.det()/(a*d*H),0])).applyfunc(s.simplify)==s.zeros(4,1)
control=s.Matrix([[0,-5,-2,3],[-9,0,6,4],[5,0,0,-3],[-6,0,7,0]])
assert control.det()==295
assert control.inv()[:,2]==s.Matrix([s.Rational(28,59),s.Rational(33,295),s.Rational(24,59),s.Rational(27,59)])
print('PASS: all adjugate, child-row, column, and primitive identities; h=m=0 exact boundary.')

# Exact complementary-boundary tests, independent of the coverage ray.
GG = s.Matrix([[0,-5,-2,3],[-9,0,6,4],[5,2,0,-3],[-6,3,7,0]])
def check_policy(zz, yy, XX, WW, p0, p1, KK, J3):
    den = (1+XX)*(1+WW)
    eta = (1-yy)*(1-zz)
    PP = 5*XX+2*WW+KK*XX*WW
    VV = s.factor((PP-(1-yy)*3*zz)/(den-eta))
    D2 = s.factor((1-zz)*VV-3*zz)
    assert (p0+5)*WW-eta*p0*WW/(1+WW) == 3*zz*(1-yy)-2*yy
    assert (p1+9)*XX-eta*p1*XX/(1+XX) == 4*zz*(1-yy)+6*yy
    assert 6*XX-3*WW-J3*XX*WW-7*yy == 0
    assert D2 >= 0 and yy*D2 == 0
    xx, ww = XX/(1+XX), WW/(1+WW)
    UU = s.Matrix([p0*ww,p1*xx,VV,0])
    own = s.Matrix([2,-3,5,-7])
    def nz(i, S):
        S = tuple(sorted(set(S)))
        if not S:
            return s.S.Zero
        if len(S) == 1:
            return GG[i,S[0]]
        if S == (0,1):
            return (p0,p1,KK,J3)[i]
        if (i,S) in CAPS:
            return -s.S.One
        return s.Integer(9)
    def ep(i, hz, original=False):
        others = [j for j in I if j != i]
        Q = B = 0
        H = s.prod(1-hz[j] for j in others)
        for bits in product((0,1),repeat=3):
            S = [j for j,bit in zip(others,bits) if bit]
            prob = s.prod(hz[j] if bit else 1-hz[j] for j,bit in zip(others,bits))
            Q += prob*(nz(i,S+[i])+(own[i] if original else 0))
            if S:
                B += prob*(nz(i,S)+(own[i] if original else 0))
        return s.factor(Q),s.factor(B),H
    def pieces(total, count):
        return [total/(count-(count-1-j)*total) for j in range(count)] if total else []
    for count in (1,2,7):
        hz = [[xx,ww,0,0]]
        micro = []
        for mover,total in ((2,yy),(3,zz)):
            for t in pieces(total,count):
                row = [0]*4
                row[mover] = t
                hz.append(row)
                micro.append(t)
        delta = max(micro)
        CC = max([0]+[nz(i,[i,j]) for i in I for j in I if i != j])
        for original in (False,True):
            target = UU+(own if original else s.zeros(4,1))
            for i in I:
                prescribed_sum = 0
                live = 1
                B = 0
                H = 1
                deadlines = []
                for row in hz:
                    Q0,B0,H0 = ep(i,row,original)
                    deadlines.append(s.factor(B+H*Q0))
                    B += H*B0
                    H *= H0
                    prescribed_sum += live*(row[i]*Q0+(1-row[i])*B0)
                    live *= (1-row[i])*H0
                assert 0 <= H < 1 and 0 <= live < 1
                assert s.factor(prescribed_sum/(1-live)-target[i]) == 0
                never = s.factor(B/(1-H))
                best = max(deadlines+[never])
                assert best-target[i] <= CC*delta
    return VV,D2

assert check_policy(R(1,2),0,R(1,10),R(1,10),R(55,3),R(121,6),300,30) == (R(220,71),R(7,142))
Vboundary, Dboundary = check_policy(R(1,100),0,R(1,225),R(3,500),0,0,-25,325)
assert Dboundary > 0
Xtest,Wtest = R(17,225),R(37,1000)
Ktest = s.factor(((1+Xtest)*(1+Wtest)/3-5*Xtest-2*Wtest)/(Xtest*Wtest))
assert check_policy(R(1,10),R(1,20),Xtest,Wtest,0,0,Ktest,-R(1725,629)) == (R(1,3),0)
print('PASS: boundary/interior exact policies, every periodic deadline and Never, signed own levels, refinements1,2,7.')
```
