# Both joint premiums arbitrary in a four-player quitting class

## 1. Complete original-game theorem

Consider a four-player quitting game with finite absorbing rewards r(S)
for every nonempty quitting coalition S. Live dates and literal Never
pay zero. Players randomize independently and deviations are arbitrary
complete behavioral strategies. Put s_i=r_i({i}) and
Z_i(S)=r_i(S)-s_i for NONEMPTY S only. The original own levels s_i may
have any sign. After relabeling, suppose the literal singleton-difference
matrix is

    G=[ 0  -a  -b   c ]
      [-d   0   e   f ]
      [ g   h   0  -k ]
      [-l   m   n   0 ],

where a,b,c,d,e,f,g,k,l,n>0 and h,m>=0. Define

    Delta=cgn-bkl, E=ec+fb,
    Dmax=gl E^2/(g c^2 e n+f b^2 k l).

Assume Delta>0 and d<=Dmax. Let the joint native pair be
Z(01)=(Pi0,Pi1,K,J), with ALL FOUR coordinates arbitrary real numbers.
Impose only the following twelve participant caps:

    Z2(02),Z2(12),Z2(012)<=0,
    Z3(03),Z3(13),Z3(013)<=0,
    Z0(02),Z1(12),Z3(23)<=0,
    Z0(03),Z1(13),Z2(23)<=0.                       (C)

Every other higher-coalition reward is arbitrary and every original own
singleton level can have either sign. Then the original four-player
quitting game has a uniform-equilibrium payoff. No Q, degree, generic
principal-minor or supplied-strategy premise is present in this raw claim.

The conclusion is UE, rather than a common strategy representation for
all branches. The main joint and cyclic-child branches produce exact
terminal Nash profiles with at most three dates per period; the deep
negative Pi0 branch uses the existing singleton-base punishment consumer.
A source alternative can also supply an existing cyclic-child UE directly.
All of these cases keep the actual original live and Never payoffs zero.

The theorem covers open regions in all sixty original reward coordinates,
including both Pi0 and Pi1 negative. It is ordinary mathematics, not a
newly checked Lean result. Removing the twelve caps or the displayed
singleton cone, and the complete Fin4 conjecture, remain open.

## 2. Same-table source reduction with no principal-minor guards

This section proves the needed alternative, including singular proper
principals and arbitrary signs of h,m. Standard Q means every offset has
a nonnegative complementary solution. R0 means that the only nonnegative
homogeneous complementary vector is zero. The degree is the standard
complementary-map degree.

### 2.1 A complete matrix alternative

Suppose G is standard Q, R0, and has degree one. Let B=G_023. Then either
B inverse is strictly positive and G_1,023 B inverse is nonnegative, or
det G>0 and G inverse e2 is strictly positive in all four coordinates.

To prove this, put

    Delta=det B=cgn-bkl,
    (N0,N2,N3)=G_1,023 adj(B),
    N0=-dkn+ekl+fgn,
    N2=bfl-cdn+cel,
    N3=-bdk+bfg+ceg.

Every entry of adj(B) is strictly positive. Direct calculation gives

    N0=(k/c)N2+f Delta/c,
    N3=(bk/(cn))N2+Delta(bf+ce)/(cn).              (A)

Thus Delta>0 and N2>=0 imply the first alternative. Assume it fails, so
either Delta<=0 or N2<0. Fix positive y0,y1,y3 in a compact box and let
y2=Y tend to infinity. A complementary solution at offset -y, with
support T, satisfies G_TT x_T=y_T and G_(I\T),T x_T>=y_(I\T).

All proper supports containing2 are exhausted as follows. Singletons,
and the opposite-sign pairs02,23, cannot map to a strictly positive
active vector. Pair12 is excluded by exterior row0, -a*x1-b*x2<0.
Triple012 is excluded by that same negative active row. On triple123,
active row1 is e*x2+f*x3=y1, bounding x2,x3; exterior row0 then bounds
x1 through -a*x1-b*x2+c*x3>=y0. This uses neither h nor m, so row2 cannot
equal unbounded Y. On triple023, Delta<0 makes its inverse strictly
negative. If Delta=0 a strictly positive row of adj(B) is a left null
vector and excludes Bx=y_023>>0. If Delta>0, failure of the first
alternative forces N2<0 by (A), and exterior row1 equals
(N0*y0+N2*Y+N3*y3)/Delta<y1 for large Y. All these exclusions are uniform
over the chosen compact box.

For supports omitting2, suppose feasible solutions existed along Y->infinity.
Their norms diverge because row2 must be at least Y. Normalize by their
sum norm and pass to a subsequence with a fixed support. The limit v has
v>=0, sum v=1, and v2=0. All entries of Gv are nonnegative: bounded
offsets disappear, and row2 remains nonnegative. On every positive
coordinate of v the active complementary equality gives (Gv)_i=0.
Hence v is a nonzero homogeneous complementary vector, contrary to R0.
The same compactness argument is uniform over the three bounded offset
coordinates. No nonsingularity of a proper principal is assumed here.

Therefore every solution at all sufficiently large Y has full support.
Q supplies such a solution for every y in an open set, so G is invertible.
The full solution G inverse*y is strictly positive. Dividing by Y and
letting Y increase yields v=G inverse e2>=0. At any such offset the entire
solution set is one full positive vector; there are no inactive rows,
and its active Jacobian G is nonsingular. The finite degree formula gives
degree(G)=sign(det G), so det G>0. The exact available declaration is
`exists_finset_r0Degree_eq_sum_sign_det`
(`MathUE/LinearProgramming/R0DegreeSum.lean`); this use imposes no
conditions on unrealized proper supports.

If v2=0, Gv=e2 would make v a nonzero homogeneous complementary vector,
again contradicting R0. Thus v2>0. Row0 gives c*v3=a*v1+b*v2>0, hence
v3>0; row1 gives d*v0=e*v2+f*v3>0, hence v0>0. If v1=0, the positive
core v_023 would solve B*v_023=e2_023. The negative inverse or positive
left-null-vector arguments exclude Delta<=0. Hence Delta>0, and exterior
row1 zero gives N2=0. Identities (A) then give N0,N3>0 and the first
alternative, a contradiction. Therefore v1>0 too.

### 2.2 Same-table no-UE premises and their exact consumer

Suppose the original four-player table lacks UE. The same-table declarations
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`)
and `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`)
give full standard Q and no nonzero homogeneous complementary vector.
The equivalence `isR0Matrix_iff_not_singletonLCPFeasible`
(`MathUE/LinearProgramming/CopositiveQ.lean`) identifies the latter with
R0. The declaration `singleton_r0Degree_eq_one_of_no_uniformPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`)
gives degree one for this same literal singleton matrix.

The first alternative above supplies original UE by
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`).
It is therefore excluded under the no-UE assumption. In the second
alternative, direct cofactors give

    adj(G)e2=(a*v,d*u,ad*A,ad*H).

Strict positivity of G inverse e2 and det G>0 force

    A=lf/d-mc/a>0, H=n-le/d-mb/a>0,
    u=cH-bA>0, v=fH+eA>0, det G>0.                 (N)

These are the numerical guards used below. No auxiliary translated game
was assumed to lack equilibrium; only terminal payoffs along surely
absorbing opponent clocks are translated in the actual consumer.

## 3. Every sufficiently negative first premium has a direct exit

Suppose Pi0<=-a and h,m>=0. Have player1 quit surely and every other
player Continue at the initial root. Each outsider's Continue-minus-Quit
comparison is respectively

    -a-Pi0>=0, h-Z2(12)>=0, m-Z3(13)>=0.

These follow from the literal pair rewards and caps, with no numerical
matrix guards or restrictions on K,J or Pi1. The designated owner's
pure Continue comparison is handled at its ACTUAL behavioral punishment
level, not a supplied favorable tail.

Indeed an abnormal player has own singleton reward strictly below its
punishment value, and that value is at most every other singleton reward,
by `abnormal_singletonFloor_chain`
(`UniformEquilibrium/Quitting/Classification/AbnormalSingletonConsequences.lean`).
For player1, Gamma_10=-d<0 contradicts that chain. Thus its actual
punishment value is at most its own singleton level, regardless of the
sign of that level. At the displayed root the owner floor excess is
exactly punishment1-s1<=0, because all opponents Continue.

Take the free set empty in
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` and use
`quittingSingletonBaseOwnerFloorExcess_nonpos_iff`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`).
The empty induced game is trivially Nash, the three joins have just been
checked, and the actual owner floor is nonpositive. This produces the
complete behavioral certificate. Its exact fixed-target compiler is
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`).
The target is the original singleton1 reward vector. This is a direct
existing exit, including the required off-path punishment consumer; the
unpunished pure stationary root alone was not asserted to be equilibrium.

## 4. Exact coarse cyclic child with a possibly negative observer

Use the literal singleton differences on core C={0,2,3}

    B=[0,-b,c; g,0,-k; -l,n,0],

where b,c,g,k,l,n>0 and Delta=cgn-bkl>0. The outside player1 has row
(-d,e,f), where d,e,f>0. Put

    N0=-dkn+ekl+fgn,
    N2=bfl-cdn+cel,
    N3=-bdk+bfg+ceg.

These are precisely the coordinates of (-d,e,f)adj(B), in core order
(0,2,3). No sign of any N coordinate is assumed. The own singleton
levels may be arbitrary signed reals; Z_i(S)=r_i(S)-r_i({i}) is defined
on nonempty coalitions only.

Prescribe the chronological three-date cycle solo0, solo2, solo3 with

    x=Delta/[g(c(l+n)+bl)],
    y=Delta/[n(g(b+c)+bk)],
    z=Delta/[c(gn+k(l+n))].                         (1)

All rates lie strictly between zero and one. Their survival product is
bkl/(cgn)<1. The core values at the starts of its three dates are

    U_C=(0,gx,0), V_C=(0,0,ny), W_C=(cz,0,0).       (2)

Indeed x*l=(1-x)n*y, y*b=(1-y)c*z, and
z*k=(1-z)g*x. These identities give all three core Bellman equations,
and every active owner's value is zero both before and after its date.
Every core prescribed value is nonnegative.

The observer's actual values are obtained by the same linear passive
relation at every date,

    U1=(N2/Delta)g*x,
    V1=(N3/Delta)n*y,
    W1=(N0/Delta)c*z.                              (3)

To justify that these are actual values, the row L=(-d,e,f)B inverse
satisfies L B=(-d,e,f). Applying L to each core Bellman equation gives
the exact observer Bellman equation. The common full-period survival
is strictly below one, so the unique periodic Bellman solution is the
actual expected terminal payoff. Nonnegative L is not required.

### 4.1. Complete exact coarse deviation conditions

Assume every participant pair coordinate inside the core is nonpositive:

    Z0(02),Z0(03),Z2(02),Z2(23),Z3(03),Z3(23)<=0.

At each coarse solo date the mover is indifferent at zero; the other
core players have nonnegative prescribed values and nonpositive forced
Quit values. For the outside player, the exact three inequalities are

    Z1(01)<=g*N2/Delta,
    Z1(12)<=n*N3/Delta,
    Z1(13)<=c*N0/Delta.                            (4)

These compare its forced Quit payoffs xZ1(01), yZ1(12), zZ1(13) directly
with (3). They remain valid when one or several of the observer's
prescribed values are negative. Thus all actual pure action endpoints
at every date are capped by the prescribed continuation vector.

Every player faces at least two core opponents with positive periodic
hazards (or all three if it is the observer). Deleted-opponent survival
therefore contracts geometrically, uniformly over the player's complete
behavioral replacement. Finite-deadline backward induction and its
vanishing survival remainder prove exact terminal Nash against every
behavioral law, including Never. All such laws absorb surely, so the
original signed own levels can be added to terminal values without
changing live or Never rewards. The common geometric opponent tail
then gives the same fixed original target at every sufficiently long
finite horizon. All triple and grand coalition rewards are arbitrary:
only pairs can be reached under one unilateral deviation from this
three-solo profile.

This is a complete raw sufficient class, not a general quiet-child
extension theorem. Condition (4) is a collision-price condition specific
to the produced finite hazards; it replaces an all-date nonnegative
observer-floor condition by literal exact coarse date comparisons.

## 5. The singleton cone joins the two strategy branches

Assume Pi0>-a and, for contradiction, that the table has no UE. The
same-table singleton consequences give standard Q, R0 and degree one.
Section2 then gives either an existing
nonnegative-inverse child exit, already a contradiction, or

    A=lf/d-mc/a>0,
    H=n-le/d-mb/a>0,
    u=cH-bA=cn-l(ec+fb)/d>0,
    v=fH+eA>0, det G>0.                           (N)

In particular N2=bfl-cdn+cel=-du<0. Put

    theta=g*N2/Delta=-dgu/Delta,
    C=dfb/E.

The exact identity

    theta+C=[gl E^2-d(g c^2 e n+f b^2 k l)]/(E Delta)

shows theta>=-C. Since E>fb, C<d, so theta>-d. Also the two observer
numerators from Section4 are strictly positive. Indeed both N0 and N3
decrease with d, and at d=Dmax their values are

    N0=ef Delta^2/(g c^2 e n+f b^2 k l)>0,
    N3=ceg E Delta/(g c^2 e n+f b^2 k l)>0.        (15)

If Pi1<=theta, the coarse child in Section4 applies: its first
observer cap is exactly Pi1<=theta, and its other two observer bounds
are strictly positive by (15), whereas (C) gives nonpositive literal
pair rewards. This proves UE for every such Pi1, including values below
-d. It remains to consider Pi1>theta, which implies Pi1>-d and Pi1>-C.

## 6. A planar winding argument produces the joint root

The following elementary lemma does not require isolated zeros,
nondegenerate roots or a globally selected zero branch.

**Boundary lemma.** Let F,R be continuous on the rectangle
[zL,zR] times [0,1], where the second coordinate is called s. Suppose
F>0 on the left edge, F<0 on the right edge, R(zL,0)>0,
R(zL,1)<0, and on the top edge every zero of R has F<0. Then either
there is a zero F=R=0 with 0<s<1 and zL<z<zR, or there is a bottom
point s=0 with zL<z<zR, R=0 and F>=0.

Proof. If neither conclusion holds, (F,R) never vanishes on the whole
rectangle. On the top, right and bottom edges it avoids the nonnegative
horizontal ray: a zero of R there must have F<0. On the left edge F>0,
and at its bottom and top endpoints R is respectively positive and
negative. Traverse the boundary from the lower-left corner upward, then
along the other three edges back. Along the left edge choose the angle
in (-pi/2,pi/2), with initial angle alpha_b>0 and final alpha_t<0.
Along the remaining three edges the image avoids the positive ray, so
its continuous angle in (0,2pi) starts at 2pi+alpha_t and ends at
alpha_b. The total change of argument is -2pi. A continuous nonvanishing
map on the rectangle has boundary winding zero, by contracting the
boundary to an interior point. This contradiction proves the lemma.
The signs on the left/right edges also exclude their corners from the
accepted bottom alternative.

Apply this to the scalar inverses for the actual joint producer,
allowing both premiums negative. For 0<z<1, 0<=y<=ymax=cz/(b+cz),
put eta=(1-y)(1-z) and define W>=0,X>0 uniquely by

    (a+Pi0)W-eta Pi0 W/(1+W)=cz(1-y)-by,
    (d+Pi1)X-eta Pi1 X/(1+X)=fz(1-y)+ey.          (16)

Their derivatives are at least min(a,a+Pi0)>0 and
min(d,d+Pi1)>0. Both left sides start at zero and tend to infinity,
so the inverses exist and are continuous. They obey uniform bounds
W<=c/min(a,a+Pi0) and X<=(f+e)/min(d,d+Pi1). The first is zero exactly
on the top edge. Define

    den=(1+X)(1+W), P=gX+hW+KXW,
    B=P/den, V0=kz/(1-z),
    R=lX-mW-JXW-ny,
    T=ge/d-hb/a, F=B-V0+(T/H)R.                   (17)

Uniformly in the strip as z tends to zero, y,X,W=O(z), eta=1+O(z),
and the linear terms are independent of either premium:

    aW=cz-by+O(z^2), dX=fz+ey+O(z^2),
    R=Az-Hy+O(z^2),
    F=[det G/(adH)]z+O(z^2).

The last identity uses det G=agv+dhu-kadH. Thus F>0 on a sufficiently
small left face z=zL, R>0 at its bottom y=0, and R<0 at its top:
there the leading coefficient is A-Hc/b=-u/b<0. As z tends to one,
B and R are bounded while V0 diverges; therefore F<0 on a sufficiently
large right face z=zR. It remains only to check the top zeros of R.

At the top, W=0 and y=cz/(b+cz). If R=0, then

    X=ncz/[l(b+cz)].                              (18)

Solving the second scalar identity (16) for Pi1 gives

    Pi1(z)=-D[lb+c(l+n)z]/[z(lb+c(l+n))],
    D=du/(cn)>0.                                 (19)

This function is strictly increasing on (0,1). At a top zero, F is
exactly gX/(1+X)-kz/(1-z). Its numerator after multiplication by
positive denominators is

    z[Delta-c(gn+k(l+n))z],

using denominator (1-z)[bl+c(l+n)z], so its unique positive zero is

    zstar=Delta/[c(gn+k(l+n))],

and it is negative for z>zstar. Direct substitution in (19) gives
Pi1(zstar)=theta. Since the actual Pi1>theta, every top zero has
z>zstar and hence F<0. This is the necessary top-boundary condition;
R itself need not remain negative there.

Normalize y=s*ymax(z) and apply the boundary lemma. It produces

    X,W>0, 0<z<1, 0<=y<ymax,
    R=0, y>0 => B=V0, y=0 => B>=V0.               (20)

The strict top exclusion also makes W>0. This is the exact complementarity
needed for the joint01/solo2/solo3 construction, even when both original
joint premiums are negative.

## 7. Exact coarse comparisons, complete caps and signed rewards


This is the extra cap comparison which cannot be inferred from solving
the scalar equations alone. Write x=X/(1+X), w=W/(1+W) and

    V=[P-(1-y)kz]/[den-(1-y)(1-z)],
    D2=(1-z)V-kz.

Equation (20) gives V>=V0>0, D2>=0 and yD2=0. The exact three value
vectors are

    U=(Pi0*w,Pi1*x,V,0),
    U2=((Pi0+a)W,(Pi1+d)X,(1-y)D2,ny),
    U3=((1-z)Pi0*w+cz,(1-z)Pi1*x+fz,D2,0).       (21)

Every coordinate of U2 is nonnegative; its first two are positive.
Moreover U3_0=(U2_0+by)/(1-y)>0 by its Bellman identity. The only
remaining sign needed for the twelve coarse caps is U3_1>=0.

For Pi1>=0 this is immediate. Otherwise set t=-Pi1 with 0<t<d and
assume U3_1<0. The identity U2_1=(1-y)U3_1+ey=(d-t)X implies y>0 and
X<ey/(d-t). Combining this with
U3_1=fz-t(1-z)X/(1+X)<0 gives

    t > fz(d+ey)/[ey(1-z)+fz].                    (22)

For z>=d/(d+f), the right side is at least d, impossible. For smaller
z it decreases as y increases, so y<=cz/(b+cz) implies

    t > Cfun(z),
    Cfun(z)=f[db+c(d+e)z]/[ec+fb+c(f-e)z].        (23)

Its denominator is positive on [0,1], and

    Cfun'(z)=cef(bd+bf+cd+ce)/[ec+fb+c(f-e)z]^2>0.

Thus Cfun(z)>Cfun(0)=dfb/(ec+fb)=C. But Pi1>theta>=-C gives t<C,
a contradiction. This proves the required solo3 observer sign.

At the joint date owners0,1 are exactly indifferent with native values
Pi0*w,Pi1*x; these may both be negative. Owners2,3 have prescribed
values V>0 and zero, and their forced-Quit values are nonpositive by
the first six caps of (C). At solo2 all prescribed coordinates are
nonnegative, the mover's value is zero when y>0, and the three inactive
Quit endpoints are y times the corresponding nonpositive pair caps.
At solo3 the prescribed values have just been shown nonnegative, its
mover is indifferent at zero, and all inactive endpoints are again
nonpositive. If y=0 the unused solo2 date is omitted.

These are exact endpoint comparisons at the actual coarse dates. No
fine subdivisions or nonnegative-global-floor claim is used. In
particular the negative joint values U0,U1 cause no missing deviation
comparison. Owners0,1,3 have positive proper hazards, so every player
faces at least two positive opponent hazards each period. Deleted-opponent
survival contracts geometrically independently of the entire unilateral
law. Finite-deadline backward induction, followed by the vanishing
opponent-survival remainder, proves exact terminal Nash against every
behavioral deviation including Never. All such laws absorb almost surely,
so adding the signed original own levels is legitimate for terminal
values only. Splitting long finite-horizon averages at a fixed early
date gives the same fixed original target uniformly over every deviation.
This proves the original UE conclusion and completes the theorem in Section1.

## 8. Full sixty-coordinate admission and coverage calibration

Set all original own levels to one and use

    G=[0,-5,-2,3; -9,0,6,4; 5,2,0,-3; -6,3,7,0].

Define multilinear joining increments, independent of the recipient's own
coordinate, by

    F0=(1-q3)[(49/10)q1+(199/100)q2-(174/5)q1q2]
                           +q3[-301/100+(31/10)q2],
    F1=(1-q3)[(89/10)q0-(601/100)q2-(149/5)q0q2]-(401/100)q3,
    F2=-(501/100)q0-(201/100)q1+(3201/100)q0q1+2q3,
    F3=-q0-4q1-8q2.                                (F)

For empty sets put Z_i(empty)=0; for a singleton not containing i use
G_ij. The remaining passive coordinates are

| Recipient | Opponent pair values | Full-opponent value |
| --- | --- | --- |
| 0 | Z0(12)=28, Z0(13)=3, Z0(23)=0 | Z0(123)=0 |
| 1 | Z1(02)=27, Z1(03)=4, Z1(23)=4 | Z1(023)=5 |
| 2 | Z2(01)=-25, Z2(03)=3, Z2(13)=0 | Z2(013)=-2599/100 |
| 3 | Z3(01)=0, Z3(02)=2, Z3(12)=6 | Z3(012)=14 |

For a coalition containing i set Z_i(A+i)=Z_i(A)+F_i(1_A), and define
every original reward by r_i(S)=1+Z_i(S). This specifies all sixty
absorbing coordinates, with no unstated completion choices.

The joint pair is Z(01)=(-1/10,-1/10,-25,0). The twelve caps, in the
order (C), are

    (-1/100,-1/100,-1/100,-7,-1,-5,
     -1/100,-1/100,-1,-1/100,-1/100,-1).

They are all strict. The grand participant vector is
(9/100,99/100,1,1)>0. Here Delta=69, E=26 and
Dmax=3380/363>9=d. Thus the table lies in an open part of the new
class with BOTH joint participant premiums negative. Every earlier
nonnegative-two-participant or arbitrary-one-participant theorem fails
its remaining nonnegative-premium hypothesis on the only mutually
negative pair01, under both orders. The twelve caps and all other
reward data are literal; no unlisted completion is being selected.

### 8.1 Entire matrix-side and phase-side comparisons

All eleven nontrivial principal minors are nonzero, and every column
has a negative entry, so G is R0. The exhaustive offset-minus-one
complementarity census has exactly one solution,

    support023, x=(16/23,0,17/23,19/23),
    Gx-1=(0,11/23,0,0), det G_023=69>0.

Hence G has degree one and is standard Q, by
`r0Degree_eq_sum_admissible_inverse_supports`
(`MathUE/LinearProgramming/FiniteSupportDegree.lean`) and
`isStandardQ_of_r0Degree_ne_zero`
(`MathUE/LinearProgramming/R0Degree.lean`). It is not already dispatched
by the non-Q or homogeneous singleton-source exit.

Only triple023 has a nonnegative inverse. Its exterior inverse row is
(59/69,-11/23,76/69), so every passive-inverse child selection fails.
The full inverse is

    G^-1=[  2  45  62  -38 ]/133.
         [-59  69  33  -76 ]
         [ 27   9  39   19 ]
         [-36 121  81 -114 ]

The mixed first column defeats full inverse positivity and every-column
signability, under all relabelings. The mutually negative pair01 has
neither Q nor a nonzero homogeneous vector; therefore projective Q-bar
also fails. The equivalence used is
`isProjectiveQMatrix_iff_standard_or_homogeneous`
(`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`).

The sole mutually negative pair is01. The two mutually positive pairs12
and13 share a vertex. This excludes the reciprocal-opposition,
no-mutually-negative, favorite/matching, opposite-sign matching, and
negative-pair-funded classes under all relabelings. There is no directed
negative Hamiltonian cycle, so neither four-cycle eigenvalue adapter
applies. Cyclic-child joint classes have only candidate child023, but
its pivot1 column is(-5,2,3), failing the required allnegative signs.
For the two-pair joining-cap selectors, partitions01|23,02|13,03|12
have respectively negative scheduled joins -8,-501/100,-1. These are
literal finite raw-family failures, not a claim about every possible
supplied finite controller.

The single-column jackpot baseline DOES pass: inverse columns1 and2
are positive. Its unspecified finite large-pole threshold is not decided
for this isolated table. The new theorem instead quantifies over every
finite completion satisfying the caps; in particular it covers the whole
ray obtained by varying ONLY passive Z2(01)=K to minus infinity, with
all participant coordinates fixed. That ray is not the old asymptotic
guarantee, which requires a selected growing participant coordinate while
bounding the other data, or bounding them by a smaller power of the pole.
This is an explicitly family-level nonimplication, not finite-table
exclusion from an unknown threshold.

### 8.2 All quiet children, with explicit finite duals

For a child C and outsider o, the required nonnegative weights satisfy
for every nonempty S subset C

    F_S: sum_i w_i[-Z_i(S)]>=-Z_o(S),
    J_S: sum_i w_i[Z_i(S+i)-Z_i(S)]>=Z_o(S+o)-Z_o(S).

These are the literal fields of `CappedClockParentRewardCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`).

Each row below is a nonnegative combination of these necessary rows.
Its child coefficient vector is componentwise nonpositive and its right
side strictly positive, proving infeasibility for every nonnegative
weight choice. The child coordinates appear in increasing order.

| Child C | Outsider | Row combination | Coefficients | Right side |
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

Thus every complete quiet child fails for at least one outsider. This
already uses necessary finite coalition rows, so adjoining Never rows
cannot repair it. No claim that every individual child/outsider LP is
infeasible is needed.

### 8.3 Complete sure-owner correspondences and actual punishment floors

At a sure owner j, an opponent coordinate q_i=0 requires F_i<=0;
q_i=1 requires F_i>=0; an interior coordinate requires F_i=0. The entire
complementary Nash correspondences are the four singletons

| Sure owner | Unique complementary point |
| --- | --- |
| 0 | (1,167/1000,890/3581,0) |
| 1 | (67/900,1,490/3281,0) |
| 2 | (1,0,1,0) |
| 3 | (200/501,0,301/310,1) |

For any sure owner0,1,2, F3<0 forces q3=0. At owner0 the remaining
opponents' increments are F1=89/10-(3581/100)q2 and
F2=-501/100+30q1. Both thresholds are strictly interior and cross in
opposite directions, so no endpoint combination is a best response and
the displayed interior point is unique. At owner1 the analogous pair
is F0=49/10-(3281/100)q2 and F2=-201/100+27q0, with the same complete
endpoint exclusion. At owner2, F1=-601/100-(209/10)q0<0 forces q1=0;
then F0=199/100>0 forces q0=1.

At owner3, F1=-401/100 forces q1=0. The two remaining increments are
F0=-301/100+(31/10)q2 and F2=2-(501/100)q0. Their opposite crossing
again excludes all four boundary combinations and forces precisely the
listed mixed root. This is an exhaustive cube-face argument, including
every potentially singular or boundary face.

Every participant reward of owner0 is at least native -1/10; for owner1
it is at least -1/10; for owner3 it is at least -7. Immediate sure Quit
therefore gives actual punishment lower bounds 9/10,9/10,-6. For the
root of owner j let h_j=product_(i!=j)(1-q_i). Its literal owner floor
excess is -F_j+h_j(punishment_j-1). The following exact lower bounds are
strictly positive:

    owner0: 1233657/17905000,
    owner1: 7198967/14764500,
    owner2: 501/100,
    owner3: 249889/31062.

Owner2 has h2=0 because opponent0 is sure. For the other three owners
the displayed bounds use their actual punishment lower bounds and their
exact positive h_j, not an arbitrary continuation. Therefore every
sure-owner or persistent-base selector fails. Any smaller free-set
candidate satisfying outsider joins would belong to these full
complementary correspondences, so it is excluded too. The exact owner
floor definition and certificate interface are the declarations in
Section3. The original positive own levels also exclude the induced
owner Never alternative.

### 8.4 Remaining finite screens and their limits

The sole premium trap is the full set I: every proper subset has at least
one member with no positive participant premium inside that subset.
Grand positivity refutes product-low-premium and every nonzero
nonnegative weighted Quit upper average. The direct declaration is
`exists_uniformEquilibriumPayoff_of_productLowPremium`
(`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`).
The mixed trap charge alternative fails at penultimate row123 because
owner0's joining increment is9/100>0. Put k(S)_i=Z_i(S union{i}) and
h(S)=Z(S). The exact strictly negative vectors

    401k(2)+k(3)=(-201/50,-201/50,-1,-401),
    3h(0)+3h(1)+h(01)=(-151/10,-271/10,-4,-9)

exclude every nonzero nonnegative global forced-Quit floor weight and
every nonzero nonnegative proper-passive-ledger weight. Every owner has
a below-own participant pair, defeating globally protected-leaver tests.
Owner0 joining singleton1 gives49/10>0, whereas joining12 gives
-2791/100<0, violating the no-strict-background-reversal condition.

For completeness, the three-passive-pole finite guards in distinct roles
(i,j,k,l), with A=F_i(l), B=F_i(kl), c=A/(A-B), are

    A>0, B<0, F_k(l)<0, F_k(il)<0,
    (1-c)F_j(l)+cF_j(kl)<0,
    (1-c)F_j(il)+cF_j(ikl)<0,
    c[(1-c)r_l(l)+c*r_l(kl)-r_l(k)]>0,
    (1-c)F_l(i)+cF_l(ik)<0.

The embedded exact program reconstructs the literal rewards and checks
all twenty-four ordered role choices; none passes all eight guards.
This excludes their finite admission conditions without modifying or
guessing any asymptotic threshold.

These tests establish the stated finite-family separation, not that
every old conceivable supplied strategy fails, nor that the calibration
has no stationary equilibrium. In particular the single-column comparison
retains the distinct family-level scope in Section8.1.

## 9. Falsification stresses and a finite formalization target

For the same G, set Z(01)=(-1,-2227/1171,-13,1208/79) and every other
nonsingleton native reward to zero. The exact joint-cycle rates

    x=1/17, w=1/21, y=2/79, z=1/10

give the three values

    U=(-1/21,-131/1171,1/3,0),
    U2=(1/5,1039/2342,0,14/79),
    U3=(9/35,701/2342,0,0).

Both joint-owner values are negative, while the entire actual solo-start
vectors are nonnegative. Every literal pure-action endpoint passes, and
the full-period survival is1056/1343. The embedded program also checks
these comparisons after adding signed original own levels (-3,5,-7,2).

This stress distinguishes coarse play from fine refinements. At the last
microdate of solo3, with hazard t, player0's gain from quitting is
(1-64t)/21. The deviation follows the prescribed law beforehand and quits
at that date conditional on survival. Its reach probability in the first
period is at least1056/1343. For every refinement of mesh below1/128 its
total gain is at least1056/(1343*42). Thus the proof cannot replace its
actual coarse solo dates by an arbitrarily fine balanced-word compiler.

A separate child stress sets Z(01)=(2,-3,0,0) and every other
nonsingleton native reward to zero. The chronological solo0,solo2,solo3
rates are (23/85,69/217,23/74), with outside values
(-11/17,76/31,59/74). The first observer cap succeeds precisely because
-3<-55/23. All exact pure-action endpoints pass despite its initial
negative observer value. The program again checks arbitrary signed own
levels on this exact example. Neither stress is the finite-selector
separation table of Section8.

The finite formalization target is a raw-table UE producer accepting the
matrix signs, Delta>0,d<=Dmax, and twelve caps, with both Pi0 and Pi1 free.
Its new finite lemmas are the positive-ray boundary winding alternative,
the exact top-zero identity Pi1(zstar)=theta, and the solo3 nonnegativity
bound Pi1>=-dfb/(ec+fb). The coarse child and joint Bellman comparisons
feed an ordinary geometric opponent-tail terminal-to-uniform argument.
Section2 supplies the source guards without any proper-minor assumption;
Section3 invokes the existing actual-punishment singleton-base consumer.
No step translates live or Never rewards or identifies terminal and
finite-horizon equilibrium without the uniform tail bound.

The result removes both joint premium restrictions on this explicit
singleton cone. Removing the collision caps or the singleton cone, and
settling the full four-player quitting conjecture, remain open.

## Appendix. Reproducible exact checks

Save and run the following complete Python program with SymPy. It
reconstructs all sixty rewards and checks all listed finite coverage
certificates, entire sure-owner correspondence equations, actual
punishment lower bounds, matrix source comparisons, universal cone/top
identities, and two distinct exact coarse strategies. These calculations
support the stated formulas; the topological and unrestricted behavioral
proofs are given above.

```python
"""Exact complete-table checks for the both-arbitrary-premium class.

Save and run with Python and SymPy. No supplied root is needed by the theorem.
The rational coarse stresses at the end are separate Bellman sanity checks.
"""
from itertools import combinations, permutations, product
import sympy as s

R = s.Rational
I = tuple(range(4))
COAL = tuple(A for n in range(1, 5) for A in combinations(I, n))
G = s.Matrix([[0, -5, -2, 3], [-9, 0, 6, 4],
              [5, 2, 0, -3], [-6, 3, 7, 0]])
q = s.symbols('q0:4')
F = s.Matrix([
    (1-q[3])*(R(49,10)*q[1]+R(199,100)*q[2]-R(174,5)*q[1]*q[2])
      +q[3]*(-R(301,100)+R(31,10)*q[2]),
    (1-q[3])*(R(89,10)*q[0]-R(601,100)*q[2]-R(149,5)*q[0]*q[2])
      -R(401,100)*q[3],
    -R(501,100)*q[0]-R(201,100)*q[1]+R(3201,100)*q[0]*q[1]+2*q[3],
    -q[0]-4*q[1]-8*q[2]])
PASSIVE = {
    (0,(1,2)):28, (0,(1,3)):3, (0,(2,3)):0, (0,(1,2,3)):0,
    (1,(0,2)):27, (1,(0,3)):4, (1,(2,3)):4, (1,(0,2,3)):5,
    (2,(0,1)):-25, (2,(0,3)):3, (2,(1,3)):0,
    (2,(0,1,3)):-R(2599,100),
    (3,(0,1)):0, (3,(0,2)):2, (3,(1,2)):6, (3,(0,1,2)):14}


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



assert native(0,(0,1))==native(1,(0,1))==-R(1,10)
print('PASS direct full table: both joint premiums negative')
assert len({(i,A):native(i,A) for A in COAL for i in I})==60
CAPS=[(2,(0,2)),(2,(1,2)),(2,(0,1,2)),(3,(0,3)),(3,(1,3)),(3,(0,1,3)),
      (0,(0,2)),(1,(1,2)),(3,(2,3)),(0,(0,3)),(1,(1,3)),(2,(2,3))]
print('caps',[native(i,A) for i,A in CAPS])
assert max(native(i,A) for i,A in CAPS)<=0
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

for C,o,terms in BLOCKERS:
 rr=rows(C,o)
 coeff=[sum(w*rr[k,A][0][j] for k,A,w in terms) for j in range(len(C))]
 rhs=sum(w*rr[k,A][1] for k,A,w in terms)
 # Exact Farkas vector: all coefficients nonpositive, right side positive.
 assert max(coeff)<=0<rhs
passing=[]
for i,j,k,l in permutations(I):
 a,b=joining(i,[l]),joining(i,[k,l])
 if not a>0>b:continue
 c=a/(a-b)
 tests=[joining(k,[l])<0,joining(k,[i,l])<0,
 (1-c)*joining(j,[l])+c*joining(j,[k,l])<0,
 (1-c)*joining(j,[i,l])+c*joining(j,[i,k,l])<0,
 c*((1-c)*reward(l,[l])+c*reward(l,[k,l])-reward(l,[k]))>0,
 (1-c)*joining(l,[i])+c*joining(l,[i,k])<0]
 if all(tests):passing.append((i,j,k,l))
assert not passing
print('PASS all24 finite passive-pole role choices fail')
traps=[A for A in COAL if all(any(i in B and set(B)<=set(A) and native(i,B)>0 for B in COAL) for i in A)]
assert traps==[I]
print('traps',traps)
assert min(native(i,I) for i in I)>0
print('grand',[native(i,I) for i in I])
for dual,insert in [([(3,(0,)),(3,(1,)),(1,(0,1))],False), ([(401,(2,)),(1,(3,))],True)]:
 vec=[sum(w*native(i,set(A)|{i} if insert else A) for w,A in dual) for i in I]
 assert max(vec)<0
 print('dual',vec)
roots=[(1,R(167,1000),R(890,3581),0),(R(67,900),1,R(490,3281),0),
       (1,0,1,0),(R(200,501),0,R(301,310),1)]
for owner,root in enumerate(roots):
 diff=F.subs(dict(zip(q,root)))
 for i in I:
  if i!=owner:
   assert (root[i]==0 and diff[i]<=0) or(root[i]==1 and diff[i]>=0) or(0<root[i]<1 and diff[i]==0)
 floor=min(native(owner,A) for A in COAL if owner in A)
 h=s.prod(1-root[j] for j in I if j!=owner)
 margin=-diff[owner]+h*floor
 print('owner',owner,root,'F',diff[owner],'floor',floor,'h',h,'margin',margin)
 assert margin>0

# Exact exhaustive endpoint correspondence identities, not merely root tests.
assert F[3]==-q[0]-4*q[1]-8*q[2]
assert s.expand(F[0].subs(q[3],1)+R(301,100)-R(31,10)*q[2])==0
assert F[1].subs(q[3],1)==-R(401,100)
assert s.expand(F[2].subs({q[1]:0,q[3]:1})-2+R(501,100)*q[0])==0
assert s.expand(F[1].subs({q[0]:1,q[3]:0})-R(89,10)+R(3581,100)*q[2])==0
assert s.expand(F[2].subs({q[0]:1,q[3]:0})+R(501,100)-30*q[1])==0
assert s.expand(F[0].subs({q[1]:1,q[3]:0})-R(49,10)+R(3281,100)*q[2])==0
assert s.expand(F[2].subs({q[1]:1,q[3]:0})+R(201,100)-27*q[0])==0
# At fixed2, first3 is off, then1 is off, then0 is sure.
assert all(F[1].subs({q[0]:b,q[2]:1,q[3]:0})<0 for b in (0,1))
assert F[0].subs({q[1]:0,q[2]:1,q[3]:0})==R(199,100)>0
print('PASS exhaustive sure-owner crossing equations and actual punishment bounds')

# The same-table singleton source screens are complete over all supports.
assert G.det()==133
assert all(G.extract(T,T).det()!=0 for n in (2,3,4) for T in combinations(I,n))
assert all(any(G[i,j]<0 for i in I) for j in I)
lcp=[]
for size in (2,3,4):
 for T0 in combinations(I,size):
  xx=s.zeros(4,1)
  for i,value in zip(T0,G.extract(T0,T0).inv()*s.ones(size,1)):xx[i]=value
  residual=G*xx-s.ones(4,1)
  if min(xx)>=0 and min(residual)>=0:
   lcp.append((T0,list(xx),list(residual),G.extract(T0,T0).det()))
assert lcp==[((0,2,3),[R(16,23),0,R(17,23),R(19,23)],
             [0,R(11,23),0,0],69)]
assert [T0 for T0 in combinations(I,3) if min(G.extract(T0,T0).inv())>=0]==[(0,2,3)]
assert list(G.extract([1],[0,2,3])*G.extract([0,2,3],[0,2,3]).inv())==[
 R(59,69),-R(11,23),R(76,69)]
assert list(G.inv()[:,0])==[R(2,133),-R(59,133),R(27,133),-R(36,133)]
assert min(G.inv()[:,1])>0 and min(G.inv()[:,2])>0
assert [(i,j) for i,j in combinations(I,2) if G[i,j]<0 and G[j,i]<0]==[(0,1)]
assert [(i,j) for i,j in combinations(I,2) if G[i,j]>0 and G[j,i]>0]==[(1,2),(1,3)]
assert not any(all(G[P[(j+1)%4],P[j]]<0 for j in I) for P in permutations(I))
assert joining(3,[2])==-8 and joining(2,[0])==-R(501,100) and joining(3,[0])==-1
assert joining(0,[1])>0>joining(0,[1,2])
assert joining(0,[1,2,3])==R(9,100)>0
print('PASS all matrix support, raw pair-phase, protected-leaver and charge screens')

# Universal cofactor and determinant identities used by the raw source adapter.
a,b,c,d,e,f,g,h,k,l,m,n=s.symbols('a b c d e f g h k l m n')
GG=s.Matrix([[0,-a,-b,c],[-d,0,e,f],[g,h,0,-k],[-l,m,n,0]])
AA=l*f/d-m*c/a;HH=n-l*e/d-m*b/a
uu=c*HH-b*AA;vv=f*HH+e*AA
assert all(s.simplify(t)==0 for t in GG.adjugate()[:,2]-s.Matrix([a*vv,d*uu,a*d*AA,a*d*HH]))
assert s.simplify(GG.det()-(a*g*vv+d*h*uu-k*a*d*HH))==0
print('PASS universal source and small-face determinant identities')


# Exact both-negative coarse stress; higher rewards here are separate from
# the finite-selector separation table above.
x=R(1,17);w=R(1,21);y=R(2,79);z=R(1,10)
ZZ=s.Matrix([-1,-R(2227,1171),-13,R(1208,79)])
U=s.Matrix([-R(1,21),-R(131,1171),R(1,3),0])
U3=(1-z)*U+z*G[:,3];U2=(1-y)*U3+y*G[:,2]
def stress_native(i,A):
 A=tuple(sorted(A))
 if not A:return s.S.Zero
 if len(A)==1:return G[i,A[0]]
 if A==(0,1):return ZZ[i]
 return s.S.Zero

def endpoint_check(native, phases, own):
 for rates,cont,prescribed in phases:
  for i in I:
   other=[j for j in I if j!=i];Q=P=0
   for bits in product((0,1),repeat=3):
    coalition=[j for j,bb in zip(other,bits) if bb]
    prob=s.prod(rates[j] if bb else 1-rates[j] for j,bb in zip(other,bits))
    Q+=prob*(own[i]+native(i,coalition+[i]))
    P+=prob*(own[i]+(native(i,coalition) if coalition else cont[i]))
   assert own[i]+prescribed[i]==(1-rates[i])*P+rates[i]*Q
   assert max(P,Q)<=own[i]+prescribed[i]
phases=[([x,w,0,0],U2,U),([0,0,y,0],U3,U2),([0,0,0,z],U,U3)]
for own in ([0,0,0,0],[-3,5,-7,2]):endpoint_check(stress_native,phases,own)
assert U[0]<0 and U[1]<0 and min(U2)>=0 and min(U3)>=0
assert s.prod(1-t for t in (x,w,y,z))==R(1056,1343)
assert all(0<s.prod(1-rate for j,rate in enumerate([x,w,y,z]) if j!=i)<1 for i in I)
print('PASS both-negative joint stress: all actual endpoints, signed levels, opponent contraction')

# Deep second-premium child stress, with negative observer payoff.
cx,cy,cz=R(23,85),R(69,217),R(23,74)
CU=s.Matrix([0,-R(11,17),5*cx,0])
CV=s.Matrix([0,R(76,31),0,7*cy])
CW=s.Matrix([3*cz,R(59,74),0,0])
def child_native(i,A):
 A=tuple(sorted(A))
 if not A:return s.S.Zero
 if len(A)==1:return G[i,A[0]]
 if A==(0,1):return (2,-3,0,0)[i]
 return s.S.Zero
childphases=[([cx,0,0,0],CV,CU),([0,0,cy,0],CW,CV),([0,0,0,cz],CU,CW)]
for own in ([0,0,0,0],[-3,5,-7,2]):endpoint_check(child_native,childphases,own)
assert CU[1]<0 and min(CV)>=0 and min(CW)>=0
print('PASS deep-negative child stress: exact negative observer collision caps')

import sympy as s
b,c,d,e,f,g,k,l,n,z=s.symbols('b c d e f g k l n z',positive=True)
Delta=c*g*n-b*k*l
E=e*c+f*b
Den=g*c*c*e*n+f*b*b*k*l
Dmax=g*l*E*E/Den
N0=-d*k*n+e*k*l+f*g*n
N2=b*f*l-c*d*n+c*e*l
N3=-b*d*k+b*f*g+c*e*g
theta=g*N2/Delta
C=d*f*b/E
u=c*n-l*E/d
assert s.factor(theta+C-(g*l*E*E-d*Den)/(E*Delta))==0
assert s.factor(N0.subs(d,Dmax)-e*f*Delta**2/Den)==0
assert s.factor(N3.subs(d,Dmax)-c*e*g*E*Delta/Den)==0
zs=Delta/(c*(g*n+k*(l+n)))
y=c*z/(b+c*z)
X=n*c*z/(l*(b+c*z))
eta=(1-y)*(1-z)
Pi=(f*z*(1-y)+e*y-d*X)/(X-eta*X/(1+X))
Piform=-d*u*(l*b+c*(l+n)*z)/(c*n*z*(l*b+c*(l+n)))
assert s.factor(Pi-Piform)==0
assert s.factor(Piform.subs(z,zs)-theta)==0
F=g*X/(1+X)-k*z/(1-z)
assert s.factor(F-z*(Delta-c*(g*n+k*(l+n))*z)/((1-z)*(b*l+c*(l+n)*z)))==0
Cf=f*(d*b+c*(d+e)*z)/(e*c+f*b+c*(f-e)*z)
assert s.factor(s.diff(Cf,z)-c*e*f*(b*d+b*f+c*d+c*e)/(e*c+f*b+c*(f-e)*z)**2)==0
base={b:2,c:3,d:9,e:6,f:4,g:5,k:3,l:6,n:7}
assert Dmax.subs(base)==s.Rational(3380,363)
assert theta.subs(base)==-s.Rational(55,23)
assert C.subs(base)==s.Rational(36,13)
print('PASS both-premium cone, top crossing and solo3 positivity identities')

assert 9<R(3380,363)
print("PASS strict both-premium raw singleton cone and complete checks")
```
