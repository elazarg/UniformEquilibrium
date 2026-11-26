# An arbitrary participant premium in a joint-pair quitting cycle

## 1. Complete original-game theorem

Consider a four-player quitting game. Every nonempty quitting coalition S
absorbs at a finite reward vector r(S); live dates and literal Never pay
zero. Players use independent private randomization, and deviations are
arbitrary complete behavioral strategies. Put s_i=r_i({i}) and
Z_i(S)=r_i(S)-s_i for NONEMPTY S only. The own levels s_i may have any
sign. Let the literal singleton-difference matrix, after relabeling, be

    G=[ 0  -a  -b   c ]
      [-d   0   e   f ]
      [ g   h   0  -k ]
      [-l   m   n   0 ],

where a,b,c,d,e,f,g,k,l,n are strictly positive. Write the literal native
pair payoff Z(01)=(Pi0,Pi1,K,J). Suppose Pi1>=0 and the following twelve
native participant coordinates are nonpositive:

    Z2(02),Z2(12),Z2(012)<=0,
    Z3(03),Z3(13),Z3(013)<=0,                       (C)
    Z0(02),Z1(12),Z3(23)<=0,
    Z0(03),Z1(13),Z2(23)<=0.                       (S)

THEOREM. Either of the following complete raw hypotheses supplies an
original uniform-equilibrium payoff:

1. h,m are arbitrary real numbers and Pi0>=-a;
2. h,m>=0 and Pi0 is an ARBITRARY real number.

In both cases K,J and every other unmentioned higher-coalition coordinate
are arbitrary finite real numbers. There are no generic principal-minor,
Q, degree, inverse, supplied root, or supplied strategy hypotheses.
The result includes open regions in all sixty original reward coordinates.
It does not remove the twelve caps or the condition Pi1>=0.

The main new producer keeps a joint01 date and up to two solo dates
coarse. Under the numerical guards derived in Section3 and Pi0>-a, it
produces one exact terminal Nash profile of period at most three and one
fixed target. That SAME profile works to every positive accuracy over
all sufficiently long finite horizons. The remaining raw cases use an
existing child or singleton-base UE exit, or actual reward closure at
Pi0=-a. The latter cases are UE conclusions, with no asserted common
three-date exact strategy representation.

This is ordinary mathematics with a complete source adapter and behavioral
consumer proof, not a newly checked Lean theorem.

## 2. Direct coarse producer

Temporarily impose Pi0>-a and the numerical conditions

    A=lf/d-mc/a>0, H=n-le/d-mb/a,
    u=cH-bA>0, v=fH+eA, det G>0.                   (N)

They imply H,v>0. The exact identity used below is

    det G=agv+dhu-kadH.

No sign restriction on h,m or magnitude restriction on Pi0,Pi1,K,J
beyond the already stated Pi0>-a and Pi1>=0 is used in this section.


### 2.1 Produced root on a compact strip

For 0<z<1 and 0<=y<=ymax(z)=cz/(b+cz), put eta=(1-y)(1-z) and define
W>=0 and X>0 by

    (Pi0+a)W-eta Pi0 W/(1+W)=cz(1-y)-by,
    (Pi1+d)X-eta Pi1 X/(1+X)=fz(1-y)+ey.           (8)

Write a0=min(a,a+Pi0)>0. If Pi0<=0, the first derivative is at
least a+Pi0; if Pi0>=0, it is at least a because eta<=1. Thus the
first derivative is always at least a0; the second is at least d>0.
Both functions vanish at zero and tend to infinity. Therefore these
solutions exist uniquely and depend continuously on (y,z). In particular

    W<=cz/a0, X<=(f+e)/d,

and W=0 exactly at y=ymax. Set

    den=(1+X)(1+W), P=gX+hW+KXW,
    B=P/den, V0=kz/(1-z),
    R=lX-mW-JXW-ny,
    T=ge/d-hb/a, F=B-V0+(T/H)R.                    (9)

On the top boundary W=0. Because Pi1>=0, the second left side in (8)
is at least dX. Thus

    X<=z(bf+ce)/[d(b+cz)],
    R<=-uz/(b+cz)<0.                              (10)

Uniformly for 0<=y<=ymax as z tends to zero, all y,X,W are O(z), and
eta=1+O(z). Expanding (8) gives

    aW=cz-by+O(z^2), dX=fz+ey+O(z^2),
    R=Az-Hy+O(z^2),
    B-V0=(gf/d+hc/a-k)z+Ty+O(z^2).

The exact determinant identity det G=agv+dhu-kadH then gives

    F=[det G/(adH)]z+O(z^2)>0                    (11)

on a whole sufficiently small-z face, and R(0,z)>0 there. The constants
depend only on this fixed finite table. As z tends to one, X,W,B,R stay
bounded, whereas V0 tends to positive infinity. Hence F<0 on a whole
sufficiently large-z face. Choose 0<zL<zR<1 realizing both face signs.

Normalize y=s*ymax(z), 0<=s<=1. Brouwer supplies a fixed point of

    (s,z) -> (projection_[0,1](s-F),
              projection_[zL,zR](z+R)).            (12)

On z=zL, F>0 forces s=0; then R>0 excludes that corner. On z=zR,
F<0 forces s=1; then (10) excludes that corner. On s=1, (10) forces
z=zL, already excluded. Therefore z is interior and s<1 at a fixed
point, giving R=0 and either s>0,F=0 or s=0,F>=0. Equivalently,

    X,W>0, 0<z<1, 0<=y<ymax,
    R=0, y>0 => B=V0, y=0 => B>=V0.               (13)

This is a produced point, fixed before accuracy. It does not assume a
global zero branch or an invertible Jacobian.

### 2.2 Three actual exact phase comparisons

Set x=X/(1+X), w=W/(1+W), and

    V=[P-(1-y)kz]/[den-(1-y)(1-z)],
    D2=(1-z)V-kz.

The denominator is positive. If y>0, (13) gives V=V0. If y=0, direct
subtraction gives

    V-V0=[(1-z)P-kz den]/[(1-z)(den-1+z)]>=0.

Thus V>=V0>0, D2>=0, and yD2=0. The three prescribed native values,
in chronological order at the starts of joint01, solo2, solo3, are

    U=(Pi0*w,Pi1*x,V,0),
    U2=((Pi0+a)W,(Pi1+d)X,(1-y)D2,ny),
    U3=((1-z)Pi0*w+cz,(1-z)Pi1*x+fz,D2,0).       (14)

The joint Bellman identity follows from (8), R=0, and the defining V.
The solo Bellman identities are U2=(1-y)U3+yG_:2 and
U3=(1-z)U+zG_:3. When y=0, omit solo2 and U2=U3.

Even when Pi0<0, its negative coordinate U0 causes no missing inequality. At the joint
date, owners0,1 have exact Quit and Continue values Pi0*w and Pi1*x,
respectively, by (8). The two inactive players have prescribed values
V>0 and zero, while their forced-Quit values are nonpositive by (C).

At solo2, all coordinates of U2 are nonnegative because Pi0+a>0 and
Pi1+d>0. If that phase is present its mover2 has U2_2=U3_2=0. The
three inactive forced-Quit values are respectively yZ0(02), yZ1(12),
yZ3(23), nonpositive by (S), hence bounded by their prescribed values.

At solo3, U3_1>=0, U3_2>=0, U3_3=0. Crucially, regardless of the sign of U0,

    U2_0=(1-y)U3_0-by>0,

so U3_0=(U2_0+by)/(1-y)>0. The three inactive forced-Quit values
zZ0(03),zZ1(13),zZ2(23) are nonpositive by (S). Mover3 is indifferent
at zero. This checks every pure action at every actual date. The
negative U0 is followed by a whole coarse solo3 in the backward equations;
there is no attempted nonnegative-floor assertion at intermediate
microdates, because those microdates are never introduced.

### 2.3 Complete behavioral caps and signed original rewards

All present hazards are strictly below one. Owners0,1 have positive joint hazards
x,w and owner3 has positive solo hazard z. Consequently each player's
deleted-opponent survival over one period is at most some fixed rho_i<1,
including when y=0 and owner2 always continues. This bound is independent
of the deviator's entire behavioral strategy.

Backward induction using the just-proved pure-action inequalities gives
the deviation bound up to any finite deadline with the prescribed bounded
continuation vector at that deadline. The discrepancy from literal terminal
payoff is bounded by a fixed payoff bound times rho_i to the number of
complete periods. Letting the deadline tend to infinity proves the exact
cap against every behavioral replacement, including Never. Bellman
iteration proves that the prescribed native payoff is U. Thus this is
an exact terminal Nash profile, including when its coordinate U0 is negative.

Opponents absorb almost surely against every unilateral law, so adding
the original own level s_i adds exactly s_i to both terminal values.
No live or Never reward is translated. The original target is s+U.
For a finite horizon N, split at a fixed early date M. Uniformly over
all deviations, the probability of no absorption by M is geometrically
small; on absorption by M the difference between the average payoff and
the absorbing reward is at most a fixed reward bound times M/N. First
choose M, then N. This proves the fixed target and same profile work at
every sufficiently large horizon. All payoff signs are allowed.


## 3. The numerical guards are forced by an actual no-UE source

This section proves the needed alternative, including singular proper
principals and arbitrary signs of h,m. Standard Q means every offset has
a nonnegative complementary solution. R0 means that the only nonnegative
homogeneous complementary vector is zero. The degree is the standard
complementary-map degree.

### 3.1 A complete matrix alternative

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

### 3.2 Same-table no-UE premises and their exact consumer

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

Strict positivity of G inverse e2 and det G>0 force precisely the guards
(N). Hence when Pi0>-a the produced original equilibrium in Section2
contradicts the source. No auxiliary translated game was assumed to
lack equilibrium; only terminal payoffs along surely absorbing opponent
clocks were translated in the actual consumer.

## 4. Deep negative premiums and the boundary

### 4.1 The existing singleton-base exit

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

### 4.2 Reward closure when h or m is negative

For Pi0=-a with arbitrary h,m, increase only original reward r0(01) by
epsilon with 0<epsilon<a. All own and singleton coordinates and all
twelve caps are unchanged. Every nearby table has Pi0>-a and hence UE
by Sections2--3. The exact closure result
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
(`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`)
supplies UE for the limit table. This selects one fixed target for that
table; no common target or bounded-period representation across the
approximating tables is claimed. Sections2--4 exhaust both clauses of
the theorem.

## 5. Full sixty-coordinate admission and coverage calibration

Set all original own levels to one and use

    G=[0,-5,-2,3; -9,0,6,4; 5,2,0,-3; -6,3,7,0].

Define multilinear joining increments, independent of the recipient's own
coordinate, by

    F0=(1-q3)[(49/10)q1+(199/100)q2-(174/5)q1q2]
                           +q3[-301/100+(31/10)q2],
    F1=(1-q3)[(91/10)q0-(601/100)q2-30q0q2]-(401/100)q3,
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

The joint pair is Z(01)=(-1/10,1/10,-25,0). The twelve caps, in the
order (C),(S), are

    (-1/100,-1/100,-1/100,-7,-1,-5,
     -1/100,-1/100,-1,-1/100,-1/100,-1).

They are all strict. The grand participant vector is
(9/100,99/100,1,1)>0. Thus this table lies in an open part of the new
class with a negative joint participant premium. Every earlier
nonnegative-two-participant theorem fails that premium hypothesis on its
only mutually negative pair01, under both orders.

### 5.1 Entire matrix-side and phase-side comparisons

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

### 5.2 All quiet children, with explicit finite duals

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

### 5.3 Complete sure-owner correspondences and actual punishment floors

At a sure owner j, an opponent coordinate q_i=0 requires F_i<=0;
q_i=1 requires F_i>=0; an interior coordinate requires F_i=0. The entire
complementary Nash correspondences are the four singletons

| Sure owner | Unique complementary point |
| --- | --- |
| 0 | (1,167/1000,70/277,0) |
| 1 | (67/900,1,490/3281,0) |
| 2 | (1,0,1,0) |
| 3 | (200/501,0,301/310,1) |

For any sure owner0,1,2, F3<0 forces q3=0. At owner0 the remaining
opponents' increments are F1=91/10-(3601/100)q2 and
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
it is at least -1/100; for owner3 it is at least -7. Immediate sure Quit
therefore gives actual punishment lower bounds 9/10,99/100,-6. For the
root of owner j let h_j=product_(i!=j)(1-q_i). Its literal owner floor
excess is -F_j+h_j(punishment_j-1). The following exact lower bounds are
strictly positive:

    owner0: 117999/1385000,
    owner1: 161163527/295290000,
    owner2: 501/100,
    owner3: 249889/31062.

Owner2 has h2=0 because opponent0 is sure. For the other three owners
the displayed bounds use their actual punishment lower bounds and their
exact positive h_j, not an arbitrary continuation. Therefore every
sure-owner or persistent-base selector fails. Any smaller free-set
candidate satisfying outsider joins would belong to these full
complementary correspondences, so it is excluded too. The exact owner
floor definition and certificate interface are the declarations in
Section4.1. The original positive own levels also exclude the induced
owner Never alternative.

### 5.4 Remaining finite screens and their limits

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
    3h(0)+3h(1)+h(01)=(-151/10,-269/10,-4,-9)

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
retains the distinct family-level scope in Section5.1.

## 6. A falsification stress and formalization target

For the same G, set Z(01)=(-1,0,-2127/214,2415/214), and every other
nonsingleton native reward to zero. The exact rates

    x=214/3769, w=1/21, y=2/79, z=1/10

give U=(-1/21,0,1/3,0). All complete coarse phase pure-action comparisons
pass exactly, as the embedded program verifies. Yet refining solo3 into
hazards tending uniformly to zero destroys the equilibrium. At its last
microdate of hazard t the conditional gain from quitting for player0 is
(1-64t)/21, tending to1/21. The deviating strategy follows the prescribed
law before that date and quits there conditional on survival. Its reach
probability in the first period is at least the fixed period survival
2970/3769; for mesh below1/128 its total gain is at least
2970/(3769*42). Thus the use of actual coarse dates is essential. This
stress table also has a separate pure012 equilibrium and is not the
coverage calibration of Section5.

The finite formalization target is a raw-table producer accepting the
sign conditions, twelve caps, Pi1>=0, and either Pi0>=-a or h,m>=0.
Useful components are the monotone scalar inverse lemma with lower
derivative min(a,a+Pi0), the crossed-projection complementarity lemma,
the exact three-date Bellman/endpoints calculation, and the geometric
opponent-tail terminal-to-uniform lemma. Section3 supplies the source
alternative without proper-minor guards. Section4 reduces the other
parameter branch to existing supplied certificates and reward closure.
No lemma should silently identify terminal and finite-horizon payoffs,
or translate live and Never rewards.

The final conclusion is a UE existence class with one unrestricted
joint participant coordinate. Removing the twelve caps, allowing both
participant coordinates to be unrestricted, and the full four-player
conjecture remain open.

## Appendix. Reproducible exact checks

The following program needs Python and SymPy. It reconstructs all sixty
rewards, checks every listed finite coverage certificate and every
complementary crossing identity, verifies universal source identities,
and separately checks the negative-value coarse stress at every pure
action endpoint. Its exact checks support the explicit calculations;
the topological and arbitrary-behavioral proofs are in the text.

```python
"""Exact complete-table checks for the coarse arbitrary-one-premium class.

Save and run with Python and SymPy. No supplied root is needed by the theorem.
The rational coarse stress at the end is a separate Bellman sanity check.
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
    (1-q[3])*(R(51, 10)*q[1]+R(199, 100)*q[2]-35*q[1]*q[2])+q[3],
    R(91, 10)*q[0]-R(601, 100)*q[2]-30*q[0]*q[2]-R(401, 100)*q[3],
    -R(501, 100)*q[0]-R(201, 100)*q[1]+R(3201, 100)*q[0]*q[1]+2*q[3],
    -q[0]-4*q[1]-8*q[2]])
PASSIVE = {
    (0, (1, 2)): 28, (0, (1, 3)): 0, (0, (2, 3)): 0,
    (1, (0, 2)): 27, (1, (0, 3)): 0, (1, (2, 3)): 11,
    (2, (0, 1)): -25, (2, (0, 3)): 0, (2, (1, 3)): 0,
    (3, (0, 1)): 0, (3, (0, 2)): 0, (3, (1, 2)): 0,
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



old0=F[0].subs(q[3],0)-R(1,5)*q[1]*(1-q[2])
old1=F[1].subs(q[3],0)
F[0]=(1-q[3])*old0+q[3]*(-R(301,100)+R(31,10)*q[2])
F[1]=(1-q[3])*old1-R(401,100)*q[3]
PASSIVE.update({(0,(1,3)):3,(1,(0,3)):4,(1,(2,3)):4,
                (1,(0,2,3)):5,(2,(0,3)):3,(3,(0,2)):2,(3,(1,2)):6})
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
roots=[(1,R(167,1000),R(70,277),0),(R(67,900),1,R(490,3281),0),
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
assert s.expand(F[1].subs({q[0]:1,q[3]:0})-R(91,10)+R(3601,100)*q[2])==0
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

# A separate rational negative-value coarse root checks the actual all-action
# semantics. Its higher table is NOT the finite-selector separation table.
x=R(214,3769);w=R(1,21);y=R(2,79);z=R(1,10)
ZZ=s.Matrix([-1,0,-R(2127,214),R(2415,214)])
U=s.Matrix([-R(1,21),0,R(1,3),0])
U3=(1-z)*U+z*G[:,3];U2=(1-y)*U3+y*G[:,2]
def stress_native(i,A):
 A=tuple(sorted(A))
 if not A:return s.S.Zero
 if len(A)==1:return G[i,A[0]]
 if A==(0,1):return ZZ[i]
 return s.S.Zero
for rates,cont,prescribed in [([x,w,0,0],U2,U),([0,0,y,0],U3,U2),([0,0,0,z],U,U3)]:
 for i in I:
  other=[j for j in I if j!=i]; Q=P=0
  for bits in product((0,1),repeat=3):
   coalition=[j for j,bb in zip(other,bits) if bb]
   prob=s.prod(rates[j] if bb else 1-rates[j] for j,bb in zip(other,bits))
   Q+=prob*stress_native(i,coalition+[i])
   P+=prob*(stress_native(i,coalition) if coalition else cont[i])
  assert prescribed[i]==(1-rates[i])*P+rates[i]*Q
  assert max(P,Q)<=prescribed[i]
assert U[0]<0 and min(U2)>=0 and min(U3)>=0
assert all(0<s.prod(1-rate for j,rate in enumerate([x,w,y,z]) if j!=i)<1 for i in I)
print('PASS separate rational coarse negative-value root: all actual pure endpoints and opponent contraction')
```
