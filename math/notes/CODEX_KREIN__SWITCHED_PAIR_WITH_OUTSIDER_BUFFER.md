# A switched joint pair with a positive outsider buffer

## 1. Game, raw reward class, and conclusion

Four players I={0,1,2,3} independently choose Quit or Continue at each
live date. The first nonempty quitting coalition S absorbs at a finite
real reward vector r(S). Live and perpetual-continuation payoffs are zero.
Strategies and unilateral deviations may be arbitrary behavioral
strategies with private independent randomization. No public correlation,
bounded memory, or restriction on deviating stopping times is imposed.

Let a,b,c,h_1,h_2,h_3>0 and D=abc−1>0. Prescribe only the following
five complete reward vectors:

    r({0})=(1,−h_1,−h_2,−h_3),
    r({1})=(U,0,b,−1),
    r({2})=(V,−1,0,c),
    r({3})=(R,a,−1,0),
    r({0,3})=(1,−h_1,−h_2,0),                         (1)

where U,V≥1 and R is any real number. The own-singleton vector is
s=(1,0,0,0). Define

    A=[[0,−1,a],[b,0,−1],[−1,c,0]],
    nu_1=(ac*h_2+c*h_1+h_3)/D,
    nu_2=(ab*h_3+a*h_2+h_1)/D,
    nu_3=(bc*h_1+b*h_3+h_2)/D.                        (2)

All nu_i are strictly positive and A*nu=(h_1,h_2,h_3), equivalently

    a*nu_3−nu_2=h_1,
    b*nu_1−nu_3=h_2,
    c*nu_2−nu_1=h_3.                                  (3)

Require three outsider collision caps

    r_2({0,2})≤0, r_2({2,3})≤0, r_2({0,2,3})≤0       (4)

and one weighted condition on the other outsider:

    J=max(0,r_1({0,1}),r_1({0,1,3})),
    Q=r_1({1,3}),
    J+nu_3*Q≤nu_2.                                    (5)

Every reward coordinate not specified by (1), (4), or (5) is arbitrary.
In particular Q may be negative, r_0({0,1}) is unrestricted, and
player 1 may have strictly positive joining rewards at the actual joint
phase. No global condition on participant premiums or passive rewards
is assumed.

**Theorem.** Every such original reward table has a uniform-equilibrium
payoff, for every real R. There is one vector z such that for every
ε>0 a behavioral profile and N₀ exist with expected average payoff
within ε of z at every horizon N≥N₀, and every complete unilateral
behavioral deviation has expected average payoff at most z_i+ε.
The target is fixed before ε. On the constructive branch below it is
the explicit vector (1,w/(1−w),0,0); only the solo subdivision depends
on accuracy.

## 2. The exact singleton source exits

Put d_1=U−1≥0 and d_2=V−1≥0. Define

    R_low=1−(d_1*nu_1+d_2*nu_2)/nu_3,
    T_1=1−(c*d_1+d_2)/(bc),
    T_2=1−ac*d_1−a*d_2,
    T_3=1−d_1/b−a*d_2,
    T=T_1.                                            (6)

The child matrix A has determinant D and strictly positive inverse

    A⁻¹=(1/D)[[c,ac,1],[1,a,ab],[bc,1,b]].             (7)

The pivot's centered passive singleton row is (d_1,d_2,R−1), with
literal inverse weights

    (d_1,d_2,R−1)A⁻¹
       =(bc(R−T_1), R−T_2, b(R−T_3))/D.              (8)

Here T_2≤T_3≤T_1: the first difference is D*d_1/b and the second
is D*d_2/(bc). Therefore R≥T gives nonnegative weights. The existing
three-child nonnegative-inverse criterion gives a uniform-equilibrium
payoff for the original four-player table, with no assumptions on its
other reward coordinates. The source is
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
It requires exactly child cardinality three, nonzero determinant,
entrywise nonnegative inverse, and the nonnegative weights (8).
Equality R=T is included directly.

For the lower exit use the full centered singleton matrix

    M=[[0,d_1,d_2,R−1],
       [−h_1,0,−1,a],
       [−h_2,b,0,−1],
       [−h_3,−1,c,0]].                                (9)

For every t>0, the complementarity problem

    z≥0, Az≥t*h, z_i(Az−t*h)_i=0

has the unique solution z=t*nu. Indeed a zero coordinate forces, by
the corresponding positive right-hand side and cyclic negative edge,
the next positive coordinate, whose active equality forces a second
positive coordinate; its equality then contradicts the original zero.
Explicitly, z_1=0 implies z_3>0, then c*z_2=t*h_3 and z_2>0,
then −z_3=t*h_2, impossible. Cyclic rotation treats the other zeros.
Thus all coordinates are positive and (7) determines z. For t=0,
a nonzero solution with a zero coordinate is likewise impossible:
if z_1=0 and z_3>0 then z_2=0 by player 3's equality, and player 2's
inequality fails; if z_3=0 and z_2>0 then player 2's equality forces
z_1=0 and player 1's inequality fails. An all-positive solution is
excluded by invertibility. Thus the homogeneous child problem has
only the zero solution.

If R≠R_low, M is R₀: a positive homogeneous pivot coordinate t
forces child coordinates t*nu, leaving pivot residual
t*nu_3(R−R_low)≠0, which contradicts pivot complementarity. A zero
pivot coordinate forces the homogeneous child to be zero. At R=R_low,
instead, (1,nu) is a nonzero homogeneous solution. The existing theorem
that four-player noUE implies full singleton R₀ therefore gives UE at
this equality. Its precise source is
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`.

If R<R_low, put δ=nu_3(R_low−R)>0 and choose q_0>δ. At offset
(q_0,−h_1,−h_2,−h_3), every complementarity root with pivot t≥0
has child coordinates (1+t)nu. Its pivot residual is q_0−δ(1+t).
There are exactly two roots: t=0 with strictly positive inactive
residual q_0−δ, and t=q_0/δ−1>0 with full support. Their active
principal determinants are D>0 and det M=−Dδ<0, respectively.
Thus the R₀ degree is +1−1=0, by the regular-offset root-sum formula
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`. All its inactive residuals
are strictly positive and both active determinants are nonzero, as
required. The source
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
then gives UE for the original table. These two source exits impose
no extra condition on nonsingleton rewards.

If U=V=1, then R_low=T=1 and these exits already cover every R.
Otherwise direct use of (3) gives

    T−R_low=[h_2(c*d_1+d_2)+b*d_2*h_3]/(bc*nu_3)>0.  (10)

It remains to construct only on R_low<R<T.

## 3. An admissible scalar selector

Let

    L=bc+c+1,          Y=D/(aL).

For 0<y<Y and a scalar k≥0 define

    z=(h_2*k+y)/[b(1−y)],
    w=(a*y−h_1*k)/[1+a*y+(1−h_1)k],
    G(k,y)=h_3*k+z−c*w*(1−z).                        (11)

Write C=b(1−y), E=b−(b+1)y, d_0=1+a*y, d_1=1−h_1.
The admissible closed interval is

    0≤k≤K=min(a*y/h_1,E/h_2).                        (12)

It is nondegenerate, because Y<b/(b+1)<1; specifically
a*b*L−D(b+1)=ab+b+1>0. On (12), z≤1, w≥0, and
d=d_0+d_1*k=1+k+a*y−h_1*k≥1+k>0, so w<1.

Clearing only positive denominators gives

    C*d*G=αk²+βk+γ,
    α=(h_3*C+h_2)d_1−c*h_1*h_2,
    β=h_3*C*d_0+h_2(d_0+c*a*y)+y+h_1(cE−y),
    γ=y(aL*y−D).                                      (13)

For 0≤y≤Y, cE−y≥1/a, so β>0. For interior y, γ<0.
At k=K either w=0 or z=1, making G(K,y)>0. Consequently (13)
has exactly one root in (0,K), and that root is simple with positive
derivative. If α≥0 the polynomial is strictly increasing on k≥0.
If α<0, its two possible positive crossings cannot both lie before K
because the value at K is positive; the admissible crossing is the
first. These observations also cover α=0 without division by α.

The continuous selector is explicitly

    k(y)=−2γ/[β+sqrt(β²−4αγ)].                        (14)

The discriminant is strictly positive, including when α vanishes, and
the denominator is positive. At y=0 and y=Y the same expression gives
k=0, because γ=0 and β>0. Thus k extends continuously to [0,Y].
At zero, β(0)=bc*h_1+h_2+b*h_3=D*nu_3, hence

    k/y→1/nu_3, z/y→nu_1/nu_3, w/y→nu_2/nu_3.        (15)

For every interior y, k>0, 0<z,w<1. Set x=k/(1+k), so 0<x<1.
These quantities depend only on the raw parameters and the eventual
choice of y, not on any supplied strategy certificate.

## 4. Pivot selection and the positive outsider buffer

Define scalar continuation coordinates

    P_C=1+(V−1)w,
    P_B=U*z+(1−z)P_C,
    R(y)=[1−(1−y)P_B]/y.                             (16)

Both P_B and P_C are at least one. By (15), R(y) extends continuously
to zero with value R_low. At y=Y the zero-k balance gives

    (1−Y)z/Y=1/b,
    (1−Y)(1−z)w/Y=1/(bc).

Substituting in (16) gives R(Y)=T. Therefore the intermediate value
theorem chooses an interior y for every R_low<R<T. Monotonicity or
uniqueness of R(y) is not required. Choose one such y once and for
all for the fixed reward table.

The key buffer estimate is

    k(y)<y/nu_3.                                      (17)

Test k_0=y/nu_3. If k_0≥K, the strict root location proves (17).
Otherwise the corresponding quantities in (11) satisfy

    z_0=nu_1*y/[nu_3(1−y)]>nu_1*y/nu_3,
    w_0=nu_2*y/[nu_3+(nu_2+1)y]<nu_2*y/nu_3.

Hence G(k_0,y)>(h_3+nu_1−c*nu_2)y/nu_3=0. Since G starts
negative and has only one admissible zero, that zero lies below k_0.
This proof uses no monotonicity assertion beyond the unique crossing
already established in Section 3.

At a joint {0,3} row with hazards x,y, outsider 1's immediate-Quit
endpoint has exact numerator

    k(1−y)r_1({0,1})+yQ+ky*r_1({0,1,3})

over denominator 1+k. By (5) this is at most (kJ+yQ)/(1+k).
Since a*nu_3−h_1=nu_2, the same raw condition gives
a−Q≥(h_1+J)/nu_3. Inequality (17) therefore implies

    (a−Q)y−(h_1+J)k>0.                               (18)

Thus outsider 1's immediate-Quit payoff is strictly below
(a*y−h_1*k)/(1+k)=w/(1−w), a strictly positive continuation value.
This permits actual positive joining premiums; it does not replace
them by a zero cap. The argument remains valid for negative Q.

Outsider 2's immediate Quit can realize exactly its singleton and
coalitions {0,2},{2,3},{0,2,3}. Their rewards are all at most zero
by (4). Its immediate-Quit endpoint is therefore at most zero.

## 5. Phase values and complete behavioral deviations

Repeat three coarse phases: A is joint {0,3} with hazards x,y;
B has only player 1 with hazard z; C has only player 2 with hazard w.
In the original player order (0,1,2,3), put

    V_A=(1,w/(1−w),0,0),
    V_B=(P_B,0,b*z,h_3*k),
    V_C=(P_C,0,0,c*w).                                (19)

Every phase value is at least the own-singleton vector s. At A the
pivot's Quit endpoint is one, and its Continue endpoint is
R*y+(1−y)P_B=1. Player 3's Quit endpoint is zero, and its Continue
endpoint is −x*h_3+(1−x)h_3*k=0. The two outsiders' policy equations
are

    V_A,1=(a*y−h_1*k)/(1+k)=w/(1−w),
    V_A,2=[−h_2*k−y+(1−y)b*z]/(1+k)=0.

Their Quit comparisons were proved in Section 4. At B and C, every
coordinate satisfies the literal singleton recurrence

    V_B=z*r({1})+(1−z)V_C,
    V_C=w*r({2})+(1−w)V_A.

The nontrivial player-3 identity at B is
−z+c*w*(1−z)=h_3*k, exactly G=0. Both solo owners are indifferent
between Quit and Continue at value zero. Consequently EVERY prescribed
Continue action is exact, including those of the four mixing players.
However arbitrary unused rewards can make some outsider Quit action
at a coarse solo phase profitable. The coarse cycle is not asserted
to be Nash for arbitrary completions.

For n≥1 replace each solo block with n identical microhazards

    z_n=1−(1−z)^(1/n), w_n=1−(1−w)^(1/n).             (20)

Their aggregate hazards remain z,w. Leave the joint A row unchanged.
The vector before a microstage with m remaining microstages in a solo-j
block, endpoint W and aggregate q, is

    [1−(1−q)^(m/n)]r({j})+(1−q)^(m/n)W.

It lies on the line segment between the original block entry and exit,
so every singleton floor is preserved. The owner coordinate remains
its singleton throughout. Direct recurrence gives exact policy and
Continue identities at every microstage, with the same V_A at the
start of each period.

Let

    C_join=max({0}∪{r_i({i,j})−s_i : j∈{1,2}, i≠j}),
    e_n=C_join*max(z_n,w_n).                            (21)

At a solo-j microhazard q_n, outsider i's immediate-Quit payoff is
s_i+q_n[r_i({i,j})−s_i], hence at most its phase value plus e_n.
Owners are exactly indifferent; the joint row retains error zero.
Thus e_n→0 while the target V_A is unchanged.

For completeness, the resulting bound is for full deviations, not
only one-step switches. For each player add e_n to every phase value.
The Quit endpoint is at most this new value. Since Continue is exact,
its new value is the old value plus c_{−i}e_n≤e_n above it, where
c_{−i} is that stage's opponent survival probability. Therefore
V_i+e_n is a Bellman supersolution at every live history. Iterating
conditional expectations caps any deviating behavioral strategy by
that same SINGLE error, not a sum over stages or periods.

To pass to an infinite horizon, let m_n=1+2n and let rho_i be the
product of all opponent Continue probabilities in one period. It is
strictly less than one: all four aggregate hazards x,y,z,w are
positive, so deleting any one player's behavior leaves a positive
opponent hazard. The event of surviving ℓ full periods under any
deviation implies that all prescribed opponents continued, giving
probability at most rho_i^ℓ. This bound is uniform over the deviator's
whole behavioral strategy. Phase values are bounded, so the terminal
remainder in the iterated supersolution tends to zero. Exact policy
evaluation and the same tail show that the profile's actual terminal
payoff is exactly V_A. Every terminal unilateral payoff is at most
(V_A)_i+e_n.

This also gives a direct finite-horizon argument. Put

    C_time=max_i m_n/(1−rho_i)

and choose M≥1 bounding every terminal reward coordinate in absolute
value. Couple any deviation with the opponents' scheduled hazards.
Actual absorption occurs no later than the opponents' first Quit, so
its expected absorption time is at most C_time. The profile has the
same bound. Expected finite-horizon average payoff differs from the
corresponding terminal payoff by at most 2M*C_time/N. Thus on-path
delivery error is at most 2M*C_time/N, and a deviator's average payoff
is at most (V_A)_i+e_n+2M*C_time/N. Its regret relative to the actual
profile payoff is at most e_n+4M*C_time/N. Choose n first to make
e_n small and then N₀ to control these tails for all N≥N₀. This proves
the uniform conclusion with the fixed target in (19).

The existing infinite-path counterpart is
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`,
with fixed-target consumer
`isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`,
both in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
The finite-law/terminal endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The new mathematical input is the raw-data construction (11)–(19), not
a new supersolution or refinement compiler.

## 6. Exact boundary tests

### A negative joining reward with a binding weighted cap

Set a=b=c=2, h_1=h_2=1, h_3=79/45, U=3/2, V=5/4,
J=2, Q=−179/383. Then

    nu=(349,451,383)/315,
    R_low=1/4, T=11/16,
    y=1/4, k=1/10, x=1/11, z=7/30, w=4/15,
    R=149/300,
    V_A=(1,4/11,0,0),
    V_B=(1051/900,0,7/15,79/450),
    V_C=(16/15,0,0,8/15).

The raw inequality (5) binds. Set r_1(01)=r_1(013)=2, set the
three coordinates in (4) to zero, and set every other unspecified
coordinate to 37. The twelve exact policy and Continue equations still
hold. At A, outsider 1's Quit payoff is 637/8426, below its prescribed
value by 2427/8426. Some coarse solo Quit inequalities fail with this
completion. They are controlled by (21), so this example genuinely
uses refinement of arbitrary unused premiums.

### A vanishing quadratic leading coefficient

Set a=b=c=2, h=(5/9,1,1), U=V=2, J=17/7 and Q=−2.
Then

    nu=(55,59,47)/63,
    R_low=−67/47, T=1/4,
    y=1/4, k=7/50, x=7/57, z=13/50, w=10/37,
    R=−19/50,
    V_A=(1,10/27,0,0).

At the selected y, α=0, β=25/4, γ=−7/8, so (14) gives
k=−γ/β=7/50 without a singularity. Condition (5) is again equality.
This checks a nontrivial zero-leading-coefficient branch, not a limiting
approximation to a nondegenerate polynomial.

## 7. Full premium core and no common leaver

The following fully specified completion shows that the class is not
subsumed by a condition requiring one player common to every premium
trap. Use a=b=c=2, all h_i=1, U=V=2 and R=0. To specify the whole
table, initially put

    r_0(S)=1                         if 0∈S,
            2                        if S={1} or S={2},
            0                        otherwise.

For each j∈{1,2,3}, put

    r_j(S)=0                         if j∈S,
            −1                       if j∉S and 0∈S,
            2*1_(pred(j)∈S)−1_(succ(j)∈S) otherwise,

where pred(1)=3, pred(2)=1, pred(3)=2, and succ is the inverse
cyclic relation. Then change exactly these five coordinates:

    r_0({0,1})=2, r_1({0,1})=1,
    r_1({1,2})=r_2({1,2})=1/2,
    r_3({1,3})=1/2.                                  (22)

This table satisfies (1), (4), and (5): nu=(1,1,1), J=1 and Q=0.
Its rates can be selected algebraically. Put

    y=(3−sqrt(5))/2,
    k=y(1−2y), x=k/(1+k), z=w=y.

The identity y=(1−y)² verifies (11) and (16), and the target is
(1,y/(1−y),0,0). The additions (22) at 12 and 13 are handled by
the solo refinement, so exact Nash of the coarse profile is not
asserted for this completion.

A premium trap is a nonempty set A such that every i∈A has some
coalition S⊆A containing i with r_i(S)>s_i. Here 01 and 12 are
traps, so their only possible common player is 1. But that player
fails even weak leave at 01:

    r_1({0,1})=1>−1=r_1({0}).

Thus no player is a common weak leaver in every trap, even if signed
premiums away from that player are allowed. The greatest premium
core is the full set: players 0,1 have witnesses at 01, player 2
at 12, and player 3 at 13. The positive player-2 reward at 12 and
player-3 reward at 13 also violate zero outsider caps at a joint-01
phase. This is separation from these precise raw criteria, not a
claim that every other equilibrium construction fails.

The proof gives ordinary mathematical evidence and names its existing
semantic consumers. It does not assert a Lean implementation of the
new raw criterion, and it does not claim that choosing a joint pair
always suffices for an arbitrary four-player reward table.
