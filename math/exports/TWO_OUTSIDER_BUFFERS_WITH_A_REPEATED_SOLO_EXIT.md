# Two outsider buffers from a repeated solo exit

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
    r({0,3})=(1+xi,−h_1,−h_2,0),                      (1)

where U,V≥1, xi≥0, and R is any real number. The own-singleton vector is
s=(1,0,0,0). Define

    A=[[0,−1,a],[b,0,−1],[−1,c,0]],
    nu_1=(ac*h_2+c*h_1+h_3)/D,
    nu_2=(ab*h_3+a*h_2+h_1)/D,
    nu_3=(bc*h_1+b*h_3+h_2)/D.                        (2)

All nu_i are strictly positive and A*nu=(h_1,h_2,h_3), equivalently

    a*nu_3−nu_2=h_1,
    b*nu_1−nu_3=h_2,
    c*nu_2−nu_1=h_3.                                  (3)

Put delta_1=U−1 and delta_2=V−1, and define
R_low=1−(delta_1*nu_1+delta_2*nu_2)/nu_3. Require an auxiliary real scalar
theta satisfying only finite raw reward inequalities:

    0≤theta<nu_2/h_1,       xi≥theta(1−R_low).           (4)

This theta is not a supplied strategy or continuation certificate.
For the two outsiders at the joint phase put

    J_1=max(0,r_1({0,1}),r_1({0,1,3})),
    Q_1=r_1({1,3}),
    J_2=max(0,r_2({0,2}),r_2({0,2,3})),
    Q_2=r_2({2,3}).

Require exactly the two weighted inequalities

    (1+theta)J_1+nu_3 Q_1≤nu_2−h_1 theta,
    (1+theta)J_2+nu_3 Q_2≤theta nu_3.                  (5)

All reward coordinates not specified in (1) or constrained in (5) are
arbitrary finite real numbers. Both Q_i may have either sign. If
theta>0 the inequalities permit all SIX nontrivial outsider joining
coordinates to be strictly positive. At theta=0 the last solo block
of the construction is empty; its proof is given directly below.

**Theorem.** Every such original reward table has a uniform-equilibrium
payoff, for every real R. There is one vector z such that for every
ε>0 a behavioral profile and N₀ exist with expected average payoff
within ε of z at every horizon N≥N₀, and every complete unilateral
behavioral deviation has expected average payoff at most z_i+ε.
The target is fixed before ε. On the constructive branch below it is
the explicit vector (p,A_1,theta*y,0); only the solo subdivision depends
on accuracy.

## 2. The exact singleton source exits

Put delta_1=U−1≥0 and delta_2=V−1≥0. Define

    R_low=1−(delta_1*nu_1+delta_2*nu_2)/nu_3,
    T_1=1−(c*delta_1+delta_2)/(bc),
    T_2=1−ac*delta_1−a*delta_2,
    T_3=1−delta_1/b−a*delta_2,
    T=T_1.                                            (6)

The child matrix A has determinant D and strictly positive inverse

    A⁻¹=(1/D)[[c,ac,1],[1,a,ab],[bc,1,b]].             (7)

The pivot's centered passive singleton row is (delta_1,delta_2,R−1), with
literal inverse weights

    (delta_1,delta_2,R−1)A⁻¹
       =(bc(R−T_1), R−T_2, b(R−T_3))/D.              (8)

Here T_2≤T_3≤T_1: the first difference is D*delta_1/b and the second
is D*delta_2/(bc). Therefore R≥T gives nonnegative weights. The existing
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

    M=[[0,delta_1,delta_2,R−1],
       [−h_1,0,−1,a],
       [−h_2,b,0,−1],
       [−h_3,−1,c,0]].                                (9)

Write h=(h_1,h_2,h_3). For every t>0, the complementarity problem

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

    T−R_low=[h_2(c*delta_1+delta_2)+b*delta_2*h_3]
             /(bc*nu_3)>0.                            (10)

It remains to construct only on R_low<R<T.

## 3. A strictly monotone raw-data selector

Put

    L_theta=a(bc+c+1)+theta(1+a+ac),
    Y_theta=D/L_theta,
    t=theta*y/(1+theta*y),
    A_1=(a*y−h_1*k)/(1+k),
    z=[h_2*k+y+(1+k)theta*y]/[b(1−y)],
    ell=a*t+(1−t)A_1,
    w=ell/(1+ell),
    G(k,y)=h_3*k+z−c*w*(1−z).                        (11)

Here t is the final solo-3 aggregate hazard, not the pivot hazard.
For 0<y<Y_theta work on

    0≤k≤K=min(a*y/h_1,
             [b−(b+1+theta)y]/[h_2+theta*y]).

Both bounds are positive: indeed

    b L_theta−D(b+1+theta)
       =(1+theta)(ab+b+1)>0.

On this interval, 0≤A_1, 0<z≤1, 0≤ell and 0≤w<1.
As k increases, z strictly increases, A_1 strictly decreases, hence
w strictly decreases. Therefore G is strictly increasing, with
derivative at least h_3>0 wherever the interval is nondegenerate.
At k=0, clearing the positive denominators gives the sign of

    −D+L_theta*y,

so G(0,y)<0. At the right endpoint, either z=1, giving G>0, or
k=a*y/h_1. In the latter case A_1=0 and w≤a*theta*y, whereas

    z≥[1+theta+a*h_2/h_1]y/b.

Consequently

    G(K,y)≥y*D*(nu_2−h_1 theta)/(b h_1)>0.

These inequalities give one and only one root k(y) in (0,K).
The derivative lower bound gives continuity in the interior. At zero,
K≤a*y/h_1 forces k→0; at Y_theta, continuity and strict monotonicity
force k→0 because G(0,Y_theta)=0. Thus the branch extends continuously
with k(0)=k(Y_theta)=0. Dividing (11) by y at zero gives

    k/y→(1+theta)/nu_3,
    z/y→(1+theta)nu_1/nu_3,
    w/y→(1+theta)nu_2/nu_3.                           (12)

To justify the division without assuming a derivative, k/y is bounded
by a/h_1. Every convergent subsequence solves the same linear limiting
balance, whose positive coefficient is
h_3+h_2/b+c*h_1=D*nu_3/b. Hence its limit is unique.

## 4. The two outsider comparisons

The strict estimate needed for (5) is

    k(y)<(1+theta)y/nu_3.                             (13)

Test k_0=(1+theta)y/nu_3. If it is outside the admissible interval,
the conclusion is immediate. Otherwise its z value is strictly greater
than (1+theta)nu_1*y/nu_3. Its w value has numerator

    (1+theta)y(nu_2+a*theta*y)/nu_3

and denominator

    1+[theta+(1+theta)(nu_2+1)/nu_3]y
      +theta(1+a)(1+theta)y²/nu_3.

It is strictly less than (1+theta)nu_2*y/nu_3. Indeed, after comparing
the first-order coefficients, the required positive difference, times
nu_3, is

    nu_2(nu_2+1)+theta(nu_2 nu_3+nu_2²−h_1)>nu_2²,

using theta*h_1<nu_2; the quadratic coefficient is nonnegative too.
It follows that

    G(k_0,y)>(1+theta)y(h_3+nu_1−c*nu_2)/nu_3=0.

Strict increase proves (13).

Set x=k/(1+k). At the joint phase outsider i∈{1,2} can meet exactly
the opponent coalitions empty, {0}, {3}, {0,3}. Since s_i=0, its
forced-Quit payoff is exactly

    [k(1−y)r_i({0,i})+y Q_i+k*y*r_i({0,i,3})]/(1+k),

which is at most [k J_i+y Q_i]/(1+k). Thus the triples and all
simultaneous events are retained. The first inequality in (5) and
(13) give a strict upper bound A_1=(a*y−h_1*k)/(1+k) for i=1,
because (5) gives a−Q_1≥(1+theta)(h_1+J_1)/nu_3. The second
inequality gives an upper bound theta*y/(1+k)≤theta*y for i=2,
strict if theta>0. Thus for theta>0 BOTH actual outsider Quit endpoints
are strictly below their positive prescribed values A_1 and theta*y.
At theta=0 the second comparison is the exact weak zero bound. No
individual zero collision cap is being silently retained.

## 5. Pivot selection and complete phase values

Put p=1+xi*y and define

    R(y)={p[1−(1−y)(1−z)(1−w)(1−t)]
           −(1−y)[U*z+(1−z)V*w]}
          /{y+(1−y)(1−z)(1−w)t}.                    (14)

Its denominator is strictly positive. Formula (12) shows that it extends
continuously with R(0)=R_low. Direct substitution at k=0,y=Y_theta
gives

    R(Y_theta)−T
       =D[ xi−theta(1−T) ]/(abc+theta).              (15)

Since R_low<T in the nonempty residual case and
xi≥theta(1−R_low), the right side is nonnegative, and strictly
positive if theta>0. The intermediate value theorem therefore selects
an interior y for EVERY R_low<R<T. Neither R(y) monotonicity nor
uniqueness is needed. Fix one such y before choosing any accuracy.

For the selected R, let

    P_D=R*t+(1−t)p
       =1+y[xi+theta(R−1)]/(1+theta*y),
    P_C=V*w+(1−w)P_D,
    P_B=U*z+(1−z)P_C.

All three are at least one: R>R_low and the xi hypothesis give the
first floor, and U,V≥1 give the other two. Equation (14) is precisely
R*y+(1−y)P_B=p, the pivot's joint-row Continue equality.

Use the following four phases, repeated after nonabsorption:

    A: independent hazards x for player 0 and y for player 3;
    B: only player 1, with hazard z;
    C: only player 2, with hazard w;
    D: only player 3, with hazard t.

All coins are private independent behavioral randomization. The full
vectors at the successive phases A,B,C,D are

    V_A=(p,A_1,theta*y,0),
    V_B=(P_B,0,b*z,h_3*k),
    V_C=(P_C,0,0,c*w),
    V_D=(P_D,ell,0,0).                                (16)

The vectors in (16) are in the original player order (0,1,2,3).
At A, the pivot's Quit endpoint is p and player 3's is zero.
Player 3's Continue equality is (1−x)h_3*k−x*h_3=0.
The outsider policy equations are

    V_A,1=(a*y−h_1*k)/(1+k),
    V_A,2=[−h_2*k−y+(1−y)b*z]/(1+k)=theta*y.

The solo recurrences give V_C,1=−w+(1−w)ell=0,
V_D,2=−t+(1−t)theta*y=0, and
V_B,3=−z+(1−z)c*w=h_3*k. Every coordinate has its singleton
floor; every Continue comparison is exact, and every supported Quit
action is indifferent. The two remaining A comparisons were proved
from (5), so these are all joint-row deviations.

## 6. Full behavioral control and the fixed uniform target

Refine ALL THREE solo blocks, not only the first two. In particular,
a pivot deviation at the final solo-3 block can collect the positive
pair premium xi, so leaving that block coarse would not be justified.
For n≥1 replace each aggregate q∈{z,w,t} by n identical hazards
q_n=1−(1−q)^(1/n). The endpoint vectors remain (16). At a solo-j
block with exit vector W and m remaining microstages, the value is

    [1−(1−q)^(m/n)]r({j})+(1−q)^(m/n)W.

This lies on the line segment between that block's original entry and
exit vectors. The owner's value is identically s_j. Thus all singleton
floors, exact policy identities, and exact Continue identities survive.
Let

    C_join=max(0, r_i({i,j})−s_i : j∈{1,2,3}, i≠j),
    e_n=C_join*max(z_n,w_n,t_n).

An outsider's immediate-Quit payoff at a solo-j microstage is
s_i+q_n[r_i({i,j})−s_i], so it is at most its phase value plus e_n.
The unchanged A row has error zero. Adding e_n to every phase value
is a Bellman supersolution: Continue transports only an opponent
survival fraction of that added constant, and Quit already has the
same single cap. Hence no error accumulates across phases or periods.

All x,y,z,w are strictly between zero and one, and 0≤t<1. Removing
any player's hazards leaves a per-period opponent survival rho_i<1,
unchanged by subdivision. Under any complete unilateral behavior,
survival for m periods requires every prescribed opponent to Continue
through those periods, an event of probability at most rho_i^m. The
phase values are bounded, so the terminal remainder in the iterated
supersolution tends to zero uniformly over all deviating strategies.
Exact policy evaluation and the same tail show that the prescribed
terminal payoff is exactly V_A. Every unilateral terminal payoff is
at most (V_A)_i+e_n.

For a direct finite-horizon bound, choose M≥1 bounding all terminal
rewards. Put m_n=1+3n and C_n=max_i m_n/(1−rho_i), counting the
first date as one. Couple any deviation to the opponents' prescribed
coins. Actual absorption occurs no later than their first scheduled
Quit, whose expected date is at most C_n. The profile itself has the
same bound. Its N-stage average payoff, and that of every deviation,
therefore differ from their terminal payoffs by at most 2M C_n/N.
In particular delivery error is at most 2M C_n/N, deviation payoff
is at most (V_A)_i+e_n+2M C_n/N, and regret relative to the actual
profile average is at most e_n+4M C_n/N. Choose n first, then one
N₀ controlling these errors for EVERY N≥N₀. The target V_A has
not changed with n or N₀.
Together with the original singleton degree and passive-inverse exits,
this proves the claimed entire R-axis raw class in ordinary mathematics.

The existing counterpart is
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`,
with fixed-target consumer
`isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`,
both in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
The semantic endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The new input is the construction from raw rewards, not a new refinement
or supersolution compiler.

The Lean handoff is the finite raw predicate (1)–(5), followed by a
helper producing the unique continuous admissible root and bound (13),
then the selected rates and phase vectors (16), then the fixed-target
refined profiles through the named existing consumer. The original-table
source exits in Section 2 complete the all-R UE theorem. The zero-phase
specialization is a direct corollary of the same producer, not a separate
closure adapter. No further strategic witness is an input to this chain.

## 7. The zero-phase boundary and a quadratic formula

At theta=0, formula (11) has t=0 and V_D=V_A exactly. Deleting this
all-Continue block preserves the terminal coalition law and values.
The endpoint test uses only
w≤a*theta*y, so it still has the strictly positive final lower bound
D*nu_2*y/(b*h_1). The strict bound (13) remains valid, even when the
first inequality (5) is equality. The second outsider comparison is
now weak, as required by the supersolution. If also xi=0, (15) gives
R(Y_theta)=T exactly; this still covers the entire open residual
interval. All x,y,z,w remain positive, so all opponent tails contract
without the last block. No reward closure or openness assertion is used.

In particular, the theorem includes the following simpler raw class:
the joint reward is (1,−h_1,−h_2,0), all three player-2 collision
coordinates at 02,23,023 are nonpositive, and
J_1+nu_3 Q_1≤nu_2. The three individual caps imply J_2=0,Q_2≤0,
so choosing theta=xi=0 meets (4)–(5). The resulting target is
(1,w/(1−w),0,0). The new theta=0 class is stronger still: positive
J_2 is allowed if sufficiently negative Q_2 makes J_2+nu_3 Q_2≤0.

At theta=0 the scalar selector also has an explicit quadratic formula.
Set L=bc+c+1, Y=D/(aL), C=b(1−y), E=b−(b+1)y,
d_0=1+a*y and d_1=1−h_1. Then

    z=(h_2*k+y)/C,
    w=(a*y−h_1*k)/(d_0+d_1*k),
    C(d_0+d_1*k)G=alpha*k²+beta*k+gamma,
    alpha=(h_3*C+h_2)d_1−c*h_1*h_2,
    beta=h_3*C*d_0+h_2(d_0+c*a*y)+y+h_1(cE−y),
    gamma=y(aL*y−D).                                   (17)

For 0≤y≤Y, cE−y≥1/a, so beta>0. For interior y, gamma<0.
The admissible cap is min(a*y/h_1,E/h_2); its endpoint has G>0.
If alpha≥0 the polynomial increases on the nonnegative axis. If
alpha<0 the positive value at the cap places the unique admissible
zero before its second crossing. In either case the zero is simple
and has positive derivative. Thus

    k=−2gamma/[beta+sqrt(beta²−4alpha*gamma)]             (18)

is continuous and valid when alpha=0 as well. At y=0,Y it gives zero,
and beta(0)=D*nu_3 gives k/y→1/nu_3. This formula is not needed for
the monotonicity proof, but makes the zero-leading-coefficient boundary
explicit.

## 8. A full-core example with six positive joining coordinates

Use a=b=c=2, h_1=h_2=1, h_3=11465/6552, U=V=2,
theta=1/4, xi=1, and

    x=1/11, y=1/4, z=67/240, w=86/273, t=1/17,
    R=4802/23743,
    nu=(50777,65516,55690)/45864,
    R_low=−60603/55690, T=1/4,
    J_1=1/2, Q_1=5077/11138,
    J_2=1/10, Q_2=16379/111380.

Both inequalities (5) bind, with all four J_i,Q_i strictly positive.
The rate k is 1/10, and xi>theta(1−R_low). The exact vectors are

    V_A=(5/4,4/11,1/16,0),
    V_B=(37971/23743,0,67/120,2293/13104),
    V_C=(34286/23743,0,0,172/273),
    V_D=(479662/403631,86/187,0,0).

Choose r_1(01)=r_1(013)=J_1, r_1(13)=Q_1,
r_2(02)=r_2(023)=J_2 and r_2(23)=Q_2. These are all SIX positive
outsider collision coordinates, which a zero-cap construction
cannot simply ignore. Their A Quit gaps are respectively
52581/245036 and 97953/4900720. Direct substitution in (11), (14),
and the four phase recurrences gives all sixteen policy and all sixteen
Continue identities.

Here a premium trap means a nonempty set A such that every i∈A has
a coalition S⊆A containing i with r_i(S)>s_i. Unions of traps are
traps, so their union is the greatest premium core.

For a full table, give every unspecified participant its singleton and
every unspecified outsider reward zero, then set r_0(01)=r_0(02)=3
and r_3(13)=1/2. Preserve (1), all singletons, and the six specified
collision coordinates. Traps 01,02,13 have empty intersection, so there
is no common player in every premium trap at all, even before any
leave inequality is tested. Their union is the full four-player set.
This completion satisfies the raw conditions and has a full greatest
premium core, while invalidating the signed common-leaver criterion.
It does not claim separation from every conceivable existing producer.

## 9. Further exact boundary tests

The first two tests use theta=xi=0, J=J_1, Q=Q_1, and J_2=Q_2=0.

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
three player-2 collision coordinates at 02,23,023 to zero, and set every
other unspecified coordinate to 37. The twelve nonempty-phase exact
policy and Continue equations still hold. At A, outsider 1's Quit
payoff is 637/8426, below its prescribed
value by 2427/8426. Some coarse solo Quit inequalities fail with this
completion. They are controlled by the solo refinement bound, so this
example genuinely uses refinement of arbitrary unused premiums.

### A vanishing quadratic leading coefficient

Set a=b=c=2, h=(5/9,1,1), U=V=2, J=17/7 and Q=−2.
Then

    nu=(55,59,47)/63,
    R_low=−67/47, T=1/4,
    y=1/4, k=7/50, x=7/57, z=13/50, w=10/37,
    R=−19/50,
    V_A=(1,10/27,0,0).

At the selected y, alpha=0, beta=25/4, gamma=−7/8, so (18) gives
k=−gamma/beta=7/50 without a singularity. Condition (5) is again equality.
This checks a nontrivial zero-leading-coefficient branch, not a limiting
approximation to a nondegenerate polynomial.

### A binding pivot-floor inequality with negative R

Take a=b=c=2, h_1=h_2=1, theta=1, U=V=2, and

    h_3=2989/2592,
    nu=(18541/18144,4933/4536,9469/9072),
    xi=38273/18938=theta(1−R_low),
    R_low=−19335/18938,
    R=−58011473/139554122<T=1/4,
    x=3/28, y=1/10, z=83/450, w=19/96, t=1/11.

Both raw caps bind with all six outsider collision coordinates positive:

    J_1=397/18144, Q_1=397/9469,
    J_2=9469/36288, Q_2=1/2.

Give both max entries defining J_i the value J_i. The joint outsider
safety margins are 104775191/1603518336 and 46399/1693440. The final
pivot floor is strict despite negative R and equality in (4):

    P_D−1=3839461/69777061>0.

The unrefined final solo-3 block has a positive pivot Quit gain. Thus
refinement of that third block is indispensable.

### Signed caps and a strengthened zero-phase case

For a signed two-buffer test, take a=b=c=2, h_1=h_2=1,
h_3=2320/873, U=2,V=3, theta=1/3, xi=2. Then

    nu=(7558,11899,9005)/6111,
    R_low=−22351/9005<R=−939/2983<T=0,
    y=1/5, k=1/12, x=1/13, z=2/9, w=83/291, t=1/16,
    Q_1=Q_2=−1, J_1=6289/2716, J_2=9005/6111.

Both caps bind. The four vectors are

    V_A=(7/5,19/65,1/15,0),
    V_B=(5455/2983,0,4/9,580/2619),
    V_C=(5309/2983,0,0,166/291),
    V_D=(7713/5966,83/208,0,0).

The two joint outsider Quit payoffs are −1147/176540 and
−28307/397215. They are below the positive target coordinates.

For a distinct theta=xi=0 test, use the first asymmetric example in
this section but change J_2 to 1 and Q_2 to −315/383. The second
weighted cap still binds, despite positive player-2 joining rewards
at 02 and 023. Its exact joint Quit payoff is −809/8426<0, while
(V_A)_2=0. This proves that the boundary comparison is not relying
on hidden individual zero caps.

## 10. A zero-phase full-core example

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
    r_3({1,3})=1/2.                                   (19)

This table satisfies (1), (4), and (5) at theta=xi=0:
nu=(1,1,1), J_1=1, Q_1=0, and J_2=Q_2=0.
Its rates can be selected algebraically. Put

    y=(3−sqrt(5))/2,
    k=y(1−2y), x=k/(1+k), z=w=y.

The identity y=(1−y)² verifies the scalar and pivot equations, and the
target is (1,y/(1−y),0,0). The additions (19) at 12 and 13 are handled by
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
