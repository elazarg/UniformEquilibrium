# Boundary two-phase equilibria funded by negative pair responses

Status: complete ordinary mathematics.

## 1. Exact statement and raw input region

Every finite signed four-player quitting reward table satisfying the
explicit raw inequalities below has an exact absorbing terminal Nash
profile against all unilateral complete behavioral replacements. The
profile alternates a phase with one mixing player and a phase with two
independently mixing players; the remaining player always Continues.
Its terminal payoff is one uniform-equilibrium payoff target.

The hypotheses involve only literal reward coordinates and finite
arithmetic, absolute values, minima and square roots of those coordinates.
They do not assume a strategic root, continuation vector, inverse matrix,
or supplied certificate. The construction permits one unbounded positive
passive pair reward, an above-own queried triple reward proportional to
that passive reward, arbitrary signed own levels, three free opponent
singleton coordinates and thirty-one free nonsingleton coordinates.
It contains a full open region in all sixty raw reward coordinates.

There are four players 0,1,2,3. Every nonempty coalition S has an arbitrary
finite reward vector r(S); the all-Continue play and literal AllNever pay
zero. Every player independently privately samples a complete stopping
clock. Write s_i=r_i({i}) and

    Gamma_ij=r_i({j})-s_i,       i!=j.

Use the following six strictly signed singleton data:

    Gamma_02=-b_2, Gamma_03=-b_3,
    Gamma_20=-d_2, Gamma_30=-d_3,
    Gamma_23=a_2,  Gamma_32=a_3,

    b_2,b_3,d_2,d_3,a_2,a_3>0.                         (1)

The other three queried singleton data, belonging to observer one, are

    g_10=Gamma_10, g_12=Gamma_12, g_13=Gamma_13.

The three remaining singleton data Gamma_01,Gamma_21,Gamma_31 are free.
The own levels s_i are arbitrary finite real numbers. Define five queried
nonsingleton inputs by

    p_i=r_i(23)-s_i>a_i,  c_i=p_i-a_i>0,  i=2,3,
    K_0=r_0(23)-s_0,
    K_1=r_1(23)-s_1,
    Pi_1=r_1(01)-s_1.                                    (2)

K_1 and Pi_1 may have either sign. In particular no raw singleton inverse,
nonnegative payoff, proper four-owner root, or supplied strategic object
is assumed. Define from these raw data

    rho_i=d_i/a_i,
    C_i=[3 rho_i(d_i+p_i)+9 c_i rho_i^2]/a_i,  i=2,3,

    T_0=g_10+g_12 rho_3+g_13 rho_2>0,
    D_max=1+3rho_2+3rho_3+9rho_2rho_3,
    beta=T_0/(2D_max)>0,
    E=|g_12|C_3+|g_13|C_2+9|K_1|rho_2rho_3,
    P_1^+=max(Pi_1,0).                                   (3)

The observer hypothesis is precisely the displayed strict inequality
T_0>0. The small time threshold is the following explicit RAW number:

    u_0=min(1/2,
       a_2/[4(d_2+p_2)], a_3/[4(d_3+p_3)],
       a_2^2/[16c_2d_2], a_3^2/[16c_3d_3],
       T_0/[2(E+1)],
       beta/[2(beta+|g_10|+1)],
       beta/[4(P_1^++1)])>0.                             (4)

All denominators are positive. For 0<u<=u_0 set

    Delta_i(u)=[a_i-u(d_i+p_i)]^2-4c_iud_i,

    Y_i(u)=2ud_i/
      [a_i-u(d_i+p_i)+sqrt(Delta_i(u))],  i=2,3.           (5)

The square roots are positive, as proved below. Hence the final raw
passive threshold is an explicitly finite radical expression:

    K_crit=b_2/Y_2(u_0)+b_3/Y_3(u_0).

Assume

    K_0>K_crit.                                          (6)

The complete remaining reward guards consist of the following EIGHT
coordinate inequalities, computed before the strategy is produced:

    r_0(02)<=s_0-b_2,
    r_0(03)<=s_0-b_3,
    r_0(023)<=s_0+K_0/2,

    r_1(12), r_1(13), r_1(123)<=s_1+beta/4,

    r_2(02)<=s_2+c_2rho_2/2,
    r_3(03)<=s_3+c_3rho_3/2.                              (7)

All thirty-one other nonsingleton coordinates are arbitrary finite
numbers. Thus (1)--(7) specify the entire sixty-coordinate raw
region: four free own levels, nine constrained/used singleton data,
three free singleton data, five used nonsingleton inputs, eight capped
nonsingleton coordinates and thirty-one free nonsingleton coordinates.
The coordinate r_0(023) is allowed strictly ABOVE s_0 by an allowance
growing linearly with the unbounded positive passive K_0. This is paid
for by the two below-own pair caps; its cap has not been replaced by an
own-level assumption.

## 2. Explicit positive inverse branches and hazard production

For 0<u<=u_0,

    a_i-u(d_i+p_i)>=3a_i/4,
    4c_iud_i<=a_i^2/4,
    Delta_i(u)>=5a_i^2/16>0.                              (8)

The positive number Y_i is the SMALL root of

    c_iY^2+[u(d_i+p_i)-a_i]Y+ud_i=0.                     (9)

Its denominator in (5) is at most 2a_i and at least 3a_i/4. Therefore

    rho_i u<=Y_i(u)<3rho_i u.                            (10)

Implicit differentiation of (9), using the small-root identity
2c_iY_i+u(d_i+p_i)-a_i=-sqrt(Delta_i), gives

    Y_i'(u)=[d_i+(d_i+p_i)Y_i(u)]/sqrt(Delta_i(u))>0.      (11)

Equivalently, these are the explicitly increasing small branches of

    h_i(Y)=Y(a_i-c_iY)/[d_i+(d_i+p_i)Y].

No global monotonicity of the other quadratic branch is used. Dividing
(9) by a_i u gives the useful error estimate

    0<=Y_i(u)/u-rho_i
       =u[(d_i+p_i)(Y_i/u)+c_i(Y_i/u)^2]/a_i
       <=C_i u.                                         (12)

The raw function

    K(u)=b_2/Y_2(u)+b_3/Y_3(u)

is continuous and strictly decreasing on (0,u_0], and tends to infinity
as u decreases to zero. Its value at u_0 is K_crit. Thus (6) produces
a UNIQUE u in (0,u_0) with K(u)=K_0. Set

    X_2=Y_3(u), X_3=Y_2(u),
    q_2=X_2/(1+X_2), q_3=X_3/(1+X_3).                    (13)

The row index of Y is intentionally opposite its hazard owner: row two
responds to player three, and row three responds to player two.

At every even date, only player zero mixes, using hazard u. At every
odd date players two and three independently use hazards q_2 and q_3.
Player one always Continues. These independent periodic hazards define
independent complete stopping clocks. Players zero, two and three have
proper hazards at their own phases; player one is literal Never. No
public random signal, root reordering, or correlation has been introduced.

## 3. Observer values and the positive limit inequality

Put R_2=X_2/u, R_3=X_3/u. Define

    B=[g_10+g_12R_2+g_13R_3+K_1uR_2R_3]/
      [1+R_2+R_3+uR_2R_3],
    A=g_10u+(1-u)B.                                      (14)

These are finite numbers. Indeed, the denominators are positive and
(10)--(12) give

    rho_3<=R_2<3rho_3,  rho_2<=R_3<3rho_2,
    |R_2-rho_3|<=C_3u,  |R_3-rho_2|<=C_2u.

The numerator of B is at least T_0-Eu>T_0/2 by (4), and its denominator
is at most D_max since u<1. Consequently

    B>=beta,
    A>=beta-u(beta+|g_10|)>beta/2,
    Pi_1u<=P_1^+u<beta/4.                                (15)

This is the promised explicit positive observer margin. It is not an
assumed positivity of a continuation supplied by an external verifier.

Let C=(1-q_2)(1-q_3) and

    P=g_12q_2(1-q_3)+g_13q_3(1-q_2)+K_1q_2q_3.

Multiplying (14) by its positive denominator verifies exactly

    A=g_10u+(1-u)B,     B=P+CA.                           (16)

This retains the actual simultaneous coalition 23 and its observer
reward K_1, of either sign. In particular it is not replaced by a
singleton-only approximation.

## 4. Exact phase policy equations and all sixteen endpoints

Let A denote the phase where only zero has a positive hazard and B the
phase where two and three have positive hazards. The proposed ORIGINAL
phase payoff vectors are

    v^A=(s_0,s_1+A,s_2+c_2X_3,s_3+c_3X_2),
    v^B=(s_0,s_1+B,s_2+p_2q_3,s_3+p_3q_2).               (17)

We check both actions for every player at both phases. A Continue
endpoint uses the NEXT phase value if nobody else quits. A Quit
endpoint always retains every actual joining coalition.

For player zero at A, the Quit endpoint is s_0 and the Continue endpoint
is v^B_0=s_0, so its proper mixing is supported. At B its Continue
endpoint minus s_0 equals

    -b_2q_2(1-q_3)-b_3q_3(1-q_2)+K_0q_2q_3=0,           (18)

because K_0=b_2/X_3+b_3/X_2. Its Quit endpoint, by the three actual
caps in (7), is at most s_0 plus

    -b_2q_2(1-q_3)-b_3q_3(1-q_2)+(K_0/2)q_2q_3
       =-(K_0/2)q_2q_3<0.                               (19)

Thus its prescribed Continue at B has a strict endpoint margin even
though r_0(023) may be above its own singleton.

For player one at A, the Continue endpoint is s_1+A by (16), while
the Quit endpoint is s_1+Pi_1u<s_1+beta/4. Its Continue value is greater
than s_1+beta/2 by (15). At B the Continue endpoint is s_1+B, at least
s_1+beta. Its Quit endpoint is at most s_1+beta/4: the no-opponent event
gives precisely s_1, and each of the other three events is bounded by
the three actual row-one caps in (7). Thus literal Never is supported
at both phases, with strict inequalities at both endpoints.

For player i=2,3 let j be the other member of {2,3}, so X_j=Y_i. At B
its Quit endpoint is s_i+p_iq_j. Its Continue endpoint is

    s_i+a_iq_j+(1-q_j)c_iX_j=s_i+p_iq_j,

since (1-q_j)X_j=q_j. Thus its proper mixing at B is supported. At A
its Continue endpoint minus s_i is

    -d_iu+(1-u)p_iq_j=c_iX_j,                            (20)

which is exactly (9) after multiplication by 1+X_j. Its Quit endpoint
is at most s_i+(c_i rho_i/2)u by its actual pair cap in (7). Since
X_j>=rho_i u, the strict Continue margin is at least

    c_i rho_i u/2>0.                                     (21)

This accounts for all sixteen action endpoints: four A endpoints for
zero/one, four B endpoints for zero/one, and four endpoints each for
players two and three. Every prescribed action has maximizing endpoint
payoff, and every phase policy recursion in (17) holds exactly.

## 5. Actual laws, unrestricted deviations and one uniform target

The cycle survival products of the opponents after deleting one owner
are respectively

    kappa_0=(1-q_2)(1-q_3),
    kappa_1=(1-u)(1-q_2)(1-q_3),
    kappa_2=(1-u)(1-q_3),
    kappa_3=(1-u)(1-q_2).                                (22)

Each lies strictly below one; joint survival equals kappa_1. Iterating
the policy recursion therefore identifies (17) with the ACTUAL
terminal payoff vectors, independently of an arbitrary bounded terminal
continuation. For a unilateral behavioral replacement, its conditional
two-action payoffs are bounded by the same phase value by Section 4.
Iterating that Bellman inequality for n cycles leaves a remainder
bounded by a fixed reward bound times kappa_i^n, uniformly over the
replacement. This tends to zero. It prices every finite deadline,
literal Never, arbitrary mixtures of deadlines, and the equivalent
complete behavioral strategy in the unique live history. Thus the
profile is exact terminal Nash against ALL independent-clock law
replacements, not merely its supported phase hazards.

Opponent absorption has a geometrically bounded mean independently of
the deviating owner's law. For every owner i, the discrepancy between
its N-stage average payoff and its terminal payoff is bounded by a
constant times E[min(T_opp,N)]/N and hence by a constant/N. The same
holds for the prescribed profile. The common even-phase terminal vector
v^A is consequently a single uniform-equilibrium payoff target, with
these same periodic laws and sufficiently long horizons for every
positive accuracy. No accuracy-dependent target is being selected.

The use of r_i(S)-s_i in the algebra does not alter the payoff convention:
live and literal AllNever still pay zero. Every actual prescribed or
unilaterally deviating play here faces surely absorbing opponents, so
each full terminal response receives the same row offset s_i. This is
the precise reason arbitrary signed own levels are legitimate.

The exact tracked compiler matching this proof is
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`: exact
phase policy recursion, phase Nash with NEXT phase values, and
playerwise opponent-cycle contraction. No global proof is inferred
from a supplied certificate: Sections 1--4 produce all its data
from the literal raw table.

## 6. Nonemptiness and open sixty-coordinate scope

For a concrete raw choice put

    a_2=a_3=3, b_2=b_3=d_2=d_3=1,
    p_2=p_3=4,
    g_10=3, g_12=g_13=-1,
    K_1=-1/10, Pi_1=4.

Then rho_2=rho_3=1/3, C_2=C_3=2, T_0=7/3, D_max=4,
beta=7/24, E=41/10 and u_0=7/480. The branch lower bounds give

    K_crit<=2880/7<500.

Thus K_0=500 satisfies (6), and every cap can be satisfied STRICTLY.
For instance choose normalized capped coordinates

    r_0(02)-s_0=r_0(03)-s_0=-2,
    r_0(023)-s_0=1,
    r_1(12)-s_1=r_1(13)-s_1=r_1(123)-s_1=beta/8,
    r_2(02)-s_2=r_3(03)-s_3=1/12.

All the remaining free finite coordinates may be selected independently.
There are no hidden equality constraints on the sixty raw coordinates:
all equalities in the statement DEFINE the parameters from the rewards.
The strict sign and observer guards are open; the explicit positive
functions u_0,Y_i(u_0),K_crit,beta are continuous on their domain, even
at a switch of the finite minimum defining u_0. Consequently every table
with strict versions of (7), such as the example, has a full
sixty-dimensional open raw neighborhood inside the proved region.

Sections 7--9 provide a complete positive-own calibration, exact finite
prior-coverage comparisons, and boundary tests. The full arbitrary-table
conjecture remains open.

## 7. A complete positive-own calibration

The following literal table supplies all sixty finite coordinates, for
every finite real M>=202500. Define a centered table Z and set

    r_i(S)=1+Z_i(S)  for EVERY nonempty S.

The live reward and AllNever payoff stay zero. Let mate interchange
0 with 1 and 2 with 3, and put epsilon=7/192. Singleton rewards are

    Z_i({i})=0,
    Z_i({mate(i)})=3,
    Z_i({j})=-1 for every other j.

At pair 01, its two participants receive 4 and the passive recipients
2,3 receive -1/10,1/10 respectively. At pair 23, its participants receive
4 and passive recipients 0,1 receive M,-1/10 respectively. At the four
cross pairs, every passive recipient receives -2; the participant rewards
are exactly

| Coalition | First participant reward | Second participant reward |
| --- | --- | --- |
| 02 | Z_0=-101/100 | Z_2=1/12 |
| 03 | Z_0=-101/100 | Z_3=1/12 |
| 12 | Z_1=epsilon | Z_2=1 |
| 13 | Z_1=epsilon | Z_3=1 |

Every passive triple recipient receives -3. Every participant triple
coordinate equals -1, with precisely four exceptions:

    Z_0(023)=1,
    Z_1(123)=epsilon,
    Z_2(012)=epsilon,
    Z_2(123)=-4.

The grand-coalition vector is (-4,-2,-2,-2). These disjoint rules exhaust
four singleton vectors, six pair vectors, four triple vectors and one
grand vector, with no unspecified coordinate.

The parameters of Section 6 apply, with K_0=M, K_1=-1/10, Pi_1=4 and
all other used singleton and participant inputs as displayed there.
Thus beta=7/24, u_0=7/480 and K_crit<=2880/7<202500. All eight cap
inequalities are STRICT: -101/100<-1; 1<M/2; epsilon<beta/4=7/96; and
1/12<c_i rho_i/2=1/6. Every table in this calibration consequently lies
in a full sixty-coordinate open part of the theorem's region. In
particular its own singleton rewards are strictly positive, so literal
AllNever is not an equilibrium.

This completion has no pure date-zero absorbing coalition Nash. Here is
a complete census of profitable one-date deviations. At a singleton,
its mate joins for centered reward 4 instead of 3. At pair 01 outsider
two joins from -1/10 to epsilon; at pair 23 outsider one does the same.
At cross pair 02 or 03 outsider one joins from -2 to -1. At cross pair
12 or 13 outsider zero does the same. At triples 012,013,023 the missing
owners 3,2,1 respectively join from -3 to their grand reward -2. At
triple 123 member two withdraws from -4 to the passive pair-13 value -2.
At the grand coalition owner zero withdraws from -4 to its passive
triple-123 value -3. The common offset one cancels in every comparison.
All fifteen nonempty coalitions are covered, and every comparison is
strict. This is not a claim of absence of all stationary mixed profiles.

## 8. Exact bounded prior-coverage comparisons

The comparisons below concern the complete calibration of Section 7,
and the indicated full finite sets of selections. They are not used as
assumptions in the proof. Some lower completions of the theorem's broad
cap region can overlap existing criteria; no disjointness of the entire
region is asserted. Positive row-affine transformations and relabelings
are retained throughout: differences from own/passive entries scale by
a positive factor, and selections are exhausted before any criterion is
rejected.

### 8.1. All partitions of own-level inactive caps

For partition 01|23 the own-level inactive triple cap at receiver zero
fails, because Z_0(023)=1>0. For partition 02|13, the inactive pair tests
at receiver zero include Z_0(01)=4>0; the same test fails for partition
03|12. Thus the two-pair own-level joining-cap criterion fails on ALL
three partitions, as do the crossed-matching or signed-inverse variants
that require these own-level caps or a still smaller nonnegative buffer.
The present theorem instead prices the actual positive triple endpoint
using the two negative pair responses in (19).

The graph-free proper-flat guard also fails: at A={0,1}, both participant
pair rewards are 4 above own zero, so neither member has all its own
participant rewards within A at most own. The same failure holds at
A={2,3}. No choice of weights or flattening chart removes these literal
strict participant comparisons.

### 8.2. Full and proper inverse selections

The centered singleton matrix is

    Gamma=[[0,3,-1,-1],
           [3,0,-1,-1],
           [-1,-1,0,3],
           [-1,-1,3,0]].

It has determinant 45 and inverse

    Gamma^-1=[[2/15,7/15,1/5,1/5],
              [7/15,2/15,1/5,1/5],
              [1/5,1/5,2/15,7/15],
              [1/5,1/5,7/15,2/15]].                     (23)

These identities follow by direct matrix multiplication. In particular,
the full nonnegative-singleton-inverse criterion requiring NEGATIVE
determinant fails, even though every inverse entry is strictly positive.
This comparison uses the determinant hypothesis in
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse` in
`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`.

Every proper triple is, after permutation,

    T=[[0,3,-1],[3,0,-1],[-1,-1,0]],
    T^-1=[[-1/6,1/6,-1/2],
           [1/6,-1/6,-1/2],
           [-1/2,-1/2,-3/2]].

Thus every triple inverse has a negative entry. Its outside singleton
row is (-1,-1,3), and its inverse weight is

    (-1,-1,3)T^-1=(-3/2,-3/2,-7/2)<0.                    (24)

This exhausts all FOUR proper child selections in
`exists_labeledCycle_uniformPayoff_of_raw_strictInverse_triple` and
`exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
Failure of these sufficient inverse guards does not exclude all possible
proper-child strategies or all punishment-tail consumers.

The signed full-inverse criterion requires signs sigma such that
Gamma^-1 diag(sigma)>0, positive signed scheduled joining increments,
and nonpositive signed passive pair differences. By (23) EVERY sign is
forced to +. In partition 01|23 the positive passive K_0=M violates the
last guard. In each cross partition the joining difference at receiver
zero is -101/100-(-1)=-1/100<0, violating the positive joining guard.
This rejects every sign choice and every partition. The constant-inverse
criterion with nonnegative participant premiums and nonpositive passive
premiums also fails: at 01|23 the passive M is positive, and at each
cross partition receiver zero's participant premium is negative.

### 8.3. Moving-matrix and fixed matching regions

The nonmatching two-positive-passive cone criterion asks that all
coefficients of the determinant and adjugate of a specified two-entry
positive update to Gamma be nonnegative, with the needed positive
constant coefficients. It also asks for nonnegative scheduled participant
premiums. For either cross partition, receiver zero's scheduled premium
is -101/100<0. For partition 01|23 its positive passive reward M uses
an update in row zero and either opposite column 2 or 3. Already with
the second update set to zero, direct cofactor expansion gives

    adj(Gamma+t E_02)_(1,1)=6-3t,
    adj(Gamma+t E_03)_(1,1)=6-3t.                         (25)

Hence the coefficient condition fails for BOTH possible opposite-column
placements. Renaming the designated positive rows does not change this
physical row-zero obstruction. The second positive row, receiver three,
cannot repair a negative coefficient obtained by setting its update to
zero. This exhausts the finite update placements after all relabelings.
It does not reject some other nonlinear, bounded-update or alternate
calendar use of inverse positivity.

The ordered-pair raw region in
`RawRegion.eq_partner_of_singleton_lt` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean` permits
at most one below-own singleton column in each recipient row. Every
row of Gamma has TWO, so no schedule ordering or positive row-affine
map admits that region.

The strict/weak matching-sign source with a negative scheduled singleton
also fails. Such a schedule must be one of the cross partitions, because
the only positive singleton columns are the original mates. At either
cross partition receiver zero's participant reward is strictly LESS
than its scheduled passive singleton: -101/100<-1. This violates even
the weak scheduled joining comparison. These exact guards are present
in `RawSource`, `WeakRawSource` and `InverseRawSource` in
`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`.

For the common-parameter asymmetric paired family, the positive singleton
graph fixes the positive pairing 01|23, and all four scheduled joining
increments in this calibration are exactly one. They cannot satisfy a
strict asymmetry e<c, under any positive row-affine chart sending its
singleton pattern to a common a,b: equality of all cross singleton
levels forces the row scales equal. Its common passive parameter also
cannot equal M,-1/10,-1/10,1/10 simultaneously. A cross partition fails
its positive joining increment at receiver zero instead. A positive
row-affine image of its independent small raw box is excluded separately:
that box's mate/cross singleton ratio lies near 5, whereas the invariant
ratio here is exactly 3. For example a box of absolute radius 10^-6
about a=3,b=3/5 has ratio at least

    (3-2*10^-6)/(3/5+2*10^-6)>4,

so it cannot contain any affine image of this calibration.

### 8.4. Weighted insertion, sure-owner and whole weak-unit guards

Let d_ij=Z_i({i,j})-Z_i({j}), d_ii=0. Directly from the complete table,

    d=[[0,1,-1/100,-1/100],
       [1,0,199/192,199/192],
       [13/12,2,0,1],
       [13/12,2,1,0]],

    d*1=(49/50,295/96,49/12,49/12)>0.                    (26)

If nonnegative nonzero recipient weights w satisfied every singleton
insertion inequality w^T d<=0, multiplication by the positive vector
1 would contradict (26). This rejects EVERY nonzero nonnegative
weighting in the H/J, weighted-floor-return and full-trap insertion
guards requiring those inequalities. The two disjoint strict participant
premium traps {0,1} and {2,3} also force the greatest premium core to
contain all four players: no nonempty part of either pair is removable
by a rule requiring all remaining participant rewards at most own.

The whole weak-unit joining guard requires one ordered receiver i and
partner j for which adding i never raises i's reward on ANY opponent
set containing j. At every ordered pair except (0,2),(0,3), the singleton
joining entry in d is already positive. At (0,2), take opponent set
{1,2}: joining changes receiver zero's reward from -2 to -1. At (0,3),
take {1,3} with the same improvement. This exhausts all TWELVE ordered
selections of `QuittingWeakUnitJoining` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitRawGuards.lean`
and its producer in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.
The guard fails in
every case. No absence of arbitrary stationary Nash profiles is asserted.

The instant no-join root necessary for
`IsQuittingInstantNoJoin` in
`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`
fails for every selected sure quitter j: its mate joins for 4 instead
of passive singleton 3. This rules out that root comparison independently
of any punishment law later chosen for that root.

Every owner-solo geometric rate is also excluded by the exact affine
inactive criterion in
`isεAsymptoticNash_soloStationary_exact_iff` in
`UniformEquilibrium/Quitting/Punishment/OwnerSoloCertification.lean`.
For candidate owners 0,1,2,3 choose observers 2,2,1,1 respectively.
Their passive singleton comparison is -1, whereas their forced Quit
mixture is nonnegative at every rate in [0,1], since their own centered
singleton is zero and their pair participant premium is positive.
Thus it always strictly exceeds -1. This is a full scalar-rate exclusion,
not merely a failed selected rate.

### 8.5. Precise meaning of the increment

The new raw region permits one literal Never owner, an unbounded passive
reward, an above-own triple funded by negative pair response values,
and independent variation in all sixty reward coordinates. The complete
calibration supplies exact all-selection exclusions for the finite raw
criteria just listed, rather than a nominal shape difference or the
failure of one supplied strategy. The existence proof produces all
strategic data for every table in the region.

These comparisons do not classify every stationary mixed equilibrium,
every arbitrary punishment tail, every proper-child repair, every local
implicit-function neighborhood or every thresholded sparse-jackpot
criterion. In particular no pointwise noncoverage of a theorem with an
existential asymptotic size threshold follows from a different reward
shape. No universal strategy-class noncoverage or positive-gap game is
claimed. The arbitrary signed four-player problem remains open.

## 9. Exact boundary tests and limits of the mechanism

The rational example in Section 6 has an especially simple produced
root when K_0=500:

    X_2=X_3=1/250, q_2=q_3=1/251,
    u=749/63750<7/480.

Indeed K(u)=2/(1/250)=500, and substitution in (9) verifies both
quadratics exactly. Thus the small inverse branches and actual hazards
are not asserted only through an abstract certificate or numerical root.
All the cap comparisons were proved at their upper boundaries, so weak
inequality in (7) is part of the theorem, including arbitrary signs of
K_1 and Pi_1. Strict versions are used only for the open-region claim.

The observer hypothesis cannot simply be omitted from this construction.
Keep the positive six singleton signs and p_i>a_i fixed, but choose
T_0<0. As K_0 tends to infinity on the same small branches, u tends to
zero, X_2/u tends to rho_3 and X_3/u tends to rho_2 by (12). The observer
values tend to

    A,B -> T_0/(1+rho_2+rho_3)<0,

whereas its phase-A immediate-Quit premium Pi_1u tends to zero. It then
has a strictly profitable actual deviation. This is a counterexample
to extending THIS producer after deleting T_0>0, not to equilibrium
existence for that altered table. The equality case T_0=0 is not settled
by the asserted positive-margin bounds.

The negative pair funding in row zero is likewise essential to the
stated endpoint calculation. If its two queried participant pair
premiums are raised to zero while retaining a strictly positive queried
triple premium, its B-phase Quit endpoint is strictly above s_0 because
q_2q_3>0. Its constructed Continue endpoint remains s_0. Thus replacing
the two negative pair caps by own-level caps would invalidate this exact
calendar despite leaving its policy recursion untouched. The cap
r_0(023)<=s_0+K_0/2 is justified by (19), not by ignoring the joining
triple or by a statement that every queried reward is at most own.

The parameter restriction K_0>K_crit is a finite sufficient bound for
the explicit SMALL branches; no necessity for all Nash laws is claimed.
Both negative passive K_1 of arbitrarily large magnitude and arbitrary
Pi_1 are allowed because (4) shrinks u_0 before the threshold is computed.
The other thirty-one higher coordinates can be arbitrarily large with
either sign. Every coalition exposed to a recipient's unilateral
deviation was already listed among that recipient's endpoint queries.
Each other coalition would require another owner to quit at a phase
where its prescribed hazard is zero, either because that owner is
literal Never or because its positive hazards occur only at the other
phase. These are genuinely free inputs, not omitted bounded error terms.

## 10. Source correspondence and Lean handoff

The probability model is the standard private independent complete-clock
model: a law on nonnegative integers together with Never for each player,
the first finite date determines the simultaneous quitting coalition,
and no finite clock means zero payoff. A unilateral deviation replaces
one entire clock law. In the associated behavioral game there is only
one nonabsorbed public history at each date, so those deviations agree
with arbitrary live-history hazards; randomization after absorption has
no payoff effect. All sixteen actual endpoint rewards and all four
opponent contraction factors were retained above.

The named existing semantic consumers are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`. They accept
arbitrary finite cycles with exact root policy recursion, exact root
Nash using the NEXT phase's vector, and strictly contracting opponent
cycle products. They have no requirement that every owner mix or quit.
Sections 2--5 produce every strategic input and prove those hypotheses
directly from the raw reward inequalities, including player one's
literal Never law. No unproduced certificate, cap vector, matrix inverse,
continuation selection or strategic root remains.

The mathematical scope missing from a supplied periodic verifier is the
raw-data producer here: the quadratic inverse branches, an explicit
pre-root threshold for a positive passive reward, the observer's
positive-limit condition, and the negative-pair-funded positive triple
cap. No existing verifier is being described as a producer on these
raw inputs. The exact guards used for bounded prior comparisons were
reproduced in Section 8, including all finite selections relevant to each
comparison.

A formalization should define the raw parameters as reward differences,
prove (8)--(12) as scalar lemmas for the smaller quadratic root, obtain
the unique u by the one-dimensional intermediate value theorem, and
construct the two phase roots and vectors (17). The sixteen endpoint
inequalities and four contractions then instantiate the named periodic
compiler. A raw-region structure should contain only (1)--(7), not the
desired root or target as a field. The final theorem should assert an
actual terminal Nash profile and a uniform-equilibrium payoff for every
finite table in that region. Relabelings inherit the corresponding
relabelled profile. A positive recipient rescaling and arbitrary
recipient offset of a certified table inherit the SAME hazards and the
affine-transformed target, because every unilateral response still
absorbs surely. This affine-closure conclusion does not assert that the
conservative finite guards themselves are scale invariant: the literal
constants +1 in (4) can change whether a rescaled input passes the same
u_0 test. No new Lean theorem, implementation or build check is claimed
here.
