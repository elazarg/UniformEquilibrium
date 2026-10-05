# Two joint phases produce a full reward-table neighborhood

## 1. Statement and strategic model

Let I={0,1,2,3}. A quitting game has one live state. At every live
date each player independently chooses Continue or Quit. The first
nonempty coalition S of quitters absorbs with reward vector r(S),
which is received thereafter. Never absorbing has terminal reward zero.
Strategies and unilateral deviations may be arbitrary behavioral
strategies. No public correlation or extra information is added.

The raw reward space has sixty real coordinates: four recipients for
each of the fifteen nonempty coalitions. For the explicit rational
table r_star in Section 2, there is an open neighborhood U of r_star
in this ENTIRE space such that every r∈U has a uniform-equilibrium
payoff. More explicitly, for each r∈U there is one vector V(r) such
that, for every epsilon>0, a behavioral profile and a horizon threshold
exist which deliver V(r) within epsilon and have unilateral regret at
most epsilon at every larger finite horizon.

All sixty coordinates may vary independently, including own singleton
rewards and every simultaneous-coalition reward. The target is fixed
before the accuracy but may depend on r. The proof constructs a smooth
local branch of four aggregate phases and refines only two solo phases.
It does not assume that existence of uniform equilibria is open, and
it asserts no explicit numerical radius or universal strategy grammar.

## 2. The complete rational table

Put

    h_1=889/4162,    h_2=12969/8324,    h_3=445/493,
    xi=100/281,     eta=50/493,         R=−94/281.

The center is the following complete table. Coalition digits name
players, not cardinalities.

| S | r_star(S) |
|---|---|
| 0 | (1,−h_1,−h_2,−h_3) |
| 1 | (2,0,2,−1) |
| 2 | (2,−1,0,2) |
| 3 | (R,2,−1,0) |
| 01 | (0,−1,0,0) |
| 02 | (0,0,−1,0) |
| 03 | (1+xi,−h_1,−h_2,eta) |
| 12 | (0,1/2,1/2,0) |
| 13 | (0,−1,0,−1/2) |
| 23 | (0,0,−1/2,−1) |
| 012 | (0,−1,−1,0) |
| 013 | (0,1/10,0,−1) |
| 023 | (0,0,1/10,−1) |
| 123 | (0,−1,−1,−1) |
| 0123 | (0,−1,−1,−1) |

Its own-singleton vector is (1,0,0,0). The aggregate cycle is

    A: joint {0,3}, rates x=1/10 and y=1/4;
    B: solo 1, rate z=1/3;
    C: solo 2, rate w=1/3;
    D: joint {0,3}, rates e=1/100 and f=1/20.

After every nonabsorbing date the next phase is used, cyclically. All
coins are private and independent. The actual phase values are

    V_A=(306/281,892/2081,144/2081,5/493),
    V_B=(1318/843,0,2/3,55/493),
    V_C=(378/281,0,0,329/493),
    V_D=(286/281,1/2,0,1/986).                         (1)

These satisfy all sixteen policy equations and all sixteen
forced-Continue equations. Both supported actions at each of the
six mixing occurrences are indifferent. The four joint-row outsider
Continue-minus-Quit margins are

    A, player 1: 604439/832400;
    A, player 2: 105797/416200;
    D, player 1: 11179/20000;
    D, player 2: 171/5000.                             (2)

They are strictly positive. All phase coordinates are at least their
own-singleton values. The only binding floors are

    V_B,1=V_C,1=0,       V_C,2=V_D,2=0.               (3)

Every other floor is strict. The solo rows need not pass their coarse
outsider tests: the two positive participant premiums at coalition 12
will instead be handled by refinement.

Two genuinely joint rows matter structurally. If a solo-3 mixing
phase were placed immediately before A, its indifference would force
V_A,3=s_3. But A's forced-Quit value is s_3+x[r_3(03)−s_3].
At a positive x, the two statements force the exact reward equality
r_3(03)=s_3. The second joint row removes this restriction.

## 3. Elimination for arbitrary raw tables

For ANY table r, write s_i=r_i({i}) and use centered coordinates

    c_i(S)=r_i(S)−s_i.

This is only algebraic notation. The game is not translated, Never
still pays zero, and actual phase values will be V=s+v. All Bellman
identities below are original-game identities: the continuation and
terminal coalition masses sum to one at each date.

Define from the actual raw table

    xi=c_0(03),  eta=c_3(03),  H=−c_3(0),  L=c_0(3).

At the center xi,eta,H are positive and L=−375/281<0. For
variables x,y near 1/10,1/4 put

    e=eta*x/[H+eta+eta*x],
    f=xi*y/[xi−L+xi*y],
    C_A=(1−x)(1−y),       C_D=(1−e)(1−f).             (4)

For i=1,2 define the centered absorbing contribution of a joint row

    B_i(q,t)=q(1−t)c_i(0)+(1−q)t*c_i(3)+qt*c_i(03).

Now put

    a_1=B_1(x,y),
    d_1=B_1(e,f)+C_D*a_1,
    a_2=−B_2(e,f)/C_D,
    w=d_1/[d_1−c_1(2)],
    z=[a_2−B_2(x,y)]/[C_A*c_2(1)].                   (5)

All these denominators are nonzero at the center and hence near it.
For instance C_A=27/40, C_D=1881/2000,
d_1−c_1(2)=3/2 and c_2(1)=2. Substitution at the center gives

    e=1/100, f=1/20, z=w=1/3,
    a_1=892/2081, a_2=144/2081, d_1=1/2.

Set

    c_0star=w*c_0(2)+(1−w)xi*f,
    b_0=z*c_0(1)+(1−z)c_0star,
    c_3star=w*c_3(2)+(1−w)eta*e,
    b_3=z*c_3(1)+(1−z)c_3star.                        (6)

Only two residual equations remain:

    F_3(r,x,y)=b_3−x(H+eta)/(1−x)=0,
    F_0(r,x,y)=L*y+(1−y)b_0−xi*y=0.                  (7)

These are smooth rational functions of the sixty raw coordinates
and the two variables x,y on a neighborhood of the center. For any
solution of (7) in that neighborhood, define centered phase vectors

    v_A=(xi*y,a_1,a_2,eta*x),
    v_B=(b_0,0,c_2(1)z,b_3),
    v_C=(c_0star,0,0,c_3star),
    v_D=(xi*f,d_1,0,eta*e).                            (8)

The actual vectors are V_A=s+v_A, and similarly for B,C,D.

### All phase identities

At D, player 0's centered Continue identity is

    L*f+(1−f)xi*y=xi*f,

which is exactly (4)'s formula for f. Player 3's is

    −H*e+(1−e)eta*x=eta*e,

which is exactly the formula for e. Their centered forced-Quit
endpoints at D are xi*f and eta*e. At A the centered forced-Quit
endpoints are xi*y and eta*x; their Continue identities are precisely
(7). Thus both joint players are indifferent at both joint rows.

For player 1 at A, the next centered value v_B,1 is zero, so its
policy and Continue value is B_1(x,y)=a_1. At D its value is
B_1(e,f)+C_D*a_1=d_1. The formula for w enforces

    w*c_1(2)+(1−w)d_1=0.

Consequently v_C,1=v_B,1=0, including both the B solo owner's
Continue equality and C's player-1 equation.

For player 2 at D, the definition of a_2 gives

    B_2(e,f)+C_D*a_2=0.

The formula for z gives

    B_2(x,y)+C_A*c_2(1)z=a_2.

These are its D and A equations. At B it obtains c_2(1)z
because its next centered value is zero. Its C solo-owner value
and next D value both vanish, giving exact solo indifference.

The remaining four scalar equations at B,C are exactly (6). Every
policy equation follows from these Continue identities and supported
Quit indifference. Thus (4)–(8) give ALL sixteen policy identities
and ALL sixteen Continue identities for arbitrary nearby tables.
No equality between perturbed raw rewards is being assumed.

## 4. The exact regularity calculation

At the table in Section 2 and at x=1/10,y=1/4, both components
of (7) vanish. With rows ordered (F_3,F_0) and columns (x,y),
their derivative is

    [[−34669831/8430300,  −21674311817/23083492500],
     [ 445211/800850,     −7722150539/6578561250]].      (9)

This is obtained by ordinary differentiation of (4)–(7), keeping
the raw table fixed, followed by exact rational substitution. Its
determinant is

    1561445159256653/291890762662500 > 0.               (10)

The sign also follows directly: both diagonal entries are negative,
the upper-right entry is negative, and the lower-left entry positive.

The finite-dimensional implicit-function theorem therefore gives an
open neighborhood of r_star in ℝ⁶⁰ and smooth functions x(r),y(r)
satisfying (7), with the stated central rates. Equations (4)–(5)
then determine e(r),f(r),z(r),w(r) from the same table. Shrink the
neighborhood so all denominators remain nonzero and all six rates
are strictly between zero and one. Equations (8) give smooth phase
vectors on it. These are produced functions of raw data, not strategic
witnesses supplied as hypotheses.

## 5. Floors and all joint outsider inequalities persist

The four equalities

    V_B,1=V_C,1=s_1,        V_C,2=V_D,2=s_2           (11)

are literal identities in (8), for EVERY nearby raw table. They do
not need a false claim that a binding inequality survives arbitrary
perturbations. Every other singleton floor is strict at (1), so all
persist after shrinking the open neighborhood once.

For a joint row with player-0 and player-3 rates q,t, the centered
forced-Quit payoff of outsider i∈{1,2} is exactly

    q(1−t)c_i(0i)+(1−q)t*c_i(i3)+qt*c_i(0i3).        (12)

The empty-opponent centered term is c_i(i)=0. Thus all four
opponent coalitions, including simultaneous {0,3}, are accounted
for. The forced-Continue value is already the phase value by
Section 3. The four Continue-minus-Quit margins are continuous in
the entire raw table and in the smooth branch rates. Their strict
central values (2) persist on a further open neighborhood.

The active joint players have exact indifference, not just a weak
comparison. Consequently both joint phases have exact Continue and
nonpositive immediate-Quit gain for all players throughout the
resulting neighborhood. All phase singleton floors hold there.
Perturbed singleton rewards need not be nonnegative; none of these
arguments changes the zero reward on Never.

## 6. Refinement, fixed target, and unrestricted deviations

Fix one table in the resulting neighborhood and fix its branch rates.
For each positive integer n replace B and C by n solo dates with
respective hazards

    beta_n=1−(1−z)^(1/n),
    gamma_n=1−(1−w)^(1/n).                            (13)

Keep A and D unchanged. Each refined period has m_n=2+2n dates.
The aggregate survival of each solo block is unchanged. Conditional
on absorption inside it, the same solo coalition receives the same
reward. Thus the terminal coalition law and all four macro endpoint
values are unchanged. In particular the terminal target is the SAME
V_A(r) for every n, not a target chosen after the accuracy.

Inside a solo block with owner j, microhazard b and m remaining
microdates, the value is

    [1−(1−b)^m]r({j})+(1−b)^m V_next.

As m varies it lies on the segment between the two macro endpoint
vectors. Hence all singleton floors persist. The owner's two endpoint
coordinates equal s_j, so it remains exactly indifferent throughout
the block. Every player's Continue equation remains exact.

Put

    C_join=max(0, r_i({i,j})−s_i : j∈{1,2}, i≠j),
    delta_n=C_join*max(beta_n,gamma_n).                (14)

At a solo microdate with owner j and rate b, outsider i's Quit
payoff is

    (1−b)s_i+b*r_i({i,j})≤s_i+b*C_join
                              ≤V_i+delta_n.

The owner has equality with V_i. Both joint rows have Quit payoff
at most V_i already. Thus at EVERY date and for EVERY player,
Continue is exact and Quit is at most the prescribed value plus
the same nonnegative delta_n, which tends to zero.

### A single error bounds an entire behavioral deviation

Add delta_n to every value coordinate at every date. Its forced-Quit
endpoint is bounded by the augmented value. Its forced-Continue
endpoint is at most the augmented value because continuing transports
only the opponent nonabsorption probability times delta_n, at most
delta_n. Therefore this augmented path is a Bellman supersolution
for any mixture of the two actions at any history. There is no sum
of local errors over time.

To remove the terminal remainder, the per-period opponent survival
probabilities for the four possible deviators are

    rho_0=(1−y)(1−f)(1−z)(1−w),
    rho_1=(1−x)(1−y)(1−e)(1−f)(1−w),
    rho_2=(1−x)(1−y)(1−e)(1−f)(1−z),
    rho_3=(1−x)(1−e)(1−z)(1−w).                      (15)

Each is strictly below one, independent of n. Opponents follow fixed
date-dependent independent coins until absorption, regardless of the
deviator's whole behavioral strategy. Their first scheduled Quit is
therefore an upper bound on the actual absorption time under ANY
such deviation. Survival after k periods is at most rho_i^k.
The value path is bounded, so finite Bellman comparison followed by
this tail estimate makes the unabsorbed remainder tend to zero.
Every complete unilateral terminal payoff is at most

    V_A,i(r)+delta_n.                                 (16)

Policy equality and the same absorption estimate give terminal payoff
exactly V_A(r) for the prescribed profile. This proves terminal
delta_n-Nash against unrestricted behavioral deviations, with a
fixed target before n is chosen. No deviator is given foresight of
opponents' coins in this coupling or comparison.

### Uniform finite horizons

Choose M≥0 bounding all rewards of the fixed table. Write

    K_n=m_n*max_i 1/(1−rho_i).

The preceding geometric estimate gives expected absorption date at
most K_n under every unilateral deviation, as well as under the
prescribed profile. Since all stage and terminal rewards have absolute
value at most M, terminal payoff differs from N-stage average payoff
by at most 2M K_n/N, uniformly over these profiles and deviations.
Indeed at most the absorption date's number of transient stages can
differ from the eventual absorbing reward, each by at most 2M.

Consequently N-stage regret is at most

    delta_n+4M K_n/N,

and each prescribed average coordinate differs from V_A(r) by at
most 2M K_n/N. Given epsilon>0, first choose n with
delta_n<epsilon/2, then choose one threshold so 4M K_n/N is
at most epsilon/2 for every larger N. This proves the asserted
uniform-equilibrium payoff with its exact quantifier order.

## 7. Exact bounded coverage distinctions

A positive-premium trap is a nonempty set A for which each i∈A
has some coalition S⊆A containing i with r_i(S)>s_i. At the
center, both 03 and 12 are traps with strictly positive participant
premiums; they are disjoint and their union is all four players.
These facts persist nearby. Thus there is no player common to all
traps, and the greatest premium core is full, not of size at most two.

There is a stronger support-specific distinction. Trap 03 has NO
weak leaver: its two leave comparisons fail by strict amounts

    r_0(03)−r_0(3)=475/281>0,
    r_3(03)−r_3(0)=495/493>0.                         (17)

These gaps also persist nearby. Therefore no choice of protected
players can make every premium trap have a weak leaver against all
nonempty coalitions of its other members. This excludes both common-
leaver and support-specific protected-floor criteria on this neighborhood,
not merely one possible choice of a protected set.

There is no pure stationary equilibrium at the center. All Never is
defeated by player 0's singleton 1. For sure coalitions ordered as

    0,1,2,3; 01,02,03,12,13,23; 012,013,023,123; 0123,

respective players

    3,3,1,2; 0,0,1,2,1,3; 1,3,3,1; 1

have strict profitable toggles. Every listed withdrawal leaves another
quitter, so no fictitious continuation is used. This finite collection
of strict improvements persists on a smaller neighborhood.

### No stationary equilibrium with player 3 quiet at the center

For constant hazards q, let Q_i be the forced-Quit expectation,
B_i the unnormalized passive reward over nonempty opponent coalitions,
and alpha_i=1−product_{j≠i}(1−q_j). Put E_i=alpha_i Q_i−B_i.
When opponents absorb with positive probability, necessary stationary
optimality conditions are E_i≤0 if q_i=0, E_i≥0 if q_i>0,
and E_i=0 if 0<q_i<1. They follow by comparison with always-Quit
and always-Continue, which are allowed complete deviations.

Assume q_3=0. Set A=q_1+q_2−q_1q_2 and
T=q_1+q_2−2q_1q_2. The table gives

    Q_0=1−A, B_0=2T,
    E_0=A(1−A)−2T≤−T.

For the inequality, A≥max(q_1,q_2), so A²≥q_1q_2.
The quantity T is nonnegative and vanishes only at (q_1,q_2)
equal to (0,0) or (1,1). Outside those two corners, E_0<0
forces q_0=0.

At q_1=q_2=1,

    E_2=(1/2−3q_0/2)−2(1−q_0)=−3/2+q_0/2<0,

contradicting q_2=1. At q_1=q_2=0 with q_0>0,
E_3=h_3q_0+eta*q_0²>0, contradicting q_3=0. With all
hazards zero, player 0 improves from Never zero to singleton 1.
Thus only q_0=q_3=0 remains. If q_1>0, then

    E_2=q_1²/2−2q_1<0,

forcing q_2=0; but now E_3=q_1−q_1²/2>0. If q_1=0
and q_2>0, then E_1=q_2+q_2²/2>0. Both contradict the
corresponding zero hazard. This exhausts the q_3=0 cube, including
all boundary hazards.

In particular the center cannot belong to any stationary-neighborhood
theorem whose conclusion has players 0,1,2 active and player 3 quiet
in these labels. This does NOT exclude all relabelings, all other
stationary supports, all stationary equilibria, or every existing
actual-table producer. None of those stronger exclusions is needed
for the neighborhood construction.

## 8. Tracked consumer and Lean handoff

The current exact-Continue compiler is
`QuittingInfinitePathQuitErrorCertificate` and its theorem
`QuittingInfinitePathQuitErrorCertificate.isεAsymptoticNash_and_delivers`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
Its fields are exactly the root path, bounded value path, fixed entry
target, policy equality, immediate-Quit error, exact Continue, and
vanishing opponent survival verified in Section 6. The declaration
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`
there proves the single-error comparison, and
`isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
consumes accuracy-indexed certificates for one fixed target. Section 6
also gives the direct geometric uniform-horizon estimate independently.

The precise existing stationary branch compared in Section 7 is
`PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`.
Its `PairedCubicStationaryExample.activeHazard`, defined in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicActiveJacobian.lean`,
is literally (point_0,point_1,point_2,0), so the fixed-label
exclusion applies. Its existing full-coordinate implicit-function
setup is in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistence.lean`.

The new formalization output has the shape: literal rational raw
center → elimination identities and nonzero two-by-two derivative →
open set of sixty-coordinate raw tables with produced smooth rates
and phase values → fixed-target refined certificates → uniform-
equilibrium payoffs. The new helper is the arbitrary-table elimination
(4)–(8), together with exact checks (1)–(3) and (9)–(10). Existing
implicit-function and exact-Continue consumers suffice after these
actual-data inputs are proved. No generic openness theorem for uniform
equilibria, supplied strategic witness, or change of deviation semantics
is part of the conclusion.
