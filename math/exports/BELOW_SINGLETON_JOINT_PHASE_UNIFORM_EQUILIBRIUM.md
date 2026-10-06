# Joint-phase uniform equilibria below the singleton floors

## 1. Game, conclusions, and scope

Let I={0,1,2,3}. A reward table assigns r(S)∈ℝ⁴ to every nonempty
coalition S⊆I. At each live date the players independently choose
Continue or Quit, with arbitrary behavioral probabilities depending on
the public history. The first nonempty quitting coalition S causes
absorption. The initial live-state payoff is zero; subsequent absorbed
dates pay r(S). If absorption never occurs, every payoff is zero.
Terminal payoff means r(S) at eventual absorption, with zero at Never.
No public randomization or correlated action device is introduced.

A uniform-equilibrium payoff is one vector v such that, for every ε>0,
there are a behavioral profile and N₀ for which every N≥N₀ has payoff
within ε of v and every unilateral behavioral deviation gains at most ε.
The vector v is fixed before ε is chosen. The profiles constructed here
are stronger: a single proper periodic profile is an exact terminal
Nash equilibrium and supplies the same target for every accuracy.

There are two raw-table conclusions.

1. The finite inequalities and equalities in Section 2 produce such a
   profile directly, for arbitrary signed own-singleton levels.
2. The complete rational table in Section 5 has an open neighborhood in
   all sixty reward coordinates with the same conclusion. Nearby tables
   need satisfy none of the singleton or pair equalities in Section 2.

In both conclusions the prescribed phase values lie strictly below the
players' own-singleton rewards. Collision rewards make Quit unattractive
at passive phases, so a phasewise singleton floor is unnecessary.
Section 6 proves the full-coordinate neighborhood by a local contraction,
not by assuming a selected root or equilibrium certificate. Sections 7–11
give exact source-separation and boundary tests. These are ordinary
mathematical proofs; no Lean verification of the new raw producer or
its neighborhood is asserted.

## 2. A raw family and an actual rate producer

Use the three perfect matchings

    f=(01)(23),       a=(02)(13),       o=f∘a=(03)(12).

The scheduled coalitions are A={0,2} and B={1,3}. Choose arbitrary
s_i∈ℝ, positive b_i, and common real parameters H,Π,K satisfying

    H>2,       Π<−1,       K<(7Π+10−2H)/2.                 (1)

Require the singleton entries

    r_i({i})=s_i,             r_i({f(i)})=s_i+Hb_i,
    r_i({a(i)})=r_i({o(i)})=s_i−b_i.                     (2)

For each scheduled pair T=A,B require

    r_i(T)=s_i+Πb_i       if i∈T,
    r_i(T)=s_i+Kb_i       if i∉T.                         (3)

Put c=−Π−1>0 and C=4c/3. The remaining assumptions are twelve caps:

    r_i({i,f(i)})≤s_i−Cb_i,
    r_i({i,o(i)})≤s_i−Cb_i,
    r_i({i,f(i),o(i)})≤s_i−Cb_i.                         (4)

Every reward coordinate not specified in (2)–(4) is unrestricted.
In particular, the grand-coalition vector is unrestricted.

Define

    P(t)=Πt³+(H−1−K)t²+Kt−(Π+1).

Its endpoint values on the interval of interest are

    P(1/2)=(2H−10−7Π+2K)/8<0,       P(1)=H−2>0.

The intermediate value theorem supplies t∈(1/2,1) with P(t)=0.
Choose one such t once and for all, and set q=1−t∈(0,1/2).
At phase A, players 0 and 2 independently quit with probability q
and the other two Continue. At phase B, players 1 and 3 do the same.
Repeat the two phases after every all-Continue outcome.

The selection interval matters: an arbitrary root in (0,1) need not
satisfy the passive incentive inequalities. Section 11 gives an exact
failure at a second proper root of the same cubic.

## 3. All phase endpoints

For player i define the active and passive phase values

    U_i=s_i+qΠb_i,
    W_i=s_i+q(Π+1)b_i/t.                                 (5)

Both are strictly below s_i. At i's active phase, its only possible
quitting opponent is a(i). The forced-Quit endpoint is

    Q_i^active=t s_i+q(s_i+Πb_i)=U_i.

The forced-Continue endpoint, with W_i at the next phase, is

    C_i^active=q(s_i−b_i)+tW_i=U_i.                       (6)

At i's passive phase, the scheduled opponents are f(i) and o(i).
The two singleton outcomes have probabilities qt each, the joint outcome
has probability q², and joint survival has probability t². Therefore

    C_i^passive
      =qt(s_i+Hb_i)+qt(s_i−b_i)+q²(s_i+Kb_i)+t²U_i
      =s_i+b_i[qt(H−1)+q²K+t²qΠ]
      =W_i.                                             (7)

The last equality is exactly P(t)=0. Forced Quit at this phase gives
the singleton reward if both opponents Continue, one of the two capped
pair rewards if exactly one quits, and the capped triple reward if both
quit. Consequently

    Q_i^passive≤t²s_i+(1−t²)(s_i−Cb_i).

Its gap below W_i is at least

    q b_i[(1+t)C−c/t]>0,                                (8)

because t(1+t)>3/4 and C=4c/3. This verifies all sixteen action
endpoints: two actions for each of four players at each of two phases.
The triple caps retain simultaneous quitting by both opponents; a
one-opponent comparison would not prove (8). The grand coalition cannot
occur on path or under a unilateral deviation from this support word.

## 4. Actual values, unrestricted deviations, and uniform horizons

The joint probability of surviving one complete period is t⁴<1.
The affine policy recursion over one period is therefore a contraction.
Equations (6)–(7) show that (5) is its unique solution. Equivalently,
iterate the equations over n periods: the remaining continuation term
has coefficient t⁴ⁿ and tends to zero. Summing the absorbed rewards
shows that (5) is the actual terminal payoff, not an auxiliary vector.
In particular, if M=max_{S,i}|r_i(S)|, all phase values have absolute
value at most M.

Fix a deviating player i. During each period, its three opponents each
have one scheduled quitting opportunity. Their probability of all
continuing is t³, independently of i's behavioral choices. Conditional
on survival, the phase is deterministic; any deviating action is a
mixture of the two endpoints already checked. Backward iteration of
the endpoint upper bounds through n periods bounds its terminal reward
up to a remainder of absolute value at most 2M t³ⁿ. This holds for
every history-dependent behavioral deviation. Letting n tend to infinity
proves exact terminal Nash optimality. It includes Never and deviations
which stop at unbounded stopping times: the opponents force absorption
almost surely with a uniform geometric tail.

For a quantitative finite-horizon comparison, let τ_{−i} be the first
date on which an opponent of i quits under the fixed periodic opponents.
Uniformly over the starting phase and every deviation,

    E[τ_{−i}]≤C_time:=1+2/(1−t³).                         (9)

Indeed, the probability of no opponent exit in n complete periods is
t³ⁿ; summing this tail gives the bound, with one extra date covering
the initial live-state convention. Actual absorption occurs no later
than this opponent exit. The difference between terminal reward and
the average of the first N state payoffs is bounded in expectation by
2M C_time/N. This conservative bound includes the initial zero date and
the possibility that absorption occurs after the horizon.

Let v be the phase-A value vector. The prescribed N-date payoff is
within 2M C_time/N of v. Every deviating N-date payoff is at most its
terminal upper bound v_i plus 2M C_time/N. Hence its gain over the
prescribed N-date payoff is at most 4M C_time/N. Taking N₀ large
proves the uniform-equilibrium conclusion with this one fixed v and
the same profile for all accuracies. It does not claim exact delivery
of v at every finite horizon.

The tracked semantic consumers with this scope are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
The raw rate production and endpoint inequalities above supply the
strategic data; they are not extra assumptions on the game.

## 5. A complete rational table

Take

    H=3,   Π=−11/10,   K=−179/60,   s_i=b_i=1.

The exact selected root is t=2/3 and q=1/3. Here C=2/15, so the
required cap is 13/15. Define the complete table r* by

| S | r*(S) |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (1/2,1/2,0,0) |
| 02 | (−1/10,−119/60,−1/10,−119/60) |
| 03 | (1/2,0,0,1/2) |
| 12 | (0,1/2,1/2,0) |
| 13 | (−119/60,−1/10,−119/60,−1/10) |
| 23 | (0,0,1/2,1/2) |
| 012 | (100,−3,100,0) |
| 013 | (−3,100,0,100) |
| 023 | (100,0,100,−3) |
| 123 | (0,100,−3,100) |
| 0123 | (−101,−102,−103,−104) |

The prescribed hazards are (1/3,0,1/3,0) and (0,1/3,0,1/3).
Their phase values are

    V_A=(19/30,19/20,19/30,19/20),
    V_B=(19/20,19/30,19/20,19/30).

Each active Quit and Continue endpoint equals 19/30. Each passive Quit
endpoint equals

    (4/9)·1+(4/9)·(1/2)+(1/9)·(−3)=1/3,

while its Continue endpoint is 19/20. The passive gap is 37/60.
All twelve cap entries are either 1/2 or −3, strictly below 13/15.
At a triple, the entries 100 belong to the two scheduled players,
not to the player who can unilaterally join that pair. Thus these
entries enter neither on-path rewards nor the deviating player's
endpoint for this profile. They remain part of the original game.

## 6. A full sixty-coordinate UE neighborhood

There exists δ>0 such that every table r with

    max_{S≠∅,i∈I}|r_i(S)−r*_i(S)|<δ                      (10)

has an exact proper two-phase terminal Nash profile on A,B and a fixed
uniform-equilibrium payoff. Its four hazards may differ. No equality
from (2)–(3) is imposed on r. The construction can be chosen so that
all eight phase values remain strictly below their own-singleton levels.

For the proof define from the actual nearby entries

    s_i=r_i({i}),       Γ_ij=r_i({j})−s_i  (j≠i),
    b_i=−Γ_i,a(i),     π_i=r_i({i,a(i)})−s_i,
    k_i=r_i({f(i),o(i)})−s_i.

Use positive odds X_i and hazards q_i=X_i/(1+X_i). For j=f(i),
k=o(i), set

    E_i(X,r)=(π_i+b_i)X_a(i)(1+X_j)(1+X_k)
       −Γ_ij X_j−Γ_ik X_k−k_i X_jX_k
       −π_i X_a(i)/(1+X_a(i)).                           (11)

For any positive X define

    U_i=s_i+π_i X_a(i)/(1+X_a(i)),
    W_i=s_i+(π_i+b_i)X_a(i).                            (12)

Both active endpoints equal U_i: the Quit endpoint uses the actual pair
reward s_i+π_i, while the Continue endpoint is
q_a(i)(s_i−b_i)+(1−q_a(i))W_i. At the passive phase the Continue
endpoint equals W_i exactly when E_i=0; multiplying by
(1+X_j)(1+X_k) gives (11). These identities do not require any
singleton symmetry or common coefficient.

At X*=(1/2,1/2,1/2,1/2) and r=r*, all E_i vanish. Their X-Jacobian is

    J = [ 0       −19/12    19/72    29/12 ]
        [−19/12    0       29/12    19/72 ]
        [ 19/72    29/12    0      −19/12 ]
        [ 29/12    19/72   −19/12    0     ].              (13)

The four characters of the commuting matchings f,a,o are eigenvectors.
The eigenvalues are 79/72, −307/72, −41/72, and 269/72; hence

    det J=267486337/26873856>0.

Here is a local root producer. Define T_r(X)=X−J⁻¹E(X,r). Its X
derivative is zero at (X*,r*). Choose a closed ball of radius ρ>0
around X*, entirely in the positive orthant, on which the derivative
norm of T_{r*} is strictly less than 1/2. By continuity, choose δ>0
so that throughout the product of this ball with the reward neighborhood
the derivative norm is at most 1/2 and

    ‖T_r(X*)−X*‖≤ρ/2.

The mean-value inequality makes each T_r a 1/2-contraction and gives
‖T_r(X)−X*‖≤ρ for every point in the ball. Starting from X*, iterate
T_r. Successive differences decrease geometrically, so the sequence
is Cauchy and converges inside the closed ball. Its limit X(r) is the
unique fixed point there, hence E(X(r),r)=0. Moreover

    ‖X(r)−X*‖≤2‖T_r(X*)−X*‖→0  as r→r*.

The four hazards remain proper. The four passive Quit endpoints are
continuous functions of r and X. At the center their gaps below (12)
are 37/60, so all four remain positive after shrinking δ. This uses
the actual nearby pair and triple rewards, without imposing caps as
additional neighborhood hypotheses. The eight below-singleton gaps
also remain positive, since at the center they are 11/30 and 1/20.

The policy and deviation proofs of Section 4 now apply with joint
survival ∏_i(1−q_i)<1 and, for player i, opponent survival
∏_{j≠i}(1−q_j)<1 per period. The same tail argument gives exact
terminal Nash and a fixed uniform target for every table in (10).
This proves a full-dimensional reward region, not just a parameterized
equality stratum. It does not assert such a neighborhood around every
member of the family in Section 2.

## 7. Premium traps, pure exits, and all proper children

Call a nonempty set T a premium trap when for every i∈T there is a
nonempty S⊆T containing i with r_i(S)>s_i. A singleton is never a
trap. For r*, every pair participant reward is below its singleton.
Every triple contains exactly one scheduled pair; the remaining player
gets −3 at the triple and has no positive participant premium in any
smaller coalition inside that triple. Thus no proper subset is a trap.
Every player receives 100 at a triple containing its scheduled pair,
so I is a trap. The greatest premium core is the full four-player set.

No pure exit coalition is Nash:

- At a singleton j, player o(j) gains 1/2 by joining instead of waiting
  for its passive reward zero.
- At a scheduled pair, a participant gains by withdrawing from −1/10
  to the passive singleton reward zero.
- At a favorable pair, a participant gains by withdrawing from 1/2 to 4.
- At an o-pair, either outsider gains 100 by joining instead of zero.
- At a triple, its player outside the scheduled pair gains by withdrawing
  from −3 to −119/60.
- At the grand coalition, every player can withdraw to zero instead of
  its negative grand reward.

All Never is defeated by own Quit, which pays 1.

All fourteen nonempty proper children have exact terminal Nash profiles
with zero probability of Never which nevertheless give a profitable
deviation to an omitted player after quiet lifting. A child is the game
in which only its members act, with the same rewards at their coalitions.
Quiet lifting asks every omitted player to Continue.

| Child | Child profile | Child comparison | Omitted deviation |
|---|---|---|---|
| {j} | j quits surely at the first date | Own reward 1 is the largest solo reward | o(j) joins, gaining 1/2 |
| A favorable pair | Either j quits surely | The other waits for 4 instead of joining for 1/2 | o(j) joins, gaining 1/2 |
| A scheduled pair | Either j quits surely | The other waits for 0 instead of joining for −1/10 | o(j) joins, gaining 1/2 |
| An o-pair | Both quit surely | Each gets 1/2 instead of 0 by withdrawing | Either outsider joins, gaining 100 |
| I∖{m} | j=o(m) quits surely | The other members are f(j),a(j), covered by the comparisons above | m joins, gaining 1/2 |

In a sure-solo profile the quitter cannot improve by delaying its own
exit or by Never, whose payoff is zero. Every other child member has
the displayed best response; later actions cannot change an already
absorbed payoff. These cases count four singleton, six pair, and four
triple children. Their child deviation debts and joint-Never mass are
all zero. Thus for each proper child there is an omitted player whose
quiet-lift debt cannot be bounded universally by any fixed nonnegative
linear combination of child debts plus any finite multiple of Never
mass. This is a failure of a universal lift estimate, not a claim that
every equilibrium of any chosen child has a bad lift.

There is also a direct raw joining-row obstruction. If a proper child
S cuts an o-pair, choose j∈S and k=o(j)∉S and background {j}.
Player k's joining gain is 1/2. The child members' joining gains are
0 for j, −7/2 if f(j) is present, and −1/10 if a(j) is present.
Their withdrawal gains are zero except possibly that of j, which is
nonpositive for any singleton fallback at most 1. Hence no nonnegative
weighted sum of these gains can dominate the omitted gain. If S cuts
neither o-pair, it is exactly 03 or 12. At background S either outsider
has joining gain 100; all child joining gains are zero and each child
withdrawal gain is −1/2. This excludes the same weighted raw row.

## 8. Exact failures of floor, cap, and potential criteria

For a product hazard vector q, a player's forced-Quit value is the
expectation of r_i({i}∪T) under the independent opponents' coalition T.
At q=(1/10,1/10,1/10,1/10), these four values for r* are

    (24739,24729,24719,24709)/10000,

all strictly greater than the singleton level 1. Thus the product-low
condition, which requires some active player to have forced-Quit value
at most its singleton at every nonzero product hazard, fails. A weighted
supportwise nonpositive-premium condition implying it fails as well.

Every player has a negative participant premium at I. Consequently the
set of players with nonnegative participant premiums at every coalition
is empty, excluding protected-player and protected-set leaver tests.
The same grand row excludes any nonzero nonnegative weighted lower-floor
condition on all reward vectors. Criteria requiring a greatest premium
core of size at most two or three fail by Section 7.

The larger-trap boxed insertion condition requires nonpositive insertion
coefficients at intermediate proper coalitions. For the full trap and
S=01 this coefficient is

    (r₂(012)−s₂)+(r₃(013)−s₃)=198>0.

This also prevents a mixed criterion that handles pair traps by index
and larger traps by those boxed coefficients. These are raw failures,
independent of any choice of a reward bound.

For a weighted terminal upper-bound criterion, let λ≥0 be a weight
vector such that every terminal reward satisfies λ·r(S)≤λ·s.
The four singleton tests say Γᵀλ≤0, where Γ_ii=0 and
Γ_ij=r_i({j})−s_i. Every row of Γ has sum 1, so summing these
inequalities gives Σ_i λ_i≤0 and hence λ=0. Thus no nonzero weight
supplies such an upper bound.

A conditional-face range bound compares an upper bound on Continue
against a convex combination of lower Quit bounds at a blocking face.
Here any such Continue upper bound is at least 4, by the favorable
singleton. The Quit lower bound without the blocker is at most 1,
by the empty background. The Quit lower bound with the blocker is at
most r_i(I)<0, by the maximal background. At every admissible blocker
lower hazard in (0,1), their combination is at most 1, not above 4.

Finally set r_i(∅)=0 and define membership gain

    D_i(T)=r_i(T∪{i})−r_i(T),       i∉T.

For player 0, adding player 1 changes this gain by −9/2 at background
∅, since D₀(∅)=1 and D₀({1})=−7/2. At background {2} it changes
the gain by 1001/10, since D₀({2})=−1/10 and D₀({1,2})=100.
Thus the ordered influence 1→0 has both signs. It is neither globally
nonnegative, globally nonpositive, nor absent. The membership gain is
also not affine in the background indicators, since that would make
this increment independent of the background. These strict failures
persist in a reward neighborhood.

The corresponding tracked raw definitions include
`IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`,
`exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`,
`SignConsistentQuittingInfluence` in
`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`,
and `IsAffineQuittingMembershipGain` in
`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.

## 9. Matching, matrix, response, and scheduled-source comparisons

### Matching producers

Consider a matching raw test with one nonnegative favorable singleton
comparison and two nonpositive harmful comparisons per player. Its
favorite matching is f; its scheduled matching a′ must be one of the
two harmful perfect matchings. The weak participant condition is

    r_i({i,a′(i)})≥r_i({a′(i)}),                         (14)

and an inactive player must have every pair/triple joining reward against
the opposite scheduled pair at most its own singleton. No restriction
on the opposite scheduled pair's passive payoff is needed for the test
considered here.

For r*, the singleton signs force f=(01)(23). If a′=(02)(13),
(14) fails at −1/10<0. If a′=(03)(12), an outsider joining the
opposite scheduled pair gets 100>1, violating its cap. This exhausts
all relabelings. Both failures are strict and invariant under positive
playerwise affine transports of the reward table. Therefore a small
reward neighborhood of r* still fails this arbitrary-passive matching
test. It is not merely excluded by a sign restriction on K.

A general inverse-positive two-pair test with nonnegative participant
premiums also fails for every partition: all pair participant rewards
of r* are below their own singleton. A pure-pair alternative fails by
the explicit deviations of Section 7. The neighborhood theorem supplies
new tables beyond these matching tests, not just a different proof of
membership in them.

### Singleton matrix and response partitions

The singleton matrix is

    Γ = [ 0   3  −1  −1 ]
        [ 3   0  −1  −1 ]
        [−1  −1   0   3 ]
        [−1  −1   3   0 ].                              (15)

Its eigenvalues are 1,5,−3,−3 and det Γ=45. Its inverse has
diagonal 2/15, favorable entry 7/15, and the other entries 1/5.
Every principal matrix of size at least two is nonsingular: pair
determinants are −9 or −1 and triple determinants are 6. A nonzero
homogeneous complementarity solution supported on at least two indices
would solve a nonsingular principal homogeneous system, which is
impossible. A singleton support fails because every column has a
negative entry outside its diagonal. Thus Γ is R₀. The nonnegative
inverse degree formula gives degree sign(det Γ)=+1, so it supplies
no degree-not-one or negative-determinant exit.

A harmful principal pair is [[0,−1],[−1,0]], which is not Q:
at offset (−1,−1) its residual is negative for every nonnegative
candidate. It has no nonzero homogeneous complementarity solution.
Every triple inverse has a diagonal entry −1/6, excluding a
nonnegative-inverse triple exit. These statements test the stated
principal-matrix screens, not every conceivable singleton-matrix
existence theorem. The degree formula is
`r0Degree_eq_sign_det_of_nonnegative_inverse` in
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`.

At all-sure hazards the four Quit-minus-Continue responses are
−101,−102,−103,−104, since r_i(I∖{i})=0. Thus every nondiscrete
partition has two members
whose responses differ, and no such response-invariant quotient exists.
This also excludes quotients after any positive playerwise affine
transport: the singleton block-row-sum identities force equal row
scales within each receiver block, because all original row sums are 1.
The all-sure response differences are multiplied by those positive row
scales and still differ within that block. There are fifteen partitions in total,
fourteen nondiscrete. The necessary block identity is
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.

### Other scheduled raw predicates

A paired-cycle raw region allowing only one below-own singleton
recipient per row cannot contain (15), which has two. Its exact
necessary property is `RawRegion.eq_partner_of_singleton_lt` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`.
The positive singleton graph is two transpositions, not a favorable
four-cycle. Every reciprocal singleton pair has agreeing signs, not
the opposite signs required in tournament or opposite-sign solo-branch
patterns. After every deletion, the favorite mate of the omitted
player has two negative comparisons to the surviving child, excluding
a three-child singleton pattern requiring a positive recipient in
every child row.

For an overlapping period-three affine-cylinder test, its center has
the same singleton levels 1,4,0 as r*, but every participant pair
reward equals its own singleton at that center. Such pair coordinates
are all visible. At coordinate radius ε=1/50000000, the absolute
participant-pair premium divided by a harmful singleton gap is at most
2ε/(1−2ε)<1/4. At r* this ratio is 1/2 or 11/10 for every
participant pair. The ratio is invariant under positive playerwise
affine transport; relabeling cannot remove the discrepancy. The exact
center and visibility definitions are `overlappingPeriodThreeRewardRow`
in `UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeReward.lean`
and `IsInvisibleRewardCoordinate` in
`UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeInvisibleCoordinates.lean`.

Every ordered lower-face singleton guard fails directly. For any selected
partner j≠f(i), the sure favorite outsider produces joining displacement
1/2−4=−7/2. If j=f(i), the sure scheduled mate produces displacement
−1/10−0. These are points of the actual closed outsider faces.
Thus nonnegative guards on those faces fail, including the weak
polynomial and one-sided guards used by their raw neighborhood tests.
Relevant definitions are `QuittingHalfWeakPolynomialGuards` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`
and `QuittingOneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.
The literal owner-risky family in
`UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyStationaryClosure.lean`
has an off-diagonal singleton difference zero, whereas (15) has none.

## 10. Robust exclusion of the proper-three stationary branch

At r*, no stationary equilibrium with exactly three proper active
hazards exists. This exclusion persists throughout the full coordinate
ball of radius 1/1000, even though that ball is not asserted to be the
explicit UE radius in Section 6. It is enough to intersect the two
neighborhoods.

The rows of size at most three of r* have the Klein symmetries generated
by f,a. It suffices first to examine support 012, with proper hazards
(a,x,c) for players 0,1,2. Player 2's payoff from Never is zero,
since every possible absorption by opponents 0 and 1 pays it zero.
Proper stationary mixing therefore requires its Quit endpoint to vanish:

    Q₂*=1−(11/10)a−x/2+(503/5)ax=0.                     (16)

At a proper stationary equilibrium a player's forced-Quit value equals
its payoff from Never against the stationary opponents. This follows
also by solving the one-state renewal equation; opponents absorb
almost surely because their hazards are proper and positive.

Solving (16) gives a=(10−5x)/(11−1006x). Positivity and a<1
imply 0<x<1/1001 and 10/11<a<1. But player 1 has

    Q₁*=1−(a+c)/2−3ac,
    N₁*=[4a(1−c)−(119/60)ac]/D,       D=a+c−ac>0.

Set F=D(N₁*−Q₁*). Direct differentiation gives

    ∂_aF=a+3+(5a−239/60)c+(5/2−6a)c².                   (17)

For a≥9/10 this is concave in c; its endpoint values on [0,1]
are a+3 and 91/60, both positive. Thus F strictly increases in a.
At a=10/11,

    F=(213c²−1855c+2280)/726≥29/33>0.

This contradicts player 1's proper mixing, proving the exact-center
exclusion.

For robustness let every reward entry change by at most δ≤1/1000.
At any fixed hazard profile, the forced-Quit endpoint changes by at
most δ. A Never payoff against absorbing opponents is a probability
average of terminal entries, so it too changes by at most δ.
Consequently proper mixing for player 2 would imply |Q₂*|≤2δ.
If a≤9/10, the affine function Q₂* of x has at x=0 the value
1−11a/10≥1/100 and at x=1 the value 1/2+(199/2)a≥1/2.
Thus Q₂*≥1/100>2δ, impossible. Necessarily a>9/10.

Equation (17) now gives

    F>F(9/10,c)=(64c²−512c+621)/200≥173/200.

Since D≤1, the center gap N₁*−Q₁* exceeds 173/200. The nearby
gap differs from it by at most 2δ, so it is still strictly positive.
This contradicts player 1's mixing. Relabeling by the Klein symmetries
treats all four deleted supports; the full coordinate ball is invariant
under these permutations of the center's rows of size at most three.

This excludes the proper-three-active local source represented by
`PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`.
It makes no claim about stationary equilibria with full support, sure
hazards, or other boundary supports.

## 11. A second cubic root is not an equilibrium certificate

Keep the parameters of Section 5 but set all twelve capped entries
in (4) equal to their allowed upper bound 13/15. All other entries
remain unchanged. This is still a member of the raw family.
The polynomial factors as

    P(t)=−(3t−2)(22t²−85t+3)/60.

Besides the selected root 2/3 there is a proper root

    t₋=(85−√6961)/44∈(0,1/20).

For the quadratic factor the values at 0 and 1/20 have opposite signs;
its smaller positive root lies in that interval. At t₋ the formal
passive continuation value is

    W=11/10−1/(10t₋)<−9/10.

The actual passive forced-Quit endpoint, however, is

    Q=t₋²+(1−t₋²)·13/15>13/15.

Hence the resulting proper periodic profile is not terminal Nash.
At t=2/3 the same modified table instead has Q=25/27<19/20=W,
with positive gap 13/540, so the theorem's selected root works.
The example refutes unrestricted cubic-root selection, not the raw
theorem, the neighborhood conclusion, or existence of uniform equilibrium.

## 12. Mathematical handoff

The new finite-data chain is: inequalities (1)–(4) produce a root in
(1/2,1); the complete endpoint calculation supplies an actual two-phase
certificate; opponent-deleted geometric absorption controls unrestricted
behavioral deviations and every sufficiently long finite horizon.
Separately, equations (11), the exact invertible Jacobian (13), and
strict passive inequalities produce the full sixty-coordinate reward
neighborhood. The scalar family and the local-neighborhood theorem have
distinct hypotheses and should remain distinct conclusions.

The periodic semantic consumer declarations in Section 4 are tracked
interfaces for the produced data. Formalizing the raw producer, its
contraction neighborhood, and the exact fixture does not require an
assumed Nash selection, a public randomization device, a phasewise
singleton floor, or a supplied continuity certificate. The conclusion
is uniform equilibrium in the original independent-action game.
