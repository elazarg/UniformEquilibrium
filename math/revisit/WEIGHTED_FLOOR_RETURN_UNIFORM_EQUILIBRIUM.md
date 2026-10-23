# Weighted floors and aggregate leave in quitting games

## 1. A finite raw criterion

Let I be a finite nonempty player set. At each live date the players
independently choose Continue or Quit. The first nonempty coalition S
of quitters absorbs at reward vector r(S), received thereafter.
Live stages and perpetual continuation pay zero. Strategies and
unilateral deviations are arbitrary behavioral strategies, with the
game's public action history and independent private randomization.
No public correlation or bounded-memory restriction is added.

Put s_i=r_i({i}). A nonempty set A is a positive-premium trap if
every i in A has some S contained in A, containing i, with r_i(S)>s_i.
Singletons are never traps. For each trap A, require weights lambda^A
strictly positive on A and zero outside A satisfying two finite tests:

    W_A(S)=sum_i lambda_i^A*(r_i(S union {i})-s_i) >= 0
                       for EVERY S contained in I;       (1)

    L_A(T)=sum_{i in A minus T} lambda_i^A*
                       (r_i(T union {i})-r_i(T)) <= 0
                       for EVERY nonempty proper T in A. (2)

The quantifier in (1) is GLOBAL: S need not be contained in the trap.
Its empty-coalition instance is identically zero; every reward used
in the formula is for a nonempty coalition. The same weights for a
trap occur in both tests. Different traps may have different weights.
If there are no traps the criterion is vacuous.

**Uniform-equilibrium theorem.** For four players, if every s_i>=0
and (1)-(2) hold, the original game has a uniform-equilibrium payoff.
There is one vector u such that for each accuracy epsilon>0 one
behavioral profile and one horizon threshold work for every larger
horizon: the prescribed expected average payoff is within epsilon
of u and every complete unilateral deviation pays at most u_i+epsilon.
The target is fixed before accuracy.

The hypotheses are finite raw reward tests. Once the traps are
enumerated, each weight problem is linear feasibility; weights can
optionally be normalized to sum to one. No strategy, root selector,
continuation annotation, or chronological controller is supplied as
input. Participant premiums and passive rewards may have either sign.
In particular there need not be a single player whose participant
premiums are all nonnegative.

The proof first uses STRICT inequalities in (2) to exclude a smooth
potential on the full exact-root relation. It then invokes the
four-player polynomial obstruction and uses reward closure for weak
(2). The weak conclusion is strategic, not a weak analytic theorem.

## 2. Exact roots and their basic estimates

For q in [0,1]^I, let mu_q be the independent product coalition law,
c(q)=mu_q(empty), and a(q)=1-c(q). At a source v the literal successor is

    w(v,q)=c(q)*v+sum_{S nonempty} mu_q(S)*r(S).       (3)

Player i's forced action endpoints are

    Q_i(q)=sum_{T contained in I minus {i}} mu_{-i}(T)*r_i(T union {i}),
    C_i(v,q)=mu_{-i}(empty)*v_i
                    +sum_{T nonempty} mu_{-i}(T)*r_i(T).

Thus w_i=q_i*Q_i+(1-q_i)*C_i. An exact Nash root satisfies
w_i>=Q_i,C_i for every player. Supported actions are optimal:
q_i>0 implies w_i=Q_i and Q_i>=C_i. Exact finite-game Nash
existence supplies a root for every source v. Sources are arbitrary
continuation annotations, not assumed to be realized by strategies.

Fix M>=0 bounding every |r_i(S)| and B>M. A boxed source has
|v_i|<=B. Formula (3) keeps its successor in the box and gives

    norm(w-v)_infinity <= (M+B)*a(q).                 (4)

For every player k, without a premium sign condition,

    Q_k(q) >= s_k-2M*a_{-k}(q) >= s_k-2M*a(q),       (5)

where a_{-k} is opponent absorption probability. On opponent
nonabsorption the Quit reward is s_k; on its complement its difference
from s_k is bounded by 2M. The exact Nash graph in (v,q) is closed,
since its finitely many endpoint inequalities are polynomial.

A full exact-root unit-absorption potential is a function H satisfying

    H(w(v,q))+a(q) <= H(v)                           (6)

for every boxed v and every exact root q. All sure hazards, simultaneous
coalitions, and inactive-player coordinates are retained.

## 3. A convex return-domain lemma

Let R be a closed convex subset of [-B,B]^I containing
U=product_i[s_i,B]. Assume:

1. Every exact root at every boxed source has successor in R.
2. Every absorbing exact root whose source lies in R has a successor
   with at least one coordinate at most its own singleton.

Then no C1 function on a neighborhood of the box satisfies (6).

### The singleton-face derivative inequality

For x in U and x_j=s_j, the full-root potential property implies

    grad H(x) dot (x-r({j})) >= 1.                   (7)

Here is a direct proof that includes signed rewards and upper-box
faces. Set b_j=0. For i!=j set b_i=0 if x_i>s_i, and otherwise
b_i=max(0,r_i({i,j})-r_i({j})). For small t>0 take source
v(t)=x+[t/(1-t)]b and a solo root with hazard t for j.
Positive corrections occur only at singleton-binding coordinates,
which lie strictly below B, so this source remains boxed. Player j
is indifferent. For every other player,

    C_i-Q_i=(1-t)(x_i-s_i)
                     +t*(b_i+r_i({j})-r_i({i,j})) >= 0

for sufficiently small t. This is direct at binding coordinates and
uses the positive first term at nonbinding coordinates, including
upper faces. The root is exact, its absorption is t, and its successor is

    w(t)=x+t*(b+r({j})-x).

Apply (6), divide by t, and differentiate at x. The two correction
terms cancel, giving (7). The probe source need not lie in R;
the potential hypothesis concerns ALL boxed exact roots.

### The actual minimum supports the whole convex invariant

Put D=R intersect {v: some v_i<=s_i}. It is compact and nonempty
because it contains s. Minimize a putative H on D at x. If some
x_i<s_i, all Continue is not Nash. Exact Nash existence gives an
absorbing root, whose successor returns to D by the two premises.
Equation (6) would strictly lower the minimum. Therefore x>=s and
x lies in L={v in U: some v_i=s_i}. It also minimizes H on L.

Write J={i:x_i=s_i} and g=grad H(x). If J had just one member j,
all other nonbinding interior partials would vanish and all upper-face
partials would be nonpositive. The j term in (7) is zero; upper-face
displacements are positive because B>M. Its left side would be
nonpositive, contradicting (7). Hence |J|>=2. Increasing one binding
coordinate leaves another binding, so g_j>=0 on J. Nonbinding
interior partials vanish and upper-face partials are nonpositive.

Crucially,

    g dot (z-x) >= 0 for EVERY z in R.               (8)

If some binding j has z_j<=x_j, the segment from x to z lies in
D by convexity of R, so its right derivative is nonnegative by
minimality on D. Otherwise every binding displacement is positive;
the coordinate derivative signs just obtained give (8) directly.
No individually protected coordinate set or global minimum on R is
being assumed. The minimum on D is what proves (8).

### Vanishing roots and absorption-scale remainders

Every exact root at x has zero absorption: an absorbing one would
return to D and contradict its minimum. Choose k in J and sources
v_n=x-epsilon_n*e_k for a sequence epsilon_n decreasing to zero,
small enough to stay boxed. All their exact roots absorb, since all
Continue gives k a strict gain epsilon_n. Choose any such roots q_n.

The hazard cube is compact. By the closed Nash graph, every
accumulation root of q_n is exact at x and therefore has zero
absorption. Thus a_n=a(q_n) tends to zero for ANY choices of roots.
No continuous selector or uniform positive absorption bound is used.
Their successors w_n belong to R even though v_n may not.

Nash, (4), and (5) imply

    s_k-2M*a_n <= Q_k <= w_n,k
                              <= s_k-epsilon_n+(M+B)*a_n.

Consequently

    epsilon_n <= (3M+B)*a_n,
    norm(w_n-x)_infinity <= (4M+2B)*a_n.             (9)

There is no asserted individual floor w_n,k>=s_k. Differentiability,
(8), (9), and g_k>=0 give

    H(v_n)-H(x)=-epsilon_n*g_k+o(a_n) <= o(a_n),
    H(w_n)-H(x)=g dot (w_n-x)+o(a_n) >= o(a_n).

Both errors are o(a_n), because both displacements are O(a_n) and
a_n tends to zero. Dividing (6) by a_n>0 now gives 1<=o(1), a
contradiction. This proves the convex return-domain lemma.

## 4. The weighted raw tests produce that convex domain

Assume (1) and STRICT (2). Define

    R={v in [-B,B]^I:
        sum_i lambda_i^A*(v_i-s_i)>=0 for every trap A}. (10)

This is closed and convex and contains U, since every weight is
nonnegative. With no traps it is simply the whole box.

For every product root q, averaging over player i's own action gives

    sum_i lambda_i^A*(Q_i(q)-s_i)
                   =sum_{S contained in I} mu_q(S)*W_A(S) >= 0. (11)

Forcing i to Quit makes its payoff independent of its prescribed
hazard, so averaging r_i(S union {i}) under the full product law
equals Q_i(q). This proves the equality, including zero and sure
hazards. Nash then gives sum_i lambda_i^A*(w_i-s_i)>=0.
Thus every exact successor lies in R at every boxed source. This
uses (1) on coalitions OUTSIDE A as well as those inside it.

Now let q absorb at a source v in R and let A={i:q_i>0}. Suppose
A is a trap. Its supported Nash comparisons give Q_i-C_i>=0 on A.
There is an exact weighted identity

    sum_{i in A} lambda_i^A*(1-q_i)*(Q_i-C_i)
      =c(q)*sum_i lambda_i^A*(s_i-v_i)
          +sum_{empty != T proper-subset A} mu_q(T)*L_A(T). (12)

To see it, multiply player i's endpoint difference by 1-q_i.
The empty-opponent term obtains coefficient c(q). Each nonempty
opponent coalition T excluding i obtains the full product mass
mu_q(T). Summing over i gives (12), with no omitted simultaneous
coalition.

The left side is nonnegative. Its first right-hand term is
nonpositive by (10). A trap has at least two players. If some
active hazard q_i<1, the coalition A minus {i} has positive product
probability and is nonempty and proper. Hence the remaining sum is
strictly negative by (2), a contradiction.

If ALL active hazards equal one, the factors 1-q_i vanish and
(12) alone gives no contradiction. In that case apply (2) to
T=A minus {i}. It says

    lambda_i^A*(r_i(A)-r_i(A minus {i}))<0.

Every lambda_i^A is positive, so each participant strictly prefers
withdrawal. The all-sure root is not Nash either. This separate
case is necessary and covers the entire hazard boundary.

Therefore A is not a trap. Negating the finite trap condition gives
some active k with r_k(S)<=s_k for every S contained in A that
contains k. Its forced-Quit average is at most s_k; support
optimality gives w_k=Q_k<=s_k. The two premises of Section 3
are now proved from the raw table.

We conclude the strict analytic theorem: for any finite nonempty I,
with arbitrary signed singleton levels and participant premiums,
(1) and strict (2) exclude every C1 full exact-root unit-absorption
potential on any box strictly larger than the reward bound.

## 5. Fin4 uniform payoffs and weak leave

The existing four-player polynomial obstruction says that, under
normality and a positive singleton, absence of a uniform-equilibrium
payoff produces a rational polynomial potential on the fixed box
M+2. Its restriction to the literal exact-root relation satisfies
(6) on the same table, for every boxed source and every exact root.
There is no supplied root selection or behavioral realization of
continuation annotations in this statement.

Nonnegative singleton levels imply normality independently of all
other reward signs. Thus, if some singleton is positive, absence of
UE would contradict the strict analytic theorem. If all singleton
levels vanish, all Never is itself an exact uniform equilibrium:
a unilateral quitter against it receives its singleton zero.

For weak (2), add delta>0 to every passive reward coordinate r_i(S)
with i outside S, changing no participant coordinate. Singletons,
traps, and every W_A(S) are unchanged, since r_i(S union {i}) is
always a participant entry. Each L_A(T) decreases by

    delta*sum_{i in A minus T} lambda_i^A > 0.

All its weak comparisons become strict, so every perturbed table has
a uniform-equilibrium payoff and is within delta of the original.

Reward closure preserves the fixed-target quantifier. Choose delta_n
decreasing to zero and corresponding targets u_n in one common compact
payoff box, then pass to a convergent subsequence u_n to u. The same
behavioral strategies and transitions are available in all these games.
A uniform reward change of at most delta_n changes any expected
finite-horizon payoff by at most delta_n, for every prescribed or
deviating profile. Given accuracy, first fix n with both this error
and the target difference sufficiently small; then choose the uniform
profile and threshold for that nearby game. The unchanged profile
delivers u and bounds all deviations in the original game at every
larger horizon. The limit target u was fixed before accuracy.

The exact semantic declarations used are:

- `isQuittingNormalPlayer_of_singleton_nonneg` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`;
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`;
- `isQuittingFullExactRootPotential_of_robustPotential` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`;
- `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
  in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.

## 6. A signed open raw-table region

Here is one complete rational table, with own singleton vector
s=(1/10,1/10,1/10,1). Coalition digits name players.

| S | r(S) |
|---|---|
| 0 | (1/10,21/10,-9/10,2) |
| 1 | (-9/10,1/10,21/10,2) |
| 2 | (21/10,-9/10,1/10,0) |
| 3 | (-9/10,-9/10,-9/10,1) |
| 01 | (8/5,-9/10,11/10,2) |
| 02 | (-9/10,11/10,8/5,2) |
| 03 | (31/10,-9/10,-9/10,0) |
| 12 | (11/10,8/5,-9/10,2) |
| 13 | (-9/10,21/10,-9/10,0) |
| 23 | (-9/10,-9/10,21/10,0) |
| 012 | (1/5,1/5,1/5,2) |
| 013 | (21/10,21/10,-9/10,0) |
| 023 | (21/10,-9/10,21/10,0) |
| 123 | (-9/10,21/10,21/10,0) |
| 0123 | (21/10,21/10,21/10,0) |

The only trap is A=012. Each core pair has one premium 3/2 and
one premium -1. Player3 has premium -1 on every larger coalition
containing it and hence belongs to no trap. The core triple has all
three participant premiums 1/10. Take lambda=(1,1,1,0).

For singleton S inside the core, W_A(S)=1/2; for core pairs it is
3/5; for S=012 it is 3/10. At S=3 or03 it is 7, and at every
other S containing3 it is 6. For singleton T inside A, L_A(T)=-1/2;
for core pairs it is -9/10. Thus every nontrivial inequality in (1)
and every inequality in (2) is strict.

All own singletons are positive, and every nonsingleton participant
premium has a strict sign. These signs fix the trap list locally.
All the finite strict inequalities therefore persist in a full
sixty-coordinate open neighborhood, with the SAME weights and trap.
This is an open region of an explicit finite-inequality raw class,
not an implicit-function neighborhood of one prescribed controller.
No density or completeness claim for arbitrary games is made.

Every player has a negative participant premium somewhere, so the
set of individually nonnegative-premium players is empty. No protected
player criterion can apply. Furthermore no individual core player
weakly leaves every coalition inside its trap: each has a pair premium
3/2 while its passive centered payoff against that partner is -1.
Thus aggregate leave is not concealing an individual common leaver.
No pair in the table has two nonnegative participant premiums.

## 7. Exact boundary regressions

### Global floor tests cannot be restricted to the trap

Modify only r_0(03), r_1(13), r_2(23) in Section 6 to -1.
The trap list and all core-only W_A tests and L_A tests remain
unchanged and strict. But W_A(3)=-33/10<0. At source

    v=(1/10,1/10,1/10,0), q=(0,0,0,1),

the three core players have Continue -9/10 and Quit -1; player3
has Quit1 and Continue0. This is an exact root with successor
(-9/10,-9/10,-9/10,1), which violates the weighted floor:
the sum of its three centered core coordinates is -3. Hence the
global quantifier in (1) is mathematically necessary for this proof.

### A protected aggregate is not an individual floor

In the UNMODIFIED Section-6 table take

    v=(-29/10,1,13/5,0), q=(1/2,0,1/2,0).

This source lies in R because its core sum is 7/10>=3/10.
The endpoint pairs (Quit,Continue) are

    (-2/5,-2/5), (1/4,33/40), (17/20,17/20), (1/4,1).

The root is exact and has successor (-2/5,33/40,17/20,1).
It respects the weighted floor but violates player0's singleton
floor. The proof cannot replace R by the full singleton orthant.

### Sources outside R need not return to a lower boundary

Again in the same table take

    v=(1/30,1/30,1/30,1), q=(1/10,1/10,1/10,0).

Each core player has both endpoints 73/500. Player3's endpoints
are (729/1000,1109/1000). Thus the exact successor is
(73/500,73/500,73/500,1109/1000), strictly above all singletons.
The source violates R. This does not contradict return inside R;
it demonstrates why the minimum argument cannot apply return to the
perturbed outside source or assert arbitrary-source root collapse.

## 8. Bounded comparisons with existing raw producers

### Supportwise participant balance and product-low premiums

The implemented supportwise certificate requires nonnegative weights
normalized on an active support and a nonpositive weighted sum of
participant premiums on EVERY contained nonempty coalition. On
support012 and coalition012, every participant premium in Section 6
is 1/10. Every normalized weighted sum is therefore 1/10>0.
There is no certificate of that kind for this support.

The product-low predicate requires every absorbing independent
product law to have an active player whose forced-Quit payoff is at
most its singleton. It fails at q=(1,1,1,0): all active endpoints
are 1/5>1/10. This product law is not Nash, since withdrawal gives
11/10. That is the precise distinction: identity (12) uses Nash
and a weighted source constraint to exclude the bad support; the
product-low condition quantifies over product laws without either.

The exact source definitions are `IsSupportwiseQuittingPremiumWeightCertificate`
in `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumBalanceAt.lean`,
`IsSupportwiseBalancedQuittingPremiumTable` in
`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`,
and `HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`.
Their strategic consumer is `exists_uniformEquilibriumPayoff_of_supportwiseBalance`
in `UniformEquilibrium/Quitting/Classification/Existence/SupportwisePremiumUniformPayoff.lean`.

The weighted criterion is not claimed to subsume an individual
protected-leaver criterion. Indeed (2) at T=A minus {i} requires
EVERY member to weakly leave the whole trap. On two players take
s=(0,0), r(0)=(0,0), r(1)=(2,0), r(01)=(1,1). Player0 is
individually protected and strictly leaves the unique trap01, but
(2) at T={0} would require a positive multiple of 1 to be nonpositive.
Conversely Section 6 has no individually protected player at all.
The raw criteria are incomparable, although the convex-domain lemma
also accommodates protected-coordinate domains.

### Singleton and response-quotient screens

The centered singleton matrix, with receiver rows, is

    Gamma=[[0,-1,2,-1],[2,0,-1,-1],
           [-1,2,0,-1],[1,1,-1,0]].                (13)

Its012 principal block A has determinant7 and

    A_inverse=[[2,4,1],[1,2,4],[4,1,2]]/7,
    A*1=1.

For t>0, Az>=t1 with z>=0 and complementarity forces every
coordinate positive: if one were zero, its cyclic predecessor row
would be nonpositive. Hence z=t1. At t=0, a zero coordinate
propagates to all three; an all-positive solution would contradict
invertibility. Thus only z=0 solves the homogeneous child problem.

In the full homogeneous problem a positive pivot h=z_3 forces core
z_core=h1 and pivot residual h>0, a contradiction. At h=0 the
child vanishes. Therefore Gamma is R0. At offset (-1,-1,-1,1),
the core must be (1+h)1 and the pivot residual is 2+h. The unique
root is (1,1,1,0), with inactive residual2 and active determinant7.
The regular-root degree formula gives degree+1; the degree-not-one
exit does not apply.

Only the012 triple has a nonnegative inverse; the013,023,123
inverse blocks have respective negative entries -1,-1/3,-1/3.
The passive inverse row of012 is (-1/7,5/7,3/7). The full inverse
has entry -5/7 in row3,column1. No pair has both off-diagonal
entries positive. Principal23 is [[0,-1],[-1,0]], which is R0
but non-Q: offset (-1,-1) is infeasible. The full matrix is not
being called non-Q.

Rows in a target block of a response-invariant quotient must have
equal singleton row sums over every source block. These witnesses
exclude thirteen nondiscrete partitions:

| Partition | Compared rows | Source block | Unequal sums |
|---|---|---|---|
| 01 / 2 / 3 | 0,1 | 01 | -1,2 |
| 02 / 1 / 3 | 0,2 | 1 | -1,2 |
| 03 / 1 / 2 | 0,3 | 1 | -1,1 |
| 0 / 12 / 3 | 1,2 | 0 | 2,-1 |
| 03 / 12 | 1,2 | 12 | -1,2 |
| 0 / 13 / 2 | 1,3 | 0 | 2,1 |
| 02 / 13 | 0,2 | 02 | 2,-1 |
| 013 / 2 | 0,1 | 2 | 2,-1 |
| 0 / 1 / 23 | 2,3 | 0 | -1,1 |
| 01 / 23 | 0,1 | 01 | -1,2 |
| 023 / 1 | 0,2 | 1 | -1,2 |
| 0 / 123 | 1,2 | 0 | 2,-1 |
| 0123 | 0,3 | 0123 | 0,1 |

Only the discrete partition and012 / 3 survive. At the literal
root (0,0,0,t), the three core response residuals are
t+3t^2, t+2t^2, t+2t^2. Hence that last nontrivial quotient
fails too. The exceptional31/10 entry at03 is essential to this
specific exclusion.

The inspected declarations for these tests are
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`,
`exists_finset_r0Degree_eq_sum_sign_det` in `MathUE/LinearProgramming/R0DegreeSum.lean`,
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`,
and `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.

### Pure equilibria and universal quiet-child debt bounds

In the Section-6 table order, pure quitting coalitions have strict
improving players

    2,0,1,0,1,0,1,2,0,0,0,2,1,0,3,

with gains

    5/2,5/2,5/2,4,3,3,3,3,3,3,9/10,3,3,3,2.

Every listed withdrawal leaves another quitter. All Never also fails
because every own singleton is positive.

For thirteen proper children the following sure first-date singleton,
followed by Never if a deviation prevents absorption, is full terminal
Nash and has the stated profitable omitted player:

| Child | Sure owner | Omitted player | Outside gain |
|---|---|---|---|
| 0 | 0 | 2 | 5/2 |
| 1 | 1 | 0 | 5/2 |
| 2 | 2 | 1 | 5/2 |
| 3 | 3 | 0 | 4 |
| 01 | 0 | 2 | 5/2 |
| 02 | 2 | 1 | 5/2 |
| 03 | 0 | 2 | 5/2 |
| 12 | 1 | 0 | 5/2 |
| 13 | 1 | 0 | 5/2 |
| 23 | 2 | 1 | 5/2 |
| 013 | 0 | 2 | 5/2 |
| 023 | 2 | 1 | 5/2 |
| 123 | 1 | 0 | 5/2 |

Each child nonowner's join is nonprofitable. A sole owner who delays
faces opponents at Never and cannot exceed its positive singleton.
These comparisons include every complete behavioral deviation. All
prescribed profiles absorb surely.

For child012 repeat half-hazard solo blocks in order2,0,1, refining
each into n hazards alpha_n=1-2^(-1/n). Relative to the child's
singleton vector, its three macro values are (1,0,0),(0,1,0),(0,0,1).
Refined values interpolate between macro endpoints and retain every
singleton floor. Pure Continue is exact. The positive pair participant
premiums are all3/2, so immediate Quit is at most the current value
plus (3/2)*alpha_n. Adding that same error everywhere is a Bellman
supersolution. Opponent-only geometric survival removes its bounded
remainder, bounding every complete child regret by (3/2)*alpha_n.
Joint Never has probability zero.

The quiet player3 has payoff

    [4*r3(2)+2*r3(0)+r3(1)]/7=6/7.

Quitting at the first player2 microstage pays1-alpha_n, giving gain
1/7-alpha_n. This stays bounded away from zero while all child
regrets tend to zero. Every fixed finite nonnegative weighted sum
of child deviation debts, plus a fixed multiple of joint Never,
therefore fails to bound this outside gain universally over child
profiles. Along with the thirteen exact examples, for EVERY proper
child there exists an omitted player falsifying such a universal bound.
This does not exclude a method which selects a special child profile.

The exact source quantifier is that of
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
The full-deviation single-error calculation is the one formalized by
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
These are bounded actual-input exclusions, not a claim that every
other stationary or selected-child architecture fails.

## 9. Implementation boundary

The intended new raw theorem is (1)-(2) plus nonnegative singletons
implying existence of a uniform-equilibrium payoff on Fin4. Its
producer enumerates traps and checks the finite weight constraints.
The proof outputs the invariant polytope (10), identities (11)-(12),
the exact-root return, and the convex minimum exclusion. The existing
normal polynomial obstruction and reward-closure consumers then yield
the semantic target; no profile input is hidden in the raw predicate.

The reusable existing analytic and root inputs are
`IsQuittingFullExactRootPotential.singletonFace_drift` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`,
`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`, and
`abs_quittingRootSuccessorPayoff_sub_tail_le_reward_add_source_mul_absorptionMass`
in `UniformEquilibrium/Quitting/Root/BoundedSuccessorDisplacement.lean`.
The elementary proofs needed here are also supplied in Sections2-4.
The new convex support argument must retain both the segment-in-D
case and the all-binding-displacements-positive case. The Taylor
remainder must be measured relative to absorption, not merely to the
source perturbation. The all-sure support case must remain separate
from identity (12).

This packet supplies ordinary mathematical evidence and named semantic
dependencies, not a claim to a checked implementation of the new raw
criterion. It proves neither generic completeness of periodic strategies
nor the arbitrary finite-quitting-game conjecture.
