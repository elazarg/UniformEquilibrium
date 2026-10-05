# Two-player premium cores with a strict preference to leave the pair

## Raw data and conclusions

Let I be a finite player set with distinct designated players i and j.
A quitting game specifies a finite real vector r(S) in R^I for every
nonempty coalition S. At every live date, players independently choose
Quit or Continue. The first nonempty quitting coalition S absorbs at
reward r(S); the live-stage reward and the reward for perpetual
continuation are zero. Strategies use independent private randomization
and observation of the public history, without a public correlating device.
Unilateral deviations may replace a player's complete behavioral strategy.

Write s_k=r_k({k}). Assume the following three raw-table conditions:

1. For every S and every participant k in S, r_k(S)≥s_k.
2. For every k outside {i,j} and every S containing k, r_k(S)=s_k.
3. The designated core player i satisfies

       r_i({i,j}) < r_i({j}).                              (1)

Thus only i and j may receive positive participant premiums. Their
premiums on triples and larger coalitions can be arbitrary nonnegative
numbers. Every nonparticipant coordinate is arbitrary, subject only to
(1). In particular no outsider joining restriction, response symmetry,
stationary equilibrium, cycle, or child strategy is supplied.

Choose M≥0 bounding the absolute values of all rewards and choose B>M.
Put K=[−B,B]^I. A product root is a vector q in [0,1]^I. Write

    p_q(S)=product_(k in S) q_k * product_(k outside S)(1−q_k),
    c(q)=p_q(empty),                 a(q)=1−c(q),
    T_q(v)=sum_(S nonempty) p_q(S)r(S)+c(q)v.              (2)

Here v is an arbitrary continuation annotation after all Continue. It
need not be a payoff achievable by a strategy. Let Q_k(q) and C_k(q,v)
be the expected payoff to k from respectively pure Quit and pure Continue
at this finite root game, holding the other marginals fixed. Then

    (T_q(v))_k=q_k Q_k(q)+(1−q_k)C_k(q,v).

The root q is exact Nash at v precisely when

    (T_q(v))_k=max(Q_k(q),C_k(q,v)) for every k.           (3)

**Analytic theorem.** Under conditions 1–3, there is no C¹ function H
on a neighborhood of K such that

    H(v)−H(T_q(v))≥a(q)                                  (4)

for every v in K and every exact Nash root q at v. This conclusion holds
for every finite I containing i and j and permits signed singletons.
It excludes polynomials of every degree, not only a finite ansatz.

**Four-player theorem.** If I has four players and all s_k≥0, the same
raw table has a uniform-equilibrium payoff. Explicitly, there exists one
vector V such that, for every ε>0, there are a behavioral profile σ and
an integer N for which every horizon n≥N satisfies

    |Eσ[average payoff over n dates]_k−V_k|≤ε

for every k, and replacing any one player's complete behavioral strategy
can increase that player's expected n-date average payoff by at most ε.
The target V is fixed before ε; σ and N may depend on ε. The proof is
an existence argument, not an algorithm returning a specified strategy.

## 1. An exhaustive return property for the actual root game

Define the upper singleton box and its lower boundary by

    C=product_k[s_k,B],
    L={x in C : x_k=s_k for at least one k}.              (5)

For any exact root at v in K, its successor w=T_q(v) satisfies w_k≥s_k:
condition 1 implies Q_k(q)≥s_k, and (3) dominates that endpoint. Also w
belongs to K, because (2) is a convex combination of v and reward vectors.
Consequently w belongs to C.

Suppose in addition only that

    v_i≥s_i and v_j≥s_j.                                (6)

The other coordinates of v may be below their singletons. We claim that
every exact Nash root with a(q)>0 has successor in the same set L.

If any k outside {i,j} has q_k>0, its supported Quit action and condition
2 give

    w_k=Q_k(q)=s_k.

This equality uses every coalition containing k, including triples and
the grand coalition. It holds regardless of all the other hazards and
the two core players' participant premiums. Since w is already in C,
this entire case returns to L.

In the remaining case all outside hazards are exactly zero. Only now is
the designated player's endpoint gap the two-core formula

    Q_i(q)−C_i(q,v)
      =(1−q_j)(s_i−v_i)
          +q_j[r_i({i,j})−r_i({j})].                    (7)

If both core players were active, then q_j>0, and (1),(6) would make
(7) strictly negative. This contradicts the supported Quit action of i.
Thus at most one core player is active. Positive absorption forces exactly
one active core player k, whose opponents all Continue, so its Quit
endpoint and its successor coordinate both equal s_k. Again w belongs
to L. We have proved

    v in K, (6), exact root q, a(q)>0  ⇒  T_q(v) in L.   (8)

No positive outsider hazard has been discarded in obtaining (7), and
the target set in (8) is exactly the original L in (5).

## 2. The singleton-face derivative inequality

Assume for contradiction that H satisfies (4). For every x in C and
every k with x_k=s_k,

    ∇H(x)·(x−r({k}))≥1.                                (9)

First suppose x_l>s_l for all l≠k. Let k alone Quit with probability
t>0. Player k is indifferent. For each nonowner l, its endpoint gap at
t=0 is s_l−x_l<0. By continuity, every nonowner strictly prefers Continue
for all sufficiently small t>0. This uses the actual endpoints, including
r_l({k,l}) if l deviates; these rewards need not satisfy any upper cap.
Thus this sole-owner root is exact Nash, with absorption t and successor
x+t(r({k})−x). Divide (4) by t and let t decrease to zero to obtain (9).

For weak nonowner inequalities, replace each x_l with l≠k by
(1−δ)x_l+δB, keeping x_k=s_k. Because B>M≥s_l, all nonowner inequalities
become strict for δ>0. Apply the preceding argument and let δ decrease
to zero. Continuity of the gradient gives (9). The sole-owner rate may
depend on δ; no uniform rate is required at a multiple-face intersection.
The successor segments stay in K, including when x has upper-box
coordinates.

## 3. A boundary minimizer has a binding constant-participant player

The nonempty set L is compact. Choose x minimizing H on L, and put

    J={k:x_k=s_k},             g=∇H(x).

If J={k}, the small sole-owner root used above is exact Nash at x and
absorbs positively. Condition (6) holds because x belongs to C. By (8)
its successor returns to L, contradicting minimality and (4). Hence
|J|≥2.

Increasing one binding coordinate slightly retains another binding
coordinate and stays in L. Therefore g_k≥0 for k in J. A nonbinding
coordinate strictly below B admits two-sided feasible variations and
has g_k=0. A coordinate at B admits a feasible decrease and has g_k≤0.

Suppose J had no player outside {i,j}. Then J={i,j}. Apply (9) with
owner j. Its owner-coordinate term is zero. Its i term is nonpositive,
since

    g_i≥0,       r_i({j})>r_i({i,j})≥s_i.

Every nonbinding interior term is zero. Every upper-box term is
nonpositive because g_k≤0 and B−r_k({j})>0. The whole left side of
(9) is at most zero, contradicting its lower bound one. Consequently

    J0=J\{i,j} is nonempty.                             (10)

This argument uses one-sided conditions on the union of lower faces;
it does not assume that L is convex.

## 4. Selective perturbation and the absorption charge

For sufficiently small ε>0 let

    v_ε=x−ε*1_J0.

This stays in K. Both core coordinates are unchanged and still satisfy
(6). Differentiability gives

    [H(v_ε)−H(x)]/ε → −sum_(k in J0)g_k≤0.              (11)

Choose any exact Nash equilibrium q_ε of the finite root game at v_ε.
Finite-game Nash existence supplies it; no continuous root selection is
needed. All-Continue is not Nash, because each k in J0 would gain ε
by quitting alone. Hence a_ε=a(q_ε)>0. The exhaustive return property
(8) puts its actual successor w_ε in the original L.

For k in J0, w_ε,k≥s_k=v_ε,k+ε. For any absorbing root, write rbar for
its reward vector conditional on absorption. Equation (2) gives

    T_q(v)−v=a(q)(rbar−v),

and every coordinate of rbar lies in [−M,M]. Therefore

    ε≤w_ε,k−v_ε,k≤(M+B)a_ε.

By (4) and minimality on L,

    ε/(M+B)≤a_ε≤H(v_ε)−H(w_ε)≤H(v_ε)−H(x).             (12)

Dividing by ε contradicts (11), since M+B>0. This proves the analytic
theorem. It treats every full simultaneous root at the chosen annotation,
including roots with larger active coalitions, and returns each such
successor to the same minimization domain.

## 5. The exact four-player semantic implication

For a player k, its behavioral punishment value is the infimum, over
independent opponent behavioral profiles, of its best terminal payoff
over all replacements of its own strategy. Immediate Quit guarantees at
least s_k under condition 1. Against all-Never opponents the best payoff
is s_k when s_k≥0: quitting pays s_k and Never pays zero. Thus the
punishment vector equals s. In particular every player is normal, meaning
its singleton payoff is at least its punishment value.

If all s_k=0, all-Never is already exact Nash at every finite horizon.
Otherwise at least one singleton is positive. The proof uses the following
existing four-player obstruction theorem, stated here in the exact form
needed: for a bounded four-player normal quitting game with a positive
singleton, absence of a uniform-equilibrium payoff produces a rational
polynomial P and a positive rational tolerance δ≤1/4 such that, on the
box [−(M+2),M+2]^4, every full robust edge has

    P(source)−P(target)≥absorption.

A full robust edge uses an actual product root. Its coordinate Bellman
residual and its ordinary coordinate Nash regret are each bounded by δ
times that root's absorption probability. The theorem also excludes a
sure-quitter punishment-vector Nash root, but that conjunct is not needed
in this contradiction. No polynomial is supplied as an extra hypothesis.

Every exact Nash root with its exact successor is such an edge: both
errors are zero. Its successor stays in the same box by convexity of
(2). Hence the same P, with the same reward table, satisfies (4) with
B=M+2. A polynomial is C¹, contradicting Sections 1–4. The claimed
uniform-equilibrium payoff therefore exists. This is a full behavioral
and fixed-target conclusion, not a stationary or periodic deviation claim.

### Source declarations and implementation boundary

The ordinary analytic proof above is new input to the following existing
source interfaces; no formal implementation of that proof is asserted.

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` supplies the exact
  finite root used in Section 4.
- `IsQuittingFullExactRootPotential.singletonFace_drift` in
  `UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`
  is the existing formal version of the singleton-face inequality (9).
- `quittingPunishmentValue_eq_singleton_of_nonnegativePremium` in
  `UniformEquilibrium/Quitting/Classification/NonnegativePremiumPunishment.lean`
  gives the punishment identification. `IsQuittingNormalPlayer` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`
  uses precisely the normality inequality stated above.
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in
  `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
  is the actual four-player polynomial producer, with reward bound M,
  all-player normality, a positive singleton, rational δ in (0,1/4], and
  box radius M+2.
- `isQuittingFullExactRootPotential_of_robustPotential` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`
  restricts that same potential to all exact Nash/Bellman roots.

The proposed formalization can reuse the face derivative and root-existence
inputs. Its new step is the raw-table return split followed by minimization
on L and selective lowering of the binding constant-participant players.
The four-player composition needs no strategy-realizability premise for
the annotations and no theorem about rational reward tables.

## 6. A complete rational fixture beyond named existing screens

Here is a fully specified example on I={0,1,2,3}:

| Quitting coalition | Reward vector |
| --- | --- |
| {0} | (1,−1,−1,−1) |
| {1} | (0,0,2,−1) |
| {2} | (0,−1,0,2) |
| {3} | (4,2,−1,0) |
| {0,1} | (1,0,−1,−1) |
| {0,2} | (1,−1,0,−1) |
| {0,3} | (2,−1,−1,1) |
| {1,2} | (0,0,0,1) |
| {1,3} | (4,0,1,0) |
| {2,3} | (4,1,0,0) |
| {0,1,2} | (1,0,0,−1) |
| {0,1,3} | (1,0,−1,0) |
| {0,2,3} | (1,−1,0,0) |
| {1,2,3} | (4,0,0,0) |
| {0,1,2,3} | (1,0,0,0) |

Its singletons are s=(1,0,0,0). All participant premiums are nonnegative,
and the only positive participant premiums occur for 0 and 3 at {0,3}.
Take i=0,j=3. The strict comparison is 2<4, so the theorem applies.

### Product-low and universal boxed-root return

At hazards q_0=q_3=1/2 and q_1=q_2=0, absorption is 3/4. The two active
forced-Quit endpoints are 3/2 and 1/2, exceeding their singletons by 1/2.
Thus `HasProductLowQuittingPremium` fails literally. The producer
`exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`
cannot consume this fixture through its displayed premise.

Under nonnegative premiums,
`hasProductLowQuittingPremium_iff_weakSupportPeeling_of_nonnegative` in
`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSupportPeelingConverse.lean`
equates product-low with weak support peeling. The declaration
`weakPeeling_iff_every_boxedExactRoot_singletonLowerBoundary` in
`UniformEquilibrium/Quitting/Classification/NonnegativePremiumBoxBoundary.lean`
equates that condition with return to L for every absorbing exact root
at every annotation in the padded box. Our return statement (8) retains
the core annotation floors (6), and is not that universal return condition.
The selective perturbation is what permits its use in the proof.

### Singleton matrix tests

The singleton comparison matrix, with diagonal zero and off-diagonal
entry r_k({l})−s_k, is

    Γ=[[ 0,−1,−1, 3],
       [−1, 0,−1, 2],
       [−1, 2, 0,−1],
       [−1,−1, 2, 0]].                                  (13)

Every row has a distinct negative witness, so its normal core is full.
For clarity, a standard linear complementarity solution at offset b is
x≥0 with b+Γx≥0 and x_k(b+Γx)_k=0 for every k.

There is no nonzero homogeneous solution. If x_0>0, the three child
residual inequalities force all child coordinates positive. Their three
complementarity equalities then give x_1=x_2=x_3=x_0. The pivot residual
is x_0>0, contradicting its own complementarity. If x_0=0 and any child
coordinate is positive, the cyclic residual inequalities force all three
positive. Their residuals then vanish, and the invertible child matrix
forces all three zero, again a contradiction.

At offset b=(1,−1,−1,−1), child residual feasibility forces all three
children positive. Their equations give x_1=x_2=x_3=1+x_0, and the pivot
residual is 2+x_0>0. Hence the unique solution is x=(0,1,1,1), with
strict inactive pivot residual 2 and active determinant 7. The root-sum
degree formula gives degree +1, and its nonzero degree implies standard Q.
The relevant declarations are `exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` and
`isStandardQ_of_r0Degree_ne_zero` in `MathUE/LinearProgramming/R0Degree.lean`.
Thus the homogeneous, non-Q, and nonunit-degree exits do not apply.

The {0,1} principal, with both off-diagonal entries −1, has no solution
at offset (−1,−1) and has no nonzero homogeneous solution. Therefore the
full matrix fails projective Q-bar. On the three-child principal A, the
pivot row (−1,−1,3) times A⁻¹ has middle entry −3/7. Every other triple
has a row with two negative off-diagonal entries and zero diagonal; an
entrywise nonnegative inverse would make the corresponding diagonal
entry of its product with that inverse nonpositive, contradicting one.
The full inverse has entry (0,1)=−9/7. No two-player principal has both
off-diagonal entries positive. These computations exclude the applicable
nonnegative-inverse/passive-row tests, including
`exists_uniformEquilibriumPayoff_of_strictInverse_passiveRows` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/StrictInversePassiveRowCycle.lean`.

### All response partitions

Response invariance on a block-constant hazard cube requires any two
players in one block to have identical Γ-row sums over each block.
This is the necessary condition
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
The fourteen nondiscrete partitions are exhausted as follows.

For a single merged pair {0,1}, singleton column 3 compares 3 with 2.
Every other merged pair has a remaining singleton column comparing −1
with 2. Thus all six single-pair merges fail. For two pairs,
{0,1}|{2,3} compares within-{2,3} sums −1 and 2;
{0,2}|{1,3} compares within-{1,3} sums 2 and −1;
{0,3}|{1,2} compares within-{0,3} sums 3 and −1.
Every triple containing 0 has a singleton column with both −1 and 2.
The full block has pivot row sum 1 and child row sums zero.

Only {0}|{1,2,3} survives this first-order test. Give player 0 hazard
t>0 and all three children hazard zero. At discount complement zero,
the literal displacement is opponent absorption times forced-Quit payoff
minus the absorbing Continue contribution. The latter is −t for each
child. Forced Quit pays zero to 1 and 2 and t to 3, by the {0,3} premium.
Thus the three residuals are t,t,t+t². They are not identical. This is
exactly `quittingDiscountedDisplacement` in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`.
No nondiscrete response-invariant partition exists; the discrete partition
is the ambient degree-one matrix itself.

### Every proper-child five-kind F/J family fails

For a proper nonempty child set S, keep all omitted players at Never.
A child equilibrium has zero deviation debt for each child. If its joint
Never probability is zero, any five-kind withdrawal/future-join certificate
for a missing player would impose

    outside debt ≤ sum_k nonnegative_weight_k*(child debt_k)
                     + nonnegative_constant*(child joint Never).   (14)

The following witnesses give positive outside debt and a zero right side
for every proper nonempty S.

1. For one or two children in {1,2,3}, choose a sure solo owner, choosing
   the predecessor of the other retained child when there are two. The
   other child receives 2 and prefers Continue. A missing child receives
   −1 and joins for zero.
2. For S={1,2,3}, use solo hazards 1/2 in order 1,2,3, repeated forever.
   Its three child-value vectors are (0,1,0), (0,0,1), (1,0,0). Each
   solo owner is indifferent, every other Quit endpoint is zero, and
   the Bellman recurrences hold exactly. Opponent survival contracts
   each period, so iterating these comparisons bounds every complete
   behavioral deviation. The quiet pivot's three values are 4/7,8/7,16/7;
   at the first phase it can Quit for one, strictly above 4/7.
3. If 0 belongs to S and 3 does not, every child Quits surely at the
   first date. Withdrawal lowers a nonpivot's payoff to −1 and lowers
   the pivot's payoff to zero; for S={0}, its withdrawal gives Never
   payoff zero. A missing nonpivot receives −1 and gains by joining.
   The special {0,3} joining payoff, when relevant, is one and is still
   strictly better.
4. If {0,3} is contained in S but 2 is not, child 3 alone Quits surely.
   The pivot receives 4 rather than the pair's 2. A retained child 1
   receives 2; owner 3 is indifferent between its zero singleton and
   Never. Missing player 2 receives −1 and joins for zero.
5. For S={0,2,3}, child 2 Quits surely, while 0 and 3 use first-date
   hazards 2/3 and 1/4. They use Never thereafter if needed. The pivot
   and child 3 have equal Quit and Continue endpoints, one and zero
   respectively. Child 2 has Quit payoff zero and Continue payoff −3/4.
   The missing player 1 receives −5/6 and joins for zero.

These cases cover all fourteen children. They have zero joint Never and
are exact child Nash against all behavioral deviations: the one-date
witnesses have all opponents at Never after that date, so any later Quit
offers only the deviator's singleton and gives no better response than
the computed first-date comparison. In case 5, child 2's later singleton
is zero, as already used in its Continue calculation.

The existing common bound is
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
Its five kinds are patient, deadline, evaluated security, terminal security,
and cancellation. Equation (14) is its relevant implication, so these
witnesses exclude every full proper-child family of any of those kinds.
They do not exclude the child equilibria themselves or other child methods.

## Scope and nonclaims

The analytic theorem excludes every C¹ full exact-root potential for the
stated raw class. The semantic conclusion is a four-player existence
theorem with unrestricted behavioral deviations and one fixed target.
The proof does not solve arbitrary four-player or arbitrary finite-player
quitting games. It requires constant participant rewards outside the pair
and the strict leave preference (1).

The fixture supplies bounded, explicit failures of the named existing
screens, not an exhaustive classification of all possible proof methods
or repository producers. The mathematical argument and its actual-data
adapter are ordinary mathematics here; source correspondences do not
constitute a Lean implementation or a build claim for this new theorem.
