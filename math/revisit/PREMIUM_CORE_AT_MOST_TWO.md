# Quitting games with greatest premium core of size at most two

## The raw class and exact conclusion

Let I={0,1,2,3}. For every nonempty coalition S⊆I, a quitting game has
a finite real reward vector r(S). At each live date, players independently
choose Quit or Continue. The first nonempty quitting coalition absorbs at
its reward. Live-stage reward and perpetual-continuation reward are zero.
Players may use arbitrary behavioral strategies with private independent
randomization and observation of public history. No public correlating
device is added.

Put s_k=r_k({k}). Assume

    s_k≥0,
    r_k(S)≥s_k whenever k∈S.                            (1)

Call a nonempty set A a premium trap if every k∈A has some coalition
S⊆A containing k for which r_k(S)>s_k. The witnessing coalition can
depend on k. Define the greatest premium core C to be the union of all
premium traps, with C empty when there is no trap.

**Theorem.** If |C|≤2, the original quitting game has a uniform-equilibrium
payoff. Explicitly, there is one vector V such that, for every ε>0, some
behavioral profile σ and some integer N satisfy, for all horizons n≥N:

- every coordinate of the expected n-date average payoff under σ is
  within ε of V;
- replacing any one player's complete behavioral strategy increases
  that player's expected n-date average payoff by at most ε.

The target precedes ε. The profile and the common threshold may depend
on ε. The theorem neither assumes a selected strategy, root, child game,
cycle, or continuation payoff nor restricts deviations to stationary or
periodic policies. It is an existence theorem, not a strategy algorithm.

Players outside C can have positive participant premiums on coalitions
requiring other outside players. The hypothesis is therefore strictly
broader than having at most two globally nonconstant participant-payoff
coordinates. No restrictions are imposed on passive rewards.

## 1. Finite core calculation and exact root geometry

The union of two premium traps is a trap: every member retains an old
witness. Since I is finite, a nonempty C is itself the greatest trap.
A singleton is never a trap. One can compute C by repeatedly removing
from the current set A a player k whose participant reward equals s_k
on every coalition inside A containing k. No trap can lose its first
member, since that member would retain its positive witness. Any nonempty
terminal residual is a trap because every surviving player has a witness.
Thus every removal order ends at C. This is a reward-table calculation;
no actual strategic player is removed from the game.

For the analytic argument allow any finite I and signed s, but retain
nonnegative participant premiums. Choose M≥0 bounding all absolute reward
coordinates, B>M, and write

    K=[−B,B]^I,
    U=product_k[s_k,B],
    L={x∈U : x_k=s_k for at least one k}.                (2)

For independent hazards q∈[0,1]^I, let p_q(S) be the product probability
of the exact quitting coalition S, c(q)=p_q(empty), and a(q)=1−c(q).
For a continuation annotation v define

    T_q(v)=sum_(S nonempty)p_q(S)r(S)+c(q)v.              (3)

The annotation is arbitrary and need not be achievable by a strategy.
Let Q_k(q) and C_k(q,v) be the two pure-action endpoints, Quit and
Continue. The root is exact Nash at v if

    (T_q(v))_k=max(Q_k(q),C_k(q,v)) for all k.            (4)

This is the ordinary simultaneous finite-game Nash condition.

Every exact successor w=T_q(v) with v∈K belongs to U: each Quit
endpoint is at least its singleton by nonnegative participant premiums,
and (4) dominates that endpoint; convexity of (3) bounds w inside K.

Suppose now C={i,j}. Both core players have strictly positive premiums
at {i,j}, because their only possible positive witness inside this pair
is the pair itself. Two facts will replace global outsider flatness.

**Support return.** If a(q)>0 and its active support A={k:q_k>0}
is not C, then A is not a trap. Otherwise A⊆C, and its only possible
proper nonempty subsets would be singletons, which are not traps.
Thus some active k is flat on every participant coalition inside A.
Its forced-Quit coalition is always inside A, so Q_k(q)=s_k. Supported
Quit and (4) give w_k=s_k. Consequently

    exact root, a(q)>0, active support≠C ⇒ T_q(v)∈L.    (5)

This retains all simultaneous coalitions and all positive hazards.

**Outsider flatness on the core face.** For every k outside C and T⊆C,

    r_k(T∪{k})=s_k.                                    (6)

A strict premium there, together with the pair witnesses of i and j,
would make C∪{k} a larger trap. In particular every outsider's Quit
endpoint against a core-only root is exactly its singleton. This is not
a claim of global outsider flatness.

If C is empty, the support-return reasoning gives an active flat player
at every absorbing product root. This is exactly the existing product-low
criterion, whose uniform-payoff producer handles that case under (1).
It remains to treat C={i,j}.

## 2. Common smooth-potential and boundary facts

We will exclude a C¹ function H on a neighborhood of K satisfying

    H(v)−H(T_q(v))≥a(q)                                 (7)

for EVERY v∈K and EVERY exact Nash root at v. This excludes polynomials
of all degrees. Finite-player analytic claims below permit signed
singletons; the final strategic application uses four players and (1).

Whenever x∈U and x_k=s_k,

    ∇H(x)·(x−r({k}))≥1.                                (8)

First suppose every other coordinate is strictly above its singleton.
Let k alone Quit with a small positive probability t. It is indifferent,
while each other player's gap at t=0 is s_l−x_l<0. Continuity of the
ACTUAL endpoints, including the pair reward if l joins, makes this an
exact root for sufficiently small t. Its successor is x+t(r({k})−x),
and its absorption is t. Apply (7), divide by t, and let t decrease to
zero. For weak nonowner inequalities, move all nonowner coordinates
toward B by a positive amount, retaining x_k=s_k, and then pass to the
limit using continuity of ∇H. The root rate can depend on this movement.
All segments stay in K, even when some coordinates of x equal B.

Choose a minimum x of H on compact nonempty L, put

    J={k:x_k=s_k},                 g=∇H(x).

If J were a singleton, the small sole-owner root just constructed would
have its owner successor coordinate equal to its singleton and all others
at least theirs. It would return to L with positive absorption, contradicting
minimality and (7). Thus |J|≥2. Increasing one binding coordinate leaves
another binding coordinate, so g_k≥0 for k∈J. Nonbinding coordinates
strictly below B have g_k=0; coordinates at B have g_k≤0.

We repeatedly use the following actual charge estimate. If v∈K,
w=T_q(v), and a(q)>0, then

    w−v=a(q)(rbar−v),       |w_k−v_k|≤(M+B)a(q),        (9)

where rbar is the conditional reward given absorption. Therefore if a
binding coordinate is lowered by at least ε and an exact successor
returns to L, its absorption is at least ε/(M+B). Minimality then yields

    ε/(M+B)≤a(q)≤H(v)−H(w)≤H(v)−H(x).                  (10)

The arguments below produce such sources and roots while making the last
difference divided by ε tend to a nonpositive number.

## 3. Strict preference to leave the pair

Suppose, after interchanging the labels if necessary,

    r_i({i,j})<r_i({j}).                                (11)

Every absorbing exact root whose source has v_i≥s_i returns to L.
Indeed (5) handles every support except C. On support C all outside
hazards are zero, and the designated player's endpoint gap is

    (1−q_j)(s_i−v_i)+q_j[r_i({i,j})−r_i({j})]<0.

This contradicts its supported Quit action. The other core source floor
is not needed in this particular return calculation.

At the boundary minimum, if J contained only core players, it would
equal {i,j}. Apply (8) with owner j. Its owner term vanishes; the i term
is nonpositive because g_i≥0 and r_i({j})>r_i({i,j})≥s_i. Every
nonbinding interior term is zero, and every upper-box term is nonpositive
because B exceeds all rewards and its gradient coordinate is nonpositive.
This contradicts (8). Thus D=J\C is nonempty.

Set v_ε=x−ε*1_D. The core coordinates remain unchanged and above their
singletons. Finite Nash existence supplies an exact root. All-Continue
is not Nash since every lowered coordinate gains ε by quitting alone.
The just-proved exhaustive return property puts its successor in the
original L. But

    [H(v_ε)−H(x)]/ε → −sum_(k∈D)g_k≤0,

contradicting (10). This excludes (7) under (11).

## 4. Mutual strict preference to join: the exact index producer

Put A_i=r_i({i,j}), b_i=r_i({j}), and analogously A_j,b_j. Suppose

    d_i=A_i−b_i>0,             d_j=A_j−b_j>0.            (12)

If all outsider passive rewards at {i,j} are at least their singletons,
the pure pair is an exact root at v=r({i,j}): both core players prefer
joining by (12), and outsiders have Quit endpoints s_k by (6). Its
successor equals v and its absorption is one, contradicting (7).
Otherwise there is a fixed outsider h with

    r_h({i,j})<s_h.                                     (13)

The pure core pair is then not an exact root at ANY annotation while
all outsiders are inactive. Its strict blocker is annotation-independent.

### A concrete degree fact

Let F:R^n→[0,1]^n be continuous and have just one fixed point p. If F
is C¹ near p and det(I−DF(p))≠0, then that determinant is positive.
To prove this, use the larger open cube W=(−1,2)^n and z=(1/2,...,1/2).
The fields

    q−[(1−t)F(q)+tz],             0≤t≤1,

never vanish on the boundary of W, since the bracket belongs to [0,1]^n.
Homotopy invariance gives total degree +1 for q−F(q), by normalization
of the translated identity. Write D=I−DF(p), and choose m>0 with
||Du||≥m||u||. On a sufficiently small cube about p, differentiability
makes the difference between p+u−F(p+u) and Du at most (m/2)||u||.
The straight-line homotopy to D(q−p) has no boundary zero there. Its
local degree is sign det D. Excision, since p is the only root, equates
this with the total degree +1. This proves the fact, including when p
is on the boundary of [0,1]^n: it is interior to the larger ambient cube.

### Full clipped map and all core-only roots

For a fixed source v, extend the independent-coalition endpoint gaps
g_k(q)=Q_k(q)−C_k(q,v) polynomially to all q∈R^I and define

    F_v(q)_k=min(1,max(0,q_k+g_k(q))).                   (14)

This actual continuous map is globally cube-valued. Its fixed points are
exactly the full Nash roots: g_k≤0 at q_k=0, g_k≥0 at q_k=1, and
g_k=0 when 0<q_k<1. No equilibrium-selection or degree assumption is
being supplied as input.

Only on the face with all outsider hazards zero do the core gaps reduce to

    g_i=s_i−v_i+(v_i−s_i+d_i)q_j,
    g_j=s_j−v_j+(v_j−s_j+d_j)q_i.                       (15)

If some core annotation is below its singleton, its gap is positive
at every opposing core hazard, being a convex combination of s_i−v_i>0
and d_i>0. That player must Quit surely, and then the other must also
Quit surely. The blocker (13) excludes this root. Consequently every
exact root has support other than C in this case.

Now suppose v_i>s_i and v_j>s_j. A single active core player is impossible
because its gap against zero opposing hazard is negative. If one core
hazard is one, the other is forced to one, again excluded by (13).
Apart from all-Continue, the only possible core-only root is

    p_i=(v_j−s_j)/(v_j−s_j+d_j),
    p_j=(v_i−s_i)/(v_i−s_i+d_i),
    p_k=0 for k outside C.                             (16)

Both displayed nonzero hazards are strictly interior; hence c(p)>0.
Suppose some annotation is below its singleton and no outsider gap at
p equals zero. All-Continue is then impossible. If an outsider gap at p
is positive, p is not Nash either and finite Nash existence supplies a
different root. Otherwise all outsider gaps are strictly negative.
Their rows in (14) are locally constant zero. The core rows are locally
q_k+g_k(q), since their clipping is inactive. In core-first coordinates
the derivative of q−F_v(q) therefore has block form

    [[0,−alpha_i,*],
     [−alpha_j,0,*],
     [0,0,Id]],

where alpha_i=v_i−s_i+d_i>0 and alpha_j=v_j−s_j+d_j>0. The determinant
is −alpha_i*alpha_j<0. The starred derivatives contain the full larger-
coalition effects and are unrestricted; the identity block makes them
irrelevant to the determinant. The degree fact rules out p as the only
fixed point. Thus there is a different exact root. Every such root has
positive absorption and support other than C, so (5) returns it to L.

### Source perturbations and the same boundary minimum

At the minimum x, if J meets C, set v_ε=x−ε*1_J. The preceding below-
singleton argument excludes support C. All-Continue is impossible, and
any exact root has positive absorption and returns to L by (5).

If J avoids C, keep the two core annotations exactly fixed. They are
strictly above their singletons, so the candidate p in (16) is independent
of all outsider annotations. For each outsider k choose

    0<η_k<ε²,
    v_ε,k=x_k−ε*1_(k∈J)−η_k,                          (17)

avoiding g_k(p)=0. This is possible because (6) gives Q_k(p)=s_k,
whereas its Continue endpoint is

    sum_(nonempty T⊆C)p_p(T)r_k(T)+c(p)v_ε,k.

The coefficient c(p) is positive, so at most one η_k is forbidden in
the interval (0,ε²). These choices are independent. At least one outsider
remains ε below its singleton, ruling out all-Continue. The index
producer above supplies an exact root with support other than C and
successor in the original L.

Every source in both cases stays in K for sufficiently small ε: x≥s≥−M
leaves fixed lower clearance, and coordinates only decrease. The original
table and the pure-pair blocker do not change. The small corrections in
(17) are O(ε²), without needing continuous dependence on ε. Consequently

    [H(v_ε)−H(x)]/ε → −sum_(k∈J)g_k≤0.

Any k∈J moves upward by at least ε at the chosen exact successor, so
(9)–(10) contradict this limit. This excludes (7) under (12). The proof
produces a good root; it does not claim that every absorbing root returns.

## 5. Four-player semantic consumer and equality cases

For nonnegative singletons and participant premiums, immediate Quit
guarantees s_k against every opponent behavior. Against all-Never
opponents, the unrestricted response cap is exactly s_k. Thus the
behavioral punishment vector equals s, and all players are normal, meaning
their singleton payoffs cover their punishment values.

The following existing four-player result is the semantic input. In a
bounded normal four-player game with some positive singleton, absence of
a uniform-equilibrium payoff produces a rational polynomial P and a
positive rational δ≤1/4 with unit absorption drift on the FULL robust
root relation in box [−(M+2),M+2]^4. Its robust edges use the actual
product root, and require both coordinate Bellman residual and ordinary
coordinate Nash regret to be at most δ times absorption. No polynomial
or strategy is an additional hypothesis. The same no-equilibrium
implication also excludes a sure-quitter punishment-vector Nash root,
but that conjunct is not needed here.

Every exact Nash root and its exact successor give a robust edge with
both errors zero. The successor remains in the same box by (3).
Therefore the same polynomial satisfies (7) with B=M+2. Sections 3–4
exclude it whenever one leave comparison is strict or both join
comparisons are strict. If all s_k=0, all-Never is already exact Nash
at every horizon, so the positive-singleton input is unnecessary.

It remains to cover equality, for example r_i({i,j})=r_i({j}). For
each δ>0, increase only the passive coordinate r_i({j}) by δ. This
changes no own singleton, participant premium, premium trap, or greatest
core. The nearby table satisfies strict leave and hence has a UE.

Existence of a uniform-equilibrium payoff is closed under uniform reward
approximation. Here is the fixed-target reasoning. For δ_m→0 choose
nearby targets V_m. They lie in one bounded reward box, so along a
subsequence V_m→V. For each requested ε choose one sufficiently close
table and one of its uniform profiles with error below ε/4, reward
distance below ε/8, and target distance below ε/4. The same profile and
every unilateral replacement have average-payoff differences at most
δ_m at every horizon, because the transition law and behavioral strategy
space are unchanged. Thus the original game's delivery error is below
ε and its full deviation gain is below ε. The same eventual threshold
works for every larger horizon. No profile limit is taken, and V is fixed
before ε. This supplies equality without claiming that the analytic C¹
exclusion itself is closed under reward limits.

For the pair core, either one player weakly prefers leaving or both
strictly prefer joining. The strict proofs and this equality argument
therefore exhaust all comparisons. Together with the empty-core case,
they prove the theorem.

## 6. Exact examples and bounded source separation

### A layered-premium family with greatest core {0,3}

For any θ≥0, consider the following fully specified table:

| Coalition | Reward |
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
| {0,1,2} | (1,θ,0,−1) |
| {0,1,3} | (1,0,−1,0) |
| {0,2,3} | (1,−1,0,0) |
| {1,2,3} | (4,0,0,0) |
| {0,1,2,3} | (1,0,0,0) |

Player 2 is globally flat. After peeling it, player 1 is flat. The
residual {0,3} is a trap with strict leave comparison 2<4. At θ=0,
only 0 and 3 have nonconstant participant rewards. At θ=1/2, three
players have positive participant premiums, so the constant-outsider
two-player statement does not apply under any relabeling, while the
greatest-core theorem does.

At q_0=q_3=1/2 and other hazards zero, the two active Quit endpoints
are 3/2 and 1/2, both 1/2 above their singletons. This refutes product-low
for every θ. The singleton matrix, unaffected by θ, is

    Γ=[[0,−1,−1,3],[-1,0,−1,2],[-1,2,0,−1],[-1,−1,2,0]].

It is R0: a positive homogeneous pivot variable forces all children
positive, then the child equalities make them equal to the pivot and
give a positive pivot residual, impossible. A zero pivot and any positive
child force all children positive, contradicting invertibility of their
matrix. At offset (1,−1,−1,−1), child feasibility forces positivity,
then x_1=x_2=x_3=1+x_0 and the pivot residual is 2+x_0. The unique
solution is (0,1,1,1), with strict inactive residual 2 and active
determinant 7. The root-sum formula therefore gives degree +1 and
standard Q. Homogeneous, non-Q, and nonunit-degree exits do not apply.

The {0,1} principal is R0 but not Q: both off-diagonal entries are −1,
and offset (−1,−1) is infeasible. Thus projective Q-bar fails. On the
child principal A for {1,2,3}, the pivot row times A⁻¹ is
(9/7,−3/7,1/7). Every other triple has a zero-diagonal row with both
off-diagonal entries negative, ruling out an entrywise nonnegative
inverse. The full inverse has entry (0,1)=−9/7. No pair has two positive
off-diagonal entries. These exclude the applicable inverse/passive-row
tests, not every conceivable matrix argument.

There is no nondiscrete response-invariant partition. The necessary
block-row-sum condition eliminates the six single-pair merges: {0,1}
compares 3 with 2 in column 3, and each other merge has a remaining
singleton column comparing −1 with 2. For pair-pair partitions the
within-block unequal sums are respectively (−1,2), (2,−1), and (3,−1).
Every triple containing 0 has a singleton column with both −1 and 2.
The full block has pivot row sum 1 and child sums zero. The only remaining
partition {0}|{1,2,3} fails the full response field: at hazards
(t,0,0,0), its child displacements are t,t,t+t². The θ-coordinate is
invisible at those hazards. Thus all fourteen nondiscrete partitions fail.

Every proper-child five-kind withdrawal/future-join family also fails.
Its necessary inequality bounds outside deviation debt by nonnegative
weights times child debts plus a nonnegative multiple of joint Never.
For every proper nonempty child, the following exact child equilibria
have zero joint Never and a missing player's strictly positive debt:

1. For one or two nonpivot children, a sure solo owner gives the other
   retained child 2 when needed; a missing child receives −1 and joins
   for zero.
2. For {1,2,3}, repeat solo hazards 1/2 in order 1,2,3. The child
   values are (0,1,0), (0,0,1), (1,0,0). Bellman equalities and both
   action comparisons hold; geometric opponent survival controls all
   behavioral deviations. The quiet pivot gets 4/7 and can Quit for one.
3. If 0 belongs to the child but 3 does not, all children Quit surely
   at the first date. Withdrawal lowers any nonpivot's payoff to −1
   and the pivot's to zero; a singleton pivot can only obtain its own
   singleton by delaying. The θ-coordinate only raises a prescribed
   participant payoff. A missing nonpivot receives −1 and improves by
   joining.
4. If {0,3} is contained in the child but 2 is not, player 3 alone
   Quits surely. The pivot receives 4 rather than its joining reward 2;
   retained player 1 receives 2; missing player 2 gets −1 and joins
   for zero.
5. For {0,2,3}, use first-date hazards 2/3,1,1/4 in that order and
   Never thereafter if needed. Players 0 and 3 have equal endpoints
   one and zero, while player 2 gets zero from Quit and −3/4 from
   Continue. Missing player 1 receives −5/6 and joins for θ/2.

These cases exhaust the fourteen children. In the one-date cases, any
survival after a unilateral change leaves opponents at Never, so later
Quit only supplies the deviator's singleton and creates no omitted gain.
The universal debt bound would force the displayed positive outside
debt to be zero, for every weight choice. This excludes those five
universal child-certificate families, not all selected-child methods.

### A real bad root of negative index, with a different returning root

On three players with core {0,1}, set

    r({0})=(1,−1,3), r({1})=(0,0,3), r({2})=(3,3,0),
    r({0,1})=(2,1,−1), r({0,2})=(1,3,0),
    r({1,2})=(3,0,0), r({0,1,2})=(1,0,0).

At v=(2,1,−1/10), the root p=(1/3,1/3,0) has exact gaps
(0,0,−53/45), successor (4/3,1/3,53/45), and determinant −9 for
the ambient derivative of q−F_v(q). Its successor is strictly above
every singleton. The different root (0,0,1) has gaps (−2,−3,1/10)
and successor (3,3,0) in L. Thus an exceptional root can be genuine;
the proof needs selection, not a false universal-return assertion.
At v=(2,1,−11/4), the same mixed candidate has an outsider tie.
Lowering the outsider annotation by η>0 makes its gap 4η/9>0, so
the candidate ceases to be Nash and the direct finite-Nash branch applies.
These are exact rational substitutions into the full endpoint polynomials.

## 7. Tracked source correspondences and formalization boundary

The proof uses the following precise existing inputs; none is an
additional supplied strategy or uninhabited parity interface.

- Core-free coverage: `HasWeakQuittingPremiumSupportPeeling` and
  `hasWeakQuittingPremiumSupportPeeling_iff` in
  `UniformEquilibrium/Quitting/Classification/QuittingPremiumSupportPeelingOrder.lean`;
  `hasProductLowQuittingPremium_iff_weakSupportPeeling_of_nonnegative` in
  `UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSupportPeelingConverse.lean`;
  `exists_uniformEquilibriumPayoff_of_productLowPremium` in
  `UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`.
  Their support-peeling premise is exactly the empty-core case, not a
  residual two-player core.
- Finite exact roots: `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`. The existing
  `IsQuittingFullExactRootPotential.singletonFace_drift` in
  `UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`
  is the formal counterpart of (8).
- Degree: `ambientDegree_homotopy` and
  `ambientDegree_affineRootField_eq_sign_det` in
  `MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`;
  `ambientDegree_excision` in `MathUE/Topology/AmbientDegreeProperties.lean`;
  `ambientDegree_of_selfMap_eq_one` in
  `MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`.
  These have implemented theorem proofs. The affine field is literally
  D(q−p), so the determinant sign matches q−F_v(q). For normalization
  one can use enclosing chart [−2,3]^I and source W=(−1,2)^I;
  the explicit remainder homotopy supplies the local nonlinear comparison.
- Normality and the actual polynomial producer:
  `quittingPunishmentValue_eq_singleton_of_nonnegativePremium` in
  `UniformEquilibrium/Quitting/Classification/NonnegativePremiumPunishment.lean`;
  `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in
  `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`;
  `isQuittingFullExactRootPotential_of_robustPotential` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`.
  They retain the same actual table, polynomial, box, and absorption charge.
- Reward closure: `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
  in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
  Its nearby targets may vary; the conclusion selects one fixed target.
- Fixture checks: `exists_finset_r0Degree_eq_sum_sign_det` in
  `MathUE/LinearProgramming/R0DegreeSum.lean` and
  `isStandardQ_of_r0Degree_ne_zero` in `MathUE/LinearProgramming/R0Degree.lean`;
  `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
  in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`;
  `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean` and
  `quittingDiscountedDisplacement` in
  `UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`;
  `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.

The new mathematical producer is the support-return/core-face-flatness
reduction together with the actual negative-index root selection and
boundary-minimum contradiction. The named source inputs do not already
produce that selection from a residual pair. This packet supplies ordinary
mathematical evidence and an explicit adapter, not a Lean build claim.

## Scope

The result settles this raw four-player class, not arbitrary four-player
quitting games. A remaining counterexample with nonnegative singletons
and nonnegative participant premiums must have greatest premium core
of size at least three. Games with negative participant premiums are
also outside the statement. The finite-player smooth-potential exclusion
for strict comparisons does not enlarge the specifically four-player
semantic polynomial producer, and reward closure of UE is not asserted
to be closure of C¹ exact-root exclusion.

The exact examples separate the result from the named existing screens.
They do not classify every possible strategy architecture or claim that
the examples are equilibrium counterexamples.
