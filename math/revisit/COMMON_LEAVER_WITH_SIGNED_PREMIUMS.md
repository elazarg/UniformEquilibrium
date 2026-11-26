# A common leaver with signed premiums in four-player quitting games

## 1. Game, finite reward criterion, and conclusion

Let I={0,1,2,3}. For every nonempty coalition S⊆I prescribe a finite
real reward vector r(S). At each live date, players independently choose
Quit or Continue. The first nonempty quitting coalition absorbs at its
reward. Live-stage and perpetual-continuation rewards are zero. Players
may use arbitrary behavioral strategies with private independent
randomization. No public correlation or bounded-controller restriction
is added.

Write s_i=r_i({i}). A **premium trap** is a nonempty A⊆I such that
every i∈A has a nonempty S⊆A containing i with r_i(S)>s_i. Let C be
the union of all premium traps, or ∅ if there are none. Unions of traps
are traps: each member keeps its original witness. Thus C, when
nonempty, is the unique greatest trap. No singleton is a trap.

The following are conditions on the original finite reward table:

1. All own singleton rewards satisfy s_i≥0.
2. There is a player p such that r_p(S)≥s_p for every S containing p.
3. Every premium trap contains p.
4. For every nonempty T⊆C\{p},

       r_p(T∪{p})≤r_p(T).                              (1)

Condition 2 is imposed only on p. All other players may have arbitrary
positive or negative participant premiums. Passive rewards outside C
are unrestricted. Condition 3 has the equivalent finite formulation:
in every nonempty A⊆I\{p} some k∈A satisfies r_k(S)≤s_k for every
S⊆A containing k. With signed premiums, these inequalities are not
equalities.

**Theorem.** Every such game has a uniform-equilibrium payoff. There is
one vector z such that, for every ε>0, a behavioral profile and N₀ can
be chosen so that at every horizon N≥N₀ its expected average payoff is
within ε of z, and every unilateral behavioral deviation has expected
average payoff at most z_i+ε. The target z is fixed before ε; the
profile and N₀ may depend on ε.

The proof first gives a finite-player analytic theorem with strict (1),
then uses the actual four-player polynomial obstruction and reward
closure. The analytic theorem allows signed singleton rewards. The
four-player semantic conclusion above retains condition 1.

## 2. Actual exact roots and the protected return domain

For this section I is any finite nonempty player set. Assume conditions
2 and 3 and the strict version of (1), without requiring s_i≥0.
Fix M≥0 with |r_i(S)|≤M, and choose B>M. For a product root
q∈[0,1]^I put

    c(q)=∏_i(1−q_i),       a(q)=1−c(q).

For player i, let T be the independently drawn quitting coalition among
its opponents, and write c_{−i}=P(T=∅). Define the two pure-action
endpoints at continuation annotation v by

    Q_i(q)=E[r_i(T∪{i})],
    C_i(v,q)=∑[T≠∅] P(T)r_i(T)+c_{−i}v_i.

The actual successor is

    w_i=T_q(v)_i=q_i Q_i(q)+(1−q_i)C_i(v,q).

The root is exact Nash when every supported action maximizes these two
endpoints. Consequently w_i≥Q_i(q) always and w_i=Q_i(q) whenever
q_i>0. Finite normal-form Nash existence supplies an exact root at
every annotation v. It does not supply an absorbing root when
all-Continue is itself Nash.

Use the compact nonempty domain

    D={v∈[−B,B]^I : v_p≥s_p and some v_i≤s_i}.         (2)

**Protected return.** If v∈[−B,B]^I, v_p≥s_p, and q is an absorbing
exact root, then T_q(v)∈D.

Indeed, condition 2 gives Q_p(q)≥s_p, so exact Nash gives w_p≥s_p,
whether or not p is active. Let A={i:q_i>0}. Suppose A were a trap.
Then p∈A⊆C. On the empty opponent coalition, p's Quit-minus-Continue
difference is s_p−v_p≤0. On every nonempty opponent coalition T it
is r_p(T∪{p})−r_p(T)<0. Another player has positive hazard because
no singleton is a trap. Thus nonempty T has positive probability and
p strictly prefers Continue, contradicting p∈A.

So A is not a trap. Some active k has r_k(S)≤s_k for every
participant coalition S inside A. Conditional on k Quitting, all
realized coalitions are inside A, including those containing several
other active players. Hence Q_k(q)≤s_k and w_k=Q_k(q)≤s_k.
Together with w_p≥s_p and the box bound, this gives w∈D. The box
bound holds because each successor coordinate is an average of
rewards and its boxed source coordinate.

This argument retains every actual hazard and every larger coalition.
It does not first replace a full root by a root on a selected face.
The nontrap witness k can depend on the root and can itself be p.

## 3. Smooth full-root exclusion

**Analytic theorem.** Under the finite-player strict hypotheses of
Section 2, there is no C¹ function H on a neighborhood of [−B,B]^I
such that every boxed exact root satisfies

    H(T_q(v))≤H(v)−a(q).                              (3)

This statement tests all exact roots at all annotations in the box;
annotations need not be strategically realizable continuation payoffs.

### Singleton-face drift without premium-sign assumptions

Put U=∏_i[s_i,B] and

    L={x∈U : some x_i=s_i}.                           (4)

If x∈U and x_j=s_j, then (3) forces

    ∇H(x)·(x−r({j}))≥1.                              (5)

First suppose every other coordinate is strictly above its singleton.
Let only j quit, with a sufficiently small positive hazard t. Player j
is indifferent. For i≠j, Continue minus Quit equals

    (1−t)(x_i−s_i)+t[r_i({j})−r_i({i,j})],

which is positive for all sufficiently small t. Thus this is an exact
root, with successor x+t(r({j})−x) and absorption t. Apply (3),
divide by t, and let t decrease to zero. For several binding
coordinates, raise all bindings other than j slightly. The preceding
argument applies, and continuity of ∇H gives (5) at the original x.
Upper-face coordinates may remain fixed at B. No premium sign was used.

### First locate the minimum on L

Let x minimize H on D. If x_k<s_k for any k, all-Continue is not Nash
at x: player k can Quit for s_k. Therefore any exact root supplied by
finite Nash existence absorbs positively. Protected return puts its
successor back in D, contradicting (3) and minimality at x. Hence
x_i≥s_i for every i. Membership in D now implies x∈L.

Since L⊆D, x also minimizes H on L. Write g=∇H(x) and
J={i:x_i=s_i}. If J contained only j, every other interior partial
would vanish, and every upper-face partial would be nonpositive.
The j component of x−r({j}) is zero; every upper-face component is
B−r_i({j})>0. Thus g·(x−r({j}))≤0, contradicting (5).
Therefore |J|≥2. At any binding coordinate k, increasing that coordinate
while another binding remains fixed stays in L. Consequently g_k≥0.

### Perturb a different binding and retain the same domain

Choose k∈J with k≠p and put v_ε=x−εe_k. For small ε>0 this is
boxed and preserves p's floor. Since v_{ε,k}<s_k, every exact root
q_ε absorbs positively. Protected return gives w_ε=T_{q_ε}(v_ε)∈D.
It need not give w_ε∈L. Minimality on the original D nevertheless
gives H(w_ε)≥H(x).

Write a=a(q_ε). With probability 1−a_{−k}, forced Quit by k meets
no opponent and pays s_k. On the complementary event each reward
differs from s_k by at most 2M. Since a_{−k}≤a,

    Q_k(q_ε)≥s_k−2M a_{−k}≥s_k−2M a.

Exact Nash gives Q_k(q_ε)≤w_{ε,k}. One-step averaging also gives

    |w_{ε,k}−v_{ε,k}|≤(M+B)a.

Combining these inequalities with v_{ε,k}=s_k−ε yields

    ε≤(3M+B)a.                                       (6)

The stronger floor estimate w_{ε,k}≥s_k is neither assumed nor true
in general here. Since B>M≥0, the coefficient in (6) is positive.
Using (3) and minimality on D,

    [H(x−εe_k)−H(x)]/ε≥1/(3M+B)>0.

Its limit is −g_k≤0, a contradiction. This proves the analytic theorem.
No fixed-point index, generic-root assumption, or supplied selector is
part of this proof.

## 4. Four-player semantic consumer and weak comparison

The semantic input is the following actual-game polynomial obstruction:
if a four-player quitting table has nonnegative own singleton rewards,
at least one positive singleton, and no uniform-equilibrium payoff,
then for a reward bound M there is a rational polynomial H whose
restriction to exact roots satisfies (3) on the box B=M+2.

This input is the composition of
`isQuittingNormalPlayer_of_singleton_nonneg`
(`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`),
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
(`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`),
and `isQuittingFullExactRootPotential_of_robustPotential`
(`UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`).
It retains the same original table, polynomial, annotation box, full
exact roots, and absorption charge. None of these steps requires
nonnegative participant premiums. Normality here follows from the own
singleton signs; no equality between punishment values and singleton
rewards is needed.

For strict (1), if some singleton is positive, the polynomial is C¹
and contradicts Section 3. If all singletons vanish, all-Never is exact
Nash at every horizon: against it, any unilateral stopping law obtains
only that player's zero singleton or zero perpetual payoff. This proves
the strict four-player conclusion.

For weak (1), and δ>0, increase only the passive coordinate r_p(T)
by δ at each nonempty T⊆C\{p}. No participant reward or own
singleton changes. The full collection of premium traps and C remain
unchanged, and all leave comparisons become strict. These nearby
tables therefore have uniform-equilibrium payoffs.

Uniform-payoff existence is closed under uniform changes to the reward
table. To see the quantifiers directly, choose nearby tables rⁿ→r
and corresponding target payoffs zⁿ. They lie in one compact reward
box, so a subsequence converges to one fixed z. For any desired
accuracy, choose a sufficiently close table and target, then its
uniform profile at a sufficiently small accuracy. The same behavioral
profile is available in r. For every horizon and every deviating
profile, the expected average payoff changes by at most
max_{S,i}|rⁿ_i(S)−r_i(S)|, because the law of play is unchanged.
Combining this estimate with convergence of zⁿ gives the required
inequalities about z at all sufficiently large horizons. Thus z is
fixed before the desired accuracy.

The named source counterpart is
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
This is closure of the strategic conclusion, not a claim of C¹
exact-root exclusion under weak leave comparisons.

## 5. A signed root which returns to D but not to L

On three players set

    r({0})=(1,−2,0), r({1})=(0,0,0), r({2})=(3,0,0),
    r({0,1})=(1,−1,1), r({0,2})=(2,0,1),
    r({1,2})=(0,0,0), r({0,1,2})=(1,0,0).

Take p=0. The only premium trap is {0,2}. Player 0's participant
rewards are at least its singleton, and its strict leave comparison is
2<3. Player 1 has the genuinely negative participant premium −1 at
01. At v=(1,0,0), the full root q=(1,1,0) has Quit-minus-Continue
gaps (1,1,−1), so it is exact Nash. Its successor is (1,−1,1).
For any B>3, that successor lies in D but not in L. Thus replacing
the signed return by equality at a singleton boundary would be false
even under the strict hypotheses.

## 6. A full rational three-core fixture and bounded source separation

The following table has p=0 and genuinely signed unprotected premiums:

| S | r(S) |
|---|---|
| 0 | (1,−1,−1,−1) |
| 1 | (11/10,0,2,−1) |
| 2 | (0,−1,0,2) |
| 3 | (5/2,2,−1,0) |
| 01 | (1,1/2,−1,−1) |
| 02 | (1,−1,−1/10,−1) |
| 03 | (2,−1,−1,1) |
| 12 | (0,0,0,1) |
| 13 | (5/2,0,1,0) |
| 23 | (5/2,1,0,0) |
| 012 | (1,0,0,−1) |
| 013 | (1,0,−1,0) |
| 023 | (1,−1,0,0) |
| 123 | (5/2,0,0,0) |
| 0123 | (1,0,0,0) |

The positive participant premiums are precisely those of 0 and 3 at
03 and of 1 at 01. The traps are {0,3} and {0,1,3}, so C={0,1,3}
and all traps contain 0. Its three strict leave comparisons are
1<11/10, 2<5/2, and 1<5/2 at T=1,3,13 respectively. Player 2
has negative premium −1/10 at 02. A root with q_0=q_3=1/2 has
positive own premiums for both active players, so product-low fails.
The greatest premium core has size three, not at most two.

The following checks separate this fixture from specified existing
sufficient hypotheses; they do not classify all equilibrium methods.

### Singleton matrix, degree, and inverse tests

The centered singleton matrix Γ_{ij}=r_i({j})−s_i is

    Γ=[[0,1/10,−1,3/2],
       [−1,0,−1,2],
       [−1,2,0,−1],
       [−1,−1,2,0]].                                  (7)

Write A for the 123 principal block. It has determinant 7,
A·1=1, and

    A⁻¹=(1/7)[[2,4,1],[1,2,4],[4,1,2]].

For t>0 the complementarity problem Az≥t·1, z≥0,
z_i(Az−t·1)_i=0 has no zero coordinate. For example, if z_1=0,
the first inequality forces z_3>0; its active equation gives
z_2=t/2>0, whose active equation requires −z_3=t, impossible.
Cyclic rotation treats the other zeros. Thus z=t·1 uniquely.
At t=0 the same argument excludes every nonzero solution with a zero
coordinate; an all-positive solution would satisfy Az=0 and is also
impossible. Hence A is R₀.

In a homogeneous full complementarity problem, a positive pivot h
would force z=h·1, but its pivot residual is (3/5)h>0. With h=0
the child gives z=0. Thus Γ is R₀. At offset (1,−1,−1,−1), the
child equations give z=(1+h)·1 and the pivot residual is
1+(3/5)(1+h)>0. The unique root is (0,1,1,1), with inactive
residual 8/5 and active determinant 7. Its degree is therefore 1,
not an exit through the degree-not-one criterion.

The principal 02 matrix [[0,−1],[−1,0]] is R₀ but not Q. A nonzero
axis violates the opposite homogeneous inequality, and two positive
coordinates cannot have zero residuals. At offset (−1,−1), its first
inequality requires −x_2≥1, so no solution exists. In contrast,
principal 01 is not R₀: (0,1) has homogeneous residual (1/10,0).

The only nonnegative-inverse triple is 123. Its passive pivot weights
are

    (1/10,−1,3/2)A⁻¹=(26/35,−1/70,−9/70),

so the weak passive-inverse criterion fails. Explicit negative inverse
entries for the other triples are −20/21 at 012, −15/13 at 013,
and −1/2 at 023. The full inverse has entry −26/21 in row 0,
column 1. No pair has two positive off-diagonal singleton entries.

### Full response partitions

For a partition to preserve the literal response field, its linear
singleton block-row sums must agree within every target block. Here
are witnesses against thirteen of the fourteen nondiscrete partitions:

| Partition | Rows in one target block | Source block | Unequal sums |
|---|---|---|---|
| 01 / 2 / 3 | 0,1 | 01 | 1/10,−1 |
| 1 / 02 / 3 | 0,2 | 1 | 1/10,2 |
| 1 / 2 / 03 | 0,3 | 1 | 1/10,−1 |
| 0 / 12 / 3 | 1,2 | 12 | −1,2 |
| 012 / 3 | 0,1 | 012 | −9/10,−2 |
| 12 / 03 | 1,2 | 12 | −1,2 |
| 0 / 2 / 13 | 1,3 | 2 | −1,2 |
| 02 / 13 | 0,2 | 13 | 8/5,1 |
| 2 / 013 | 0,1 | 013 | 8/5,1 |
| 0 / 1 / 23 | 2,3 | 1 | 2,−1 |
| 01 / 23 | 0,1 | 01 | 1/10,−1 |
| 1 / 023 | 0,2 | 1 | 1/10,2 |
| 0123 | 0,1 | 0123 | 3/5,0 |

For the remaining 0 / 123 partition, take hazards (t,0,0,0).
The zero-discount response coordinate is
(1−c_{−i})Q_i−∑_{T≠∅}P(T)r_i(T). Its three child values are
t+t²/2, t−t²/10, and t+t². They are unequal for t>0. Thus the
full response field fails to preserve the last partition as well;
first-order compatibility alone is not treated as response invariance.

### Pure exits and every proper quiet child

No pure quitting coalition is equilibrium. For the coalitions in the
table's displayed order, respective strictly improving players are
1,3,0,2,0,1,0,2,1,3,3,0,0,1,0. Each gain is an immediate join,
or withdrawal from a nonsingleton coalition while its other members quit.

Every proper nonempty child has an exact terminal-Nash profile whose
quiet lift leaves an omitted player with a strictly profitable deviation:

- For singleton children 1,2,3, let the child quit surely. For 12,13,23
  use respectively sure 1,3,2.
- For 01 and 012 use sure 1; for 03 and 013 use sure 3.
- For child 0 use sure 0. For 02 let both members quit surely. Player 2
  receives −1/10, above its withdrawal payoff −1.
- For 123 repeat sole hazards 1/2 in the order 1,2,3. The successive
  child value vectors are (0,1,0), (0,0,1), and (1,0,0). Each active
  player is indifferent at value zero, every other forced-Quit endpoint
  is zero, and every phase value is nonnegative. Opponent survival
  contracts every period, so the Bellman comparisons control all
  behavioral deviations. The quiet pivot's initial value is
  (4·11/10+5/2)/7=69/70, but immediate Quit gives 1.
- For 023, use one date with hazards (q_0,q_2,q_3)=(2/3,1,2/5)
  and then Never if play survives. The Continue/Quit endpoint pairs
  for players 0,2,3 are (1,1), (−4/5,−1/25), and (0,0).
  The profile absorbs surely. Omitted player 1 has Continue value
  −11/15 and Quit value 0.

In the sure-owner cases a missing nonpivot with payoff −1 can join
for at least zero. The prescribed children have no profitable join or
withdrawal; after a deviator avoids a lone sure exit, later unilateral
Quit gives only its singleton. In the 023 case, survival after a
deviation by 2 leaves opponents at Never and gives maximal continuation
zero, already included in −4/5. Thus the endpoint checks cover complete
behavioral strategies, not just first-date deviations.

All fourteen child profiles have zero child regret and zero joint
Never probability. Consequently none can satisfy a universal outside
debt bound by nonnegative weights times child debts plus a nonnegative
multiple of joint Never. In particular, each corresponding five-kind
withdrawal/future-join certificate family fails for this same table.
This excludes those universal families, not every selected-child
construction.

## 7. Tracked correspondences and scope

The root existence and face calculations have existing counterparts
`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean` and
`IsQuittingFullExactRootPotential.singletonFace_drift` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`.
The latter requires no premium-sign hypothesis. The new mathematical
step is the raw trap-based return to D, its minimum localization to L,
and the signed charge (6).

The Lean handoff is the exact chain: the raw premium-trap predicate and
common-player criterion, then protected D return from the full endpoint
sums, then signed C¹ potential exclusion using (6), then Fin4 strict UE
through the existing polynomial consumer and weak UE through reward
closure. No additional strategic input is assumed in this chain.

`hasWeakQuittingPremiumSupportPeeling_iff` in
`UniformEquilibrium/Quitting/Classification/QuittingPremiumSupportPeelingOrder.lean`
requires a nonpositive-premium witness in every full support, whereas
condition 3 permits traps containing p. The declarations
`exactRootSuccessor_mem_singletonLowerBoundary_of_twoPlayerPremiumCore_strictLeave`
in `UniformEquilibrium/Quitting/Classification/TwoPlayerPremiumCoreExactRootBoundary.lean`
and `exists_uniformEquilibriumPayoff_of_twoPlayerPremiumCore_strictLeave`
in `UniformEquilibrium/Quitting/Classification/Existence/TwoPlayerPremiumCoreUniformPayoff.lean`
require nonnegative participant premiums and globally flat participants
outside a pair. Those hypotheses fail for the signed three-core fixture.

The degree, inverse, response, and quiet-child comparisons use the
following precise existing source criteria:

- `exists_finset_r0Degree_eq_sum_sign_det` in
  `MathUE/LinearProgramming/R0DegreeSum.lean`;
  `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
  `UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`.
- `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
  in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
- `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`;
  `quittingDiscountedDisplacement` in
  `UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`.
- `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.

The theorem is ordinary mathematical evidence with an explicit existing
semantic consumer; it does not assert a Lean implementation of the new
trap criterion. Its analytic part holds for finite player sets, but the
stated strategic conclusion uses the specifically four-player polynomial
producer. It does not solve every three-core or four-core table, nor
arbitrary signed-premium quitting games. The weak-comparison extension
is a uniform-payoff closure argument, not a weak analytic exclusion.
