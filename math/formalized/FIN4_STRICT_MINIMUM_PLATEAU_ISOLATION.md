# Strict minimum-plateau isolation in four-player quitting games

Author: `CODEX_CEDAR`

Independent reviews:

- [Proposition 1 review](../feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_RAMSEY__PROPOSITION_1.md)
- [Proposition 2 review](../feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_RAMSEY__PROPOSITION_2.md)
- [Proposition 3 review](../feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_RAMSEY__PROPOSITION_3.md)
- [Proposition 4 review](../feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_RAMSEY__PROPOSITION_4.md)

## Exact statement

Let the player type be literally `Fin 4`, and let

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
```

be a bounded quitting reward table.  Write

```text
s_i = reward({i})_i,
P_i = quittingPunishmentValue reward i.
```

For a terminal-semantic pair `x=(U,B)`, put

```text
d_i(x)=B_i-U_i,
D(x)=sum_i d_i(x).
```

Assume that the game has no uniform-equilibrium payoff.  Then there is a
terminal-semantic pair `x=(U,B)` such that:

1. `x` belongs to the terminal-semantic carrier;
2. `x` globally minimizes `D` over that carrier and `D(x)>0`;
3. the all-Continue product root is exact Nash against `U` and fixes `x`
   under terminal-semantic prefixing;
4. for every player `i`,

   ```text
   P_i <= s_i < U_i;                                  (1)
   ```

5. there is an open neighborhood `N` of `U` such that the all-Continue root
   is the unique exact product-root Nash equilibrium against every tail
   `V in N`.
6. writing `H(t)=B-t(B-U)` for `0<=t<=1`, there is one open neighborhood
   `T` of the compact segment `H([0,1])` such that all-Continue is the unique
   exact product-root Nash equilibrium against every tail `V in T`.

The conclusion is uniform over the whole minimum fiber, not only the selected
pair.  Let `D_*` be the global carrier minimum and

```text
M_*={X in terminal-semantic carrier : D(X)=D_*}.
```

There are `delta_*>0`, `epsilon_*>0`, and an open payoff set `T_*` containing
the prescribed-payoff projection of `M_*` such that:

7. every `X in M_*` satisfies

   ```text
   P_i<=s_i<X.1_i,             X.1_i-s_i>=delta_*
   ```

   for every player;
8. all-Continue is the unique exact root against every tail in `T_*`; and
9. if a terminal-semantic carrier pair `X` satisfies
   `D(X)<D_*+epsilon_*`, then `X.1 in T_*`.  Consequently the tail carrier
   pair of every positive-charge exact semantic-prefix edge satisfies

   ```text
   D(X)>=D_*+epsilon_*.
   ```

Item 9 is deliberately carrier-semantic.  It does not apply to an arbitrary
payoff-only Bellman tail with no supplied carrier pair.

Consequently, if an exact Nash--Bellman edge has continuation/tail node in
`T`, its root is all-Continue, its head equals its tail, and its absorption
charge is zero.  This is an orientation-sensitive conclusion: a charged edge
may have its head near the segment while its continuation/tail lies outside
`T`.

More quantitatively, let

```text
delta = min_i (U_i-s_i)>0
```

and choose `M>0` with `|reward(S)_i|<=M` for all `S,i`.  If

```text
|V_i-U_i| < delta/2                                  (2)
```

for every `i`, then every non-all-Continue exact root `q` against `V`
satisfies

```text
delta/(delta+4M) <= absorption(q).                   (3)
```

The neighborhood in item 5 may be chosen inside the box (2).

## Conjecture-facing change

The checked four-player residual in
`questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md` supplies all-player
punishment normality and a terminal exploitability witness, but it does not
previously consume the chronological minimum-spine alternative on the same
table.  This packet does so.

It eliminates two complete counterexample architectures:

- the fixed-owner solo semantic spine; and
- every singleton-tight positive minimum face.

It also proves that the surviving minimum plateau is not merely a strict
all-Continue point.  Its entire prescribed-to-envelope debt segment lies in
one open tube where the exact Bellman relation is the zero-charge identity.
The same strict isolation holds uniformly over every global-minimum carrier
pair.  Moreover, any charged exact semantic-prefix edge must originate at a
carrier debt at least `epsilon_*` above the global minimum.  Hence the
remaining four-player
obligation is necessarily nonlocal: an exact construction must use an
incoming continuation/tail outside this region, return after a nonlocal
excursion, or contradict the positive minimum before return.  A local
homotopy, diffuse exact-root approach, or local cap repair cannot be the
missing consumer.

## Definitions and semantic audit

A terminal-semantic pair is the prescribed terminal payoff and the
all-behavior best-response envelope of an executable behavioral profile, or a
limit of such pairs.  Thus `d_i` is the unrestricted unilateral terminal gain
available to player `i`; it is not stationary regret.

All root distributions in the proof are independent Boolean product roots.
The proof introduces no public correlation and no restricted deviation
class.  Unrestricted behavioral deviations enter through:

- the same-table `QuittingTerminalExploitabilityWitness`;
- the behavioral punishment value `P_i`;
- the terminal-semantic best-response envelope `B_i`; and
- the fixed-owner spine occupation theorems, including the atomic terminal
  endpoint restriction.

The open-basin proof itself is a finite one-stage statement about all exact
product-root Nash equilibria against a supplied tail.  Its Bellman conclusion
uses the checked exact successor identity.  It does not assert that an
arbitrary head near `U` has a local tail.

## Source correspondence

The adapter uses the following checked declarations on the original reward
table.

1. `uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual`
   and its `all_punishmentNormal` field, from
   `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
   It is instantiated with `quittingRewardBound reward` and
   `abs_reward_le_quittingRewardBound`.

2. `exists_positiveMinimumPlateau_or_fixedOwnerSoloSemanticSpine_of_no_uniformPayoff`,
   from
   `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumSpine.lean`.

3. `exists_pos_le_quittingSoloSemanticSurvival_of_not_tendsto_zero`,
   `exists_minimum_allContinueNash_of_soloSemanticSpine_survival_lower`,
   `isZeroSoloEndpointNash_of_soloRoot_continue_eq_zero`, and
   `QuittingTerminalExploitabilityWitness.atomic_restrictions_of_soloSemanticSpine_survival_zero`,
   from
   `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSoloSpineOccupation.lean`.

4. `minimumTerminalSemantic_debt_eq_sum_of_singleton_tight`, from
   `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumPlateauPacket.lean`.

5. `quittingSoloRateControlled_of_q_le_debt_div_debt_add_gainMax`,
   `quittingControlledSolo_outsiderEndpoint_le_solo`, and
   `singletonTight_soloReward_lt_punishmentValue_and_nonpos`, from
   `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonTightMinimumFaceIteration.lean`.

6. `minimumTerminalSemantic_exactNash_allContinue_or_debtGateSolo`,
   `minimumTerminalSemantic_exactNash_eq_allContinue_of_no_debtGate`, and
   `minimumTerminalSemantic_debtHomotopy_eq_allContinue`, from
   `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumDebtSimplex.lean`.

7. `quittingRootEndpointDifference_eq_outsiderNever` and the bounded joining
   contribution in
   `UniformEquilibrium/Quitting/Paths/OutsiderNeverGluing.lean` and
   `UniformEquilibrium/Quitting/Boundary/Repair/FixedTailUniformAbsorption.lean`.

The new content is the same-table composition eliminating the solo-spine and
singleton-tight branches simultaneously for `Fin 4`, followed by the reverse
singleton-gap estimate (3) and the compact open isolation of the entire debt
segment.
No literature theorem is being strengthened or attributed here.

## Proof

### 1. Same-table punishment normality

Choose the checked finite coordinate bound `quittingRewardBound reward`.
Because a uniform payoff is assumed absent, the no-uniform arm of the checked
four-player hard-residual theorem supplies a terminal exploitability witness
and

```text
IsQuittingNormalPlayer reward i
```

for every `i`.  By definition,

```text
P_i <= s_i.                                           (4)
```

All fields refer to the original reward table.

### 2. Eliminate the fixed-owner spine

Apply the checked minimum-spine dichotomy.  Its first arm is already a
positive-debt minimum all-Continue plateau.  Suppose its second arm holds.
There is one owner `o`; every outsider always Continues, every owner row has
positive Quit mass, the owner debt is one fixed positive number, and the next
prescribed owner coordinate is always `s_o`.

Let `S_n` be the owner's survival product.  It is decreasing.

If `S_n` does not tend to zero, the checked survival lemma gives a positive
uniform lower bound.  The checked occupation/compactness theorem then
produces a minimum carrier point at which all-Continue is exact Nash.  This
contradicts the spine arm's explicit negation of every such point.

Suppose `S_n -> 0`.  If the first owner row has positive Continue mass, the
checked atomic restriction gives

```text
s_o < P_o,
```

contrary to (4).  If its Continue mass is zero, PMF mass makes it a sure-Quit
row.  Rewrite the row using the supplied spine equality

```text
root 0 = quittingSoloStationaryRoot o (root 0 o).
```

The sure-Quit endpoint lemma removes the irrelevant tail, and the witness's
solo-endpoint restriction again gives `s_o<P_o`.  Thus the spine arm is
impossible.

The plateau arm therefore holds.  Carrier debt nonnegativity and its supplied
positive coordinate imply `D(x)>0`.

### 3. Eliminate singleton equality

Exact all-Continue Nash against `U` gives `s_i<=U_i` for every `i`.  Suppose
`U_i=s_i` for some `i`.  The checked minimum singleton-margin identity gives

```text
d_i(x)=D(x).
```

Since every carrier debt is nonnegative and the debts sum to `D(x)`, all
other debts are zero.  Hence `x,i` form a singleton-tight minimum face.

Put `G=quittingSingletonCollisionGainMax reward i`.  Then `G>=0`, and

```text
q = D(x)/(2(D(x)+G))
```

is positive, at most one, and at most `D(x)/(D(x)+G)`.  The checked controlled
solo construction and its outsider endpoint theorem apply.  The checked
punishment theorem then gives

```text
s_i < P_i <= 0,
```

contradicting (4).  The chosen `i` was arbitrary, so `s_i<U_i` holds for all
four players.  Combining this with (4) proves (1).

### 4. Uniqueness at the plateau

The checked critical-face classification says that an exact root against `U`
is all-Continue or is solo at a minimum debt gate.  At a debt gate `i`,

```text
d_i(x)=D(x),
B_i-s_i=D(x).
```

As `B_i=U_i+d_i(x)`, these equations imply `U_i=s_i`, contradicting (1).
Thus all-Continue is the unique exact root at `U`.

### 5. Quantitative isolation

Let `V` satisfy (2), and let `q` be a non-all-Continue exact root against
`V`.  Some player `i` has positive Quit probability.  Exact Quit support says
that the endpoint difference `Quit-Continue` is nonnegative.

Let `O_i` be the probability that at least one opponent of `i` Quits.  The
exact outsider decomposition is

```text
endpointDifference_i
  = (1-O_i)(s_i-V_i) + joiningContribution_i,
```

and bounded rewards give

```text
joiningContribution_i <= 2M O_i.
```

Since `V_i-s_i>delta/2`,

```text
0 <= -(1-O_i)delta/2 + 2M O_i.
```

Rearranging yields

```text
O_i >= delta/(delta+4M).
```

Joint absorption dominates opponent absorption, proving (3).

Assume no open unique-root neighborhood exists.  Then one can choose
`V_n->U` and non-all-Continue exact roots `q_n`.  Eventually (2) holds, so
(3) gives a fixed positive absorption floor.  The product-root simplex is
compact; pass to a convergent subsequence.  Endpoint differences and root
probabilities are continuous, so the limit is exact Nash against `U`.
Absorption is continuous and remains positive.  This contradicts the
uniqueness proved in Step 4.

After shrinking the resulting neighborhood inside (2), every tail in it
strictly dominates the singleton vector, so all-Continue is exact there.  It
is therefore the unique exact root throughout that neighborhood.  Its
successor is the tail itself and its charge is zero, proving the Bellman-edge
conclusion.

### 6. Freeze the whole debt segment

Put `d=B-U` and

```text
H(t)=B-t d=U+(1-t)d,     0<=t<=1.
```

For `0<=t<1`, the checked theorem
`minimumTerminalSemantic_debtHomotopy_eq_allContinue` says directly that
every exact root against `H(t)` is all-Continue.  At `t=1`, `H(1)=U`, so Step
4 gives the same conclusion.  Carrier debt nonnegativity gives

```text
H(t)_i >= U_i > s_i
```

with the uniform gap at least `delta` for every player and every `t`.

If there were no open unique-root tube around the segment, choose tails
`V_n` whose distance to the segment tends to zero and non-all-Continue exact
roots `q_n` against them.  Choose `t_n` with `V_n-H(t_n)->0`; compactness of
`[0,1]` gives a subsequence `t_n->t`.  Then `V_n->H(t)`, and eventually every
coordinate exceeds its singleton payoff by `delta/2`.  Step 5 gives the
fixed absorption floor (3).  Root compactness and closedness of exact Nash
produce a positive-absorption exact root against `H(t)`, contradicting its
pointwise uniqueness.

Finally intersect the resulting tube with the open coordinate set
`V_i>s_i` for every player.  The segment remains inside, and all-Continue is
itself exact throughout the final tube.  This proves item 6 and the stated
Bellman-edge conclusion.

### 7. Uniformize over the whole minimum fiber

Fix arbitrary `X in M_*`.  The checked minimum singleton-margin theorem gives
`X.1_i>=s_i` for every player.  If equality held at `i`, the exact
complementary-debt identity and nonnegative slack would give

```text
d_i(X)=D_*,             d_j(X)=0 for j!=i.
```

Thus `X,i` would form a singleton-tight minimum face.  The controlled rate

```text
q=D_*/(2(D_*+quittingSingletonCollisionGainMax reward i))
```

and the same outsider-clearance/punishment theorem used in Step 3 would give
`s_i<P_i`, contrary to same-table punishment normality.  Hence every minimum
pair is strictly singleton-separated.

The carrier is compact and `M_*` is its nonempty closed minimum subset.
Finite-player compactness turns the pointwise strict gaps into one positive
minimum `delta_*`.  The minimum critical-face classification then makes
all-Continue the unique exact root at every prescribed payoff in the compact
projection of `M_*`: every alternative root would require a debt gate, and a
debt gate is exactly the excluded singleton equality.

Apply the reverse outsider estimate uniformly with `delta_*`.  If nontrivial
exact roots approached the compact projection, their absorption would stay
at least `delta_*/(delta_*+4M)`; compactness and closedness would produce a
nontrivial exact root at a member of `M_*`, contradiction.  Intersect the
resulting neighborhood with `V_i>s_i` to obtain `T_*`.

Finally

```text
C={X in carrier : X.1 notin T_*}
```

is compact and disjoint from `M_*`.  If nonempty, continuity gives
`min_(X in C)D(X)>D_*`; take half that gap as `epsilon_*`.  If empty, take
any positive `epsilon_*`.  This proves items 7--9.  The last implication uses
the supplied carrier pair at the tail: an exact semantic prefix of such a
pair with positive charge is not all-Continue and therefore its prescribed
tail lies outside `T_*`.

## Boundary tests

1. **Normality is essential.**  The checked singleton-tight theorem concludes
   `s_i<P_i<=0`; without same-table punishment normality this is a surviving
   atomic refusal branch, not a contradiction.

2. **Strict singleton separation alone does not imply uniqueness.**  In a
   two-player one-stage table take both singleton payoffs, including outsider
   coordinates, equal to zero; take the joint-quitting payoffs equal to one;
   and use tail `(1/4,1/4)`.  Besides all-Continue, the symmetric root with
   Quit probability `1/5` for each player is exact:

   ```text
   Quit payoff = 1/5,
   Continue payoff = (4/5)(1/4)=1/5.
   ```

   Thus Step 4 genuinely uses the positive-minimum critical-face theorem.

3. **The estimate has the correct orientation.**  It uses positive Quit
   support and `Quit-Continue>=0` when the tail lies *above* the singleton
   payoff.  The familiar fixed-tail absorption lemma for tails below the
   singleton uses positive Continue support instead; reversing these signs
   would be false.

4. **Incoming-tail boundary.**  The theorem does not exclude a charged edge
   with head in `T` and tail outside `T`.  That nonlocal incoming edge is
   precisely part of the remaining conjecture-facing obligation.

## Adapter and consumer

The actual-data adapter is the checked no-uniform arm
`uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual`, on the
same `Fin 4` reward table, composed with the checked minimum-spine dichotomy.
No supplied packet, selected certificate, or modified reward table is assumed.

The packet is a strict residual reduction, not a terminal-equilibrium
consumer.  Its output refines the maintained four-player singleton-packet
question: any no-uniform table must have the displayed source-native plateau,
every global-minimum carrier pair lies in one uniformly frozen region, and
any exact semantic paid consumer must first retain the fixed carrier-debt
excess `epsilon_*` before it can carry positive charge.  A payoff-only edge
still requires separate carrier provenance.  The
downstream semantic endpoint remains
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`;
this packet does not yet reach it.

## Lean handoff

The narrowest formalization is two declarations on literal `Fin 4`.

1. A composition theorem returning a minimum carrier pair with
   `P_i<=s_i<U_i` for all `i`.  Reuse the declarations listed in Source
   correspondence; do not introduce a new structure whose field assumes the
   conclusion.  Instantiate the hard residual with the checked reward bound.

2. A whole-minimum-fiber isolation theorem.  First use
   `minimumTerminalSemantic_exactNash_eq_allContinue_of_no_debtGate`.  Prove
   the reverse singleton-gap absorption bound from
   `quittingRootEndpointDifference_eq_outsiderNever` and the existing joining
   contribution bound.  Apply
   `minimumTerminalSemantic_debtHomotopy_eq_allContinue` on `0<=t<1`, and use
   compactness of the segment, `QuittingRootSimplex (Fin 4)`, and
   closedness/continuity of exact endpoint Nash to obtain one open tube.
   Compactify the set of all minimum carrier pairs, repeat the singleton-tight
   contradiction uniformly, and minimize total debt on the carrier complement
   of the resulting open payoff tube to obtain `epsilon_*`.

Useful exact regressions are the sure-Quit first-row subcase and the rational
two-player root in Boundary test 2.  The external formalizer should preserve
the edge orientation: the unique-root hypothesis is imposed at the tail.

## Scope and nonclaims

- This packet does not prove the four-player conjecture or produce a terminal
  approximate Nash profile.
- It is stated for literal `Fin 4`; no arbitrary four-element reindexing
  theorem is claimed.
- It produces no charged edge, return path, or chronological repayment.
- Its `epsilon_*` conclusion applies to exact semantic-prefix edges with a
  carrier pair at the tail, not arbitrary payoff-only Bellman edges.
- It does not identify the plateau with the stationary large-base paid source
  or with a selected LCP principal.
- It does not exclude a nonlocal incoming tail whose Bellman head is near the
  debt segment.
- The root isolation concerns exact product-root Nash equilibria.  It makes no
  claim that arbitrary approximate roots are literally all-Continue.
