# CODEX_CEDAR — four-player conjecture capstone

Author: `CODEX_CEDAR`

## Current status

**Proof in progress.**  Propositions 1--6, 8--9 and Corollary 4A below are
independently reviewed.  The reviewed argument first reduces the `Fin 4`
counterexample residual to a positive-debt minimum terminal-semantic
all-Continue plateau whose prescribed payoff is strictly above every own
singleton payoff and every punishment value.  This plateau lies in an open
exact-Nash basin on which all-Continue is the only root, so any successful
Bellman construction must make a genuinely nonlocal payoff excursion.

The later source-native wall dispatch is now also complete.  After the
off-minimum charged blocker gate, finitely many literal exact semantic
prefixes produce either

1. a strict floor-safe carrier debt descent with positive charge, or
2. an actual stationary source with two solved unrestricted coordinates,
   debt on at most two coordinates, a fixed nonsingleton atom, and a literal
   source-matched paid first-disagreement row.

This two-output theorem is exported and independently gated in
`exports/FIN4_SOLO_WALL_DEBT_DESCENT_OR_TWO_DEBTOR_HANDOFF.md`.  It removes
the all-Continue/changed-solo root-selection wall; it does not synchronize
the descent into a returned exact path or Nashify the reselected stationary
source.

This does **not** yet prove the conjecture.  The exact remaining task is to
consume one of the two outputs above: either iterate/synchronize the literal
carrier descent without losing its gate provenance, or turn the actual
stationary two-debtor paid source into a floor-admissible exact Bellman path
with a fixed charged return.  The abstract finite-cell/restart argument does
not supply this producer; its audit is in
`notes/CODEX_CEDAR__PAID_REACHABLE_CELL_RANK_AUDIT.md`.  No Lean theorem is
claimed here.

## 1. Exact target

Let the player type be literally `Fin 4` and

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
```

a finite quitting reward table.  The target is a fixed payoff satisfying the
uniform finite-horizon equilibrium contract against every unilateral
behavioral strategy.  Equivalently, it is enough to construct unrestricted
terminal `epsilon`-Nash profiles for every positive `epsilon`; a counterexample
would instead supply a fixed positive terminal exploitability gap.

Write

```text
s_i = reward({i})_i,
P_i = quittingPunishmentValue reward i.
```

For a terminal-semantic pair `x=(U,B)`, write

```text
d_i(x)=B_i-U_i,
D(x)=sum_i d_i(x).
```

## 2. Sources inspected

The bounded source set for Proposition 1 is:

- `uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual` and
  the field `all_punishmentNormal` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
- `exists_positiveMinimumPlateau_or_fixedOwnerSoloSemanticSpine_of_no_uniformPayoff`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumSpine.lean`;
- `exists_minimum_allContinueNash_of_soloSemanticSpine_survival_lower`,
  `isZeroSoloEndpointNash_of_soloRoot_continue_eq_zero`, and
  `QuittingTerminalExploitabilityWitness.atomic_restrictions_of_soloSemanticSpine_survival_zero`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSoloSpineOccupation.lean`;
- `minimumTerminalSemantic_debt_eq_sum_of_singleton_tight` and
  `minimumTerminalSemantic_not_two_singleton_tight` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumPlateauPacket.lean`;
- `minimumTerminalSemantic_exactNash_allContinue_or_debtGateSolo` and
  `minimumTerminalSemantic_exactNash_eq_allContinue_of_no_debtGate`, and
  `minimumTerminalSemantic_debtHomotopy_eq_allContinue` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumDebtSimplex.lean`;
- `quittingSoloRateControlled_of_q_le_debt_div_debt_add_gainMax`,
  `quittingControlledSolo_outsiderEndpoint_le_solo`, and
  `singletonTight_soloReward_lt_punishmentValue_and_nonpos` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonTightMinimumFaceIteration.lean`; and
- the exact terminal/uniform endpoints named in `SOURCES.md` and `GOAL.md`.

For Proposition 5 I additionally inspected
`sum_opponentAbsorptionMass_mul_debt_le_sumDebt_drift_add_totalNashDefect`
and `quittingRootCoalitionMass_mul_debt_le_drift_add_nashDefect` in
`TerminalSemanticPlateauDefectCharge.lean`, the collision-mass identities in
`Quitting/AbsorptionPath/CollisionConcentration.lean`, the exact floor-root
marginal cap in `Collision/Toggles/TerminalGapExactRootMarginalCap.lean`, and
the punishment-completed solo compiler and cap formulas in
`Quitting/Punishment/SoloCycleCompletion.lean` and
`Quitting/Boundary/Exceptional/TailFallback.lean`.

The result below is an adapter between these checked facts.  It does not
assert that the remaining plateau is already consumed by any checked theorem.

## 3. The normal strict-plateau reduction

> **Proposition 1 (four-player nonexistence forces a wholly separated normal
> plateau).**  Assume the four-player quitting game has no uniform-equilibrium
> payoff.  Then there is a terminal-semantic pair `x=(U,B)` such that:
>
> 1. `x` belongs to the terminal-semantic carrier;
> 2. `x` minimizes `D` over that carrier and `D(x)>0`;
> 3. the all-Continue product root is exact Nash at tail `U` and semantically
>    fixes `x`;
> 4. every player is punishment-normal, `P_i<=s_i`; and
> 5. for every player,
>
>    ```text
>    P_i <= s_i < U_i.                                (3.1)
>    ```
>
> Thus the only surviving minimum-spine architecture is a floor-interior,
> strictly singleton-separated, positive-debt all-Continue plateau.  Neither
> a fixed-owner solo spine nor a singleton-tight minimum face survives.

### Proof

Choose the checked finite coordinate bound `quittingRewardBound reward`, using
`abs_reward_le_quittingRewardBound`.  The checked four-player hard-residual
theorem applied to the assumed absence of a uniform payoff then supplies, on
the same reward table, a terminal exploitability witness and

```text
IsQuittingNormalPlayer reward i
```

for every player.  By definition this is

```text
P_i<=s_i.                                             (3.2)
```

Apply the checked chronological counterexample dichotomy
`exists_positiveMinimumPlateau_or_fixedOwnerSoloSemanticSpine_of_no_uniformPayoff`.
Its first arm is already items 1--3 of the proposition.  We show that its
second arm is impossible.

In that second arm one fixed owner `o` is the only active player at every
date.  Its Quit probability is positive, all outsiders Continue purely, its
debt is one fixed positive constant, and its prescribed tail coordinate is
singleton-tight:

```text
U_(t+1,o)=s_o.                                        (3.3)
```

Let `S_n` be the owner's finite survival product through the first `n` rows.
There are two cases.

If `S_n` does not tend to zero, monotonicity gives a positive uniform lower
bound.  The checked theorem
`exists_minimum_allContinueNash_of_soloSemanticSpine_survival_lower` then
produces a minimum carrier pair at which all Continue is exact Nash.  But the
second arm of the chronological dichotomy explicitly includes the negation of
every such minimum plateau.  Contradiction.

Suppose therefore that `S_n` tends to zero.  If the first owner row has
positive Continue probability, the checked atomic restriction gives

```text
s_o<P_o.                                              (3.4)
```

If that Continue probability is zero, PMF mass makes the first owner row a
sure-solo Quit root.  Rewrite it using the spine identity

```text
root 0 = quittingSoloStationaryRoot o (root 0 o).
```

Then `isZeroSoloEndpointNash_of_soloRoot_continue_eq_zero` removes the
irrelevant tail, and the terminal-witness solo-endpoint restriction again
gives (3.4).
In both subcases (3.4) contradicts the same-table normality (3.2).  Hence the
fixed-owner branch is impossible, and a minimum all-Continue plateau `x`
exists.  Its supplied positive debt coordinate and carrier debt
nonnegativity imply `D(x)>0`.

It remains to prove strictness in (3.1).  Exact all-Continue Nash at `U`
gives

```text
s_i<=U_i                                               (3.5)
```

for every player.  Suppose equality holds for some owner `i`.  At a positive
minimum pair, the checked singleton-margin identity says that this coordinate
carries the whole debt:

```text
d_i(x)=D(x),
d_j(x)=0 for j!=i.                                    (3.6)
```

Carrier debt nonnegativity and `D=sum_j d_j` also imply `d_j=0` for every
`j!=i`, so `x,i` satisfy `QuittingSingletonTightMinimumFace`.  Since `D(x)>0`
and the collision gain maximum `G` is finite and nonnegative, choose the
explicit positive rate

```text
q = D(x)/(2*(D(x)+G)).
```

It satisfies `q<=1` and `q<=D(x)/(D(x)+G)`.  The checked controlled-rate lemma
therefore applies, and `quittingControlledSolo_outsiderEndpoint_le_solo`
supplies every outsider endpoint inequality.  The checked washout and
punishment theorem then yields

```text
s_i<P_i<=0,                                           (3.7)
```

again contradicting (3.2).  Equality in (3.5) is therefore impossible for
every player.  Combining strict (3.5) with (3.2) proves (3.1).  `QED`

## 4. The exact root is locally frozen

Fix the plateau from Proposition 1 and put

```text
delta = min_i (U_i-s_i)>0.                            (4.1)
```

> **Proposition 2 (open all-Continue basin).**  There is an open neighborhood
> `N` of `U` such that for every tail `V in N`, the all-Continue product root
> is the unique exact quitting-root Nash equilibrium against `V`.
> Consequently every exact Nash--Bellman edge whose tail lies in `N` is the
> zero-charge identity edge.  In particular a charged edge cannot depart from
> a continuation/tail node in `N`.  This does not exclude a charged edge whose
> head lies near `U` but whose continuation/tail lies nonlocally outside `N`.

### Proof

First consider exact roots at `U`.  The checked minimum-debt critical-face
theorem says that such a root is either all-Continue or is a solo root at a
debt gate.  A debt gate at player `i` has

```text
d_i(x)=D(x),
B_i-s_i=D(x).
```

Since `B_i=U_i+d_i(x)`, these two equalities imply `U_i=s_i`, contradicting
(3.1).  Thus all-Continue is the unique exact root at `U`.

We record the quantitative compactness argument because it rules out more
than one selected vanishing sequence.  Choose a positive reward bound `M`.
Shrink to the open box

```text
|V_i-U_i| < delta/2  for every i.                     (4.2)
```

Then `V_i-s_i>delta/2` for every player.  Let `q` be any exact root against
such a `V`, distinct from all-Continue, and choose `i` with positive Quit
probability.  Put `O_i` for the probability that some opponent of `i` Quits
at the row.  Exact Quit support gives a nonnegative endpoint difference.  The
outsider decomposition and the reward bound give

```text
0 <= endpointDifference_i
   = (1-O_i)(s_i-V_i) + joiningContribution_i,
|joiningContribution_i| <= 2 M O_i.
```

Therefore

```text
delta/(delta+4M) <= O_i <= absorption(q).             (4.3)
```

If the claimed neighborhood did not exist, there would be tails `V_n -> U`
and non-all-Continue exact roots `q_n`.  After eventually imposing (4.2),
(4.3) makes their absorption masses uniformly positive.  Compactness of the
product-root simplex selects a limit root `q`; continuity of the endpoint
inequalities makes `q` exact at `U`, while continuity of absorption keeps its
absorption positive.  This contradicts uniqueness at `U`.  Hence some
neighborhood `N` has only the all-Continue exact root.  The singleton
inequalities remain strict after shrinking `N`, so all-Continue is indeed
exact throughout `N`.

Finally its successor payoff is literally its tail and its absorption charge
is zero.  Hence every exact Bellman edge with tail in `N` is the identity
edge.  `QED`

### The whole debt segment is frozen

The local conclusion is not confined to `U`.  Let

```text
H(t)=B-t(B-U)=U+(1-t)d,       0<=t<=1.                (4.4)
```

> **Proposition 3 (open frozen tube around the debt segment).**  There is an
> open neighborhood `T` of the compact segment
> `H([0,1])` such that all-Continue is the unique exact root against every
> tail in `T`.  Therefore every charged exact Bellman edge has its
> continuation/tail outside this whole tube.

For `0<=t<1`, the checked theorem
`minimumTerminalSemantic_debtHomotopy_eq_allContinue` says directly that
every exact root against `H(t)` is all-Continue.  At `t=1`, Proposition 2
gives the same conclusion.  All-Continue is exact throughout because

```text
H(t)_i >= U_i > s_i.                                  (4.5)
```

Moreover (4.5) has the same uniform gap `delta` for the entire segment.  If
no open unique-root tube existed, choose `V_n` converging in distance to the
segment and a non-all-Continue exact root `q_n` against each `V_n`.  Choose
`t_n` with `V_n-H(t_n)->0`; compactness gives a subsequence `t_n->t`.  Then
`V_n->H(t)`.  Eventually every coordinate of `V_n` exceeds its singleton by
`delta/2`, so the calculation (4.3) gives the same fixed absorption floor.
Compactness of roots produces a positive-absorption exact root against
`H(t)`, contradicting the just-proved pointwise uniqueness.  Finally,
intersect the tube with the open set on which every tail coordinate strictly
exceeds its singleton payoff.  This retains the whole segment by (4.5) and
ensures that all-Continue is itself exact throughout the final tube.  `QED`

### The whole minimum fiber has a debt moat

The preceding argument does not depend on the selected plateau once
same-table punishment normality is available.

> **Proposition 4 (uniformly frozen minimum fiber and positive debt moat).**
> Let `D_*` be the global minimum of total debt on the
> terminal-semantic carrier, and let
>
> ```text
> M_*={X in carrier : D(X)=D_*}.
> ```
>
> In the no-uniform branch, `D_*>0` and there are constants
> `delta_*>0`, `epsilon_*>0` and an open payoff set `T_*` containing the
> prescribed-payoff projection of `M_*` such that:
>
> 1. every `X in M_*` satisfies
>
>    ```text
>    P_i<=s_i<X.1_i,                  X.1_i-s_i>=delta_*
>    ```
>
>    for all four players;
> 2. all-Continue is the unique exact root against every tail in `T_*`;
> 3. if `X` is any carrier point with `D(X)<D_*+epsilon_*`, then
>    `X.1 in T_*`, so every exact semantic prefix from `X` is the zero-charge
>    identity; and
> 4. contrapositively, the tail semantic pair of every positive-charge exact
>    semantic-prefix edge has total debt at least `D_*+epsilon_*`.
>
> Item 4 requires an actual carrier semantic pair at the tail.  It is not a
> statement about an arbitrary payoff-only Bellman tail.

**Proof.**  Proposition 1 supplies `D_*>0` and the hard residual supplies
`P_i<=s_i` on the same reward table.  Fix arbitrary `X in M_*`.  The checked
minimum singleton-margin theorem gives `X.1_i>=s_i` for every player.
Suppose equality holds for `i`.  The complementary-debt identity and
nonnegative minimum slack imply

```text
d_i(X)=D_*,             d_j(X)=0 for j!=i.
```

Thus `X,i` form a `QuittingSingletonTightMinimumFace`.  With
`G=quittingSingletonCollisionGainMax reward i`, the same controlled rate as
in Proposition 1,

```text
q=D_*/(2(D_*+G)),
```

is positive, at most one, and satisfies the required collision inequalities.
`quittingControlledSolo_outsiderEndpoint_le_solo` and
`singletonTight_soloReward_lt_punishmentValue_and_nonpos` then give
`s_i<P_i`, contradicting punishment normality.  Hence `X.1_i>s_i` for every
`X in M_*` and every player.

The carrier is compact, `D` is continuous, and `M_*` is its nonempty closed
minimum subset.  Finite-player compactness therefore upgrades the pointwise
strict inequalities to one constant

```text
delta_*=min_(X in M_*,i)(X.1_i-s_i)>0.                (4.6)
```

At any `X in M_*`, the checked exact-root critical-face theorem says that a
non-all-Continue root must be solo through a debt gate.  A debt gate is
equivalent to singleton equality, which was just excluded.  Thus
all-Continue is the unique exact root at every prescribed payoff in the
compact projection of `M_*`.

The reverse outsider estimate of Proposition 2 is uniform: for any tail
within `delta_*/2` coordinatewise of that compact projection, every
non-all-Continue exact root would have absorption at least

```text
delta_*/(delta_*+4M).
```

If nontrivial exact roots approached the projection, compactness of `M_*`
and of the root simplex plus closedness of exact Nash would produce a
positive-absorption exact root at one member of `M_*`, contradiction.
Intersect the resulting neighborhood with `V_i>s_i` for all `i`; call the
final open set `T_*`.  All-Continue exists and is unique throughout it.

Finally the closed carrier subset

```text
C={X in carrier : X.1 notin T_*}
```

is compact and disjoint from `M_*`.  If `C` is empty, take any
`epsilon_*>0`.  Otherwise continuity and compactness give
`min_(X in C)D(X)>D_*`; take half of this strict gap as `epsilon_*`.  Then
`D(X)<D_*+epsilon_*` forces `X.1 in T_*`.  A positive-charge exact root
cannot be all-Continue, proving the contrapositive edge statement.  `QED`

> **Corollary 4A (near-minimum exact atom-access stacks are only delays).**
> Let `frontier` be any checked positive-minimum stopping-law tangent family
> on the same no-uniform `Fin 4` table.  For each rank let `roots_r` be an
> arbitrary finite literal exact-root stack ending at `frontier.source r`;
> its length may grow without bound.  For all sufficiently large ranks,
> every root occurring in `roots_r` is all-Continue.  Consequently the stack
> has zero literal absorption charge and makes no semantic payoff movement.
>
> In particular, `QuittingStoppingLawAtomExactPrefixStackAccess` cannot turn
> its fixed terminal atom into an exact paid edge near the minimum source.
> It can only place an arbitrarily long pure-delay word before the atom
> suffix.  Any exact charged realization must first move to a carrier pair
> with debt at least `D_*+epsilon_*`.

Indeed `Sem(frontier.source r)->frontier.base`, so its total debt tends to
`D_*`.  Eventually it is below `D_*+epsilon_*`.  Consider any suffix of the
finite exact stack.  Its semantic pair is in the carrier, and exact-root debt
monotonicity puts its total debt between `D_*` and the terminal source debt.
Proposition 4 therefore puts its prescribed payoff in `T_*`.  The root
immediately before that suffix is exact Nash at this payoff and hence must be
all-Continue.  Apply this argument to every list position; the estimate is
uniform in the list length.  All root absorption masses are zero, and
all-Continue prefixing preserves the terminal-semantic pair.  `QED`

## 5. Exact remaining residual

Propositions 1--4 imply:

1. `U` is strictly floor-admissible: `U_i-P_i>=delta` for every player.
2. The exact predecessor relation is the zero-charge identity on an open tube
   around the entire prescribed-to-envelope debt segment `[U,B]`.
3. Any exact charged return must use a continuation/tail outside that tube;
   neither a local cap homotopy nor a diffuse local root sequence can supply
   the missing edge.
4. More globally, every positive-charge exact semantic edge starts at a
   carrier point whose debt exceeds the minimum by the fixed amount
   `epsilon_*`.  Exactifying an off-minimum paid row therefore necessarily
   retains a nonperturbative semantic-debt excursion.

The genuine residual is therefore:

> Use the executable carrier sequence converging to `(U,B)` and its positive
> debt to produce a **nonlocal** exact floor block which exits `N` and returns
> near `U`, or derive a contradiction to minimum debt before return.

This is exactly where nonsingleton terminal outcomes enter.  For a positive
debtor, the checked plateau passport gives either a negative Never component
or fixed opponent-containing chronological charge on one source-matched
pure-time replacement.  Turning that literal charge into simultaneous exact
Nash--Bellman rows is the next proof step; the present proposition does not
silently make that conversion.

## 6. Boundary checks

- The normality hypothesis is essential.  A singleton-tight positive-debt
  minimum has `s_i<P_i<=0`, and is precisely the atomic refusal branch rather
  than a contradiction in an arbitrary game.
- Positive survival on the solo spine does not itself give a terminal
  equilibrium; it gives a minimum all-Continue cluster point.  Vanishing
  survival likewise does not give an equilibrium when `s_o<0`, because the
  owner can choose Never.  The proof uses punishment normality to exclude that
  seam.
- Strict singleton separation alone does not imply root uniqueness.  Here
  uniqueness uses positive minimum debt: the checked critical-face theorem
  reduces every nontrivial root at `U` to a singleton debt gate, and (3.1)
  removes exactly that gate.
- Proposition 2 is an obstruction, not a return producer.  It eliminates the
  local/diffuse connector architecture but does not control an exact path
  after it exits `N`.

## 7. Requested falsification

Please check Proposition 1 independently, especially the sure-Quit first-row
subcase in the fixed-owner branch, the use of all-player normality on the same
reward table, and the construction of the controlled positive solo rate in
the singleton-tight plateau subcase.  For Proposition 2, check the debt-gate
algebra, the sign in the outsider endpoint decomposition, the constant
`delta/(delta+4M)`, and the passage from sequential compactness to one open
neighborhood of unique exact roots.  For Proposition 3, check both homotopy
endpoints, the uniform singleton gap along (4.4), and the compact-tube
quantifiers.

## 8. Vanishing debt-drop charge forces a floor-safe outside-activation gate

The debt moat leaves two genuinely different ways for a charged edge to stay
off the minimum fiber.  Its semantic debt can fall by a macroscopic amount,
or the debt drop can vanish along a charged family.  The second possibility
has a rigid limit which uses nonsingleton incentives, not just another
singleton-matrix classification.

Fix a reward bound `M>=1` and a terminal witness gap `Gamma>0`.  For a carrier
pair `X` write `d_i(X)=X.2_i-X.1_i` and `D(X)=sum_i d_i(X)`.  Consider any
sequence `X_n,q_n` such that, literally,

```text
X_n in quittingTerminalSemanticCarrier reward,
IsεQuittingRootNash reward X_n.1 0 q_n,
X_n.1>=P,
a<=absorption(q_n)                         (a>0),       (8.1)
Delta_n=D(X_n)-D(Prefix(q_n,X_n))->0.                   (8.2)
```

The pairs and roots need not come from one orbit.  In particular this applies
to one selected charged row in each member of a varying exact-path family.

> **Proposition 5 (zero-drop charged rows have a normal blocker gate).**
> On literal `Fin 4`, in the no-uniform branch of Proposition 1, a subsequence
> of `(X_n,q_n)` has a limit `(X,q)` and distinct players `k,i` with the
> following properties.  Put `p=q_k(Quit)`.  Then
>
> ```text
> a/8 <= p <= 1-Gamma/(4M),                            (8.3)
> q = soloRoot(k,p),
> d_j(X)=0 for j!=k,       d_k(X)=D(X)>=D_*>0,          (8.4)
> X.1_k=s_k.                                           (8.5)
> ```
>
> Define the blocker endpoint and its exact threshold by
>
> ```text
> Q_i=(1-p)s_i+p*r_{ki}(i),
> R_i=r_k(i),
> T_i=(Q_i-p*R_i)/(1-p).                               (8.6)
> ```
>
> Then
>
> ```text
> P_i <= Q_i < T_i <= X.1_i,
> R_i < Q_i,                                           (8.7)
> ```
>
> and if `Y` is obtained from `X.1` by replacing only coordinate `i` by
> `T_i`, the same solo root `q` is exact Nash at the floor tail `Y`.
> Player `k` is genuinely mixed and player `i` is exactly indifferent there.
> Thus the vanishing-debt-drop arm produces a quantitatively charged,
> floor-safe outside-activation gate; it cannot converge to a closed solo
> face.

**Proof.**  Let `X'_n=Prefix(q_n,X_n)`.  Exact semantic prefixing decreases
every nonnegative debt coordinate.  The summed opponent-absorption account
therefore gives

```text
sum_j O_j(q_n)d_j(X_n) <= Delta_n.                     (8.8)
```

Collision is contained in every opponent-absorption event.  Since every
carrier has total debt at least `D_*>0`,

```text
D_* collision(q_n) <= Delta_n.                        (8.9)
```

Hence collision mass tends to zero.  The exact decomposition of absorption
into collision mass plus the four singleton masses and `(8.1)` show that,
eventually, some singleton has mass at least `a/8`.  Pass to a subsequence on
which its owner is one fixed `k`, and then use compactness of the carrier and
the product-root cube to obtain `X_n->X`, `q_n->q`.  The limiting singleton
mass is at least `a/8`, while limiting collision mass is zero.  Zero collision
permits at most one positive Quit marginal, so `q` is the solo root owned by
`k`, and its hazard `p` is its singleton mass.  This proves the lower half of
`(8.3)`.

For every `j!=k`, the singleton coalition `{k}` is contained in `j`'s
opponent-absorption event.  The exact coordinate debt-drift inequality gives

```text
mass_{q_n}({k}) d_j(X_n)
  <= d_j(X_n)-d_j(X'_n).
```

Summing over `j!=k`, using `mass({k})>=a/8`, and `(8.2)` gives
`sum_(j!=k)d_j(X_n)->0`.  Thus all complementary limiting debts vanish.
The limit remains in the carrier, so `D(X)>=D_*>0`; consequently `k` carries
all of the positive limiting debt, proving `(8.4)`.

Exact Nash is closed under the joint limit.  The checked terminal-gap
marginal cap applies because every tail is above punishment and boxed, giving
the upper half of `(8.3)`.  Thus both actions of `k` have positive support.
Against a solo root its forced Continue value is its own tail coordinate and
its forced Quit value is `s_k`, so exact mixing gives `(8.5)`.

Suppose the same root were exact at the singleton vector `r_k`.  Its positive
solo hazard, together with punishment normality `P_k<=s_k`, would enter the
checked punishment-completed solo-cycle compiler and yield a uniform-equilibrium
payoff.  Hence it is not exact there.  The owner is automatically indifferent,
so the solo endpoint characterization supplies a distinct blocker `i` with

```text
R_i < Q_i.                                            (8.10)
```

Exactness at `X.1` gives

```text
Q_i <= p*R_i+(1-p)*X.1_i,
```

and therefore `T_i<=X.1_i`.  Since `p<1`, `(8.10)` also gives

```text
T_i-Q_i=p*(Q_i-R_i)/(1-p)>0.                          (8.11)
```

The stationary unilateral cap of player `i` against the solo root is
`max(Q_i,R_i)=Q_i`.  The behavioral punishment value is below every such
stationary cap, hence `P_i<=Q_i`.  This proves `(8.7)`.

Finally, a root's endpoint inequality for player `j` depends on the declared
tail only through coordinate `j`.  Replacing `X.1_i` by `T_i` leaves every
other player's support condition unchanged, and `(8.6)` makes player `i`'s
condition equality.  The new tail is boxed and floor-safe by `(8.7)`, and
`q` retains charge `p>=a/8`.  `QED`

### Exact scope

Proposition 5 is a limit producer, not yet the desired payoff return.  It
gives a strict dichotomy for any fixed-charge family:

1. a subsequence has a nonvanishing semantic debt drop, which is the required
   nonperturbative debt-excursion architecture; or
2. a subsequence has vanishing drop and produces the displayed two-label
   floor-safe activation gate.

The blocker is indifferent but still plays Continue in the limiting root.
No claim is made that a nearby full-game Nash equilibrium retains both `k`
and `i`: the equilibrium correspondence can jump to the all-Continue root.
Converting this gate into a two-owner exact edge, or proving that such a jump
enters an already solved branch, is the remaining step.

Independent falsification review:
`feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_EULER__PROPOSITION_5.md`
checks the `a/8` selection, actual debt-drift localization, compact solo
limit, marginal cap, punishment-completed blocker, threshold algebra, floor
safety, and endpoint-coordinate locality.  Its verdict is `PASS` with no
repair and with the same two-owner/return nonclaim.  A second review,
`feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_RAMSEY__PROPOSITION_5.md`,
requires and then passes the literal carrier-membership and exact-root-at-
`X_n.1` quantifiers now displayed in `(8.1)`.

## 9. The blocker gap forces collision premium or nonlocal exact repayment

Proposition 5 states only a strict blocker inequality, but on a fixed charged
cell it is uniformly strict.  Put

```text
alpha=a/8,             d=Gamma/(4M),
g_{k,i}(p)=(1-p)s_i+p*r_{ki}(i)-r_k(i),
G_k(p)=max_(i!=k) g_{k,i}(p).                          (9.1)
```

Whenever the interval `[alpha,1-d]` is nonempty, define

```text
g_a=min_(k in Fin 4, p in [alpha,1-d]) G_k(p).         (9.2)
```

> **Proposition 6 (uniform blocker seam and exact excursion/collision
> split).**  In the no-uniform branch, `g_a>0`.  Hence the blocker `i` in
> Proposition 5 may be selected so that, with `g=Q_i-R_i`,
>
> ```text
> g>=g_a,
> T_i-Q_i=p*g/(1-p)>=alpha*g_a.                        (9.3)
> ```
>
> Write `b=r_{ki}(i)`.  Exactly one of the following two useful alternatives
> can be selected.
>
> 1. **Quantitative pair-collision premium:**
>
>    ```text
>    b-R_i>=g/2>=g_a/2.                                (9.4)
>    ```
>
> 2. **Nonlocal exact repayment:** `b-R_i<g/2`.  Let `Y` be the floor tail
>    from Proposition 5, let `q=soloRoot(k,p)`, and extend the exact first
>    row `(Y,q)` to any infinite punishment-floor Nash--Bellman orbit
>    `(V_t,q_t)` with
>
>    ```text
>    V_0=Y,       q_0=q,
>    V_(t+1)=Succ(V_t,q_t).                            (9.5)
>    ```
>
>    Then `V_1(i)=Q_i`, the orbit has a payoff limit `L`, and
>
>    ```text
>    L_i-Q_i>=alpha*g_a/2.                             (9.6)
>    ```
>
>    Consequently some finite later annotation satisfies
>
>    ```text
>    V_t(i)-V_1(i)>=alpha*g_a/4,                       (9.7)
>    ```
>
>    and the exact segment from `V_t` back to `V_0` contains the original
>    edge of charge at least `alpha`.  Before that charged edge the orbit has
>    made a source-matched nonlocal payoff excursion of fixed size.

The pair premium in `(9.4)` is a reward-table collision incentive, not an
assertion that the orbit has already spent collision probability.  The
repayment in `(9.7)` is one-coordinate and need not return the other three
coordinates.  Thus Proposition 6 reaches exactly the two maintained escape
architectures but does not yet give a payoff near-return.

### Proof

Fix `k` and `p in [alpha,1-d]`.  If `G_k(p)<=0`, every outsider's
Quit-minus-Continue endpoint difference against the solo root at the full
singleton vector `r_k` is nonpositive.  The owner is indifferent there.
Thus the positive solo root is exact endpoint Nash at `r_k`.  By all-player
normality, `P_k<=s_k`, so the checked punishment-completed solo compiler
would make `r_k` a uniform-equilibrium payoff.  This contradicts the standing
branch.  Hence `G_k(p)>0` for every `(k,p)` in the compact finite union.
Continuity of the finite maximum and compactness give `g_a>0`.

In Proposition 5 choose an outsider attaining `G_k(p)`.  Then
`g=Q_i-R_i>=g_a`, and the definition of `T_i` gives

```text
T_i-Q_i=p(Q_i-R_i)/(1-p)=p*g/(1-p).
```

Since `p>=alpha` and `p<1`, `(9.3)` follows.

Now either `(9.4)` holds or `b-R_i<g/2`.  Work in the latter case.  Elementary
algebra using

```text
g=(1-p)(s_i-R_i)+p(b-R_i)
```

gives

```text
s_i-Q_i
  =p*(g-(b-R_i))/(1-p)
  >p*g/(2(1-p))
  =(T_i-Q_i)/2
  >=alpha*g_a/2.                                      (9.8)
```

The tail `Y` is boxed and above punishment, and `q` is exact there.  Ordinary
finite mixed-Nash existence at every subsequent boxed floor tail, exact
floor propagation, and dependent choice extend this row to an infinite
punishment-floor orbit.  For its first successor,

```text
V_1(i)=pR_i+(1-p)T_i=Q_i.                             (9.9)
```

The checked all-orbits value-limit theorem gives a limit `L` satisfying
`L_i>=s_i`.  Equations `(9.8)`--`(9.9)` prove `(9.6)`.  Convergence then gives
some finite `t` satisfying `(9.7)`.  By the orientation in `(9.5)`, the
finite exact path runs from `V_t` through `V_1` to `V_0`; its final edge is
the original charged row `q`.  `QED`

### Independent falsification review

`feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_RAMSEY__PROPOSITION_6.md`
checks especially:

1. positivity of the compact minimum `g_a`, including the owner indifference
   and all outsider endpoint signs at `r_k`;
2. the factor `1/2` in `(9.8)` and the fixed constants in `(9.3)--(9.7)`;
3. existence/orientation of an infinite exact floor extension anchored at
   the supplied first root; and
4. the scope distinction between a pair-reward premium, actual collision
   probability, one-coordinate repayment, and full payoff near-return.

Its verdict is `PASS` with no repair.  It confirms the anchored infinite-
orbit construction and the reverse Bellman-edge orientation, and retains the
explicit nonclaim that this is not yet invariant descent or a full payoff
near-return.

## 10. Reviewed consumption of the pair-premium arm

Section 18 of `notes/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY.md`, independently
reviewed in
`feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_18.md`,
applies the checked membership-toggle theorem to the pair in `(9.4)`.  Its
conclusion is the following exact same-table refinement.

> **Reviewed input 7 (pair premium dispatch).**  The pair-premium arm of
> Proposition 6 yields either:
>
> 1. a full-terminal-gap pair-to-triple join: for some
>    `j notin {k,i}`,
>
>    ```text
>    r_{ki}(j)+Gamma<=r_{kij}(j);                    (10.1)
>    ```
>
> 2. the checked `FinFourLeaveJoinStationaryTwoDebtorHandoff` on the same
>    reward table and terminal witness.

Indeed, terminal-gap failure of the pure pair gives either `(10.1)` or a
member leave.  The member cannot be `i`, because `(9.4)` is a strict join in
the opposite direction; hence `k` leaves.  Punishment normality of `i`
supplies a second atomic join with a third label, and the two inequalities
are exactly the inputs of the checked stationary handoff constructor.

This input removes the bare pair premium as a residual, but it does not close
either resulting arm.  The stationary handoff returns to the paid semantic
source problem, while `(10.1)` is still a static pair-to-triple toggle.  The
only other output of Proposition 6 is the exact repayment arm.

## 11. The repayment arm immediately hits a second charge and a support wall

Continue in alternative 2 of Proposition 6.  Put

```text
eta=alpha*g_a/2,
d=Gamma/(4M),
c_1=eta/(eta+2M),
rho=d*alpha*g_a/(16M).                               (11.1)
```

The actual gate supplies `0<alpha<=p<=1-d`; in particular `0<d<1`, and all
four constants in `(11.1)` are positive.

Let `q_1` be the exact root selected at the first successor `V_1` in any
anchored infinite extension `(9.5)`, and write

```text
x=q_1(k)(Quit),
H=sum_(j notin {k,i}) q_1(j)(Quit),
c=b-R_i.                                              (11.2)
```

> **Proposition 8 (second charge and quantitative reached-support wall).**
> Every such extension satisfies
>
> ```text
> A(q_1)>=c_1.                                        (11.3)
> ```
>
> Moreover:
>
> 1. if `c>=0`, then some `j notin {k,i}` has
>
>    ```text
>    q_1(j)(Quit)>=rho;                               (11.4)
>    ```
>
> 2. if `c<0`, then either `(11.4)` holds for some third label, or
>
>    ```text
>    x-p>=alpha*g_a/(8M).                             (11.5)
>    ```
>
> Thus the repayment branch cannot pass directly to a collision-free small
> perturbation of the old solo root.  Its next literal exact row is charged,
> and it either activates a player outside the owner--blocker pair at a fixed
> rate or spends a fixed upward increment of the old owner's bounded hazard.

### Proof

Equation `(9.8)` says

```text
V_1(i)=Q_i<=s_i-eta.                                  (11.6)
```

The checked singleton-deficit absorption estimate, applied to the exact root
`q_1` at the literal floor tail `V_1`, gives `(11.3)`.

The exact-floor terminal-gap marginal cap gives

```text
q_1(j)(Quit)<=1-d                                    (11.7)
```

for every player `j`.  In particular player `i` uses Continue with positive
probability, so its Quit-minus-Continue endpoint difference under `q_1` is
nonpositive.

Compare that difference with the opponent product environment in which only
`k` retains the same marginal `x` and both labels outside `{k,i}` are forced
to Continue.  Call the latter difference `F(x)`.  Since `V_1(i)=Q_i`,

```text
F(x)=(1-x)(s_i-Q_i)+x(b-R_i).                        (11.8)
```

The forced-action difference is an expectation of a function of the three
opponents bounded in absolute value by `2M`.  Coupling the two third-player
marginals to Continue therefore gives

```text
F(x)<=4M H.                                           (11.9)
```

Notice that `q_1(i)` does not enter this comparison: a player's own mixing
rate never changes that player's two forced-action endpoints.

Suppose first that `c=b-R_i>=0`.  Equations `(11.6)--(11.8)` and
`x<=1-d` give

```text
F(x)>=d(s_i-Q_i)>=d*eta.
```

Thus `(11.9)` gives `H>=d*eta/(4M)`.  There are exactly two labels outside
`{k,i}`, so one has Quit marginal at least

```text
d*eta/(8M)=d*alpha*g_a/(16M)=rho,
```

proving `(11.4)`.

Now suppose `c<0`.  At the old rate `p`, direct substitution and `(9.3)`
give

```text
F(p)=p(Q_i-R_i)=p*g>=alpha*g_a.                       (11.10)
```

If `H>=alpha*g_a/(8M)`, one of the two third labels has marginal at least
`alpha*g_a/(16M)>=rho`, using `d<1`; this is `(11.4)`.  Otherwise `(11.9)`
gives `F(x)<F(p)/2`.  The affine function `(11.8)` is strictly decreasing,
and

```text
|F'(x)|=(s_i-Q_i)-(b-R_i)<=4M.                        (11.11)
```

Therefore `x>p` and

```text
4M(x-p)>=F(p)-F(x)>F(p)/2>=alpha*g_a/2,
```

which proves `(11.5)`.  `QED`

### Exact scope and requested falsification

Proposition 8 is a literal two-row statement.  The upward rate increment in
`(11.5)` is a bounded obstruction only if a later theorem regenerates the
same reached solo configuration; that regeneration is not asserted here.
Likewise `(11.4)` is an exact outside-owner activation, but not yet a
collision, semantic source lift, or payoff return.  The result should not be
used as an iteration theorem before those provenance fields are supplied.

Requested independent checks are: the endpoint-difference orientation in
`(11.8)`, the `4M H` coupling in `(11.9)`, use of the marginal cap to force
Continue support for `i`, the factor two from the two remaining labels, and
the derivative/rate-increment constants in the negative-`c` arm.

Independent reviews:

- `feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_EULER__PROPOSITION_8.md`;
- `feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_RAMSEY__PROPOSITION_8.md`.

Both verdicts are `PASS` with no repair and retain the literal two-row,
noniteration scope.

## 12. Literal carrier iteration removes the all-Continue/solo selection wall

The independently reviewed note
`notes/CODEX_RAMSEY__PAID_SOLO_PREFIX_REACHED_SUPPORT_WALL.md` proves the
following exact fact after its charged-relation arrow repair: starting at the
literal carrier gate `X` of Proposition 5 and repeatedly prefixing the same
solo root `q=soloRoot(k,p)`, the unique-debtor vector is preserved at every
exact row, and within bounded depth the same root reaches a literal carrier
tail where an outsider strictly prefers Quit.  Its review is
`feedback/CODEX_RAMSEY__PAID_SOLO_PREFIX_REACHED_SUPPORT_WALL__BY_CODEX_CEDAR.md`.

The wall note leaves open the possibility that exact-root selection merely
jumps to all-Continue or another solo-`k` root.  All-player normality rules
out an infinite repetition of that escape.

> **Proposition 9 (source-native wall dispatch).**  Start with the literal
> zero-drop carrier gate of Proposition 5, reselecting a maximizing blocker
> as in Proposition 6.  Then after finitely many literal exact carrier
> prefixes, at least one of the following occurs on the same reward table.
>
> 1. **Strict semantic debt descent.**  There is an exact floor-safe carrier
>    edge
>
>    ```text
>    W.1 -> Prefix(z,W).1                                  (12.1)
>    ```
>
>    and constants `omega>0`, `D>0` such that
>
>    ```text
>    A(z)>=omega,
>    D(Prefix(z,W))<=D(W)-omega*D,
>    D(W)=D.                                               (12.2)
>    ```
>
> 2. **Full-gap triple join.**  There are distinct `k,i,j` with
>
>    ```text
>    r_{ki}(j)+Gamma<=r_{kij}(j).                          (12.3)
>    ```
>
> 3. **Stationary two-debtor handoff.**  The checked
>    `FinFourLeaveJoinStationaryTwoDebtorHandoff` is nonempty.
>
> Thus the all-Continue/changed-solo-root response at the reached wall is not
> a fourth residual.  If it persisted, backward compactification of the
> literal prefixes would produce a fixed-owner semantic spine with uniformly
> positive Quit hazard, contradicting punishment normality.

### Proof

We prove a slightly sharper iterative claim.  A **solo gate state** consists
of a carrier pair `Z`, a solo-`k` exact root of rate

```text
alpha<=x<=1-d,                                         (12.4)
```

and

```text
d_k(Z)=D>0,
d_l(Z)=0 for l!=k,
Z.1_k=s_k.                                             (12.5)
```

The original `X,q` is such a state.  For a given gate choose an outsider
`i` maximizing `g_(k,i)(x)`.  Equations `(9.1)--(9.2)` give
`g_(k,i)(x)>=g_a>0`.  Apply the reviewed repeated-prefix wall theorem.  It
produces a finite nonempty word of the same rate-`x` solo root, every row
exact and every state in the carrier, ending at a wall pair `W` such that

```text
Delta_i(W.1,soloRoot(k,x))>0.                          (12.6)
```

Throughout the word `(12.5)` and total debt `D` are preserved exactly.

Put

```text
c=r_{ki}(i)-r_k(i).                                    (12.7)
```

If `c>0`, apply Reviewed input 7 with `kappa=c`.  This gives `(12.3)` or the
stationary handoff, so assume `c<=0`.

Let `E(W)` be the compact nonempty set of exact product roots at the literal
tail `W.1`.  Suppose first that no root in `E(W)` is supported inside the
singleton face `{k}`.  The continuous opponent-absorption function for `k`
is then strictly positive on `E(W)`.  Compactness gives

```text
omega=min_(z in E(W)) OppAbs_k(z)>0.                   (12.8)
```

Choose any `z in E(W)`.  Exact semantic prefixing preserves carrier
membership and floor safety.  Every outsider has old debt zero, hence exact
prefix debt zero.  For `k`, the checked block-action formula gives

```text
d_k(Prefix(z,W))
 <=OpponentContinue_k(z)*d_k(W)
 <=(1-omega)D.                                        (12.9)
```

Thus total debt falls by at least `omega D`, and total absorption is at least
opponent absorption `omega`.  This is `(12.1)--(12.2)`.

It remains to analyze a root in `E(W)` supported inside `{k}`.  Write its
owner rate as `y`.  The wall witness's Quit-minus-Continue difference against
a solo-`k` environment of rate `u` is affine:

```text
F(u)=(1-u)(s_i-W.1_i)+u c.                            (12.10)
```

Equation `(12.6)` says `F(x)>0`, while exactness of the selected root says
`F(y)<=0`.  If `y=0`, all-Continue exactness would give
`s_i-W.1_i<=0`; together with `c<=0` this would imply `F(x)<=0`, a
contradiction.  If `c=0`, then `F(x)>0` makes
`s_i-W.1_i>0`, so `F(y)>0` for every `y<1`.  The terminal marginal cap gives
`y<=1-d<1`, again a contradiction.  Therefore necessarily

```text
c<0,
x<y<=1-d.                                             (12.11)
```

Lemma 2.2 of the wall note, applied to this exact solo root at `W`, shows
that `W,y` is another solo gate state with the same owner and the same debt
vector.  We may restart the construction there.

Suppose this restart never reaches one of the three displayed outputs.
Flatten its successive finite repeated-root words.  We obtain an infinite
outward prefix sequence

```text
Z_(n+1)=Prefix(root_n,Z_n),                            (12.12)
```

where every `Z_n` is in the carrier, every `root_n` is exact at `Z_n.1`,
only `k` Quits, and

```text
alpha<=root_n(k)(Quit)<=1-d.                          (12.13)
```

The carrier and the closed rate interval are compact.  Take longer and
longer terminal windows of `(12.12)` and use a diagonal subsequence with
`n_m>=m`.  For
each fixed backward depth `t`, let

```text
pair_t =lim_m Z_(n_m-t),
rho_t  =lim_m root_(n_m-t-1).                         (12.14)
```

Continuity of semantic prefixing, closedness of the carrier and exact-Nash
graph, and `(12.12)` give

```text
pair_t=Prefix(rho_t,pair_(t+1)),
rho_t exact at pair_(t+1).1.                          (12.15)
```

Every outsider of `k` Continues purely, and `(12.13)` survives in the limit.
Hence the owner survival product is at most `(1-alpha)^n` and tends to zero;
the first limiting root has both Quit mass at least `alpha` and Continue mass
at least `d`.

Apply the checked theorem

```text
QuittingTerminalExploitabilityWitness.
  atomic_restrictions_of_soloSemanticSpine_survival_zero
```

to `(12.14)--(12.15)`.  It yields

```text
s_k<P_k.                                               (12.16)
```

But all-player punishment normality gives `P_k<=s_k`.  This contradiction
shows that the restart terminates after finitely many walls.  At termination
we are in `(12.1)`, `(12.3)`, or the stationary handoff.  `QED`

### Probability, orientation, and exact scope

The finite construction runs in charged-relation orientation from a
continuation carrier to its prefixed current carrier.  The compactification
in `(12.14)` deliberately reverses terminal windows; this is what produces
the behavioral-spine orientation required by `(12.15)`.  An outward infinite
prefix orbit cannot be inserted directly into the occupation theorem without
this diagonal reversal.

The debt decrement in `(12.9)` is all-behavior semantic debt, not stationary
regret.  It uses the exact semantic prefix block-action identity.  The number
`omega` is source-specific but fixed and positive once the finite wall is
reached.  Proposition 9 does not iterate debt descent after support changes,
does not consume `(12.3)`, and does not yet produce a payoff near-return.

Requested falsification should focus on: compactness of `E(W)` and positivity
of `(12.8)`; exclusion of all-Continue and the sign/rate conclusion `(12.11)`;
the exact outsider-zero and owner debt bounds in `(12.9)`; and the backward
diagonal indexing/closed-graph passage in `(12.14)--(12.15)`.

Independent reviews:

- `feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_EULER__PROPOSITION_9.md`;
- `feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_RAMSEY__PROPOSITION_9.md`.

Both reviews pass the mathematics.  The second required the three literal
repairs now incorporated above: carrier rather than attained-profile wording,
payoff-component typing in `(12.1)`, and `n_m>=m` in the diagonal selection.
