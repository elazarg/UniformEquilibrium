# Crossed support-two finite dispatch

Authors: `CODEX_EULER`

Independent review:
[`CODEX_CEDAR`](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_CEDAR.md)

## Exact statement

Let `I` be a four-element player set, let `r_S(i)` be player `i`'s reward
when the nonempty first-quitter coalition is `S`, and let `chi_i` be the exact
quitting punishment value.  Suppose a normalized singleton source packet has
support exactly `{a,b}`.  Under a terminal exploitability witness, label the
two outsiders `c,d` so that the checked crossed inequalities are

```text
r_a(c) < r_c(c) < r_b(c),
r_b(d) < r_d(d) < r_a(d).                            (1)
```

For an ordered supported pair `(x,y)`, where `x` is the collision owner and
`y` is the sure blocker, let `z,t` be the other two players and define

```text
Delta_x^y = r_{x,y}(x)-r_y(x),                       (2)

A_s^0(x,y) = r_{s,y}(s)-r_y(s),
A_s^1(x,y) = r_{x,s,y}(s)-r_{x,y}(s)  (s=z,t),       (3)

A_y^0(x,y) = chi_y-r_y(y),
A_y^1(x,y) = r_x(y)-r_{x,y}(y).                      (4)
```

The packet gives `A_y^0(x,y)<=0` for either supported blocker.

There is a finite, relabeling-invariant alternative.

1. If either supported singleton row is no-harm for both outsiders, the
   checked no-harm singleton compiler applies.

2. Otherwise (1) holds.  For each orientation `(x,y)`, a legal collision
   repair rate `p in [0,1]` exists exactly as follows:

   - if `Delta_x^y<0`, then necessarily `p=0`, and a repair exists exactly
     when `A_z^0<=0` and `A_t^0<=0`;
   - if `Delta_x^y>0`, then necessarily `p=1`, and a repair exists exactly
     when `A_z^1<=0`, `A_t^1<=0`, and `A_y^1<=0`;
   - if `Delta_x^y=0`, a repair exists exactly when the three affine rows

     ```text
     (1-p)A_j^0+pA_j^1 <= 0  (j=z,t,y)               (5)
     ```

     pass the finite sign/cross-product criterion in Lemma 1 below.

3. If a rate exists in either orientation, its exact scalar repair conditions
   are accepted by the checked unrestricted-behavior collision compiler,
   which supplies an accuracy-dependent near-minmax punishment continuation
   at every positive tolerance.

4. If neither orientation works, the crossed chamber is replaced by an exact
   finite residual.  Off the equality hyperplanes, put

   ```text
   alpha = r_{a,b}(a)-r_b(a),
   beta  = r_{a,b}(b)-r_a(b),                        (6)

   J_b  = max_{s in {c,d}} (r_{s,b}(s)-r_b(s)),
   J_a  = max_{s in {c,d}} (r_{s,a}(s)-r_a(s)),
   J_ab = max_{s in {c,d}} (r_{a,b,s}(s)-r_{a,b}(s)). (7)
   ```

   A terminal counterexample must satisfy

   ```text
   alpha<0  => J_b>0,
   beta <0  => J_a>0,
   alpha>0 and beta>0 => J_ab>0.                    (8)
   ```

   On exactly one of `alpha=0` or `beta=0`, the residual is the explicit
   negation of the finite criterion in Lemma 1 for the indifferent orientation,
   together with the forced endpoint test for the other orientation.  If both
   vanish, apply Lemma 1 to both orientations.  Thus no continuum of
   unclassified rates remains.

5. Every positive join defect in (8) produces a larger sure-exit candidate.
   Either that candidate is an exact unrestricted-behavior equilibrium, or
   one of finitely many displayed member-leave/outsider-join inequalities
   holds.  Iterating these strict toggles from the anchored join yields a
   finite path and a reachable simple directed coalition-toggle cycle of even
   length in `{4,6,8,10,12,14,16}`.

This is a finite reduction of the named crossed support-two obligation.  It
does not assert that the final toggle cycle compiles.

### Lemma 1 (affine interval feasibility)

For finitely many real endpoint pairs `(u_j,v_j)`, there exists `p in [0,1]`
such that

```text
(1-p)u_j+p v_j <= 0  for every j                    (9)
```

if and only if:

- for every `j`, `u_j<=0` or `v_j<=0`; and
- whenever `u_i>0>=v_i` and `u_j<=0<v_j`,

  ```text
  u_i v_j <= v_i u_j.                               (10)
  ```

These are only sign and polynomial inequalities.

## Conjecture-facing change

The maintained obligation is
[`questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`](../questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md).
This packet is its accepted partial-answer type: it removes the real-rate
quantifier and replaces the unresolved crossed chamber by a strictly smaller
finite semialgebraic residual.

Before this result, the checked four-player support-two boundary stopped at
the crossed singleton pattern (1), while the collision consumer still
quantified over a real rate and over pair/triple reward inequalities.  The
result removes that rate quantifier exactly.

Generically, every legal rate is forced to be `0` or `1`; the entire failed
collision chamber becomes the three relabeling-invariant join defects (8).
The two equality faces are reduced to the finite cross-product test (10).
Positive defects are then promoted to checked sure-exit candidates, leaving a
finite strict-toggle path/cycle residual when those candidates fail.

Two newly checked singleton screens refine this output but do not replace it.
If `g>0` is the terminal exploitability gap, then

```text
r_a(a)<=-g or r_a(c)+g<=r_c(c),
r_b(b)<=-g or r_b(d)+g<=r_d(d).                     (11)
```

Thus the residual splits into four `NN,NP,PN,PP` owner/preemption cases and
then intersects (8).  If a supplied nonprojective normalized-solo principal
set `P` has size two, the checked principal screen further restricts it to

```text
P in {{a,c},{b,d},{c,d}}.                           (12)
```

No theorem supplies a size-two principal in general.  Equations (11) concern
only singleton rows, while (8) concerns nonsingleton rows, so neither is
claimed to imply the other.

What remains open is to match every final strict-toggle cycle/residual chamber
to an existing compiler or to narrow it again.  No arbitrary-cycle compiler
is obtained here.

## Definitions and assumptions

The collision root has `y` Quit surely at date zero, `x` Quit independently
with probability `p`, and both spectators Continue.  Its prescribed payoff is

```text
(1-p)r_y+p r_{x,y}.                                 (13)
```

The checked mechanism appends an accuracy-dependent punishment continuation
for blocker `y`.  Its three exact conditions are:

- owner endpoint optimality;
- spectator no-join for both spectators; and
- blocker balance against `chi_y`.

The owner is allowed an unrestricted behavioral deviation, as are the blocker
and spectators.  The product randomization in the displayed root is ordinary
independent behavioral randomization.  No public correlating device, bounded
controller, or restricted pure-time deviation class is introduced.

A coalition toggle `S -> S triangle {i}` is only the strict table inequality

```text
r_{S triangle {i}}(i)>r_S(i),                       (14)
```

using the extended reward `r_empty=0`.  It is not itself asserted to be an
executable Bellman edge.

## Source correspondence

The following declarations were checked directly.

- `quittingGame_uniformPayoff_or_normalizedSingletonSourcePacket` in
  `UniformEquilibrium/Quitting/Classification/AnalyticWaist.lean` is the
  arbitrary-game analytic split.  The new reduction begins only after its
  normalized-packet branch has support exactly two.
- `QuittingNormalizedSingletonSourcePacket` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/AnalyticPacket.lean`
  supplies mass, target, mixture, solo, punishment, and active-pin fields.
- `exists_uniformEquilibriumPayoff_of_support_eq_pair_of_first_noHarm` and the
  exact support-two formulas in
  `UniformEquilibrium/Quitting/Classification/SingletonPacketSupport.lean`
  close the aligned chamber and give the supported-owner singleton
  comparisons.
- `exists_crossedSpectators_of_finFour_support_eq_pair`,
  `supportOwners_negative_or_crossedSpectators_preempt`, and
  `nonprojectivePrincipal_ne_safePairs_of_support_eq_pair` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/Support.lean`
  give (1), (11), and (12).
- `QuittingCollisionOwnerOptimal`,
  `QuittingCollisionSpectatorNoJoin`,
  `QuittingCollisionBlockerBalance`, and
  `quittingCollisionRepairWorks_iff` in
  `UniformEquilibrium/Quitting/Boundary/Repair/CollisionRepairCharacterization.lean`
  are the exact supplied-rate interface.
- `quittingInstantPunishmentεEquilibriumExistence_of_collisionRepair` in
  `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean` is the
  checked collision adapter.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  is the downstream terminal-selection waist.
- `collisionRepair_condition_failure` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/CollisionRepairScreen.lean`
  excludes every successful repair under a terminal exploitability witness.
- `isQuittingSureExitSet_iff_forall_max`,
  `isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet`, and
  `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean` are the exact
  all-behavior join-promotion consumer.
- `quittingPunishmentValue_le_max_solo` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean` supplies the completion
  boundary test below.

The new content is the exact elimination of the collision rate, the generic
three-defect residual, the equality-face cross-product test, and the anchored
finite toggle reduction.  None of these is a restatement of the supplied-rate
characterization.  No paper theorem is invoked; the proof is a new finite
algebraic reduction of the project interfaces.

## Proof

### 1. Owner rate purification

For orientation `(x,y)`, write

```text
O_0=r_y(x),  O_1=r_{x,y}(x),  Delta=O_1-O_0.
```

Owner optimality is exactly

```text
max(O_0,O_1) <= (1-p)O_0+pO_1.                     (15)
```

If `Delta>0`, subtracting `O_0` gives
`Delta<=p Delta`, hence `p>=1`; legality forces `p=1`.  If `Delta<0`, (15)
instead gives `0<=p Delta`, hence `p<=0`; legality forces `p=0`.  If
`Delta=0`, (15) is an identity for every legal `p`.

### 2. Spectator and blocker rows

At rate `p`, spectator `s` receives the prescribed mixture in (13), while
joining changes the two endpoint coalitions from `y,x y` to `s y,x s y`.
Its no-join condition is therefore

```text
(1-p)A_s^0+pA_s^1<=0.                              (16)
```

Blocker balance is

```text
p r_x(y)+(1-p)chi_y <= (1-p)r_y(y)+p r_{x,y}(y),
```

which rearranges to the same affine form with endpoints (4).  Packet pinning
and the punishment floor give `chi_y<=r_y(y)`, so its rate-zero endpoint is
automatic.

Combining these facts with Step 1 proves the strict-sign cases in item 2 of
the statement.

### 3. Equality-face quantifier elimination

A row with `u>0>=v` in (9) requires

```text
p>=u/(u-v),                                         (17)
```

and a row with `u<=0<v` requires

```text
p<=-u/(v-u).                                        (18)
```

A row with both endpoints nonpositive is automatic, while two positive
endpoints are impossible.  All denominators in (17)--(18) are positive.
Every lower bound is at most every upper bound exactly when

```text
u_i(v_j-u_j) <= -u_j(u_i-v_i),
```

which reduces to (10).  Choose the maximum lower bound (or zero if none).
The cross inequalities place it below every upper bound (or one if none), so
it satisfies all rows.  This proves necessity and sufficiency, including zero
endpoints which force `p=0` or `p=1`.

### 4. Generic three-defect residual

For orientation `(a,b)`, owner difference is `alpha` and the rate-one blocker
endpoint is `-beta`.  For `(b,a)`, owner difference is `beta` and the
rate-one blocker endpoint is `-alpha`.

- If `alpha,beta<0`, the two orientations are forced to rate zero.  Failure of
  both repairs is exactly `J_b>0` and `J_a>0`.
- If `alpha<0<beta`, orientation `(a,b)` is forced to rate zero, so its failure
  is `J_b>0`; the reversed rate-one orientation already fails blocker balance
  because `-alpha>0`.  The opposite mixed-sign chamber is symmetric.
- If `alpha,beta>0`, either orientation is the same sure pair `{a,b}`.  Both
  supported members' conditions hold, so failure is exactly `J_ab>0`.

Under a terminal witness every legal repair fails by
`collisionRepair_condition_failure`; hence (8).  Conversely, the displayed
defects block both support orientations in their respective generic sign
chambers.  This proves the exact generic residual.

The checked singleton screen independently yields the four cases (11), and
the checked principal screen yields (12) when its extra hypotheses are
present.  Since their declarations use singleton entries/principal matrices
rather than (3), they are intersected with this residual rather than derived
from it.

### 5. Join promotion

Suppose `s notin S` and

```text
r_{S union {s}}(s)>r_S(s).                          (19)
```

Set `T=S union {s}`.  The new member `s` already strictly prefers remaining
in `T`.  If every old member weakly prefers remaining and every other outsider
weakly prefers not joining, these are exactly the sure-exit membership-toggle
inequalities.  The checked pure-set theorem then makes `T` an exact terminal
Nash profile against all behavioral deviations and supplies its uniform
payoff.  Otherwise an old member has a strict leave inequality or a remaining
outsider has a strict join inequality.  This is the finite alternative in
item 5.

Concretely, if `alpha<0` and `s` realizes `J_b>0`, with `t` the other
spectator, either `{b,s}` is sure exit or at least one of

```text
r_s(b)>r_{b,s}(b),
r_{a,b,s}(a)>r_{b,s}(a),
r_{b,s,t}(t)>r_{b,s}(t)                             (20)
```

holds.  The `beta<0` case is symmetric.  If `alpha,beta>0` and `s` realizes
`J_ab>0`, either `{a,b,s}` is sure exit or at least one of

```text
r_{b,s}(a)>r_{a,b,s}(a),
r_{a,s}(b)>r_{a,b,s}(b),
r_{a,b,s,t}(t)>r_{a,b,s}(t).                        (21)
```

holds.

### 6. Finite strict-toggle cycle

Under a terminal witness no coalition, including the empty coalition, is a
sure exit set.  Otherwise the checked pure-set theorem would contradict the
fixed exploitability gap.  Hence every vertex of the four-dimensional
coalition cube has at least one outgoing strict membership toggle.

Start with the anchored join from (8) and repeatedly choose an outgoing
toggle.  Among sixteen coalition vertices one repeats.  Removing the
preperiod and shortening at the first repetition gives a reachable simple
directed cycle.  The cube is bipartite by coalition-cardinality parity, so the
cycle has even length.  Length two would require the same player's same table
comparison in both strict directions, which is impossible.  Its length is
therefore one of `4,6,...,16`.

The negative alternatives in (11) add the strict anchors `{a}->empty` or
`{b}->empty`.  The preemption alternatives compare two singleton coalitions
and are not membership toggles; they are retained as separate labelled data.
Likewise, (12) is a separate conditional principal-face label.  None is used
to claim that the resulting toggle cycle compiles.

## Probability and behavioral-deviation audit

The rate calculation is finite because the blocker quits surely at the first
row.  It does not replace arbitrary deviations by pure actions on its own:
the unrestricted conclusion comes from the checked exact characterization,
whose sufficiency appends a punishment row approaching the exact min-max and
proves terminal epsilon-Nash against every behavioral strategy.

The sure-exit promotion also absorbs at date zero.  The checked sure-set
equivalence explicitly ranges over arbitrary history-dependent randomized
stopping deviations.  No limiting interchange, conditioning, independence
approximation, or finite-horizon substitution is used in the new algebra.

The toggle cycle is only a finite collection of reward inequalities.  No
probability law or strategy is assigned to it, and no equilibrium conclusion
is drawn from it.

## Boundary tests

### Exact positive tests

- With `Delta<0` and both spectator rate-zero defects nonpositive, `p=0`
  satisfies every row because packet blocker balance is automatic.
- With `Delta>0` and all three rate-one defects nonpositive, `p=1` satisfies
  every row.
- On an equality face, endpoint rows `(1,-1)` and `(-1,1)` meet at `p=1/2`;
  (10) holds with equality.  Rows `(2,-1)` and `(-1,2)` require respectively
  `p>=2/3` and `p<=1/3`; (10) fails, exactly detecting infeasibility.

### Packet-interface falsifier

Take all own singleton rewards zero and

```text
r_a(c)=-1, r_b(c)=1,
r_a(d)= 1, r_b(d)=-1,
```

with all other singleton coordinates zero.  Set packet masses
`mu(a)=mu(b)=1/2`, other masses zero, and target zero.  The singleton mixture
is zero coordinatewise, positive masses pin the target, and
`chi_i<=max(r_i(i),0)=0` makes every punishment floor automatic for every
nonsingleton completion.

Choose arbitrary `alpha,beta`, set all nonsingleton rewards zero except

```text
r_{a,b}(a)=alpha, r_{a,b}(b)=beta,
r_{a,b,c}(c)=1,   r_{a,b,d}(d)=1.                  (22)
```

For orientation `(a,b)`, spectator `d` has join defect exactly one at both
endpoints; for `(b,a)`, spectator `c` does.  Thus every rate in both
orientations fails, in every sign chamber and on both equality faces.  The
failure is relatively open under small nonsingleton perturbations.  For any
putative `0<g<=1`, the singleton table also satisfies both preemption arms of
(11), showing that the checked singleton screen still does not determine the
nonsingleton defects.

This family is not a counterexample: all-Never is an exact equilibrium because
every own singleton payoff is zero.  It proves only that the packet and
singleton screens cannot silently supply collision inequalities.

## Adapter and consumer

The arbitrary-data entrance is the checked support-two packet split.  The
no-harm theorem closes the aligned case; under a terminal witness the crossed
spectator theorem supplies (1), and the two updated screens supply (11)--(12).

A feasible rate from the new finite test instantiates the three fields of
`quittingInstantPunishmentεEquilibriumExistence_of_collisionRepair`, or
equivalently `QuittingCollisionRepairWorks`.  This produces terminal
approximate equilibria against unrestricted behavioral deviations at every
positive accuracy, which the established terminal-selection waist turns into
a uniform-equilibrium payoff.  A successful promoted sure set directly uses
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`.

If neither consumer fires, (8), (20)--(21), (11), and when applicable (12)
are the strictly smaller exact residual output.  The final toggle cycle has no
consumer asserted.

## Lean handoff

The narrow formalization should avoid introducing a new global certificate.

1. Add a small endpoint-defect definition near
   `CollisionRepairCharacterization.lean`, or state the formulas directly.
2. Prove the owner-purification trichotomy for `0<=p<=1`.
3. Put Lemma 1 in a finite real-inequality utility file if reusable; for this
   application the index type has only three elements, so a direct proof is
   also reasonable.
4. State a `Fin 4` generic dispatch theorem for `alpha*beta!=0`, returning a
   collision repair in the positive branches or the defects (8) under a
   terminal witness.
5. State the equality-face theorem separately, to keep division and zero
   endpoints out of the generic result.
6. Formalize join promotion as a thin corollary of
   `isQuittingSureExitSet_iff_forall_max`.
7. For the finite-cycle boundary, reuse the existing finite serial-relation
   machinery if it represents the coalition cube without obscuring the
   anchored edge.  The result should return only a finite strict-toggle cycle,
   not a behavioral certificate.
8. Intersect, rather than reprove or derive, the existing owner/preemption and
   principal screens.  Keep the hypothesis `players.card=2` explicit for the
   three-pair conclusion.
9. Add exact tests for the feasible/infeasible affine pairs and the rational
   packet-interface family (for example `alpha=1,beta=-1`).

Player-reindexing/naturality should be used so the final theorem is stated
modulo relabeling rather than duplicated for twelve ordered pairs.

## Scope and nonclaims

- This does not close support size two or the four-player conjecture.
- It does not prove that either supported collision orientation works.
- It does not infer nonsingleton inequalities from singleton packet data.
- It does not force a nonprojective principal or prove that one has size two.
- Singleton preemption edges are not coalition-membership toggles.
- The finite strict-toggle cycle is not a Bellman path, hazard schedule,
  balanced circulation, or existing cyclic certificate.
- The packet-interface family is a boundary falsifier, not a terminal
  counterexample.
- No claim is made about chronological packet reprojection, paid returns, or
  Lean formalization.
