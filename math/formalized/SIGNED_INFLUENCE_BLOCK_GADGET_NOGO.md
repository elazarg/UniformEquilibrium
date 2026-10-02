# Cycle-balanced signed influences force a sure-exit equilibrium

Author: `CODEX_RAMSEY`

Independent reviews:
[`CODEX_EULER`](../feedback/CODEX_RAMSEY__SIGNED_INFLUENCE_BLOCK_GADGET_NOGO__BY_CODEX_EULER.md),
[`CODEX_CEDAR`](../feedback/CODEX_RAMSEY__SIGNED_INFLUENCE_BLOCK_GADGET_NOGO__BY_CODEX_CEDAR.md)

Whole-packet export gate:
[`CODEX_EULER`](../feedback/SIGNED_INFLUENCE_BLOCK_GADGET_NOGO__BY_CODEX_EULER__PACKET_GATE.md)

## Exact statement

Let `I` be a finite player set and let

```text
r : {nonempty S subset I} -> R^I
```

be a finite quitting-game reward table.  Extend each payoff coordinate to the
empty coalition by

```text
w_i(empty)=0,
w_i(S)=r(S)_i for nonempty S.
```

For distinct `i,j` and a coalition `S` containing neither player, define

```text
g_i(S)       =w_i(S union {i})-w_i(S),
d_(j->i)(S)  =g_i(S union {j})-g_i(S).             (1)
```

Assume that each ordered pair `j->i` has one fixed influence type:

```text
positive: d_(j->i)(S)>=0 for all S, and >0 for some S;
negative: d_(j->i)(S)<=0 for all S, and <0 for some S;
absent:   d_(j->i)(S)=0  for all S.                (2)
```

Give each nonabsent ordered pair a directed edge, signed `+1` in the positive
case and `-1` in the negative case.  Suppose the product of edge signs around
every directed simple cycle is `+1`.

Then there is a coalition `S_* subset I` such that

```text
w_i(S_* erase {i})<=w_i(S_*)       for i in S_*,
w_i(S_* union {i})<=w_i(S_*)       for i notin S_*. (3)
```

Thus `S_*` is an `IsQuittingSureExitSet`.  The pure stationary profile in
which precisely the members of `S_*` Quit is an exact terminal Nash profile
against every unilateral behavioral deviation, and its payoff is a uniform-
equilibrium payoff.

In particular, consider the architecture in
[`INCENTIVE_GADGET.md`](../questions/INCENTIVE_GADGET.md), with four clock
players divided into two distinct disjoint target pairs `A,B` and any finite
set of calibrators.  If the complete reward table satisfies (1)--(2) and the
positive-cycle condition, the pure profile above has

```text
min(targetMass(A),targetMass(B))=0.                 (4)
```

It is already an exact terminal Nash profile.  Consequently no reward-table
class satisfying these signed-influence hypotheses can force both target
masses to be at least any fixed `alpha>0` at every sufficiently accurate
terminal approximate Nash profile.  Equivalently, any viable fixed-sign
gadget with no pure sure-exit escape must contain a negative directed
influence cycle.

## Conjecture-facing change

`INCENTIVE_GADGET.md` accepts a negative answer that rules out a precisely
defined universal gadget architecture by constructing an exact stationary or
sure-exit escape for every table in the class.  The theorem does this for all
sign-consistent tables whose signed directed influence graph has no negative
directed cycle.  It includes every calibrator and every terminal coalition;
it is not a finite-watchdog or selected-deviation argument.

The result strictly extends the previously recorded global-polarity class.
Different strongly connected components may require mutually inconsistent
action switches.  Only the switch within each component is used, and the
components are frozen in condensation order.  The surviving fixed-sign
obligation is therefore narrowed to tables with a negative directed
influence cycle.  Tables whose influences change sign across coalition
backgrounds remain outside the theorem.

## Definitions and behavioral semantics

A behavioral strategy may use arbitrary private randomization after every
finite observed history.  Never is allowed.  The game terminates at the first
date with a nonempty Quit coalition, and the corresponding row of `r` is
paid; Never pays zero.

The number `g_i(S)` in (1) is player `i`'s payoff change when it joins the
terminal quitter coalition `S`.  The number `d_(j->i)(S)` records how adding
player `j` changes that membership gain.  Sign consistency is imposed on all
coalition backgrounds, not merely on coalitions reached by one candidate
profile.

A pure set root for `S_*` makes every member Quit surely at every live history
and every outsider Continue surely.  If `S_*` is nonempty, it absorbs at date
zero in the deterministic coalition `S_*`; if `S_*` is empty, it is Never.
The inequalities (3) are exactly the full behavioral Nash test for this root,
not only its one-stage normal-form test, by the checked sure-exit
characterization cited below.

For the two-pair clock notation, a strict-first target atom is the probability
that the first quitter coalition is exactly the specified pair, with the
other clock players and all calibrators Continuing at that row.  Under a pure
set root this mass is one exactly when `S_*` is that pair and is zero
otherwise.  Since `A` and `B` are distinct, (4) follows.

## Source correspondence and novelty

The semantic consumer is in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.  The exact declarations
are

```text
IsQuittingSureExitSet
isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet.
```

The equivalence quantifies over arbitrary unilateral behavioral strategies,
including randomized stopping and Never.  The last theorem turns the
constructed sure-exit set into a uniform-equilibrium payoff.

`UniformEquilibrium/Quitting/Stationary/TogglePotential.lean` consumes a
supplied ordinal potential; it does not construct a potential or a sure-exit
set from signed influences.  The conference result
`CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` proves strategic complements and
a single global action-polarity transform.  It explicitly identifies
blockwise monotonicity as an open extension.  The new ordinary mathematics is
the componentwise polarity construction and the condensation induction,
which work even when no single global polarity exists.

No literature theorem is invoked.  The quitting-game semantics and uniform
payoff are supplied only by the named checked declarations after the new
finite construction has produced `S_*`.

## Proof

### 1. Positive directed cycles balance every strongly connected component

Let `K` be a strongly connected component of the nonabsent influence graph.
Choose a root `r in K`.  For `i in K`, choose a directed path from `r` to `i`
and define `epsilon_i in {+1,-1}` to be the product of its edge signs.

This sign is independent of the chosen path.  Fix a directed return path from
`i` to `r` and append it to two candidate forward paths.  Each resulting
closed directed walk can be reduced by successively deleting directed simple
cycles.  Every deleted cycle has sign `+1`, so both closed walks have sign
`+1`.  Cancelling the common return-path sign shows that the two forward path
signs agree.

If an internal edge `j->i` has sign `sigma_(j->i)`, append it to a path from
`r` to `j`.  Path independence gives

```text
epsilon_i=epsilon_j sigma_(j->i),
epsilon_i epsilon_j sigma_(j->i)=1.                (5)
```

### 2. Switch actions inside one component

Put

```text
P_K={i in K: epsilon_i=-1}.
```

In transformed coordinates, action one means original Quit when
`epsilon_i=+1` and original Continue when `epsilon_i=-1`.  Thus a transformed
coalition `T subset K` represents the original internal coalition

```text
tau(T)=T symmetric_difference P_K.                 (6)
```

Fix an original outside coalition `E subset I setminus K`.  For transformed
`T` omitting `i`, define

```text
B_i(T)=E union (tau(T) erase {i}),
h_i(T)=epsilon_i g_i(B_i(T)).                       (7)
```

Here `h_i(T)` is exactly the payoff gain from changing transformed player `i`
from action zero to action one.

Let `T` omit distinct transformed players `i,j`.  If `epsilon_j=+1`, adding
transformed `j` inserts original `j`, and

```text
B_i(T union {j})=B_i(T) union {j},
h_i(T union {j})-h_i(T)
  =epsilon_i d_(j->i)(B_i(T)).                     (8+)
```

If `epsilon_j=-1`, adding transformed `j` removes original `j`, and

```text
B_i(T)=B_i(T union {j}) union {j},
h_i(T union {j})-h_i(T)
  =-epsilon_i d_(j->i)(B_i(T union {j})).           (8-)
```

Both cases can be written

```text
h_i(T union {j})-h_i(T)
  =epsilon_i epsilon_j d_(j->i)(S)                 (8)
```

at the displayed original background `S`, which omits `i,j`.  An absent edge
makes (8) zero.  For a nonabsent internal edge, sign consistency and (5) make
(8) nonnegative.  The transformed binary game within `K` therefore has
strategic complements against every fixed outside coalition.

### 3. Construct a pure equilibrium inside one component

Start with no transformed action-one players.  While some absent player has
strictly positive current transformed gain, add one such player.  The
cardinality grows, so the procedure terminates.

At termination, every absent player has nonpositive join gain.  A present
player was added when its action-one gain was positive.  Every subsequent
addition weakly increases that gain by (8), so its final action-one gain is
still positive.  It cannot profit by leaving.  The terminal transformed
coalition is therefore a pure Nash action for every player in `K`, against
the fixed outside actions.  Undoing (6) gives the corresponding original
actions.

### 4. Freeze components in condensation order

Order the strongly connected components `K_1,...,K_m` so every
intercomponent edge points from an earlier block to a later block.  Give
unsolved blocks arbitrary provisional actions.  Solve `K_1` by Step 3, then
solve `K_2`, and continue in order, always treating all outside actions as
fixed background.

No player in an unsolved later component influences a player in an already
solved earlier component: such an influence would be a backward condensation
edge.  By the absent clause of (2), absence means

```text
d_(j->i)(S)=0
```

for every background, so changing a later action leaves every earlier
membership gain exactly unchanged.  Earlier actions may affect a later block,
but they are fixed before that block is solved.  Induction therefore produces
one full original coalition `S_*` at which no player gains by toggling its
membership.

For a member, no profitable toggle is the first inequality in (3); for an
outsider it is the second.  Hence `S_*` is a sure-exit set.  The named checked
all-behavior characterization and uniform-payoff consumer finish the proof.

## Boundary tests

### Acyclic signed interactions need not admit one global polarity

Take three players.  Give an absent player payoff zero.  When player `i` is
present, give it payoff `g_i(S)` where `S` is the coalition of other present
players and

```text
g_1(S)=1,
g_2(S)=1-2 1_{1 in S},
g_3(S)=1+1_{1 in S}+1_{2 in S}.                    (9)
```

The only influence edges are

```text
1->2 negative,  1->3 positive,  2->3 positive.
```

The graph is acyclic, so the theorem applies.  The constructed coalition
`{1,3}` is a sure-exit set: its two member gains are positive and outsider
`2` has join gain `-1`.

A single global polarity would require

```text
epsilon_1 epsilon_2=-1,
epsilon_1 epsilon_3=+1,
epsilon_2 epsilon_3=+1.
```

Multiplying gives `1=-1`.  Thus this exact table is covered by the block
theorem but not by the earlier one-switch result.

### A negative directed cycle is a sharp pure boundary

Take three cyclically indexed players, give every absent player payoff zero,
and for `i` present set

```text
w_i(S)= 1  if succ(i) is absent,
       =-1  if succ(i) is present.                 (10)
```

The only influence edges are the three negative edges `succ(i)->i`; their
directed cycle has product `-1`.  A sure-exit coalition would have to satisfy

```text
i in S  iff  succ(i) notin S                       (11)
```

for every player.  This is impossible on an odd cycle.  Thus the positive-
cycle hypothesis cannot be removed from this pure sure-exit theorem.  This
does not claim that the table lacks a non-pure uniform payoff; the checked
three-player theorem solves it by another route.

## Adapter and consumer

The actual-data adapter is finite and constructive:

1. Compute every number `d_(j->i)(S)` from the complete terminal reward table.
2. Verify the trichotomy (2), form the signed directed graph, and check its
   directed simple cycles.
3. Compute its strongly connected components and a topological order of the
   condensation.
4. Within each component, compute the path signs `epsilon`, run the finite
   monotone-addition algorithm, and freeze the resulting actions.

The output is the literal coalition `S_*` satisfying (3).  It feeds directly
into `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`.  No
candidate clock law, finite deviation menu, continuation selection, or
unproved strategy-class completeness theorem is inserted between the actual
reward table and the checked semantic consumer.

## Lean handoff

A narrow formalization can define the ordered influence trichotomy and the
finite signed directed graph, then prove a component switching lemma and a
condensation induction.  The intended theorem shape is

```text
exists_sureExitSet_of_cycleBalancedSignConsistentInfluence
  (hsign : SignConsistentQuittingInfluence reward)
  (hcycle : EveryDirectedInfluenceCyclePositive hsign) :
  exists S, IsQuittingSureExitSet reward S.
```

Useful exact regression tests are (9), which must pass despite having no
global polarity, and (10), which must fail the cycle hypothesis and have no
sure-exit set.  Existing definitions such as `quittingSetReward`,
`quittingToggleCoalition`, and `IsQuittingSureExitSet` should be reused.  The
uniform payoff should be obtained afterward from the existing consumer, not
stored as a field of the new influence structure.

## Scope and nonclaims

The result is an impossibility theorem for one precisely defined universal
gadget architecture.  It does not construct the positive clock gadget, rule
out sign-changing influences, or solve a fixed-sign table containing a
negative directed cycle.  The negative-cycle boundary example is not a
counterexample to uniform-equilibrium existence.  The theorem does not claim
that arbitrary stationary profiles suffice: unrestricted behavioral control
enters only through the exact checked sure-exit characterization.
