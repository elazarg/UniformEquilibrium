# CODEX_RAMSEY — signed-influence block no-go for clock gadgets

Author: `CODEX_RAMSEY`

Status: `EXPORTED AFTER TWO INDEPENDENT FALSIFICATION PASSES AND A WHOLE-PACKET GATE; NO LEAN IMPLEMENTATION`

Independent reviews:
`feedback/CODEX_RAMSEY__SIGNED_INFLUENCE_BLOCK_GADGET_NOGO__BY_CODEX_EULER.md`
and
`feedback/CODEX_RAMSEY__SIGNED_INFLUENCE_BLOCK_GADGET_NOGO__BY_CODEX_CEDAR.md`.
The accepted packet is
`exports/SIGNED_INFLUENCE_BLOCK_GADGET_NOGO.md`; its separate gate is
`feedback/SIGNED_INFLUENCE_BLOCK_GADGET_NOGO__BY_CODEX_EULER__PACKET_GATE.md`.

## Exact question

Let `I` be a finite player set and extend a quitting reward table to the empty
coalition by

```text
w_i(empty)=0,
w_i(S)=r_i(S) for nonempty S.
```

For `i notin S`, define player `i`'s terminal membership gain

```text
g_i(S)=w_i(S union {i})-w_i(S).                     (1)
```

This note asks whether a broad blockwise strategic-complements architecture
can force the incompatible independent-clock outcomes in
`questions/INCENTIVE_GADGET.md`.  The answer is no.

## Signed influence architecture

For distinct players `j,i`, compare

```text
d_(j->i)(S)=g_i(S union {j})-g_i(S),                (2)
```

where `S` ranges over coalitions containing neither `i` nor `j`.  Call the
table **sign-consistent** if every ordered pair `j!=i` is exactly one of:

```text
positive: d_(j->i)(S)>=0 for every S, and >0 for some S;
negative: d_(j->i)(S)<=0 for every S, and <0 for some S;
absent:   d_(j->i)(S)=0  for every S.               (3)
```

The nonabsent pairs form a directed influence graph.  Label a positive edge
by `+1` and a negative edge by `-1`.  Call this graph **cycle-balanced** if
the product of edge labels around every directed simple cycle is `+1`.
(Equivalently every closed directed walk has positive product, by deleting
successive simple cycles.)

The definition covers every terminal coalition, every clock player, and every
calibrator.  It is an actual reward-table condition, not a supplied strategy
or a bounded deviation menu.

## Theorem: cycle-balanced signed blocks always have a sure exit

> **Signed-influence block theorem.**  Every finite sign-consistent quitting
> table with cycle-balanced directed influence graph has a coalition `S_*`
> satisfying `IsQuittingSureExitSet reward S_*`.  Consequently it has an
> ordinary uniform-equilibrium payoff against unrestricted behavioral
> deviations.

### 1. Balance inside one strongly connected block

Let `K` be a strongly connected component of the influence graph.  There are
signs `epsilon_i in {+1,-1}` for `i in K` such that every internal edge
`j->i` of sign `sigma_(j->i)` satisfies

```text
epsilon_i*epsilon_j*sigma_(j->i)=+1.               (4)
```

To see this, choose `r in K`.  For each `i`, choose a directed path from `r`
to `i` and let `epsilon_i` be the product of its edge signs.  This is path
independent.  Indeed, append one fixed directed path from `i` back to `r` to
either of two paths from `r` to `i`.  The resulting closed directed walks
decompose into directed cycles, each of positive sign, so the two forward
path products agree.  Appending an internal edge `j->i` to a path ending at
`j` now gives (4).

Put

```text
P_K={i in K: epsilon_i=-1}.
```

Use transformed action one for original Quit when `epsilon_i=+1`, and for
original Continue when `epsilon_i=-1`.  Equivalently, a transformed coalition
`T subset K` represents the original internal coalition

```text
tau(T)=T symmetric_difference P_K.                 (5)
```

Fix an original outside coalition `E subset I setminus K`, and let `h_i(T)`
be the payoff gain when transformed player `i` changes from action zero to
action one.  More explicitly, for a transformed coalition `T` omitting `i`,
put

```text
B_i(T)=E union (tau(T) erase {i}).
```

Switching player `i` from transformed zero to transformed one changes its
original action in the direction `epsilon_i`, and therefore

```text
h_i(T)=epsilon_i*g_i(B_i(T)).
```

Now let `T` omit distinct transformed players `i,j`.  There are two cases.
If `epsilon_j=+1`, then

```text
B_i(T union {j})=B_i(T) union {j},
h_i(T union {j})-h_i(T)
  =epsilon_i*d_(j->i)(B_i(T)).
```

If `epsilon_j=-1`, transformed addition removes original player `j`, so

```text
B_i(T)=B_i(T union {j}) union {j},
h_i(T union {j})-h_i(T)
  =-epsilon_i*d_(j->i)(B_i(T union {j})).
```

Thus in either case, at the displayed background `S` containing neither
`i` nor `j`,

```text
h_i(T union {j})-h_i(T)
  =epsilon_i*epsilon_j*d_(j->i)(S)                 (6)
```

If `j->i` is absent, the right side is zero.  Otherwise (3)--(4) make it
nonnegative.  Thus the transformed binary game on one strongly connected
block has strategic complements: every transformed own-action gain is
nondecreasing in every other transformed action.

### 2. Solve one block

For completeness, the needed complements argument is finite.  Start with no
transformed action-one players.  While some absent player has strictly
positive transformed gain, add one such player.  Cardinality increases, so
the algorithm stops.

At termination every absent player has gain at most zero.  A present player
was added at a background where its gain was positive; all subsequent moves
only added transformed actions, so monotonicity keeps its final leave-reversed
gain positive.  Hence no player in the block can profit by toggling its
transformed action.  Reversing (5), no player in the block can profit by
toggling original Quit/Continue membership.

### 3. Solve the condensation in topological order

Order the strongly connected components `K_1,...,K_m` so every intercomponent
edge points from an earlier block to a later block.  Give every still-unsolved
block an arbitrary provisional action, and solve `K_1` by the previous step.
Having fixed `K_1,...,K_(q-1)`, solve `K_q` with all outside actions as
background.

No unsolved later player influences a player in `K_q`: such a nonconstant
dependence would be an edge from a later component into `K_q`, contrary to
the topological order.  By the absent case of (3), later actions therefore
leave every `K_q` gain exactly unchanged.  Conversely, fixing a later block
cannot disturb the best-response inequalities already established in an
earlier block.  Induction produces a full coalition `S_*` at which no player
has a profitable membership toggle.

Unpacking (1), for members and outsiders respectively,

```text
w_i(S_* erase {i})<=w_i(S_*)       (i in S_*),
w_i(S_* union {i})<=w_i(S_*)       (i notin S_*).   (7)
```

These are exactly `IsQuittingSureExitSet reward S_*`, including the empty and
singleton boundary conventions.  The checked theorem

```text
isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
```

in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean` gives the claimed
uniform payoff.  Its underlying exact characterization
`isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet` already quantifies
over every unilateral behavioral deviation.  Thus the argument does not stop
at the finite membership game.

## Consequence for the two-pair clock gadget

At the exact pure profile generated by `S_*`, either `S_*` is empty and play
Never absorbs, or the same deterministic coalition exits at date zero.  The
strict-first target atom for `A` has mass one exactly when the date-zero
quitter coalition is `A` (with every clock outsider and calibrator
Continuing), and otherwise has mass zero; the same statement holds for `B`.
Since `A` and `B` are distinct and disjoint, at most one target atom can have
positive mass.  In the notation of the maintained question,

```text
min(a,b)=0.                                           (8)
```

The profile has zero terminal exploitability against unrestricted behavioral
deviations.  Hence no sign-consistent, cycle-balanced reward gadget can force
`a,b>=alpha>0` at every sufficiently accurate terminal approximate Nash
profile.  Extra calibrators do not help because they are vertices of the same
influence graph and are included in (3)--(7).

The checked square-root clock ledger remains exact, but this architecture
escapes before its positive-mass rigidity branch: (8) violates the producer
hypothesis itself.  Therefore any viable fixed-sign nonlocal gadget must carry
a **negative directed influence cycle**.  If it has no such cycle, the theorem
constructs the exact equilibrium escape.

## Boundary tests

### Strict extension beyond one global polarity

Take three players and define absent-player payoff to be zero.  For a terminal
coalition `T` containing `i`, set `w_i(T)=g_i(T erase {i})`, where

```text
g_1(S)=1,
g_2(S)=1-2*1_{1 in S},
g_3(S)=1+1_{1 in S}+1_{2 in S}.                    (9)
```

The only influence edges are

```text
1->2 negative,  1->3 positive,  2->3 positive.
```

The graph is acyclic, so the theorem applies and the topological construction
returns `S_*={1,3}`.  Directly, players 1 and 3 have positive stay gains and
outsider 2 has join gain `-1`.

This table is not covered by one global action-polarity transform.  Such a
transform would require signs satisfying

```text
epsilon_1*epsilon_2=-1,
epsilon_1*epsilon_3=+1,
epsilon_2*epsilon_3=+1,
```

whose product is impossible.  Thus the block theorem strictly extends the
global polarity-complementary class recorded in
`notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`.

### A negative directed cycle is a real boundary

Take three cyclically indexed players.  Again give every absent player payoff
zero, and for `i in S` put

```text
w_i(S)= 1  if succ(i) notin S,
       =-1  if succ(i) in S.                        (10)
```

Then `g_i(T)` has the same displayed value.  The only influence edges are the
three negative edges `succ(i)->i`, whose directed cycle has sign `-1`.

A sure-exit coalition would have to satisfy

```text
i in S  iff  succ(i) notin S                        (11)
```

for all three players: the forward direction is the member no-leave
inequality and the reverse direction is the outsider no-join inequality.
Condition (11) is impossible on an odd cycle.  Hence the cycle-balance
hypothesis cannot simply be deleted.  This table is only a boundary test for
the pure producer; the separate checked three-player theorem gives it a
uniform payoff by another route.

## Source and novelty audit

The local source search inspected:

- `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`;
- `UniformEquilibrium/Quitting/Stationary/TogglePotential.lean`;
- `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`; and
- `notes/CODEX_CEDAR__TWO_PAIR_CLOCK_RIGIDITY_COMPILER.md`.

The checked Lean source consumes a supplied ordinal potential or a supplied
sure-exit set.  It does not construct either from a signed influence graph.
The Gauss note proves global strategic complements and one global
action-polarity transform, then explicitly leaves block monotonicity as the
next conjectural extension.  The theorem here closes that block extension
under the exact sign-consistency and no-negative-directed-cycle hypotheses.
No literature theorem is invoked.

This is a universal architecture-level impossibility, not a reward-table
counterexample and not a proof for reward tables with sign-changing
influences or a negative directed influence cycle.  It does not constrain
the actual clock law outside the constructed sure-exit equilibrium.  Its
conjecture-facing content is the necessary structural condition:

```text
fixed-sign gadget with no exact equilibrium escape
  -> some directed influence cycle has negative sign. (12)
```

## Lean handoff

A formalization can define the trichotomy (3) on ordered pairs, use a finite
strongly-connected-component/topological-order library, and prove the block
sign-switching lemma (4).  Within one component, the existing
`quittingSetReward`, `quittingToggleCoalition`, and
`IsQuittingSureExitSet` definitions are the intended semantic objects.  The
narrow theorem shape is:

```text
exists_sureExitSet_of_cycleBalancedSignConsistentInfluence
  (hsign : SignConsistentQuittingInfluence reward)
  (hcycle : EveryDirectedInfluenceCyclePositive hsign) :
  exists S, IsQuittingSureExitSet reward S.
```

The existing sure-exit consumer should be applied after constructing `S`;
the desired uniform payoff must not be stored in the influence structure.
