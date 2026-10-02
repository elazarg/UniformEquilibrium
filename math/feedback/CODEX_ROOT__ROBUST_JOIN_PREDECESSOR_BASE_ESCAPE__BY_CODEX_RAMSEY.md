# Source, novelty, and Lean-handoff audit of `CODEX_ROOT__ROBUST_JOIN_PREDECESSOR_BASE_ESCAPE`

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS as a strict adapter/corollary; export-qualified after an
ordinary whole-packet gate.**  The robust-predecessor theorem is not a new
equilibrium mechanism: it produces exactly the hypothesis of the already
checked persistent-base arbitrary-completion compiler.  I found no existing
declaration for this finite graph-to-base adapter, and the Fin4 strict
background reversal is genuinely stronger than the reviewed weak
cancellation theorem.

I derived the result independently from the definitions before comparing the
author's proof.  No mathematical repair is required.  The novelty and Lean
handoff should retain the narrow calibration below.

## 1. Exact claim checked

For distinct players `e,j`, write `e robustly joins j` when for every
background disjoint from `{e,j}`,

```text
r_j(T union {e}) <= r_j(T union {e,j}).
```

If a finite base `C` has cardinality at least two and every `j in C` has a
distinct robust predecessor `e in C`, the note claims:

1. `QuittingPersistentBaseComplementLeaveSafe reward C`;
2. an exact stationary terminal Nash profile against unrestricted behavioral
   deviations; and
3. a uniform-equilibrium payoff.

It then specializes this to a directed robust-join cycle, proves strict
background reversal on every selected Fin4 terminal-gap collision-map cycle
under no uniform payoff, and derives the unconditional Fin4 existence class
from the no-strict-reversal table condition `(6.1)`.

All four claims pass.

## 2. The adapter is exact

Fix `j in C`, choose its robust predecessor `e in C`, and let
`Q subset univ \ C`.  The background

```text
T = (C \ {e,j}) union Q
```

is disjoint from `{e,j}`.  The two robust-join coalitions are literally

```text
T union {e,j} = C union Q,
T union {e}   = (C erase j) union Q.
```

The second coalition is nonempty because `e in C`, `e != j`.  Thus the
robust inequality is exactly

```text
quittingSetReward reward (C.erase j union Q) j <=
  quittingSetReward reward (C union Q) j,
```

which is the `j,Q` instance of
`QuittingPersistentBaseComplementLeaveSafe reward C`.  There is no missing
outsider sign: the checked compiler takes `free = univ \ C`, so every player
outside the base is solved inside the induced finite Boolean game.

The cardinality-two boundary is exact.  If one base member deviates, the
other still Quits surely at date zero.  Therefore the checked
`QuittingPersistentBaseCertificate.isZeroAsymptoticNash` conclusion really
covers arbitrary history-dependent randomized deviations, not only
stationary or pure deviations.

## 3. Exact checked consumer and source paths

The central file is

```text
UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/
  PersistentBaseArbitraryCompletionEscape.lean
```

The exact declarations used are:

- `QuittingPersistentBaseComplementLeaveSafe`;
- `exists_quittingPersistentBaseCertificate_of_complementLeaveSafe`;
- `QuittingPersistentBaseCertificate.isZeroAsymptoticNash`; and
- `exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe`.

The last theorem already selects an induced-game mixed Nash point and returns
both exact all-behavior terminal Nash and a uniform-equilibrium payoff.  The
new result adds no strategy construction beyond this theorem.

For Fin4, the no-uniform branch is exactly
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff` in

```text
Diagnostics/Quitting/Collision/SingletonPacket/
  FullSupportProjectiveQBarResidual.lean
```

and the fixed-point-free positive collision selector is
`FinFourQuantitativeFullSupportHardResidual.
exists_fixedPointFree_terminalGap_collisionMap` in

```text
Diagnostics/Quitting/Collision/SingletonPacket/
  PunishmentNormalAtomicCollisionHandoff.lean.
```

For a theorem with no supplied numeric bound, instantiate the former with
`quittingRewardBound reward` and discharge its bound premise using
`abs_reward_le_quittingRewardBound`.  This small bridge should be explicit in
the Lean handoff.

## 4. Directed cycle and strict Fin4 reversal

A simple directed cycle supplies a distinct predecessor for every vertex, so
its vertex set is a robust predecessor base.  Hence a no-uniform-payoff game
cannot contain such a cycle.  Since the relation is irreflexive by definition,
the equivalent finite directed graph is acyclic; the topological-order
corollary is standard but not needed for the main formalization.

Now fix any simple cycle of a Fin4 collision map.  Every selected edge has
empty-background increment at least `gamma>0`.  If every background increment
on every cycle edge were nonnegative, every edge would be robust and the
cycle base would compile to a uniform payoff.  Thus some edge and background
have strictly negative increment.  The background cannot be empty because of
the positive singleton collision.  In Fin4 it contains one or both remaining
labels, giving exactly pair-to-triple or triple-to-grand reversal.

The strict sign is correct: the robust predicate is weak (`0 <= increment`),
so its negation is strict (`increment < 0`).  This is a genuine strengthening
of `FIN4_COLLISION_CYCLE_FACE_SIGN_CANCELLATION`, whose contradiction assumed
strict positivity on every background and therefore obtained only a weak
nonpositive corner.

The unconditional theorem `(6.1)` also passes.  Under a hypothetical lack of
uniform payoff, every selected collision-map edge has positive singleton
increment, so `(6.1)` makes it robust.  A fixed-point-free map on `Fin 4` has
a directed cycle, which the main adapter consumes.  No residual hypothesis is
left in the statement.

## 5. Novelty and overlap

The correct classification is:

```text
new finite-table/graph adapter
  + checked persistent-base arbitrary-completion compiler
  + checked Fin4 collision selector
= new strict corollary and new sufficient table class.
```

It is not duplicate as an exact theorem: a narrow search found no declaration
turning robust predecessors or a robust player-cycle into
`QuittingPersistentBaseComplementLeaveSafe`.  It is also not subsumed by the
existing static strict-toggle orbit: that orbit lives on coalition vertices
and explicitly lacks a semantic compiler.  Solo-preemption cycles concern
singleton payoff comparisons, not background-uniform membership joins.

It is, however, misleading to describe the examples or theorem as outside
known equilibrium branches merely because there is no pure sure-exit
coalition.  The complementary players may mix, and that mixed completion is
precisely the already checked persistent-base arbitrary-completion branch.
The author's Sections 7.5 and 8 state this correctly.  Any earlier intake
claim that random examples satisfying the robust-cycle condition lie outside
known branches should be removed, unless “known branch” is explicitly limited
to pure sure-exit profiles.  Random testing also does not certify absence of
the other checked branches.

Thus novelty should be advertised as a robust-join graph criterion and strict
Fin4 sign screen, not as a new all-behavior equilibrium mechanism.

## 6. Narrowest Lean handoff

The smallest useful implementation needs only:

1. `QuittingRobustJoin reward enforcer joiner`;
2. `QuittingRobustPredecessorBase reward base`;
3. `QuittingRobustPredecessorBase.complementLeaveSafe`; and
4. `exists_exactTerminalNash_and_uniformPayoff_of_robustPredecessorBase`, a
   one-line call to the checked compiler.

These belong beside `PersistentBaseArbitraryCompletionEscape.lean` and need
no new strategy, cap, Bellman, or stopping-law import.

For the graph layer, prefer a supplied finite-cycle wrapper or use
`Math.FiniteSerialRelation.nonempty_periodicCycle_of_serial` from
`MathUE/FiniteSerialRelation.lean`.  A periodic-cycle vertex range is enough;
one does not need a new simple-cycle data structure or a topological-sort API.
Irreflexivity gives at least two distinct vertices, and periodicity supplies a
predecessor in the range for every vertex.  If bookkeeping over a possibly
nonminimal period becomes longer than the theorem, a supplied simple cycle is
the better public interface.

The Fin4 declarations can then be kept to:

- a collision-map-cycle strict-background-reversal theorem; and
- `finFour_exists_uniformPayoff_of_noStrictBackgroundReversal`, with the
  canonical reward-bound bridge made explicit.

The first can live beside `PunishmentNormalAtomicCollisionHandoff.lean`; the
second may import that file, `FullSupportProjectiveQBarResidual.lean`, the
robust-base adapter, and `MathUE.FiniteSerialRelation`.  There is no reason to
import the much larger strict coalition-toggle cycle stack or the sure-exit
strategy compiler.

## 7. Export assessment

The result merits a narrow export as an adapter/corollary packet because it:

- has finite, checkable reward-table hypotheses;
- reaches an already checked unrestricted-deviation consumer;
- gives a genuinely strict Fin4 reversal and an unconditional Fin4 existence
  subclass; and
- has exact, small Lean targets.

An export packet should explicitly name the checked persistent-base theorem,
state that this is not a new equilibrium mechanism, include the cardinality
two and empty-complement boundaries, and distinguish its strict reversal from
the earlier weak cancellation theorem.  It should not claim that numerical or
random examples evade existing architectures.

