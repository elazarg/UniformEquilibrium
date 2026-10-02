# Exact positive-gap deletion to at most three survivors is impossible

## Status

**Complete ordinary mathematical proof; not yet packaged by a generic checked
declaration.** The sole source-attached strong concentrated-singleton atlas
node currently returns, in its static strategic branch,

```text
HasQuittingStaticAtomicToggleHandoff reward
  or
HasQuittingExactPlayerDeletionAtGap reward owner gap.
```

More generally, the deletion disjunct is impossible whenever the deleted
player type has cardinality at most three and `gap>0`. The checked
at-most-three-player uniform-equilibrium theorem contradicts the retained
positive terminal exploitability gap. For `reward` on `Fin 4`, deleting one
player leaves exactly three players, giving the atlas specialization.

Thus the strong node's strategic branch contracts to the atomic-toggle
handoff. No minimum-fiber, packet, or source provenance is needed beyond the
positive gap already carried by its terminal witness.

## Declarations inspected

In
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/StaticStrategicOrientation.lean`:

* `HasQuittingExactPlayerDeletionAtGap`;
* `HasQuittingStaticAtomicToggleHandoff`; and
* `HasQuittingSingletonStaticStrategicDispatch`.

In
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/StaticStrategicCompression.lean`:

* `QuittingTerminalExploitabilityWitness.singletonStaticStrategicDispatch_compress`;
  and
* `stoppingLawSingletonStrategicOrientation_compress`.

In `Research/Quitting/ConcentratedSingleton/Compression.lean`:

* `QuittingTerminalExploitabilityWitness.concentratedSingletonStrategicDispatch_compress`.

In `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`:

* `FinFourStrongConcentratedPacketConsumerResult`;
* `FinFourSingletonStageStrongConcentratedPacket.consumerResult`; and
* the dependent weak-core and owner-compressed consumption structures.

In the player-deletion and small-cardinality infrastructure:

* `QuittingDeletedPlayer` and `quittingDeletePlayerReward` in
  `UniformEquilibrium/Quitting/Classification/PlayerDeletion.lean` and
  `PlayerDeletionLift.lean`;
* `card_quittingDeletedPlayer_eq_three_of_card_eq_four` in
  `UniformEquilibrium/Quitting/Classification/PlayerDeletion.lean`;
* `quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three` in
  `UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`; and
* `quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSmallSurvivorDeletion.lean`;
  and
* `quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap`
  in
  `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

Two nearby proofs contain the same contradiction only under narrower
packaging:

* `MinimalFinQuittingCounterexample.not_hasQuittingExactPlayerDeletionAtGap`
  assumes a cardinality-minimal counterexample and works at arbitrary minimal
  cardinality; and
* `FourPlayerCyclicPlateauCandidate.no_exactPlayerDeletionAtPositiveGap`
  proves the Fin4 argument only for that example's local `Player` and reward
  table.

`FinFourDeletionNearCap.lean` uses the three-player theorem to build a lifted
near-cap profile, but does not state the generic impossibility of
`HasQuittingExactPlayerDeletionAtGap` on Fin4. I found no existing generic
declaration with the statement below.

## Exact general theorem

Let `iota` be a finite player type with decidable equality, let

```text
reward : {S : Finset iota // S.Nonempty} -> Payoff iota
owner : iota
gap : Real
```

and assume

```text
0 < gap
Fintype.card (QuittingDeletedPlayer owner) <= 3.
```

Then

```text
not_hasQuittingExactPlayerDeletionAtGap_of_card_le_three :
  not (HasQuittingExactPlayerDeletionAtGap reward owner gap).
```

The Fin4 statement below is an immediate corollary.

## Fin4 corollary

Let

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
owner : Fin 4
gap : Real
```

and assume `0 < gap`. Then

```text
not_hasQuittingExactPlayerDeletionAtGap_finFour :
  not (HasQuittingExactPlayerDeletionAtGap reward owner gap).
```

Equivalently, no deletion of one player from a four-player quitting game can
retain a positive all-behavior terminal exploitability gap.

## Proof

Suppose

```text
hdelete : HasQuittingExactPlayerDeletionAtGap reward owner gap.
```

Unfolding the definition gives

```text
hdelete.1 : Nonempty (QuittingDeletedPlayer owner)
hdelete.2 : HasTerminalExploitabilityGap
  (quittingDeletePlayerReward reward owner) gap.
```

By hypothesis the surviving player type has cardinality at most three.
Therefore

```text
quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three
```

produces a uniform-equilibrium payoff of the deleted game. On the other hand,
`gap>0` and `hdelete.2` imply, by
`quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap`,
that the deleted game has no uniform-equilibrium payoff. Contradiction.

For Fin4, the cardinal hypothesis follows from

```text
card_quittingDeletedPlayer_eq_three_of_card_eq_four owner (by decide).
```

This covers arbitrary behavioral deviations because both the definition of
`HasTerminalExploitabilityGap` and the at-most-three-player uniform-equilibrium
theorem use the full behavioral quitting-game semantics. There is no
stationarity or finite-horizon restriction.

## Strong-packet contraction

Let

```text
source : FinFourMinimumAtomProducer reward bound
strong : FinFourSingletonStageStrongConcentratedPacket ...
```

The checked `strong.consumerResult` returns

```text
(strategicDispatch /\
  (HasQuittingStaticAtomicToggleHandoff reward \/
   HasQuittingExactPlayerDeletionAtGap
     reward strong.singletonOwner source.residual.witness.terminalGap))
\/
collisionMinimumResidual.
```

The witness field supplies

```text
source.residual.witness.terminalGap_pos.
```

Applying the theorem above to the deletion disjunct leaves exactly

```text
(strategicDispatch /\ HasQuittingStaticAtomicToggleHandoff reward)
  \/
collisionMinimumResidual.
```

The same simplification applies to the dependent weak-core and
owner-compressed consumer structures without losing their exact source,
packet, endpoint, or chronology fields. Only an impossible static alternative
is removed.

## What kind of consumer this is

This is a complete contradiction consumer for the exact-deletion arm. It does
not turn deletion into a four-player terminal approximation or regenerated
minimum point; it proves that the arm cannot occur at the positive witness gap
in the first place.

The result is stronger than a cardinality-minimal-counterexample argument.
Every three-player quitting table has a uniform-equilibrium payoff, whether or
not the ambient Fin4 table is minimal among counterexamples. The positive-
minimum source provenance is therefore unnecessary for this arm.

## Boundary tests

### Positivity of the gap is essential

For every nonempty player type, every reward table, and every `gap <= 0`,
`HasTerminalExploitabilityGap reward gap` holds: use the player's prescribed
strategy itself as the unilateral deviation. Hence deletion at every
nonpositive gap is generally possible. The theorem must retain `0<gap`.

### Four players are the last cardinality covered by the present theorem

Deleting one player from a five-player game leaves four players. The four-
player conjecture is precisely unresolved, so the same argument cannot
eliminate positive-gap deletion in Fin5. This is a sharp cardinal boundary of
the currently checked small-player theorem.

### The deleted-player nonemptiness field is harmless but not the argument

`HasQuittingExactPlayerDeletionAtGap` includes
`Nonempty (QuittingDeletedPlayer owner)`. On Fin4 this is automatic, but the
contradiction uses the exact survivor cardinality three, not merely
nonemptiness.

## Conjecture-facing change

The strong concentrated-singleton atlas node is the sole remaining
source-attached node after the nonsingleton and monodromy contractions. Its
checked strategic compression still records exact player deletion as a live
arm. The theorem above removes that arm completely on Fin4:

\[
\boxed{
\text{strong concentrated singleton strategic branch}
\Longrightarrow
\text{static atomic-toggle handoff}.}
\]

What remains is the actual atomic-toggle handoff and the separate
`QuittingConcentratedCollisionMinimumResidual`. This result does not consume
either of those two outputs.

## Lean handoff

A reusable declaration belongs in a small-cardinality specialization file
importing `TerminalSemanticSmallSurvivorDeletion` and the static deletion
predicate:

```lean
theorem not_hasQuittingExactPlayerDeletionAtGap_of_card_le_three
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (owner : iota) {gap : Real} (hgap : 0 < gap)
    (hcard : Fintype.card (QuittingDeletedPlayer owner) <= 3) :
    not (HasQuittingExactPlayerDeletionAtGap reward owner gap) := by
  rintro ⟨_hdeletedNonempty, hdeletedGap⟩
  have hUE := quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three
    hcard (quittingDeletePlayerReward reward owner)
  exact
    (quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
      (quittingDeletePlayerReward reward owner) hgap hdeletedGap) hUE
```

The Fin4 corollary then belongs near
`StaticStrategicOrientation.lean` or in a small Fin4 specialization importing
`PlayerReindex` and `ExploitabilityGap`:

```lean
theorem not_hasQuittingExactPlayerDeletionAtGap_finFour
    (reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4))
    (owner : Fin 4) {gap : Real} (hgap : 0 < gap) :
    not (HasQuittingExactPlayerDeletionAtGap reward owner gap) := by
  rintro ⟨_hdeletedNonempty, hdeletedGap⟩
  have hcard : Fintype.card (QuittingDeletedPlayer owner) = 3 :=
    card_quittingDeletedPlayer_eq_three_of_card_eq_four owner (by decide)
  have hUE := quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three
    hcard (quittingDeletePlayerReward reward owner)
  exact
    (quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
      (quittingDeletePlayerReward reward owner) hgap hdeletedGap) hUE
```

Then add a source-preserving corollary in
`FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean` which rewrites
`FinFourStrongConcentratedPacketConsumerResult` to the two surviving outputs.
Do not change the generic deletion predicate: it remains meaningful for larger
player types.

## Scope and nonclaims

This result does not:

* prove the static atomic handoff has an executable chronology;
* consume the collision-minimum residual;
* prove Fin4 or any new result for Fin5;
* lift a three-player uniform equilibrium back to the ambient four-player
  game; or
* claim player deletion is harmless. It proves only that a positive terminal
  gap cannot survive in the deleted three-player table.
