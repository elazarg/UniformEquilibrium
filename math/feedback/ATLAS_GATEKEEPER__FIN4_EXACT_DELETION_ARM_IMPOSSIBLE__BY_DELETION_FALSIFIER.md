# Review of exact positive-gap player deletion on Fin4

Reviewer: DELETION_FALSIFIER

## Claim checked

The note claims that for a reward table on `Fin 4`, an owner, and a positive
number `gap`, the predicate

```text
HasQuittingExactPlayerDeletionAtGap reward owner gap
```

is impossible.  It then removes the exact-deletion disjunct from
`FinFourStrongConcentratedPacketConsumerResult`, leaving the static atomic
toggle handoff in the strategic branch and retaining the collision-minimum
residual unchanged.

## Verdict

**PASS.**  The argument is correct against the exact checked definitions, the
positivity boundary is sharp, and the proposed packet contraction preserves
the dependent source and packet data.  I found no generic checked declaration
already stating this exact contradiction.

There is a useful strengthening: the underlying theorem applies whenever the
deleted player type has cardinality at most three, not only when it has
cardinality exactly three.  The Fin4 statement is its immediate specialization.

## Declarations inspected

The audit used the following exact interfaces.

In
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/StaticStrategicOrientation.lean`:

* `HasQuittingExactPlayerDeletionAtGap` is exactly the conjunction of
  `Nonempty (QuittingDeletedPlayer owner)` and a
  `HasTerminalExploitabilityGap` for the literal deleted reward table.

In `UniformEquilibrium/Quitting/Classification/PlayerDeletion.lean`:

* `card_quittingDeletedPlayer_eq_three_of_card_eq_four` proves that deleting
  one player from a four-player type leaves cardinality three.

In `UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`:

* `quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three` produces a
  uniform-equilibrium payoff for every reward table on a type of cardinality
  three.

In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSmallSurvivorDeletion.lean`:

* `quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three` gives the
  stronger at-most-three-player form.

In `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`:

* `quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap`
  says that a strictly positive all-behavior terminal gap excludes every
  uniform-equilibrium payoff.

In
`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`:

* `FinFourStrongConcentratedPacketConsumerResult` has exactly the disjunction
  quoted in the note;
* `FinFourSingletonStageStrongConcentratedPacket.consumerResult` produces that
  result at the witness's `terminalGap`; and
* the weak-core and owner-compressed structures retain the actual produced
  packet together with that same result.

The nearby
`MinimalFinQuittingCounterexample.not_hasQuittingExactPlayerDeletionAtGap`
uses the same semantic contradiction but requires cardinality minimality.
`FourPlayerCyclicPlateauCandidate.no_exactPlayerDeletionAtPositiveGap` is
table-specific.  Neither subsumes the proposed generic Fin4 corollary.

## Independent proof check

Assume

```text
hdelete : HasQuittingExactPlayerDeletionAtGap reward owner gap
```

with `0 < gap`.  Its second field is

```text
HasTerminalExploitabilityGap
  (quittingDeletePlayerReward reward owner) gap.
```

For `reward` on `Fin 4`, the checked cardinality theorem gives

```text
Fintype.card (QuittingDeletedPlayer owner) = 3.
```

The three-player theorem therefore supplies

```text
exists payoff,
  (quittingGame (quittingDeletePlayerReward reward owner))
    .IsUniformEquilibriumPayoff none payoff.
```

But the positive gap on that identical deleted reward table implies the
negation of this existential.  The two conclusions contradict one another
directly.  No lifting of the deleted equilibrium to the four-player game is
used or needed.

The first field of `hdelete` is unused in the Fin4 proof.  This is harmless:
cardinality three already implies nonemptiness.  It is nevertheless correct
to preserve the generic predicate unchanged, since its explicit nonemptiness
is relevant away from this specialization.

## Strategy-class and quantifier audit

`HasTerminalExploitabilityGap` quantifies over every behavioral profile and
produces a complete unilateral behavioral strategy.  The three-player theorem
has the full uniform-horizon conclusion.  The contradiction theorem between
these notions is already checked.  Thus there is no hidden restriction to
stationary, pure-time, finite-support, or finite-horizon deviations.

The proof is entirely about the reduced game.  It does not assert that a
three-player equilibrium lifts to the ambient game and does not require any
claim about the deleted player's behavior or payoff.

## Boundary audit

Strict positivity is essential.  More sharply, on every nonempty player type,
every `gap <= 0` is a terminal exploitability gap: choose any player and use
that player's prescribed behavioral strategy as the deviation.  The payoff is
unchanged, so the required weak inequality follows from `gap <= 0`.

Consequently, on Fin4 the exact-deletion predicate is generally true at every
nonpositive gap, because the deleted type is nonempty.  The theorem cannot be
weakened from `0 < gap` to `0 <= gap`.

The cardinal boundary is also exact relative to the currently checked small
player theory.  Deleting one player from Fin5 leaves four players, so this
argument would require the unresolved Fin4 existence theorem.

## Stronger reusable theorem

The proof naturally factors through the checked at-most-three-player theorem:

```lean
theorem not_hasQuittingExactPlayerDeletionAtGap_of_card_le_three
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (owner : iota) {gap : Real} (hgap : 0 < gap)
    (hcard : Fintype.card (QuittingDeletedPlayer owner) <= 3) :
    not (HasQuittingExactPlayerDeletionAtGap reward owner gap) := by
  rintro <_, hdeletedGap>
  exact
    (quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
      (quittingDeletePlayerReward reward owner) hgap hdeletedGap)
      (quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three
        hcard (quittingDeletePlayerReward reward owner))
```

The angle brackets above are schematic Lean notation for the conjunction
pattern; the mathematical statement and proof are exact.  The Fin4 corollary
uses
`card_quittingDeletedPlayer_eq_three_of_card_eq_four owner (by decide)`.

This stronger declaration is preferable as the reusable semantic lemma, with
a short named Fin4 corollary for the atlas consumer.  Because the generic
static-orientation file currently has a deliberately small import boundary, a
small-cardinality specialization file or the Fin4 consumer file is a cleaner
placement than adding the full player-reindex dependency to the generic
predicate definition module.

## Packet contraction check

For the strong packet, `source.residual.witness.terminalGap_pos` supplies the
required strict positivity.  Case analysis on `strong.consumerResult` gives:

* strategic dispatch plus atomic handoff: retain it;
* strategic dispatch plus exact deletion: contradiction by the Fin4 theorem;
* collision-minimum residual: retain it verbatim.

Therefore the valid contracted conclusion is exactly

```text
(HasQuittingConcentratedSingletonStrategicDispatch ... /\
  HasQuittingStaticAtomicToggleHandoff reward)
or
Nonempty (QuittingConcentratedCollisionMinimumResidual ...).
```

For the weak-core and owner-compressed dependent structures, this
simplification can be exposed as projection theorems from the stored `result`.
No structure needs to be rebuilt, so the source, endpoint, packet, owner,
stage, scale, and chronology fields remain definitionally the same objects.

## Scope

This closes only the exact positive-gap deletion alternative.  It does not
consume the atomic-toggle handoff or the collision-minimum residual, and it
does not prove Fin4.  Within that scope, the note's conjecture-facing
contraction is complete and correctly stated.
