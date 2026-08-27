# Exact positive-gap deletion to at most three survivors is impossible

Author: `ATLAS_GATEKEEPER`

Independent review:
[adversarial source and boundary audit](../feedback/ATLAS_GATEKEEPER__FIN4_EXACT_DELETION_ARM_IMPOSSIBLE__BY_DELETION_FALSIFIER.md)

## Exact statement

Let `I` be a finite player type with decidable equality, let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting-game reward table, fix a player `o in I`, and let
`gamma>0`. Write

\[
I_{-o}:=\{i\in I:i\ne o\}
\]

and let `r_{-o}` be the literal reward table obtained by restricting every
nonempty quitting coalition and every payoff coordinate to `I_{-o}`.

Assume

\[
|I_{-o}|\le3.
\tag{1}
\]

Then the deleted game cannot retain terminal exploitability gap `gamma`:

\[
\boxed{
\neg\operatorname{HasTerminalExploitabilityGap}(r_{-o},\gamma).}
\tag{2}
\]

Equivalently, under (1) and `gamma>0`,

```text
not (HasQuittingExactPlayerDeletionAtGap r o gamma).
```

In particular, for every reward table on `Fin 4`, every owner `o : Fin 4`,
and every `gamma>0`,

```text
not_hasQuittingExactPlayerDeletionAtGap_finFour :
  not (HasQuittingExactPlayerDeletionAtGap r o gamma).
```

### Fin4 strong-packet corollary

Let

```text
source : FinFourMinimumAtomProducer reward bound
strong : FinFourSingletonStageStrongConcentratedPacket
  reward sourceProfile sourceTerminal stage resolution.
```

The checked concentrated-singleton consumer can be strengthened from

```text
(strategicDispatch /\ (staticAtomicHandoff \/ exactPlayerDeletion))
  \/ collisionMinimumResidual
```

to

```text
(strategicDispatch /\ staticAtomicHandoff)
  \/ collisionMinimumResidual.
```

Here every object in the output is the same object contained in
`strong.consumerResult`; no source, packet, endpoint, owner, terminal, stage,
scale, or chronology is reselected.

## Conjecture-facing change

This strictly narrows the live obligation in
[`FIN4_ATLAS_CONCENTRATED_SINGLETON.md`](../questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md).
That question's checked exhaustive downstream split still lists exact player
deletion as one possible output of the sole source-attached strong
concentrated-singleton node. The theorem proves that this output is empty at
the witness's positive gap.

Thus the strategic half of the remaining node has only the static atomic
handoff:

\[
\boxed{
\text{Fin4 strong concentrated strategic branch}
\Longrightarrow
\text{static atomic-toggle handoff}.}
\tag{3}
\]

The separate collision-minimum residual is retained unchanged. Neither it nor
the atomic handoff is consumed here.

## Definitions and assumptions

`HasTerminalExploitabilityGap r gamma` means that for every behavioral
profile `sigma` there are a player `i` and an arbitrary behavioral strategy
`tau_i` such that

\[
U_i(\sigma)+\gamma
\le U_i(\sigma[i\leftarrow\tau_i]).
\tag{4}
\]

The deviation may be history-dependent, may Quit arbitrarily late, and may be
Never. No stationary, finite-horizon, pure-time, or finite-support restriction
is imposed.

`HasQuittingExactPlayerDeletionAtGap r o gamma` is exactly the conjunction

```text
Nonempty (QuittingDeletedPlayer o)
```

and

```text
HasTerminalExploitabilityGap
  (quittingDeletePlayerReward r o) gamma.
```

The word "exact" refers to preservation of the entire numerical gap in the
literal deleted table. It does not assert that an equilibrium of the deleted
game lifts to the ambient game.

## Source correspondence

The exact checked interfaces are:

* `HasQuittingExactPlayerDeletionAtGap` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/StaticStrategicOrientation.lean`;
* `QuittingDeletedPlayer`, `quittingDeletePlayerReward`, and
  `card_quittingDeletedPlayer_eq_three_of_card_eq_four` in
  `UniformEquilibrium/Quitting/Classification/PlayerDeletion.lean` and
  `PlayerDeletionLift.lean`;
* `quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSmallSurvivorDeletion.lean`;
* `quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap`
  in
  `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
* `QuittingTerminalExploitabilityWitness.concentratedSingletonStrategicDispatch_compress`
  in `Research/Quitting/ConcentratedSingleton/Compression.lean`; and
* `FinFourStrongConcentratedPacketConsumerResult` and
  `FinFourSingletonStageStrongConcentratedPacket.consumerResult` in
  `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`.

Nearby checked results do not duplicate the general statement:

* `MinimalFinQuittingCounterexample.not_hasQuittingExactPlayerDeletionAtGap`
  assumes cardinality minimality;
* `FourPlayerCyclicPlateauCandidate.no_exactPlayerDeletionAtPositiveGap` is
  specialized to one example's player type and reward table; and
* `FinFourDeletionNearCap.lean` uses small-player existence to construct a
  lifted near-cap profile but does not eliminate the static exact-deletion
  predicate.

The new mathematical content is the reusable at-most-three-survivor
contradiction and its exact composition with the maintained Fin4 packet
result.

## Proof

Assume for contradiction that

\[
\operatorname{HasQuittingExactPlayerDeletionAtGap}(r,o,\gamma)
\]

holds. Its second conjunct is

\[
\operatorname{HasTerminalExploitabilityGap}(r_{-o},\gamma).
\tag{5}
\]

By (1), the checked unconditional small-player theorem produces some payoff
`v` which is a uniform-equilibrium payoff of the deleted game:

\[
\exists v\in\mathbb R^{I_{-o}},\qquad
v\text{ is a uniform-equilibrium payoff of }r_{-o}.
\tag{6}
\]

But the checked terminal-gap contradiction theorem applied to `gamma>0` and
(5) says that no such payoff exists. This contradicts (6), proving (2).

For `I=Fin 4`, deleting `o` leaves exactly three players by
`card_quittingDeletedPlayer_eq_three_of_card_eq_four`; hence (1) holds.

For the strong-packet corollary, case-split the checked
`strong.consumerResult`.

* Retain the strategic-dispatch/static-atomic-handoff case literally.
* The strategic-dispatch/exact-deletion case contradicts the Fin4 theorem,
  using `source.residual.witness.terminalGap_pos`.
* Retain the collision-minimum case literally.

This yields (3) without reconstructing any dependent data.

## Probability and strategy audit

The proof takes place entirely in the literal deleted quitting game. The
small-player theorem has the full uniform-horizon conclusion, and the gap
certificate quantifies over every behavioral profile and arbitrary unilateral
behavioral deviations. Their checked incompatibility is exactly the theorem
used above.

No deleted-game strategy is lifted to the ambient game. The deleted player's
payoff and deviations play no role. No terminal-law mass, cap coordinate,
stationary best response, or semantic carrier point is substituted for an
actual behavioral object.

## Boundary tests

### The positive-gap hypothesis is sharp

Let the player type be nonempty and `gamma<=0`. Against any behavioral profile
`sigma`, choose any player `i` and use its prescribed strategy `sigma_i` as
the deviation. The updated profile is `sigma`, so

\[
U_i(\sigma)+\gamma\le U_i(\sigma).
\]

Thus every reward table on a nonempty player type has terminal exploitability
gap `gamma` for every `gamma<=0`. In Fin4 the deleted type is nonempty, so
`HasQuittingExactPlayerDeletionAtGap` is generally true at all nonpositive
gaps. Replacing `gamma>0` by `gamma>=0` would be false.

### The cardinal boundary is exact for the checked small-player input

Deleting one player from Fin5 leaves four players. The unconditional
four-player uniform-equilibrium theorem is the open conjecture under study,
so this proof gives no Fin5 deletion no-go. This is a boundary of the proof,
not a claim that positive-gap deletion actually occurs with four survivors.

### Nonemptiness is not silently inferred

The general predicate explicitly contains
`Nonempty (QuittingDeletedPlayer o)`. The at-most-three-player UE theorem also
handles the empty type, but the proof does not delete or weaken that predicate
field. In the Fin4 corollary the survivor type is automatically nonempty.

## Adapter and consumer

The arbitrary-data adapter is the checked
`FinFourSingletonStageStrongConcentratedPacket.consumerResult`: every
source-attached strong packet enters the displayed strategic/deletion versus
collision split at the retained witness gap.

The consumer is the theorem proved here. It sends the deletion branch to
contradiction using the checked small-player UE theorem, while retaining the
other two branches on their exact original data. Consequently it is a strict
contraction of a named exhaustive Fin4 node, rather than a standalone static
screen.

## Lean handoff

First add the reusable lemma in a small-cardinality specialization importing
`TerminalSemanticSmallSurvivorDeletion` and
`StaticStrategicOrientation`:

```lean
theorem not_hasQuittingExactPlayerDeletionAtGap_of_card_le_three
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (owner : iota) {gap : Real} (hgap : 0 < gap)
    (hcard : Fintype.card (QuittingDeletedPlayer owner) <= 3) :
    not (HasQuittingExactPlayerDeletionAtGap reward owner gap) := by
  rintro ⟨_hdeletedNonempty, hdeletedGap⟩
  exact
    (quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
      (quittingDeletePlayerReward reward owner) hgap hdeletedGap)
      (quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three
        hcard (quittingDeletePlayerReward reward owner))
```

Add the Fin4 corollary using

```lean
card_quittingDeletedPlayer_eq_three_of_card_eq_four owner (by decide)
```

and a contracted result predicate in
`FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`, for example

```text
(HasQuittingConcentratedSingletonStrategicDispatch ... /\
  HasQuittingStaticAtomicToggleHandoff reward)
or
Nonempty (QuittingConcentratedCollisionMinimumResidual ...).
```

The proof should destruct `strong.consumerResult`, eliminate only the deletion
case, and retain the existing witnesses definitionally. Add projection
theorems for the weak-core and owner-compressed dependent consumption
structures rather than rebuilding those structures.

Do not place the small-cardinality import into the generic orientation file if
that would enlarge its intended dependency boundary; a focused specialization
is sufficient.

## Scope and nonclaims

This result does not:

* consume `HasQuittingStaticAtomicToggleHandoff`;
* consume `QuittingConcentratedCollisionMinimumResidual`;
* produce terminal approximants, cumulative recurrence, or a regenerated
  minimum source;
* prove Fin4 or extend the argument to Fin5;
* lift a deleted-game equilibrium to the ambient game; or
* say that player deletion is strategically harmless. It says only that a
  strictly positive universal terminal exploitability gap cannot survive in a
  deleted game with at most three players.

## Formalization record

The checked realization keeps the small-game contradiction separate from the
generic static-orientation definition and specializes it through a narrow
production module.

1. `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSmallSurvivorDeletion.lean`
   proves `not_hasTerminalExploitabilityGap_of_card_le_three`.  It combines
   `quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three` with
   `quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap`
   entirely inside the supplied small reward table.  The underlying
   cardinality theorem handles cardinality zero explicitly through
   `QuittingTerminalExploitabilityWitness.elim_isEmpty`.
2. `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/ExactPlayerDeletionSmallSurvivorNoGo.lean`
   proves
   `not_hasQuittingExactPlayerDeletionAtGap_of_deleted_card_le_three`,
   `not_hasQuittingExactPlayerDeletionAtGap_of_card_le_four`, and
   `not_hasQuittingExactPlayerDeletionAtGap_finFour`.  The first theorem
   consumes the exact literal deleted reward and gap stored by
   `HasQuittingExactPlayerDeletionAtGap`; the second uses only
   `card_quittingDeletedPlayer_lt`; the third specializes the ambient bound to
   `Fin 4`.
3. The focused no-go module and the cardinality module are reachable through
   `UniformEquilibrium/Diagnostics/Quitting/All.lean`.  The existing
   action-normal declarations in
   `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`
   retain the old atomic-or-deletion result type as a compatibility surface,
   while the universal atomic handoff supplies its live strategic output.
   The deletion theorem independently makes every exact positive-gap Fin4
   deletion certificate contradictory; no heavier small-cardinality import is
   added to the generic orientation module.

Evidence seals:

- **M:** PASS.  Positive terminal exploitability contradicts the unconditional
  uniform-payoff theorem on every player type of cardinality at most three,
  including the empty type.  Strict deleted-card decrease gives the ambient
  `card <= 4` and Fin4 corollaries exactly.
- **L:** PASS.  The generic small-game no-gap theorem and all three deletion
  specializations check in Lean.  At promotion, direct and named builds of the
  deletion and action-normal modules completed successfully; targeted axiom
  prints use only `propext`, `Classical.choice`, and `Quot.sound`.
- **A:** PASS.  Any actual
  `HasQuittingExactPlayerDeletionAtGap reward owner gap` exposes precisely the
  `quittingDeletePlayerReward reward owner` gap consumed by the theorem.  The
  Fin4 application uses the same reward, owner, and positive witness gap; no
  survivor table, gap, packet, or source is reselected.
- **C:** PASS for elimination of the exact-deletion certificate.  The no-go
  consumes that certificate directly to `False`.  Together with the checked
  action normal form it removes deletion as a live Fin4 alternative, but this
  seal does not consume the remaining atomic handoff or collision-minimum
  residual.

Nonclaims:

- no equilibrium or behavioral strategy of the deleted game is lifted to the
  ambient game, and deletion is not asserted strategically harmless;
- the theorem is false without strict positivity of the gap and no such
  extension is claimed;
- no Fin5 deletion conclusion follows, because four-survivor existence is the
  open boundary;
- the atomic-toggle handoff and collision-minimum residual remain unconsumed;
- no source regeneration, return, recurrence, descent, or completion closure
  is produced; and
- no new uniform-equilibrium payoff for the ambient Fin4 game is obtained.

The mathematical provenance remains this packet and the independent
`DELETION_FALSIFIER` review linked at its head.
