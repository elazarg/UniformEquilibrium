# The strategic concentrated-singleton arm is only its routing geometry

Author: `STRENGTHENER`

## Status

**Ordinary mathematics, not Lean-checked as the composed statements below.**
All ingredients used in the proofs are checked declarations.  The result is
a sharp interface no-go and an atlas simplification, not a uniform-equilibrium
consumer.

For a terminal exploitability witness, the static atomic-toggle handoff is
already available without any concentrated packet, minimum point, or source
chronology.  More strongly, under the standard positive-scale hypotheses the
full proposition
`HasQuittingConcentratedSingletonStrategicDispatch` is equivalent to the bare
identity saying that the packet terminal is the named singleton.

For the strong Fin4 packet, this makes its strategic consumer arm equivalent
to the one-date adapter having selected **Continue**.  If it selected Quit,
the checked consumer necessarily returns the collision-minimum residual.
Thus the present strategic arm cannot be coupled to a paid row, toggle SCC,
or minimum-fiber rank through its exported fields: those fields contain no
source-dependent strategic information beyond the routing mode.

## 1. Every terminal-gap table already has the static atomic handoff

Let

```text
witness : QuittingTerminalExploitabilityWitness reward.
```

Then

```text
HasQuittingStaticAtomicToggleHandoff reward
```

holds, without a minimal-cardinality hypothesis.

### Proof

The checked theorem

```text
witness.exists_terminalGap_le_soloReward
```

gives a player `s` such that

\[
 \Gamma\le r_s(\{s\}),
 \qquad \Gamma:=\texttt{witness.terminalGap}>0.
\tag{1}
\]

In particular `-Gamma < r_s({s})`.  Apply

```text
witness.exists_collision_gain
```

to the singleton owner `s`.  It returns `j != s` with

\[
 r_j(\{s\})+\Gamma\le r_j(\{s,j\}),
\tag{2}
\]

so `j` strictly gains by joining the nonempty coalition `{s}`.  The checked
theorem

```text
witness.hasStaticAtomicToggleHandoff_of_strictSingletonJoiner
```

then returns the desired handoff with toggle owner `j` and `quitters={s}`.

A direct Lean-facing proof is:

```lean
theorem QuittingTerminalExploitabilityWitness.hasStaticAtomicToggleHandoff
    (witness : QuittingTerminalExploitabilityWitness reward) :
    HasQuittingStaticAtomicToggleHandoff reward := by
  obtain ⟨s, hsolo⟩ := witness.exists_terminalGap_le_soloReward
  have hs : -witness.terminalGap < quittingSoloReward reward s s := by
    linarith [witness.terminalGap_pos]
  obtain ⟨j, hjs, hjoin⟩ := witness.exists_collision_gain hs
  apply witness.hasStaticAtomicToggleHandoff_of_strictSingletonJoiner s j hjs
  linarith [witness.terminalGap_pos]
```

This strengthens
`MinimalFinQuittingCounterexample.hasStaticAtomicToggleHandoff`: cardinal
minimality and the deletion alternative are unnecessary.

## 2. The full singleton strategic proposition is equivalent to its label

Let

```text
packet : QuittingReprojectionConcentratedPacket
  reward profiles owner terminal cutoff scale
```

and fix `other != owner`.  Assume

```text
∀ n, 0 < scale n
Tendsto scale atTop (nhds 0).
```

Then

\[
\boxed{
\operatorname{HasQuittingConcentratedSingletonStrategicDispatch}
  (witness,packet,other)
\iff terminal=\{other\}.}
\tag{3}
\]

The forward implication is the first field of the definition.  Conversely,
the singleton identity supplies cardinality one and membership of `other`, so
the checked theorem

```text
witness.concentratedSingletonStrategicDispatch
```

constructs the full proposition.

Thus all its remaining conjuncts are automatic once the label is a singleton:

- the positive part of the packet owner's Quit advantage tends to zero;
- `HasQuittingSingletonStaticStrategicDispatch` holds;
- and the final five-way strategic disjunction holds.

This is not merely a logical weakening caused by compression.  The atomic
alternative in the final disjunction can always be discharged by the
game-wide handoff of Section 1, independently of the packet.  Hence the
proposition does not force its owner-tail-escape or played-join-loss witnesses
to exist, even when the proof that originally introduced the proposition
passed through those alternatives.

The corresponding narrow Lean statement is:

```lean
theorem hasQuittingConcentratedSingletonStrategicDispatch_iff_terminal_eq
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (other : iota) (hne : other ≠ owner)
    (hscale : ∀ n, 0 < scale n)
    (hscale0 : Tendsto scale atTop (nhds 0)) :
    HasQuittingConcentratedSingletonStrategicDispatch witness packet other ↔
      terminal.val = {other} := by
  constructor
  · exact fun h => h.1
  · intro hterminal
    apply witness.concentratedSingletonStrategicDispatch packet
      (by simp [hterminal]) other hne (by simp [hterminal]) hscale hscale0
```

## 3. Exact action normal form for the strong Fin4 packet

Let

```text
source : FinFourMinimumAtomProducer reward bound
strong : FinFourSingletonStageStrongConcentratedPacket ...
```

and abbreviate the left side of
`FinFourStrongConcentratedPacketConsumerResult source strong` by

```text
StrategicArm(source,strong) :=
  HasQuittingConcentratedSingletonStrategicDispatch
    source.residual.witness strong.adapter.packet strong.singletonOwner ∧
  (HasQuittingStaticAtomicToggleHandoff reward ∨
   HasQuittingExactPlayerDeletionAtGap reward strong.singletonOwner
     source.residual.witness.terminalGap).
```

Then

\[
\boxed{
\operatorname{StrategicArm}(source,strong)
\iff strong.adapter.action=false.}
\tag{4}
\]

### Continue implies the strategic arm

If `action=false`,
`FinFourSingletonStageStrongConcentratedPacket.routedTerminal_mode_and_card`
identifies the routed terminal with `{strong.singletonOwner}`.  Equation (3)
supplies the strategic dispatch.  Section 1 supplies the left member of the
static-toggle/deletion disjunction.

### The strategic arm implies Continue

Its strategic-dispatch conjunct identifies the routed terminal with the
singleton `{strong.singletonOwner}`.  If `action=true`, the checked mode
theorem instead identifies it with the two-element set
`{strong.packetOwner,strong.singletonOwner}`; the two labels are distinct.
The cardinalities `2` and `1` contradict each other.  Hence the action is
Continue.

Combining (4) with the checked theorem

```text
strong.consumerResult
```

gives the exact action-indexed normal form:

\[
\boxed{
\begin{array}{rcl}
action=false&\Longrightarrow&\text{the strategic arm, automatically},\\[1mm]
action=true&\Longrightarrow&
\operatorname{Nonempty}(
  \texttt{QuittingConcentratedCollisionMinimumResidual}).
\end{array}}
\tag{5}
\]

For the second line, apply `strong.consumerResult`; its left alternative
would imply `action=false` by (4), so only the collision-minimum residual
remains.

There is no genuine exact-deletion outlet on `Fin 4`.  Independently, for any
positive `gap`, deleting one Fin4 player gives a three-player quitting game,
which has a uniform-equilibrium payoff by
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three`.  This
contradicts the retained positive terminal exploitability gap.  The proof is
already instantiated for one table as
`FourPlayerCyclicPlateauCandidate.no_exactPlayerDeletionAtPositiveGap`; the
same proof is table-independent.

## 4. Why the handoff cannot be coupled from its present type

`HasQuittingStaticAtomicToggleHandoff reward` is a table-level existential.
It stores:

- a strict insertion edge `A -> A+owner` for a nonempty coalition `A`; and
- an unstable pure atomic row at `A+owner`, witnessed by a different player.

It stores no equality between any of these labels and:

- the strong packet owner or singleton owner;
- its marked date or actual live root;
- its literal post-date tail;
- the selected minimum semantic/law point; or
- a paid observer and its first-disagreement times.

Because Section 1 constructs this proposition before the packet is even
chosen, no such equality can be recovered by destructing the proposition.
Proof provenance is not data provenance.

The pure atomic row itself has perfect all-behavior cap localization: its quit
set contains at least two players, so after any unilateral behavioral
replacement at least one prescribed player still Quits and the row absorbs
immediately.  Cap leakage is therefore not the local problem.  The problem is
that this pure row is a horizontal counterfactual unrelated to the actual
packet chronology.

Likewise, the toggle-SCC route cannot use the handoff as a rank.  The terminal
witness already supplies a strict toggle at every coalition, and

```text
witness.not_exists_globalStrictToggleRank
```

rules out every coalition-only natural rank decreasing along all such edges.
`StaticCycleChronologyBarrier.lean` proves the orthogonal chronology no-go:
nonempty pure-set roots have zero joint survival, so an ordered list of them
never reaches its second vertex.  A singleton leave also exposes the actual
tail rather than the artificial empty-coalition reward.

Thus coupling the static handoff to a nonowner paid row or a toggle SCC would
require a new dependent source theorem.  It cannot be extracted from
`HasQuittingStaticAtomicToggleHandoff` or from the present strategic-arm
proposition.

## 5. Exact local regression against debt descent

`Research/Quitting/StoppingLawSingletonOrientationNoGo.lean` supplies a
checked two-player boundary example with:

- a positive singleton rectangle atom;
- zero debt, indeed no profitable arbitrary behavioral deviation, for the
  marked observer at the target;
- a static atomic-toggle handoff; and
- equal source and target total debt, both equal to one.

The theorem

```text
positive_singletonAtom_with_staticHandoff_is_pureDebtTransfer
```

packages these facts.  Hence the local singleton mark, zero selected debt,
and static handoff do not imply strict total-debt descent.  The table has
global minimum zero and therefore is not a counterexample to a theorem using
positive-minimum provenance.  Its role is narrower: it proves that any such
consumer must use the retained minimum/source connection in a quantitatively
new way, rather than the strategic-arm fields themselves.

## 6. Consequence for the atlas

The phrase “strategic/static-toggle branch” should not be read as a consumed
atlas branch.  At the current interface it means exactly:

```text
the one-date best-endpoint router selected Continue,
so the marked terminal stayed the original singleton.
```

All of its advertised strategic/static fields are forced by the terminal
witness and this geometry.  The source-attached information which remains
potentially useful lies outside the proposition:

- the actual marked source profile;
- its fixed positive singleton mass;
- exact post-date tail equality;
- and the selected minimum/source chronology.

The next legitimate theorem for this mode must consume those dependent fields
directly.  Restating or iterating the static handoff cannot do so.  In the Quit
mode, (5) already returns the existing source-indexed collision-minimum
residual.

## 7. Files and declarations inspected

- `HasQuittingStaticAtomicToggleHandoff` and
  `HasQuittingExactPlayerDeletionAtGap` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/StaticStrategicOrientation.lean`;
- `exists_outsider_atomicDeviation_of_strict_ownerToggle` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlayerDeletion.lean`;
- `exists_terminalGap_le_soloReward` and `exists_collision_gain` in
  `UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`;
- `hasStaticAtomicToggleHandoff_of_strictSingletonJoiner` and
  `singletonStaticStrategicDispatch_compress` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/StaticStrategicCompression.lean`;
- `HasQuittingConcentratedSingletonStrategicDispatch` and
  `concentratedSingletonStrategicDispatch` in
  `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`;
- `FinFourSingletonStageStrongConcentratedPacket.routedTerminal_mode_and_card`
  in `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`;
- `FinFourSingletonStageStrongConcentratedPacket.consumerResult` in
  `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three` in
  `UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`;
- `QuittingTerminalExploitabilityWitness.not_exists_globalStrictToggleRank`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictToggleWellFoundedBarrier.lean`;
- the executable barriers in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StaticCycleChronologyBarrier.lean`;
  and
- `positive_singletonAtom_with_staticHandoff_is_pureDebtTransfer` in
  `Research/Quitting/StoppingLawSingletonOrientationNoGo.lean`.

## 8. Concrete next question

In the Continue-routing mode, use the external source attachment—not the
strategic proposition—to compare the actual near-minimum post-date tail with
the fixed positive singleton row.  Either produce an exact source-matched
entrance/return whose cap account survives arbitrary deviations, or exhibit a
positive-minimum regression.  The static handoff should not appear as an
input: Section 1 shows it is already free under the terminal witness.
