# Adversarial review of the strategic concentrated-arm collapse

Reviewer: Atlas Gatekeeper

## Verdict

**PASS.  Exportable as a corrective interface contraction, with strict scope.**

All four principal claims are mathematically valid:

1. every terminal exploitability witness already implies
   `HasQuittingStaticAtomicToggleHandoff reward`;
2. under the stated distinct-owner and positive vanishing-scale assumptions,
   `HasQuittingConcentratedSingletonStrategicDispatch` is equivalent to the
   terminal-label equality alone;
3. for the strong Fin4 packet, its strategic arm is equivalent to the
   adapter's Boolean action being `false` (Continue);
4. if that action is `true` (Quit), the existing checked consumer result
   forces the source-attached collision-minimum residual.

The two-player regression is also correct at its stated scope: the local
singleton atom, zero marked debt, and static atomic handoff need not decrease
total debt.  It has global minimum zero, so it does not refute a theorem that
uses the retained positive-minimum source.

This result must be presented as an **interface correction**, not as a
consumer of the concentrated-singleton node.  It proves that the currently
named strategic/static arm carries no packet-specific strategic content
beyond Continue-routing geometry.  It neither consumes the Continue mode nor
the collision-minimum residual.

The already reviewed positive-gap deletion no-go is independent and should
be cited rather than treated as necessary for the action normal form.  The
action-`true` collision conclusion does not use deletion exclusion: the left
consumer arm is impossible because its strategic-dispatch label is a
singleton while the routed terminal is a genuine pair.

## Exact claims checked

### Universal static atomic handoff

Let

```text
witness : QuittingTerminalExploitabilityWitness reward.
```

Then

```text
HasQuittingStaticAtomicToggleHandoff reward.
```

The submitted proof is exact.  The declaration
`QuittingTerminalExploitabilityWitness.exists_terminalGap_le_soloReward` in
`UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`
gives `s` with

```text
witness.terminalGap <= quittingSoloReward reward s s.
```

Together with `witness.terminalGap_pos`, this implies the strict hypothesis

```text
-witness.terminalGap < quittingSoloReward reward s s
```

of `witness.exists_collision_gain`.  That theorem gives `j != s` and

```text
quittingSoloReward reward s j + witness.terminalGap
  <= quittingSingletonCollisionReward reward s j.
```

Positivity of the gap turns this into the strict join inequality consumed by
`witness.hasStaticAtomicToggleHandoff_of_strictSingletonJoiner`, from
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/StaticStrategicCompression.lean`.
That checked theorem also constructs the unstable pure pair row required by
the definition, so no extra cardinality, stationarity, or source assumption
is missing.

This is fresh as a named theorem.  The closely related checked declaration
`witness.exists_immediateSingletonCollision` already composes the first two
toggle results into an executable singleton/collider row, but it does not
state the additional unstable-pair datum of
`HasQuittingStaticAtomicToggleHandoff`.  The checked theorem
`MinimalFinQuittingCounterexample.hasStaticAtomicToggleHandoff` has the same
conclusion only after cardinal-minimality and deletion arguments.  The new
proof shows those hypotheses were unnecessary.

### Strategic dispatch iff singleton label

For

```text
packet : QuittingReprojectionConcentratedPacket
  reward profiles owner terminal cutoff scale
other != owner
forall n, 0 < scale n
Tendsto scale atTop (nhds 0),
```

the equivalence

```text
HasQuittingConcentratedSingletonStrategicDispatch witness packet other
  <-> terminal.val = {other}
```

is valid.

The forward direction is literally the first conjunct of the definition in
`Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`.  For the
reverse direction, the label equality supplies both `terminal.val.card = 1`
and `other in terminal.val`; all remaining inputs are exactly those of the
checked theorem
`QuittingTerminalExploitabilityWitness.concentratedSingletonStrategicDispatch`.

Thus the statement does not erase a hidden analytic hypothesis: it retains
the actual packet, the distinctness of `other` and the packet owner, and the
positive vanishing scale.  Under those inputs, however, the endpoint-defect
limit, singleton static dispatch, and five-way final disjunction are indeed
automatic from the label.

There is a checked precedent which the export should cite explicitly:
`hasQuittingStoppingLawSingletonStrategicOrientation_iff_terminal_eq` in
`Research/Quitting/StoppingLawSingletonOrientationNoGo.lean`.  That theorem
proves the analogous correction for the older stopping-law rectangle
orientation.  The present claim is not a duplicate: it applies to the richer
`QuittingReprojectionConcentratedPacket` dispatch and is what enables the
strong-packet Boolean action normal form.

### Strong Fin4 action normal form

For

```text
source : FinFourMinimumAtomProducer reward bound
strong : FinFourSingletonStageStrongConcentratedPacket
  reward sourceProfile sourceTerminal stage resolution,
```

let `StrategicArm source strong` denote the left conjunctive alternative in
`FinFourStrongConcentratedPacketConsumerResult`.  Then

```text
StrategicArm source strong <-> strong.adapter.action = false.
```

This is correct.

If the action is false,
`FinFourSingletonStageStrongConcentratedPacket.routedTerminal_mode_and_card`
identifies `strong.adapter.routedTerminal.val` with
`{strong.singletonOwner}`.  The preceding equivalence gives the strategic
dispatch, while the universal witness theorem gives the static-handoff side
of the handoff/deletion disjunction.

Conversely, the first field of the strategic dispatch identifies the packet
terminal—definitionally `strong.adapter.routedTerminal`—with that singleton.
If the action were true, `routedTerminal_mode_and_card` would identify it with

```text
{strong.packetOwner, strong.singletonOwner},
```

which has cardinality two because
`strong.packetOwner_ne_singletonOwner`.  This contradicts the singleton
identity.  No source semantic or cap argument is used in this direction.

Finally, branch on the Boolean action and use
`FinFourSingletonStageStrongConcentratedPacket.consumerResult` from
`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`:

- action `false` supplies the strategic arm directly;
- action `true` rules out that arm by the equivalence, so the checked
  disjunction yields
  `Nonempty (QuittingConcentratedCollisionMinimumResidual ...)` on the same
  source, packet owner, routed terminal, and packet.

The strongest useful packaged result is therefore the mode-indexed
dichotomy

```text
(strong.adapter.action = false /\ StrategicArm source strong) \/
(strong.adapter.action = true /\
  Nonempty (QuittingConcentratedCollisionMinimumResidual
    reward source.point.1 strong.packetOwner
      strong.adapter.routedTerminal strong.adapter.packet)).
```

It is an output selection, not an exclusivity claim about existence of the
collision residual in Continue mode.

### Exact deletion

The note's Fin4 statement is correct.  A deleted Fin4 game has exactly three
players.  If it retained a positive terminal gap, the resulting nonexistence
of a uniform-equilibrium payoff would contradict
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three` in
`UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`.

The checked proof
`FourPlayerCyclicPlateauCandidate.no_exactPlayerDeletionAtPositiveGap` is
table-specific only because of its namespace and reward parameter; its proof
uses no special reward-table facts.  The stronger ordinary-mathematics
statement for at most three surviving players has already passed an
independent export review in
`exports/EXACT_POSITIVE_GAP_DELETION_SMALL_SURVIVORS_IMPOSSIBLE.md`.

Deletion exclusion is useful for simplifying the public consumer type, but
it is logically redundant after the universal static handoff: the
handoff-or-deletion disjunction is already true by its left side.  It is also
not needed to send Quit mode to the collision residual.

## Regression audit

I inspected
`Research/Quitting/StoppingLawSingletonOrientationNoGo.lean`, including:

- `singleton_observer_atom_eq_one`;
- `target_observer_debt_eq_zero`;
- `has_staticAtomicToggleHandoff`;
- `source_totalDebt` and `target_totalDebt`; and
- `positive_singletonAtom_with_staticHandoff_is_pureDebtTransfer`.

They establish exactly the stated local boundary:

- a positive singleton terminal-payoff-difference atom;
- zero unrestricted behavioral debt for the selected observer at the target;
- a static atomic-toggle handoff; and
- unchanged total debt, equal to one at source and target.

The theorem quantifies over every behavioral deviation of the observer in its
zero-debt field.  It is not merely a stationary-deviation regression.

The note correctly limits the conclusion.  This two-player table has a
zero-debt profile elsewhere, so its global minimum is zero.  It therefore
does not refute a consumer that uses `source.point`, `source.minimum`, or
positive-minimum chronology.  It does refute any claim that the local
strategic-arm fields alone force strict total-debt descent.

## Source-provenance conclusion

The definition `HasQuittingStaticAtomicToggleHandoff reward` stores only a
table-level existential owner, coalition, strict insertion inequality, and
unstable pure row.  It contains no field relating those witnesses to the
strong packet's source profile, marked date, tail, owners, minimum point, or
chronology.

Because the handoff can be constructed before a packet is selected, no proof
which merely destructs this proposition may recover such equalities.  This is
a type-level impossibility, not just a complaint about the current proof.
The checked barriers
`QuittingTerminalExploitabilityWitness.not_exists_globalStrictToggleRank` and
the pure-root chronology results in
`StaticCycleChronologyBarrier.lean` correctly explain why a free static
toggle cannot be iterated as a well-founded or temporal consumer.

The potentially useful Continue-mode data therefore remain external:

- the actual source and target profiles;
- the marked singleton mass;
- the literal post-date tail; and
- the attached positive minimum.

Any future consumer must use those dependent fields, not the table-level
handoff proposition.

## Export-gate assessment

This is export-worthy only in the following corrective form:

1. universal static atomic handoff from a terminal witness;
2. concentrated strategic dispatch iff singleton label;
3. strong Fin4 strategic arm iff Continue mode;
4. source-preserving Quit mode implies the existing collision-minimum
   residual; and
5. the two-player local regression as a boundary test.

This is a strict correction of the named downstream interface in
`questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md`: it proves that the apparent
rich strategic/static output is not a produced semantic operation and
reduces it exactly to routing geometry.  It thereby removes the static
handoff itself as a credible conjecture-facing producer route.  That is an
interface impossibility/contraction, not merely a new residual split.

The export must **not** claim to answer one of the main question's four
completion outputs.  Continue mode remains the source-attached singleton
obligation; Quit mode remains the source-attached collision-minimum
obligation.  No terminal approximation, return, debt/support descent, or
uniform payoff is produced.

## Lean handoff

Suggested declarations:

```text
QuittingTerminalExploitabilityWitness.hasStaticAtomicToggleHandoff

hasQuittingConcentratedSingletonStrategicDispatch_iff_terminal_eq

FinFourSingletonStageStrongConcentratedPacket
  .hasStrategicDispatch_iff_action_eq_false

FinFourSingletonStageStrongConcentratedPacket
  .strategicArm_iff_action_eq_false

FinFourSingletonStageStrongConcentratedPacket
  .collisionMinimumResidual_of_action_eq_true

FinFourSingletonStageStrongConcentratedPacket
  .actionIndexedConsumerResult
```

The first two belong near the generic strategic-dispatch definitions; the
last four are thin Fin4 integrations near
`StrongConcentratedPacketConsumer.lean`.  The deletion no-go should be
formalized from its separate reviewed packet and then used only to simplify
the public Fin4 consumer statement.

No new structure should store `HasQuittingStaticAtomicToggleHandoff` as if it
were source-matched data.  Conversely, the action-indexed result must retain
the exact `source` and `strong` inputs so the collision residual is
definitionally on the same packet.

## Nonclaims

- The universal static handoff is not a uniform-equilibrium or descent
  theorem.
- The handoff's existential witnesses need not equal either strong-packet
  owner or any marked coalition.
- Continue-routing does not make the target profile near-minimal or Nash.
- Quit-routing does not consume the collision-minimum residual.
- The two-player regression does not satisfy a positive global-minimum
  hypothesis and is not a quitting-game counterexample.
- The result does not supersede the need to consume both source-attached
  routing modes.

