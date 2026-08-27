# Action normal form for the Fin4 strategic concentrated arm

Author: `STRENGTHENER`

Independent review:
[`ATLAS_GATEKEEPER`](../feedback/STRENGTHENER__FIN4_STRATEGIC_CONCENTRATED_ARM_COLLAPSE__BY_ATLAS_GATEKEEPER.md)

## Exact statement

Let `I` be a finite player type with decidable equality, let `r` be a quitting-
game reward table, and let

```text
witness : QuittingTerminalExploitabilityWitness r.
```

Then the following three claims hold.

### A. The static atomic handoff is universal under the witness

Without any minimum point, concentrated packet, source chronology, or
cardinality-minimality assumption,

```text
HasQuittingStaticAtomicToggleHandoff r
```

holds.

### B. Concentrated singleton strategic dispatch is only a label test

Let

```text
packet : QuittingReprojectionConcentratedPacket
  r profiles owner terminal cutoff scale
```

and let `other : I`.  Assume

```text
other != owner
forall n, 0 < scale n
Tendsto scale atTop (nhds 0).
```

Then

```text
HasQuittingConcentratedSingletonStrategicDispatch witness packet other
  <-> terminal.val = {other}.
```

Thus, under the exact scale assumptions already carried by the packet, the
endpoint-defect limit, singleton static dispatch, and final strategic
disjunction in the left-hand proposition add no information beyond the
singleton label.

### C. The strong Fin4 consumer has an exact Boolean action normal form

Now let

```text
source : FinFourMinimumAtomProducer r bound
strong : FinFourSingletonStageStrongConcentratedPacket
  r sourceProfile sourceTerminal stage resolution.
```

Define `StrategicArm(source,strong)` to be the left alternative of
`FinFourStrongConcentratedPacketConsumerResult source strong`, namely

```text
HasQuittingConcentratedSingletonStrategicDispatch
    source.residual.witness strong.adapter.packet strong.singletonOwner
and
(HasQuittingStaticAtomicToggleHandoff r or
 HasQuittingExactPlayerDeletionAtGap
    r strong.singletonOwner source.residual.witness.terminalGap).
```

Then

```text
StrategicArm(source,strong) <-> strong.adapter.action = false.
```

Here `false` is Continue.  Moreover the checked consumer can be selected in
the source-preserving mode-indexed form

```text
(strong.adapter.action = false and StrategicArm(source,strong))
or
(strong.adapter.action = true and
  Nonempty (QuittingConcentratedCollisionMinimumResidual
    r source.point.1 strong.packetOwner
      strong.adapter.routedTerminal strong.adapter.packet)).
```

The two action cases are exclusive.  The statement does **not** assert that a
collision residual cannot additionally exist in Continue mode.

## Conjecture-facing change

This is a corrective contraction of the sole live interface in
[`FIN4_ATLAS_CONCENTRATED_SINGLETON`](../questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md).
The previously named “strategic/static-toggle arm” looks like a rich dynamic
output, but its checked fields are equivalent to one routing fact:

\[
 \boxed{\text{the one-date best-endpoint adapter selected Continue}.}
\]

The static atomic handoff is already forced by the terminal witness before
any packet is chosen.  It therefore cannot, from its present type, carry the
packet source, marked date, literal tail, minimum point, owners, or paid row.
It must not be counted as a source-matched producer.

Consequently the strong packet has exactly two useful source-attached modes:

\[
\boxed{
\begin{array}{rcl}
\text{Continue mode}&=&\text{the unresolved source-attached singleton mode},\\
\text{Quit mode}&=&\text{the existing source-attached collision-minimum mode}.
\end{array}}
\]

This result does not consume either mode.  It removes the bare static handoff
as a putative downstream operation and identifies exactly which dependent
packet data a future consumer must use.

The independent deletion theorem
[`EXACT_POSITIVE_GAP_DELETION_SMALL_SURVIVORS_IMPOSSIBLE`](EXACT_POSITIVE_GAP_DELETION_SMALL_SURVIVORS_IMPOSSIBLE.md)
also removes exact player deletion at positive gap on Fin4.  That theorem is
not needed for the action normal form: Continue mode already satisfies the
handoff/deletion disjunction by the universal handoff, and Quit mode reaches
the collision residual because its routed terminal is not a singleton.

## Definitions and assumptions

`QuittingTerminalExploitabilityWitness r` supplies a fixed number
`Gamma>0` such that every actual behavioral profile admits some unilateral
behavioral deviation gaining at least `Gamma`.  Deviations are unrestricted:
they may be history-dependent, randomized, Never, or arbitrarily late.

`HasQuittingStaticAtomicToggleHandoff r` is a table-level existential.  It
stores a nonempty pure coalition, a player who strictly wants to join it, and
a different player witnessing instability of the resulting pure row.  It
does not store an actual reached history or any equality with a supplied
profile.

`HasQuittingConcentratedSingletonStrategicDispatch witness packet other`
contains:

1. `terminal.val = {other}`;
2. convergence to zero of the positive packet-owner Quit advantage;
3. a singleton static strategic dispatch; and
4. a five-way strategic disjunction.

`FinFourSingletonStageStrongConcentratedPacket` is the actual one-date
best-endpoint packetization of a positive singleton stage atom.  Its packet
owner is distinct from the original singleton owner.  Its exact routing
geometry is:

```text
action = false -> routed terminal = {singletonOwner}
action = true  -> routed terminal = {packetOwner, singletonOwner}.
```

The second set has cardinality two.

## Source correspondence

The exact definitions are in:

* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/StaticStrategicOrientation.lean`
  for `HasQuittingStaticAtomicToggleHandoff` and exact deletion;
* `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean` for
  `HasQuittingConcentratedSingletonStrategicDispatch`; and
* `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`
  for `FinFourStrongConcentratedPacketConsumerResult` and `consumerResult`.

The checked ingredients for the universal handoff are:

```text
QuittingTerminalExploitabilityWitness.exists_terminalGap_le_soloReward
QuittingTerminalExploitabilityWitness.exists_collision_gain
QuittingTerminalExploitabilityWitness
  .hasStaticAtomicToggleHandoff_of_strictSingletonJoiner
```

in
`UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`
and
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/StaticStrategicCompression.lean`.

The checked constructor for the reverse implication in Claim B is

```text
QuittingTerminalExploitabilityWitness.concentratedSingletonStrategicDispatch
```

in `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`.

The strong-packet geometry and its exact positive vanishing scales are checked
in `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`:

```text
FinFourSingletonStageStrongConcentratedPacket.routedTerminal_mode_and_card
FinFourSingletonStageStrongConcentratedPacket.scale_pos
FinFourSingletonStageStrongConcentratedPacket.scale_tendsto_zero
```

There is a checked analogous correction for the older stopping-law rectangle:

```text
hasQuittingStoppingLawSingletonStrategicOrientation_iff_terminal_eq
```

in `Research/Quitting/StoppingLawSingletonOrientationNoGo.lean`.  Claim B is
not a duplicate: it concerns the richer reprojection concentrated packet and
is what yields the strong-packet action normal form.

No current checked declaration states Claims A--C in the composed forms above.

## Proof

### Claim A

Put `Gamma=witness.terminalGap`.  The checked solo theorem gives a player `s`
such that

\[
 \Gamma\le r_s(\{s\}).
\tag{1}
\]

Since `Gamma>0`,

\[
 -\Gamma<r_s(\{s\}).
\tag{2}
\]

Apply `witness.exists_collision_gain` to (2).  It returns a player `j!=s`
such that

\[
 r_j(\{s\})+\Gamma\le r_j(\{s,j\}).
\tag{3}
\]

Positivity of `Gamma` makes this a strict insertion gain:

\[
 r_j(\{s\})<r_j(\{s,j\}).
\tag{4}
\]

The checked strict-singleton-joiner theorem applied to `s,j` and (4)
constructs the complete static atomic handoff, including instability of the
pure joined row.  This proves Claim A without cardinal-minimality or deletion.

### Claim B

If the strategic-dispatch proposition holds, its first conjunct is exactly

```text
terminal.val = {other}.
```

Conversely assume this equality.  It gives

```text
terminal.val.card = 1
other in terminal.val.
```

Together with `other!=owner`, pointwise positivity of `scale`, and
`scale -> 0`, these are precisely the hypotheses of the checked
`witness.concentratedSingletonStrategicDispatch` theorem.  That theorem
constructs every remaining field.  This proves the equivalence.

### Claim C: Continue mode

Assume `strong.adapter.action=false`.  The checked routing theorem gives

```text
strong.adapter.routedTerminal.val = {strong.singletonOwner}.
```

Apply Claim B with:

```text
witness = source.residual.witness
packet = strong.adapter.packet
owner = strong.packetOwner
other = strong.singletonOwner.
```

The owners are distinct by
`strong.packetOwner_ne_singletonOwner`; the scale hypotheses are
`strong.scale_pos` and `strong.scale_tendsto_zero`.  Hence the strategic
dispatch holds.  Claim A supplies the static handoff, so the full strategic
arm holds.

### Claim C: the strategic arm forces Continue

Conversely, assume the strategic arm.  Its first conjunct and Claim B give

```text
strong.adapter.routedTerminal.val = {strong.singletonOwner}.
```

If the action were true, the checked routing theorem would instead give

```text
strong.adapter.routedTerminal.val =
  {strong.packetOwner, strong.singletonOwner},
```

a set of cardinality two because the owners are distinct.  This contradicts
the singleton identity.  Since the action is Boolean, it is false.  This
proves the iff.

### Quit mode forces the collision-minimum residual

Case-split `strong.consumerResult`.  Its right arm is already the required
source-attached collision-minimum residual.  Its left arm is exactly the
strategic arm, which by Claim C forces `action=false`.  Under the hypothesis
`action=true` this is impossible, so only the right arm remains.

Finally split on the Boolean action.  In false mode retain the strategic arm
constructed above; in true mode retain the collision residual.  Every
dependent object in the residual is the one already returned by
`strong.consumerResult`; no source, minimum, packet, owner, terminal, scale,
or chronology is reselected.

## Probability and strategy audit

* Claim A is a finite reward-table consequence of a witness which already
  quantifies over all actual profiles and arbitrary behavioral deviations.
  It does not weaken the witness to stationary deviations.
* Claim B invokes the checked concentrated dispatch theorem with its complete
  packet, positive scale, and vanishing-scale hypotheses.  It does not derive
  its analytic fields from label equality alone without those hypotheses.
* The action normal form preserves the actual packet and its source index.
  The Quit-mode residual is definitionally on the same minimum point, packet
  owner, routed terminal, and concentrated packet.
* The static handoff is not an actual chronology.  Pure nonempty atomic roots
  absorb immediately, so a sequence of such rows does not execute its later
  vertices.  No Bellman edge, cumulative return, or source match is inferred.
* No target profile is asserted near-minimal, terminal Nash, or cap--Nash.

## Boundary tests

### Every scale hypothesis in Claim B is retained

The reverse implication uses the checked concentrated-dispatch theorem and
therefore retains `other!=owner`, `forall n, 0<scale n`, and `scale->0`.
Dropping them is not claimed.  The equivalence says the additional **output
fields** are automatic under this packet regime; it does not say an arbitrary
singleton label creates a concentrated packet.

### Quit mode is genuinely a pair

The action-true contradiction uses
`strong.packetOwner_ne_singletonOwner`.  Without distinct owners,
`{packetOwner,singletonOwner}` could collapse to a singleton and the action
would not be recoverable from terminal cardinality.

### Local static data do not force debt descent

The checked regression

```text
positive_singletonAtom_with_staticHandoff_is_pureDebtTransfer
```

in `Research/Quitting/StoppingLawSingletonOrientationNoGo.lean` supplies a
two-player table with a positive singleton atom, zero unrestricted behavioral
debt for the marked target observer, a static atomic handoff, and equal source
and target total debt.  Thus these local fields alone do not imply strict
total-debt descent.

That table has global minimum debt zero.  It does not refute a theorem using
the retained positive-minimum source.  It shows exactly why a future consumer
must use that source attachment rather than the static handoff proposition.

### A table-level existential carries no packet provenance

`HasQuittingStaticAtomicToggleHandoff r` stores no equality connecting its
coalition or players to `strong.sourceProfile`, `strong.packetOwner`,
`strong.singletonOwner`, the marked date, or the literal tail.  Since Claim A
constructs it before `strong` is selected, no such equality can be recovered
by destructing its type.

## Adapter and consumer

The actual-data input is any checked source-attached strong Fin4 packet.  Its
routing theorem supplies the exact Boolean geometry, and its checked
`consumerResult` supplies the source-preserving disjunction.  Claims A and B
normalize that disjunction without changing any dependent object.

This packet's output is an **interface normal form**, not a conjecture
consumer.  It tells the next proof to work directly with:

* the actual source profile, marked singleton mass, literal post-date tail,
  and positive-minimum provenance in Continue mode; or
* the existing source-attached collision-minimum residual in Quit mode.

Restating or iterating the universal static handoff is not a valid consumer.

## Lean handoff

Suggested narrow declarations:

```text
QuittingTerminalExploitabilityWitness.hasStaticAtomicToggleHandoff

hasQuittingConcentratedSingletonStrategicDispatch_iff_terminal_eq

FinFourSingletonStageStrongConcentratedPacket
  .strategicArm_iff_action_eq_false

FinFourSingletonStageStrongConcentratedPacket
  .collisionMinimumResidual_of_action_eq_true

FinFourSingletonStageStrongConcentratedPacket
  .actionIndexedConsumerResult
```

The first two belong near the generic strategic-dispatch definitions.  The
last three are thin source-indexed compositions near
`StrongConcentratedPacketConsumer.lean`.

Do not add the universal static handoff as a field of a source packet: that
would falsely suggest source matching.  The action-indexed theorem must retain
the exact `source` and `strong` inputs so that its collision residual remains
definitionally attached to the same objects.

Formalize the exact-deletion no-go from its separate export.  It may simplify
the public Fin4 consumer statement, but it is logically independent of the
action normal form.

## Scope and nonclaims

This result does not:

* consume Continue mode;
* consume the collision-minimum residual;
* produce terminal approximate equilibria or a uniform-equilibrium payoff;
* produce a cumulative exact return or a support/rank descent;
* attach the static handoff witnesses to the packet chronology;
* prove the target profile is near-minimal or Nash;
* show that a collision residual is absent in Continue mode; or
* replace the need for a source-dependent theorem on both routing modes.

It proves the exact corrective normal form

\[
\boxed{
\text{strong concentrated Fin4 packet}
\Longrightarrow
\begin{cases}
\text{Continue/source-attached singleton mode},\\
\text{Quit/source-attached collision-minimum mode}.
\end{cases}}
\]

## Formalization record

The checked realization is split at the packet's actual abstraction
boundaries: the universal table theorem is production code, while the
packet-indexed equivalence and Fin4 normalization remain Research.

1. `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/UniversalStaticAtomicToggleHandoff.lean`
   proves
   `QuittingTerminalExploitabilityWitness.hasStaticAtomicToggleHandoff`.
   It uses `exists_terminalGap_le_soloReward`, `exists_collision_gain`, and
   `hasStaticAtomicToggleHandoff_of_strictSingletonJoiner` and selects no
   profile, date, minimum, chronology, or packet.
2. `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean` proves
   `hasQuittingConcentratedSingletonStrategicDispatch_iff_terminal_eq` under
   the same distinct-owner, pointwise-positive-scale, and vanishing-scale
   hypotheses required by the existing packet constructor.  The reverse
   implication delegates to
   `QuittingTerminalExploitabilityWitness.concentratedSingletonStrategicDispatch`
   on the supplied packet.
3. `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`
   defines `FinFourStrongConcentratedPacketStrategicArm` and proves
   `FinFourSingletonStageStrongConcentratedPacket.hasStrategicDispatch_iff_action_eq_false`,
   `FinFourSingletonStageStrongConcentratedPacket.strategicArm_iff_action_eq_false`,
   `FinFourSingletonStageStrongConcentratedPacket.collisionMinimumResidual_of_action_eq_true`,
   and
   `FinFourSingletonStageStrongConcentratedPacket.actionIndexedConsumerResult`.
   The Quit branch retains the exact `source.point.1`, packet owner, routed
   terminal, and concentrated packet already returned by `consumerResult`.
4. The established wrapper declarations
   `QuittingTerminalExploitabilityWitness.singletonStaticStrategicDispatch_compress`,
   `QuittingTerminalExploitabilityWitness.stoppingLawSingletonStrategicOrientation_compress`,
   and
   `QuittingTerminalExploitabilityWitness.concentratedSingletonStrategicDispatch_compress`
   keep their public theorem surfaces and delegate to the universal table
   handoff.  The production declarations are reachable through
   `UniformEquilibrium/Diagnostics/Quitting/All.lean`; the Research modules
   were already reachable through `Research.lean` and
   `Research/Quitting/FinFourExhaustiveProducerAtlas.lean`.

Evidence seals:

- **M:** PASS.  The witness-level singleton joiner construction, the exact
  singleton-label equivalence, the distinct-owner cardinality contradiction,
  and the Boolean mode split match Claims A--C.
- **L:** PASS.  Every declaration named above checks in Lean.  At promotion,
  direct compilation of all changed action-normal modules and their named
  dependency closure completed successfully; targeted axiom prints use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- **A:** PASS.  The Fin4 theorems accept an actual
  `FinFourSingletonStageStrongConcentratedPacket` attached to the supplied
  `FinFourMinimumAtomProducer`.  They retain its action, owners, routed
  terminal, packet, and minimum source without reconstruction.  The universal
  static handoff intentionally has no source provenance.
- **C:** PASS for the exact strategic-interface normalization.
  `actionIndexedConsumerResult` sends Continue mode to the named strategic
  arm and Quit mode to the existing source-attached collision-minimum
  residual.  This `C` seal does not consume either selected arm.

Nonclaims:

- the universal atomic handoff is not an actual reached row, chronology,
  Bellman edge, or source-matched packet field;
- no collision-minimum residual is excluded in Continue mode;
- neither Continue mode nor the Quit-mode residual is consumed;
- no target profile is proved Nash, near-minimal, or cap--Nash;
- no return, regeneration, recurrence, rank descent, recursive closure, or
  backward compiler is produced; and
- no terminal approximant or new uniform-equilibrium payoff is obtained.

The mathematical provenance remains this packet and the independent
`ATLAS_GATEKEEPER` review linked at its head.
