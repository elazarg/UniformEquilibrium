# Review of pure-collision screening

Reviewer: Atlas Gatekeeper

## Verdict

**PASS, in a corrected and slightly stronger form.**

The mathematical core is valid and does not use a tail-debt, near-minimum,
cap-Nash, or self-tail hypothesis.  It gives a direct actual-data arrow from
every positive-mass nonsingleton Fin4 row over a positive global semantic-debt
minimum to a positive-mass singleton row, and hence to the already checked
strong concentrated-singleton packet and its consumer split.

The cleanest proof is stronger than the submitted proof: the bounded partial
purification is unnecessary.  Replace the marked product root simultaneously
by the pure root of the displayed nonsingleton coalition.  This is an actual
literal profile, keeps every date before and after the mark unchanged, and
has marked coalition mass equal to the original live mass.  The finite
best-endpoint screening orbit can start there.

Two wording repairs are required before export:

1. the lower bound `lambda * D_* / 4` applies to the strict best-endpoint
   edges in the **pure nonsingleton orbit**.  It does not apply to the
   submitted preliminary purification steps, nor to the final arbitrary
   mass-preserving route from a pair to a singleton;
2. there is a missing closing display delimiter after equation (6).

Subject to those repairs, this is suitable as a stronger replacement for the
pending self-tail atlas-entrance export.  It reaches the same maintained
strong concentrated-singleton node, but eliminates the high/low tail split,
the restarted continuation, and all near-minimum estimates.  It does not
consume that remaining node.

## Claim audited

Let `reward` be a quitting-game table on `Fin 4`.  Let `minimum` be a global
minimum of total terminal semantic debt on the carrier, with

```text
D_* = quittingTerminalSemanticDebtSum minimum > 0.
```

Let `profile` be any actual behavioral profile, `stage` a date, `terminal` a
nonsingleton coalition, and `lambda > 0`, with

```text
lambda <= quittingStageCoalitionMass reward profile stage terminal.
```

Then there is an actual literal same-stage singleton target whose stage mass
is at least `lambda`.  It is obtained by:

1. replacing the marked root by the pure root of `terminal`; and
2. following exact best-endpoint updates while the pure coalition is
   nonsingleton, stopping at a mass-preserving singleton route.

Every best-endpoint edge in step 2 has literal payoff gain at least

```text
lambda * D_* / 4.
```

All profiles in this construction copy the original live roots at every date
other than `stage`.  In particular, the past and the complete post-date tail
are literal, not merely semantically equivalent.

## Source declarations inspected

I inspected the following exact declarations and their proof bodies.

### Literal profiles, gains, and debt

In `Research/Quitting/SameStageEndpointMonodromy.lean`:

- `quittingLiteralOneDateProfile`;
- `quittingLiteralPureRootProfile`;
- `quittingLiteralPureRootCoalitionProfile`;
- `quittingProfileLiveRoot_literalPureRootProfile_self`;
- `quittingLiteralPureRootProfile_tail_eq`;
- `quittingTerminalSemanticPair_spine_literalPureRoot_tail_eq`;
- `quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass`;
- `quittingTerminalPayoff_literalOneDateProfile_bestEndpoint_gain_eq`;
- `quittingTerminalSemanticDebt_literalOneDateProfile_bestEndpoint_eq_sub_gain`;
- `QuittingSameStageEndpointEdge`;
- `QuittingSameStageSingletonRoute`;
- `exists_quittingSameStage_terminalRoute_or_closedSegment`.

In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauIncidence.lean`:

- `quittingTerminalSemanticPair_spine_eq_prefix`.

In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectCharge.lean`:

- `quittingRootCoordinateNashDefect_le_terminalSemanticDebt_prefix`.

In `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`:

- `quittingTerminalDeviationDebt_rootThenContinuation_le_coordinateDefect_add`.

The last two declarations give the two one-sided ingredients behind the
submitted zero-transport calculation.  For formalization, a direct semantic
calculation is cleaner: when the opponents-only Continue mass is zero,
`quittingRootContinuePayoff_update_add` shows that replacing the tail payoff
by the tail cap changes nothing, so the prefix semantic debt is exactly the
root coordinate Nash defect.

### Purification and orbit exclusion

In `Research/Quitting/SameStageEndpointPurification.lean`:

- `quittingPartialPurification_exists_step`;
- `quittingPartialPurification_exists_total_or_singleton`;
- `quittingPartialPurification_then_sameStage_dispatch`.

These validate the submitted bounded-purification route, but the last theorem
does carry the old `hlowTail` hypothesis.  It must not be invoked by the new
proof.  The direct pure-root overwrite above avoids it completely.

In `Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean`:

- `quittingSameStageSingletonRoute_of_card_eq_two`;
- `sameStageEndpointTrace_false_of_effectiveSupport_card_le_four`;
- `not_nonempty_finFourSameStageEndpointClosedSegment`.

The terminal predicate is exactly suitable: it permits an arbitrary Boolean
endpoint action with no-loss routed mass.  In particular, a two-player pure
coalition is terminal by forcing one member to Continue.  The final singleton
route need not be a best response, and the proof does not claim that it is.

### Atlas source and downstream adapter

In `Research/Quitting/FinFourProducerAtlas/Source.lean`:

- `FinFourMinimumAtomProducer`;
- `FinFourMinimumAtomProducer.minimumDebt_pos`;
- `QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows` as used by
  `FinFourMinimumAtomProducer.nonempty_tailEscape_or_lowTailRow`.

In `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`:

- `FinFourSingletonStageStrongConcentratedPacket`;
- `FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass`.

In
`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`:

- `FinFourStrongConcentratedPacketConsumerResult`;
- `FinFourSingletonStageStrongConcentratedPacket.consumerResult`.

The generic strong-packet constructor and consumer do not require a
`FinFourLowTailRow` or a `FinFourAtlasWeakConcentratedSingletonCore`.  Thus the
new singleton output can be kept dependent on the original
`FinFourMinimumAtomProducer` and passed directly to the existing consumer.
The current weak-core `.reached` constructor is low-row-specific; a new
source-attached result structure is preferable to manufacturing that old
wrapper.

## Mathematical verification

### 1. Direct pure sibling, with no purification hypothesis

Write `C = terminal.val` and let

```text
pureProfile =
  quittingLiteralPureRootCoalitionProfile reward profile stage C.
```

The original stage mass is at most the original live mass.  The checked
pure-root mass identity gives

```text
quittingStageCoalitionMass reward pureProfile stage C
  = quittingLiveMass reward profile stage.
```

Therefore the pure sibling still carries mass at least `lambda`.  By the
literal override definitions, its live roots before and after `stage` are
exactly those of `profile`.  This step changes several marked marginals at
once, but it is an actual profile construction; it is not represented as a
unilateral profitable deviation and does not need to be.

### 2. Pure nonsingleton roots erase all continuation debt

Fix any nonsingleton coalition `C`, use its pure root `q_C`, and let `tail` be
the actual semantic pair of the common post-date spine.  For every player
`i`, choose `j in C` distinct from `i`; this is possible because
`C.card >= 2`.  After forcing `i` to Continue, `j` still Quits surely, hence

```text
quittingRootOpponentContinueMass q_C i = 0.
```

In the semantic prefix formula, the only occurrence of `tail.2 i` instead
of `tail.1 i` is multiplied by this opponent-Continue mass.  Consequently

```text
quittingTerminalSemanticDebt
    (quittingTerminalSemanticPrefix reward q_C tail) i
  = quittingRootCoordinateNashDefect reward tail.1 q_C i.
```

This is an all-behavior statement: the second coordinate of `tail` is the
unrestricted behavioral cap.  Sure absorption after every unilateral
deviation is exactly why no later strategy can contribute.

The conditional spine beginning at `stage` is an actual behavioral profile,
and `quittingTerminalSemanticPair_spine_eq_prefix` identifies its semantic
pair with this prefix.  Global minimality therefore yields

```text
D_* <= sum_i quittingRootCoordinateNashDefect reward tail.1 q_C i.
```

On `Fin 4`, some coordinate defect is at least `D_*/4`.

### 3. Literal edge gain and mass preservation

Choose a maximizing coordinate as in the preceding step and its checked best
endpoint.  The exact one-date gain identity gives

```text
gain = liveMass * coordinateDefect.
```

Every pure coalition sibling has the same live mass at `stage`, and that live
mass is at least `lambda`.  Hence

```text
gain >= lambda * D_* / 4 > 0.
```

The existing routed-coalition theorem preserves stage mass, and the mover's
unrestricted semantic debt decreases by this exact literal gain.  If the
target is nonsingleton, these facts construct a
`QuittingSameStageEndpointEdge`.  Its stored floor is only
`lambda * D_* / 8`, so the new estimate is more than sufficient.  If the
target is a singleton, it is already the desired output.

### 4. Finite dispatch

The preceding construction gives, at every pure nonsingleton coalition, a
terminal singleton route or a strict endpoint edge.  Apply
`exists_quittingSameStage_terminalRoute_or_closedSegment`.  The closed arm is
contradicted by `not_nonempty_finFourSameStageEndpointClosedSegment`.
Therefore the terminal orbit supplies an actual singleton target with stage
mass at least `lambda`.

Notice that `QuittingSameStageSingletonRoute` is deliberately broader than a
best-response route.  A terminal pair can be reduced to a singleton by an
arbitrary Continue action.  Accordingly, the `lambda * D_*/4` gain statement
is for the strict orbit edges only, not for this last route.

## No hidden tail or near-minimum premise

The proof uses the tail only as the literal continuation of the conditional
spine.  It never assumes:

- small tail debt or small total tail excess;
- that the marked full profile is close to the minimum fiber;
- that a copied cap-root stack remains cap-Nash after any update;
- that the target root is cap-Nash;
- a self-tail equality; or
- finite support or eventual absorption of the tail.

The only minimum input is the universal carrier inequality
`D_* <= D(candidate)`, applied to each actual conditional pure-root sibling.
This is precisely why the new proof remains valid for arbitrary behavioral
tails, including infinite support and Never mass.

## Atlas integration and freshness

The current checked atlas source first applies
`FinFourMinimumAtomProducer.nonempty_tailEscape_or_lowTailRow`, and the pending
export `FIN4_NONSINGLETON_MINIMUM_LAW_SELF_TAIL_CONTRACTION.md` repairs the
high-tail arm by restarting a selected profile.  Neither construction is
needed here.

For a nonsingleton minimum-law atom, obtain its one retained `SelectedRows`
family directly.  The checked eventual stage-mass estimate supplies a rank
with

```text
source.minimumSingletonClockResolution
  < selectedStageMass rows rank.
```

Apply the local theorem to that actual selected profile and date.  Its
singleton output gives a
`FinFourSingletonStageStrongConcentratedPacket` by
`nonempty_of_singleton_stageMass`, and the same source's
`consumerResult` gives the maintained strategic-versus-collision split.

This is new relative to the inspected declarations.  The existing raw
same-stage dispatch requires `hlowTail`; the existing direct atlas source
performs a high/low split; and the current self-tail theorem supplies a
near-minimum restarted tail.  No checked declaration derives the singleton
from the positive-mass row and global minimum alone.

The conjecture-facing terminal node does not become smaller—the strong
concentrated-singleton consumer remains open—but the pending atlas-entrance
proof is strictly strengthened and simplified.  An export should therefore
replace or supersede the self-tail entrance packet rather than be presented
as a second terminal-node contraction.

## Strongest recommended statement

The local theorem should be stated independently of the minimum-law source:

> **Fin4 positive-minimum pure-collision screening.**  Given a positive global
> minimum semantic pair, any actual Fin4 profile carrying a nonsingleton
> coalition at one date with unconditional mass at least `lambda > 0` has a
> literal same-date singleton target with mass at least `lambda`.  It is
> reached from the pure sibling of the displayed coalition through a finite
> dispatched best-endpoint orbit.  Every strict orbit edge has literal gain
> at least `lambda * D_* / 4`; every profile retains the original past and
> post-date tail.

Then give a dependent atlas corollary:

> **Nonsingleton minimum-law contraction.**  Every
> `FinFourMinimumAtomProducer` whose retained atom is nonsingleton produces a
> source-attached `FinFourSingletonStageStrongConcentratedPacket` at the
> canonical resolution, and hence its checked
> `FinFourStrongConcentratedPacketConsumerResult`.

This is the actual-data adapter and downstream semantic consumer required by
the export gate.

## Lean handoff

Suggested narrow declarations:

```text
quittingPureNonsingleton_opponentContinueMass_eq_zero
quittingPureNonsingleton_prefixDebt_eq_coordinateNashDefect
quittingFinFourPureNonsingleton_dispatch_noTail
quittingFinFourPositiveMassNonsingleton_exists_singleton_noTail
FinFourMinimumAtomProducer.nonempty_strongConcentratedPacket_of_nonsingleton
FinFourMinimumAtomProducer.nonempty_strongConcentratedPacketConsumption_of_nonsingleton
```

The local dispatch should construct `QuittingSameStageEndpointEdge` directly;
it must not call `quittingLiteralSameStage_dispatch` or
`quittingPartialPurification_then_sameStage_dispatch`, because both public
theorems still require `hlowTail`.  Reuse the existing literal gain, mover
debt, routed-mass, finite-dispatch, and closed-segment declarations.

For source provenance, retain the chosen `SelectedRows`, rank, actual
prefixed profile, marked date, pure sibling/orbit, terminal route, singleton
target, and produced strong packet in one dependent result.  Do not pretend
the output is an existing `FinFourLowTailRow` or a current weak-core
`.reached` value.

## Boundary tests and nonclaims

- `terminal.card >= 2` is essential to make every opponents-only Continue
  mass zero.  A pure singleton owner can expose the complete tail by
  Continuing.
- `D_* > 0` and `lambda > 0` are essential for serial **strict** edges and the
  uniform gain floor.
- Fin4, or the checked effective-support bound of four, is used to exclude a
  closed same-stage orbit.  The zero-transport lemma itself is valid for any
  finite player type.
- The initial simultaneous pure-root overwrite is not a unilateral profitable
  move.  No gain lower bound is claimed for it.
- The final terminal singleton route need not be a best response.  No gain
  lower bound is claimed for it.
- The theorem produces neither terminal approximants, a cumulative return,
  total-debt descent, nor a lower-rank regenerated source.
- It does not consume the strategic/atomic or collision-minimum arms of the
  strong concentrated-packet consumer.

