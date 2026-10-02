# Source audit: vanishing Jensen selection and whole-source return

Reviewer: `GATE_SOURCE_AUDIT`

Target connection: `Vanishing-Jensen selection into the whole-source return
seam` in
[`GATE_SOURCE_AUDIT__CHRONOLOGY_NOTE_MINING.md`](../notes/GATE_SOURCE_AUDIT__CHRONOLOGY_NOTE_MINING.md).

Primary records inspected:

- [`SERIAL_ENDPOINT_AUDITOR__VANISHING_JENSEN_CLOCK_COMPRESSION.md`](../notes/SERIAL_ENDPOINT_AUDITOR__VANISHING_JENSEN_CLOCK_COMPRESSION.md);
- [`ATLAS_GATEKEEPER__COLLISION_MINIMUM_WHOLE_SOURCE_RETURN_SEAM.md`](../notes/ATLAS_GATEKEEPER__COLLISION_MINIMUM_WHOLE_SOURCE_RETURN_SEAM.md);
- [`SERIAL_ENDPOINT_AUDITOR__SUFFIX_CLOSED_PASSPORT_OCCUPATION_NOGO.md`](../notes/SERIAL_ENDPOINT_AUDITOR__SUFFIX_CLOSED_PASSPORT_OCCUPATION_NOGO.md);
- the three direct reviews of the Jensen note; and
- the later anchored Jensen and mass-good localization notes and their review.

## Verdict

**The conditional Jensen selection is sound, but the proposed connection is
not yet a composition theorem.**  The current fixed-source/cofinal singleton
machinery supplies the two inputs

1. actual reference profiles whose total debt tends to the global minimum;
2. a fixed positive singleton tail-mass floor on the same retained chronology;

but it does **not** supply vanishing Jensen loss.  Nor does a selected
near-minimum deterministic-clock component automatically supply the
whole-source field required by the collision return compiler after the marked
row is exactified or forced to a pair.

Persistent positive Jensen curvature has an exact response-switch/paid-row
decoder and can enter the checked paid-cap trichotomy.  It has no exhaustive
terminal consumer retaining the minimum source and marked atom.  Thus the
central issue remains a genuine theorem, but it has two distinct parts:

1. produce vanishing Jensen loss, or consume persistent positive loss while
   retaining mass and minimum provenance; and
2. turn the resulting near-minimum singleton component into the exact
   near-minimum collision packet source required by the whole-source
   compiler, without cross-coordinate cap leakage.

The phrase “selection into the whole-source return seam” currently hides the
second part.  No export is recommended.

## 1. Exact valid conditional theorem

Let `D_*` be the global minimum of total terminal-semantic debt on the
carrier, with `D_*>0`.  Let `S_n` be actual profiles such that

\[
 D(S_n)\longrightarrow D_*,
\]

and fix one owner `j`.  At a finite anchor `a_n`, condition the owner's
post-anchor stopping law on survival to the anchor.  Denote the resulting
law on finite clocks and `Never` by `alpha_n`.  For a finite clock `t`, let
`P_(n,t)` copy the complete source before the anchor, make `j` Continue from
the anchor through `t-1` and Quit at `t`, restore its source behavior after
`t`, and leave every opponent unchanged.  Define `P_(n,infinity)` similarly
using Never after the anchor.

For every player `i`, prescribed payoff is affine in this conditional
stopping-law decomposition.  The owner's cap is identical at all components.
For every outsider, every fixed complete behavioral deviation payoff is
affine, so the unrestricted cap is convex.  Hence the countable Jensen loss

\[
 J_n:=\int D(P_{n,t})\,d\alpha_n(t)-D(S_n)
\]

is nonnegative and equals the sum of the three outsider cap Jensen gaps.

Suppose the anchored singleton mass has a uniform floor `mu>0`, and put

\[
 G_n=\{t<\infty:
       \Pr_{P_{n,t}}(\{j\}\text{ absorbs at }t)\ge\mu/2\}.
\]

The stopping-law mass ledger gives

\[
 \alpha_n(G_n)\ge {\mu\over 2-\mu}\ge {\mu\over2}.
\]

Since every component is an actual profile, global minimality gives
`D(P_(n,t))>=D_*`.  Therefore

\[
 \int (D(P_{n,t})-D_*)\,d\alpha_n(t)
   =D(S_n)-D_*+J_n.
\]

If `J_n -> 0`, a supported finite `t_n in G_n` can be selected so that

\[
 D(P_{n,t_n})-D_*
 \le {2\over\mu}\bigl(D(S_n)-D_*+J_n\bigr)\longrightarrow0.
\]

Thus the same actual component has whole debt tending to `D_*` and a fixed
unconditional singleton stage-mass floor.  At its marked sure-Quit root,
global positivity of `D_*` gives one root-defect coordinate of size at least
`D_*/4`.  The owner case uses Continue followed by an unrestricted
approximately optimal tail response; every outsider case is screened by the
sure quitter.  Reached-row localization gives an actual whole-profile gain
at least `mu*D_*/16`, after a subsequence fixing the gaining player.

This is a genuine simultaneous-selection theorem.  It is stronger than the
checked mass-only clock compression.  It is not presently a Lean declaration.

Two repairs to the original note remain mandatory:

- `D_*` must be stated as the global carrier minimum, not merely the limit of
  `D(S_n)`;
- the profile-mixture notation must be read as exact payoff/law expectation
  identities, not literal vector-space equality of behavioral profiles.

The note's old whole-word-square paragraph is not proved.  The later
two-clock/two-response switch argument is the valid replacement.

## 2. What the current fixed-source chronology really supplies

The source attachment is exact up to the Jensen premise.

`FinFourMinimumAtomChronology.prefix_debt_tendsto` in
`Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`
gives minimum convergence for the literally prefixed **reference profiles**.
`FinFourMinimumAtomChronology.tendsto_prefixedTailMass` gives the positive
singleton tail mass on that same source chronology.  Passing to any strict
cofinal refinement preserves both statements.

The newer common interface makes the separation especially explicit.
`FinFourSourcePreservingCofinalSingletonPacket` in
`Research/Quitting/FinFourProducerAtlas/SourcePreservingSingletonFrames.lean`
stores:

- `referenceDebt_tendsto` for `frame.referenceProfile`; and
- `resolution_le_stageMass` for `frame.targetProfile`.

There is no target-debt convergence field.  Its two facts concern different
actual profiles.  Likewise:

- `FinFourOwnerCompressedSingletonEndpoint.targetProfile_ownerCap_eq`
  preserves only the compressed owner's unrestricted cap;
- `targetProfile_other_eq` preserves opponents' prescribed strategies, not
  their caps; and
- `rootStack_nash` remains certified only over the unmodified source suffix.

This is exactly the cap-Jensen seam.  The fixed-source/cofinal construction
does not imply `J_n -> 0`, and none of its declarations bounds the sum of the
other three target caps by `o(1)`.

The two-date timing-match regression in the Jensen reviews confirms the
logical independence at minimum value zero: a zero-debt mixed-clock source
can have positive singleton mass while each relevant deterministic component
lies a fixed distance above the minimum.  It is not a positive-minimum
counterexample, but it prevents deriving vanishing Jensen loss from affinity,
minimum provenance, and singleton mass alone.

## 3. Why the selected clock does not yet satisfy whole-source return

The checked collision compiler
`ConcentratedCollisionFourRole.packet_eventually_tailEscape_or_threeRoleTransfer`
in `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean` requires

\[
 D(\text{actual packet profile}_n)\longrightarrow D_*.
\]

It also requires a nonsingleton terminal and a packet owner whose normalized
marked defect vanishes.  The Jensen-selected `P_(n,t_n)` has a singleton row
and a positive executable defect.  It is not yet that packet.

There are two natural attempts, and neither is justified:

1. Keep `P_(n,t_n)` as packet source.  Then the marked owner-defect condition
   need not vanish.
2. Change one player's marked action to an exact best endpoint, or force the
   hard-residual singleton-to-pair join.  This gives the required zero marked
   coordinate and nonsingleton row, but changes that player's prescribed
   strategy.  Its own cap is fixed and its own debt drops exactly; the other
   three unrestricted caps can rise by order one.  Therefore near-minimality
   of `P_(n,t_n)` does not imply near-minimality of the modified pair profile.

The checked source-preserving forced-pair module states this limitation in
its file contract: it asserts no target-side near-minimality or return.
`FinFourSourcePreservingForcedPairPacket.payerTargetDebt_eq_sourceDebt_sub_gain`
controls only the mover coordinate.  The complete post-date tail and law are
preserved, but two sure quitters screen that tail from the whole semantic
pair, so a tail repair cannot correct the new cross-coordinate caps.

Consequently the conditional Jensen theorem reaches a stronger singleton
node, not the `(SR)` field of the older whole-source collision seam.  A new
cross-coordinate estimate or a different singleton consumer is still needed.

## 4. Positive Jensen curvature is decoded but not closed

If `liminf J_n>0`, finite-player pigeonhole fixes an outsider with positive
Jensen contribution.  Selecting approximately optimal pure times gives two
supported clocks and a two-response switch.  Even when the Jensen mass first
appears on the `Never` component, source optimality forces an oppositely
oriented finite-clock switch.  The exact pure-time first-disagreement theorem
therefore produces an actual paid row on a finite deterministic-clock
component.

This uses unrestricted behavioral caps: pure times, arbitrarily late times,
and Never are the exact extremal class for terminal best responses.  The
owner-clock replacement and outsider response commute, and all four corners
are actual profiles on a common outer rank.

There are checked downstream operations:

- `exists_pureTimeWitnessSwitchCertificate_of_abs_envelopeCurvature` decodes
  envelope curvature;
- `QuittingPureTimeWitnessSwitchCertificate.exists_paidFirstDisagreementRow`
  produces the paid row;
- `QuittingPaidCapLiftedSource.exactTrichotomy` returns charged near-return,
  quantitative descent, or inert stall.

This is only a partial consumer.  The charged arm has a uniform-payoff
consumer, but the other two arms do not retain a well-founded minimum-source
rank or eliminate inertness.  In addition, the positive-Jensen switch may
live on a mass-poor, uniformly off-minimum clock.

The current source-attached response-chord machinery does not fill that gap.
`FinFourMinimumResponseRectanglePacket` requires one common subsequence on
which both its endpoint and response joint semantic/law points lie on the
minimum fibre, together with a marked mass floor.  The Jensen switch supplies
neither minimum identity for its receiver nor a mass floor on that receiver.
The mass-good localization theorem can force the square or paid row onto a
mass-good clock, but that clock is then in the uniformly off-minimum arm.

There is also a checked obstruction to a tempting shortcut.  If near-minimum
actual profiles are merely fed into generic paid-cap lifts, then
`QuittingPaidCapLiftedSource.totalAbsorption_tendsto_zero_of_initialDebt_tendsto_minimum`
and
`not_eventually_chargeFloor_le_totalAbsorption_of_initialDebt_tendsto_minimum`
in `Research/Quitting/PaidRowCapPortDispatch.lean` show that no fixed positive
cap-lift absorption charge survives.  The paid gain may remain fixed while
the admissible prefix charge vanishes.

Thus “positive curvature has a consumer” is true only in the weak sense of a
checked trichotomy.  It is false in the conjecture-facing sense needed here.

## 5. Provenance audit

### Actual profiles

The conditional components are actual behavioral profiles.  The stopping-law
integral is used only for payoff, law, and cap inequalities.  No barycentre is
substituted as a behavioral profile.

### Common subsequence

For every outer rank, the mass and debt selection concerns one clock
component of that rank.  A strict refinement can freeze the gaining player
and all finite labels while preserving source-rank cofinality.  What is not
preserved automatically is minimum convergence after a later endpoint or
pair modification.

### Minimum

Global minimum provenance is essential because it makes every component
excess nonnegative.  Merely assuming `D(S_n)->D_*` is insufficient.

### Atom

The selected finite component carries the advertised unconditional singleton
stage mass on the same actual profile.  A later outsider response or pair
forcing may route or destroy the singleton label; any downstream interface
must store the routed mass explicitly.

### Unrestricted caps

The Jensen inequality ranges over all complete behavioral deviations.  It is
not a stationary or bounded-horizon calculation.  Existing pure-time
extremality justifies approximate response selection including Never.  Only
the owner's cap is invariant under clock replacement; no invariance claim is
available for the other three coordinates.

## 6. Exact source correspondence

Checked ingredients:

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `quittingTerminalPayoff_eq_expect_behaviorStoppingLaw_pureTime` and
  `quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect` in
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- binary payoff affinity, cap convexity, and debt convexity in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`;
- `FinFourMinimumAtomChronology.prefix_debt_tendsto` and
  `.tendsto_prefixedTailMass` in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
- `FinFourSourcePreservingCofinalSingletonPacket.referenceDebt_tendsto` and
  `.resolution_le_stageMass` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingSingletonFrames.lean`;
- source-preserving pair, mass, tail, and coordinate-debt facts in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingForcedPair.lean`;
- `ConcentratedCollisionFourRole.packet_eventually_tailEscape_or_threeRoleTransfer`
  in `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`; and
- the paid-cap charge-collapse theorems in
  `Research/Quitting/PaidRowCapPortDispatch.lean`.

No checked declaration was found for the countable anchored Jensen ledger,
the simultaneous mass/near-minimum clock selection, vanishing Jensen loss on
the Fin4 source chronology, or the pair-exactification cap-leakage bound.

## 7. Precise remaining theorem

A valid conjecture-facing connection must prove an exhaustive alternative
from the fixed Fin4 minimum-singleton chronology:

1. produce deterministic-clock components with fixed singleton mass and
   whole debt tending to `D_*`, then either consume them directly or convert
   them to a collision packet whose **modified whole-profile** debt still
   tends to `D_*`; or
2. from persistent positive Jensen loss, produce a source-attached terminal
   output, renewable finite-rank descent, or charged return while retaining a
   common mass/minimum/response subsequence.

Proving only `J_n->0 => near-minimum component` is a useful conditional
selection theorem.  Proving only `J_n` positive implies a paid row duplicates
an already consumable local object.  Neither alone is the missing
whole-source return theorem.

## Final recommendation

Keep this as a narrow producer question, not an export candidate.  If the
conditional Jensen selection is formalized, its interface should stop at the
actual near-minimum singleton component and explicitly expose the untouched
source rank, anchor, clock weight, stage mass, and unrestricted-cap Jensen
loss.  It should not claim a collision return until the pair-modification
whole-debt estimate is proved.
