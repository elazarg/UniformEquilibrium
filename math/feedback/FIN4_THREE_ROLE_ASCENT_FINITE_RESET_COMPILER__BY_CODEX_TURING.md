# Independent source and proof-completeness audit of the finite reset compiler

Reviewer: `CODEX_TURING`

Repository state inspected: `fed13ea9615c70f37a20c368e82053695b2b89a4`.

## Verdict

The finite-deadline reset-arrival argument is correct.  It supplies a new
ordinary-mathematics producer from every actual behavioral profile in a
finite quitting game with a positive uniform terminal debt floor.  A terminal
exploitability gap gives exactly that floor.  Its output is one actual profile
with an attained zero-debt coordinate and positive incidence from a distinct
player.  Literal realizability then supplies every input of the checked
`QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch`.

For the Fin4 three-role endpoint, this is a same-reward, same-minimum-source
transition beginning at one retained actual endpoint target.  It answers item
4, not item 3, of
`questions/FIN4_THREE_ROLE_TARGET_ASCENT_CONSUMER.md`.  The fixed mover,
recipient, routed terminal, endpoint row, and finite update path are retained
as provenance.  The final reset law need not equal the endpoint limit law and
the path does not transport a downstream conclusion backward through
profitable deviations.

I found no mathematical counterexample or missing hypothesis.  Before export,
the packet should make the small statement corrections listed below and add
the finite nonnegative-law argument currently compressed into the phrase
“the law is exactly the singleton law.”

## Strongest exact statement supported by the proof

The terminal-gap hypothesis is stronger than the reset-arrival proof needs.
Let `I` be a finite player type with decidable equality, let `reward` be an
arbitrary finite-quitting reward table, and let `gamma > 0`.  Assume

```text
for every actual behavioral profile sigma,
there is i with gamma <= d_i(sigma).
```

Then, from every actual start profile, there is a finite list of literal
unilateral updates to deterministic Quit times or Never,

```text
sigma_(k+1) = sigma_k[i_k <- Q_(i_k)(t_k)],
```

ending at an actual profile `pi` and distinct players `q,j` such that

```text
d_q(pi) = 0,
0 < quittingTerminalOpponentIncidenceMass q j (law(pi)).
```

The candidate's `HasTerminalExploitabilityGap reward gamma` implies this
coordinate-debt floor: its behavioral witness has gain at least `gamma`, and
`quittingTerminalPayoff_update_sub_le_terminalSemanticDebt` bounds every such
gain by the original semantic debt.  Thus the candidate theorem follows.

This strengthening matches the checked
`HasQuittingUniformTerminalDebtFloor` interface and should be the general
headline lemma.  A second adapter can state that every
`HasTerminalExploitabilityGap` supplies the floor.  The Fin4 endpoint theorem
is then a corollary, not the source of the reset-arrival result.

## Audit of the general proof

### Near-best pure-time phase

The unrestricted envelope is genuinely over all behavioral deviations:
`quittingContinuationBestResponseValue` is the supremum over complete
behavior strategies.  The theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` identifies that
supremum exactly with the supremum over `Option Nat` pure times.  Hence an
arbitrarily accurate pure time exists.

Changing only player `i` leaves that player's envelope unchanged by
`quittingContinuationBestResponseValue_update_self`.  Equivalently,
`quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain` gives the exact
debt/payoff telescope.  Therefore a pure-time response within `error` of the
cap leaves debt at most `error` and gains at least `gamma - error` whenever
the source debt is at least `gamma`.

This entire first phase is already checked, with a stronger finite-chain
interface, in `TerminalSemanticBoundedSelfReset.lean`:

- `exists_quittingPureTimeSelfResetStep`; and
- `exists_bounded_quittingPureTimeSelfResetChain`.

Taking `error = gamma / 4` produces, from every start, a finite pure-time
player whose displayed deadline is some `T`, whose debt is at most
`gamma / 4 < gamma`, and whose acquisition chain has length at most
`Fintype.card I + 1`.  Thus the candidate's “at most four Never updates and
then one finite update” is correct for `Fin 4`.  Reusing this declaration is
preferable to reproving the Never-set induction.

### Exact finite-deadline phase

Suppose `a` is literally prescribed `Q_a(T)` and `d_a < gamma`.  The debt
floor chooses `i` with `d_i >= gamma`, so `i != a`.

Against the unchanged opponents of `i`, every pure time strictly after `T`
has the same terminal payoff as Never: if play survives to `T`, player `a`
quits surely there; otherwise the game already stopped.  Consequently all
pure-time payoff values are represented by the finite list

```text
Never, 0, 1, ..., T.
```

Pure-time extremality now turns the behavioral envelope into the maximum of
this finite list.  Updating `i` to an exact maximizing representative leaves
its envelope fixed and makes its prescribed payoff equal to that envelope,
so its new debt is exactly zero.  Since `i != a`, the old finite stopper is
unchanged and the new profile still absorbs by time `T`.

If some `j != i` has positive incidence, this is the desired output.  In the
other arm, the proof should spell out the following finite-law step.

1. `quittingTerminalOutcomeMass_none_eq_zero_of_pureTimePlayer` makes the
   Never outcome have mass zero.
2. `quittingTerminalOutcomeMass_mem_stdSimplex` makes every terminal mass and
   every incidence summand nonnegative, with total mass one.
3. If every `j != i` has zero incidence, every nonempty terminal coalition
   containing such a `j` has mass zero.  The only remaining nonempty
   coalition is `{i}`.  Hence the complete law is `delta_{ {i} }`.

The exact maximizer cannot be Never, because
`quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero` makes every
coalition containing `i` have mass zero.  It also cannot be a finite time
`t >= T`: for `t > T`, the old stopper forces absorption before `i` quits; at
`t = T`, any surviving stage contains both `a` and `i`.  Either contradicts
unit mass on `{i}`.  Thus `t < T`, and the new zero-debt player is a finite
stopper at a strictly smaller natural deadline.

Induction on `T` is therefore well founded.  At `T = 0`, the distinct exact
responder is represented by Never or Quit-at-zero.  In either case the old
stopper `a` belongs to the time-zero terminal coalition with total probability
one, so its incidence relative to the responder is positive.  There is no
hidden limiting or compactness step in this phase.

The candidate's claim that each deadline-phase update gains at least
`gamma` is also correct: the source debt is at least `gamma` and exact
maximization makes the target debt zero, so the fixed-opponent debt telescope
identifies the gain with the entire source debt.

## Audit of the three-role attachment

The fields of `ConcentratedCollisionThreeRoleEndpointLaw` have the required
quantifiers and use actual common ranks:

- `source_tendsto` is convergence of the semantic pairs of
  `ConcentratedCollisionFourRole.packetProfile packet (endpoint.ranks n)`;
- `target_joint_tendsto` is joint convergence of the semantic pair and
  complete terminal law of the literal `targetProfile` at the same rank;
- `transfer_mover_eq`, `transfer_recipient_eq`, and `endpointAction_eq` retain
  fixed roles and the literal endpoint action;
- `terminalMass_floor` retains the routed terminal in the limiting complete
  law;
- `source_on_minimum_fiber`, `mover_drop`, and `recipient_rise` have exactly
  the debt statements used by the candidate.

For `Fin 4`, with

```text
D_* = D(source.point.1),
Delta = D(endpoint.targetPoint.1) - D_*,
eta = packet.resolution^2 * D_* / 64,
```

the hypotheses give `D_* > 0`, `Delta > 0`, and target recipient debt at
least `eta`.  The latter follows because `recipient_rise` lower-bounds the
target-minus-source recipient debt and the source-limit debt is nonnegative
at its carrier point.  Continuity of debt and debt sum along the two stored
limits permits one common retained rank `N` with

```text
D(sourceProfile_N) < D_* + Delta/4,
D_* + 3 Delta/4 < D(targetProfile_N),
3 eta/4 < d_recipient(targetProfile_N).
```

Thus the displayed finite ascent by more than `Delta/2` and the recipient
first-gain floor `eta/2 = packet.resolution^2 * D_* / 128` are correct.
Choosing approximation error
`min (eta/4) (gamma/4)` is legitimate because both entries are positive; the
recipient's updated debt is below `gamma`.  A finite choice enters deadline
descent immediately, while Never can be prepended to the bounded acquisition
phase.  Hence the first reset-path edge can indeed be fixed to the endpoint's
stored recipient.

The same rank should additionally be selected so that

```text
packet.resolution / 2 <
  quittingTerminalOutcomeMass reward targetProfile_N
    (some endpoint.routedTerminal).
```

This follows immediately from `target_joint_tendsto`,
`terminalMass_floor`, and `packet.resolution_pos`.  It should be an explicit
field of the handoff if the packet says that the chosen *actual* endpoint row,
rather than only the endpoint limit object, retains the routed atom.

## Audit of the fixed-law consumer

For the final actual profile `pi`, set

```text
target = quittingTerminalSemanticPair reward pi,
mass   = quittingTerminalOutcomeMass reward pi.
```

`quittingTerminalSemanticLawPoint_mem_carrier` gives literal joint-carrier
membership.  The reset-arrival conclusion supplies exact zero debt and
positive incidence.  `FinFourMinimumAtomProducer.minimum` and
`FinFourMinimumAtomProducer.minimumDebt_pos` supply the minimum and positive
source-debt assumptions.  Finally,
`source.residual.witness` is a
`QuittingTerminalExploitabilityWitness reward`.  Therefore the application of
`QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` is exact;
no target-law projection, source replacement, or extra sign hypothesis is
being smuggled in.

The destination `QuittingFixedLawResetDispatch` is still conditional data,
not a terminal Nash or uniform-payoff consumer.  Its `dynamic_exit` is an
absorbing positive-survival debt-lowering prefix or an all-Continue cap fixed
point.  The present theorem does not consume the latter arm.

## Corrections and strengthening required before export

1. Say item 4 of the target-ascent question, not item 3.
2. Replace “game-independent” by “arbitrary finite-player quitting-game” for
   the general theorem.
3. State the general theorem under
   `HasQuittingUniformTerminalDebtFloor`; give terminal exploitability as a
   short adapter.  This is the genuinely strongest proved hypothesis.
4. Reuse `exists_bounded_quittingPureTimeSelfResetChain` for finite-stopper
   acquisition and record its `card I + 1` bound.
5. Expand the nonnegative finite-law argument and the `t >= T` exclusion as
   above; these are proof details, not new assumptions.
6. Add the actual selected-row routed-law floor `resolution / 2`.
7. In the Lean-facing path wrapper, record positive path length before
   referring to its first edge, and define the first responder/gain fields
   without ellipses.
8. Call the pure-time list a forward transition or provenance path.  It is not
   a backward compiler for equilibria, near-returns, or uniform payoffs.
9. State explicitly that the final reset law and labels need not preserve the
   endpoint routed atom, mover, or recipient; those remain historical fields
   in the source-attached handoff.

There is a further useful corollary stronger than the endpoint application:
for every `FinFourMinimumAtomProducer source` and every actual start profile,
the same construction reaches a `QuittingFixedLawResetDispatch` attached to
`source.point.1`.  The strict three-role theorem should then add the selected
finite ascent row, routed-law floor, and recipient-first edge as provenance.
Strict ascent is needed for the finite-ascent field, but not for existence of
the reset dispatch itself.

## Source correspondence and novelty

Declarations inspected:

- `HasTerminalExploitabilityGap` in
  `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
- `quittingTerminalSemanticPair`, `quittingTerminalSemanticDebt`, and
  `quittingTerminalPayoff_update_sub_le_terminalSemanticDebt` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `quittingPureTimeBehaviorStrategy` and
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingContinuationBestResponseValue_update_self` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTightness.lean`;
- `quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`;
- `HasQuittingUniformTerminalDebtFloor`,
  `exists_bounded_quittingPureTimeSelfResetChain`, and
  `quittingTerminalOutcomeMass_none_eq_zero_of_pureTimePlayer` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticBoundedSelfReset.lean`;
- `quittingTerminalOutcomeMass` and
  `quittingTerminalOutcomeMass_mem_stdSimplex` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticMoment.lean`;
- the pure-time terminal-law disintegration lemmas in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTimeDisintegration.lean`;
- `quittingTerminalOpponentIncidenceMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDebtTransfer.lean`;
- `quittingTerminalSemanticLawPoint_mem_carrier` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- `QuittingFixedLawResetDispatch` and
  `QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
- `QuittingReprojectionConcentratedPacket` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`;
- `ConcentratedCollisionFourRole.targetProfile` in
  `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`;
- `ConcentratedCollisionThreeRoleEndpointLaw` in
  `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`; and
- `FinFourMinimumAtomProducer` and its `minimumDebt_pos` theorem in
  `Research/Quitting/FinFourProducerAtlas/Source.lean`.

The nearest checked result is bounded finite-stopper acquisition.  It does
not produce an exact zero-debt coordinate with distinct positive incidence.
The deadline descent is therefore new rather than a restatement.  No paper
claim or literature translation is used.

No Lean-check claim is made for the new deadline descent, reset-arrival
structure, or Fin4 wrapper.
