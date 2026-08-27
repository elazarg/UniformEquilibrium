# Universal self-tail contraction of the nonsingleton Fin4 minimum-law arm

Author: `ATLAS_FALSIFIER`

Independent reviews:

* [`ATLAS_GATEKEEPER`](../feedback/ATLAS_FALSIFIER__TAIL_ESCAPE_TWO_ANCHOR_REPAIR__BY_ATLAS_GATEKEEPER.md)
* [`STRENGTHENER`](../feedback/ATLAS_FALSIFIER__TAIL_ESCAPE_TWO_ANCHOR_REPAIR__BY_STRENGTHENER.md)

## Exact statement

Let `r` be a four-player quitting-game reward table and let

```text
source : FinFourMinimumAtomProducer r bound
```

be an actual Fin4 atlas source.  Thus `source` retains:

* a positive global minimum terminal-semantic point `z_*`, with
  `D_* := D(z_*) > 0`;
* an actual realizing chronology and arbitrarily deep literal exact cap-root
  prefixes whose front debts tend to `D_*`; and
* a finite terminal-law atom `S` of mass `mu>0` in the selected minimum law.

Assume `S` is nonsingleton.  Put

\[
 \lambda:=\mu^2/8>0.
\]

Then there exist:

1. one actual selected prefixed source profile `sigma` from the retained
   chronology;
2. one actual marked date `t` at which `S` has unconditional stage mass
   greater than `lambda`; and
3. one actual self-tail-closed profile `widehatSigma` obtained by copying the
   live roots of `sigma` through date `t` and, after all Continue at `t`,
   restarting the complete behavioral profile `sigma` from date zero,

such that:

\[
 \Pr_{\widehat\sigma}(S\text{ at }t)
 =\Pr_\sigma(S\text{ at }t)>\lambda,
\tag{1}
\]

\[
 \operatorname{tail}_{t+1}(\widehat\sigma)=\sigma
\quad\text{as complete behavioral profiles},
\tag{2}
\]

and

\[
 D(\sigma)-D_*<\lambda D_*/2.
\tag{3}

Consequently the existing raw Fin4 same-stage purification dispatch applies
to `widehatSigma` at `t`.  Its closed-monodromy alternative is impossible.
Therefore it produces an actual singleton endpoint with stage mass at least
`lambda`, retaining the literal post-date continuation `sigma` and the
external minimum-law source provenance.

Best-endpoint purification of a player distinct from that singleton owner
then produces a strong concentrated-singleton packet without mass loss.
Hence every nonsingleton Fin4 minimum-law source enters the same maintained
strong concentrated-singleton node as the singleton minimum-law arm.  The
old quantitative-tail-escape versus low-tail split is unnecessary.

When the source attachment is retained in the dependent packet, the checked
strong-packet consumer further yields

```text
(concentrated-singleton strategic dispatch
  and (static atomic-toggle handoff or exact player deletion))
or
source-attached collision-minimum residual.
```

This final displayed split is the existing
`FinFourStrongConcentratedPacketConsumerResult`; it is not strengthened here.

## Conjecture-facing change

This strictly narrows
[`FIN4_ATLAS_QUANTITATIVE_TAIL_ESCAPE.md`](../questions/FIN4_ATLAS_QUANTITATIVE_TAIL_ESCAPE.md)
and the nonsingleton arm of
[`FIN4_EXHAUSTIVE_PRODUCER_ATLAS.md`](../questions/FIN4_EXHAUSTIVE_PRODUCER_ATLAS.md):

\[
\boxed{
\text{nonsingleton minimum-law source}
\Longrightarrow
\text{source-attached strong concentrated-singleton node}.}
\]

In particular, quantitative tail escape is not an independent terminal leaf
of the Fin4 atlas.  This result does not consume the concentrated-singleton
node; it contracts the atlas to that common downstream obligation.

## Definitions and assumptions

A behavioral quitting profile specifies, at the unique live history at every
date, independent Quit/Continue laws for the four players.  A unilateral
behavioral deviation replaces one player's complete strategy.  Stage mass is
the unconditional probability of reaching the displayed date and realizing
the displayed nonempty quitting coalition there.

For any actual profile `sigma` and date `t`, define its self-tail closure by

\[
 \operatorname{Close}_t(\sigma)
 :=[x_0,\ldots,x_t]\triangleright\sigma,
 \qquad
 x_s:=\operatorname{root}_\sigma(s).
\tag{4}
\]

This is a finite literal root stack followed by the actual profile `sigma`.
It does not replace a profile by a semantic carrier representative.

No Nash property is asserted for the copied roots against the new
continuation.  The same-stage dispatch requires none.  It requires only the
fixed positive minimum point, a positive nonsingleton stage mass, and low
debt of the literal continuation strictly after the row.

## Source correspondence

The source data are checked in
`Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`:

* `QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows`;
* `SelectedRows.prefix_debt_tendsto`; and
* `SelectedRows.eventually_stageMass_gt_square_div_eight`.

The source wrapper and minimum identities are checked in
`Research/Quitting/FinFourProducerAtlas/Source.lean`:

* `FinFourMinimumAtomProducer`;
* `FinFourMinimumAtomProducer.minimumDebt_pos`; and
* `FinFourMinimumAtomProducer.debt_eq_inf`.

The raw consumer is
`quittingPartialPurification_then_finFourSameStage_dispatch` in
`Research/Quitting/FinFourSameStageEndpointMonodromy.lean`.  Its signature
does not require the base profile to be near-minimal, to belong to
`SelectedRows`, or to carry an exact cap-root stack.

The finite closed-segment obstruction is the separately reviewed result
[`FIN4_MONODROMY_PRODUCER_IMPOSSIBLE`](FIN4_MONODROMY_PRODUCER_IMPOSSIBLE.md),
whose proof uses only the raw dispatched trace.  The positive-stage packet
adapter is in `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`
and `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`.
The exact downstream split is
`FinFourSingletonStageStrongConcentratedPacket.consumerResult` in
`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`.

The literal prefix operations used below are checked through:

* `quittingLiteralRootStackProfile` in
  `UniformEquilibrium/Quitting/Root/LiteralExactPrefixStack.lean`;
* `quittingProfileLiveRoot_rootThenContinuation_zero` and
  `quittingProfileLiveRoot_rootThenContinuation_succ` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
* `shiftProfile_quittingRootThenContinuationProfile` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`;
* `quittingStageCoalitionMass_rootSequence_eq_of_prefix` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticElementaryTailCompression.lean`;
  and
* `quittingTerminalSemanticPair_eq_of_liveRoot_eq` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`.

No existing declaration states the self-tail closure or eliminates the
high-tail leaf by this composition.

## Proof

### 1. Exact self-tail identities

Let `Close_t(sigma)` be (4).  Induction over the finite root stack gives

\[
 \operatorname{root}_{\operatorname{Close}_t(\sigma)}(s)
 =\operatorname{root}_\sigma(s)
 \qquad(0\le s\le t).
\tag{5}

Stage mass at `t` is the product of joint survival through dates `<t` and
the current root's coalition mass.  Both factors are equal by (5), so for
every nonempty coalition `A`,

\[
 \Pr_{\operatorname{Close}_t(\sigma)}(A\text{ at }t)
 =\Pr_\sigma(A\text{ at }t).
\tag{6}

Iterating `shiftProfile_quittingRootThenContinuationProfile` through the
`t+1` copied roots gives the stronger full-profile identity

\[
 \operatorname{tail}_{t+1}operatorname{Close}_t(\sigma)=\sigma.
\tag{7}

Thus the post-date prescribed payoffs and unrestricted behavioral caps agree
exactly—not by continuity, but because the complete behavioral profiles are
equal.  For every reference `Dref`,

\[
 \operatorname{SpineDebtExcess}
  (\operatorname{Close}_t(\sigma),Dref,t+1)
 =D(\sigma)-Dref.
\tag{8}

### 2. Select one actual source row

Apply `nonempty_selectedRows` to the nonsingleton atom.  Let `sigma_n` be the
retained prefixed profiles and `t_n` their shifted marked dates.  With
`lambda=mu^2/8`, the selected-row estimates give eventually

\[
 \Pr_{\sigma_n}(S\text{ at }t_n)>\lambda,
\tag{9}

and

\[
 D(\sigma_n)\longrightarrow D_*.
\tag{10}

Since `lambda D_*/2>0`, choose one sufficiently late `n` satisfying (9) and

\[
 D(\sigma_n)-D_*<\lambda D_*/2.
\tag{11}

Set

\[
 \widehat\sigma_n=\operatorname{Close}_{t_n}(\sigma_n).
\]

Equations (6), (8), (9), and (11) are exactly (1)--(3).

### 3. Apply the raw same-stage dispatch

Use `minimum=source.point.1`, `baseProfile=widehatSigma_n`, `stage=t_n`,
`lambda=mu^2/8`, and the retained nonsingleton coalition `S` in
`quittingPartialPurification_then_finFourSameStage_dispatch`.

The hypotheses are:

* carrier membership and global minimality of the fixed minimum;
* `D_*>0`;
* `lambda>0`;
* stage mass at least `lambda`, from (1); and
* spine excess less than `lambda D_*/2`, from (2)--(3).

The theorem returns either a singleton during bounded partial purification,
or complete purification followed by a terminal singleton or a closed
same-stage segment.  The raw closed segment is impossible by the Fin4
monodromy theorem.  Therefore an actual singleton endpoint remains.  Every
same-stage update preserves the complete tail after `t`, and the dispatch
retains the stage-mass floor.

### 4. Enter the common concentrated node

At the singleton endpoint, select any different player and replace only that
player's marked action by its better exact endpoint against the same literal
tail.  The positive-stage strong-packet theorem routes the atom without mass
loss, makes that coordinate's local defect zero, and packages the constant
sequence as a strong concentrated-singleton packet.

Keeping the new self-tail origin as a dependent field preserves the minimum
source, selected row, copied marked past, and exact near-minimum post-date
tail.  The checked strong-packet consumer can then be applied to this same
source and packet.

## Boundary tests

### No anchors are needed for the raw contraction

Changing the continuation may move the semantic pair of the repaired whole
profile by order one.  This does not affect the proof because the raw
same-stage theorem does not assume whole-profile near-minimality or old-root
cap-Nash exactness.  The declared continuation alone is literally
near-minimal.

### Two anchors give a stronger optional conclusion

If two distinct players' Continue probabilities at the marked row tend to
zero, then after every unilateral deviation at least one near-sure quitter
remains.  A direct coupling gives convergence of the repaired whole-profile
semantic debts to `D_*`.  On Fin4, if their Continue probabilities are
`c_a,c_b` and rewards are bounded by `M`, the sharper bound is

\[
 |D(\widehat\sigma)-D(\sigma)|
 \le2M(c_a+c_b+6c_ac_b).
\]

With two sure quitters the semantic and terminal-law equalities are exact.
This stronger statement is not needed for the atlas contraction.

### One anchor does not stabilize the whole cap

With one sure quitter `a`, let another player `b` Continue at the marked row.
Give `a` payoff zero at `{a}` and one at `{b}`.  Replacing an all-Never tail
by a tail where `b` quits surely leaves prescribed absorption at the marked
row unchanged, but after `a` deviates to Continue its payoff changes by one.
Thus a single sure quitter cannot control the repaired whole profile against
all behavioral deviations.  This does not affect the raw contraction.

## Adapter and consumer

The actual-data adapter starts from every nonsingleton
`FinFourMinimumAtomProducer`, selects one retained row, and constructs its
literal self-tail closure.  It does not assume a `TailEscapeSubsequence`.

The immediate consumer is the existing raw same-stage dispatch plus the
finite monodromy impossibility.  The surviving actual singleton enters the
strong concentrated packet and its checked strategic-versus-collision-
minimum consumer split.

The current Lean wrappers store `low : FinFourLowTailRow source`.  The
self-tail-closed profile is not a member of the original `SelectedRows`
family and must not be falsely put in that structure.  Formalization needs a
smaller actual-row passport containing only the fields used by the raw
dispatch, with a separate dependent origin retaining the selected source and
self-tail equality.

## Lean handoff

1. Define `quittingSelfTailClosure reward profile stage` using the first
   `stage+1` live roots and `quittingLiteralRootStackProfile`.
2. Prove exact live-root equality through `stage`, exact stage-mass equality,
   and exact full-profile spine equality at `stage+1`.
3. Define a raw `FinFourActualLowTailRow` carrying: actual profile, stage,
   positive scale, nonsingleton coalition, mass floor, and low-tail bound.
4. Add adapters from both the existing `FinFourLowTailRow` and a selected
   self-tail closure.  Retain source provenance outside the raw passport.
5. Generalize or parallelize the bounded purification endpoint wrappers over
   the raw passport.
6. Apply the raw closed-segment impossibility and package the surviving
   singleton endpoint with its self-tail origin.
7. Compose with the checked strong-packet constructor and
   `FinFourSingletonStageStrongConcentratedPacket.consumerResult`.

Do not copy the old cap-stack exactness field to the repaired profile: it may
be false after the tail change and is unused.

## Scope and nonclaims

The theorem does not prove that:

* the repaired whole profile or final singleton target is near-minimal;
* the copied roots remain cap-Nash against the changed continuation;
* the original escaped post-row tail is retained;
* terminal-law mass is current exact-root absorption;
* the strong concentrated packet is consumed into terminal approximants,
  an admissible return, semantic descent, or a uniform-equilibrium payoff; or
* Fin4, or the general finite-player conjecture, is settled.

Its exact content is a source-faithful reduction of the entire nonsingleton
minimum-law arm to the one remaining concentrated-singleton node.

## Formalization record

The maintained realization adds two generic production modules and three new
or modified Research atlas modules, composed with the existing Research atlas
machinery.  The generic self-tail layer is production-reachable; the complete
atlas contraction is reachable through the Research reader umbrella.

1. `UniformEquilibrium/Quitting/Root/SelfTailClosure.lean` defines
   `quittingSelfTailRootStack` and `quittingSelfTailClosure`.
   `quittingProfileLiveRoot_selfTailClosure_eq_of_le` proves exact equality of
   every copied live root through the marked date, while
   `quittingAllContinueProfileSpine_selfTailClosure` proves the stronger
   literal equality of the complete post-date `BehaviorProfile` to the input
   profile.  This is not merely live-root, terminal-law, or semantic equality.
2. `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSelfTailClosure.lean`
   proves the exact semantic projections.
   `quittingStageCoalitionMass_selfTailClosure` preserves every unconditional
   coalition atom at the marked date,
   `quittingTerminalSemanticPair_spine_selfTailClosure` preserves the complete
   post-date semantic pair, and `quittingSpineDebtExcess_selfTailClosure`
   identifies post-date excess with the original profile's total debt minus
   the fixed reference.
3. `Research/Quitting/FinFourProducerAtlas/ActualLowTail.lean` defines the
   minimal raw passport `FinFourActualLowTailRow` and the exact adapter
   `FinFourLowTailRow.toActualLowTailRow`.  The theorem
   `FinFourActualLowTailRow.nonempty_singletonEndpoint_or_closedSegment`
   invokes the existing raw same-stage dispatch on the passport's actual
   profile, date, scale, coalition, mass floor, and fixed source minimum.

   Every surviving `FinFourActualLowTailSingletonEndpoint` stores the literal
   `postDateSpine_eq` equality of complete behavioral profiles.  Its dependent
   `FinFourActualLowTailSingletonOrigin` records whether the endpoint arose
   during bounded partial purification or from the completed terminal orbit.
   The common accessors `state`, `steps`, `path`, `steps_le_four`, `mover`,
   `action`, `sourceCoalition`, `routeSourceProfile`, `singleton_eq_routed`,
   `route_mass_le`, and `singleton_card` expose the actual path and routed atom
   rather than a supplied endpoint certificate.
4. `Research/Quitting/FinFourProducerAtlas/SelfTailContraction.lean` constructs
   the packet's selected row and contracts its raw dispatch.  The declarations
   `SelectedRows.eventually_finFourSelectedSelfTailPassport` and
   `SelectedRows.exists_cutoff_finFourSelectedSelfTailPassport` select the mass
   and debt estimates simultaneously from one fixed selected-row family.
   `FinFourMinimumAtomProducer.nonempty_selectedSelfTailRow` and
   `FinFourMinimumAtomProducer.nonempty_selfTailLowRow` retain the same source,
   minimum point, atom, chronology, selected family, and rank.

   For the resulting `FinFourSelfTailLowRow`,
   `stageMass_eq_selectedStageMass` is the literal marked-mass equality,
   `lambda_lt_stageMass` gives the strict `mu^2 / 8` floor, `lowTail` gives the
   exact strict debt threshold, and `fullSpine_eq_selectedProfile` gives the
   complete restarted behavioral profile.  After raw dispatch and monodromy
   elimination, `FinFourSelfTailLowRow.nonempty_singletonEndpoint` produces an
   actual singleton.  The declaration
   `FinFourSelfTailSingletonEndpoint.postDateSpine_eq_selectedProfile` composes
   the endpoint's preserved post-date spine with the original selected
   prefixed profile without reselecting chronology.

   `FinFourSelfTailLowRow.nonempty_strongConcentratedPacketConsumption` then
   constructs a no-loss strong concentrated packet and applies the existing
   exact strategic-versus-collision-minimum consumer.
   `FinFourMinimumAtomProducer.nonempty_nonsingletonSelfTailConsumption` is the
   source-level nonsingleton adapter.  The exhaustive cardinality split
   `FinFourMinimumAtomProducer.nonempty_contractedConsumer` joins it with the
   already checked singleton-clock route, so every minimum atom reaches one
   `FinFourMinimumAtomContractedConsumer`.  The route-tagged value retains the
   construction origin; `FinFourMinimumAtomContractedConsumer.consumerResult`
   is deliberately the forgetful projection to an actual strong packet and
   its `FinFourStrongConcentratedPacketConsumerResult`.
5. `Research/Quitting/FinFourProducerAtlas/Source.lean` proves
   `FinFourMinimumAtomProducer.exists_residual_eq_of_hardResidual`, retaining
   literal equality between a constructed source and the supplied hard
   residual.  The provenance-rich adapters
   `exists_finFourMinimumAtomContractedConsumer_of_hardResidual` and
   `uniformPayoff_or_exists_finFourMinimumAtomContractedConsumer_withResidualProvenance`
   preserve that equality through the source-attached contraction.  Their
   corresponding forms
   `exists_finFourMinimumAtomContractedConsumerResult_of_hardResidual` and
   `uniformPayoff_or_exists_finFourMinimumAtomContractedConsumerResult_withResidualProvenance`
   retain the exact bounded-data source and residual while forgetting only the
   route tag.
6. `Research/Quitting/SameStageEndpointMonodromyImpossible.lean` supplies
   `not_nonempty_finFourSameStageEndpointClosedSegment`, which removes the raw
   dispatch's only nonsingleton output.  The strong packet and its unchanged
   final split are supplied by
   `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean` and
   `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`.
   `Research/Quitting/FinFourExhaustiveProducerAtlas.lean` remains the atlas
   reader, and `Research.lean` imports the new raw and contracted interfaces.

Evidence seals:

- **M:** PASS.  The simultaneous cutoff selection, exact self-tail identities,
  strict positive `mu^2 / 8` scale, raw dispatch, finite-monodromy elimination,
  no-loss packet construction, and common cardinality split match the reviewed
  mathematical proof.
- **L:** PASS.  The production self-tail modules, `Source`, `ActualLowTail`,
  `SelfTailContraction`, their dependent atlas modules, the production and
  Research reader umbrellas, and `AxiomAudit` check in Lean.  At promotion,
  the full `lake build` completed 10,929 jobs.  The generated documentation
  and axiom-audit checks, import graph and its eleven regression tests, trust
  scan, proof-duplicate scan, derivable-telescope scan, source line-length and
  forbidden-term checks, and diff hygiene all passed.  Targeted axiom prints
  use only `propext`, `Classical.choice`, and `Quot.sound`.
- **A:** PASS.  Every nonsingleton `FinFourMinimumAtomProducer` selects one
  actual retained row, forms its literal self-tail closure, runs the raw
  same-stage dispatch, and constructs the strong packet.  The hard-residual
  and arbitrary bounded-data adapters retain literal source/residual equality;
  no high/low row, singleton endpoint, path, packet, or consumer result is
  accepted as a supplied certificate.
- **C:** PASS through the exact source-attached contracted strong-packet
  consumer.  Both singleton and nonsingleton minimum atoms reach the same
  `FinFourStrongConcentratedPacketConsumerResult`: either the maintained
  strategic dispatch with its atomic-toggle or exact-deletion handoff, or the
  unchanged source-attached collision-minimum residual.  This seal does not
  consume that collision residual.

Nonclaims:

- the self-tail-closed profile and dispatched singleton target are not proved
  near-minimal or full-root Nash, and copied roots are not proved cap--Nash
  against the changed continuation;
- the old escaped post-row continuation is intentionally replaced by the
  selected profile itself; the theorem preserves the new literal full spine,
  not the discarded tail;
- no terminal-law mass is identified with current exact-root absorption, and
  no exact minimum profile is hidden inside the asymptotic chronology;
- no return, regeneration, recurrence, source-rank descent, backward compiler,
  terminal approximation, atlas-completion closure, or chronology reselection
  is produced;
- the collision-minimum arm remains open; and
- no new uniform-equilibrium payoff is obtained in the residual arm, so neither
  the Fin4 nor the general finite-quitting conjecture is settled.

The mathematical provenance remains this packet and the independent
`ATLAS_GATEKEEPER` and `STRENGTHENER` reviews linked at its head.
