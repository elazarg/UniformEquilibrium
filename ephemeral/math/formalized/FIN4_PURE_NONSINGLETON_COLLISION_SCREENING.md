# Pure nonsingleton collision screening on Fin4

Author: external contribution supplied in conference

Independent reviews:

* [`ATLAS_GATEKEEPER`](../feedback/EXTERNAL__PURE_COLLISION_SCREENING__BY_ATLAS_GATEKEEPER.md)
* [`STRENGTHENER`](../feedback/EXTERNAL__PURE_COLLISION_SCREENING__BY_STRENGTHENER.md)

## Exact statement

Let `r` be a quitting-game reward table on `Fin 4`.  Let `z_*` be a global
minimum of total terminal-semantic debt on the terminal-semantic carrier:

\[
 D_*:=D(z_*)>0,
 \qquad
 D_*\le D(z)\quad\text{for every carrier point }z.
\tag{1}
\]

Let `sigma` be an arbitrary actual behavioral profile, let `t` be a date, and
let `S` be a nonempty coalition with

\[
 |S|\ge2,
 \qquad
 0<\lambda\le
 \Pr_\sigma(\text{the terminal coalition is }S\text{ at date }t).
\tag{2}
\]

Write

\[
 L:=\Pr_\sigma(\text{play is live at the start of date }t).
\tag{3}
\]

Then there is a finite family of actual profiles, all identical to `sigma` at
every date other than `t`, with the following properties.

1. The first profile replaces the root at `t` by the pure product root whose
   Quit set is exactly `S`.  Its `S`-mass at `t` is exactly `L`.
2. From that pure nonsingleton root, every profitable transition changes one
   player's action at date `t` to its exact best pure endpoint against the
   literal post-date continuation.  Each such transition has actual payoff
   gain

   \[
   g\ge \frac{LD_*}{4}\ge\frac{\lambda D_*}{4}>0,
   \tag{4}
   \]

   lowers the mover's unrestricted behavioral debt by exactly `g`, preserves
   the complete post-date continuation, and routes the marked stage mass
   without loss.
3. After at most three profitable transitions, a pure two-player coalition is
   reached.  Making either member Continue at the marked row then gives a
   literal singleton terminal coalition with unconditional stage mass exactly
   `L`.  This final pair-to-singleton route is not asserted to be profitable.

Equivalently, the pure nonsingleton row supplies the existing
`QuittingSameStageEndpointDispatch` relation with the stronger floor (4), but
without any tail-debt hypothesis.  The dispatched finite orbit cannot close
on an effective support of cardinality at most four, so it must reach the
singleton terminal predicate.

### Source-indexed atlas corollary

Let

```text
source : FinFourMinimumAtomProducer r bound
```

and assume its retained positive finite minimum-law atom `S` is
nonsingleton.  Put

\[
 \mu:=\Pr_{\text{selected minimum law}}(S)>0,
 \qquad \lambda_0:=\mu^2/8.
\tag{5}
\]

The retained causal selected-row family contains an actual row at which `S`
has stage mass greater than `lambda_0`.  Applying the local theorem produces,
on that same selected source, a literal singleton endpoint of mass at least
`lambda_0`.  Hence `source` produces a source-attached

```text
FinFourSingletonStageStrongConcentratedPacket
```

at resolution `lambda_0`, and the already checked `consumerResult` gives

```text
(concentrated-singleton strategic dispatch
  and (static atomic-toggle handoff or exact player deletion))
or
source-attached collision-minimum residual.
```

No high-tail/low-tail split, near-minimum selected row, self-tail closure, or
cap-Nash preservation is needed for this contraction.

## Conjecture-facing change

This strictly strengthens the atlas entrance proved in
[`FIN4_NONSINGLETON_MINIMUM_LAW_SELF_TAIL_CONTRACTION`](FIN4_NONSINGLETON_MINIMUM_LAW_SELF_TAIL_CONTRACTION.md).
The earlier route first chooses a near-minimum selected source and replaces
its continuation by an exact self-tail in order to satisfy the old low-tail
dispatch.  The present theorem proves that a pure nonsingleton row erases all
continuation debt by itself.  Therefore **every** positive-mass selected row
already enters the common source-attached strong concentrated-singleton node.

The earlier self-tail packet is not withdrawn or deleted.  Its exact restarted
continuation and near-minimum provenance are stronger data that may be useful
to a future consumer.  The new theorem supersedes it only as the minimal proof
of the nonsingleton atlas entrance.

The remaining Fin4 atlas obligation is unchanged: consume the strong
concentrated-singleton node, in particular its source-attached
collision-minimum arm, into terminal approximants, a positive cumulative
return, a regenerated well-founded descent, or an actual counterexample.

## Definitions and assumptions

A behavioral quitting profile specifies, at the unique live history at every
date, one independent Quit/Continue law for each player.  A unilateral
behavioral deviation replaces one player's complete behavioral strategy and
may use Never, an arbitrarily late stopping time, or an arbitrary randomized
stopping law.

For a terminal-semantic pair `z=(u,b)`, define

\[
 d_i(z):=b_i-u_i,
 \qquad D(z):=\sum_i d_i(z).
\tag{6}
\]

The cap `b_i` is the supremum over all unilateral behavioral deviations, not
only stationary or one-stage deviations.

For a coalition `C` and a player `i`, write

\[
 C\triangle\{i\}=
 \begin{cases}
 C\setminus\{i\},&i\in C,\\
 C\cup\{i\},&i\notin C.
 \end{cases}
\tag{7}
\]

At a pure root with Quit set `C`, define its membership-toggle defect

\[
 \delta_i(C)
 :=\max\{r_i(C),r_i(C\triangle\{i\})\}-r_i(C)
 =\bigl(r_i(C\triangle\{i\})-r_i(C)\bigr)_+.
\tag{8}
\]

For the empty coalition, the continuation payoff is used in the general
formula.  The proof below never exposes the empty coalition because every
screened source has at least two Quitters and the process stops at a pair.

The initial pure-root overwrite changes several players' marked marginals at
once.  It is an actual behavioral profile construction, not a unilateral
profitable deviation and not an exact Nash--Bellman edge.  Every later strict
edge is a literal unilateral one-date best-endpoint update.  The final
pair-to-singleton route is a literal one-date update but need not be a best
response.

## Source correspondence

### Existing exact semantic ingredients

The two checked arbitrary-root debt bounds are

```text
quittingRootCoordinateNashDefect_le_terminalSemanticDebt_prefix
quittingTerminalSemanticDebt_prefix_le_nashDefect_add_transport
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectCharge.lean`.
Their directions are exactly

\[
 \delta_i\le d_i(\text{prefix})
 \le\delta_i+\operatorname{OppCont}_i\,d_i(\text{tail}).
\tag{9}
\]

The specialized sure-quitter equality is

```text
quittingTerminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_sureQuitter
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticReachedRowDebtLocalization.lean`.

The literal profile, mass, payoff-gain, and own-debt identities are in
`Research/Quitting/SameStageEndpointMonodromy.lean`:

```text
quittingLiteralPureRootCoalitionProfile
quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass
quittingTerminalPayoff_literalOneDateProfile_bestEndpoint_gain_eq
quittingTerminalSemanticDebt_literalOneDateProfile_bestEndpoint_eq_sub_gain
QuittingSameStageEndpointEdge
QuittingSameStageSingletonRoute
exists_quittingSameStage_terminalRoute_or_closedSegment
```

The finite obstruction is checked in
`Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean`:

```text
quittingSameStageSingletonRoute_of_card_eq_two
sameStageEndpointTrace_false_of_effectiveSupport_card_le_four
not_nonempty_finFourSameStageEndpointClosedSegment
```

The generic positive-singleton adapter and its source-indexed consumer are
checked in
`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean` and
`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`:

```text
FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass
FinFourSingletonStageStrongConcentratedPacket.consumerResult
```

### Existing source producer

`FinFourMinimumAtomProducer` and its positive-minimum fields are checked in
`Research/Quitting/FinFourProducerAtlas/Source.lean`.  The literal selected
rows and their eventual nonsingleton mass floor are checked through

```text
QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows
SelectedRows.eventually_stageMass_gt_square_div_eight
```

in `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`.

### New content

No existing declaration removes `hlowTail` from the pure-row dispatch.  In
particular, the following checked theorems still require it and must not be
invoked as if their signatures had changed:

```text
quittingLiteralSameStage_dispatch
exists_quittingSameStage_terminalRoute_or_closedSegment_of_liveMass
exists_quittingSameStage_terminalRoute_or_closedSegment_of_sourceRow
quittingPartialPurification_then_sameStage_dispatch
quittingPartialPurification_then_finFourSameStage_dispatch
```

The new mathematical content is the zero-transport pure-row adapter proved
below.  Once it supplies `QuittingSameStageEndpointDispatch` for every pure
nonsingleton coalition, the already checked raw finite-orbit and Fin4
closed-segment theorems apply without modification.

## Proof

### Lemma 1: a pure nonsingleton row screens every continuation cap

Fix an actual post-date behavioral tail `tau` and a pure root `q_C` with
`|C|>=2`.  Let `y=Sem(tau)`.  Fix a player `i`.

Because `C` has at least two members, choose `j in C` with `j!=i`.  This is
also possible when `i` is outside `C`, by choosing any member of `C`.  After
an arbitrary unilateral behavioral replacement by `i`, player `j` still
Quits surely at the current root.  Absorption therefore occurs immediately.
Equivalently,

\[
 \operatorname{OppCont}_i(q_C)=0.
\tag{10}
\]

The tail is actual, so `d_i(y)>=0`.  Applying both sides of (9) and using
(10) gives

\[
 d_i(\operatorname{Sem}(q_C\triangleright\tau))=\delta_i(C).
\tag{11}
\]

This identity is against all behavioral deviations.  Later behavior is
irrelevant because another player still Quits at the current row after every
unilateral replacement.

### Lemma 2: every pure nonsingleton row has a large strict toggle

The behavioral profile `q_C` followed by `tau` is actual, so its semantic pair
is a carrier point.  Global minimality and (11) imply

\[
 D_*\le \sum_{i\in\operatorname{Fin}4}\delta_i(C).
\tag{12}
\]

Hence some player `i` satisfies

\[
 \delta_i(C)\ge D_*/4>0.
\tag{13}
\]

Since the current action of `i` is pure, strict positivity means that its
unique better endpoint toggles its membership in `C`.  The routed coalition
is `C triangle {i}`.

This argument applies separately to every pure nonsingleton coalition over
the same literal tail.  It does not assume that the original whole profile,
the tail, or any target is near the minimum fiber.

### Lemma 3: exact reached gain, debt decrease, and mass

Return to the original profile `sigma` and marked date `t`.  Its displayed
stage mass factors as

\[
 \Pr_\sigma(S\text{ at }t)
 =L\,\Pr_{x_t}(S),
\tag{14}
\]

so (2) gives `L>=lambda>0`.

Let `sigma^C` be `sigma` with only the root at `t` replaced by the pure root
`q_C`.  All roots before `t` are unchanged, so the live mass remains `L`.
The pure root assigns probability one to `C`, hence

\[
 \Pr_{\sigma^C}(C\text{ at }t)=L.
\tag{15}
\]

Choose `i` from Lemma 2 and change only its date-`t` action to the exact best
endpoint.  On histories which do not reach `t`, nothing changes.  Conditional
on reaching `t`, the payoff changes from `r_i(C)` to
`r_i(C triangle {i})`.  Therefore the literal payoff gain is exactly

\[
 g_i=L\delta_i(C)\ge LD_*/4\ge\lambda D_*/4.
\tag{16}
\]

Only player `i`'s prescribed strategy changed, so the set and payoff of all
its unilateral deviations—and therefore its unrestricted behavioral cap—are
unchanged.  Thus

\[
 d_i(\sigma^{C\triangle\{i\}})
 =d_i(\sigma^C)-g_i.
\tag{17}
\]

The update changes no earlier root and no post-date behavior.  The target is
again pure at `t`, with coalition `C triangle {i}`, so its unconditional
marked mass is exactly `L`.  This proves every field of the existing
`QuittingSameStageEndpointEdge`, with the stronger floor (16).

### Lemma 4: the Fin4 orbit reaches a pair

At a pure pair, stop the strict orbit.  The checked terminal predicate makes
either member Continue and routes the pair to the other member, producing a
singleton with mass `L`.  No payoff sign is required for this final route.

At a triple or the universal coalition, apply Lemma 2 and follow its strict
toggle.  Since there are finitely many nonsingleton coalitions, either this
process reaches a pair or it contains a simple closed dispatched segment.
Every visited coalition is contained in `Fin 4`; the checked
`sameStageEndpointTrace_false_of_effectiveSupport_card_le_four` contradicts
the closed alternative.  Hence a pair, and then a singleton, is reached.

The sharper bound of three strict transitions follows directly.  A triple
either leaves to a pair or joins its unique outsider to reach the universal
coalition.  From the universal coalition, the strict toggle must leave to a
triple and cannot reverse the immediately preceding strict join.  At that new
triple, the strict toggle cannot reverse the immediately preceding strict
leave, so it must leave to a pair.  Starting from the universal coalition
needs at most two strict transitions; starting from a pair needs none.

Lemmas 1--4 prove the local theorem.

### Atlas adapter and consumer

Let `source` have a nonsingleton retained atom `S` of law mass `mu`.  Use
`source.atom.nonempty_selectedRows` to retain one actual selected-row family.
The eventual stage-mass theorem gives a rank `n` such that the actual selected
profile `sigma_n` and its actual shifted marked date `t_n` satisfy

\[
 \Pr_{\sigma_n}(S\text{ at }t_n)>\mu^2/8=\lambda_0.
\tag{18}
\]

Apply the local theorem to `sigma_n,t_n,S,lambda_0`.  The result is an actual
singleton terminal at the same date with mass at least `lambda_0`, retaining
the selected source and every off-date behavioral law as dependent
provenance.

Apply
`FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass`
to that endpoint.  Keep the selected rows, rank, pure sibling, dispatched
orbit, terminal route, singleton target, and strong packet in one dependent
source result.  Finally apply
`FinFourSingletonStageStrongConcentratedPacket.consumerResult` with the
original `source`.  This gives the exact source-indexed split displayed after
(5).  No source, minimum point, terminal atom, or reward table is reselected.

## Probability and strategy audit

* Stage mass is unconditional: it includes survival through all dates before
  `t` and the marked root's coalition probability.
* The marked root is a product of independent player actions.  Replacing it by
  `q_C` is a literal product-root replacement in an actual behavioral profile.
* Every strict edge changes only one player's action at one date.  The mover's
  opponents and hence its full behavioral cap remain unchanged.
* Lemma 1 quantifies over arbitrary behavioral deviations.  Never, unbounded
  stopping times, randomized stopping laws, and post-date deviations are all
  included; another sure Quitter makes them irrelevant at the screened row.
* Every profile retains the exact post-date behavioral continuation.  No
  semantic carrier representative or separately selected tail is substituted.
* The initial pure overwrite is not claimed unilateral or profitable.  The
  final pair-to-singleton route is not claimed profitable.  Only the intervening
  pure-orbit edges carry (16).
* No target root is claimed cap--Nash, and terminal-law mass is never equated
  with fresh cap-prefix absorption.

## Boundary tests

### Nonsingleton cardinality is exact

At a pure singleton `{i}`, if `i` deviates to Continue there need be no other
sure Quitter.  The tail can then be reached, so
`OppCont_i=1` is possible and (11) fails.  This is precisely why the singleton
node remains a separate consumer obligation.

### Positive minimum debt is used only for the paid floor

If `D_*=0`, (12) does not force any strict toggle.  The mass-preserving pure
overwrites remain actual, but the profitable orbit need not exist.

### The final route need not be profitable

For a pure pair `{a,b}`, take

\[
 r_a(\{a,b\})=1,
 \qquad r_a(\{b\})=0.
\]

Making `a` Continue routes the mass to the singleton `{b}` but lowers `a`'s
payoff.  The theorem deliberately uses the broader terminal predicate here
and assigns no gain floor to this step.

### Pair terminals are essential on Fin4

Strict Boolean better-response cycles can exist on four players if pairs are
not treated as terminal.  For example, the coalitions

\[
\{0,1\}\to\{0,1,2\}\to\{0,2\}\to\{0,2,3\}
\to\{0,3\}\to\{0,1,3\}\to\{0,1\}
\]

can be made strict by assigning each displayed mover payoff `1` at its target
and `0` at its source.  The checked Fin4 obstruction applies because each
visited pair already has a no-loss singleton route; it is not a theorem that
all four-player Boolean better-response graphs are acyclic.

### Effective support four is sharp combinatorially

On five players set

\[
A_0=\{0,1,2\},\quad A_1=A_0\cup\{3\},\quad
A_2=A_1\cup\{4\},\quad A_3=A_0\cup\{4\}.
\]

Choose payoffs with

\[
r_3(A_1)>r_3(A_0),\quad r_4(A_2)>r_4(A_1),\quad
r_3(A_3)>r_3(A_2),\quad r_4(A_0)>r_4(A_3).
\]

This is a strict four-edge toggle cycle containing no singleton or pair.  It
uses five effective labels and shows why the checked support-at-most-four
premise cannot simply be dropped.  It is a finite combinatorial boundary
example, not a positive-gap quitting-game counterexample.

## Adapter and consumer

The arbitrary-data local adapter takes exactly:

```text
minimum carrier point + global minimality + D_* > 0
actual behavioral profile + marked date
nonsingleton stage coalition + positive mass floor
```

and returns a literal source-pure sibling, a finite exact endpoint orbit, and
a singleton target at the same mass scale.  The atlas adapter obtains those
inputs from any nonsingleton `FinFourMinimumAtomProducer`, without first
forming `TailEscapeSubsequence` or `FinFourLowTailRow`.

The named downstream semantic endpoint is the already checked
`FinFourStrongConcentratedPacketConsumerResult`.  Its collision-minimum branch
remains open; this export closes the atlas entrance, not the final consumer.

## Lean handoff

Suggested narrow declarations:

```text
quittingPureNonsingleton_opponentContinueMass_eq_zero
quittingPureNonsingleton_prefixDebt_eq_coordinateNashDefect
quittingPureNonsingleton_sameStage_dispatch_noTail
quittingPositiveMassNonsingleton_terminalRoute_or_closedSegment_noTail
quittingFinFourPositiveMassNonsingleton_exists_singleton_noTail
FinFourMinimumAtomProducer.nonempty_strongConcentratedPacket_of_nonsingleton
FinFourMinimumAtomProducer.nonempty_strongConcentratedPacketConsumption_of_nonsingleton
```

The pure-row dispatch should construct `QuittingSameStageEndpointEdge`
directly from Lemmas 1--3.  It must not call an existing declaration whose
signature contains `hlowTail`.  Feed the resulting pointwise dispatch to
`exists_quittingSameStage_terminalRoute_or_closedSegment`, then eliminate the
closed arm with
`not_nonempty_finFourSameStageEndpointClosedSegment`.

The source-indexed result should retain:

* the original `FinFourMinimumAtomProducer`;
* one fixed `SelectedRows` family and selected rank;
* the actual selected profile and marked date;
* the literal pure sibling and dispatched orbit;
* the terminal pair-to-singleton route and singleton target; and
* the produced strong packet and checked consumer result.

Do not manufacture `FinFourLowTailRow`, claim that a copied cap-root remains
cap--Nash, or package the new endpoint as the current low-row-specific
`FinFourAtlasWeakConcentratedSingletonOrigin.reached` constructor.  A new
source-indexed wrapper, or direct composition with the generic strong packet,
is the honest interface.

Useful finite tests are:

1. a pure pair whose only singleton route is payoff-losing;
2. the six-edge Fin4 cycle above, verifying that pair terminality blocks it;
3. the five-label four-edge cycle above, verifying the effective-support
   boundary; and
4. a pure singleton with a tail-dependent owner cap, verifying that the
   zero-transport lemma is not generalized past its cardinality hypothesis.

## Scope and nonclaims

This theorem does not:

* consume the strong concentrated-singleton node;
* prove terminal approximate equilibria or a uniform-equilibrium payoff;
* make the final singleton target near-minimal;
* prove a total-debt decrease or a minimum-fiber support drop;
* control cross-coordinate cap leakage after the singleton is produced;
* preserve the original marked root or its cap--Nash status;
* make the initial simultaneous pure overwrite unilateral or profitable;
* make the final pair-to-singleton route profitable; or
* extend the Fin4 monodromy exclusion to effective support five.

It proves the exact no-tail, source-attached contraction

\[
\boxed{
\text{nonsingleton Fin4 minimum-law source}
\Longrightarrow
\text{strong concentrated-singleton consumer node}.}
\]

## Formalization record

The checked realization is split at the game-independent orbit, generic
same-stage, Fin4 endpoint, and source-atlas boundaries.  It preserves the
packet's original source and reviews while replacing the suggested handoff
names by the exact maintained declarations.

1. `MathUE/FiniteBooleanEndpointOrbit.lean` strengthens `DispatchedOrbit` with
   `not_terminal_before` and `edge_before`, so a stopped trace retains its
   first terminal vertex and every preceding edge.  `DispatchedOrbit.mapEdge`
   and `DispatchedClosedSegment.mapEdge` preserve the identical orbit while
   forgetting edge data.  The generic theorem
   `DispatchedOrbit.terminal_time_le_three_of_effectiveSupport_card_le_four`
   uses only effective-support cardinality at most four, card-two terminality,
   one-coordinate cardinality change, and absence of an immediate reverse.
2. `Research/Quitting/SameStageEndpointMonodromy.lean` proves
   `quittingLiveMass_literalPureRootProfile_eq` and the general literal update
   identity `quittingLiteralPureRootProfile_update_eq_routed`, while retaining
   the existing nonsingleton wrapper.  The declarations
   `quittingSameStageSingletonRoute_of_card_eq_two` and
   `QuittingSameStageEndpointEdge.not_reverse` provide the terminal pair route
   and rule out a reverse pair of strict edges by exact positive mover-debt
   subtraction.
3. `Research/Quitting/SameStageEndpointMonodromyImpossible.lean` is the
   producer-neutral monodromy obstruction.  It proves
   `sameStageEndpointTrace_false_of_effectiveSupport_card_le_four`,
   `sameStageEndpointTrace_false_of_visitedSupport_card_le_four`, and the Fin4
   specialization `not_nonempty_finFourSameStageEndpointClosedSegment` for an
   arbitrary finite ambient player type with at most four effective visited
   labels.  The producer-specific wrappers remain in
   `Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean`, so their
   public names and source-preserving residual eliminators are unchanged.
4. `Research/Quitting/PureNonsingletonCollisionScreening.lean` proves the
   continuation-screening identity
   `quittingTerminalSemanticDebtSum_pureNonsingletonRow_eq_totalDefect` against
   unrestricted behavioral caps.  `quittingPureNonsingleton_screenedDispatch`
   constructs a strict literal best-endpoint edge with reached-live-mass floor
   `L * D_* / card(I)`, exact mover-debt subtraction, and no-loss routed mass,
   or stops at the mass-preserving singleton predicate.  The resulting
   `exists_pureNonsingletonScreened_terminalOrbit_or_closedSegment` invokes no
   tail-debt, near-minimality, or copied-root Nash hypothesis.
5. `Research/Quitting/FinFourPureNonsingletonCollisionScreening.lean` defines
   `FinFourPureNonsingletonScreenedEndpoint`.  Its canonical `screenedEdge`
   supplies every preterminal accessor coherently.  `edge_gain_floor_live`,
   `edge_gain_floor`, `edge_mover_debt`, and `edge_stageMass_le` give the exact
   `L * D_* / 4` and `lambda * D_* / 4` floors, exact unrestricted mover-debt
   decrease, and no-loss mass.  `edge_count_le_three` and
   `terminal_action_and_card` reach a pair in at most three strict edges and
   identify the final route as Continue.  `sourcePure_stageMass_eq_liveMass`,
   `targetStageMass_eq_liveMass`, `orbitProfile_eq_of_time_ne`, and
   `targetProfile_eq_of_time_ne` retain exact initial and final mass and the
   complete off-date behavioral profile.  The arbitrary-data constructor is
   `quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint`.
6. `Research/Quitting/FinFourProducerAtlas/PureNonsingletonCollisionScreening.lean`
   defines `FinFourPureNonsingletonSelectedRow`, retaining one actual
   `SelectedRows` family and rank from the same `FinFourMinimumAtomProducer`.
   `FinFourMinimumAtomProducer.nonempty_pureNonsingletonSelectedRow` derives
   the strict `mu^2 / 8` marked-mass floor from the selected-row theorem.
   `FinFourPureNonsingletonStrongConcentratedPacket.canonical_edge_gain_floor`
   states the literal paid floor `mu^2 * D_* / 32`, while
   `packet_resolution_eq` and `resolution_le_singletonStageMass` retain the
   exact canonical scale and target mass.
7. The same source module proves
   `FinFourMinimumAtomProducer.nonempty_strongConcentratedPacket_of_nonsingleton`
   and
   `FinFourMinimumAtomProducer.nonempty_strongConcentratedPacketConsumption_of_nonsingleton`.
   The dependent `FinFourPureNonsingletonStrongConcentratedPacketConsumption`
   stores the selected row, complete orbit, literal singleton endpoint, exact
   strong packet, and `FinFourStrongConcentratedPacketConsumerResult` on the
   original minimum source.  Its `strategic_or_collisionMinimumResidual`
   accessor is the unchanged consumer split, not a consumer of the residual.
8. `Research/Quitting/FinFourExhaustiveProducerAtlas.lean` imports the new
   source adapter and remains the Fin4 reader; `Research.lean` already imports
   that reader.  The older self-tail contraction remains available because it
   retains stronger restarted-continuation provenance, although pure
   screening supersedes it as the minimal nonsingleton atlas entrance.

Evidence seals:

- **M:** PASS.  The pure-row unrestricted-debt identity, averaging constant,
  exact reached gain, first-terminal orbit, support-four obstruction, and
  source-scale arithmetic match the reviewed proof.
- **L:** PASS.  Every declaration named above checks in Lean.  Promotion checks
  include direct and named module compilation, a full `lake build`, trust and
  generated axiom-audit checks, import-graph checks and regression tests,
  proof-duplicate and derivable-telescope checks, documentation checks, and
  diff hygiene.  Targeted axiom prints use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- **A:** PASS.  Every nonsingleton `FinFourMinimumAtomProducer` supplies one
  actual selected-row family and rank, literal pure sibling, certified orbit,
  singleton target, and strong packet.  No minimum, row, tail, endpoint,
  packet, or source equality is accepted as a supplied certificate.
- **C:** PASS through the exact source-attached strong-packet consumer.
  `nonempty_strongConcentratedPacketConsumption_of_nonsingleton` returns the
  maintained strategic arm or the unchanged source-attached
  `QuittingConcentratedCollisionMinimumResidual`.  This seal does not consume
  either selected arm.

Nonclaims:

- the initial simultaneous pure overwrite is not unilateral or profitable;
- the final pair-to-singleton Continue route is not asserted profitable;
- the pure sibling, orbit profiles, and singleton target are not proved
  cap--Nash or near-minimal;
- no tail split, self-tail closure, or high/low-row passport is used by this
  minimal route, but the older self-tail construction is not withdrawn;
- exact mover-debt subtraction does not control the other coordinates or give
  total-debt or minimum-fibre support descent;
- no return, regeneration, recurrence, recursive closure, terminal
  approximation, or chronology reselection is produced;
- the concentrated collision-minimum residual remains open; and
- no new uniform-equilibrium payoff is obtained, so neither the Fin4 nor the
  general finite-quitting conjecture is settled.

The mathematical provenance remains this packet and the independent
`ATLAS_GATEKEEPER` and `STRENGTHENER` reviews linked at its head.
