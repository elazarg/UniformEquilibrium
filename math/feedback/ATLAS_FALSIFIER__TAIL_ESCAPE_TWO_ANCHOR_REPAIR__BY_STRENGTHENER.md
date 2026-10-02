# Review of `ATLAS_FALSIFIER__TAIL_ESCAPE_TWO_ANCHOR_REPAIR`

Reviewer: `STRENGTHENER`

## Verdict

**PASS as an ordinary-mathematics atlas contraction, subject to the stated
Lean packaging seam.**  The universal self-tail closure is valid and is
strictly stronger than the old high-tail/low-tail classification for the raw
same-stage consumer.  The decisive point is exact: the profile after the
marked row is literally the chosen near-minimum actual profile, so its full
terminal semantic pair and unrestricted behavioral caps are preserved by
profile equality.  No cap stability of the repaired *whole* profile is used.

The two-anchor supplement is also valid.  Two anchors are the minimal purely
root-theoretic condition that controls the repaired whole profile uniformly
against every unilateral behavioral deviation.  It can be sharpened
coordinatewise as recorded below.

The note's final downstream statement is conservative but no longer maximal.
After the reviewed monodromy impossibility and the strong singleton-packet
adapter, the checked `consumerResult` theorem gives a further exact
source-attached strategic-versus-collision-minimum split.  This is still not a
uniform-equilibrium or regeneration theorem.

## Claim reviewed

For an actual profile `sigma` and marked date `t`, copy its exact live roots
through `t` and then use `sigma` itself as the continuation.  The resulting
literal stack:

1. has the same live roots and stage-coalition mass through `t`;
2. has post-`t` all-Continue spine exactly equal to `sigma`; and therefore
3. has post-`t` spine debt excess exactly
   `D(sigma) - Dref`.

Applying this to sufficiently late selected rows of a nonsingleton minimum-law
atom supplies every hypothesis of
`quittingPartialPurification_then_finFourSameStage_dispatch`, independently of
the original selected tail's debt.  The monodromy alternative is then removed
by `FIN4_MONODROMY_PRODUCER_IMPOSSIBLE`, leaving a literal concentrated
singleton route with the restarted near-minimum source as its exact post-date
tail.

## 1. Exact continuation and all-behavior cap audit

The construction is genuinely executable:

```text
quittingLiteralRootStackProfile reward copiedRoots sigma
```

is a fold of `quittingRootThenContinuationProfile`.  The theorem

```text
shiftProfile_quittingRootThenContinuationProfile
```

identifies the shifted profile after one realized root with the declared
continuation as a full behavioral-profile equality, not only as a live-root or
payoff equality.  Iterating along the all-Continue actions through the copied
word gives

```text
quittingAllContinueProfileSpine reward (Close_t sigma) (t + 1) = sigma.
```

Consequently, for every player `i`, both prescribed payoff and unrestricted
behavioral cap agree exactly on that continuation:

\[
 U_i(\operatorname{spine}_{t+1}\operatorname{Close}_t(\sigma))=U_i(\sigma),
 \qquad
 B_i(\operatorname{spine}_{t+1}\operatorname{Close}_t(\sigma))=B_i(\sigma).
\]

The cap equality is not inferred from pure-time continuity.  It follows from
equality of the opponents' complete behavioral profiles, hence equality of
every unilateral deviation payoff before taking the supremum.  The weaker
semantic route through `quittingTerminalSemanticPair_eq_of_liveRoot_eq` is
also sound because terminal semantic caps have already been proved to depend
only on the canonical live-root word.

The copied roots retain the stage mass through `t`.  The relevant exact
ingredients are
`quittingProfileLiveRoot_rootThenContinuation_zero`,
`quittingProfileLiveRoot_rootThenContinuation_succ`, and the factorization of
stage mass into prior joint survival and current root coalition mass.

The note correctly warns that none of this preserves cap--Nash exactness of
the copied word after changing its continuation.  The old cap--Nash proof is
used only upstream to produce the selected near-minimum source and marked
atom.

## 2. Exact low-tail dispatch hypotheses

Inspection of
`quittingPartialPurification_then_finFourSameStage_dispatch` in
`Research/Quitting/FinFourSameStageEndpointMonodromy.lean` confirms that its
inputs are exactly:

1. one fixed minimum semantic pair in the terminal carrier;
2. global minimality of that pair;
3. strictly positive minimum total debt;
4. one actual base profile and one date;
5. one positive scale `lambda` and a nonsingleton coalition whose literal
   stage mass is at least `lambda`; and
6. post-date spine debt excess strictly below `lambda * D_* / 2`.

It does **not** require the whole base profile to be near-minimum, the copied
roots to remain cap--Nash, a `SelectedRows` object, or the original post-mark
tail.  Therefore the self-tail closure is a valid direct producer for this raw
theorem.

For the selected rows, `SelectedRows.prefix_debt_tendsto` gives convergence of
the actual prefixed source debts to `quittingTerminalDebtSumInf reward`, and
`source.debt_eq_inf` identifies this with `D_*`.  Strict cofinal reindexing, if
one starts from `TailEscapeSubsequence`, preserves the convergence.  The
selected stage mass is already strictly above `mu^2/8`, so one sufficiently
late row satisfies both raw hypotheses simultaneously.  As the author notes,
the stronger construction starts directly from
`QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows` and never uses
`tail_excess_floor`.

## 3. Why two anchors are genuinely needed for whole-source provenance

The universal closure controls the continuation exactly but does not control
the semantic pair of the repaired whole source.  To obtain such control from
root probabilities alone, two distinct near-sure Quit anchors are genuinely
needed.

Let their marked-root Continue probabilities be `c_a,c_b`.  Couple the
original and repaired profiles, using the same arbitrary deviation by player
`i`.  The profiles can differ only if the marked row is reached and all
players Continue there.  If `i=a`, the nondeviating anchor `b` must Continue;
if `i=b`, anchor `a` must Continue; and if `i` is neither anchor, both must
Continue.  Product behavior at the live root gives the sharper pointwise
bounds

\[
\begin{aligned}
 |U_i(\widehat\sigma[i\leftarrow\tau_i])
      -U_i(\sigma[i\leftarrow\tau_i])|
 &\le 2M c_b &&(i=a),\\
 &\le 2M c_a &&(i=b),\\
 &\le 2M c_ac_b &&(i\notin\{a,b\}).
\end{aligned}
\tag{A}
\]

These estimates hold for every history-dependent behavioral deviation.  Taking
suprema in both directions proves the identical bounds for the caps.  Under
prescribed play, neither anchor is replaced, so every prescribed-payoff
coordinate differs by at most `2M c_a c_b`.  Hence for `n` players

\[
 |D(\widehat\sigma)-D(\sigma)|
 \le 2M\bigl(c_a+c_b+(2n-2)c_ac_b\bigr).
\tag{B}
\]

For `Fin 4`, this is

\[
 |D(\widehat\sigma)-D(\sigma)|
 \le 2M(c_a+c_b+6c_ac_b),
\]

which sharpens the note's sufficient `16M max(c_a,c_b)` bound.  Either bound
is enough for cofinal near-minimum repaired sources.

One anchor does not suffice for uniform cap stability.  A two-player boundary
example is enough.  At the copied root let `a` Quit surely and `b` Continue.
Give `a` payoff zero from `{a}` and payoff one from `{b}`.  Compare an
all-Never continuation with a continuation in which `b` Quits surely.  The
prescribed whole payoff is unchanged because `a` Quits at the root, but after
the unilateral deviation in which `a` Continues, the two continuation payoffs
are respectively zero and one.  Thus the cap changes by one although the sole
anchor has Continue probability zero.  With two sure Quit anchors, at least
one remains after every unilateral deviation and the continuation is never
reached, giving exact zero error.

This establishes the precise scope:

- no anchors are needed for the raw low-tail dispatch;
- two are sufficient, and in this uniform sense necessary, to retain
  near-minimum **whole repaired sources** without extra tail-specific payoff
  hypotheses.

The two-anchor assumption is conditional; positive nonsingleton stage mass
alone does not imply that two member Continue probabilities tend to zero.

## 4. Strongest source-attached output after the monodromy no-go

The note currently stops at a source-attached strong concentrated-singleton
packet.  The checked file
`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`
allows one further exact contraction.  Once the raw low-row packaging adapter
has retained the same `FinFourMinimumAtomProducer source`, the produced strong
packet `strong` satisfies

```text
FinFourStrongConcentratedPacketConsumerResult source strong
```

by `FinFourSingletonStageStrongConcentratedPacket.consumerResult`.  Expanded,
the output is

```text
(HasQuittingConcentratedSingletonStrategicDispatch
    source.residual.witness strong.adapter.packet strong.singletonOwner ∧
  (HasQuittingStaticAtomicToggleHandoff reward ∨
   HasQuittingExactPlayerDeletionAtGap reward strong.singletonOwner
     source.residual.witness.terminalGap))
∨
Nonempty (QuittingConcentratedCollisionMinimumResidual reward
  source.point.1 strong.packetOwner strong.adapter.routedTerminal
    strong.adapter.packet).
```

This is the strongest presently checked post-packet consumer output I found.
It retains the exact hard-residual witness, minimum point, routed terminal,
packet owner, and literal packet.  It does not produce terminal approximants,
a cumulative return, or regeneration, and it does not make the singleton
target near-minimum.

The source attachment after self-tail closure is exact but limited:

- the minimum point, causal atom, selected source row, copied marked past, and
  restarted near-minimum post-date tail are retained;
- bounded purification and terminal-orbit endpoint updates preserve that
  post-date live-root tail;
- the monodromy alternative is eliminated by the separately reviewed
  `FIN4_MONODROMY_PRODUCER_IMPOSSIBLE` result;
- the resulting strong packet is built on the actual singleton endpoint;
- the old cap--Nash stack certificate and near-minimum debt of the final
  singleton target are not retained.

The existing `consumerResult` is Lean-checked.  The self-tail closure adapter,
raw low-row passport, and monodromy impossibility are not yet all connected in
Lean, so the full contraction should not be labelled checked until those
interfaces are implemented.

## 5. Declaration audit

Inspected declarations and files:

- `quittingRootThenContinuationProfile` and
  `shiftProfile_quittingRootThenContinuationProfile` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`;
- `quittingLiteralRootStackProfile` and its `nil`/`cons` equations in
  `UniformEquilibrium/Quitting/Root/LiteralExactPrefixStack.lean`;
- `quittingAllContinueProfileSpine` and
  `quittingAllContinueProfileSpine_apply_liveHist` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingProfileLiveRoot_rootThenContinuation_zero` and
  `quittingProfileLiveRoot_rootThenContinuation_succ` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- `SelectedRows`, `SelectedRows.prefix_debt_tendsto`,
  `SelectedRows.eventually_stageMass_gt_square_div_eight`, and
  `TailEscapeSubsequence` in
  `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`;
- `FinFourLowTailRow` in
  `Research/Quitting/FinFourProducerAtlas/Source.lean`;
- `quittingPartialPurification_then_finFourSameStage_dispatch` in
  `Research/Quitting/FinFourSameStageEndpointMonodromy.lean`;
- `FinFourLowTailRow.nonempty_leaf` and the singleton/monodromy producer
  structures in `Research/Quitting/FinFourProducerAtlas/Leaves.lean`;
- the reached-singleton semantic connections in
  `Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean`;
- `FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass`
  in `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`;
- `FinFourSingletonStageStrongConcentratedPacket.consumerResult` in
  `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`;
  and
- the independently reviewed mathematical export
  `exports/FIN4_MONODROMY_PRODUCER_IMPOSSIBLE.md`.

## 6. Recommended Lean-facing statement

The local generic self-tail lemmas proposed by the author are the right first
handoff.  The Fin4 adapter should avoid fabricating a `FinFourLowTailRow`, whose
fields assert membership in the original selected-row family.  A raw actual
low-tail passport should retain exactly the six hypotheses listed in Section
2, and the existing purification producers should either be generalized over
that passport or receive parallel constructors.

After that adapter, add one theorem composing:

```text
selected nonsingleton minimum-law atom
→ self-tail raw low row
→ raw same-stage dispatch
→ (monodromy impossible) singleton endpoint
→ strong concentrated packet
→ FinFourStrongConcentratedPacketConsumerResult.
```

This is a real atlas contraction.  Its honest endpoint remains the checked
strategic-versus-collision-minimum split, not a uniform-equilibrium payoff.
