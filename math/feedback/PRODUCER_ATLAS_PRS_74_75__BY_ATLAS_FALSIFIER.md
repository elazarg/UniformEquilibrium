# Adversarial mathematical review of the Fin4 six-leaf producer reduction

Reviewer: ATLAS_FALSIFIER

## Exact claim reviewed

I reviewed only the final six-leaf reduction in PR 75 (with PR 74 as its
monolithic predecessor): from a
`FinFourQuantitativeFullSupportHardResidual`, one obtains one of

1. a singleton atom in the selected minimum law;
2. a singleton reached during bounded partial purification;
3. a singleton route from the subsequent pure-root orbit;
4. a cofinal quantitative tail-escape subsequence;
5. a common-host simple same-stage endpoint cycle; or
6. a complementary-pair simple same-stage endpoint cycle.

I did **not** review Lean elaboration or compilation. I also did not review the
stronger claim that these leaves have already been consumed, that they form a
recursive well-founded atlas, or that the names assigned by
`FinFourProducerCompletionContract` are theorems.

## Sources inspected

The review followed the exact declarations in:

- `FinFourMinimumAtomProducer.nonempty_of_hardResidual` and
  `nonempty_finFourProducerResidual_of_hardResidual` in the final PR 75 files
  `Research/Quitting/FinFourProducerAtlas/Source.lean` and
  `Research/Quitting/FinFourProducerAtlas/Coverage.lean`;
- `exists_finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows` and
  `SelectedRows.eventually_stageMass_gt_square_div_eight` in
  `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`;
- `quittingPartialPurification_exists_step`,
  `quittingPartialPurification_exists_total_or_singleton`, and
  `quittingPartialPurification_then_sameStage_dispatch` in
  `Research/Quitting/SameStageEndpointPurification.lean`;
- `quittingLiteralSameStage_exists_strictGain_or_singletonRoute`,
  `quittingLiteralSameStage_exists_singleton_or_endpointEdge`, and
  `exists_quittingSameStage_terminalRoute_or_closedSegment_of_sourceRow` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`;
- `finFourTrace_period_le_eight_and_geometry` and
  `quittingPartialPurification_then_finFourSameStage_dispatch` in
  `Research/Quitting/FinFourSameStageEndpointMonodromy.lean`;
- `orderedBooleanCycle_card_le_eight_and_geometry` in
  `MathUE/FinFourOrderedCoalitionCycle.lean`; and
- `QuittingLiteralPositiveActualRowPacket.not_exists_literalNashBellmanEmbedding`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiteralSourceReturnNoGo.lean`.

The dependency files relevant to the mathematical argument are unchanged
between the PR 75 merge base and current `main`.

## Falsification audit

### 1. The finite-atom source is genuine

The hard residual supplies a minimum joint semantic/law point with positive
minimum debt and a positive finite terminal atom. This is stronger than the
generic positive-Never-or-finite-atom dispatch: punishment normality has
already removed the pure-Never-only case at this interface. If the selected
coalition has cardinality one, the first leaf is immediate; otherwise its
cardinality is at least two and the anti-diffusion extraction applies.

The source object retains the table, hard residual, minimum point, complete
limiting law, minimum proof, positive debt infimum, and the literal causal
suffix chronology. No semantic representative is substituted for an actual
profile later in the argument.

### 2. The high-tail/low-tail split is exhaustive

Write

\[
  \mu=\text{the selected finite-atom mass},\qquad D_*=D(z_*),
\]

and let the selected rows have stage masses \(m_n\) and tail excesses \(E_n\).
The selected-row theorem gives eventually

\[
  m_n>\mu^2/8.
\]

The atlas tests the proposition

\[
  \mu^2D_*/16\le E_n.
\]

If it occurs frequently, strict-subsequence extraction gives the tail-escape
leaf with both displayed floors. If it does not occur frequently, it is
eventually false, hence eventually

\[
  E_n<\mu^2D_*/16.
\]

Intersecting this eventual set with the eventual stage-mass set supplies one
literal low-tail row. The inclusive high threshold and strict low threshold
leave no boundary case unclassified.

The constants match the downstream hypothesis exactly. Setting
\(\lambda=\mu^2/8\) gives

\[
  \mu^2D_*/16=\lambda D_*/2.
\]

### 3. Same-date root updates do not invalidate the hypotheses

This was the principal attempted falsification.

Each preliminary update changes one player's action only at the selected
date. The declarations used by the proof establish all of the invariants
needed for the next update:

- the probability of reaching the selected date is unchanged;
- the entire post-date live-root tail is unchanged;
- the marked coalition is routed by toggling only the updated player; and
- the routed coalition's stage mass is no smaller than the previous marked
  mass.

Accordingly, the `QuittingPartialPurificationState.mass_floor` invariant is
preserved through every update. The process touches each player at most once,
so in at most four updates it either routes the mark to a singleton or makes
the whole selected root pure. The equality of the spine after the selected
date proves that the original low-tail inequality still holds at the final
profile.

After the root is pure, every nonsingleton coalition vertex in the endpoint
orbit is realized by replacing only that same root while keeping the same
pre-date survival and the same tail. Its marked stage mass is exactly the
common live mass, hence at least \(\lambda\). Therefore the collision/low-tail
dispatch can be reapplied freshly at every orbit vertex. It is not using a
recipient-transfer estimate transported from the original row.

In particular, the proof does **not** use the invalid inference that a routed
endpoint is near the minimum fiber. No `recipient_floor`,
`aggregate_transfer`, or near-minimum source-excess hypothesis from
`RoutedTransferSubsequence` occurs in the six-leaf argument. The only debt
input used after purification is the unchanged tail excess.

### 4. Fin4 cycle geometry is exhaustive

Every nonterminal orbit step changes exactly one coalition coordinate, every
cycle vertex is nonsingleton, and the selected closed segment is simple. The
Fin4 Boolean-cycle theorem then gives period at most eight and either a player
common to all cycle coalitions or two disjoint two-player coalitions. On four
players, two disjoint pairs are exact complements.

As an independent finite falsification, I enumerated all simple cycles in the
one-coordinate graph on the eleven Fin4 coalitions of sizes two, three, and
four. There are 53 unoriented cycles: 16 of length two, 6 of length four, 16
of length six, and 15 of length eight. None lacks both a common player and a
pair of disjoint two-player vertices. No cycle has length greater than eight.

### 5. Source preservation: exact strength and one interface caveat

Every leaf retains the common `FinFourMinimumAtomProducer`. The low-tail
leaves additionally retain the selected rows and literal selected row. The
partial-purification path is edge-certified and all its profiles differ from
one common base profile only at the selected date. The cycle profiles retain
that same base, selected date, tail, live mass, and minimum point.

There is, however, a precise distinction that an export must respect.
`DispatchedOrbit` and `DispatchedClosedSegment` retain the orbit values and,
for a closed segment, the edges **inside the final period**. Their public
structures do not retain edge certificates for the transient orbit segment
from time zero to the terminal vertex or to the beginning of the closed
period. The construction used in their existence proof does have those
edges, but the PR leaf records discard them.

Therefore the exact PR theorem supports “same literal base/tail/source family”
and “edge-certified closed cycle,” but not the stronger public-interface claim
that the complete endpoint-update path from the final purification state to
the terminal/cycle leaf is retained. This does not invalidate the six-way
existence reduction: all pure-root vertices are actual profiles in the same
source family and the cycle edges themselves are certified. If a downstream
consumer needs the transient update path, the orbit wrapper should be
strengthened with `edge_before_terminal` or `prefix_edge` fields. Otherwise
the export should simply avoid claiming that stronger path provenance.

### 6. Exact scope of the local no-go

At every monodromy-cycle edge, the chosen endpoint is a literal profitable
one-date deviation with positive gain. The gain equals live mass times the
root-tail coordinate Nash defect. An exact Nash--Bellman edge with the same
current prescribed payoff, the same root, and the same next-tail payoff would
force that defect to zero. Hence such a literal embedding is impossible.

This no-go does not exclude:

- changing the root;
- changing the continuation payoff or complete tail;
- paying a Nash error at least as large as the retained gain;
- a nonlocal source-anchored repair;
- a chronology which visits different semantic states; or
- a support/debt regeneration outside that fixed root-tail fiber.

It is therefore a correct local obstruction, not a proof that the cycle leaf
is globally irreducible.

## Conjecture-facing value

The reduction is mathematically more than a supplied-object verifier. Its
input is the arbitrary Fin4 hard residual already produced by the checked
global structural reduction, and its output is one of a finite list of
actual-source objects. It composes the previously separate minimum-law,
anti-diffusion, low-tail purification, and Fin4 orbit geometry results into a
single exhaustive theorem. This strictly replaces the undifferentiated Fin4
hard residual by four honest completion obligations:

1. consume one of the three singleton origins;
2. consume quantitative tail escape;
3. consume common-host monodromy; or
4. consume complementary-pair monodromy.

It does not solve any of those four obligations and does not provide a
well-founded recursive rank. The `completionContract` function only names
them.

PR 74 has the same mathematical theorem in monolithic form. PR 75 is the
maintained split form and repairs the explicit positivity proof for
\(\lambda\); I found no additional mathematical result unique to PR 74.

## Export conditions and unresolved objections

There is no unresolved mathematical objection to exporting the **narrowly
stated six-leaf reduction**. An export packet must nevertheless:

- state the six actual leaves, not the stale three-mode description in the PR
  body;
- call the four completion items obligations, not established consumers;
- make no claim of a concrete mixed-radix descent or recursive atlas;
- describe monodromy as a horizontal same-stage cycle rather than an ordered
  play chronology;
- state the literal-exactification no-go with its fixed source-payoff/root/tail
  hypotheses; and
- either avoid claiming an edge-certified transient path into the terminal or
  periodic leaf, or strengthen the orbit records to retain that path.

The last item is an interface-strength caveat, not a counterexample to the
six-leaf existence theorem. No hidden use of near-minimum recipient transfer
was found.

**PASS** for mathematical export of only the six-leaf reduction, with the
scope conditions above. Unresolved mathematical objections to that exact
reduction: none.
