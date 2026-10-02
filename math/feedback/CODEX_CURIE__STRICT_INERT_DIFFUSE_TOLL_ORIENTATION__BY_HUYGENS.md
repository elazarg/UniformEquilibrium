# Review of the strict-inert diffuse-toll orientation note

Reviewer: `HUYGENS`

## Claim reviewed

I reviewed Section 8 of
`notes/CODEX_CURIE__STRICT_INERT_DIFFUSE_TOLL_ORIENTATION.md` and its use in
the strict normalized-passport arm.  The exact claim is the following.

Let `I` be finite, let `C : Finset I` have `2 <= C.card`, let `W` be one
fixed finite list of product roots, and let `tau` and `tau'` be arbitrary
behavioral tails.  Prefix each tail first by the same pure root `C` and then
by the same root word `W`.  The two resulting profiles have equal complete
terminal semantic pairs.  In particular their prescribed payoff vectors,
their unrestricted behavioral best-response caps, their coordinate debts,
and their total debts agree exactly.

The intended strict-arm consequence is only a no-go for a direct repair that
changes the post-mark tail while preserving the pre-mark word and the pure
nonsingleton marked root.  It is not a no-go for changing a pre-mark root,
using different prefix words, replacing the marked row by a non-pure root,
or proving an independent seam/commutator transport theorem.

## Verdict

The exact tail-screening theorem is correct and directly formalizable from
checked declarations.  Its all-behavior scope is genuine: the equality is of
the project's complete terminal semantic pair, whose second coordinate is
the supremum over arbitrary unilateral behavioral replacements.

The strict-arm placement conclusion is also correct at the current
interface, after one wording correction described below.  The current Fin4
packet supplies minimum-fibre anchoring for the post-mark reference tail.
That tail is screened from the whole profile by the pure marked pair.  A
repair before the marked pair can affect the whole profile, but the packet
does not assert that the continuation seen at that pre-mark location lies in
the minimum-fibre tube required by the linear-basin toll.  Thus the direct
signed-post-tail-toll completion is unavailable from the current fields.

This is a useful exact no-go, but not a terminal consumer.

## Proof audit

The checked theorem
`quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean` states that, when
`2 <= C.card`, the complete semantic pair of a pure-`C` root followed by an
arbitrary behavioral continuation is the explicit tail-independent pair

```text
(quittingSetReward reward C,
  fun i => max
    (quittingSetReward reward (insert i C) i)
    (quittingSetReward reward (C.erase i) i)).
```

This theorem already checks the delicate deviation point.  If player `i`
replaces its entire behavioral strategy, some member of `C \ {i}` still
quits surely at the marked root.  Therefore the post-mark continuation is
unreachable under both prescribed play and every unilateral behavioral
replacement.  Never, arbitrarily late stopping, mixed hazards, and
history-dependent behavior are all included.

Apply the checked identity separately to `tau` and `tau'`.  Their semantic
pairs immediately after the pure root are equal.  The checked theorem
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` says that
prefixing one product root applies the deterministic semantic-prefix map to
the continuation semantic pair.  Induction on the common list `W`, using
`quittingLiteralRootStackProfile_cons` from
`UniformEquilibrium/Quitting/Root/LiteralExactPrefixStack.lean`, preserves
the equality.  This proves equality of the complete semantic pairs after the
whole common word.

Coordinate payoff and cap equalities are the two components of this product
equality.  Coordinate debt and total-debt equalities follow by unfolding
their definitions.  No compactness, limiting, stationarity, or attainment
argument occurs.

## Fin4 source audit

The current forced-pair source supplies the exact chronology needed for the
screening application:

- `forcedPair_postDateSpine_eq_reference` in
  `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`
  identifies the complete spine after the marked pure pair with the selected
  near-minimum reference profile;
- `forcedTerminal_card` in the same file proves that the marked coalition has
  cardinality two;
- `finFour_profile_eq_literalRootStack` in
  `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean` identifies
  every actualized descendant as one common finite root word prefixed to the
  selected forced-pair target; and
- the forced-pair target is a literal pure-root edit at its marked date, as
  recorded by `targetProfile_eq_literalOneDateProfile` together with
  `quittingLiteralPureRootProfile_update_eq_routed` in the forced-pair
  construction.

Consequently, changing only the post-mark reference tail while retaining all
pre-mark roots and the marked pure pair cannot change the actualized whole
semantic point.

## Required wording correction

Section 7 says that a word inserted in the pre-mark prefix has as its inner
continuation “the semantic pair of the pure-pair endpoint,” and that this
pair is table-determined.  This is literally true only for the suffix that
starts at the marked pure pair.  At an earlier insertion point, the
continuation can also contain the remaining copied pre-mark roots.

The needed and correct statement is weaker:

> the current packet gives no theorem placing the continuation at an
> arbitrary pre-mark insertion point in the minimum-fibre tube.

That suffices for the claimed interface no-go.  It must not be strengthened
to an assertion that every pre-mark continuation is outside the tube, or
that it is always the bare table-determined pure-pair semantic point.

## Boundary tests

The cardinality hypothesis is sharp.  With a singleton marked coalition
`C = {i}`, player `i` can replace its strategy by Continue at the marked row,
after which the post-mark tail is reachable.  Take a two-player table with
`r_i({i}) = 0`, `r_i({j}) = 1`, and `r_i({i,j}) = 1`.  An all-Continue tail
and a tail in which `j` quits surely at the next date give different caps for
`i` after the pure singleton root.

The common-word hypothesis is also essential.  Different prefixes can have
different prescribed absorption and different cap values even when their
post-prefix tails agree.  Likewise a non-pure marked root with positive
opponent-continuation probability can transmit tail payoff and cap changes.

These tests confirm that the result is a tail-screening theorem, not a no-go
for pre-mark, non-pure, different-word, or commutator repairs.

## Lean handoff

The narrow wrapper theorem proposed in Section 8 is appropriate:

```lean
theorem quittingTerminalSemanticPair_literalRootStack_pureSet_screen
    (roots : List (iota -> PMF Bool))
    (C : Finset iota) (hC : 2 <= C.card)
    (first second : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots
          (quittingRootThenContinuationProfile reward
            (quittingPureSetRoot C) first)) =
      quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots
          (quittingRootThenContinuationProfile reward
            (quittingPureSetRoot C) second))
```

Its proof is induction on `roots`; the base case rewrites both sides with
`quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`,
and the step rewrites with `quittingLiteralRootStackProfile_cons` and
`quittingTerminalSemanticPair_rootThenContinuation` before applying the
induction hypothesis.  Separate payoff, cap, coordinate-debt, and total-debt
corollaries should be derived rather than stored as assumptions.

An additional Fin4 specialization may package the forced-pair chronology and
show invariance under replacement of the post-mark reference tail while the
pre-mark roots and pure marked pair remain literal.  It must not claim
nonmembership of a pre-mark continuation in the minimum tube; only the
absence of such an anchor from the current source interface is established.

## Export-gate assessment

The result precisely blocks one named attempted completion of Arm B and is
worth retaining for formalization.  Because the exported statement asserts
equality of unrestricted behavioral caps, the conference rule requires a
second independent review before it enters `exports/`.  I found no
mathematical objection after the wording correction above.
