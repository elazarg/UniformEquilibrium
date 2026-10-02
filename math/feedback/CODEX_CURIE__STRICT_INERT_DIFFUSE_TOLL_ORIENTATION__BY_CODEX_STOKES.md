# Second review of pure-nonsingleton tail screening

Reviewer: `CODEX_STOKES`

## Claim reviewed

Let `I` be finite, let `C : Finset I` satisfy `2 <= C.card`, let `W` be one
fixed finite list of product roots, and let `tau,tau'` be arbitrary behavioral
profiles.  Write

\[
 P_\tau=W*((\operatorname{pure}C)*\tau),\qquad
 P_{\tau'}=W*((\operatorname{pure}C)*\tau').
\]

The claim is

\[
 \operatorname{Sem}(P_\tau)=\operatorname{Sem}(P_{\tau'}),
\]

where the second coordinate of `Sem` is the supremum against every complete
unilateral behavioral replacement.  Hence prescribed payoffs, behavioral
caps, coordinate debts, and total debt are all exactly equal.

The proposed strict-arm application is narrower: changing only the tail after
the retained pure nonsingleton marked row, while keeping that row and every
earlier root literal, cannot repair the whole strict-arm semantic point.  It
does not exclude a pre-mark repair, a different prefix, a non-pure marked row,
or a theorem which transports a post-mark account across the sure-exit seam.

## Verdict

The theorem is correct.  I independently tried to falsify the cardinality,
common-prefix, and purity hypotheses, and each is genuinely necessary.  The
unrestricted behavioral-cap conclusion is also correct; it does not rely on a
stationary or pure-time reduction.

The strict-arm application is correct only with the following scope:

* the supplied minimum-fibre anchor is the post-mark tail;
* a post-mark tail-only repair is screened from the whole source; and
* the current packet supplies no minimum-tube hypothesis for the continuation
  at an arbitrary pre-mark insertion point.

One must not claim that every such pre-mark continuation is outside the
minimum tube, or that it is the bare pure-pair semantic point.  It may contain
the remaining copied pre-mark roots.  With this correction there is no
mathematical objection.

## Independent proof

At the pure `C` root, prescribed play absorbs immediately because `C` is
nonempty.  Fix a player `i` and replace its entire behavioral strategy.  Since
`C.card >= 2`, choose `j in C` with `j != i`.  Player `j` is not controlled by
the deviator and still Quits surely at that root.  Therefore the game also
absorbs at the root under every complete unilateral replacement by `i`.

It follows that the continuation tail is reached neither under prescribed
play nor under any strategy over which player `i`'s best-response supremum is
taken.  The semantic pair immediately before the pure root is consequently

\[
 \left(r(C),\ i\mapsto
   \max\{r_i(C\cup\{i\}),r_i(C\setminus\{i\})\}\right),
\]

with the project's extended-set convention covering membership and
nonmembership uniformly.  This expression is independent of `tau`.

Now prefix one common product root.  The complete semantic pair of the
prefixed profile is a deterministic function of that root and the continuation
semantic pair.  Equality therefore survives one common prefix.  Induction on
the finite list `W` proves equality after the whole word.  Projecting the pair
gives payoff and unrestricted-cap equality; unfolding debt gives coordinate
and total-debt equality.

The possible concern that one deviator chooses actions both before and after
the common prefix does not invalidate the induction.  The checked one-root
semantic-prefix identity itself quantifies over complete behavioral
replacements and proves that the continuation is summarized by its full
semantic pair.

## Source correspondence

The exact tail-independent semantic computation is
`quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.  I independently ran

```text
lake env lean UniformEquilibrium/Quitting/Paths/SureExitSet.lean
```

successfully in the current worktree.

The all-behavior one-root prefix identity is
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.  Literal finite
words are represented by `quittingLiteralRootStackProfile`, with the `nil` and
`cons` equations in
`UniformEquilibrium/Quitting/Root/LiteralExactPrefixStack.lean`.

For the current Fin4 ray, `rayBaseProfile` in
`Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean` is
literally a date-zero pure pair followed by the selected reference tail, and
`rayBaseProfile_semantic_eq` already applies the two-quitter computation.  The
outer `rayProfiles` are common maximal-cap prefix words placed before these
base profiles.  Thus changing only the reference tail after the pure pair
cannot change the corresponding whole semantic pair.

For the marked forced-pair presentation,
`forcedPair_postDateSpine_eq_reference` and `forcedTerminal_card` in
`Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean` identify
the literal post-mark reference tail and the cardinality-two screen.
`finFour_profile_eq_literalRootStack` in
`Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean` records the
additional common outer prefix.  These declarations do not supply a theorem
putting an arbitrary pre-mark continuation in the minimum-fibre tube.

## Falsification tests

### Singleton marked coalition

The cardinality bound is sharp.  Take players `i,j`, mark the pure singleton
`{i}`, and set

\[
 r_i(\{i\})=0,\qquad r_i(\{j\})=r_i(\{i,j\})=1.
\]

With an all-Continue tail, player `i`'s cap after the singleton root is `0`.
With a tail in which `j` Quits surely at the next date, player `i` can Continue
at the marked row and obtain `1`.  Thus tail independence fails for
`C.card=1`.

### Non-pure marked root

If every member of a nominal pair Quits only with probability strictly below
one, then after one player's replacement there can be positive probability
that every remaining opponent Continues.  Two tails with different continuation
values can therefore produce different caps.  Purity, or equivalently a sure
remaining quitter after every unilateral replacement, is essential.

### Different prefix words

If the two profiles use different words before the screen, fresh prefix
absorption and the probability of reaching the sure-exit row can differ.  The
conclusion is false in general.  The theorem requires the same literal `W`.

These failures also show why the theorem is not a universal no-go for seam or
commutator constructions.

## Export assessment

The theorem gives an exact impossibility result for the direct post-mark
signed-toll completion of the strict normalized-passport arm.  Together with
the independent `HUYGENS` review, it satisfies the extra review requirement
arising from equality of unrestricted behavioral caps.  I recommend export
only in the corrected narrow form above.
