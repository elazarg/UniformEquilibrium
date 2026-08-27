# Pure nonsingleton common-prefix tail screening

Author: `CODEX_CURIE`

Independent reviews:

- [HUYGENS](../feedback/CODEX_CURIE__STRICT_INERT_DIFFUSE_TOLL_ORIENTATION__BY_HUYGENS.md)
- [CODEX_STOKES](../feedback/CODEX_CURIE__STRICT_INERT_DIFFUSE_TOLL_ORIENTATION__BY_CODEX_STOKES.md)

## Exact statement

Let `I` be a finite player set and let

\[
 r:\{C\subseteq I:C\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a finite quitting-game reward table.  Infinite continuation pays zero.
Strategies are arbitrary behavioral strategies: at each unresolved public
history a player may randomize between Quit and Continue, and a unilateral
deviation replaces that player's complete behavioral strategy.

For a behavioral profile `sigma`, write

\[
 U_i(\sigma)
\]

for its prescribed terminal payoff and

\[
 B_i(\sigma)
   :=\sup_{\tau_i}U_i(\sigma[i\leftarrow\tau_i])
\]

for the supremum over all unilateral behavioral replacements.  Put

\[
 \operatorname{Sem}(\sigma)=(U(\sigma),B(\sigma)),\qquad
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),\qquad
 D(\sigma)=\sum_i d_i(\sigma).
\]

Let `C subseteq I` satisfy `|C| >= 2`.  Let `pure(C)` be the product root at
which exactly the members of `C` Quit surely.  Let

\[
 W=(q_0,\ldots,q_{m-1})
\]

be any finite word of product roots.  For arbitrary behavioral tails `tau`
and `tau'`, define

\[
 P_\tau=W*((\operatorname{pure}(C))*\tau),\qquad
 P_{\tau'}=W*((\operatorname{pure}(C))*\tau').
\]

Then

\[
 \boxed{\operatorname{Sem}(P_\tau)=
        \operatorname{Sem}(P_{\tau'}).}
\tag{1}
\]

Consequently, for every player `i`,

\[
 U_i(P_\tau)=U_i(P_{\tau'}),\qquad
 B_i(P_\tau)=B_i(P_{\tau'}),
\tag{2}
\]

and therefore

\[
 d_i(P_\tau)=d_i(P_{\tau'}),\qquad
 D(P_\tau)=D(P_{\tau'}).
\tag{3}
\]

### Direct signed-toll no-go

Suppose a proposed repair of an actual source profile changes only the
behavioral tail strictly after a retained pure nonsingleton marked row and
keeps both that row and the whole finite prefix before it literal and fixed.
Then the repair cannot change any prescribed payoff, unrestricted behavioral
cap, coordinate debt, or total debt of the whole source profile.  In
particular, a positive signed payoff or debt account constructed solely in the
post-mark tail cannot by itself repair the whole source.

## Conjecture-facing change

The strict normalized-passport arm in
`questions/FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md` retains a pure
marked pair.  Its supplied minimum-fibre anchor is the post-mark reference
tail, while the positively reached whole source lies before the pair.  A
proposed completion attempted to orient a positive aggregate toll in a
successor word based at that minimum tail and use it as a paid move of the
whole strict-arm source.

The theorem proves that this direct post-mark completion is impossible: the
pure pair is an exact semantic screen, including for unrestricted behavioral
caps.  Hence the remaining strict-arm proof must do at least one of the
following:

1. act on the outer prefix itself;
2. produce a pre-mark repair whose continuation has an independently proved
   minimum-fibre anchor;
3. replace the marked pair by a root with positive unilateral continuation
   reach; or
4. prove a source-matched seam or commutator theorem transporting the
   post-mark account to a pre-mark paid edge.

This removes one purported completion of the strict arm.  It does not consume
that arm or prove a uniform-equilibrium payoff.

## Definitions and assumptions

At one unresolved date, a product root specifies independent Quit/Continue
distributions for all players.  `q * tau` plays `q` at the current date and,
only if everyone Continues, resumes `tau` at the next date.  A finite word is
composed chronologically by

\[
 [] * \tau=\tau,\qquad
 (q::W)*\tau=q*(W*\tau).
\]

No stationarity, finite support, finite memory, or bounded stopping-time
assumption is made about `tau`, `tau'`, or a unilateral deviation.  In
particular, Never and arbitrarily late stopping are included.

The common-word hypothesis means literal equality of all roots in `W`, not
semantic equivalence of two independently selected prefixes.

## Proof

### Lemma 1: one pure nonsingleton root screens its tail

Fix an arbitrary tail `tau`.  Prescribed play at `pure(C)` absorbs immediately
in coalition `C`, so its prescribed payoff is `r(C)` and is independent of
`tau`.

Fix player `i` and allow `i` to replace its complete behavioral strategy.
Since `|C| >= 2`, there is a player

\[
 j\in C\setminus\{i\}.
\]

Player `j` is an opponent of `i` and still Quits surely at the marked root.
Therefore, under every complete unilateral behavioral replacement by `i`, the
game absorbs at that root.  The continuation `tau` is never reached.

The only effective choice by `i` is its current Boolean endpoint.  If it Quits,
the terminal coalition is `C union {i}`; if it Continues, it is `C minus {i}`.
The latter remains nonempty.  Hence

\[
 B_i((\operatorname{pure}(C))*\tau)
 =\max\{r_i(C\cup\{i\}),r_i(C\setminus\{i\})\}.
\tag{4}
\]

Both the payoff and cap coordinates are thus independent of `tau`, and

\[
 \operatorname{Sem}((\operatorname{pure}(C))*\tau)
 =
 \left(r(C),,i\mapsto
   \max\{r_i(C\cup\{i\}),r_i(C\setminus\{i\})\}\right).
\tag{5}
\]

The same formula holds for `tau'`.

### Lemma 2: a common root preserves semantic equality

For every product root `q`, the one-step Bellman identity has the form

\[
 \operatorname{Sem}(q*\sigma)
   =T_q(\operatorname{Sem}(\sigma)),
\tag{6}
\]

where `T_q` is a deterministic finite-dimensional map depending only on `q`
and `r`.  Its cap coordinate is the full all-behavior cap identity, not a
stationary restriction.  Therefore

\[
 \operatorname{Sem}(\sigma)=\operatorname{Sem}(\sigma')
 \Longrightarrow
 \operatorname{Sem}(q*\sigma)=\operatorname{Sem}(q*\sigma').
\tag{7}
\]

### Completion

Equation (5) gives equality immediately after the pure nonsingleton root.
Apply (7) successively to the common roots of `W`, from the innermost root to
the outermost.  This proves (1).  Equations (2) and (3) follow by projection
and the definitions of coordinate and total debt.

The argument covers a deviator that changes its behavior both before and after
the marked row: equation (6) already takes a supremum over complete behavioral
replacements.  No interchange of a supremum and a limit is used.

## Boundary tests

### The cardinality assumption is sharp

Take two players `i,j`, let the marked coalition be the singleton `{i}`, and
set

\[
 r_i(\{i\})=0,\qquad
 r_i(\{j\})=r_i(\{i,j\})=1.
\]

After the pure singleton root, an all-Continue tail gives player `i` cap zero.
If instead `j` Quits surely at the next date, player `i` can Continue at the
marked row and obtain one.  Thus tail independence fails when `|C|=1`.

### Purity is essential

If the displayed pair members Quit only with probabilities below one, then
after one player's replacement there may be positive probability that every
opponent Continues.  Different tails can then produce different continuation
payoffs and caps.

### The prefix must be common

Different prefix words may have different fresh absorption laws and different
probabilities of reaching the sure-exit row.  The theorem does not compare
independently selected prefixes.

These exact failures prevent the no-go from being misread as a ban on
pre-mark, non-pure, or different-word repairs.

## Source correspondence

The checked all-behavior identity

```text
quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
```

in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean` is equation (5) in the
project's extended set-reward notation.  It computes the complete semantic
pair and therefore already includes arbitrary behavioral deviations.  The
one-root semantic Bellman identity is

```text
quittingTerminalSemanticPair_rootThenContinuation
```

in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.  Finite
literal words are represented by

```text
quittingLiteralRootStackProfile
quittingLiteralRootStackProfile_nil
quittingLiteralRootStackProfile_cons
```

in `UniformEquilibrium/Quitting/Root/LiteralExactPrefixStack.lean`.

The new mathematical content to expose is the common-word wrapper and its
explicit use as a strict-arm no-go.  The base two-quitter computation itself
already exists.

For the source-facing Fin4 ray,
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.rayBaseProfile` in
`Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean` is a
date-zero pure pair followed by the selected reference tail, and
`rayBaseProfile_semantic_eq` applies the checked two-quitter theorem.
`QuittingCommonSemanticMarkedBaseFamily.rayProfiles` in
`Research/Quitting/MaximalCapSemanticPrefixReturn.lean` puts the same explicit
maximal-cap word before the corresponding base row.

In the marked forced-pair presentation,
`forcedPair_postDateSpine_eq_reference` and `forcedTerminal_card` in
`Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean` retain
the post-mark reference tail and cardinality-two row.
`QuittingMarkedPairMinimumReturnActualizer.finFour_profile_eq_literalRootStack`
in `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean` retains the
additional common outer word.

These source fields provide the screened post-mark tail.  They do not provide
a minimum-tube hypothesis for the continuation seen at an arbitrary pre-mark
insertion point.

## Adapter and consumer

The actual-data adapter takes:

1. the retained forced pair, whose cardinality is exactly two;
2. its literal post-mark reference tail; and
3. any fixed finite literal outer prefix used by the actualized descendant or
   maximal-prefix ray.

It instantiates `C` with the forced pair, `tau` with the supplied reference
tail, and `W` with the retained outer word.  Any alternative post-mark repair
tail is `tau'`.

The conclusion is a no-go consumer rather than a uniform-payoff consumer: it
proves that a direct post-mark signed-toll repair cannot alter the strict-arm
whole semantic point.  The live target is thereby narrowed to outer-prefix or
seam-crossing mechanisms.  No new residual object is introduced.

## Lean handoff

The narrow theorem should be stated generically:

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

For the empty word, rewrite both sides with
`quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`.
For a cons word, rewrite with `quittingLiteralRootStackProfile_cons` and
`quittingTerminalSemanticPair_rootThenContinuation`, then apply congruence to
the induction hypothesis.

Payoff, cap, coordinate-debt, and total-debt corollaries should be derived from
the semantic equality.  A Fin4 specialization may package the forced-pair and
maximal-ray fields, but it must only conclude invariance under changing the
post-mark tail with the same prefix and pure pair.  It must not assert that an
arbitrary pre-mark continuation is the bare pair point or is outside the
minimum tube.

## Scope and nonclaims

The theorem does not:

- consume the strict normalized-passport arm;
- rule out changing a pre-mark root;
- rule out a pre-mark word whose continuation is separately proved to be near
  the minimum fibre;
- cover a non-pure marked root with positive opponent-continuation mass;
- compare different outer prefix words;
- rule out a commutator or seam theorem transporting post-mark charge to a
  pre-mark edge;
- create a chronological return, rank descent, terminal approximation, or
  uniform-equilibrium payoff; or
- assert anything about the existence of a positive-gap table.

It proves exactly that a tail-only signed-toll repair behind a fixed pure
nonsingleton screen is semantically invisible to the whole source, even for
unrestricted behavioral caps.

## Formalization record

The packet is formalized by one generic production theorem layer and one
actual-data Fin4 maximal-ray adapter.

1. `UniformEquilibrium/Quitting/Paths/PureNonsingletonCommonPrefixScreening.lean`
   proves `quittingTerminalSemanticPair_literalRootStack_congr` by induction
   on the common literal root word and then applies the checked pure-set
   all-behavior identity in
   `quittingTerminalSemanticPair_literalRootStack_pureSet_screen`.
   `quittingTerminalPayoff_literalRootStack_pureSet_screen` and
   `quittingContinuationBestResponseValue_literalRootStack_pureSet_screen`
   expose the prescribed-payoff and unrestricted-cap coordinates.
   `quittingTerminalSemanticDebt_literalRootStack_pureSet_screen` and
   `quittingTerminalSemanticDebtSum_literalRootStack_pureSet_screen` give
   coordinate and total-debt equality; their two named `_sub_..._eq_zero`
   corollaries state the literal signed zero changes.
2. `Research/Quitting/FinFourProducerAtlas/PureNonsingletonCommonPrefixScreening.lean`
   specializes the theorem to one fixed
   `FinFourOwnerCompressedMinimumReturnForcedPairPacket`.
   `rayScreeningWord`, `rayTailReplacementBaseProfile`, and
   `rayTailReplacementProfile` retain the packet's `raySource`, actual index,
   unchanged maximal-prefix word, pure pair, and arbitrary replacement tail.
   `rayScreeningWord_length`,
   `rayTailReplacementProfile_eq_literalRootStack`,
   `rayProfiles_eq_literalRootStack_purePair`, and
   `rayScreeningTerminal_card` expose that provenance literally.
3. `rayTailReplacementProfile_semantic_eq_actual` and
   `rayTailReplacementProfile_semantic_eq_orbit` identify every such
   replacement with the actual indexed ray semantics.
   `rayTailReplacementProfile_debt_eq_actual`,
   `rayTailReplacementProfile_debtChange_eq_zero`,
   `rayTailReplacementProfile_wholeDebt_eq_actual`, and
   `rayTailReplacementProfile_wholeDebtChange_eq_zero` give the exact debt
   account.  `rayTailReplacementProfile_wholeDebt_tendsto_rayLimit` retains
   the actual scalar limit for an arbitrary varying family of post-pair tails.
4. `rayTailReplacementBaseProfile_outcomeMass_eq_pointMass` proves that the
   replacement base law is the Dirac law at the fixed pair.
   `rayTailReplacementProfile_outcomeMass_eq_actual` proves equality of the
   complete terminal-outcome laws after the common outer word.  It does not
   call that outer law Dirac, because an outer root may absorb first.
5. `not_exists_positiveDebtChange_rayTailReplacement`,
   `not_exists_positiveWholeDebtChange_rayTailReplacement`, and
   `not_exists_positivePayoffChange_rayTailReplacement` are the checked
   architecture no-go consumers.  They exclude only positive repair obtained
   by changing the tail strictly behind the retained word and pure pair.

Evidence seals:

- **M:** PASS.  Pure nonsingleton screening covers arbitrary behavioral tails
  and unrestricted complete-strategy deviations; the common-word induction
  and the terminal-law transport preserve the literal constants and signs.
- **L:** PASS.  The generic and Fin4 declarations are checked Lean.  Direct,
  named, production-reader, Research-reader, full, axiom, trust, import-graph,
  documentation, duplicate-proof, derivable-telescope, generated-file, unit,
  and source-format checks passed at promotion.
- **A:** PASS for the Fin4 declarations.  The adapter takes one actual
  source-attached maximal-prefix packet and retains its source, word, index,
  pair, reference tail, actual ray profile, outcome law, and debt limit.  The
  generic production theorem remains a supplied-word theorem.
- **C:** PASS only as the negative tail-repair consumer stated above.  It
  closes that architecture while leaving every positive strict-ray branch and
  every mechanism that changes or crosses the marked row open.

The common prefix is literal, not merely semantically equivalent, and the
pure coalition has cardinality at least two.  The result does not compare two
different words, cover a non-pure marked root, change or screen the marked
root itself, eliminate the strict maximal ray, transport charge across a
pre-mark seam, regenerate a source, produce chronology or rank descent, give
terminal approximation, or prove a uniform-equilibrium payoff or
counterexample.  The mathematical provenance remains the CODEX_CURIE packet
and the two independent reviews linked at its head; no external paper theorem
is imported.
