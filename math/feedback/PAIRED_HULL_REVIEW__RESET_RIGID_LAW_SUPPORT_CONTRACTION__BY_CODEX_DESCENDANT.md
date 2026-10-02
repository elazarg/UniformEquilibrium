# Review of reset-rigid law-support contraction

Reviewer: `CODEX_DESCENDANT`

Verdict: **REVISE, with one bounded proof gap; the contraction and its two
case arguments otherwise pass.**  The missing step is not a new game-theoretic
idea, but it is needed because Output B explicitly promises joint
semantic/law convergence of the freshly prefixed child chronology.

## Claim checked

The note claims that a reset-rigid positive global-minimum joint point yields
either:

1. an actual source-attached off-minimum paid port; or
2. a source-attached global-minimum chronology whose limiting law has zero
   Never mass and a fixed positive singleton coordinate.

It splits the law into positive Never, zero Never with no singleton, and zero
Never with a positive singleton.  The last case is retained as the exact
unconsumed residual.

## Parts which pass

### Zero Never and zero singleton

The closed-law product-base theorem applies exactly.  Its strict singleton
margin at a positive global minimum removes the padding row and realizes the
same complete semantic pair and the same law by a product root followed by
Never.  The product root has at least two sure quitters.  This is an actual
finite-clock global minimum, so the reviewed finite-clock deadline-rank
theorem produces an actual off-minimum profile and an outgoing unrestricted
pure-time/Never response of gain greater than `D_*/4`, with literal finite
ancestry.  No full-debt hypothesis is needed for this use of the finite-clock
theorem.

### Positive Never release

The finite-support compression and late cap are used correctly.  On the
joint-Never event the capped player produces the singleton terminal, and off
that event the finite-support source and target have the same terminal
outcome.  Thus the payoff gain and singleton mass are exact before the common
prefix.  The fresh exact source word has Continue product tending to one, so
the displayed `q/4` and fixed-gain floors survive.  The target is not asserted
to be Nash after the late release.

Joint compactification of the actual targets is legitimate.  If the target
limit is strictly off minimum, one sufficiently late target is an actual
off-minimum profile, and the hard terminal gap supplies its outgoing paid
response.  If the target limit is minimum, its law has exactly zero Never
mass and singleton mass at least `q/4`.

### Debt restriction

For any player `i`, cap its finite-support clock strictly after the common
finite support.  The only changed event is joint Never, so the exact payoff
difference is `q_n s_i`.  Passing through the semantic approximation gives

\[
 d_i(z)\ge q s_i.
\]

Together with nonnegativity of debt this is precisely

\[
 d_i(z)\ge q(s_i)_+.
\]

The zero-debt reset owner therefore has nonpositive singleton reward when
`q>0`.  The hard terminal witness supplies a distinct positive-singleton
owner.  The signs and quantifiers in this part are correct.

### Residual classification and provenance

The three law cases are exhaustive.  Same-law reset moves cannot recreate
positive Never after reaching the zero-Never face.  The remaining
zero-Never/positive-singleton case honestly re-enters the known singleton
compression/forced-pair waist; the note does not call the same-date pair edge
a chronological Nash edge and does not claim that cross-coordinate cap
leakage is controlled.

The source distinctions are also correct: exact roots are chosen for the
source to which they are attached; no source word is reused after the target
strategy changes; and the late singleton is a suffix stage atom rather than
fresh exact-root absorption.

## Required repair

In the minimum-target branch of Section 4, (4.5) and the resulting Continue
product tending to one do prove that the fresh prefix becomes invisible, but
the note currently uses only the debt squeeze and then immediately asserts a
jointly convergent child chronology.  Debt convergence alone would not imply
semantic or law convergence.  Add the following short argument.

Let `a_{n,t}` be the absorption probability of row `t` in the fresh exact
word and let

\[
 c_n=\prod_t(1-a_{n,t})\longrightarrow1.
\]

Then

\[
 \sum_t a_{n,t}\le -\log c_n\longrightarrow0.
\]

Hence the word's ordinary absorption probability tends to zero.  For every
player, the probability that one of that player's opponents absorbs inside
the word is bounded by the same sum, so it also tends to zero.  Coupling the
freshly prefixed profile to `Q_n` now gives:

* total-variation convergence of its terminal law to the law of `Q_n`;
* convergence of every prescribed payoff coordinate; and
* uniform convergence over every unilateral behavioral response, hence
  convergence of every unrestricted cap coordinate.

Therefore the freshly prefixed joint semantic/law points converge to the
same `y`, while the shifted singleton coordinate retains (say) the `q/8`
floor.  This completes the exact source-faithful chronology promised by
Output B.

Also replace any unqualified phrase that prefixing occurs “without changing
the semantic point or law” by “without changing the limiting semantic point
or law”; each finite prefix can change both.

## Disposition

After this bounded repair, I find no mathematical obstruction.  The result
is a genuine contraction of reset-rigid law support to the zero-Never,
positive-singleton residual or the actual off-minimum paid-port waist.  It is
not a reset-rigid chamber consumer and should not be exported as one.
