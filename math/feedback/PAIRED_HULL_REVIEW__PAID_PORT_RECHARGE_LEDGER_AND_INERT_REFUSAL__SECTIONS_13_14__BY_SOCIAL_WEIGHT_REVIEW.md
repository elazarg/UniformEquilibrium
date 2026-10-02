# Review of Sections 13--14: receiving-earlier recharge and the response-tail ledger

Reviewer: `SOCIAL_WEIGHT_REVIEW`

Note reviewed:
[PAIRED_HULL_REVIEW__PAID_PORT_RECHARGE_LEDGER_AND_INERT_REFUSAL.md](../notes/PAIRED_HULL_REVIEW__PAID_PORT_RECHARGE_LEDGER_AND_INERT_REFUSAL.md),
corrected Sections 13--14.

## Verdict

**REVISE, bounded.**  The receiving-earlier stage-absorption equality, the
finite complement Nash reduction, the unique-owner-debt conclusion, the
eight-cell split, the nonattained-cap epsilon repair, and the exact ledger
(14.2)--(14.4) are correct.  The supplied-family minimum causalization is
also a legitimate source construction over the literal response targets.

One sentence after (14.4) is too strong: a positive free-player *root defect*
does not in general admit a literal pure best-endpoint update on the same
complete response tail.  If Continue is the best endpoint, its value uses
the unrestricted continuation cap, and realizing it requires an approximate
complete tail response (which may change that player's tail and need not
attain the cap).  The output is therefore a positive current root defect and
an epsilon-family of literal horizontal responses, not automatically one
exact pure row update on the unchanged tail.

The causalization should also be described as source-faithful to the supplied
target family `Y_n`.  It does not by itself transport the incoming
`P -> Y_n` paid-response edge through the newly selected prefixes, and hence
does not create a renewable transition from the old paid source.

## 1. Receiving-earlier absorption

When `row.receivingEarlier = true`, chronology identifies the receiving pure
time with `some row.start`.  Before that date the observer Continues surely,
and at that date it Quits surely.  Updating the observer does not alter any
opponent hazard.  Thus joint reach to the marked date is exactly the deleted
opponent survival `ell`, and conditional absorption there is one:

\[
 \Pr_P(\text{absorption at the marked row})=\ell.
\]

The checked inequality `gain_le_liveMass` then gives

\[
 \ell\ge g/(2M).
\]

Positive gain excludes the boundary `M = 0`.  This is an actual stage-mass
identity and does not confuse terminal atom mass with causal row mass.

## 2. Complement Nashification and concentration of debt

Fixing the observer `i` to Quit surely makes the continuation unreachable.
For each free player `j`, every complete behavioral deviation is payoff-
equivalent to choosing one of the two actions at the first row.  A product
Nash equilibrium of

\[
 u_j(A)=r_j(\{i\}\cup A)
\]

therefore gives the full unrestricted statement

\[
 d_j(Z)=0\qquad(j\ne i).
\]

Because `Z` is an actual behavioral profile, global minimality gives
`D(Z) >= D_*`; debt nonnegativity then yields

\[
 d_i(Z)=D(Z)\ge D_*.
\]

This is not merely a root-Nash conclusion.  It is an exact cap conclusion
because the sure-Quit owner screens all later behavior of every free-player
replacement.

## 3. Eight-cell split and epsilon response

The owner's Quit endpoint is the product average of `Q_i(A)`.  Its Continue
endpoint is the product average of `C_i(A)`, with the empty cell valued by the
unrestricted suffix cap.  Since the owner debt is strictly positive, the
Continue endpoint is the cap endpoint, so

\[
 d_i(Z)=\sum_{A\subseteq F}p(A)(C_i(A)-Q_i(A)).
\]

Among eight cells one has weighted contribution at least `D_*/8`.  Since
both a terminal reward and a continuation cap lie in the reward box,
`|C_i(A)-Q_i(A)| <= 2M`, and hence the selected positive cell obeys

\[
 p(A)\ge D_*/(16M).
\]

For nonempty `A`, owner-Continue leaves the free coalition `A` absorbing at
that row.  The current text correctly repairs nonattainment: for every
`epsilon > 0`, choose a complete continuation response within `epsilon` of
the suffix cap.  The resulting literal target has

\[
 d_i(Y_\varepsilon)\le\varepsilon,
 \qquad
 a(Y_\varepsilon)\ge p(A).
\]

No exact cap-attaining strategy is needed or asserted.  The empty-cell arm
is correctly left as the cap/tail seam.

## 4. Minimum-cluster causalization: exact scope

After passing to a convergent joint semantic/law subsequence, the minimum
arm supplies a point with exact owner debt zero and retained row-zero
`A`-mass at least `D_*/(16M)`.  The hypotheses of
`nonempty_sourceFaithfulMinimumCausalization` in
`Research/Quitting/SourceFaithfulMinimumLawCausalization.lean` are then met
with:

- `profiles n = Y_n`;
- `mark n = 0`;
- terminal coalition `A`; and
- any positive `lambda <= D_*/(16M)`.

The theorem keeps these literal suffix profiles and marks, selects finite
exact cap--Nash words, makes their survival tend to one, and preserves an
eventual positive shifted atom floor.  Thus it really does construct a
complete source-faithful chronology **over the response-target family**.

It does not store or transport the earlier incoming response edge from `P`
or `Z` to `Y_n`.  Copying the selected prefix to both endpoints and proving
the backward edge would require a separate common-prefix wrapper.  Therefore
this landing is a regenerated minimum source, but it is not yet a renewable
paid-source transition or a rank edge.  Sections 13.2 and 14 otherwise state
the absence of such a rank honestly; wording such as "followed by the
regenerated source" should not be read as preserving the incoming ancestry.

## 5. Exact root-versus-tail ledger

Let `q` be the unchanged marked root with owner Continue and free law `x`,
let `T_epsilon` be the literal response tail, and write

\[
 c=p(\varnothing),\qquad
 E_\varepsilon=D(T_\varepsilon)-D_*.
\]

The owner's cap is invariant under its own strategy replacement.  The same
strict endpoint comparison that produced positive owner debt in `Z` therefore
makes Continue the owner's exact best root endpoint against `T_epsilon`; its
root defect is zero.  The exact prefix debt identity gives

\[
 D(Y_\varepsilon)=c(D_*+E_\varepsilon)+N_\varepsilon.
\]

Since `Y_epsilon` is actual and `D(Y_epsilon) >= D_*`, rearrangement yields

\[
 N_\varepsilon+cE_\varepsilon
 \ge (1-c)D_*
 \ge \rho D_*.
\]

The inclusive split (14.4) is valid: if `E_epsilon < rho D_*/2`, then
`c E_epsilon <= E_epsilon`, so `N_epsilon >= rho D_*/2`.  As the owner
contributes zero, some free player has root defect at least
`rho D_*/6`.

## 6. Remaining repair: root defect is not an unchanged-tail response

For a free player `j`, the Continue endpoint appearing in its root defect is
computed using `B_j(T_epsilon)`, not the prescribed tail payoff
`U_j(T_epsilon)`.  If `d_j(T_epsilon) > 0`, changing only `j`'s current
action to Continue while keeping its old tail strategy realizes the latter,
not the former.  If the cap is not attained, there is not even one exact
complete response realizing the endpoint.

Accordingly, replace

> Its pure best-endpoint update is a literal next horizontal response on the
> same response tail.

by the following scoped conclusion:

> The same actual current root and literal continuation exhibit a free-player
> root defect of at least `rho D_*/6`.  For every positive approximation
> tolerance, a complete behavioral response can choose the corresponding
> pure current endpoint and, in the Continue arm, an approximately optimal
> continuation.  This is a literal horizontal response against unchanged
> opponents, but its player component may change throughout the tail.

This repair leaves (14.2)--(14.4) unchanged.  It also reinforces the stated
nonclaim: the ledger is a two-level causal certificate, not an exact
Nash--Bellman edge, terminal consumer, or renewable rank.

## 7. Boundary tests

- If the selected cell is empty, there is no row absorption after owner
  Continue; the cap/tail arm remains.
- If a free player's current defect is carried entirely by continuation
  debt, row-only purification realizes none of that debt.  This is the exact
  countertest to the sentence identified above.
- Complement Nash may be all Continue; positive minimum does not force a
  nonempty selected cell.
- Recomputing a complement Nash after changing the owner can reactivate every
  previous zero debt.  No zero-set or anchor-cardinality rank follows.
- The newly causalized `Y_n` source need not retain an incoming paid edge from
  the original marked source.

After the bounded response-typing repair and provenance clarification, the
sections are mathematically sound.  They narrow the receiving-earlier arm to
an inert tail, an off-minimum response tail, or a positive current free-player
refusal, but they do not consume any of those outputs.

## Addendum: review of Sections 15--16

### Verdict

**REVISE, bounded.**  The two mathematical contractions are valid:

1. a nonempty selected cell gives a strong concentrated-singleton packet,
   directly when the cell is a singleton and through the checked pure
   nonsingleton screening orbit otherwise; and
2. in the empty-cell arm, the literal reached response tail inherits the
   owner's vanishing debt by the exact scaling identity
   `d_i(Y_epsilon) = c d_i(sigma^+_epsilon)`.

The remaining repairs concern exact mass and ancestry scope.  Pure
nonsingleton screening starts with a simultaneous pure overwrite; it does
not transport the original mixed-cell atom through a unilateral edge.  If a
singleton cell is first put behind newly selected causal prefixes, its exact
stage mass is multiplied by prefix survival, so the original closed floor
`rho` may be lost at equality; `rho/2` is a uniform safe scale.  Finally,
minimum causalization of the empty-cell successor tails uses a newly selected
positive finite-law atom and marks.  It keeps the tail family but does not
automatically retain the incoming `Y_epsilon -> sigma^+_epsilon` transition
through the new prefixes.

### 8. Nonempty cell to strong singleton packet

If `A` is a singleton, (13.11) directly supplies the hypotheses of
`FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass`
at the unprefixed literal target `Y_n`, with resolution

\[
 \rho=D_*/(16M).
\]

If `|A| >= 2`, the generic pure-nonsingleton screening theorem applies at
the same date and over the same complete post-row tail.  Its first operation
is a simultaneous overwrite of the marked root by the pure coalition `A`.
From that pure sibling, every strict endpoint edge is a literal one-player
same-date update, preserves the off-date profile, and routes the pure marked
mass without loss.  In Fin4 the checked no-closed-segment theorem reaches a
pair within at most three strict edges, and the final (not necessarily
profitable) pair route gives a singleton.  Thus a strong singleton packet is
indeed produced.

Two qualifications are necessary.

First, the no-loss statement begins **after the pure overwrite**.  The
original `A` occurrence inside the mixed law `x` is not itself followed
through a unilateral path.  What is retained from it is the support label,
date, complete tail, and a quantitative scale; the simultaneous pure sibling
creates stage mass equal to the date's live mass.

Second, suppose one first causalizes `Y_n` by exact prefix words whose joint
survival `S_n` tends to one.  For a singleton `A`, its shifted stage mass is

\[
 S_n p(A).
\]

If `p(A)=rho` and every `S_n<1`, no rank has mass at least the closed floor
`rho`.  The causalization theorem guarantees an eventual `rho/2` floor, and
any fixed scale strictly below `rho` is available cofinally.  Therefore the
phrase "the same fixed mass floor" is exact on the original `Y_n` family but
must become `rho/2` (or an arbitrary smaller positive scale) when the packet
is required on the newly prefixed singleton chronology.  In the
nonsingleton case the subsequent pure overwrite has mass equal to prefix
live mass, so `rho` is eventually available, but the unified statement should
use the safe half-scale.

With that repair, the checked `consumerResult` yields precisely the strategic
singleton arm or the collision-minimum residual.  This is a finite stopped
screening orbit, not a monotone coalition-cardinality descent: strict edges
may join as well as leave.  It gives a bounded internal orbit/rank only after
the orbit witness is selected, and gives no renewable outer source rank.

### 9. Empty cell: exact successor debt scaling

In the empty-cell arm, `c=p(empty)>=rho`.  The owner Continues at the marked
root and Continue is its exact best root endpoint.  Hence its coordinate root
defect is zero.  The coordinatewise prefix formula is exactly

\[
 d_i(Y_\varepsilon)=c\,d_i(\sigma^+_\varepsilon).
\]

Together with `d_i(Y_epsilon)<=epsilon`, this proves

\[
 d_i(\sigma^+_\varepsilon)
 \le {16M\over D_*}\varepsilon.
\]

This part is fully literal.  Conditional on the empty cell, the actual
response target reaches exactly `sigma^+_epsilon`, and any minimum joint-law
cluster of those tails has zero `i`-debt.

Under the hard residual, every supplied minimum joint-law point has a
positive finite coalition coordinate by
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`.  Thus the
weaker supplied-family theorem
`nonempty_sourceFaithfulMinimumCausalChronology` can causalize the actual tail
family.  It selects a terminal coordinate and positive dates from finite
windows; it does **not** retain a uniform stage-mass floor or any incoming
date family.  This distinction should replace the unqualified phrase
"supplied-family causalization" in Section 16.

Moreover, the newly selected exact prefixes sit over the tail profiles.  The
theorem does not itself copy those prefixes to the predecessor response
profiles or store the original root-to-tail transition.  Hence the valid
conclusion is:

- before causalization, a literal reached successor family with owner debt
  tending to zero; and
- after causalization, a complete minimum source over that same successor
  family, with the same limiting zero coordinate but reselected finite marks.

Calling this a literal successor transition *inside the regenerated source*
would require a separate common-prefix edge wrapper.  Section 16 correctly
notes the earlier complement-Nashification ancestry loss, but should add this
second post-causalization limitation.

If the tail cluster is strictly off minimum, it may feed the generic paid
port only after separately selecting the terminal-gap observer and paid row
on the tail family.  That observer need not be the current owner, and the old
paid passport is not inherited.  This is an adapter into the maintained
off-minimum paid waist, not consumption of it.

### 10. Net contraction

After these repairs, the exact orientation split is:

\[
\begin{array}{ll}
A\ne\varnothing:
 & \text{a strong singleton packet at a fixed positive scale,}\
 & \text{ending in the strategic or collision-minimum residual;}\\[1mm]
A=\varnothing:
 & \text{a uniformly reached literal tail whose current owner debt vanishes,}\
 & \text{then an off-minimum paid-port adapter or a newly causalized}\
 & \text{minimum source with that zero coordinate.}
\end{array}
\]

Neither line yields an outer renewable rank, a transported incoming paid
edge, a Nash--Bellman chronology, or a terminal uniform payoff.  The new
sections are nevertheless a genuine contraction once the pure-overwrite,
half-scale, and reselected-mark scopes are stated explicitly.
