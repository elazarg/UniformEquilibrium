# Review of `gpt/TOGGLE.md`

Reviewer: `SOCIAL_WEIGHT_REVIEW`

Verdict: **REVISE (the horizontal theorem is valid; the temporal conclusion is
not).**

## Claim checked

The note starts from the pure date-zero pair profile \(\sigma^P\), computes
its unrestricted behavioral caps, chooses a player with debt at least
\(D_*/4\), and toggles that player's date-zero action.  In the outsider case
it then calls the resulting unilateral replacement an "exact charged temporal
edge" and appends it to the retained source path.

## Valid part

The cap identity is correct:

\[
B_i(\sigma^P)=\max\{r_i(P),r_i(P\mathbin\triangle\{i\})\}.
\]

At least one opponent quits surely at date zero after every unilateral
behavioral replacement by \(i\), so late stopping and Never add no response
value.  Hence a maximal-debt player has a literal complete best response of
gain at least \(D_*/4\), and its debt at the target is zero.  This holds for
both member-leaving and outsider-joining toggles.  It is a useful instance of
the already exported finite pure-clock exact-response geometry.

## Typing failure

The outsider join is **not** thereby a Nash--Bellman temporal edge.  The
checked definition `IsQuittingNashBellmanEdge` in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean` requires
both

1. the current payoff to be the Bellman successor payoff of one displayed
   root against the supplied tail payoff, and
2. that displayed root to be exact endpoint Nash for **every** player.

The toggle proves only that the joining outsider's changed complete strategy
is a best response to the three unchanged strategies.  It gives no endpoint
Nash inequality for the other three players.  Indeed the source date-zero
root cannot be exact Nash: the chosen outsider has strictly positive debt at
that very root.  At the target the outsider is best responding, but the other
players' inequalities remain uncontrolled.

Sure absorption of both horizontal endpoints proves only that the payoff
difference is undiluted.  It does not turn a replacement of one complete
strategy into a predecessor/successor Bellman relation.  Nor does literal
profile equality at the end of the retained replacement ancestry make the
new target the next tail state of an in-game chronology.

There is no automatic alternative temporal interpretation.  A sure-absorbing
root can reproduce the terminal reward cell, but it is an exact
Nash--Bellman root only after all four endpoint inequalities are supplied.
Those hypotheses are exactly what the argument lacks.

## Required correction and frontier value

Replace every occurrence of "temporal edge", "temporal charge", and
chronological path extension by:

> literal horizontal one-player unrestricted-best-response edge, with exact
> gain at least \(D_*/4\) and zero target debt for the mover.

With that correction the conclusion is sound, but it does not close either
case.  It is subsumed by the finite literal pure-clock response-cycle packet,
whose explicit nonclaim is that horizontal response dynamics is not an
in-game Nash--Bellman chronology.  A genuine consumer still needs an exact
root for all players, a punishment-floor admissible chronology, a renewable
minimum-fibre rank, or a charged near-return.

