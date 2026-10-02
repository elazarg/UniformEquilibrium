# Review of finite pure-clock exact-response cycles

Reviewer: `SOCIAL_WEIGHT_REVIEW`

Verdict on the mathematics: **PASS**.

Export recommendation: **do not export in its present form**.  The theorem is
a correct and useful horizontal normal form, but the named paid-cap question
explicitly requires a temporal Nash--Bellman consumer or renewable rank.  The
cycle supplies neither.  It is strong internal conference progress and could
become exportable if the project decides that replacing the arbitrary paid
port by one finite exact-response-cycle compiler obligation is itself a named
accepted reduction.

## Claim checked

From any pure-clock profile in a finite quitting game with global terminal
semantic debt bounded below by (D_*>0), deterministic maximum-debt exact
pure-clock replies remain in one finite inherited clock alphabet.  Their
orbit therefore reaches a literal nontrivial cycle.  Every edge is a complete
unrestricted behavioral best response, has mover gain at least (D_*/4) in
Fin4, and kills the mover's debt.  The arbitrary-clock minimum entrance can
be connected by literal replacements to a pure off-minimum starting point.

## Verification

### Unrestricted cap attainment

Against pure-clock opponents, a player's payoff from a pure stopping time has
only the three values listed in the note: singleton before the first opponent
deadline, collision at that deadline, and pass/late after it.  Never realizes
the last value.  A behavioral strategy is a stopping-time distribution, so
its payoff is an average of these values.  Hence a cap attainer exists in
({0,m_i,infty}), with the singleton option correctly omitted when
(m_i=0).  This covers the full behavioral response class.

### Finite alphabet and literal cycle

The inherited alphabet

\[
  \Lambda=\{0,\infty\}\cup\{t_i^0:t_i^0<\infty\}
\]

has at most six elements in Fin4.  Every first opponent deadline at a current
profile is a current coordinate, hence belongs to (Lambda), and the
canonical reply stays in (Lambda).  Thus the deterministic map acts on at
most (6^4) literal profiles.  Positive debt excludes a fixed point, so the
eventual period is nontrivial.  No quotient by calendar type is used.

### Gain, debt kill, and minimum hit

At every actual profile (x), carrier minimality gives (D(x)ge D_*), so a
maximum-debt player has (d_i(x)ge D_*/4).  Replacing only (i)'s strategy
does not change (B_i), and installing a cap attainer sets its prescribed
payoff equal to that cap.  Therefore the gain is exactly (d_i(x)), and the
target (i)-debt is zero.  These assertions remain valid when a target first
hits the minimum fibre.  Stopping there gives the note's minimum-return arm;
if no target hits the fibre, the repeated cycle is entirely off minimum.

### Source adapter

The arbitrary-clock purification packet already proves supported one-player
pure-clock replacement and permits uncontrolled nonmover cap leakage.  Apply
it successively to the strict off-minimum target.  The final pure profile is
still in the carrier, hence has debt at least (D_*).  If it is strict, it is
the required start.  If it equals (D_*), the checked
`pureTimeMinimum_exists_offMinimumPaidPort` theorem returns a literal
pure-clock descendant strictly above (D_*).  This is a finite literal
replacement ancestry; no limiting clock or unrelated carrier realizer is
introduced.

### Regression

The two-player four-state cycle in the note is correct.  Direct calculation
gives gain one on each edge, total debt one at every cycle state, and the
stated stationary exact equilibrium for every stationary quit rate
(q\in(0,1/2]) of player 2 with player 1 Never.  It is therefore an honest
warning that a horizontal best-response cycle is not itself a contradiction.

## Exact strengthening: the cycle leakage is payoff externality, not cap
holonomy

Let the cycle be (x^0,\ldots,x^L=x^0), let (i_k) move on edge (k), and
write

\[
  g_k=U_{i_k}(x^{k+1})-U_{i_k}(x^k)
      =d_{i_k}(x^k)\ge D_*/4.
\]

For a fixed player (j), put

\[
  G_j=\sum_{k:i_k=j}g_k.
\]

On an edge where (j) moves, its cap is unchanged and its payoff rises by
(g_k).  Telescoping the literal returned profile therefore gives the two
exact identities

\[
 \sum_{k:i_k\ne j}
   \bigl(B_j(x^{k+1})-B_j(x^k)\bigr)=0,
\tag{1}
\]

and

\[
 \sum_{k:i_k\ne j}
   \bigl(U_j(x^{k+1})-U_j(x^k)\bigr)=-G_j.
\tag{2}
\]

Consequently

\[
 \sum_{k:i_k\ne j}
   \bigl(d_j(x^{k+1})-d_j(x^k)\bigr)=G_j.
\tag{3}
\]

Summing (2)--(3) over players shows that among the (3L) nonmover edge
coordinates there is

* one prescribed-payoff externality at most (-D_*/12); and
* one nonmover debt increase at least (D_*/12).

The two witnesses need not be the same edge or recipient.  More importantly,
(1) shows that **aggregate cross-cap displacement cancels exactly around the
cycle**.  Thus the cycle does not create a cap-holonomy contradiction.  Its
positive debt leakage is paid exactly by negative prescribed-payoff
externalities from other players.  The checked role-swapped actual-reach
localization can turn the negative externality into a reached row, but that
row is still horizontal and need not benefit its controller.

This strengthening is worth adding to the internal note.  It sharpens the
remaining bridge to a temporal consumer of a fixed-size payoff-externality
edge; it does not supply that consumer.

## Novelty and boundary

The finite-clock response trichotomy elsewhere allows horizons to grow by one
when opponents have mixed finite support.  The present pure-clock theorem is
strictly sharper: pure responses introduce no new deadline, so literal finite
recurrence is unconditional.  I found no checked declaration with this exact
finite inherited-alphabet cycle.

The missing field remains decisive.  A complete-strategy response edge is
not an exact temporal Nash--Bellman predecessor edge, and its mover gain is
not root absorption charge.  Literal target-to-next-source identity fixes the
old source-reconstruction problem only in response-update time.  It does not
serialize the cycle inside one quitting play.
