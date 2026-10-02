# Review of finite pure-clock exact-response cycles

## Verdict

**PASS with bounded revisions.**

The finite inherited-alphabet theorem, exact cap attainment, deterministic
cycle, (D_*/4) gain floor, killed-mover identity, literal ancestry, and
Nash--Bellman consumer mismatch are mathematically correct.  The result is a
genuine strengthening from calendar-type recurrence to literal recurrence of
actual pure-clock profiles.

It does not consume the off-minimum port.  The cycle is horizontal response
dynamics, not an in-game chronology.

## 1. Alphabet closure and cap attainment

The three-value calculation is exact.  Against pure-clock opponents, if the
earliest finite opponent deadline is (m) with quitting coalition (A), any
pure response has one of the values

\[
r_i(\{i\}),\qquad r_i(A\cup\{i\}),\qquad r_i(A),
\]

according as it stops before, at, or after (m).  The before option is
available iff (m>0), represented by time zero; the after option is
represented by Never.  If all opponents use Never, zero and Never represent
the singleton and nonabsorption values.

An arbitrary behavioral response induces a distribution on
(overline{\mathbb N}), and its payoff against these deterministic opponents
is the average of the corresponding pure-time values.  Thus a member of
({0,m,\infty\}) attains the unrestricted cap.  This agrees with
`exists_quittingPureTime_capAttainer`; the more precise inherited-alphabet
statement also follows from its case split.

Since (m) is a coordinate of the current pure profile, it belongs to the
initial inherited alphabet whenever all current coordinates do.  Calendar
zero causes no exception, and no successor date such as (m+1) is needed:
Never already represents every response strictly after the sure earliest
opponent absorption.

## 2. Deterministic selection, gain, and zero mover debt

Both tie-break sets are finite and nonempty, so the successor map is total and
deterministic.  For every actual profile (t), carrier minimality gives
(D(t)\ge D_*).  Hence a maximum-debt player has

\[
d_i(t)\ge D_*/4.
\]

Installing a cap-attaining response changes only (i)'s strategy.  The
opponents, and therefore (B_i), are unchanged, while the new prescribed
payoff equals the old cap.  The claimed identities

\[
U_i(F(t))-U_i(t)=d_i(t)\ge D_*/4,
\qquad d_i(F(t))=0
\]

are exact.

This does **not** imply that the target remains on the minimum fibre.  The
note correctly avoids that claim: other-player cap leakage may raise total
debt.

## 3. Literal cycle and explicit bound

The orbit lies in the literal finite state set (Lambda(t^0)^4), rather than
only a finite calendar quotient.  Thus first repetition gives literal profile
equality and a nontrivial cycle.  Positive selected debt excludes a fixed
point.

The note can be strengthened at no cost by recording the bound

\[
b\le |\Lambda(t^0)|^4\le 6^4=1296
\]

for the first repetition, and the same upper bound for the transient plus
period.  For (m) players the corresponding crude bound is
((m+2)^m).

## 4. Pure-minimum hit branch: one sentence must be deleted

Section 4 chooses the **least** (n>0) such that (D(t^n)=D_*), starting
from (D(t^0)>D_*).  Therefore (D(t^{n-1})=D_*) is impossible.  The
sentence

> If already (D(t^{n-1})=D_*), the last edge is a genuine
> minimum-to-minimum response chord

must be deleted.  Under the stated stopping rule the last edge is always a
horizontal off-minimum-to-minimum exact response.  Continuing the dynamics
after the first minimum hit could later produce a minimum-to-minimum chord,
but that is a different dispatch and is not needed here.

It would also be clearer to call (4.2) a horizontal response return, not a
paid return without qualification, because Section 5 correctly proves it is
not an admissible temporal return.

## 5. Source ancestry

The finite ancestry claim is sound, with one documentation qualification.
Sequentially replacing remaining mixed players by pure clocks chosen from
their stopping laws is an elementary affine-selection argument.  It does not
preserve off-minimality, and the note handles both possible outcomes:

* if the resulting pure profile is off minimum, start there;
* if it is on the minimum fibre, apply
  `pureTimeMinimum_exists_offMinimum`.

Every operation is a literal unilateral replacement, so it composes with the
incoming purification ancestry.  No independent carrier realizer is chosen.
For a declaration-level handoff, the supported pure-clock selection used in
the extra purification should be named explicitly or stated as a small lemma;
the present ordinary proof is nevertheless complete.

The original paid row survives only as historical provenance, not as an
operational row for every later state.  The note says this correctly.  Each
new pure response edge has its own first-disagreement localization.

## 6. Falsification regression

Horizontal recurrence is genuinely possible.  For two players take

\[
\begin{array}{c|ccc}
&\{1\}&\{2\}&\{1,2\}\\ \hline
r_1&-1&0&1\\
r_2&1&1&0.
\end{array}
\]

On the clock alphabet ({0,\infty\}), exact pure best responses form the
literal cycle

\[
(0,0)\to(0,\infty)\to(\infty,\infty)
\to(\infty,0)\to(0,0),
\]

with unit mover gain at every edge and total debt one at every displayed
state.  Yet the game has an exact terminal stationary equilibrium: player 1
always Continues and player 2 Quits at any stationary rate in ((0,1/2]),
with payoff ((0,1)).

This regression does not challenge the positive-(D_*) conditional theorem;
its global minimum debt is zero.  It confirms the note's main nonclaim: a
literal positive-gain best-response cycle alone is not a contradiction and
cannot be silently read as temporal play.

## 7. Exact admissible-consumer mismatch

The source audit is correct.  `QuittingPunishmentFloorAdmissibleEdge` contains
an `IsQuittingNashBellmanEdge` between two boxed punishment-floor states, and
its charge is literal root absorption.  A whole-strategy response replacement
provides none of:

* the Bellman predecessor payoff identity;
* all-player exact root Nash at the displayed continuation cap;
* punishment-floor state certificates; or
* absorption charge equal to the mover's full-profile gain.

Localizing two pure clocks at their first disagreement produces a horizontal
paid row, not these missing fields.  Consequently the positive admissible
cycle and payoff-near-return consumers do not accept the constructed cycle.

The most informative exact ledger around a period is, for mover (i_k), gain
(g_k), and nonmover debt change
(ell_{k,j}=d_j(t^{k+1})-d_j(t^k)),

\[
\sum_{k:i_k\ne j}\ell_{k,j}
=\sum_{k:i_k=j}g_k.
\]

All killed debt is recreated by other-player externalities around the loop.
Positive global minimum debt bounds the gains below but supplies no sign on
those externalities.  Hence this identity yields no renewable rank or
chronological charge.

## Recommendation

Retain the theorem as a precise horizontal normal form.  Make the two bounded
edits above:

1. delete the impossible minimum-to-minimum sentence; and
2. expose the (1296)-state bound.

Do not promote it as consumption of the paid-cap waist.  Its exact successor
question is whether positive-minimum hard-residual provenance can turn one
edge of the literal response cycle into an exact Nash--Bellman edge, rule out
the cycle, or orient the reactivated debts by a finite rank.

