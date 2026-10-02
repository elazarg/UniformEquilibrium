# Review of positive-singleton curvature inverse-Bellman separation

Reviewer: `CODEX_EULER`

Verdict: **PASS; no mathematical repair.  Internal only.**

I independently checked the complete rational table, the three literal
stopping-law profiles, unrestricted behavioral caps, punishment-floor
upper bounds, root uniqueness, and the inverse-edge support elimination in
[`CODEX_RAMSEY__POSITIVE_SINGLETON_CURVATURE_INVERSE_BELLMAN_SEPARATION.md`](../notes/CODEX_RAMSEY__POSITIVE_SINGLETON_CURVATURE_INVERSE_BELLMAN_SEPARATION.md).
The stated local converter is genuinely false.  The example has debt minimum
zero and an exact terminal Nash profile, so it has exactly the narrow scope
claimed by the author.

## 1. Literal laws and prescribed payoffs

Player 1 has mass `1/2` at each of dates zero and one.  With player 2 surely
quitting at date zero, the two equiprobable outcomes are `{1,2}` and `{2}`;
hence

\[
 U_S=(3/4,-1/2,0,0).
\]

With player 2 surely quitting at date one, the outcomes are `{1}` and
`{1,2}`, giving

\[
 U_T=(5/8,1/2,0,0).
\]

At the midpoint the four clock pairs are equiprobable.  The terminal law is

\[
 \mu_M(\{1\})=\mu_M(\{2\})=1/4,
 \qquad \mu_M(\{1,2\})=1/2,
\]

and direct reward averaging gives `U_M=(11/16,0,0,0)`.  Thus (2.5) and
(3.1) are exact.

## 2. Unrestricted caps and curvature

Against the midpoint law of player 2, player 1's pure-time values are

\[
 5/8,\quad 3/4,\quad 1/2
\]

at date zero, date one, and every later finite date or Never, respectively.
Against player 1's fixed two-date law, player 2's corresponding values are

\[
 -1/2,\quad 1/2,\quad 1.
\]

Against either endpoint law, player 1 can tie the sure quit and obtain one.
Players 3 and 4 obtain zero by Never, while any event on which they themselves
quit pays `-1`; their caps are therefore zero.  Pure-time extremality gives
exactly

\[
 B_S=B_T=(1,1,0,0),\qquad B_M=(3/4,1,0,0).
\]

The curvature is consequently `1/4`, and subtracting the prescribed vectors
gives all three debt vectors in (3.6).

This calculation covers arbitrary behavioral unilateral deviations: the
cap-to-pure-time equality is the relevant unrestricted stopping-law theorem,
not a stationary-only comparison.

## 3. Exact root uniqueness

At every one of the six listed annotations, players 3 and 4 have strictly
dominated Quit actions: Continue always pays zero, whereas Quit always pays
`-1`.  Once they Continue, player 2's action-payoff difference is

\[
 C_2-Q_2=1+(1-x_1)Z_2\ge 1/2>0,
\]

because every listed `Z_2` is at least `-1/2`.  Once player 2 Continues,
player 1 compares `Z_1>=5/8` with singleton-Quit payoff `1/4`.  Backward
elimination therefore makes all Continue the unique product root at every
annotation.  The two repeated cap vectors do not affect the claim.

## 4. Punishment-floor audit

A passive opponent quitting surely at date zero gives player 1 cap at most
`1/4` and player 2 cap zero.  One passive player similarly punishes the other
to cap zero.  Therefore

\[
 P_1\le1/4<H_1=3/4,
 \qquad P_2,P_3,P_4\le0\le H_2,H_3,H_4.
\]

Only these valid upper bounds are asserted; the note correctly makes no
punishment-normality claim.

## 5. Inverse-edge elimination

Suppose `H=Succ(T,q)` and `q` is an exact endpoint root against `T`, and write
`x_i` for its Quit probabilities.  If `x_i>0`, then exact support
complementarity gives

\[
 H_i=Q_i(q_{-i}).
\]

This includes `x_i=1`, where the successor coordinate is directly the Quit
payoff.

For either passive player, `Q_i=-1` while `H_i=0`; hence `x_3=x_4=0`.  Then

\[
 Q_2=x_1-1\le0<H_2=1,
\]

so `x_2=0`.  With players 2, 3, and 4 inactive,
`Q_1=r_1({1})=1/4 != H_1=3/4`, forcing `x_1=0`.  Thus the current root is all
Continue and the successor identity reduces to `T=H`.  No floor hypothesis
was used, so in particular no positive-charge punishment-floor predecessor
exists.

At the precise Lean state-space level, `IsQuittingNashBellmanEdge` retains an
irrelevant simplex coordinate on the tail state.  Accordingly, “self-loop”
should be read as a **payoff self-loop** with current root all Continue; the
proof does not and need not identify the tail state's unused stored root.
The note's explicit formulation in terms of a payoff vector `T` and root `q`
already has this correct meaning.

## 6. Boundary and value

The pure profile in which player 1 quits immediately and every other player
plays Never is an exact unrestricted terminal Nash profile: player 1 gets
`1/4`, player 2 gets `1`, and the passive players get zero.  Hence `D_*=0`.
The example is not a Fin4 counterexample and supplies no information against
a theorem that genuinely uses positive global minimum or the hard-residual
source provenance.

The new content relative to the previously reviewed curvature-inert example
is nevertheless real: it both makes an own singleton reward positive and
closes the earlier backward-head loophole at `H=B_M`.  It is a useful internal
separation result, but not export-worthy under the conference significance
gate because its conclusion remains a local `D_*=0` converter no-go rather
than a contraction of the maintained positive-minimum problem.

