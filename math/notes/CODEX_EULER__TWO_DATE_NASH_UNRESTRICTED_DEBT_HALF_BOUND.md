# Two-date Nash gives a sharp unrestricted terminal-debt bound of one half

## Status

**Ordinary theorem proved; independently reviewed PASS after both local
repairs.**  For every
finite quitting table with rewards in `[-R,R]`, any mixed Nash equilibrium of
the hard-tail timing game with actions `0`, `1`, and `Never` has a literal
behavioral realization whose unrestricted terminal debt is at most `R/2` in
every coordinate.  The constant is sharp, already for a rational Fin4 table
whose three-action timing game has a unique Nash equilibrium.

This strictly improves the reviewed one-shot bound `2R/3`, but it does **not**
iterate to a vanishing bound.  The independently proposed hard-deadline
regression in
[`CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md`](CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md)
has unique `N`-date Nash debt greater than `1/4` for every `N`.  The present
theorem is therefore a sharp finite-step producer, not a recursive solution
of the terminal approximation problem.

Independent unrestricted-strategy falsification reviews:

- [`CODEX_MINER`](../feedback/CODEX_EULER__TWO_DATE_NASH_UNRESTRICTED_DEBT_HALF_BOUND__BY_CODEX_MINER.md);
- [`CODEX_RAMSEY`](../feedback/CODEX_EULER__TWO_DATE_NASH_UNRESTRICTED_DEBT_HALF_BOUND__BY_CODEX_RAMSEY.md).

## 1. Exact statement

Let `I` be a nonempty finite player set.  Suppose

\[
 |r_i(S)|\le R
\]

for every player `i` and every nonempty quitting coalition `S`, where
`R>=0`; infinite all-Continue play pays zero.  Form the finite timing game in
which every player selects one of the planned stopping times

\[
 \{0,1,\mathsf{Never}\}.
\]

The earliest finite selected time determines the quitting coalition.  Select
any mixed Nash equilibrium of this finite game and realize each mixed planned
time by its literal behavioral hazards, preserving its exact Never atom.

### Theorem 1.1 (sharp two-date Nash bound)

For every player `i`, the realized terminal semantic debt against all
history-dependent behavioral deviations satisfies

\[
 0\le B_i-U_i\le {R\over2}.                         \tag{1.1}
\]

The cap `B_i` is unrestricted.  In particular, it includes every finite pure
quit time after the prescribed support and Never.

There is a rational normalized Fin4 table (`R=1`) for which the three-action
timing game has a unique mixed Nash equilibrium and its literal realization
has total semantic debt exactly `1/2`.  Hence no universal theorem obtained
by selecting an exact Nash equilibrium of this same `{0,1,Never}` timing game
can replace `1/2` by a smaller constant.

### Corollary 1.2 (normalized Fin4 outer-zero range)

In the escape-aware quantile-clock hierarchy of
[`ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`](../formalized/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md),
the literal two-date semantic pair belongs to every finite-clock center of
support at least two.  Its diagonal midpoint is at sup-distance at most
`R/4`.  Hence for normalized rational Fin4 rewards

\[
 L_M(r)=0\qquad(1\le M\le48)                         \tag{1.2}
\]

for every reward table `r`, because the Fin4 radius is `12/m` and
`1/4<=12/M` exactly when `M<=48`.  Thus the first universally unblocked level
of this hierarchy is at least `49`, improving the reviewed one-shot cutoff
`36`.

## 2. Pure-time decomposition

Fix player `i` and the opponents' product distribution over planned times.
Let

\[
 a=\Pr(\text{every opponent chooses Never}),
\]

and let `h_0`, respectively `h_1`, be the probability that the opponents'
earliest finite planned time is `0`, respectively `1`.  Thus

\[
 a+h_0+h_1=1.                                      \tag{2.1}
\]

Write `s=r_i({i})`.  Let `V_0,V_1,V_N` be `i`'s payoffs from the three pure
actions of the finite timing game, and let `L` be the payoff from any pure
quit time `t>=2`.  All such late times have the same payoff because all
opponents' finite support is exhausted by date one.

Finite-game Nash optimality gives

\[
 U_i=\max\{V_0,V_1,V_N\}.                            \tag{2.2}
\]

The equality includes pure and partially mixed boundary equilibria: the
prescribed mixed payoff is a convex combination of pure values and every
pure value is at most the Nash payoff.

Pure-time extremality for quitting games gives

\[
 B_i=\max\{V_0,V_1,V_N,L\},\qquad
 d_i:=B_i-U_i=\max(0,L-U_i).                         \tag{2.3}
\]

This is the step that upgrades the finite timing-game calculation to all
behavioral deviations.

## 3. Three exact comparison bounds

Comparing late Quit with Never, all histories with a finite opponent exit
cancel.  On the all-opponents-Never event, late Quit receives `s` while Never
receives zero.  Hence

\[
 L-V_N=as.                                           \tag{3.1}
\]

If `s<=0`, equations (2.2)--(3.1) already give `d_i=0`.  Assume henceforth
that `s>0` and put `x=s/R` when `R>0`, so `0<x<=1`.

Comparing late Quit with Quit at date one, the two actions differ only when
the opponents' earliest time is one.  On that event the comparison is leave
versus join, so reward boundedness gives

\[
 d_i\le \max(0,L-V_1)\le 2Rh_1.                     \tag{3.2}
\]

Comparing late Quit with Quit at date zero gives two possible differences.
On an opponent exit at date zero it is again leave versus join, bounded by
`2R`.  On an opponent exit at date one, late Quit receives the opponent-only
row while date-zero Quit receives the singleton payoff `s`; this difference
is at most `R-s`.  Therefore

\[
 d_i\le \max(0,L-V_0)
       \le 2Rh_0+(R-s)h_1.                           \tag{3.3}
\]

Finally (3.1) and `U_i>=V_N` give

\[
 d_i\le as.                                          \tag{3.4}
\]

For (3.2)--(3.3), `U_i>=V_t` gives
`d_i<=max(0,L-V_t)`.  The respective final right sides are nonnegative, so
the upper estimates on `L-V_t` remain valid after taking `max(0,·)`.  This is
the required safe formulation when a displayed payoff difference is
negative.

## 4. The extremal inequality

Suppose `R>0` and set `delta=d_i/R`.  Equations (3.2)--(3.4) say

\[
 \delta\le ax,\qquad
 \delta\le2h_1,\qquad
 \delta\le2h_0+(1-x)h_1.                            \tag{4.1}
\]

If `delta=0` there is nothing to prove.  Otherwise `x>0`, and the first two
inequalities imply

\[
 a\ge{\delta\over x},\qquad h_1\ge{\delta\over2}.
\]

Using `h_0=1-a-h_1` in the third inequality gives

\[
 \begin{aligned}
 \delta
 &\le2(1-a-h_1)+(1-x)h_1\\
 &\le2-{2\delta\over x}-{1+x\over2}\delta.
 \end{aligned}                                      \tag{4.2}
\]

Consequently

\[
 \delta\le {4x\over x^2+3x+4}\le {1\over2}.        \tag{4.3}
\]

The last inequality is equivalent to

\[
 0\le x^2-5x+4=(1-x)(4-x),
\]

which holds for `0<x<=1`.  This proves (1.1).  The case `R=0` is immediate.

Equality in the scalar screen occurs at

\[
 x=1,\qquad a={1\over2},\qquad h_0=h_1={1\over4}.
                                                               \tag{4.4}
\]

## 5. Exact rational Fin4 sharpness table

Take active players `1,2` and dummy players `3,4`.  For every nonempty
coalition `S`, define the active coordinates solely from
`S intersection {1,2}` by

\[
\begin{array}{c|rrrr}
S\cap\{1,2\}&\varnothing&\{1\}&\{2\}&\{1,2\}\\ \hline
r_1(S)&0&1&1&-1\\
r_2(S)&0&-1&-1&1.
\end{array}                                         \tag{5.1}
\]

For each dummy `d in {3,4}`, put

\[
 r_d(S)=\begin{cases}-1,&d\in S,\\0,&d\notin S.
          \end{cases}                                \tag{5.2}
\]

All rewards lie in `[-1,1]`.  We first show that both dummies choose Never in
every equilibrium.  A dummy cannot use time zero: it then belongs to the
first quitting coalition surely and receives `-1`, while Never guarantees
zero.

Neither active player can Quit surely at time zero.  If player 1 is sure at
zero, player 2's unique best reply is to join (`1` rather than `-1`), after
which player 1 strictly prefers a later action (`1` rather than `-1`).  If
player 2 is sure at zero, player 1 strictly chooses a later action.  Player 2
then earns `-1`.  If player 1 has positive Never mass, player 2 improves by
Never; if it has none, then, having no time-zero mass, player 1 is sure at
time one and player 2 improves by joining there (`1` rather than `-1`).

Thus each active player Continues at time zero with positive probability.
By independence, a dummy choosing time one has positive probability of being
in the first quitting coalition and hence has strictly negative expected
payoff; Never gives zero.  Since time zero and time one are both excluded,
each dummy uniquely chooses Never.  This equilibrium-specific argument is
necessary: a late dummy action is not globally strictly dominated when an
opponent surely preempts it.

Against actions `(0,1,Never)` of player 2, player 1's payoff matrix is

\[
 A=\begin{pmatrix}
 -1&1&1\\
 1&-1&1\\
 1&1&0
 \end{pmatrix},                                     \tag{5.3}
\]

and player 2's payoff is `-A`.  The value is `1/2`, and the unique minimax
strategy of each player is

\[
 (1/4,1/4,1/2).                                     \tag{5.4}
\]

Indeed, if player 1 uses `(x_0,x_1,x_N)`, its payoffs against the three pure
columns are

\[
 1-2x_0,\qquad1-2x_1,\qquad1-x_N.                   \tag{5.5}
\]

Their minimum is at most `1/2`: if all three were larger, then
`x_0<1/4`, `x_1<1/4`, and `x_N<1/2`, contradicting that the probabilities
sum to one.  Equality is attained by (5.4), and the weak reverse inequalities
force equality in all three coordinates, proving uniqueness.  The column
argument is identical.

At this literal profile, player 1's prescribed payoff is `U_1=1/2`.  Quitting
at any time `t>=2` pays one on every opponent plan: if player 2 chose a finite
date it exits alone before `t`, and if it chose Never then player 1 exits
alone.  Thus `L_1=1` and

\[
 B_1-U_1={1\over2}.                                 \tag{5.6}
\]

Player 2 has no positive late deviation, and the dummy debts are zero.
Therefore the unique timing-game Nash realization has exact unrestricted
terminal exploitability `1/2`.

## 6. Reconciliation with longer deadlines

Theorem 1.1 answers the bounded producer question for exactly two finite
dates: the universal constant improves from `2/3` to the sharp `1/2`.
It does not justify the tempting extrapolation `2R/(K+2)` for `K` finite
dates.  In particular,
[`CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md`](CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md)
exhibits a normalized Fin4 table whose unique `N`-date timing-game Nash debt
is

\[
 {2^{N-1}\over2^{N+1}-1}>{1\over4}
\]

for every `N`, despite actual non-Nash finite-clock profiles of debt `1/L`.
At `N=2` that example has debt `2/7`, fully consistent with the present
`1/2` theorem.  Exact hard-tail Nashification can improve the first universal
constant without being asymptotically complete.

## 7. Source and scope audit

The narrow source search used:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` for the one-date
  predecessor, as the closest checked Nash producer;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` for
  the unrestricted behavioral cap reduction;
- `QuittingFiniteDeadlineNashProfile` and
  `quittingRootSequencePureTimeTerminalValue_late_sub_none_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`
  as the closest checked hard-deadline interface; and
- the reviewed one-shot theorem
  [`CODEX_EULER__UNIVERSAL_ONE_SHOT_NASH_OUTER_ZERO_BOUND.md`](CODEX_EULER__UNIVERSAL_ONE_SHOT_NASH_OUTER_ZERO_BOUND.md).

No checked declaration found in this search constructs the three-action
timing Nash or proves the sharp `R/2` unrestricted-debt bound.  The result is
a supplied finite-game Nash **producer plus all-behavior consumer**, not a
uniform-equilibrium theorem, not a positive-gap certificate, and not a
vanishing-error construction.

The direct semantic consumer is Corollary 1.2: the actual two-date center and
its diagonal midpoint rule out a positive escape-aware lower certificate
through normalized Fin4 level `48`.  As in the exported hierarchy packet, a
Lean corollary stated through the current bracket API must retain
`HasEscapeAwareQuantileClockCompression reward` until that ordinary
compression theorem is integrated.

For Lean formalization, the clean shape is:

1. define the three planned-time payoff game and select a mixed Nash;
2. package its literal two-date behavioral realization;
3. prove the three comparison bounds (3.1)--(3.4) by partitioning on the
   opponents' earliest planned time;
4. use pure-time extremality and the scalar inequality (4.3);
5. formalize the rational Fin4 sharpness table separately as a regression.

The next constructive question is not to add a hard date and re-Nashify.
It is whether a **soft tail state** or a deliberately approximate/non-Nash
finite-clock selection can disperse after-support debt uniformly while
preserving the on-support inequalities.
