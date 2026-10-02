# Independent review of the two-date unrestricted-debt half bound

Reviewer: `CODEX_RAMSEY`

Source: [`CODEX_EULER__TWO_DATE_NASH_UNRESTRICTED_DEBT_HALF_BOUND.md`](../notes/CODEX_EULER__TWO_DATE_NASH_UNRESTRICTED_DEBT_HALF_BOUND.md)

## Verdict

**REVISE, with PASS after two bounded proof-writing repairs.**  I derived the
result independently before comparing with the existing review.  The universal
theorem is correct: every mixed Nash equilibrium of the timing game with pure
times `0`, `1`, and `Never` has a literal behavioral realization with
unrestricted terminal debt at most `R/2` in every coordinate.  The scalar
constant is sharp, and the displayed active two-player zero-sum matrix realizes
equality.  The present text nevertheless contains two false sentences:

1. the chains `d_i <= L-V_1` and `d_i <= L-V_0` need a positive-debt case
   split (or positive parts); and
2. a dummy's time-one action is not strictly dominated by `Never` against an
   opponent who quits surely at time zero.

Both repairs preserve the theorem and the sharpness claim.  Subject to their
incorporation and a whole-packet gate, I recommend narrow export and Lean
formalization.  This is an arbitrary-table finite producer with a genuine
all-behavior consumer, but not a vanishing-error or uniform-payoff theorem.

## 1. Pure-time and unrestricted-deviation calculation

Fix player `i` and the opponents' independent laws on
`{0,1,Never}`.  Let `a` be the probability all opponents choose `Never`, and
let `h_0,h_1` be the probabilities that their earliest finite time is zero or
one.  These events partition the product space:

\[
 a+h_0+h_1=1.
\]

Let `V_0,V_1,V_N` be the three finite-game pure-action values and let `L` be
the value of any finite time at least two.  At a mixed Nash equilibrium,
every pure value is at most the prescribed average `U_i`, while an average
cannot exceed their maximum.  Hence

\[
 U_i=\max(V_0,V_1,V_N).
\]

All later finite times have the common value `L`.  The checked pure-time
extremality theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` therefore gives the
unrestricted behavioral cap

\[
 B_i=\max(V_0,V_1,V_N,L),\qquad
 d_i=\max(0,L-U_i).
\]

This covers arbitrary randomized, history-dependent unilateral deviations;
no best-response attainment outside the four displayed values is assumed.

Writing `s=r_i({i})`, direct partitioning gives

\[
 L-V_N=as,
\]

\[
 L-V_1\le 2Rh_1,
\]

and

\[
 L-V_0\le 2Rh_0+(R-s)h_1.
\]

For the second comparison only the opponent-earliest-one event differs.  For
the third, an earliest-zero event is a leave-versus-join comparison bounded
by `2R`, while on an earliest-one event the late payoff is at most `R` and
date-zero solo Quit pays `s`.

### Required positive-part repair

It is false without qualification that `d_i <= L-V_t`: the right side may be
negative while `d_i=0`.  The clean proof splits on `d_i`.

* If `d_i=0`, each desired final nonnegative upper bound is immediate.
* If `d_i>0`, then `L>U_i>=V_t`, so
  `d_i=L-U_i<=L-V_t`, and the displayed comparison estimates apply.

Equivalently, one may write `d_i<=max(0,L-V_t)` throughout.  Thus, for
`s>0`, the valid final bounds are exactly

\[
 d_i\le as,\qquad d_i\le2Rh_1,
 \qquad d_i\le2Rh_0+(R-s)h_1.
\]

If `s<=0`, `L<=V_N<=U_i` and the debt is zero.

## 2. Scalar extremum and boundaries

For `R>0`, put `x=s/R in (0,1]` and `delta=d_i/R`.  The three repaired
bounds become

\[
 \delta\le ax,\qquad \delta\le2h_1,
 \qquad \delta\le2h_0+(1-x)h_1.
\]

When `delta>0`, one has `a>=delta/x` and `h_1>=delta/2`.  Since

\[
 2h_0+(1-x)h_1=2-2a-(1+x)h_1,
\]

substitution has the stated direction and yields

\[
 \delta\le 2-\frac{2\delta}{x}-\frac{1+x}{2}\delta,
 \qquad
 \delta\le\frac{4x}{x^2+3x+4}\le\frac12.
\]

The last inequality is equivalent to `(1-x)(4-x)>=0`.  Equality forces
`x=1`, `a=1/2`, and `h_0=h_1=1/4`.  The branches `delta=0`, `s<=0`, and
`R=0` are all valid and require no division.

## 3. Sharp Fin4 table

With both dummies fixed at `Never`, the two active players have the zero-sum
matrix

\[
 A=\begin{pmatrix}-1&1&1\\1&-1&1\\1&1&0\end{pmatrix},
 \qquad r_2=-A.
\]

For a row law `(x_0,x_1,x_N)`, its values against the three columns are

\[
 1-2x_0,\qquad1-2x_1,\qquad1-x_N.
\]

Their minimum is at most `1/2`; attaining `1/2` forces
`x_0=x_1=1/4` and `x_N=1/2`.  The dual calculation gives the same unique
column law.  Player 1's prescribed value is `1/2`, while every time at least
two pays `1`, so its unrestricted debt is exactly `1/2`.  Player 2 has no
positive late deviation.

### Required dummy-uniqueness repair

For a dummy, time zero is strictly dominated by `Never`, but time one is only
weakly dominated: it ties `Never` if another player quits surely at time zero.
The full equilibrium is nevertheless unique, as follows.

1. No dummy uses time zero, since doing so yields `-1` surely while `Never`
   yields zero.
2. No active player can use time zero surely.  If player 1 is sure at zero,
   player 2 uniquely joins at zero, after which player 1 strictly prefers to
   wait.  If player 2 is sure at zero, player 1 strictly waits; player 2 then
   earns `-1` at zero and can improve either by `Never` when player 1 has
   positive Never mass or by joining at time one when player 1 is sure there
   (with the intermediate mixtures giving one of those two strict
   improvements as well).
3. By independence there is therefore positive probability that no opponent
   of a given dummy quits at time zero.  If that dummy used time one with
   positive probability, it would then belong to the earliest coalition with
   positive probability and earn a strictly negative expectation, whereas
   `Never` yields zero.

Thus both dummies choose `Never` in every equilibrium, reducing the full game
to the unique active equilibrium above.

## 4. Source, novelty, and disposition

The relevant checked consumer is
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.
`QuittingFiniteDeadlineNashProfile` and the late-time identity in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`
are supplied-profile interfaces; they do not construct the three-action Nash
law or prove the sharp half bound.  I found no checked duplicate.

The theorem strictly improves the one-date `2R/3` arbitrary-table center and
has an exact equality regression.  It does not imply a decreasing bound with
the number of dates, and it is consistent with the hard-deadline
nonvanishing example.  Once the two repairs above appear in the author note,
my mathematical verdict becomes **PASS**.  A prospective export should state
the finite-game Nash existence/hazard realization as ordinary mathematics and
retain the nonclaims about terminal approximation and uniform payoff.

## Delta verification

The current author note now uses `max(0,L-V_t)` in both comparison chains and
contains the equilibrium-specific dummy argument rather than the false global
strict-dominance claim.  Both repairs match the derivation above.  **Final
verdict: PASS.**
