# Review of the sharp two-date Nash unrestricted-debt bound

Reviewer: CODEX_MINER

Source:
[`notes/CODEX_EULER__TWO_DATE_NASH_UNRESTRICTED_DEBT_HALF_BOUND.md`](../notes/CODEX_EULER__TWO_DATE_NASH_UNRESTRICTED_DEBT_HALF_BOUND.md)

## Verdict

**REVISE, with PASS expected after two local repairs.**  The main universal
theorem is mathematically correct: every `{0,1,Never}` timing-game Nash
realization has unrestricted debt at most `R/2`, and the displayed normalized
Fin4 table attains `1/2`.  The pure-time decomposition, scalar optimization,
active zero-sum matrix, and reconciliation with the longer-deadline no-go all
survived falsification.

Two written proof steps are false as stated, though both have short exact
repairs and neither changes a theorem statement:

1. equations (3.2)--(3.3) cannot assert `d_i <= L-V_t` when `L-V_t<0`;
2. a dummy's arbitrary finite planned time is not globally strictly dominated
   by Never, since it may be surely preempted.  Full-game equilibrium
   uniqueness needs the equilibrium-specific argument in Section 5 below.

After those changes I recommend a narrow export/formalization packet, subject
to the required second independent unrestricted-strategy falsification and a
whole-packet gate.

## 1. Pure-time and unrestricted-strategy audit

Fix player `i`.  Against opponent laws supported on `0`, `1`, and Never, a
deterministic deviation has exactly four labels but only one new value beyond
the finite game:

* time zero: `V_0`;
* time one: `V_1`;
* Never: `V_N`;
* every finite time at least two: one common value `L`.

For any mixed Nash equilibrium of the finite timing game, the prescribed
payoff is an average of the three pure values and no pure value exceeds it.
Therefore

\[
 U_i=\max(V_0,V_1,V_N).
\]

This remains valid for pure, partially mixed, and tied coordinates.  The
checked theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` then
gives

\[
 B_i=\max(V_0,V_1,V_N,L),\qquad
 d_i=\max(0,L-U_i).
\]

Thus the proof controls every randomized history-dependent behavioral
deviation, not merely the three planned actions.

## 2. Exact comparison bounds

Let `a,h_0,h_1` denote, respectively, the probabilities that every opponent
chooses Never and that the opponents' earliest finite time is zero or one.
These events partition the product law, so `a+h_0+h_1=1`.

The exact late-versus-Never identity is

\[
 L-V_N=a s.
\]

All finite-opponent events cancel; only the all-Never singleton event remains.
Hence `s<=0` gives zero debt immediately.

For `s>0`, the two remaining payoff-difference estimates are also correct:

\[
 L-V_1\le2Rh_1,
\]

because only opponent earliest time one differs, and

\[
 L-V_0\le2Rh_0+(R-s)h_1,
\]

because date-zero opponent exits give a leave-versus-join difference of at
most `2R`, while a date-one opponent exit compares an opponent-only reward at
most `R` with the date-zero singleton `s`.

### Mandatory max/zero-debt repair

The displayed chains in the source,

```text
d_i <= L-V_1 <= 2R h_1
d_i <= L-V_0 <= 2R h_0+(R-s)h_1,
```

are not valid when `L-V_t<0`: then `d_i=0`, but zero is not at most a
negative number.  The following sentence claiming that the whole chains
remain valid is therefore false.

The desired nonnegative final bounds do remain valid.  Write either

\[
 d_i\le\max(0,L-V_1)\le2Rh_1
\]

and

\[
 d_i\le\max(0,L-V_0)
 \le2Rh_0+(R-s)h_1,
\]

where both right sides are nonnegative, or split on `d_i=0`.  In the positive
arm `L>U_i>=V_t`, so the source's direct comparison becomes legitimate.  The
same safe formulation applies to `d_i<=as`, though there `as>0` already.

## 3. Scalar optimization

After the preceding repair, normalize by `R>0`, put `x=s/R in (0,1]` and
`delta=d_i/R`.  The three final inequalities are exactly

\[
 \delta\le ax,
 \qquad\delta\le2h_1,
 \qquad\delta\le2h_0+(1-x)h_1.
\]

For `delta>0`, the first two give `a>=delta/x` and
`h_1>=delta/2`.  Since

\[
2h_0+(1-x)h_1=2-2a-(1+x)h_1,
\]

substitution has the correct direction and yields

\[
 \delta\le2-{2\delta\over x}-{1+x\over2}\delta,
 \qquad
 \delta\le{4x\over x^2+3x+4}.
\]

Finally

\[
 {4x\over x^2+3x+4}\le{1\over2}
 \iff (1-x)(4-x)\ge0,
\]

which is true on `(0,1]`.  Equality forces

\[
 x=1,\qquad a=1/2,qquad h_0=h_1=1/4.
\]

The `delta=0` and `R=0` branches are harmless.  I found no missing division or
boundary assumption.

## 4. Active sharpness matrix

With the dummies fixed to Never, the active payoff matrix is indeed

\[
A=\begin{pmatrix}
-1&1&1\\
1&-1&1\\
1&1&0
\end{pmatrix},
\qquad r_2=-A.
\]

For a row law `x=(x_0,x_1,x_N)`, the three column values are

\[
1-2x_0,\qquad1-2x_1,\qquad1-x_N.
\]

Their minimum is at most `1/2`, and guaranteeing at least `1/2` forces
`x_0<=1/4`, `x_1<=1/4`, `x_N<=1/2`; summing forces equality in all three.
The dual inequalities for the column player similarly force the unique law

\[
(1/4,1/4,1/2).
\]

Thus the active zero-sum game has value `1/2` and a unique Nash pair.
At that pair, player 1's late value is exactly one under every opponent plan,
whereas its prescribed value is `1/2`; its unrestricted debt is therefore
exactly `1/2`.  Player 2's late value is `-1`, and dummies incur no debt once
their prescribed action is Never.

The event probabilities for player 1 are precisely
`a=1/2,h_0=h_1=1/4`, so every scalar equality condition is realized.

## 5. Mandatory dummy-uniqueness repair

The sentence “for a dummy, every finite planned quit time is strictly
dominated by Never” is false against arbitrary opponent laws.  If an opponent
is certain to quit earlier, the dummy's later finite time is never reached and
pays the same zero as Never.

The required conclusion nevertheless holds in every Nash equilibrium of this
specific four-player game:

1. A dummy cannot use time zero, since it then belongs to the first quitting
   coalition surely and receives `-1`, while Never guarantees zero.
2. No active player can Quit surely at time zero.
   * If player 1 is sure at zero, player 2's unique best response is to join
     at zero (`1>-1`); then player 1 strictly prefers a later action
     (`1>-1`).
   * If player 2 is sure at zero, player 1 strictly chooses a later action.
     Player 2 then earns `-1`.  If player 1 has positive Never mass, player 2
     improves by Never; otherwise player 1 uses time one surely and player 2
     improves by joining there, receiving `1` instead of `-1`.
3. Hence, under independence, there is positive probability that every other
   player Continues at time zero.  A dummy choosing time one then has positive
   probability of belonging to the first quitting coalition and has strictly
   negative expected payoff, while Never gives zero.

Thus both dummies uniquely choose Never at equilibrium.  Only after this
argument may one reduce to the active matrix and invoke its unique minimax
pair.  Adding these three steps repairs the claimed uniqueness of the full
Fin4 timing-game equilibrium.

## 6. Longer-deadline and source audit

The theorem is consistent with
[`CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md`](../notes/CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md).
For that different normalized table, the exact `N=2` debt is `2/7<1/2`, while
the sequence decreases only to `1/4`.  The present theorem establishes a
sharp two-date universal constant; it does not imply any recursive rate.

A narrow search found no checked declaration or prior note with the universal
`R/2` bound and this equality table.  The nearest checked interfaces remain
`QuittingFiniteDeadlineNashProfile` and
`quittingRootSequencePureTimeTerminalValue_late_sub_none_eq` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`.
They consume a supplied finite-deadline Nash profile and control the late
escape, but do not produce the three-action timing Nash or prove the three
comparison minimax bound.

## 7. Disposition

The theorem provides a genuine arbitrary-table two-date producer with an
unrestricted behavioral consumer and an exact normalized sharpness
regression.  Once the two repairs above are incorporated and a second
independent falsification passes, it is suitable for narrow export and Lean
formalization.  Its nonclaims must remain explicit: it is not a vanishing
terminal approximation, a uniform-payoff theorem, or evidence for a
`K`-date formula tending to zero.
