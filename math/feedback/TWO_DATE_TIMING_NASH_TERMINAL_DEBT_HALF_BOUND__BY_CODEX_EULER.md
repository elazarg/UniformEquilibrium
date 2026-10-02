# Whole-packet gate: `TWO_DATE_TIMING_NASH_TERMINAL_DEBT_HALF_BOUND`

Packet:
[`exports/TWO_DATE_TIMING_NASH_TERMINAL_DEBT_HALF_BOUND.md`](../exports/TWO_DATE_TIMING_NASH_TERMINAL_DEBT_HALF_BOUND.md)

Gate reviewer: `CODEX_EULER`  
Independent theorem reviewers: `CODEX_MINER`, `CODEX_RAMSEY`

## Verdict

**PASS after two bounded source/probability prose repairs applied directly.**
No mathematical repair was needed.  I added the exact two-date hazard formula
including its zero-tail convention, replaced a generic hierarchy-source
reference by exact declaration names, and named the checked general
finite-game Nash producer.  The current packet satisfies every item in
`exports/README.md`.

## 1. Universal theorem and unrestricted strategy class

For a player facing opponents supported on `{0,1,Never}`, the opponent events
“all Never,” “earliest zero,” and “earliest one” have probabilities
`a,h_0,h_1` and partition the product law.  A pure unilateral stopping time
has exactly one of four values: `V_0,V_1,V_N`, or the common after-support
value `L`.  Finite-game Nash gives

\[
 U_i=\max(V_0,V_1,V_N),
\]

and the checked pure-time extremality theorem gives the full randomized,
history-dependent behavioral cap

\[
 B_i=\max(V_0,V_1,V_N,L).
\]

The repaired positive-part comparisons are exact:

\[
 d_i\le as,qquad d_i\le2Rh_1,qquad
 d_i\le2Rh_0+(R-s)h_1
\]

when `s>0`; for `s<=0`, the debt is zero.  Normalizing by `R`, the scalar
calculation yields

\[
 d_i/R\le {4x\over x^2+3x+4}\le1/2.
\]

All divisions occur only after `R>0`, `s>0`.  Pure and partially mixed Nash
coordinates, zero event masses, exact Never, and the one-player boundary are
covered.  The newly inserted hazard formula realizes every law
`(x_0,x_1,x_N)` exactly and explicitly treats the unreachable denominator-zero
history.

## 2. Sharpness and dummy proof

The rational Fin4 table is complete and normalized.  Its two active players
induce the zero-sum matrix

\[
 \begin{pmatrix}-1&1&1\\1&-1&1\\1&1&0\end{pmatrix},
\]

whose unique minimax law is `(1/4,1/4,1/2)` for both players and whose value
is `1/2`.  The dummy elimination is now correctly equilibrium-specific:

1. a dummy cannot put mass at zero because Never guarantees zero while the
   dummy's own exit pays `-1`;
2. neither active player can be sure at zero, by the displayed join/wait
   best-response cycle; and
3. therefore a dummy at time one has positive probability of being in the
   first coalition and strictly loses relative to Never.

Thus both dummies are uniquely Never in equilibrium, after which the active
matrix proves full-game uniqueness.  Player 1's after-support value is one
and prescribed value is `1/2`, so the unrestricted debt is exactly `1/2`.
This genuinely proves sharpness for exact `{0,1,Never}` Nash selection, not
only for a supplied equilibrium.

## 3. Hierarchy adapter and constants

The literal profile has finite support `{0,1}` and therefore belongs to every
`A_(K_m)` by the checked support monotonicity.  Its diagonal midpoint has
zero objective and sup-distance at most half its maximum debt, namely `1/4`
for normalized rewards.  For Fin4,

\[
 \delta_m=12/m,qquad 12/48=1/4,qquad12/49<1/4.
\]

Hence the same center lies in every outer neighborhood through `M=48`, and
`L_M=0` there.  The packet correctly says only that level 49 is the first
universally unblocked level; it does not infer a positive value at level 49.
The Lean handoff correctly retains
`HasEscapeAwareQuantileClockCompression reward` if the current checked
bracket API still requires it.

## 4. Source and novelty audit

The following cited declarations and paths were checked literally:

- `KernelGame.mixed_nash_exists` in
  `UniformEquilibrium/ProofView/Concepts/Existence/NashExistenceMixed.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `QuittingFiniteDeadlineNashProfile` and
  `quittingRootSequencePureTimeTerminalValue_late_sub_none_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`;
  and
- `quittingFiniteClockSemanticReachable_eq_range_fold`,
  `quittingFiniteClockSemanticReachable_isCompact`,
  `quittingFiniteClockSemanticReachable_mono`, `quantileClockSupport`, and
  `quantileClockRadius` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`.

These sources provide Nash existence, cap reduction, deadline interfaces, and
actual hierarchy centers, but no existing declaration supplies the sharp
`R/2` combination.  The packet explicitly records that no external paper is
used.  The two independent reviews include adversarial unrestricted-strategy
checks and have no remaining objection.

## 5. Hard-deadline boundary and export significance

The packet accurately preserves the longer-deadline limitation.  Miner's
separate rational Fin4 table has unique exact `N`-date timing Nash debt
strictly above `1/4` for every `N`, while explicit non-Nash finite-clock
profiles on that table have debt tending to zero.  This does not contradict
the present two-date `R/2` bound; it forbids extrapolating it into a vanishing
hard-tail Nash sequence.

The packet makes a named conjecture-facing change: it is an arbitrary-table,
literal actual-profile producer with a complete behavioral consumer, improves
`2R/3` to the sharp `R/2`, and advances the universal normalized Fin4
outer-zero cutoff from 36 to 48.  It explicitly does not claim terminal
approximation, uniform payoff, a positive gap, or induction over deadlines.
The Lean handoff is narrow and does not assume the new estimate as a structure
field.  Final export verdict: **PASS**.
