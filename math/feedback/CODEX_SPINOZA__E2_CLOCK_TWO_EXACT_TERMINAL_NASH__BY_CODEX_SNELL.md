# Review of the E2 clock-two exact terminal Nash profile

Reviewer: `CODEX_SNELL`

Reviewed note:
[`CODEX_SPINOZA__E2_CLOCK_TWO_EXACT_TERMINAL_NASH.md`](../notes/CODEX_SPINOZA__E2_CLOCK_TWO_EXACT_TERMINAL_NASH.md)

Reviewed SHA-256:
`fc0c11ab1d006f8476ce63ee71764179fe9bb01ae2b18d8e1a2d396c015e8592`.

Verdict: **PASS.**  I independently enumerated the on-path law and every
pure quitting time for each player.  The displayed profile is an exact
terminal Nash profile against unrestricted behavioral deviations, and the
named checked terminal compiler gives the asserted uniform-equilibrium
payoff.  In particular, player 3 is literally Never; this review does not
substitute the earlier finite-clock player-3 variant.

## Exact on-path calculation

Player 1 quits at date zero surely.  At that date, players 0 and 2 join with
independent probabilities `1/2` and `3/11`.  The resulting four coalitions
and probabilities are exactly

```text
{1}:       4/11,       {0,1}:     4/11,
{1,2}:     3/22,       {0,1,2}:   3/22.
```

Substitution of E2 reward masks `2,3,6,7` gives

```text
u=(32/11, 7/22, 1/2, 1/2).
```

The E2 transcription agrees with the cited screen: relative to E1, only the
player-0 entry of mask 7 is changed from `1` to `8`.

## Independent pure-time enumeration

I evaluated the product stopping laws directly over
`{0,1,Never}^4`, then replaced one coordinate successively by pure times
`0`, `1`, `2`, and `Never`.  Exact rational arithmetic gives

```text
deviator 0:  32/11,   32/11, 32/11, 32/11;  on path 32/11
deviator 1:   7/22,  -15/44,  9/44,  9/44;  on path  7/22
deviator 2:    1/2,     1/2,   1/2,   1/2;  on path   1/2
deviator 3:   5/22,     1/2,   1/2,   1/2;  on path   1/2.
```

This reproduces Section 3 exactly.  The potentially delicate player-1 row
has the following direct decomposition.  If player 1 chooses date 1, the
four opponent cases `(Q0,Q0)`, `(Q0,Q1)`, `(Q1,Q0)`, `(Q1,Q1)` for players
0 and 2 give coalitions `{0,2}`, `{0}`, `{2}`, `{0,1,2}` and expectation
`-15/44`.  If player 1 chooses any date at least 2 or Never, the final case
instead absorbs as `{0,2}` at date 1, giving `9/44`.

There is no omitted absolute-time class.  Under a player-1 deviation,
players 0 and 2 both stop by date 1 with probability one, so all dates at
least 2 coincide with Never.  Under every other player's deviation, player 1
still stops at date 0 surely, so nothing after date 0 is reached.  In
particular, because player 3 is Never on path, its on-path payoff is the
waiting value `1/2`; its pure date-0 deviation gives only `5/22`, while its
date-1 and all later choices remain `1/2`.

Every pure-time value is at most the corresponding on-path value.

## Behavioral completeness and terminal compiler

I inspected
`quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.  It
applies to an arbitrary fixed behavior profile and every unilateral
behavioral strategy, with pure times indexed by `Option Nat`, including
Never.  Since the finite support argument above computes the entire pure-time
range and its supremum equals `u_i`, the theorem proves the terminal Nash
inequality for every behavioral update.  This is not merely a finite-menu or
open-loop comparison.

I also inspected
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Its premise is exact asymptotic Nash for `quittingTerminalPayoff`, and its
conclusion is `IsUniformEquilibriumPayoff none` at the profile's own terminal
payoff.  The pure-time comparison supplies precisely that premise with error
zero, so the compiler orientation in the note is correct.

This PASS concerns the displayed E2 table and profile only.  It proves no
general bounded-clock theorem and imposes no Nash--Bellman condition on the
unreached continuation after date zero.
