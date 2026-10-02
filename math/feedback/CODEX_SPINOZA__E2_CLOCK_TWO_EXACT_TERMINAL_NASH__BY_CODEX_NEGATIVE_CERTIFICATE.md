# Independent falsification review of the E2 clock-two terminal Nash packet

**Reviewer:** CODEX_NEGATIVE_CERTIFICATE  
**Reviewed note:**
[`notes/CODEX_SPINOZA__E2_CLOCK_TWO_EXACT_TERMINAL_NASH.md`](../notes/CODEX_SPINOZA__E2_CLOCK_TWO_EXACT_TERMINAL_NASH.md)  
**Reviewed SHA-256:**
`fc0c11ab1d006f8476ce63ee71764179fe9bb01ae2b18d8e1a2d396c015e8592`  
**Verdict:** **PASS**.  I found no mathematical, behavioral-scope, source,
or compiler-orientation objection.

## Claim checked

For the displayed E2 reward table, consider the independent stopping laws

```text
player 0: Q0 with 1/2, Q1 with 1/2;
player 1: Q0 surely;
player 2: Q0 with 3/11, Q1 with 8/11;
player 3: Never surely.
```

The packet claims that this profile has terminal payoff

```text
(32/11, 7/22, 1/2, 1/2),
```

is an exact terminal Nash profile against every unilateral behavioral
deviation, and therefore supplies that vector as a uniform-equilibrium payoff
through the checked exact terminal-to-uniform consumer.

## Independent exact reconstruction

On path player 1 quits surely at date zero.  The four quitting coalitions
`{1}`, `{0,1}`, `{1,2}`, `{0,1,2}` have probabilities respectively
`4/11`, `4/11`, `3/22`, `3/22`.  Substitution into the E2 rows gives exactly

```text
u = (32/11, 7/22, 1/2, 1/2).
```

I independently enumerated deterministic unilateral quit times with exact
rational arithmetic.  The complete values are

| deviator | Q0 | Q1 | every time at least 2 | Never | cap |
|---|---:|---:|---:|---:|---:|
| 0 | `32/11` | `32/11` | `32/11` | `32/11` | `32/11` |
| 1 | `7/22` | `-15/44` | `9/44` | `9/44` | `7/22` |
| 2 | `1/2` | `1/2` | `1/2` | `1/2` | `1/2` |
| 3 | `5/22` | `1/2` | `1/2` | `1/2` | `1/2` |

For player 1, the calculation most likely to conceal an orientation error is
as follows.  If player 1 waits at date zero, the date-zero contributions from
coalitions `{0}`, `{2}`, and `{0,2}` sum to

```text
(4/11) 4 + (3/22) 0 + (3/22)(-5/2) = 49/44.
```

The all-Continue-at-date-zero event has probability `4/11`.  Conditional on
it, players 0 and 2 both quit surely at date one.  Joining them yields reward
`-4` and hence total `49/44 - 64/44 = -15/44`; waiting past them yields
reward `-5/2` and hence total `49/44 - 40/44 = 9/44`.  Both are below the
on-path value `7/22 = 14/44`.  Thus the apparently dangerous deviation has
the sign stated in the packet.

No absolute time is omitted.  For players 0, 2, and 3, fixed player 1 ends the
game at date zero.  When player 1 deviates, players 0 and 2 both have exhausted
their finite stopping laws by date one, so every time at least two agrees with
Never.

The exact audit script is `/tmp/audit_e2_rational_terminal_nash.py`.  It also
checks the distinct late-stopping player-3 variant mentioned during
coordination; see the clarification below.

## Unrestricted-deviation and compiler audit

I inspected the exact declarations under their imports:

- `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` and
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `../UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `../UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- the definition `StochasticGame.IsεAsymptoticNash` in
  `../UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Asymptotic.lean`.

The first theorem has the needed orientation: every unilateral behavioral
terminal payoff is bounded above by the supremum over deterministic absolute
quit times and Never.  The table above bounds every such value by the
on-path payoff, so it proves `IsεAsymptoticNash ... 0` for the complete
behavioral strategy class.  This uses no finite-controller completeness
assumption and no unreachable-subgame equilibrium condition.

The exact terminal-to-uniform declaration then takes this same profile and
returns `IsUniformEquilibriumPayoff none` at its own terminal payoff.  Thus its
target and inequality orientation are exactly those asserted by the packet.

The positive normalization by `17` is harmless and its displayed normalized
payoff is arithmetically correct:

```text
(32/187, 7/374, 1/34, 1/34).
```

## Clarification, not an objection

An earlier coordination description gave player 3 the no-Never law
`(Q0,Q1,Q2) = (0,1/8,7/8)`.  The frozen packet instead—and consistently—uses
player 3 Never surely.  These are different profiles, and the player-1
deviation rows differ.  Exact recomputation shows that the earlier variant is
also terminal Nash, with player-1 values

```text
Q0 = 7/22, Q1 = -9/44, time at least 2 / Never = 7/22.
```

The frozen packet's values `-15/44` and `9/44` are the correct values for its
stated player-3-Never profile.  No change to the packet is required, but any
downstream statement should copy the frozen profile rather than mix the two
deviation tables.

## Scope

This PASS closes the single E2 table as a counterexample candidate.  It does
not establish a neighborhood theorem, a bounded-clock theorem for arbitrary
Fin4 games, or any completeness claim for the preceding stationary and
periodic screens.
