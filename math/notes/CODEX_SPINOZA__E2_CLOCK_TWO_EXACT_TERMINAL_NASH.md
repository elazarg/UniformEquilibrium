# E2 has a clock-two exact terminal Nash equilibrium

**Author:** CODEX_SPINOZA  
**Status (2026-09-03):** proof complete in ordinary mathematics and
independently recomputed with exact rational arithmetic; substantive content
frozen pending independent falsification review.  This note is not
Lean-checked and is not yet an export.

## 1. Result

The four-player rational quitting table E2 has a two-date exact terminal Nash
profile against unrestricted behavioral deviations.  Its terminal payoff is

```text
(32/11, 7/22, 1/2, 1/2).
```

Consequently the checked compiler
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` makes this
vector a uniform-equilibrium payoff of E2.

Players are numbered `0,1,2,3`.  In coalition-mask order the nonempty terminal
reward rows of E2 are

```text
 1  ( 1,    4,  0,  0)       9  ( 1,  0,  1,  1)
 2  ( 4,    1,  0,  0)      10  ( 2,  1, 16,  1)
 3  ( 1,    1,  1,  1)      11  ( 0,  7,  0,  0)
 4  ( 0,    0,  1,  4)      12  ( 1,  1,  1,  1)
 5  ( 1, -5/2,  1,  2)      13  ( 0,  0,  0,  4)
 6  ( 0,    1,  1,  1)      14  ( 0,  0, 17,  0)
 7  ( 8,   -4,  0,  0)      15  (-1, -1, -1, -1)
 8  ( 0,    0,  4,  1).
```

This is the screened table called E2 in
`CODEX_SPINOZA__E2_SINGLE_GATE_PERIODIC_SCREEN.md`; equivalently it is E1
with only `r_0({0,1,2})` changed from `1` to `8`.

## 2. The profile

Let `Q0`, `Q1`, and `N` denote quitting at dates 0 and 1 and Never.  Use the
independent stopping laws

| player | Q0 | Q1 | N |
|---|---:|---:|---:|
| 0 | `1/2` | `1/2` | `0` |
| 1 | `1` | `0` | `0` |
| 2 | `3/11` | `8/11` | `0` |
| 3 | `0` | `0` | `1` |

Player 1 quits at date 0 surely, so the on-path game absorbs at date 0 with
probability one.  The four possible quitting coalitions and their
probabilities are

```text
{1}       4/11,        {0,1}       4/11,
{1,2}     3/22,        {0,1,2}     3/22.
```

Reading the four corresponding reward rows gives the claimed on-path payoff

```text
u = (32/11, 7/22, 1/2, 1/2).
```

## 3. Complete pure-time deviation table

Fix one deviator and keep the other three laws from Section 2.  Direct exact
enumeration gives the following payoff.  The last column represents every
finite quitting time at least 2 and Never; these choices coincide because the
relevant opponents have already quit by date 1 whenever player 1 is the
deviator, and player 1 quits surely at date 0 for every other deviator.

| deviator | Q0 | Q1 | time at least 2 / Never | on-path payoff |
|---|---:|---:|---:|---:|
| 0 | `32/11` | `32/11` | `32/11` | `32/11` |
| 1 | `7/22` | `-15/44` | `9/44` | `7/22` |
| 2 | `1/2` | `1/2` | `1/2` | `1/2` |
| 3 | `5/22` | `1/2` | `1/2` | `1/2` |

Every entry in a player's deviation row is at most that player's on-path
payoff.  Notice especially that player 1's deviation does not create an
uncontrolled tail: players 0 and 2 both quit by date 1 surely.

For a transparent check of the only nontrivial tie balances:

- Player 0 is indifferent between joining player 1 at date 0 and waiting
  because player 2 quits at date 0 with probability `3/11`; both values are
  `32/11`.
- Player 2 is indifferent between joining at date 0 and waiting because
  player 0 quits there with probability `1/2`; both values are `1/2`.
- Player 1 obtains `7/22` by following Q0, while Q1 gives `-15/44` and every
  later time gives `9/44`.
- Player 3 obtains `1/2` by waiting, whereas joining at date 0 gives only
  `5/22`.

## 4. From pure times to unrestricted behavioral deviations

The checked behavioral pure-time extremality theorem
`quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` says that an
arbitrary behavioral unilateral update cannot exceed the supremum of the
corresponding pure-time payoffs.  Section 3 computes that complete supremum
for every player and shows it equals the on-path payoff.  Hence the displayed
profile is exact terminal Nash against the full behavioral strategy class,
not merely against the three displayed finite-menu actions.

There is no hidden positive-reach continuation issue.  The profile absorbs at
date 0 on path.  If player 1 alone deviates, players 0 and 2 still force
absorption by date 1; if any other player deviates, player 1 still forces
absorption at date 0.

Applying
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` from
`TerminalUniformPayoffSelection.lean` therefore proves that

```text
(32/11, 7/22, 1/2, 1/2)
```

is a uniform-equilibrium payoff of E2.

## 5. Independent exact recomputation

For compatibility with the exact finite-clock verifier, divide all rewards by
`17`.  Instantiate `RationalLaw`s with common clock bound 2:

```text
player 0: finite (1/2, 1/2), Never 0
player 1: finite (1,   0),   Never 0
player 2: finite (3/11,8/11),Never 0
player 3: finite (0,   0),   Never 1.
```

Exact `Fraction` evaluation by `terminal_semantics` returns

```text
payoff = cap = (32/187, 7/374, 1/34, 1/34),
debt = (0,0,0,0),
exploitability = 0.
```

The resulting object passes `ProfileCertificate.verify()`.  This executable
check is independent corroboration of the hand table, not a Lean proof.

## 6. Scope and nonclaims

This result closes E2 as a prospective counterexample or difficult periodic
survivor.  It does not prove a structural theorem for arbitrary Fin4 tables,
and it does not validate any general bounded-period conjecture.  The initially
found clock-5 approximate profile is unnecessary for existence; its small
debt merely led to the support enumeration that exposed this exact boundary
equilibrium.

The inactive continuation after date 0 need not satisfy a Nash--Bellman root
condition.  Exact terminal Nash and the checked terminal-to-uniform compiler
do not require such an unreachable continuation condition.

## 7. Sources and declarations inspected

- `../UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`:
  `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` and
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime`.
- `../UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact`.
- `../Experiments/fin4_exact_search/fin4_exact_search/engine.py`:
  `RationalLaw`, `terminal_semantics`, and `ProfileCertificate`.
- `notes/CODEX_SPINOZA__E2_SINGLE_GATE_PERIODIC_SCREEN.md`: exact E2 table and
  the earlier periodic screens.  Its screens asserted no absence theorem.

## 8. Requested review

Please independently rederive the four rows in Section 3, including player
1's late deviation; verify that pure-time extremality applies to unrestricted
behavioral updates with this stopping-law profile; and confirm the exact
terminal-to-uniform compiler orientation.  A falsification attempt should
also test whether any absolute quitting time omitted from the three columns
can differ after the opponents' bounded supports.

