# CODEX SKEPTIC — One exact four-active portfolio refinement

Status: **completed bounded experiment**, with an ordinary exact proof of the
new profile and a certified reward-box improvement. Not a global lower bound,
not an all-accuracy producer, and not a new Lean theorem. All new artifacts are
local gitignored `math/` files. No export or external tool-source edit.

## 1. Question and outcome

Can an explicitly listed finite portfolio, containing every pure coalition
and some known cyclic/comparison clock shapes, miss a genuinely four-active
normalized rational table at a fixed accuracy, while the existing unrestricted
upper-profile checker finds a new policy covering a positive reward region?

Yes. At the table below, all 141 old policies have full terminal exploitability
at least 1/4, so none is 1/5-good. A single bounded call to the existing rational
finite-clock upper enumeration found an exact terminal Nash profile after
266 tested profiles. Adding it covers the entire clipped sup-norm reward box
of radius 1/80 around this table, while every old policy still has regret
strictly above 1/5 throughout that box.

This is a deliberately constructed cyclic binary table, not the result of a
global reward-table optimization. It is not an unresolved counterexample:
the new profile solves it exactly. The experiment tests adaptive portfolio
extension beyond the old two-active/dummy regression; it makes no novelty
claim about the solved game itself.

## 2. Full finite data and four-player activity

Players are 0,1,2,3. A coalition mask has bit i set exactly when player i quits
at the first quitting date. The reward on all-Never is zero. Nonempty rows are:

| Mask | Coalition | Reward vector |
| --- | --- | --- |
| 1 | 0 | (1,0,0,0) |
| 2 | 1 | (0,1,0,0) |
| 3 | 01 | (1,1,1,0) |
| 4 | 2 | (0,0,1,0) |
| 5 | 02 | (1,0,1,1) |
| 6 | 12 | (0,-1,-1,0) |
| 7 | 012 | (1,1,-1,1) |
| 8 | 3 | (0,0,0,1) |
| 9 | 03 | (1,1,0,1) |
| 10 | 13 | (0,-1,0,-1) |
| 11 | 013 | (1,-1,1,1) |
| 12 | 23 | (0,0,-1,-1) |
| 13 | 023 | (1,1,1,-1) |
| 14 | 123 | (1,-1,-1,-1) |
| 15 | 0123 | (-1,-1,-1,-1) |

Every own singleton reward is 1. Each player has both a strictly profitable
join context and a strictly profitable leave context. The following
background coalitions exclude that player; gain means the difference between
joining and staying out, or its negative for leaving:

| Player | Join background; gain | Leave background; gain |
| --- | --- | --- |
| 0 | 23; 1 | 123; 2 |
| 1 | 02; 1 | 03; 2 |
| 2 | 03; 1 | 01; 2 |
| 3 | 01; 1 | 02; 2 |

Thus no player is a payoff dummy or has one action globally dominant across
terminal coalition contexts. This claim does not say that all four players
must randomize in the new equilibrium; player 0 does not.

## 3. The complete old portfolio

Each item below is an actual independent stopping-law profile. A player's
Never mass is literal probability of never quitting, not a correlated choice
between whole profiles. All unspecified finite atoms are zero.

1. **81 one-date policies.** For every vector c in {0,1,2}⁴, player i quits at
   date 0 with probability cᵢ/2 and otherwise Never. Names are
   `ONE_DATE_c0c1c2c3`. In particular this includes all 16 pure coalition
   policies, including all-Never.
2. **48 finite cyclic policies.** For every ordered three-player subset and
   every order of all four players, repeat that order four times. At each
   displayed date only the displayed player has conditional quit hazard 1/2.
   Its kth own turn has unconditional atom 2⁻ᵏ, k=1,2,3,4, with residual Never
   mass 1/16. A player omitted from a three-cycle always Never. The clocks are
   12 or 16. Names are `HALF_CYCLE_` followed by the ordered player labels.
   Counts are 4·6+24=48. These are finite truncations of cyclic word shapes,
   not a test of every cyclic, periodic, or stationary policy.
3. **12 finite comparison policies.** For every distinct ordered pair (j,k),
   player j quits surely at date 0; player k is uniform on dates 1,2,3,4;
   the other players Never. Clock bound is 5. Names are `COMPARISON_j_k`.
   These are relabelings of the finite comparison shape discussed in
   `CODEX_SKEPTIC__FIN4_BLINDSPOT_RESTART.md`; there is no claim that its
   original hard-deadline payoff identities transfer to this different table.

The saved manifest contains all 141 literal laws, their payoffs, full caps,
individual debts, and maximum debts. Exact minimum exploitability is 1/4,
attained uniquely by `ONE_DATE_2111`, the root quit vector (1,1/2,1/2,1/2).

The evaluator includes every date in the clock, one date after the clock,
and Never. These are enough for the unrestricted behavioral cap against
finite-clock independent opponents. In particular this is not a
finite-deadline Nash calculation that omits late deviations.

## 4. New profile and an independent exact calculation

The emitted clock-1 laws are:

    player 0: Quit at date 0 surely;
    players 1,2,3: independently Quit at date 0 with probability 1/3,
                   otherwise Never with probability 2/3.

Payoffs and full best-response caps are both

    (25/27, 1/3, 1/3, 1/3),

so all four debts are zero. For a direct check, let the predecessor cycle be
3→1→2→3. Conditional on player 0 quitting, an active player's Quit payoff is
1 if its predecessor continues and -1 if its predecessor quits; its Continue
payoff is the indicator that its predecessor quits. At predecessor quit
probability 1/3 these two expected payoffs are both 1/3. Every date after 0
and Never gives the same payoff as Continue, since player 0 has already quit.

Player 0's Quit-at-0 payoff is 1 except when all three others quit, when it
is -1; hence it is 1-2/27=25/27. Never gives 1/27, since its reward without
joining is 1 exactly when the other three all quit. Quitting at any later
date gives 1/27+(2/3)³=1/3. Thus its exact cap is also 25/27. A general
unilateral stopping law cannot exceed the maximum of these pure stopping
payoffs, so the computation covers unrestricted behavioral deviations.

## 5. A full-dimensional uncovered-cell reduction

Write r⁰ for the displayed 60-coordinate table and set

    B = {r in [-1,1]⁶⁰ : ‖r-r⁰‖∞ ≤ 1/80}.

This clipped box has positive length in every coordinate, including the
coordinates at the boundary of the normalized cube. For any fixed policy,
terminal exploitability is 2-Lipschitz in the reward sup norm: its prescribed
payoff and every deviation payoff are each 1-Lipschitz, and the cap is their
supremum. The same literal policy is reused at every table.

Consequently, throughout B,

    every old policy: E ≥ 1/4 - 2/80 = 9/40 > 1/5;
    the new policy:   E ≤ 0   + 2/80 = 1/40 < 1/5.

Adding this one policy therefore removes B from the old portfolio's
uncovered region at accuracy 1/5. All 60 rational interval endpoints are
saved in the report. The assertion is reward-uniform over B, not merely a
point certificate. It is not a full-cube cover or a decrease of the true
global minimum, which was already zero at r⁰.

## 6. Executed bounded search and verification

The local wrapper imports the existing `UpperSearch` class read-only from
`../Experiments/fin4_exact_search/fin4_exact_search/engine.py`. It starts a
fresh diagonal enumeration, with no supplied successful profile. The strict
upper threshold is 1/8, below the old portfolio target 1/5. It stops at the
first certificate, 2,000 quanta, or 45 seconds; an external 55-second timeout
also bounded the invocation. It found the certificate after 266 profiles,
269 quanta, and about 0.05 seconds of recorded enumeration time. Runtime is
diagnostic only; all mathematical tests use exact rational arithmetic.

This used only the existing upper-profile search, not the lower subdivision
search, not a stationary optimizer, and not an optional decision oracle.
The independent coalition-law evaluator from the earlier local portfolio
regressions cross-checked the old minimizing profile and the emitted new
profile. The full old portfolio was recomputed with the existing exact
engine; the public command-line verifier separately accepted the new file.

Executed from `math/`:

```sh
PYTHONDONTWRITEBYTECODE=1 timeout --signal=TERM --kill-after=5s 55s python experiments/CODEX_SKEPTIC__FOUR_ACTIVE_PORTFOLIO_TEST.py prepare
PYTHONDONTWRITEBYTECODE=1 timeout --signal=TERM --kill-after=5s 55s python experiments/CODEX_SKEPTIC__FOUR_ACTIVE_PORTFOLIO_TEST.py search
PYTHONDONTWRITEBYTECODE=1 python experiments/CODEX_SKEPTIC__FOUR_ACTIVE_PORTFOLIO_TEST.py verify
PYTHONDONTWRITEBYTECODE=1 python ../Experiments/fin4_exact_search/run.py verify experiments/CODEX_SKEPTIC__FOUR_ACTIVE_UPPER_CERTIFICATE.json.gz
```

The last command returned `verified exact profile certificate;
exploitability=0 threshold=1/8`. No packages were installed. The external
package's worktree remained unchanged.

## 7. Artifacts and inspected mathematical interfaces

All paths below are relative to `math/experiments/`:

- `CODEX_SKEPTIC__FOUR_ACTIVE_PORTFOLIO_TEST.py`: bounded experiment wrapper.
- `CODEX_SKEPTIC__FOUR_ACTIVE_TABLE.json`: exact normalized reward table.
- `CODEX_SKEPTIC__FOUR_ACTIVE_PORTFOLIO.json.gz`: explicit old policies and caps.
- `CODEX_SKEPTIC__FOUR_ACTIVE_UPPER_CERTIFICATE.json.gz`: new rational profile.
- `CODEX_SKEPTIC__FOUR_ACTIVE_UPPER_STATE.json.gz`: bounded search endpoint.
- `CODEX_SKEPTIC__FOUR_ACTIVE_REPORT.json`: exact gaps and reward-box endpoints.

The engine's canonical table hash is
`be414b3e8b9933bc0330c52a079124908b6baa986ee7c3bd380514e16ba3d66e`.

Read `Experiments/README.md`, the exact-search README, and the concrete engine
definitions `terminal_semantics`, `ProfileCertificate.verify`, and
`UpperSearch.step`. The named Lean interfaces inspected, without rebuilding,
were:

- `FinFourRationalFiniteClockProfileCompleteness.realCap_eq_continuationBestResponseValue`
  in `Research/Quitting/FinFourRationalFiniteClockProfileCompleteness.lean`:
  finite-clock candidate caps equal the full continuation response value,
  with zero mass at the auxiliary after-support atom.
- `abs_quittingTerminalExploitability_sub_le_of_reward_close` in
  `Research/Quitting/TerminalExploitabilityRewardRobustness.lean`:
  fixed-profile exploitability changes by at most twice the reward distance.

These are existing checked interface declarations, not a claim that this
new JSON payload was imported into or checked by Lean.

## 8. Verdict and stopping point

The requested single four-active refinement succeeded. An explicit old
portfolio gap led to a new independently verified mixed finite-clock policy
and a positive-volume certified reduction of its uncovered reward region.
The result gives no lower bound against policies outside the listed old
portfolio. In particular it must not be reported as a stationary or global
counterexample gap.

No more tables or search stages are run in this tranche. A genuinely stronger
next mathematical output would be a rule forcing a new policy to cover part
of every nonempty uncovered region of a reward-uniform portfolio, with
controlled progress; this successful single box supplies no such rule.
