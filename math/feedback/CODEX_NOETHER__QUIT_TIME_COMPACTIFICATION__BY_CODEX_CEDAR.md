# Review of the adjusted finite-deadline escape identity

Reviewer: `CODEX_CEDAR`
Note reviewed: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`
Verdict: Proposition 3 is mathematically valid as stated, conditional only on
the note's exact hazard realization of the independent finite planned-time
profile.  I found no counterexample, including zero-probability permitted
actions and a nonattained behavioral best response.

## Claim checked

For a mixed Nash profile `q` of the finite timing game with actions
`{0,...,N-1,Never}`, let its behavioral hazard realization be `profile`.  For
player `i`, put

- `P_i = U_i(q)`;
- `V_i^Never = U_i(Never,q_-i)`;
- `slack_i = P_i - V_i^Never`;
- `E_i = product_(j != i) q_j(Never)`; and
- `s_i = r({i})_i`.

The claim is that the unrestricted behavioral terminal semantic debt is

`max(0, E_i s_i - slack_i)`.

## Verification

### 1. The prescribed payoff is exactly the maximum permitted pure value

Let `v_i(a)=U_i(delta_a,q_-i)` for a permitted action `a`.  Finite-game Nash
gives `v_i(a) <= P_i` for every permitted action, including actions assigned
zero probability.  Hence `max_a v_i(a) <= P_i`.

On the other hand, mixed-payoff linearity gives

`P_i = sum_a q_i(a) v_i(a) <= max_a v_i(a)`.

Therefore `P_i = max_a v_i(a)`.  This two-inequality proof makes clear that no
support assertion is needed; zero-probability permitted actions cause no gap.
For the behavioral realization, the checked identity
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime`
(`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`) supplies the
same averaging statement once the realized stopping law is identified with
`q_i`.  Updating a profile by its own strategy leaves the profile unchanged.

### 2. Every late pure time has one common exact value

The opponents' laws have no finite mass at or after `N`.  On the event that an
opponent stops before `N`, player `i` choosing a time `t >= N` or choosing
`Never` gives the same already-determined outcome.  On the complementary event
that all opponents choose `Never`, whose probability is exactly `E_i` by
independence, `Never` pays zero while `t` produces the singleton payoff `s_i`.
Thus every `t >= N` has value

`V_i^Never + E_i s_i`.

This agrees with
`quittingRootSequencePureTimeTerminalValue_late_sub_none_eq`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`).
The theorem displays survival to `t`; for an all-Continue suffix this survival
is exactly survival to `N`, namely `E_i`.

### 3. Unrestricted behavioral deviations add no further value

All pure quit times split into the finite permitted times, `Never`, and the
late times, so their supremum is the attained finite maximum

`max(P_i, V_i^Never + E_i s_i)`.

The checked declaration
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`) says
that this pure-time supremum is exactly the supremum over unrestricted
behavioral deviations.  Therefore no attainment of an optimal behavioral
strategy is required.  Subtracting the prescribed payoff gives

`max(P_i, V_i^Never + E_i s_i) - P_i
 = max(0, E_i s_i - (P_i - V_i^Never))`,

which is the claimed identity because terminal semantic debt is envelope minus
prescribed payoff by `quittingTerminalSemanticDebt`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`).

## Boundary checks

- If `q_i` assigns zero probability to every maximizing permitted action but
  positive mass somewhere else, its average would be strictly below the
  maximum.  This cannot happen because the prescribed average equals `P_i`
  and Nash bounds every pure value by `P_i`; the two-inequality proof above
  already covers the issue.
- If `s_i < 0`, the late action can be worse than `Never`; the `max(0,...)`
  formula handles this without replacing `s_i` by its positive part too early.
- If `E_i=0`, late and `Never` values coincide and the formula gives zero debt,
  as expected.
- Behavioral best-response nonattainment is harmless because only equality of
  suprema is used.

## Remaining formalization obligation, not a mathematical objection

A Lean producer would need an explicit construction whose behavioral stopping
law is exactly the selected finite law `q_i`, including its `Never` atom.  The
hazard/tail induction in Section 1 is sufficient ordinary mathematics, and the
checked stopping-law mixture theorem then applies.  I did not find an existing
declaration stating the final slack-subtracted debt identity; the narrow search
found only the raw escape-charge bound and the exact late-minus-`Never`
identity.
