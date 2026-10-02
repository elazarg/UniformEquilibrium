# Feedback on the deleted-observer guardrail in `NONLOCAL_RECENTERING_ATTACK`

Reviewer: `CODEX_SOURCE_GATE`

## Verdict

The Revision 6/7 typing correction is right for the **inherited**
`QuittingPaidFirstDisagreementRow`: its `liveMass` is opponents-only and does
not imply actual joint reach. However, positive semantic debt permits a
different, debt-aware selection at the same literal profile. The reselected
row has a uniform own-survival factor and uniform actual joint reach. More
strongly, the selection produces a profitable behavioral fork whose source
and deviation share the literal live-root prefix up to that reached cut.

This repairs the input of Theorem 4.2 for the reselected row. It does not
produce an actual absorption car, nest the cuts across the outward-prefix
ancestry, or make the fork Nash--Bellman admissible. Therefore Guardrail 1
should be narrowed, not deleted: arbitrary paid rows remain deleted-player
objects, while positive-debt profiles admit an additional actual-reach
response-cut producer.

The complete proof and source audit are in
[`CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT.md`](../notes/CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT.md),
Section 11.

## Quantitative producer

Fix a profile `sigma`, player `i`, reward bound `M`, and semantic debt

```text
d_i(sigma) >= Delta > 0.
```

Let `f(q)` be the payoff of pure quit-time/Never choice `q`, let `C=sup f` be
the unrestricted cap, and let `nu` be `i`'s prescribed stopping law. The
checked stopping-law disintegration gives

```text
E_nu(C-f) = d_i(sigma),       0 <= C-f <= 2M.
```

For the bad set `A={C-f >= Delta/2}`, its mass `a` obeys

```text
a >= Delta/(4M).
```

Choose `r` with `f(r)>C-Delta/4`. Choose `s` to be the least finite
positive-mass bad prescribed time, or Never if all positive bad mass is at
Never. At `t=min(s,r)`, the prescribed own-survival is at least `a`. Also

```text
f(r)-f(s) > Delta/4.
```

The exact paid-row decoder therefore returns a row of gain `Delta/4` at
`start=t`, and `gain_le_liveMass` gives opponents-only survival at least
`Delta/(8M)`. The exact full/deleted survival factorization yields

```text
P_sigma(alive at t) >= Delta^2/(32 M^2).
```

Thus any cofinal sequence of these cuts satisfies Theorem 4.2 with one fixed
positive `lambda`; a bounded-date subsequence is its stated one-sided arm.

## Literal profitable fork

Replace the entire bad submass of `nu` by mass at `r`:

```text
nu_tilde = nu - nu|A + a delta_r.
```

The checked arbitrary stopping-law behavior constructor realizes this as an
unrestricted behavioral deviation. Exact affinity gives

```text
U_i(sigma[i <- nu_tilde]) - U_i(sigma)
  = integral_A (f(r)-f(q)) dnu(q)
  > Delta^2/(16M).
```

The two stopping laws have identical atoms strictly before `t`. Since source
survival through `t` is positive, their live hazards are identical strictly
before `t` and differ first at `t`. Opponents are unchanged. This gives a
literal common-prefix, actually reached, profitable fork, suitable for a
coupled recentered-kernel state.

## Effect on the conditioning-escape regression

The regression in
`CODEX_MINER__ACTUAL_PAID_FIRST_DISAGREEMENT_SUFFIX_COMPACTIFICATION.md`
chooses source witness `n+1`, whose prescribed mass is `epsilon_n`, and hence
gets vanishing own survival. Its prescribed date-zero atom has the same low
value and mass `1-epsilon_n`. The least-bad selection chooses date zero as
source and date `n` as receiver. The new row starts at zero and has joint
reach one. The regression therefore refutes arbitrary support-pair selection,
not debt-aware least-bad selection.

## Remaining blocker

This does not close the Fin4 chamber.

- The fork need not have positive prescribed absorption at its cut; an
  all-Never source with a profitable solo deviation shows that no such claim
  follows from debt.
- A paid response row does not control the incentives of the other players
  at a desired absorbing event; the exact Euler regression with full row
  reach still blocks a local Nashification inference.
- Selection is separate at every outward-prefix source. The selected cuts are
  not proved nested under suffix restriction. In the all-Continue-delay
  family they simply shift to the right with the inserted prefix, which is
  still the wrong orientation for a forward chronology.
- The later pure-time witness, or the right tail of the aggregate deviation,
  may escape after recentering. The ordinary full-kernel theorem retains the
  shared past, but no checked finite-forward or Nash--Bellman consumer accepts
  this coupled fork yet.

The new precise frontier is therefore: consume a uniformly reached,
source-attached profitable fork with common literal past, while preserving
the outward-prefix ancestry and controlling the participant-Nash seam.

## Checked declarations used

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime`;
- `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`;
- `QuittingPaidFirstDisagreementRow.gain_le_liveMass`;
- `quittingSurvivalPrefix_eq_opponentSurvivalWeight_mul_own`;
- `quittingStoppingLawBehaviorStrategy`;
- `quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy`; and
- `quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect`.

The bad-set mass selection and common-prefix aggregate fork are ordinary
mathematics, not checked Lean declarations.
