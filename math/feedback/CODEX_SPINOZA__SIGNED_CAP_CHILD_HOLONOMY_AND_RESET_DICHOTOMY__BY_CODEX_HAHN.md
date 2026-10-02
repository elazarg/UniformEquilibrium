# Review of signed cap-child holonomy and reset dichotomy

Reviewer: `CODEX_HAHN`

Reviewed file:
`notes/CODEX_SPINOZA__SIGNED_CAP_CHILD_HOLONOMY_AND_RESET_DICHOTOMY.md`

Reviewed SHA-256:
`877e0d8b2253b10c74e74d1bb877461732dcd37c06c0f8e36a59924c5028044e`

## Verdict

**PASS.** The exact displacement recurrence, its bounded forcing term and
finite-total-variation consequence, the recursive cap-clock classification,
and the negative-holonomy conclusion in the infinite-reset arm are correct.
The note also keeps the decisive scope boundary: neither arm is yet a
Nash--Bellman chronology.

## Exact displacement recurrence

Condition on player `b`'s current Bernoulli action while keeping the outsider
coalition law fixed. Under `bar q^n`, an empty outsider coalition reaches
`W_i^n`; under `q^n`, the same event mixes continuation to `U_i^n` with the
singleton `{b}` outcome. A nonempty outsider coalition `S` similarly changes
from `r_i(S)` to a mixture with `r_i(S union {b})`. Direct subtraction gives
exactly

```
Delta_i^(n+1) = bar c_n Delta_i^n + h_(n,b) G_(n,i).
```

The displayed formula for `G_(n,i)` is the resulting conditional payoff
difference. With all payoffs and rewards in `[-M,M]`, the stated `4M` bound is
safe (and deliberately nonsharp). Hence the increment is bounded by
`2M(1-bar c_n)+4M h_(n,b)`. Both series are summable, so every displacement
has finite total variation and a limit. Unrolling the affine recurrence gives
the stated signed series, with no lost survival factor.

## Cap clocks and reset sign

Sure termination by player `b` makes every outsider cap attainable by a pure
time in `0,...,n,Never`. Dynamic programming across the literal nested child
therefore permits the recursive choice `0` or `T_(n,j)+1`. Finitely many
resets leave one old finite cap (or Never) shifted forever; otherwise reset
indices are cofinal.

At a reset, Quit0 is a complete cap. Since the prescribed player-`j` root has
positive Continue probability, its debt is

```
d_j(zeta^(n+1)) = (1-h_(n,j)) bar E_n.
```

The fixed debt floor therefore gives `bar E_n >= delta`. At the original
exact root, positive Continue probability gives `E_old <= 0`. The endpoint
comparison after removing only `b`'s current hazard has the exact tail term
`-bar s_(n,j) Delta_j^n`; all remaining current-row terms are bounded by
`6M h_(n,b)`. Thus at every late reset

```
-bar s_(n,j) Delta_j^n >= delta-o(1),
```

and `bar s_(n,j) -> 1` forces `Delta_j^n <= -delta/2`. Convergence of the
full displacement sequence yields the claimed strictly negative limit.

## Scope

Finite total variation of `Delta` does not imply summability of its values,
and a nonzero negative limit is a macroscopic payoff externality rather than
a semantic return. A shifted full cap is likewise not a persistent hazard on
an accepted exact spine. The note does not confuse either output with root
Nash, source renewal, or a terminal consumer.

The nested-child source cited in this version is the earlier frozen SHA that
already contains all mathematical inputs used here; the later repair only
made cap attainment and wording explicit. I found no dependency on the
repaired wording.

