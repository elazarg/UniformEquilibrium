# Review of Section 31 / Proposition 31

**Reviewer:** `CODEX_EULER`  
**Scope:** only Section 31 of
`notes/CODEX_CEDAR__PAID_ROW_REENTRY.md`  
**Verdict:** **valid**, with one wording repair: the fixed aggregate transfer
is eventual along the selected ranks, not asserted at every rank.

## Exact identity

Write `d_i(X)` for terminal semantic debt and `D(X)=sum_i d_i(X)`.  The named
checked identity
`fullReplacementPrescribedGain_eq_sourceDebt_sub_endpointDebt` gives

```text
G_n = d_m(P_n)-d_m(F_n).
```

Therefore, by an exact finite-sum split,

```text
sum_(j != m) (d_j(F_n)-d_j(P_n))
= D(F_n)-D(P_n) - (d_m(F_n)-d_m(P_n))
= D(F_n)-D(P_n)+G_n.
```

Global `base_minimum` applies because the literal full-replacement semantic
pair `F_n` is in the terminal semantic carrier.  Hence

```text
D(F_n) >= D(base),
D(P_n)=D(base)+e_n,
```

and the displayed expression is at least `G_n-e_n`.  Thus (31.2) is exact.
In this scalar calculation, `base_minimum` is used precisely in the single
inequality `D(F_n)>=D(base)`.

## Eventual constant and fixed recipient

Let `d=d_m(base)>0`.  Continuity of terminal semantic debt plus
`source_tendsto` gives `d_m(P_n)->d`; continuity of total debt gives
`e_n->0`.  The checked replacement tolerance yields pointwise

```text
G_n >= d_m(P_n)/2.
```

On ranks satisfying

```text
d_m(P_n) >= 3d/4,
e_n <= d/8,
```

we therefore have

```text
G_n-e_n >= 3d/8-d/8=d/4.
```

Both conditions hold eventually, proving (31.3).  Since the paid-row context
supplies an observer distinct from `m`, the opponent set is nonempty.  At
each sufficiently late rank, one opponent has debt increment at least the
average

```text
d/[4 (|I|-1)].
```

There are finitely many opponents, so one label occurs on infinitely many of
these rankwise choices; extracting its increasing occurrence sequence proves
(31.4).  No positivity of every individual increment is needed.

## Scope

The chronology disclaimer is correct and essential.  `P_n` and `F_n` are
terminal semantic pairs of literal behavioral profiles.  The inequality
locates terminal best-response debt at `F_n`; it does not show that the reset
root is simultaneous Nash against a punishment-floor tail, that the selected
recipient owns an absorbing row, or that any exact Nash--Bellman edge reaches
or leaves `F_n`.  The pigeonhole recipient also need not equal the curvature
observer selected by the paid-row decoder.

Nor is (31.2) directly iterable.  After replacing the selected recipient by a
best response, its debt decrease may be funded by the already positive total
excess `D(F_n)-D(base)`.  Global minimality gives a floor, not a fresh
near-minimum source or a return map.  Proposition 31 is therefore a genuine
one-reset quantitative transfer, not a floor-admissible charged chronology.

The phrase “full quantitative leverage” is safe only in the narrow sense of
the **direct scalar consequence of `base_minimum` for this literal reset**:
after the exact debt split, (31.2) is just `D(F_n)>=D(base)`.  It should not be
read as excluding consequences that combine global minimality with new
game-specific or chronological structure.

Finally, the proposition headline should say “every literal full reset ...
**eventually creates**” (or “along all sufficiently late ranks creates”).
The proof establishes no uniform `d/4` bound at the finitely many early
ranks.  With that wording repair, I found no mathematical gap.
