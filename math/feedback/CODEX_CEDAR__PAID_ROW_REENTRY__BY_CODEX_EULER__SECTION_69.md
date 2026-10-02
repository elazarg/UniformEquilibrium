# Review of paid-row Proposition 69

Reviewer: `CODEX_EULER`

Verdict: **PASS**.

I checked Section 69 of
[`CODEX_CEDAR__PAID_ROW_REENTRY.md`](../notes/CODEX_CEDAR__PAID_ROW_REENTRY.md),
including the off-diagonal averaging, shadow error, Bellman motion constant,
raw-to-aggregate product estimate, bounded-row consequence, and the stated
conditional scope.

## Static orbit ledger

The returned coalition orbit gives `u_L=u_0` coordinatewise.  Hence

```text
sum_(t<L) sum_i [u_(t+1,i)-u_(t,i)] = 0.
```

Its `L` selected-coordinate terms are each at least `gamma`, so the sum of
the exactly `L(n-1)` off-diagonal terms is at most `-L gamma`.  One such term
is therefore at most `-gamma/(n-1)`.  This argument does not require one
fixed harmed player around the orbit.

At the selected edge, two `epsilon` shadow errors change the payoff drop by
at most `2 epsilon`.  Under

```text
epsilon <= gamma/[4(n-1)],
```

the exact endpoint drop remains at least `gamma/[2(n-1)]` in absolute value.
All signs and the factor two in (69.11) are correct.

## Exact-edge motion and constants

For every exact edge in the floor-admissible boxed relation, its current and
tail payoffs lie in the reward box.  The checked declaration
`abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass` therefore
gives

```text
|current_i-tail_i| <= 2 M q.
```

Although the charged relation presents an edge from its stored `tail` to its
Bellman `current`, the estimate is absolute, so telescoping along the path in
the relation's direction is legitimate.  Applied to the selected shadow
segment, it yields

```text
gamma/[2(n-1)] <= 2 M Raw(pi_t),
Raw(Pi) >= gamma/[4M(n-1)].
```

Thus the orientation and constant in (69.7) check exactly.

For finite `q_k in [0,1]`, if one `q_k=1` the product estimate is immediate.
Otherwise

```text
1/(1-q_k) >= 1+q_k,
product_k(1+q_k) >= 1+sum_k q_k,
```

so

```text
product_k(1-q_k) <= 1/(1+Raw),
Agg >= Raw/(1+Raw).
```

Substituting the raw lower bound gives exactly

```text
Agg(Pi) >= gamma/[gamma+4M(n-1)].
```

If at most `H` edges occur, positive raw mass ensures the concatenation is
nonempty and averaging gives one edge of charge at least
`gamma/[4M(n-1)H]`.  The endpoint seam `2 epsilon` follows directly from
`u_L=u_0`; no pathwise estimate is used for it.

## Scope and consumer

The conclusion is correctly conditional.  The proposition does not produce
any floor-admissible state, exact edge, connecting path, or uniform row-count
bound.  It proves that **once** an arbitrary-accuracy global exact payoff
shadow of the checked static orbit is supplied, a separate charge-retention
hypothesis is unnecessary: the orbit's off-diagonal payoff loss forces a
fixed aggregate absorption denominator.  The reviewed aggregate-block
consumer then covers unrestricted behavioral deviations; with an additional
uniform row-count bound the stronger single-edge charge follows.

Nothing in the proof turns the static membership-toggle orbit into a reached
chronology.  Path lengths may diverge, and the source-matched construction of
the exact shadows is precisely the remaining open input.  The section's
conditional-connectivity wording and its distinction between aggregate and
single-edge charge are therefore exact.

## Addendum: Corollary 69B

Verdict: **PASS**.

The preceding ledger depends only on a closed finite payoff sequence and a
lower bound `g` for each selected coordinate's forward gain.  Proposition 66
supplies exactly such a closed deterministic strategy-update sequence with
`g=3 gamma/4`.  Substitution into Proposition 69 gives

```text
epsilon <= g/[4(n-1)] = 3 gamma/[16(n-1)],
Raw >= g/[4M(n-1)] = 3 gamma/[16M(n-1)],
Agg >= g/[g+4M(n-1)]
    = 3 gamma/[3 gamma+16M(n-1)].
```

All constants in (69.14) are therefore exact.  With at most `H` exact rows,
averaging gives (69.15) with the same substitution.

The scope qualification is necessary and correct.  Proposition 66 bounds the
number of behavioral updater segments by `2^n`, but it gives no bound on the
number of exact Bellman edges in a connector shadowing one segment.  Thus it
does not supply `H`.  Its small updater-debt conclusion is unused in the
off-diagonal/absorption ledger and may matter only in a future producer for
the assumed connectors.  Corollary 69B remains a conditional exact-path
reduction, not a construction of those paths.
