# Compressed Clock Ledger and Floor-Tight Residual Review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: Sections 58.11--58.12, Propositions 66--67.  I independently checked
positive-date enumeration, zero-row compression, the logarithmic telescope,
the source-floor orientation, and the recurrent sign dispatch.  This is
ordinary mathematics, not Lean-checked.

## Verdict

**Propositions 66--67 are VALID ordinary mathematics as stated.**  Proposition
66 converts the entire summable chronology into a source-matched positive-row
graph with unbounded net logarithmic contraction.  Proposition 67 proves that
a positive-tangent expanding chart can use only a strictly production-normal
owner; punishment-tight owners contract.  Neither result turns logarithmic
clock contraction into semantic absorption charge or supplies a return.

## 1. Positive-row compression

If the canonical tail has only finitely many positive-absorption dates, every
row after the last one has zero absorption.  The checked
`zeroAbsorption_dynamicDebtEdge_plateau`
(`UniformEquilibrium/Quitting/Debt/Dynamic/ZeroAbsorptionPlateau.lean`)
makes each such root all-Continue and preserves its payoff, so the tail is
eventually all-Continue.  On the complementary branch the positive dates can
therefore be enumerated increasingly as `d_k`.

Every date strictly between `d_k` and `d_(k+1)` is a zero row.  Repeated use
of the same checked plateau theorem gives

```text
x_(d_k+1)=x_(d_k+2)=...=x_(d_(k+1))=X_(k+1).
```

Thus the actual one-row successor after the positive root at `d_k` is exactly
the next compressed source.  No root coordinate is claimed to remain fixed;
only the payoff equality used in `(N80)--(N81)` is needed.

Substituting

```text
V_k=(X_k-b)/Q_k,
Z_k=(X_k-X_(k+1))/Q_k,
Theta_k=Q_(k+1)/Q_k
```

gives `V_k=Z_k+Theta_k V_(k+1)` by exact algebra.

## 2. Global logarithmic ledger

The positive `Q_k` form a subsequence of the canonical summable absorption
charges, hence are summable and tend to zero.  Since every ratio is positive,

```text
sum_(k<N) log Theta_k
 =sum_(k<N)[log Q_(k+1)-log Q_k]
 =log(Q_N/Q_0).
```

As `Q_N->0`, the right side tends to negative infinity.  Negating gives
`(N83)`.  Sparse ratios above one are fully compatible with this statement;
the result concerns net log contraction, not monotonicity or ordinary
absorption charge.  Proposition 65 applies to any consecutive-chart
subsequence once its compact chart data and finite ratio limit are selected.

## 3. Punishment-tight active owners

For an active limiting owner `i`, packet pinning gives
`b_i=r_i({i})`.  The canonical-tail source bound is

```text
quittingPunishmentValue reward i <= x_i^n.
```

If punishment is tight at the solo payoff, then `x_i^n-b_i>=0`.  Division by
the positive absorption scale and Proposition 64's radial readout yields
`R_i>=0`.  Since packet normality already gives punishment at most solo, the
contrapositive is the strict statement

```text
R_i<0 -> punishment_i<r_i({i}).
```

In a recurrent same-chart transition with `z_i>0`, the corrected Proposition
65 dichotomy has only two branches.  Tightness rules out `R_i<0`, while
`R_i=0` is incompatible with `z_i=(1-theta)R_i`; hence
`R_i>0,theta<1`.  The sign orientation is correct.

## 4. Exact scope

The logarithmic account is not the charge consumed by the floor-prefix or
near-return compilers: the total `sum Q_k` is finite.  Nor does Proposition 67
control strictly normal owners, for which a fixed punishment slack permits a
negative `O(Q_k)` radial displacement.  The remaining universal obstruction
is therefore a support-changing graph which assigns its expanding steps to
strictly normal owners while overpaying them with later log contraction.

Gauss Proposition 50 gives a complementary selection: suffix-record positive
rows always satisfy `Theta<=1`, eliminating the expanding branch there, but a
common active owner need not survive to the next chart.  Together the results
isolate support turnover/deleted-clock transport rather than scalar clock
oscillation as the next producer obligation.
