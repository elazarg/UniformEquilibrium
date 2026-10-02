# Independent review of the pair-base missing-face dichotomy

**Reviewer:** CODEX_MINER  
**Target:**
[`CODEX_RAMSEY__PAIR_BASE_PAID_SOFTENING_MISSING_BASE_DICHOTOMY.md`](../notes/CODEX_RAMSEY__PAIR_BASE_PAID_SOFTENING_MISSING_BASE_DICHOTOMY.md)  
**Verdict:** **PASS.**  Proposition 1.1, the exact and approximate constants
in Theorem 2.1, the missing-face cancellation identity, and the scoped field
independence audit are correct.  The result is an actual theorem only on the
specified two-base softening face and is correctly not applied to arbitrary
cap-port roots.

## 1. Same-source averaged leave advantage

Let `d` be the selected debtor and `e` the other sure-Quit base player.  The
source prescribes Quit for `d`, so its payoff is the pure-Quit endpoint

```text
Q_d = sum_A nu(A) r_d(A union {d,e}).
```

Because `e` Quits surely, the opponents' all-Continue mass for `d` is zero.
The pure-Continue endpoint is therefore

```text
C_d = sum_A nu(A) r_d(A union {e}),
```

with no tail term or normalization.  The checked stationary semantic
envelope is `max(Q_d,C_d)`, while the prescribed value is `Q_d`.
`target.debtor_gap` gives

```text
Gamma <= max(Q_d,C_d)-Q_d.
```

Since `Gamma>0`, the maximum must use `C_d`; hence `C_d-Q_d>=Gamma`, exactly
the average in (1.2).  The orientation and same-source provenance are both
correct.

## 2. Softening constants

At `q(p,z)`, orient `G` as Continue minus Quit for debtor `d`.  Conditional
on `e` quitting, the retained free law gives `G=L_d>=Gamma`.  Conditional on
`e` continuing, a nonempty free coalition compares two bounded terminal
rewards; the empty free coalition compares bounded tail `x_d` with the
bounded solo reward.  Thus the other conditional average is at least `-2M`,
and

```text
G >= z*Gamma-(1-z)*2M
  = (Gamma+2M)z-2M.
```

The prescribed Quit mass of `d` is `p`, so its regret to pure Continue is
exactly `pG`.  Exact endpoint Nash gives `pG<=0`.  Therefore either `p=0` or

```text
z <= 2M/(Gamma+2M),
1-z >= Gamma/(Gamma+2M).
```

The total one-stage product mass on the face omitting `e` is exactly `1-z`.
There are eight configurations of the other three players, including the
all-Continue cell, so the pigeonhole constant in (2.2) is correct.

For an `epsilon` root with `p>=theta>0`, `pG<=epsilon` implies
`G<=epsilon/theta`.  Combining with the lower bound gives

```text
1-z >= (Gamma-epsilon/theta)/(Gamma+2M),
```

and `epsilon<=theta*Gamma/2` gives the stated half-size positive bound.  No
free-law mass factor is missing: `nu` is a conditional probability law and
sums to one.

## 3. Interior cancellation and sign

If `0<p<1`, exact endpoint Nash forces the debtor's Quit-minus-Continue
difference to be zero, equivalently `G=0`.  If also `0<z<1`, direct
conditioning gives

```text
0 = z L_d + (1-z) H_d(x),
H_d(x) = -z L_d/(1-z) <= -z Gamma/(1-z).
```

The definition of `h_A` has the correct Continue-minus-Quit orientation.
Negating the weighted average shows that at least one free coalition has
Quit-over-Continue advantage at least `z*Gamma/(1-z)`.  At the empty free
coalition this is precisely solo reward minus tail.  The sign and empty-cell
interpretation in Section 3 are correct.

## 4. Missing-face and residual-field audit

Every terminal coalition in the original pair-base source contains the sure
player `e`.  The same is true after a unilateral deviation by debtor `d`,
because `e` still Quits at date zero.  Hence the source law, its prescribed
payoff, `d`'s cap/debt, and the paid first-disagreement row do not inspect any
coalition in (3.2), all of which omit `e`.  The fixed-law reset retains that
same law and is equally blind to the missing face.

The full-support packet and `ResidualHardClass` use the singleton table.  The
nonempty terms of `H_d` require pair or triple rows.  Punishment normality
only bounds the abstract punishment value by the solo payoff and does not
orient these fixed membership differences.  Thus no currently named hard-
residual field supplies (3.3) with debtor `d`, its orientation, and weights
`nu`.

The note's perturbation paragraph is properly scoped as field independence,
not as a realizable hard-residual perturbation theorem.  Changing only
`d`'s nonsingleton payoffs on coalitions omitting `e` leaves the displayed
source fields and singleton matrix unchanged, but may change the ambient
terminal witness or punishment value; the note explicitly does not claim
otherwise.

Finally, an arbitrary cap-port root may reselect all four marginals, so
Theorem 2.1 cannot be silently applied beyond `q(p,z)`.  Near the checked
minimum-fiber tube, positive exact absorption is already excluded by unique
all-Continue; this note concerns the off-tube/source-face seam and does not
replace the linear defect or debt moat.

