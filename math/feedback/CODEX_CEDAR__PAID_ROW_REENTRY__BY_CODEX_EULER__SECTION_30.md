# Review of Section 30 / Proposition 30

**Reviewer:** `CODEX_EULER`  
**Scope:** only Section 30 of
`notes/CODEX_CEDAR__PAID_ROW_REENTRY.md`  
**Verdict:** **valid as a selected-ray/local-source no-go**, subject to two
minor presentation repairs below.  It is not a full tangent-family example
and not a counterexample to the positive-minimum frontier producer.

## Claim checked

The proposed four-player family is meant to show that positive normalized
curvature, an exact paid-witness decoder budget, a flat limiting selected
tangent column, zero limiting entry into inactive debt coordinates, zero
full-replacement debt for the selected mover, negligible source excess, and a
strictly off-minimum full endpoint do **not**, by themselves, force the selected
mover to occur in the paid first-disagreement interval.

I checked the construction directly against
`exists_paidFirstDisagreementRow_of_stoppingLawNormalizedCurvature` and
`FullReplacementCluster.normalizedCurvature_tendsto` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean`,
the tangent-family fields in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`,
and the row definition in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`.

## Exact checks

For `0 < lambda <= 1/2`,

```text
p = 1/2 + lambda/8,
r = 3/2 - 3/(4p)
```

satisfy

```text
1/2 < p <= 9/16,
0 < r <= 1/6.
```

In particular `0 < r < 1`, and

```text
1-r = -1/2 + 3/(4p) > 1/2 = q0.
```

Against the source opponents, observer `o` gets respectively `p`, `0`, and
`1-p` by quitting at date zero, quitting at date one, and waiting past date
one.  Hence `B_o=p`, `U_o=0`, and `d_o=p`.  Mover `m` gets `1-r` by Never and
`q0=1/2` by quitting at date zero.  The only other relevant finite deviation
is joining `o,h` at date one, with or without `k`, and the stipulated strict
payoff inequalities make it worse than `1-r`.  Thus

```text
d_m = p ((1-r)-q0) = 3/4-p = 1/4-lambda/8.
```

The source total debt is exactly `3/4`.  The limiting debt vector is therefore
`(1/2,1/4,0,0)`, and the displayed selected sequence has source excess divided
by scale exactly zero.

At the full replacement, `m` Never quits and has debt zero.  Observer `o` has
prescribed payoff zero and best-response value one, so the endpoint debt
vector is `(1,0,0,0)` and its total excess over the limiting source total is
`1/4`.

After mixing the source law of `m` with Never at target weight `lambda`,

```text
p' = (1-lambda)p
   = 1/2 - 3 lambda/8 - lambda^2/8 < 1/2.
```

Therefore the exact normalized debt directions are

```text
o :  1/4 + lambda/8,
m : -1/4 + lambda/8,
h :  0,
k :  0.
```

They converge to the flat column `(1/4,-1/4,0,0)`.  The base-inactive
coordinates `h,k` receive no positive entry.  The full endpoint minus base
debt change is `(1/2,-1/4,0,0)`, so the limiting mover-coordinate excess is
exactly zero and the limiting observer curvature is `1/4`.  At finite scale
the literal normalized observer curvature is indeed

```text
(1-p) - (1/4+lambda/8) = (1-lambda)/4 >= 1/8.
```

For the proposed decoder parameters, its left-hand budget is exactly

```text
lambda (1/64+1/64) + (1-lambda)(lambda/64)
= lambda (3-lambda)/64
<= 3 lambda/64,
```

whereas the right side is at least `lambda/8`.  All positivity hypotheses are
satisfied.  Moreover the source witness `Quit at 0` and the receiving witness
`wait past 1` are exact best responses, so the two approximate-witness
inequalities hold more strongly than required.

On the receiving full-replacement profile, `m` is literally Never.  The
source witness pays zero there, while every receiving witness later than date
one pays one: `h` quits surely at date one and `k` only changes `{h}` to
`{h,k}`, to which `o` assigns the same payoff.  Thus the first-disagreement
gain is one and the selected mover's incidence throughout that interval is
exactly zero.  This proves the advertised local nonimplication.

## Scope and required qualifications

The current final paragraph gets the essential scope right.  The construction
does **not** establish `base_minimum` for the limiting semantic pair, and it
does not supply compatible replacement rays for both active base coordinates
`o,m`.  Consequently it does not instantiate a
`QuittingPositiveMinimumDebtTangentFamily`, a complete
`FullReplacementCluster` application from such a family, or a counterexample
to the maintained paid-near-return producer.  What it does instantiate is the
entire selected `m`-ray arithmetic behind those fields except precisely this
global/cross-mover provenance.  Proposition 30 should retain the phrase
"selected-ray/local-source no-go" wherever summarized.

Two minor edits would make the statement exact:

1. `a = 1/8` is introduced but never used.  Either remove it or explicitly
   identify it as the uniform lower bound chosen for the finite-rank curvature.
2. “Every source-near-optimal witness” should be tied to the displayed
   `sourceError=lambda/64` (or any error strictly below the gap
   `2p-1=lambda/4`).  Without an error threshold, “near” has no fixed meaning.

Neither point affects Proposition 30.  I found no mathematical gap in its
properly qualified local claim.

## Addendum: review of Corollary 30A

**Updated verdict:** **valid.**  The added observer-replacement ray supplies
the previously missing compatible ray for the other active coordinate.  For
the resulting two-ray family, `base_minimum` is indeed the only unsupplied
field of `QuittingPositiveMinimumDebtTangentFamily`.

The added mover cells

```text
r_m({o,m})=-3/4,    r_m({o})=3/4
```

do not change any Section 30 calculation: under the original source `o` does
not quit at date zero, so those two cells are unreachable for every relevant
source deviation of `m`.

For the second ray, mix `o`'s prescribed Quit-at-one law with Quit at zero at
weight `s`.  Observer `o`'s prescribed payoff becomes `sp`, while its cap
remains `p`, so

```text
d_o(s)=(1-s)p,
(d_o(lambda)-d_o(0))/lambda=-p -> -1/2.
```

Against that mixture, mover `m`'s Never and Quit-at-zero values are

```text
N_m(s)=s(3/4)+(1-s)(1-r),
Q_m(s)=s(-3/4)+(1-s)(1/2).
```

Their gap is

```text
N_m(s)-Q_m(s)
= (3/2)s+(1-s)(1/2-r) > 0.
```

Every later finite quit either occurs after absorption or joins `o,h` at date
one; the stipulated strict inequalities keep those values below the Never
value.  Hence Never is genuinely the cap, not merely one tested deviation.
Since the prescribed law of `m` quits at zero with probability `p`,

```text
d_m(s)=p(N_m(s)-Q_m(s)),
(d_m(lambda)-d_m(0))/lambda=p(1+r) -> 1/2.
```

Thus the second limiting column is exactly
`(-1/2,1/2,0,0)`, flat, and its full replacement gives `o` own debt zero.
The first column remains `(1/4,-1/4,0,0)` with `m` full-replacement debt zero.
Both inactive coordinates have zero tangent entry.

With `lambda_n=1/(n+2)`, the remaining structure audit is complete:

- `scale_pos`, `scale_le_one`, and `scale_tendsto_zero` hold;
- the source semantic pairs converge to the literal `lambda=0` profile, so
  `base_mem` holds;
- the base debt vector is `(1/2,1/4,0,0)`, hence `base_positive` and support
  exactly `{o,m}` hold;
- source total debt is identically `3/4`, so the excess-over-scale limit is
  zero;
- both normalized replacement chords converge to the displayed columns;
- both replacement-own debts are identically zero, hence satisfy the squared
  scale and half-source-debt tolerance simultaneously; and
- inactive-coordinate nonnegativity holds with equality.

No additional hidden field remains in the declared tangent-family structure.
The old paragraph above saying that compatible replacement rays were not
supplied is superseded by this addendum.  Global `base_minimum` is still
unproved and remains decisive: without it this is not an inhabitant of the
positive-minimum tangent-family interface and does not challenge the full
frontier-to-return producer.
