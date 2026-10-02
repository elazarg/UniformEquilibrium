# Review of Propositions 87--88 by `CODEX_GAUSS`

Reviewed note: [`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md), Sections 67--68.

## Claims checked

- Proposition 87 decodes a zero-target, nonnegative-floor physical lift into
  a clean negative joined hyperedge: every opponent-only subcoalition in its
  down-set is payoff-zero.
- Proposition 88 gives the exact opponent-only deficit/excess ledger for an
  arbitrary supplied returned exact Nash--Bellman block, together with the
  separate joined-coalition ledger at active Quit coordinates.

Both are claims in ordinary mathematics.  I did not run Lean and assign no
`L`, `A`, or `C` seal.

## Verdict

**VALID in the stated scope.**  I found no mathematical objection.  The two
results fit together sharply: Proposition 87 explains why a frozen
zero-target row can fail for support-sign reasons, while Proposition 88 shows
the exact survival-normalized balance by which a moving returned block can
repair that failure.  Neither proposition produces a block.

## Proposition 87

Fix active owner `i`.  The checked
`quittingRootQuitPayoff_eq_zero_of_zeroTargetLift`
(`UniformEquilibrium/Quitting/Boundary/Repair/TerminalFunding/SupportNecessity.lean`)
gives forced-Quit endpoint zero.  Active derivative equality gives equality
of the two endpoints, so forced Continue is also zero.

Under the hypotheses, every terminal term in the forced-Continue expectation
is nonnegative, and its empty-opponent term is `c z_i` with `c>0` and
`z_i>=floor_i>=0`.  Interiority on `S` gives positive probability to every
exact coalition `U subset S\{i}`, including the empty coalition.  A finite
nonnegative sum can vanish only termwise.  Hence

```text
z_i=0,
r_i(U)=0 for every nonempty U subset S\{i}.          (R87.1)
```

In the forced-Quit expectation, the positive-probability empty-opponent term
is the strictly positive solo reward.  Since the whole expectation is zero,
some nonempty `T subset S\{i}` has `r_i(T union {i})<0`.  Equation (R87.1)
makes its entire nonempty opponent-only down-set zero, exactly the claimed
clean hyperedge.

The two-player sharpness test is consistent simultaneously for both owners:
choose

```text
p_j=s_i/(s_i+a_i),
p_i=s_j/(s_j+a_j),
```

with continuation and floor zero.  Each forced-Continue endpoint is zero and
each forced-Quit endpoint is the convex combination of `s_owner` and
`-a_owner` with the displayed zero-expectation hazard.

For `SolanVieilleBoundary.boundaryReward`, all opponent-only rewards are
nonnegative and the floor is zero.  The only negative owner-containing row is
the grand coalition, but the same-pair singleton subcoalition pays `4`.
Thus no clean hyperedge exists, reproducing Proposition 86 without solving
the product equations.

## Proposition 88

At phase `t`, exact endpoint Nash says both pure endpoints are at most the
Bellman successor mixture `X_t`.  Since player `i`'s prescribed Continue
probability is positive, its forced-Continue endpoint must equal `X_t`: if it
were strictly smaller, the other endpoint would have to lie strictly above
the convex mixture.  Expanding forced Continue over the opponent law gives

```text
X_t = c_t X_(t+1) + sum_(U nonempty) mu_t(U) r_i(U). (R88.1)
```

Because `sum_(U nonempty)mu_t(U)=1-c_t`, rearrangement yields

```text
c_t(X_(t+1)-X_t)
  = sum_(U nonempty)mu_t(U)(X_t-r_i(U))
  = D_t-E_t.                                         (R88.2)
```

Every opponent has positive Continue probability, so `c_t>0`.  Dividing
(R88.2) by `c_t` and summing around a returned block telescopes the payoff
increments and proves

```text
sum_t D_t/c_t = sum_t E_t/c_t.
```

If player `i` also has positive Quit probability, the same convex-mixture
argument pins its forced-Quit endpoint to `X_t`; expansion gives the separate
joined-coalition equality.  This correctly keeps opponent-only target motion
distinct from active joined-collision balance.

### Solan--Vieille phase check

Write `a=periodTwoParameter`, `b=periodTwoSecondary`.  At the odd phase for
player `0`, only opponent `2` is active, so

```text
c_odd=b,
X_odd=1,
X_even=1/b,
(D_odd-E_odd)/c_odd=1/b-1.
```

At the even phase, opponents `1,3` have joint Continue probability `ab`, and
the successor returns to `1`.  Therefore

```text
c_even=ab,
(D_even-E_even)/c_even=1-1/b.
```

The normalized ledgers cancel exactly.  Direct inspection also confirms the
sign explanation: at odd phase the cross-pair singleton `{2}` pays player
`0` zero, producing deficit; at even phase the same-pair singleton `{1}`
pays `4`, producing the compensating excess (with the other opponent-only
rows included in the exact net identity).

At odd phase, active player `0` receives `1` both at `{0}` and `{0,2}`, equal
to `X_odd,0`; the joined ledger vanishes termwise.  The same holds for player
`2`, and symmetrically for active players `1,3` in the even phase.  Every
actual phase coordinate is `1`, `1/a`, or `1/b`, hence at least `1`; no
negative continuation is transported.

## Exact remaining obligation

The ledger turns moving-target funding into a finite-cycle feasibility
problem, but it is only necessary data for a supplied return.  A universal
positive producer must obtain the compensating `E/c` mass at later reached
sources while also satisfying all joined-coalition and inactive endpoint
inequalities.  A negative route would need a single separator that survives
arbitrary block length, simultaneous quitters, and changing supports; failure
of one two-phase ansatz is not enough.
