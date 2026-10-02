# Review of `SHADOW.md`

## Claim reviewed

The note separates the proposed shadowing construction into three levels and
claims:

1. the current `QuittingBudgetStablePacketSystem` interface is inhabited by a
   universal stationary self-loop and therefore does not encode attachment to
   the supplied tangent source;
2. an actual all-behavior implementation of a coordinatewise small-debt seed
   must pay a quantitative payoff/cap error controlled by the positive minimum
   debt; and
3. a source-faithful packet chain carrying repeated positive total-debt slope
   or zero-coordinate support entry must contain cumulative internal debt
   decrease.

I checked the relevant declarations in:

* `UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean`:
  `QuittingBudgetStablePacketData` and `QuittingBudgetStablePacketSystem`;
* `MathUE/SublinearCostSchedule.lean`:
  `IsOperationallySublinearCost` and `BudgetedDivergentCostSchedule`;
* `UniformEquilibrium/Diagnostics/Quitting/PositiveMinimumSeedSeamBarrier.lean`:
  the direct semantic-seam bounds; and
* `UniformEquilibrium/Quitting/Stationary/Root.lean`:
  `quittingRootThenContinuationProfile_stationary` and the stationary payoff
  fixed-point identity.

## Verdict

The central mathematics is sound and useful, but the current note is not
export-ready. It contains one genuine specification audit and two clean,
formalizable conditional inequalities. It does **not** prove that a richer
source-faithful shadowing producer cannot follow from the tangent entrance, and
it does **not** yet construct an admissible payoff return. Those two
overstatements should be corrected.

## Valid results

### 1. The packet-system interface is provenance-vacuous

The all-half stationary construction works. For the root with every Quit
probability equal to `1/2`, let `z` be the complete terminal semantic pair of
its stationary profile. The stationary profile is literally its root followed
by itself, so the complete semantic prefix identity gives `z = T_q z`, including
the unrestricted cap coordinates. Taking a singleton port, constant
annotation, zero endpoint and availability costs, radius one, and
`kappa = 1/2` satisfies every field of
`QuittingBudgetStablePacketSystem` for Fin 4. A reward bound `R` gives prescribed
payoff bound `R` and debt bound `2R`.

This is a substantive interface defect: the structure has no actual profile,
marked atom, tangent-family source, or equation identifying its annotation with
the supplied source semantics. A theorem producing only this structure from
the tangent entrance could ignore the entrance completely.

Two bullets in the note should be reclassified. Positive successor reach and
the `1/16` mass of a chosen coalition are true facts about the stationary
example, but they are not fields of the inspected packet-system structure.
Their absence strengthens the specification diagnosis; they should not be
described as fields being verified.

### 2. The Tier-II implementation inequality is correct

If an artificial pair `z = (u,b)` has `b_i-u_i <= eta`, while an actual profile
obeys

```text
U_i(sigma) >= u_i-alpha_i,
B_i(sigma) <= b_i+beta_i,
```

then

```text
d_i(sigma) <= eta + alpha_i + beta_i.
```

For Fin 4, global minimum debt therefore gives

```text
D_* <= 4 eta + sum_i (alpha_i+beta_i).
```

The two symmetric specializations and the lower bound
`delta >= (D_*-4 eta)/8` are correct. This is a useful extension of the checked
direct-seam barrier to an arbitrary actual implementation with one-sided
all-behavior payoff and cap estimates.

### 3. The aggregate telescope is correct under its stated drift data

The debt functional is 1-Lipschitz in the coordinatewise payoff/cap `L1`
metric. Hence `total_endpoint` gives

```text
|D(e_n)-D(x_(n+1))| <= 4 omega(h_n)
```

in Fin 4. If a selected compatible chain also carries internal candidates
`m_n` with

```text
D(m_n)-D(x_n) >= c h_n-rho_n,
```

then, for `R_n = (D(m_n)-D(e_n))_+`, the displayed telescope

```text
sum_(n<N) R_n >=
  c sum_(n<N) h_n - sum_(n<N) rho_n
  - 4M - 4 sum_(n<N) omega(h_n)
```

is correct when every coordinate debt is between zero and `M`. The operational
sublinearity API supplies a chosen schedule with divergent total scale and
summable combined cost, so the right-hand side diverges when `rho` is
summable. The coordinate version has the corresponding `-M` and `-omega`
terms and is also correct.

These are worthwhile generic no-go/telescope lemmas: repeated positive drift
cannot be absorbed by a summable endpoint seam while bounded debt is preserved.

## Required corrections

### 1. Preserve the conditional hypotheses

The current packet structure does not itself provide the marked internal
candidate `m_n`, the positive-drift inequality, or the summable residual
`rho_n`. These are extra source-faithful inputs. The telescope proves a theorem
of the form:

```text
compatible packet chain + marked drift data
  -> divergent cumulative internal debt decrease.
```

It is not an unconditional theorem about every packet system.

### 2. Replace “does not follow” by a specification statement

No countermodel or logical nonimplication is proved. The analysis shows that:

* the **current formal Tier-I target** is too weak and is unrelated to the
  tangent entrance; and
* any **genuine source-faithful strengthening** with the stated drift data must
  also produce cumulative internal debt decrease.

It remains possible that the tangent entrance implies exactly such a stronger
producer; proving that would be the desired breakthrough. The conclusion
should therefore say “is not supplied by the presently represented entrance
and target interface,” rather than “does not follow from the entrance.”

### 3. Do not call the telescope an admissible return

The quantity `R_n` is a positive drop in total semantic debt between an
internal marked candidate and the packet endpoint. Exact prefix identities
make this an internal exact-Bellman **debt drain**. The argument does not show
that this drain is:

* positive prescribed-payoff charge;
* an admissible punishment-floor edge;
* a near-return to one fixed semantic pair or law; or
* directly consumable by the existing charged-return compiler.

Use “cumulative internal exact-Bellman debt drain” unless a separate bridge to
one of those consumers is supplied.

### 4. State the sublinearity contradiction along the selected schedule

`IsOperationallySublinearCost` gives arbitrarily small favorable scales and,
through the schedule theorem, a vanishing nonsummable scale sequence with
summable cost. It does not assert a pointwise `omega(h)=o(h)` estimate at every
small `h`. The claimed impossibility of direct reprojection is an aggregate
contradiction along the selected schedule, not a pointwise contradiction for
all scales.

## Recommended retained result

After correction, the note should retain three named targets:

1. a universal-inhabitation theorem for the present packet-system interface;
2. the Fin4 all-behavior seed-implementation inequality; and
3. total and coordinate packet-drift telescope theorems.

Together they sharpen the real producer obligation: a meaningful shadowing
theorem must attach packets to the supplied actual source and must explain the
forced internal debt drains—by an admissible return, a renewable finite-rank
transition, or a direct terminal consumer. That is important frontier
clarification, but it is not itself the missing producer.
