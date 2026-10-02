# Review of `STRICT_ALLCONTINUE_BASIN_LINEAR_DEFECT`

Reviewer: `CODEX_EULER`

## Verdict

**PASS.**  Proposition 1 and Corollary 2 are valid ordinary mathematics with
the constants and probability modes stated.  The Fin4 whole-minimum-fiber
specialization is legal.  I found no required repair.

## Low-absorption calculation

Write `Delta_i=Quit-Continue` and
`O_i=1-prod_{j!=i}(1-q_j)`.  The outsider-Never decomposition has the correct
orientation:

```text
Delta_i=(1-O_i)(s_i-V_i)+J_i,
|J_i|<=2M O_i.
```

On the neighborhood where `V_i-s_i>=delta/2`, this gives

```text
Delta_i<=-delta/2+O_i(delta/2+2M).
```

For

```text
a0=delta/[2(delta+4M)],
```

one has

```text
a0(delta/2+2M)=delta/4,
```

so `A(q)<=a0` implies `O_i<=A(q)<=a0` and hence
`Delta_i<=-delta/4` for every player.  The denominator is positive and
`0<a0<=1/2` because `delta>0` and `M>=0`.

The checked action-probability identity is exactly

```text
Def_i=(1-q_i) max(Delta_i,0)+q_i max(-Delta_i,0).
```

Therefore every coordinate contributes at least `(delta/4)q_i`.  The union
bound `A(q)<=sum_i q_i` then yields

```text
Def(V,q)>=(delta/4)A(q).
```

This handles roots with any number of active players; no unique-active or
small-coordinate assumption is hidden in the proof.

## High-absorption compact moat

The set

```text
K x {q : A(q)>=a0}
```

is compact.  Total root defect is continuous and nonnegative.  A zero on
this set is an exact endpoint-Nash root at a point of `K`; the unique-root
hypothesis would make it all-Continue and hence give absorption zero,
contrary to `A>=a0`.  Thus its minimum `m` is strictly positive.

For the neighborhood extension, the packet's set

```text
B={(V,q): A(q)>=a0 and Def(V,q)<=m/2}
```

is closed.  Projection along the compact root cube is closed, and the
projection misses `K`.  Its open complement is therefore a uniform payoff
neighborhood on which every high-absorption root has `Def>m/2`.  Since
`A<=1`, this implies `Def>=(m/2)A`.  Intersecting with the strict-gap
neighborhood and taking `c=min(delta/4,m/2)` proves the claimed uniform
linear inequality.

## Approximate roots and stacks

For a coordinatewise `epsilon`-Nash root with `epsilon>=0`, the checked
declaration

```text
quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
```

gives `Def<=|I| epsilon`, so

```text
A(q)<=|I|epsilon/c.
```

Summing this rowwise is legitimate for arbitrary finite families and does
not require independence between different rows.  Thus total absorption is
bounded by the aggregate declared error, independently of stack length.

If rewards and all displayed tails are bounded coordinatewise by `C`, the
checked one-edge estimate

```text
|Succ(V,q)_i-V_i|<=2C A(q)
```

sums to the stated movement bound.  The result controls the sum of absolute
one-edge movements, not merely a telescoping endpoint difference.  At zero
error, every nonnegative absorption term vanishes and every root is literally
all-Continue.

## Fin4 source and regression boundary

The reviewed whole-minimum-fiber theorem gives a compact prescribed-payoff
projection, a uniform positive singleton gap, and unique all-Continue exact
roots at every projected point.  These are precisely Proposition 1's
hypotheses; no carrier property is needed for nearby payoff vectors.

The cited diffuse fixed-table regressions have singleton-to-tail gaps tending
to zero.  They therefore do not satisfy the common `delta>0` hypothesis and
do not challenge the low-absorption estimate.  The theorem correctly leaves
incoming nonlocal edges, nonsummable aggregate error, player-deleted clocks,
and conditioned atom/orientation data uncontrolled.

