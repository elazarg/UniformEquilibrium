# Review of `CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION`

Reviewer: `CODEX_RAMSEY`

Status: `PROPOSITION 8 VALID; POSITIVE-COLLISION SOURCE SHARPENED`

## Claim checked

I checked Proposition 8's one-row assertion: if every player has a
Continue-over-Quit endpoint gap at least `a>0` and

```text
g_i <= eta * (1-O_i)
```

for every player, then all Quit marginals vanish when
`eta<a/(|I|-1)`.

The proof is valid.  With `p_i` the prescribed Quit marginal, affine mixing
gives `g_i>=a*p_i`.  The union bound gives
`1-O_i<=sum_{j!=i}p_j`.  Summing produces

```text
a * sum_i p_i <= eta*(|I|-1)*sum_i p_i,
```

so strict inequality of the coefficients forces every nonnegative `p_i` to
be zero.  No independence estimate stronger than the union bound is used,
and the one-player boundary is correctly separated.

## Source-specific sharpening

The notebook's final proposed check asks for the second hazard label and its
action gap at a clock-carrying atom row.  In the positive-target collision
orientation, the checked reached-row localization already gives a sharper
answer.

Let `o` be the observer, `T` the fixed collision terminal, and `lower>0` the
stored stage-mass floor.  At every selected reached row:

1. `o` Quits surely by the pure-time construction;
2. choose any fixed `b in T\{o}`; factorization of stage mass gives
   `rootMass(T)>=lower`, hence `q_b(Quit)>=lower`;
3. reached-row localization fixes some `i!=o` with global legal gain at least
   `gamma>0`.

Thus these literal roots already carry two fixed persistent labels in the
strong pointwise form `q_o=1`, `q_b>=lower`.  Joint survival is zero at every
row; deleting `o` leaves survival at most `(1-lower)^K` over `K` rows; deleting
any other player leaves the sure observer.

However, the selected player's diagonal gap is at least `gamma` for **every**
artificial diagonal continuation.  Since `o` is a sure opponent of `i`, both
pure endpoints and the prescribed mixture for `i` are independent of the
tail.  The global gain is `liveMass*g_i`, with `liveMass<=1`, so `g_i>=gamma`.
The normalized condition would require `g_i<=eta`, because
`1-O_i=1`.  It therefore fails for every `eta<gamma` without needing
Proposition 8's all-player strict-Continue hypothesis.

This means the positive-collision branch is not waiting for a second-label
clock calculation.  Its literal clocks are already complete, while the
normalized-incentive route is blocked by a fixed tail-independent defect on
one other player.

## Exact artificial-prefix modulus

The same sure-observer rows have a useful complementary property.  For any
two successor semantic pairs `S,T`, prefixing by such a root `q` makes the
entire prescribed vector and every nonobserver cap coordinate identical.
Only the observer cap can differ, by at most

```text
O_o(q) * |S.B_o-T.B_o|.
```

The collision event has root mass at least `lower` and contains an outsider,
so `O_o(q)<=1-lower`.  A word of `K` selected roots therefore forgets every
terminal annotation except the observer cap, and contracts that last
difference by `(1-lower)^K`.  This uses exact prefix maps on the same literal
two-label roots; it does not identify equal semantic states with equal
conditioned ports.

There is nevertheless a head obstruction: every such word starts with
candidate debt at least `gamma` in the selected player's coordinate,
independently of its terminal annotation.  Hence it cannot itself be the
small-initial-debt block at accuracy below `gamma`.

The resulting source-facing problem is more specific than the notebook's
current last paragraph:

> Construct a small-debt entry bridge into the positive-collision word, with
> its prescribed/direct seam accounts inside the every-suffix budget.

The word after entry already supplies the two clocks and an explicit
geometric tail-forgetting modulus.  The proof and quantitative root-repair
floor are recorded in
[`CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`](../notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md).

## Scope

This review does not address the three open rectangle orientations or the
prescribed-atom branch.  It supplies no entry bridge and hence no full
chronological certificate.
