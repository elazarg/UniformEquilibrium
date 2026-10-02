# Bounded Radial Oscillation and Returned-Block Review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: Section 58.17, Proposition 72. I independently checked eventual
production-normal support, the compact recurrence selection, the
variable-horizon triangular diagonal, raw-hazard versus absorption-charge
normalization, seam closure, and the exact hypotheses of the reviewed
returned-block obstruction. This is ordinary mathematics, not Lean-checked.

## Verdict

**Proposition 72 is VALID ordinary mathematics as stated.** Under the
residual-hard/no-uniform hypotheses, the full radial trajectory from
Proposition 71 cannot have bounded range. If it did, compact recurrence of its
integer samples would produce literal finite chronology segments whose
endpoint mismatch is `o(total hazard)`. Closing only the last seam gives the
production-normal-supported approximate returned blocks excluded by Gauss
Proposition 47 and Noether Proposition 63.

The proof needs a quantitative diagonal choice slightly stronger than merely
"mesh tends to zero": because the recurrence intervals have variable lengths
`T_k`, choose the approximating record so that `mesh_k*T_k->0` as well as
`q_(l_k)T_k->0`. This is available from the fixed-prefix convergence before
passing to the diagonal and is already covered by "sufficiently late" in the
proof. I found no mathematical objection.

## 1. Eventual support is production-normal

On the canonical hard tail, row absorption tends to zero. If player `i` has
positive Quit probability at arbitrarily late dates, take such a sequence.
Eventually `0<p_i<1`, so exact endpoint Nash makes Quit and Continue
indifferent. The forced-Quit payoff tends to `r_i({i})`, because every
opponent's Quit probability is bounded by the vanishing row absorption. The
row values tend to the canonical boundary `b`, hence

```text
b_i=r_i({i}).
```

The canonical punishment floor passes to the same limit and gives
`punishment_i<=b_i`; thus `i` is production-normal. Contrapositively, a
production-abnormal owner is active only finitely often. Finiteness of the
player set supplies one common cutoff, establishing `(N119)`.

## 2. Compact recurrence has the required orientation

If `w` is bounded, the integer samples `w(n)` lie in a compact
finite-dimensional set. A convergent subsequence, relabeled at strictly
increasing integers `n_k`, satisfies

```text
||w(n_(k+1))-w(n_k)|| -> 0.
```

The chronology segment is taken forward from the grid crossing near `n_k` to
the crossing near `n_(k+1)`. This matches the Bellman orientation: its final
successor payoff is the later radial point and is the only value replaced when
the block is closed.

There is no need for a uniform bound on
`T_k=n_(k+1)-n_k`. For each already selected finite interval, the triangular
record-prefix convergence allows an independently later record `l_k`.

## 3. Variable-horizon diagonal and hazard normalization

Choose `l_k` so late that, simultaneously,

```text
sup_[0,n_(k+1)] ||w_(l_k)-w|| -> 0,
mesh_k -> 0,
mesh_k*T_k -> 0,
q_(l_k)*T_k -> 0,
```

and the record date lies beyond the common cutoff in `(N119)`. All four
conditions are available because `T_k` and `n_(k+1)` are fixed when `l_k` is
chosen.

The normalized grid uses absorption probabilities `Q_m`, whereas Gauss
Proposition 47 uses raw one-stage hazards `h_m=sum_i p_(m,i)`. For a finite
player set and small product rows,

```text
0 <= h_m-Q_m <= C Q_m^2,
h_m <= C Q_m.
```

On the cut segment, therefore,

```text
sum_m (h_m-Q_m)/q_l
  <= C (max_m Q_m/q_l) (sum_m Q_m/q_l)
  = O(mesh_k*T_k) -> 0.
```

Grid-crossing errors are `O(mesh_k)`. It follows that the raw total hazard
`S_k` satisfies `S_k/q_(l_k)=T_k+o(1)`. Source-centering and uniform path
convergence give

```text
||X_start-X_end||/q_(l_k)
 <= ||w(n_k)-w(n_(k+1))||+o(1).
```

Since `T_k>=1`, the endpoint mismatch is `o(S_k)`. Also
`S_k~q_(l_k)T_k->0`.

## 4. Closing the seam has exactly the reviewed error scale

Retain every product row and every intermediate value from the literal exact
chronology segment. Replace only the final successor payoff `X_end` by the
initial source payoff `X_start`. Then:

- all nonfinal Bellman and endpoint-Nash rows remain exact;
- the final Bellman residual changes by at most the seam mismatch;
- forced Quit is independent of the successor tail, while forced Continue
  depends linearly on it with coefficient at most one;
- each of the two probability-weighted endpoint-regret functions in `(VH13)`
  is Lipschitz in that endpoint difference.

Thus, after summing over the fixed finite player set,

```text
B_k+E_k <= C ||X_start-X_end|| = o(S_k).
```

The phase values remain in the original bounded payoff box. Every positive
hazard owner lies in the fixed production-normal set by `(N119)`. The closed
blocks therefore meet exactly Corollary 49's hypotheses: `S_k->0`, bounded
values, production-normal support, and aggregate Bellman plus standard
probability-weighted endpoint regret `o(S_k)`. The returned-block telescope
and Proposition 63 give the claimed contradiction.

## 5. Exact remaining scope

The conclusion is stronger than unbounded variation: the full radial path
itself must leave every bounded set. It still concerns the payoff displacement
divided by the vanishing record charge. It supplies neither a positive
unscaled displacement nor a radial point in the checked Simon near-feasible
carrier. The next genuine obligation is therefore to control the direction
and rate of radial escape, or to convert it into an unscaled return/charged
consumer by another argument.
