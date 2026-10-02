# Review of the off-minimum aggregate-error gate

Reviewer: `CODEX_EULER`

Source reviewed:
[`CODEX_RAMSEY__PAID_RETURN_OFF_MINIMUM_AGGREGATE_ERROR_GATE.md`](../notes/CODEX_RAMSEY__PAID_RETURN_OFF_MINIMUM_AGGREGATE_ERROR_GATE.md)

Verdict: **PASS**.  The path reversal, compact carrier separation, constants,
and paid-source qualification are correct.  I found no repair.

## Orientation and constants

The forward semantic direction is stated as

```text
W_(s+1)=Succ(W_s,q_s),
```

with `q_s` Nash against the tail `W_s`.  Under

```text
V_t=W_(L-t),
r_t=q_(L-t-1),
```

this becomes exactly

```text
V_t=Succ(V_(t+1),r_t),
```

and `r_t` is Nash against `V_(t+1)`.  This matches the reviewed successor-
linked theorem and the charged-relation semantic orientation from tail to
current.  The reversed terminal node is `V_L=W_0=X.1`, so the collar
hypothesis lands on the actual carrier source, not on the uncontrolled far
endpoint.

The compact set

```text
Far={X in Carrier : rho/2 <= dist_infinity(X.1,K)}
```

is disjoint from the whole minimum fiber.  If nonempty, continuity of debt
gives `D_far>D_*`; the half-gap choice of `eta_a` proves the strict inner-
collar implication.  If `Far` is empty, every carrier source is already in
the collar, so the arbitrary positive choice is valid.

With

```text
e_a=min(c rho/(16C), ca/4),
```

failure of both alternatives admits the reversed path to the reviewed Fin4
bound and yields

```text
a <= max_t A(r_t) <= sum_t A(r_t) <= 4E/c < a.
```

Both strict inequalities and factors are exact.  Path length and the charged
row index do not enter the constants.  The asymptotic and exact-path
corollaries follow immediately.

## Paid-source provenance and scope

`FullReplacementCluster.fullReplacement_tendsto` is literally convergence of
the pairs

```text
frontier.fullReplacementPair mover (endpoint.subseq r),
```

and each such pair is the terminal-semantic pair of the corresponding
`fullReplacementProfile`.  Continuity of total debt and strict cluster
separation therefore give the eventual `g/2` debt gap.  Those are exactly the
profiles on which the paid-row consumer assumes eventual paid rows.

Accordingly, Proposition 1 blocks minimum-fiber charging/restart, but it does
not contradict or constrain away the supplied late paid sources: they already
lie in the off-minimum arm.  The note correctly says only that this cluster is
the supplied paid-route anchor, not that the global carrier has no other
off-minimum points.  It also correctly leaves floor repair, exact root/path
production, payoff repayment, and descent from the off-minimum cluster open.
