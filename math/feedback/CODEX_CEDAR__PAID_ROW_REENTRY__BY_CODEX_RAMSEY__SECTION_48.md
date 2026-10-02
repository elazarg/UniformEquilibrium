# Review of `CODEX_CEDAR__PAID_ROW_REENTRY`, Section 48

Reviewer: `CODEX_RAMSEY`

## Verdict

`VALID` with the stated exact-edge/aggregate-charge scope.

## Audit

For one exact Bellman edge, the relation is oriented from its tail `v` to its
current predecessor `x`.  Expanding the successor equation gives

```text
x_i-v_i=sum_(nonempty S) pi_p(S)*(r_i(S)-v_i).
```

The coalition probabilities sum to the literal root absorption charge.
Since both rewards and boxed tail coordinates lie in `[-M,M]`, every summand
is at least `-2M*pi_p(S)`, proving `(48.2)` with the stated sign.

A later relation path from `X` to `Y` is oriented in the same tail-to-current
direction, so its coordinate displacements telescope as

```text
sum_e (current(e)_k-tail(e)_k)=Y_k-X_k.
```

From `X_k=V_k+a` and `|Y_k-V_k|<=eta`, this sum is at most `eta-a<0`.
Hence at least one summand is negative.  Summing the one-edge lower bounds
gives

```text
-2M*sum_e A(e) <= Y_k-X_k <= eta-a,
```

and therefore `sum_e A(e)>=(a-eta)/(2M)`.  The observation that `a>0`
forces `M>0` is correct because both endpoints lie in the canonical box.

If `eta<=a/2`, the bound becomes `a/(4M)`.  Combining
`a>=mu_0/2` with `eta<=mu_0/4` yields `a-eta>=mu_0/4`, hence exactly
`mu_0/(8M)`.

The result prices only the aggregate literal charges of the later exact
edges.  It neither converts a behavioral paid-block hazard into relation
charge nor yields one later edge with fixed charge when the path length is
unbounded.  Section 48 states these limitations correctly.
