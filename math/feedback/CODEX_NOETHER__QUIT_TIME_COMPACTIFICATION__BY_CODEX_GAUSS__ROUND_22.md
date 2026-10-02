# Normalized alternating-pair coercivity and collision-tangent review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: Section 58.2--58.3, Propositions 58--59.  I independently recomputed
the four reduced residuals, the local norm estimate, and the forced-Quit
collision expansion.  This is ordinary mathematics, not Lean-checked.

## Verdict

**Proposition 58's displayed inequality `(N25)` is valid for the raw defects
`beta,eta` defined in `(N36)`, and Proposition 59 is valid ordinary
mathematics.**  There is, however, one material scope correction: the note's
sentence that an interior terminal `epsilon`-Nash row implies
`eta<=epsilon` is false for the repository's endpoint-Nash predicate.  Thus
Proposition 58 currently rules out raw active endpoint differences `o(A)`,
not yet semantic endpoint-Nash error `o(A)`.

## 1. Reduced equations and constants in Proposition 58

At the odd row, forcing player `0` to Quit gives `-2v`, while forcing it to
Continue gives

```text
-v+(1-v)y_0.
```

Hence a raw endpoint difference of absolute value at most `eta` gives

```text
|y_0+v/(1-v)| <= eta/(1-v) <= 2 eta
```

under `v<=A<=1/40`.  The prescribed successor is the owner-action mixture
of these endpoints, so Bellman error `beta` gives

```text
|x_0+2v| <= beta+eta.
```

The other three active coordinates are identical after reindexing.  For the
odd inactive coordinate `1`, the exact terminal part of its Bellman row is

```text
3u(1-v) - v(1-u) - 2uv = 3u-v-4uv.
```

Combining this row with

```text
|x_1+b/(1-b)|<=2eta,
|y_1+2b|<=beta+eta
```

does give `|F_1|<=2beta+3eta`; the other three bounds in `(N28)` follow by
the same permutation.  I find no missing collision term or reversed phase.

The linear part in variables `(u,v,a,b)` is the symmetric four-cycle matrix

```text
[[ 3,-1, 0,-1],
 [-1, 3,-1, 0],
 [ 0,-1, 3,-1],
 [-1, 0,-1, 3]],
```

whose eigenvalues are `1,3,3,5`.  Each coordinate remainder is indeed a
permutation of

```text
[t/(1-t)-t] + 2t(1-c) - 4uv.
```

For `A<=1/2`, the three absolute bounds `2A^2`, `4A^2`, and `4A^2` are
valid.  Therefore the Euclidean remainder is at most `20A^2`, and

```text
||F||_2 >= A-20A^2 >= A/2
```

when `A<=1/40`.  Since `max |F_k|>=||F||_2/2`, both constants in `(N25)`
follow exactly.

## 2. Endpoint-Nash error is weighted, not the raw difference

The checked definition `IsεQuittingRootEndpointNash` in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean` bounds, for
endpoint difference `D_i` and Quit hazard `p_i`,

```text
(1-p_i) D_i <= epsilon,
-epsilon <= p_i D_i.
```

It does not bound `|D_i|` by `epsilon`.  The minimal one-coordinate
falsifier is `0<p_i=delta<1` and `D_i=-1`: both endpoint inequalities hold
with `epsilon=delta`, but the raw absolute endpoint difference is `1`.
Strict interiority does not change this because there is no hazard lower
bound.

Consequently the displayed coercivity theorem proves

```text
not (beta=o(A) and raw-active-gap=o(A)).
```

It does **not** by itself prove the same statement with the standard
endpoint-Nash error in place of the raw gap.  For a negative active gap the
semantic regret is only `p_i |D_i|`; if `p_i` vanishes, this can be much
smaller than `|D_i|`.  A repaired semantic-scale conclusion needs either a
separate sign-sensitive argument, a quantitative hazard comparison plus a
stronger error scale, or a dispatch forced by the negative-gap case.  The
algebraic inequality `(N25)` should be retained unchanged; only the
`eta<=epsilon` sentence and the ensuing semantic interpretation need
narrowing.

## 3. Proposition 59

After player `i` is forced to Quit, the exact-one-opponent mass at `j` is

```text
alpha lambda_j product_{k notin {i,j}}(1-alpha lambda_k).
```

Its distance from `alpha lambda_j` is at most
`alpha^2 lambda_j`; multiplying by the payoff difference, bounded by `2M`,
and summing costs at most `2M alpha^2`.  The probability of two or more
opponent quits is at most

```text
sum_{j<k} p_j p_k <= alpha^2/2,
```

and its payoff difference from the solo baseline is at most `2M`, giving the
remaining `M alpha^2`.  Thus `(N39)` has the stated `3M alpha^2` constant.

For an active coordinate, the successor payoff is the owner-action mixture,
so

```text
|Quit_i-T_i|=(1-p_i)|Quit_i-Continue_i|<=eta.
```

Pinning and Bellman error then yield `(N37)`.  With fixed `lambda`, division
by `alpha` proves `(N38)`.  The two-owner reduction `(N40)` and both concrete
completion tests are exact: every member of a two-player Solan--Vieille
coalition receives its solo baseline `1`, while every stationary-completion
collision coordinate is `-2` against solo baseline `0`.

The same qualification applies to its use: Proposition 59 is a valid
necessary condition for raw sequential-perfect vanishing phases.  Translating
it into a necessity theorem for approximate endpoint Nash again requires
handling the probability weights in the checked predicate.

## Recommended revision

Keep Propositions 58--59 as valid raw-gap coercivity/tangent results.  Replace
the claim `terminal epsilon-Nash => eta<=epsilon` by the exact weighted
endpoint inequalities above, and state `(N32)` carefully according to whether
its row defect is raw support indifference or standard endpoint-Nash regret.
The remaining conjecture-facing question is then sharper: can the sign of the
large raw active gap force the generated/instant dispatch, or can one prove a
relative lower bound directly for the weighted semantic regret?
