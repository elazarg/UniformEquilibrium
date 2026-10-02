# Ballistic Full-Radial Escape Review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: Section 58.18, Proposition 73. I independently checked the integrated
motion identity, compact affine separation, the production-normal support
hypothesis in Proposition 63, the active-face sign, and the two escape modes.
This is ordinary mathematics, not Lean-checked.

## Verdict

**Proposition 73 is VALID ordinary mathematics as stated.** In fact it gives
the qualitative unboundedness of Proposition 72 directly at the limiting
radial-path level: under `(N61)`, the full radial path escapes at a uniform
linear rate. The exact residual fork is also correct.

The remaining issue is still the triangular scale adapter. A fixed-time
ballistic bound for the limit path does not by itself permit choosing
`T_l` of order `1/q_l` while retaining approximation by the record-`l` exact
prefix. Thus the theorem does not yet give positive unscaled displacement.

## 1. Integrated identity

Let `s_i=r_i({i})`, `c=b-s`, and use
`M_(i,j)=r_i({j})-s_i`. Since `mu(t)` is simplex-valued on `A` almost
everywhere, its time average `barMu_T` is again in `Simplex(A)`. Integrating
Proposition 71's full-coordinate differential identity gives

```text
w(T)/T
 = b-sum_j barMu_(T,j)r({j})
 = (b-s)-sum_j barMu_(T,j)(r({j})-s)
 = c-M barMu_T.
```

The subtraction of `s` in the last step uses
`sum_j barMu_(T,j)=1`; the orientation in `(N130)` is correct.

## 2. Compact affine separation is strict

The simplex supported on finite `A` is compact, so

```text
delta=min_(nu in Simplex(A)) ||c-Mnu||
```

is attained. If `delta=0`, then some `nu` supported on `A` has `Mnu=c`.
The canonical endpoint-Nash limit gives `c>=0`. Moreover Proposition 70 pins
`c_i=0` for every `i in A`. Therefore

```text
Mnu>=0,
nu_i>0 -> i in A -> (Mnu)_i=c_i=0.
```

This is a full ambient homogeneous simplex witness, not merely a principal
one. Every support owner lies in the production-normal set `A`. Proposition
63 has exactly this support hypothesis and, under `(N61)`, dispatches both
the nonvertex normal-core case and the production-normal no-harm vertex case.
Hence zero is absent from the compact affine image, `delta>0`, and

```text
||w(T)|| = T ||c-M barMu_T|| >= delta T
```

for every `T>0`.

## 3. Active-face sign and exhaustive fork

Along any sequence `T_k->infinity`, compactness gives a subsequence with
`barMu_(T_k)->nu`. Then

```text
w(T_k)/T_k -> d=c-Mnu,
||d||>=delta.
```

For `i in A`, the two radial constructions satisfy

```text
w_i(T)=v_i(T)-v_i(0).
```

Since `v_i(T)>=0`, division by `T` gives `d_i>=0`. Also `c_i=0` on `A`, so

```text
d_i=-(M_A nu)_i >=0.
```

Either at least one of these active-face coordinates is positive, equivalently
some principal residual is strictly negative, or they all vanish. In the
second case `M_A nu=0`; since `d` is nonzero, at least one omitted ambient
coordinate carries nonzero drift. The alternatives are mutually exclusive
and exhaustive along the chosen average-control subsequence.

## 4. Exact remaining scope

The result is a quantitative normalized-motion theorem. Proposition 69's
triangular compactness approximates each fixed normalized horizon after
passing sufficiently far down the record sequence. It supplies no uniform
rate relating that required record index to the horizon. Consequently one
cannot yet set `T_l` proportional to `1/q_l` and infer an unscaled displacement
`q_l||w_l(T_l)||` bounded below. A conjecture-closing next step must obtain
such a rate, a face-descent producer from the fork `(N132)`, or a different
chronological return/consumer.
