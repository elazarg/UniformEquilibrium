# Strict Halfspace Radial Drift Review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: Section 58.21, Proposition 76. I independently checked closest-point
separation, the path and first-exit orientations, the fixed-horizon exact
prefix transfer, and the stated support/scale exceptions. This is ordinary
mathematics, not Lean-checked.

## Verdict

**Proposition 76 is VALID ordinary mathematics as stated.** The old-face
radial motion lies in one strict affine halfspace, not merely outside a ball
around zero. Hence it has a fixed linear Lyapunov coordinate and cannot
oscillate or return while its limiting owner control remains on `A`.

The fixed-horizon transfer is also correct. It does not cover horizons growing
with the record index, exact blocks with material cross-face owner mass, or
nonnegligible atoms/collisions.

## 1. Closest-point separation

The drift set

```text
D={c-Mmu | mu in Simplex(A)}
```

is the compact convex affine image of a finite simplex. Proposition 73 proves
`0 notin D`. Let `d_*` minimize Euclidean norm on `D`. Then `d_*!=0` and, for
every `d in D`, convexity keeps
`d_*+t(d-d_*)` in `D` for `0<=t<=1`. The right derivative at `t=0` of its
squared norm is nonnegative, giving

```text
d_* dot (d-d_*)>=0.
```

Thus with `ell=d_*/||d_*||` and `kappa=||d_*||>0`,

```text
ell dot d >= kappa
```

uniformly on `D`. The normalization and inequality in `(N148)` are exact.

## 2. Path orientation

Proposition 71 has the forward chronological derivative

```text
w'=c-Mmu(t).
```

Therefore for `0<=S<T`,

```text
ell dot [w(T)-w(S)]
 = integral_S^T ell dot [c-Mmu(t)] dt
 >= kappa(T-S).
```

The orientation in `(N149)` is correct. Equality of two distinct-time radial
points would contradict the strict positive right side, so no returned subarc
is possible. For the first-exit limit,
`u'=lambda(c-Mnu)` and `u(0)=0`; integration gives
`ell dot u(1)>=lambda*kappa`, also with the stated sign.

## 3. Exact fixed-horizon transfer

Fix `T>0` before selecting the triangular record subsequence. The centered
exact interpolants converge uniformly to `w` on `[0,T+1]`. The first grid
crossing after normalized charge `T` overshoots by at most the mesh
`Phi_l->0`; their uniform Lipschitz bound makes the interpolated endpoint
error `o(1)`. Since

```text
ell dot w(T)>=kappa*T,
```

the exact chronology endpoints eventually satisfy

```text
ell dot [X_end-X_start]/q_l >= kappa*T/2.
```

This is `(N151)`. The same reasoning works for any fixed compact interval
`[S,T]`, after subtracting its source.

## 4. Scope

The halfspace is tied to the fixed active simplex `A`. A returned construction
must therefore leave this limiting support class, retain a nonvanishing
atom/collision term absent from the singleton drift set, or use horizons whose
growth is not controlled by the fixed-compact triangular convergence. The
result supplies no uniform estimate for such moving horizons and no literal
support-entry producer for the positive production-normal exit of Gauss
Proposition 53.
