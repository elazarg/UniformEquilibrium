# Cross-Face Mass Pinning Review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: Section 58.22, Proposition 77. I independently checked the convex
mass split, conditional-absorption normalization, Bellman seam orientation,
collision decomposition, and the precise returned-block scope. This is
ordinary mathematics, not Lean-checked.

## Verdict

**Proposition 77 is VALID ordinary mathematics as stated.** A vanishing amount
of cross-face singleton mass cannot cancel the strict old-face separator. Any
diffuse exact Bellman block returning to `b` up to `o(absorption)` must carry a
fixed positive fraction of its conditional singleton-owner law outside `A`.

This is a necessary first-absorption statement. It does not construct the
cross-face phase or verify endpoint Nash and punishment floors for it.

## 1. Convex owner-mass estimate

For `g_j=c-Me_j=b-r({j})`, Proposition 76 gives
`ell dot g_j>=kappa` on every old-face vertex `j in A`. For an omitted owner,
`ell dot g_j>=-K_out` by the definition of `K_out`. If
`e=sum_(j outside A)mu_j`, linearity gives

```text
ell dot(c-Mmu)
 = sum_j mu_j ell dot g_j
 >= (1-e)kappa-e K_out
 = kappa-(kappa+K_out)e.
```

Rearrangement gives `(N156)`. Since `kappa>0` and `K_out>=0`, the stated
`theta` is positive. If the singleton mixture equals `b`, its drift is zero
and the lower bound is exactly `theta`.

## 2. Bellman seam orientation

For a finite block with total absorption probability `a>0`, conditional
absorbing delivery `D`, start `x^0`, and surviving successor `x^1`, exact
Bellman recursion is

```text
x^0=(1-a)x^1+aD.
```

Therefore

```text
D-x^1=(x^0-x^1)/a.
```

The orientation in the proof is correct. The seam hypothesis and
`x_l^1->b` imply `D_l->b`.

## 3. Conditional collision decomposition

Let `zeta_l` be the conditional probability that the first absorbing
coalition is nonsingleton. Once `zeta_l<1`, the remaining conditional law
defines a probability vector `mu_l` on singleton owners and

```text
D_l=(1-zeta_l) sum_j mu_(l,j)r({j})
       +zeta_l R_l^collision.
```

The finite reward table uniformly bounds every conditional collision
delivery. Since `zeta_l->0` and `D_l->b`, the singleton mixture converges to
`b`. Hence

```text
c-Mmu_l=b-sum_j mu_(l,j)r({j})->0.
```

Applying `(N156)` with the scalar drift itself, or with its vanishing absolute
value, gives the claimed liminf outside mass at least `theta`.

## 4. Scope

No probability is lost to Never after conditioning on block absorption; the
surviving outcome is exactly `x_l^1` in the Bellman identity. The result needs
neither endpoint Nash nor a floor to derive its mass lower bound, but those
semantic fields remain essential and unconstructed for any proposed
cross-face producer. Material collision mass and horizons lacking an
`o(a_l)` endpoint seam remain explicit escape routes.
