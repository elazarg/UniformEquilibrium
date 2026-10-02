# Full Centered Motion and Homogeneous Dispatch Review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: Section 58.16, Proposition 71. I independently checked the
full-coordinate compactness, derivative orientation, finite-variation
selection, ambient homogeneous signs, production-normal support, and the
exact use of Proposition 63. This is ordinary mathematics, not Lean-checked.

## Verdict

**Proposition 71 is VALID ordinary mathematics as stated.** Source-centering
removes the outside-coordinate compactness gap in Proposition 70. In the
finite-full-variation arm it produces a full, rather than merely principal,
homogeneous simplex witness. Under `(N61)`, the independently reviewed
Proposition 63 dispatches that witness because its support consists of
production-normal owners. Thus the infinite normalized-horizon survivor in a
residual-hard counterexample must have unbounded normalized full-payoff
variation.

The normalization remains a binding limitation: the result does not give a
positive lower bound on unscaled variation, a returned payoff, or membership
of the radial path in the checked Simon carrier.

## 1. Full-coordinate compactness after source-centering

On the triangular prefixes, set

```text
w_l(t_(l,m)) = [X_(l,m)-X_(l,0)]/q_l,
dt_(l,m) = Q_(l,m)/q_l.
```

The exact one-edge motion bound gives, in every ambient coordinate,

```text
|X_(l,m+1)-X_(l,m)| <= 2M Q_(l,m).
```

Hence each affine segment of `w_l` has slope bounded by `2M`, independently
of `l`, the coordinate, and whether that coordinate ever becomes active.
Since `w_l(0)=0`, the paths are also uniformly bounded on every compact
normalized-time interval. Arzela--Ascoli and a finite-coordinate diagonal
extraction therefore yield a locally absolutely continuous full path `w`.
This is precisely the compactness unavailable for the uncentered radial
coordinates of Proposition 70.

The variation of the affine interpolant is exactly

```text
sum_m ||X_(l,m+1)-X_(l,m)||/q_l
```

over the corresponding exact prefix. Lower semicontinuity under local uniform
convergence therefore transfers every fixed lower bound on `Var(w;[0,T])` to
the original normalized exact blocks.

## 2. Derivative identity and its sign

Bellman equality on a row of absorption `Q` and conditional absorbing delivery
`D` is

```text
X_m = (1-Q)X_(m+1) + QD.
```

Thus the slope of the centered interpolation is

```text
(X_(m+1)-X_m)/Q = X_(m+1)-D.
```

Across a fixed normalized horizon, the source convergence and the one-edge
motion bound imply `X_(l,m+1)->b` uniformly. Proposition 70's collision
estimate makes the nonsingleton fraction of `D` vanish, while the singleton
owner distribution converges weak-star to `mu`. Passing to distributions gives

```text
w_i' = b_i - sum_(j in A) mu_j r_i({j})
```

in every coordinate, with the sign claimed in `(N112)`. No active-coordinate
anchoring is used in this passage.

## 3. Finite variation gives a full homogeneous witness

If the full variation is finite, local absolute continuity gives

```text
integral_0^infinity ||b-sum_j mu_j(t)r({j})|| dt < infinity.
```

For a nonnegative integrable function there are arbitrarily late Lebesgue
points at which its value tends to zero. Choose such points inside the
full-measure set where the derivative identity holds. Compactness of the
finite simplex permits `mu(t_n)->mu_*`; continuity then gives the identity in
all ambient coordinates

```text
b_i = sum_j mu*_j r_i({j}).
```

The canonical limiting endpoint-Nash inequality is `r_i({i})<=b_i` for every
player. Therefore, for the full normalized singleton matrix
`M_(i,j)=r_i({j})-r_i({i})`,

```text
(M mu*)_i = b_i-r_i({i}) >= 0.
```

The vector is supported on `A`; if `mu*_i>0`, Proposition 70 pins
`b_i=r_i({i})`. Hence `mu*_i(M mu*)_i=0`. This is a full ambient homogeneous
simplex solution, not only the principal kernel from Proposition 70.

## 4. Exact use of the production-normal dispatch

Proposition 70 proves every owner in `A` production-normal, so every positive
coordinate of `mu_*` is production-normal. Proposition 63, independently
audited in
[`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_24.md`](CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_24.md),
has exactly this static hypothesis under `(N61)`:

- a nonvertex full homogeneous witness restricts to the recursive normal core
  and contradicts `not HasHomogeneousSimplexSolution(normalPlayerMatrix M)`;
- a vertex is a production-normal no-harm singleton owner and the checked
  `exists_uniformEquilibriumPayoff_of_normalNoHarmSingletonOwner`
  (`UniformEquilibrium/Quitting/Classification/LCP/ProjectiveQBarBehavioralDecoder.lean`)
  supplies an unrestricted uniform-equilibrium payoff.

Thus no additional packet identity is needed at the limiting stage. The
support normality supplied by Proposition 70 is exactly what Proposition 63
uses.

## 5. Remaining obligation

Arm (a) controls variation after division by the vanishing record scale
`q_l`. For a selected exact prefix,

```text
unscaled variation = q_l * normalized variation.
```

Arbitrary divergence of the limiting normalized variation does not by itself
provide horizons whose variation grows as fast as `1/q_l`. Consequently the
argument does not yet produce a positive unscaled Simon excursion, a payoff
near-return, or a common `QuittingSimonFiniteOrbitCarrier`. The next producer
must relate excursion growth to the record scale, or turn repeated radial
excursions into an unscaled return by another chronological mechanism.
