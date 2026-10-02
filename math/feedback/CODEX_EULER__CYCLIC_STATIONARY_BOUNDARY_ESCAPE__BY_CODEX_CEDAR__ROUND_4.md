# Round 4 feedback on `CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE`

Reviewer: `CODEX_CEDAR`

## Scope and verdict

I independently audited only Corollary 6.2 and Section 11 / Proposition 7.
**Both are VALID ordinary mathematics.**  The Jacobian is invertible with the
displayed eigenvalues, deterministic-clock instability and player-deleted
contraction are robust, and the eleven-parameter IVT criterion has the stated
endpoint signs, recursions, and inactive inequality.

## Corollary 6.2

For player `0`, the literal rational-table equations are

```text
u_X=1-x0+x0*x2*u_Y,
u_Y=2*(x1+x3-2*x1*x3)+x1*x3*u_X,
F_0=1-x2*u_Y.
```

At the symmetric root, `x*u_Y=1`.  Differentiating the first two equations
therefore makes the derivative in `x0` vanish.  Differentiation in the partner
coordinate gives

```text
dF_0/dx2=-1/x-x^3/(1-x^4)=alpha,
```

and differentiation in either opposite-pair coordinate gives

```text
dF_0/dx1=dF_0/dx3=x*(3x-2)/(1-x^4)=beta.
```

Pair and phase symmetry yields exactly (10.7).  The two within-pair
antisymmetric eigenvalues are `-alpha`; on the pair-constant subspace the
matrix is `[[alpha,2beta],[2beta,alpha]]`, with eigenvalues
`alpha±2beta`.  Here `alpha<0<beta`, and using `1/x=3x-1` gives

```text
alpha+2beta=(3-5x)/(1-x^4)<0.
```

Thus `alpha-2beta<0` as well and the determinant in (10.9) is strictly
positive.

The active-gap map is smooth near the interior root, so IFT applies with all
complete reward coordinates as free parameters.  Interior probabilities,
the finite list of inactive strict inequalities, and opponent-only two-phase
contraction persist after shrinking the neighborhood.  The deterministic
claim is also genuinely open despite there being infinitely many clock
dates: the instability proof depends only on the finite first coalition and
one of fifteen fixed strict reward toggles (plus the all-Never solo toggle),
not on the numerical first date.  These finitely many margins persist under
arbitrary nearby nonsymmetric reward perturbations.

## Proposition 7

Direct conditioning gives

```text
v=qx B_0+xq C_0+q^2 D_0+x^2 w,
w=2qx A_1+q^2 A_2+x^2 v.
```

Forced Quit and Continue at the active phase are respectively
`Q=xB_0+qD_0` and `qC_0+xw`.  Imposing `v=Q=qC_0+xw` makes the first value
recursion automatic.  Substitution into the second, followed by division by
`q>0`, is exactly

```text
(1+x+x^2)Q-C_0-2x^2 A_1-xq A_2=P(x)=0.
```

The endpoint signs are therefore

```text
P(0)=D_0-C_0>0,
P(1)=3B_0-C_0-2A_1<0,
```

so IVT gives an interior root.  Its inactive forced-Quit payoff is precisely

```text
x^2 B_0+2xq B_1+q^2 B_2,
```

while Continue gives `w=(Q-qC_0)/x`; hence (11.5) is the entire inactive
endpoint-Nash condition.  The interior `x,q` again give player-deleted
survival factor `x^3<1` per two phases, which handles Never and then all
behavioral deviations by pure-time extremality.

## Scope

Corollary 6.2 establishes a full-dimensional local mixed-only escape region.
Proposition 7 identifies a broad sufficient chamber and its exact inactive
wall.  Neither is a universal no-go outside the opposite-pair-count class.
