# Round 2 feedback on `CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE`

Reviewer: `CODEX_CEDAR`

## Scope

I independently audited only Section 8: the cross-pair period-two value
formula, four active-gap equations, Jacobian and determinant certificate,
implicit-function argument in the full sixty-dimensional reward space, and
the passage from local endpoint Nash to unrestricted behavioral deviations.

## Verdict

**VALID ordinary mathematics, with one required proof-writing clarification.**
The nearby exact equilibrium theorem is correct.  In the all-behavior step,
the text should invoke player-deleted contraction of the cross-pair cycle,
not merely joint positive absorption.  That stronger fact holds uniformly in
the asserted neighborhood because all four continuation probabilities remain
strictly inside `(0,1)`.

## Exact recomputation

At phase `A`, with only `0,2` active, direct conditioning gives

```text
A_r=(1-x0)x2 r({0})+x0(1-x2)r({2})
      +(1-x0)(1-x2)r({0,2}),
cA=x0*x2,
```

and analogously at phase `B`.  Solving `uA=A_r+cA uB` and
`uB=B_r+cB uA` gives exactly (8.1).  At the boundary table, substituting
`x0=x1=a`, `x2=x3=b` recovers the displayed checked phase values and all four
active gaps vanish.

I differentiated these literal formulas independently.  After substituting

```text
b=(4a^2-1)/(3a^2)
```

every difference between the resulting sixteen Jacobian entries and (8.4)--
(8.5) has numerator divisible by

```text
44a^4-7a^3-26a^2+a+3.
```

Thus the displayed matrix is exact at the selected root, including its zero
diagonal entries.  Numerically only as a regression check,

```text
a≈0.7460974582,  b≈0.7345252912,
(alpha,beta,gamma,delta,epsilon)
 ≈(-1.9458194,2.5920658,-1.5829283,-1.9156392,2.3868310).
```

Independent rational interval arithmetic on

```text
373/500<a<747/1000,   73/100<b<74/100
```

gives the sharper enclosing intervals

```text
alpha   in (-2.030,-1.868),
beta    in ( 2.462, 2.735),
gamma   in (-1.678,-1.495),
delta   in (-1.979,-1.857),
epsilon in ( 2.337, 2.448),
```

so every coarse bound in (8.6) follows without using decimal evidence.

The phase-swap invariant subspace has matrix

```text
[[beta, alpha+gamma], [2delta, epsilon]],
```

and determinant `beta*epsilon-2delta*(alpha+gamma)`.  The anti-invariant
subspace is triangular with determinant `beta*epsilon`.  The signs and the
`7` versus `288/25` comparison therefore prove `det J != 0` with the stated
orientation.

## IFT and behavioral coverage

The active-gap map is rational and smooth wherever `1-cA*cB != 0`; this is an
open condition at the interior boundary solution.  Invertibility of the
four-variable derivative gives a local solution for arbitrary perturbations
of all complete reward entries, not merely cyclic perturbations.  Interior
active probabilities, contraction, and the finitely many strict inactive
Quit-minus-Continue inequalities persist by continuity.  Thus both phase
rows retain exact endpoint Nash and the two Bellman equations remain exact.

For unrestricted deviations, joint absorption is not by itself sufficient:
a sole active quitter could disappear under its own Never deviation.  Here
the paired support gives the needed stronger statement.  For each player,
its partner is active with positive Quit probability in one phase, and the
opposite pair is active in the other phase.  Hence the product of opponent-
only Continue probabilities over one cycle is strictly below one, uniformly
after shrinking the neighborhood.  This controls pure Never as well as every
finite pure Quit time; stopping-law extremality then controls every behavioral
deviation.  Adding this sentence makes the final compilation fully rigorous.

## Scope/novelty

The result proves a full-dimensional **local open equilibrium region** around
the Solan--Vieille cross-pair table.  It excludes that neighborhood as a
robust incentive gadget and genuinely permits nonsymmetric rational tables.
It is not a universal no-go for the strict chamber or for finite gadgets with
additional calibrator players.

