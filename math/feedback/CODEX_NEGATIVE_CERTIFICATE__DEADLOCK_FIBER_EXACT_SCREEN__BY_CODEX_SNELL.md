# Second falsification review of the exact period-three closure

Reviewer: `CODEX_SNELL`

Reviewed object:
`notes/CODEX_NEGATIVE_CERTIFICATE__DEADLOCK_FIBER_EXACT_SCREEN.md`, SHA-256
`506d91eb352f927717b90aaef4973614f644b58855b08608ede03a228d8cf80c`.

Verdict: **PASS for the exact period-three block and its unrestricted uniform-
equilibrium-payoff conclusion.**  I found no algebraic, sign, quantifier,
reward-bound, or consumer mismatch.  This review does not upgrade the
ordinary existence calculation to Lean and does not review a whole-fibre
claim, which the note does not make.

## Claim checked

For the displayed integer completion, the four polynomial equations (B1)
have a unique root in the displayed rational parallelotope.  At that root,
the three product rows supported on `{0}`, `{2}`, and `{1,3}` and the four
displayed value rows (B5) satisfy every field of `IsQuittingBlockCertificate`.
The checked all-behavior consumer therefore makes the single, fixed row `U^0`
a uniform-equilibrium payoff.

I independently rebuilt the rational contraction calculation and the block
recursion from the reward table rather than relying on the decimal center.

## Rational parallelotope and contraction

Exact recomputation gives

```text
det A = -41914379009 / 10^12,
```

so the affine parametrization is injective.  Substitution of the stated
center into (B1) reproduces, coordinate by coordinate,

```text
 1732473241/(5*10^19),
 7039082593629169961/10^29,
 12514868747864475471/(2*10^29),
-69568260756753837021/10^30.
```

The largest absolute coordinate is about `7.04*10^-11`, hence is strictly
below `10^-9` as claimed.

I expanded `T(z)=z-F(x+Az)` over the rationals, differentiated it, and bounded
each monomial `u z^alpha` on `|z_j|<=10^-6` by
`|u|*10^(-6|alpha|)`.  The four infinity-norm row bounds are exactly

```text
14618922367/10^13,
170910873577211158347/(5*10^22),
13928416905704981571/(3125*10^18),
191805008621195199843/10^23.
```

They are respectively approximately

```text
0.0014618922, 0.0034182175, 0.0044570934, 0.0019180501,
```

all strictly below `1/200`.  Thus the derivative bound really is a contraction
bound in the infinity norm on the convex cube.  Moreover

```text
||T(z)||_infinity
 <= ||F(x)||_infinity + (1/200)*10^-6
 < 10^-9 + 5*10^-9 < 10^-6,
```

so the map sends the closed cube strictly into itself.  Banach gives one and
only one fixed point there, and `T(z)=z` is exactly `F(x+Az)=0`; there is no
wrong fixed-point equation or unproved self-map step.

The coordinate radii `10^-6 * sum_j |A_ij|` reproduce the four hulls in (B2)
exactly.  Each lies in the stated open rational interval and hence in `(0,1)`.

## Independent Poincare--Miranda check

I also substituted `z_i=+-10^-6` into each polynomial `G_i(z)=F_i(x+Az)` and
bounded all remaining monomials rationally.  On every negative face the
result is below `-99/10^8`; on every positive face it is above `99/10^8`.
The four conservative absolute lower bounds printed in (B4) are each strictly
larger than `99/10^8`.  Thus the Miranda orientation is correct in all four
coordinates.  It independently proves existence; Banach supplies the stated
additional uniqueness in the same parallelotope.

## Block recursion and structural ties

Using the displayed 15 reward rows, I independently enumerated all product-
row coalitions and computed both the on-path successor and every player's
Quit-minus-Continue endpoint gap.

For phases `0,1,2`, the recursion residuals are exactly

```text
phase 0: (0, 0, 0, 0),
phase 1: (F_0, 0, 0, 0),
phase 2: (0, (1-c)F_2, F_1, (1-d)F_3).
```

The endpoint-gap table is exactly the one displayed in the note:

```text
phase 0: (0, ab-2a-b, -2a, ab+a-b),
phase 1: (F_0, -b, 0, -b),
phase 2: (-3(c+d), F_2, F_1, F_3).
```

Consequently the four positive-hazard coordinates are tied exactly, not just
approximately.  The inactive coordinates `(phase 1, player 0)` and
`(phase 2, player 2)` are the two additional structural ties `F_0=F_1=0`.
This is allowed by the certificate: hazard zero requires a nonpositive gap,
not a strict one.  The remaining six inactive inequalities follow strictly
from the rational box.  In particular the least transparent one satisfies

```text
a(1+b)-b
 < (23/100)(29/20)-11/25
 = -213/2000 < -1/10.
```

Thus no tied inactive coordinate was accidentally advertised as strict, and
no support coordinate has the wrong complementarity sign.

## Probability, admissibility, and reward bound

All four variables lie strictly between zero and one, so every product row is
a valid independent hazard law.  Phase zero has absorption probability `a>0`.
After deleting player `0`, the phase-one hazard `b` remains; after deleting
any of players `1,2,3`, player `0`'s phase-zero hazard `a` remains.  Therefore
the deleted-opponent one-turn survival product is strictly below one for every
player.  Independently, every own singleton reward equals one, so the second
branch of the checked admissibility disjunction also holds for every player.

The bounds in (B2) put every coordinate of (B5) strictly between zero and two.
The canonical reward bound for the literal table is at least eleven because
the grand-coalition player-0 reward is eleven.  Hence the certificate's box
field is satisfied without pretending that the table is normalized to the
value-row scale.  This addresses the nonuniform reward-bound issue directly.

Finite product hazards are used independently at each phase and the
three-phase schedule repeats forever.  No public correlating device or
bounded-controller deviation restriction is inserted.

## Unrestricted consumer and quantifiers

I checked the actual declaration

```text
isUniformEquilibriumPayoff_of_isQuittingBlockCertificate
```

in `UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`.  Its
conclusion is `IsUniformEquilibriumPayoff none (U 0)` and its documentation
and proof route use the admissible cyclic continuation-block consumer against
all behavioral strategies.  The finite complementarity table is therefore
not being mistaken for a stationary or bounded-clock Nash check.

Banach selects the algebraic tuple `(a,b,c,d)` once from the fixed rational
parallelotope.  The hazards and

```text
v = U^0 = (1, 1+2a+b-ab, 1+2a, (1-a)(1+b))
```

are consequently fixed before the accuracy and horizon quantifiers in the
uniform-payoff definition.  There is no horizon-dependent root or target.

## Scope

The two inactive equalities make this exact certificate non-open under an
arbitrary reward perturbation; the note states that caveat.  The result closes
only the displayed stationary-free table.  It neither proves a neighborhood
theorem nor covers all 44 nonsingleton coordinates of the deadlock fibre.
The algebraic-root producer remains ordinary mathematics until separately
formalized, while the block consumer is already checked.
