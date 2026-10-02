# Round 47 feedback on `CODEX_NOETHER` Proposition 89

Reviewed note:
[`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md),
Section 69, Proposition 89.

## Claim checked

The strict singleton separator from Gauss Proposition 54 remains coercive on
any exact punishment-floor admissible path whose payoffs remain near the
limiting boundary `b` and whose positive Quit support remains in the tight
face `E`.  Collision delivery is the only rowwise error.  Summation gives an
aggregate collision budget, and the no-uniform finite-prefix capacity turns
that budget into one macroscopic collision row.

This is an ordinary-mathematics review.  I did not run Lean and assign no
`L`, `A`, or `C` seal.

## Verdict

**VALID in the stated conditional scope.**  I independently recomputed the
relation orientation, singleton/collision decomposition including `Q=0` and
`zeta=1`, every constant in `(N233)--(N239)`, the path telescope, the
near-return trichotomy, and the capacity-to-one-row upgrade `(N239b)`.  I
found no mathematical objection.

The result is a producer-facing obstruction, not a producer: it says that a
fixed-charge payoff near-return cannot remain a diffuse singleton recurrence
inside one local tight face.  It does not construct the required nonlocal
excursion, outside-face owner, or collision row.

## One-edge reconstruction and orientation

Let `x` be the current payoff stored with an edge root, `y` its Bellman tail,
and `Q` the root absorption.  The admissible charged relation is oriented
from the tail state to the current state.  Thus the edge contributes
`y-x` to `payoff(source)-payoff(target)`.  The checked declaration
`IsQuittingNashBellmanEdge.eq_collisionAwareSegment`
(`UniformEquilibrium/Quitting/Cycles/CollisionAwareFiniteReturn.lean`) gives

```text
x=(1-Q)y+QD,
y-x=Q(y-D),                                            (R1)
```

where `D` is the full conditional absorbing delivery when `Q>0`.

If `Q=0`, product absorption and collision mass are both zero and `(R1)`
gives `x=y`; the asserted one-edge inequality is `0>=0`.

Suppose `Q>0`, and put

```text
zeta=collisionMass/Q.
```

When `zeta<1`, normalize the exact singleton atoms to a probability vector
`mu`.  A positive singleton atom for owner `j` implies a positive Quit
coordinate for `j`; hence the path support hypothesis puts `mu` in the
simplex on `E`.  Writing `R_single` for its singleton reward mixture and
`R_collision` for the conditional multi-quitter mixture gives exactly

```text
D=(1-zeta)R_single+zeta R_collision.                 (R2)
```

When `zeta=1`, the singleton coefficient vanishes.  Proposition 54 has
`E` nonempty, so choosing any `mu` on `E` defines `R_single`; `(R2)` remains
literal and independent of that arbitrary choice.

Every terminal reward coordinate is bounded in absolute value by
`M=quittingRewardBound reward`.  Both conditional mixtures are therefore in
the coordinate box `[-M,M]`, and

```text
||D-R_single||_infinity <= 2M zeta.                  (R3)
```

Let `L=sum_i |ell_i|`, `B=max(1,M)`, and suppose
`||y-b||_infinity<=kappa/(4L)`.  The strict separator and Holder's finite-sum
bound give

```text
ell dot (y-D)
 >= kappa-L||y-b||_infinity-2ML zeta
 >= 3kappa/4-2BL zeta.                               (R4)
```

Multiplying `(R4)` by `Q`, using `Q*zeta=collisionMass`, and then summing
along the relation path makes every intermediate payoff cancel with the
correct sign.  This proves exactly

```text
ell dot (payoff(source)-payoff(target))
 >= (3kappa/4) path.chargeSum-2BL Collision(path).   (R5)
```

No endpoint-Nash or punishment-floor field is dropped: those fields are
retained because the input path stays in the literal admissible relation;
only its Bellman identity is used in the estimate.

## Constants and both collision conclusions

If every edge satisfies

```text
zeta <= zeta_0=min(1/2,kappa/(8BL)),
```

then

```text
Collision(path)=sum Q*zeta <= zeta_0 path.chargeSum.
```

Substitution into `(R5)` leaves coefficient at least
`3kappa/4-kappa/4=kappa/2`, proving `(N237)`.  A displayed edge with
`Q>=a>0` makes total path charge at least `a`, and

```text
|ell dot v|<=L||v||_infinity
```

then proves the endpoint gap `kappa*a/(2L)`.

Without the rowwise bound, if the endpoint norm is at most
`kappa*a/(4L)`, the left side of `(R5)` is at most `kappa*a/4`, while the
charge term is at least `3kappa*a/4`.  Hence

```text
Collision(path) >= kappa*a/(4BL),                   (R6)
```

with the claimed absolute rather than conditional scale.

In the counterexample branch, let `P_0` be the checked canonical finite-prefix
charge bound.  Decoding an arbitrary admissible path by `pathToFinitePrefix`
preserves charge exactly, and
`QuittingTerminalExploitabilityWitness.prefixCharge_le` bounds the decoded
prefix.  Thus

```text
a <= path.chargeSum <= P_0,
```

so `P_0>0`.  With `gamma=kappa*a/(4BLP_0)`, `(R6)` says
`Collision(path)>=gamma*P_0`.  A finite weighted-average argument gives an
edge with

```text
zeta >= Collision(path)/path.chargeSum >= gamma.    (R7)
```

The checked product estimate
`quittingRootCollisionMass_le_choose_card_mul_absorption_sq`
(`UniformEquilibrium/Quitting/AbsorptionPath/CollisionConcentration.lean`)
then yields, for `C_pair=choose(card(I),2)`,

```text
zeta <= C_pair*Q,
Q >= gamma/C_pair,
collisionMass=Q*zeta >= gamma^2/C_pair.             (R8)
```

The positive budget `(R6)` itself rules out `C_pair=0`, so division introduces
no missing cardinality case.

## Consumer quantifiers and exact scope

`QuittingPositiveAdmissiblePayoffNearReturnFamily` permits the source,
target, path, and high edge to vary with endpoint tolerance.  Proposition 89
uses no common choice among them.  At any tolerance below
`kappa*a/(2L)`, a selected path that stays in the local payoff ball, uses only
positive Quit coordinates in `E`, and has every conditional collision ratio
at most `zeta_0` contradicts `(N238)`.  This proves the displayed three-way
escape trichotomy with the exact quantifiers of the checked near-return
consumer.

The stronger absolute collision conclusion requires the smaller endpoint
scale `kappa*a/(4L)` and absence of the first two escape arms.  Its final
macroscopic-row upgrade additionally uses the no-uniform terminal witness.
Neither statement claims that the Solan--Vieille block, or any unrelated
collision construction, crosses the numerical threshold belonging to this
particular boundary point.

