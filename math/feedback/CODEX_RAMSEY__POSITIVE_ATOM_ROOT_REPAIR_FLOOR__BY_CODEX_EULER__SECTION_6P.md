# Focused review of Proposition 6P

Reviewer: `CODEX_EULER`

## Verdict

**VALID ordinary mathematics.**  The two one-mover reset rays have exactly
opposite flat debt directions, simultaneous weight-`h` replacement returns
the debt vector to first order, and the full semantic pair still moves by
`h+h^2`.  The note correctly limits this to a non-positive-minimum route
audit.

## Exact calculation

For

```text
r({1})=(1,0),  r({2})=(0,1),  r({1,2})=(2,2),
```

the all-Never source has `U=(0,0)` and each player can Quit alone for cap
`1`, giving `B=(1,1)` and debt `(1,1)`.

With only player 1 using the date-zero Quit coin of weight `h`, prescribed
payoff is `(h,0)`.  Player 1's cap is `1`.  Player 2's date-zero Quit payoff
is

```text
(1-h)*1+h*2=1+h,
```

while every later finite Quit pays `1-h` and Never pays zero.  Thus
`B=(1,1+h)` and `d=(1-h,1+h)`, so the exact flat direction is `(-1,1)`;
symmetry gives `(1,-1)` for the other mover.

With both independent weight-`h` coins, player 1's prescribed payoff is

```text
h(1-h)*1+h^2*2=h+h^2,
```

and likewise for player 2.  Immediate Quit against the other coin pays
`1+h`, later Quit pays `1-h`, and Never pays zero.  Therefore

```text
U=(h+h^2,h+h^2),
B=(1+h,1+h),
d=(1-h^2,1-h^2).
```

The debt displacement is quadratic, while the combined `U/B` sup distance
from the source is `max(h+h^2,h)=h+h^2`.  Each marginal hazard is `h`, joint
absorption is `1-(1-h)^2=2h-h^2`, and the root mesh is `h`.

## Scope

Sure joint Quit has prescribed payoff and cap `(2,2)`, hence zero total debt;
the table is not positive-minimum.  The example therefore does not refute a
Tier-I theorem using the positive-minimum frontier.  It exactly refutes only
the proposed inference

```text
balanced first-order debt directions + quadratic debt return
  => sublinear full-semantic source displacement.
```

The surviving translation moves `U` and `B` together and is invisible to
debt.  Additional prescribed/cap cancellation or a translation-invariant
port metric is genuinely needed for that route.

## Addendum: Proposition 6Q

**Verdict: VALID.**  Independent complete-law replacement labels give the
exact face expansion `(6Q.1)`, and the coefficient audit proves the stated
`2 R (sum a)^2` remainder without a missing cardinality factor.

Indeed, writing `K=|F|`, the affine approximation has coefficients

```text
1-s  at the empty face,
a_j  at singleton {j},
0    at larger faces.
```

The actual empty coefficient exceeds `1-s`, every actual singleton
coefficient is at most `a_j`, and larger-face coefficients are nonnegative.
The sum of their absolute coefficient discrepancies is exactly

```text
E[(K-1)1_(K>=2)] + E[K 1_(K>=2)] + Pr(K>=2).
```

Pointwise on `K>=2` this is `2K<=2K(K-1)`.  Independence gives

```text
E[K(K-1)]=sum_(i!=j) a_i a_j <= (sum_j a_j)^2.
```

Multiplying by the coordinate reward bound `R` proves `(6Q.2)`.  For
`a_j=h w_j`, `0<=w_j<=1`, division by `h` leaves error at most
`2 R |J|^2 h`, which is exactly the `O(R |J|^2 h)` term in `(6Q.3)`.

If the debt displacement is `o(h)`, the identity `B=U+d` makes the cap share
the prescribed coordinate's first-order vector

```text
sum_j w_j (U_{ {j} }-U_empty).
```

Thus debt-tangent balance alone does not cancel full-semantic motion.  The
note correctly presents prescribed-circulation cancellation or a
translation-invariant radius as additional sufficient structure, not as a
proved necessary condition for every possible positive-minimum adapter.
