# Finite witness passports along a stopping-law segment

## Result

There is an effective finite strategic reduction along every legal complete
one-player stopping-law mixture segment.

Fix a reward bound

```text
|reward(S,i)| <= M,
```

mix one player's complete stopping law between arbitrary source and target
strategies, and observe a different player's best-response value `V(lambda)`.
For every `epsilon, delta > 0`, there is a finite set `P` of pure quit times
(including the possible choice `Never`) such that

```text
card(P) <= floor(4 M / delta) + 2
```

and, simultaneously for every `lambda` in `[0,1]`,

```text
0 <= V(lambda) - max_{t in P} U_t(lambda) <= epsilon + delta.
```

Here `U_t(lambda)` is the payoff obtained by deviating to the deterministic
quit time `t`.  The comparison remains against **all history-dependent
behavioral deviations in the original infinite-horizon game**.  There is no
horizon truncation and no best-response-attainment assumption.

The Lean development is
`QuittingStoppingLawMixtureFiniteWitnessPassport.lean`.
It proves the pointwise witness form of the displayed maximum statement; the
maximum formulation follows because every passport payoff is below the full
best-response supremum.

## 1. Why a finite passport exists

For any fixed deviation `d`, complete stopping-law mixing is a literal
mixture of the mover's two terminal stopping laws.  Therefore

```text
U_d(lambda) = (1-lambda) U_d(0) + lambda U_d(1).
```

The reward bound gives

```text
|U_d(lambda) - U_d(mu)| <= 2 M |lambda-mu|.
```

The supremum over all deviations inherits exactly the same modulus:

```text
|V(lambda) - V(mu)| <= 2 M |lambda-mu|.
```

At each point of the uniform grid

```text
{0, 1/N, ..., N/N},
```

choose one pure quit time whose payoff is within `epsilon` of the behavioral
supremum.  Such a pure time exists even when the supremum is not attained:
first choose an approximately optimal behavioral deviation, then use
pure-time extremality to approximate that deviation.

For an arbitrary `lambda`, move to a grid point at distance at most `1/N`.
Moving the envelope costs at most `2M/N`; moving the selected witness back
costs another `2M/N`.  Hence

```text
V(lambda) <= U_t(lambda) + epsilon + 4M/N.
```

Lean constructs the uniform grid, proves that it is a `1/N`-net, and proves
the explicit passport bound

```text
card(P) <= N+1.
```

Taking

```text
N = floor(4M/delta) + 1
```

gives the accuracy form stated above.  The small positive `epsilon` is
load-bearing: a general infinite-horizon best-response supremum need not be
attained.  It may be chosen arbitrarily small, but cannot honestly be
replaced by zero without an additional attainment or tail hypothesis.

## 2. A finite affine atlas for semantic debt

Let `P(lambda)` be the prescribed terminal payoff and define the pure-time
deviation-gain chart

```text
g_t(lambda) = U_t(lambda) - P(lambda).
```

Both terms are affine under complete stopping-law mixing, so Lean proves
that every `g_t` is exactly affine in `lambda`.

Literal semantic debt is

```text
D(lambda) = V(lambda) - P(lambda).
```

The same passport satisfies

```text
0 <= D(lambda) - max_{t in P} g_t(lambda) <= epsilon + delta
```

uniformly on `[0,1]`.  Thus the nonlinear debt coordinate is uniformly
approximated from below by the upper envelope of a bounded finite family of
affine functions.

This is stronger than merely sampling the value function.  The retained
objects are legal deviations in the original game, and their payoff charts
remain exact at every mixture weight.

## 3. The finite equivalence-class axis

The passport gives an honest approximate answer to the equivalence-class
question.

For one observer, use the active passport witness of the finite upper
envelope as the class label.  A finite upper envelope of affine functions on
an interval is piecewise affine; witness changes can occur only at pairwise
line intersections.  After quotienting coincident charts and allowing ties
on cell boundaries, there are at most `card(P)` one-dimensional active
pieces.

For all players other than the mover, Lean chooses the passports
simultaneously.  If there are `m` such observers, the total number of stored
charts is bounded by

```text
m * (floor(4M/delta) + 2).
```

A common refinement of their one-dimensional passport envelopes is still a
finite polyhedral subdivision.  On each open cell:

- the mover's prescribed payoff coordinates are affine;
- every retained pure-time deviation-gain coordinate is affine; and
- every actual debt coordinate is within `epsilon + delta` of the selected
  affine chart.

This is the useful finite type: **an approximate joint active-witness
signature along a specified legal stopping-law direction**.

It is not a finite exact quotient of all infinite quitting profiles.  The
passport depends on the segment and the requested accuracy, and exact active
witness strata can be countably infinite with nonattainment.  What is exact
is the quantified reduction: for every positive accuracy, a uniformly
bounded finite affine atlas exists and is compared to the full behavioral
game.

## 4. What this changes for seam repair

Best-response switching is no longer an uncontrolled infinite obstruction
along a proposed stopping-law repair direction.  At fixed accuracy it can be
replaced by finitely many explicit affine inequalities, with a bound depending
only on the reward scale and accuracy—not on the horizon or on the endpoint
strategies.

Combined with the earlier results, a one-player stopping-law segment now has
the following terminal geometry:

1. terminal outcome law and prescribed payoffs are exactly affine;
2. every fixed deviation-gain chart is exactly affine;
3. the full debt vector is coordinatewise convex and uniformly represented
   by a finite affine atlas;
4. on a common exact-witness stratum it is exactly affine;
5. on the zero-debt face it is exactly affine; and
6. between same-minimum-fiber endpoints it is exactly affine in every debt
   coordinate.

This removes the infinite behavioral supremum as the main reason a
one-dimensional repair chart might fail to be finite.

## 5. What it still does not solve

The result does not create a suitable repair segment.  In particular, it
does not prove that two endpoint blocks:

- have the original fixed entry and exit anchors;
- lie on the required zero-debt or minimum-total-debt fiber;
- preserve conditional live roots or marked chronology; or
- span enough independent directions to solve all external seam equations.

Nor does it make an approximate passport exact.  Zero-slack inequalities
still require an exact face theorem, a positive margin, or a separate repair.

The sharpened remaining problem is therefore not “control all deviations.”
That part is now finite at every accuracy.  It is:

```text
Find endpoint-conditioned legal stopping-law directions whose exact affine
law/payoff motion has enough rank to solve the fixed external anchor
equations, while remaining on the required exact debt fiber; use the finite
passport atlas only to control the finitely many off-face inequalities.
```

A promising coordinate choice for that question is unnormalized
chronological flux rather than conditional roots.  Complete stopping-law
mixing is affine in outcome mass; conditional roots introduce ratios.  If
the fixed-neighbour equations can be rewritten as finitely many linear or
polynomial flux equations plus nonvanishing denominators, the remaining
selection problem becomes a finite semialgebraic rank problem on each
passport cell.

This flux suggestion now has an exact companion result. The mixed hazard
satisfies `h_lambda S_lambda = J_lambda`; common endpoint hazards are
preserved on positive-survival rows, and equal time-zero endpoint roots are
preserved unconditionally. Together with minimum-fiber debt rigidity this
gives an exact fixed **terminal-semantic** payoff/root/debt port, subject to
the endpoint ports already being equal. See
[`QUITTING_STOPPING_LAW_MIXTURE_FIXED_PORT.md`](QUITTING_STOPPING_LAW_MIXTURE_FIXED_PORT.md).

## 6. Lean inventory

The experiment formalizes:

- `2M`-Lipschitz prescribed payoff along the segment;
- `2M`-Lipschitz payoff for every fixed other-player deviation;
- `2M`-Lipschitz full behavioral best-response value;
- epsilon-near pure-time witnesses for arbitrary behavioral suprema;
- finite passports over arbitrary finite nets, including a cardinal bound;
- the canonical uniform `N`-grid and its `1/N` covering property;
- the explicit `N+1`, `epsilon + 4M/N` passport theorem;
- the `floor(4M/delta)+2`, `epsilon+delta` accuracy theorem;
- exact affinity of every pure-time deviation-gain chart;
- uniform approximation of semantic debt by the finite affine atlas; and
- simultaneous atlases for every nonmoving player with the total chart-count
  bound.

All printed capstones compile without `sorry` or `admit` and use only
`propext`, `Classical.choice`, and `Quot.sound`.
