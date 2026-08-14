# P x W: packet defect versus canonical periodic windows

## Classification

**Status: Consistent.**

There is an exact rational four-player table satisfying the table-wide packet
defect and a canonical periodic-window obstruction with one common margin.
The witness is stronger than bare same-table coexistence: the selected packet
mass is exactly the normalized singleton-owner occupation of every periodic
window.  Thus even that natural packet/window equation does not create a
contradiction.  The packet refusal defect instead predicts the stabilized
refusal branch.

This does **not** identify the packet target with a periodic delivery or with
a tail annotation.  That additional identification is neither part of `P x W`
nor valid in this witness.

## One common rational table

Let `I = {0,1,2,3}`, set `eta = 1/32`, and use the following singleton payoff
matrix.  Rows are payoff recipients and columns are the unique quitter:

```text
             quitter
             0    1    2    3
player 0     1    2    0    1
player 1     1    1    2    0
player 2     0    1    1    2
player 3     2   1/2   1    1
```

For every coalition of size at least two, set every player's payoff to zero.
The table is bounded by `M = 2`, and every own singleton payoff is one.  The
same table, player set, and `eta` are used below.

The behavioral punishment value satisfies `chi_i <= 1` for every player:
opponents can all Continue forever, against which player `i` obtains at most
one (quit eventually for payoff `r_i({i}) = 1`, or never quit for zero).

## P: a normalized packet and a table-wide margin

For a probability vector `lambda = (x0,x1,x2,x3)`, write

```text
b0 = x1 - x2,
b1 = x2 - x3,
b2 = x3 - x0,
b3 = x0 - x1/2.
```

The singleton mixture is

```text
m_i(lambda) = 1 + b_i.
```

Any normalized packet `(lambda,z)` satisfying (15) in Question 172 must have
`b_i >= 0` for every `i`, since `1 = r_i({i}) <= z_i <= m_i(lambda)`.
These inequalities give

```text
x1 >= x2 >= x3 >= x0 >= x1/2.
```

As the coordinates sum to one, `x1 >= 1/4`, and hence every coordinate is at
least `1/8`.  In particular every coordinate is positive, so the support
condition in (15) forces `z_i = r_i({i}) = 1` for all `i`.  It also follows
that every coordinate is strictly below one.

The four slacks telescope with a positive residue:

```text
b0 + b1 + b2 + b3 = x1/2 >= 1/8.
```

Therefore some `b_i >= 1/32`.  Refusing player `i` deletes its own singleton
atom, so its exact refusal gain over the mixture is

```text
R_i(lambda) - m_i(lambda)
  = x_i * (m_i(lambda) - r_i({i})) / (1-x_i)
  = x_i * b_i / (1-x_i)
  >= (1/8)(1/32)
  = 1/256.
```

Thus `delta = 1/256` works for **every** normalized packet allowed by this
table, not just for the selected packet.  For the witnessing packet take

```text
lambda = (1/4,1/4,1/4,1/4),   z = (1,1,1,1).
```

Then `m(lambda) = (1,1,1,9/8)`.  Player 3 is active, has `z_3 < m_3`, and has
refusal value `7/6`, hence refusal gain `1/24 > delta`.  The punishment
inequalities hold because `chi_i <= 1 = z_i`.

The compact packet family is exactly the nonempty rational polytope cut out
by the simplex and the four inequalities `b_i >= 0`, with target fixed at the
all-one vector.  So the uniform statement is not being replaced by a check of
one packet.

## W: one canonical tail and one fixed refusal branch

Define a common product root at every tail date by

```text
p_t = 1 / (200 * 2^t),
a_t = (p_t,p_t,p_t,p_t).
```

These are exact rational roots, `a_t -> 0`, and even
`sum_t q(a_t) < infinity` (the latter is not required for the `P x W` pair).
For each `n`, periodically repeat the canonical word

```text
W_n = (a_n,a_(n+1),...,a_(2n)).
```

Every phase has positive absorption probability, so every repeated word
absorbs almost surely.  Consider player 3.

Under the prescribed four-player profile, conditional on a singleton terminal
coalition, symmetry makes its owner uniform.  All nonsingleton rewards are
zero.  Consequently the prescribed delivery to player 3 is at most

```text
(2 + 1/2 + 1 + 1)/4 = 9/8.
```

If player 3 refuses forever, only the other three symmetric hazards remain.
At a phase with hazard `p`, the conditional probability that an absorbing
opponent coalition is a singleton is

```text
rho_3(p) = 3(1-p)^2 / (3-3p+p^2).
```

For `0 <= p <= 1/200`, exact cross multiplication gives
`rho_3(p) >= 99/100`.  The terminal phase distribution of a periodic word is
a probability distribution, so its overall singleton probability is a convex
combination of these phasewise ratios and obeys the same bound.  Conditional
on an opponent singleton, player 3's average payoff is

```text
(2 + 1/2 + 1)/3 = 7/6.
```

Therefore, for every canonical window,

```text
refusal value - prescribed delivery
  >= (7/6)(99/100) - 9/8
   = 3/100
   > eta/2 = 1/64.
```

Thus all windows are obstructed by the same player (player 3), the same branch
(Never/refusal), and the same positive margin.  In particular the stabilized
infinite set can be all natural numbers.

## Same table versus a genuine packet/window equation

Mere coexistence would use the packet and window sequence only as unrelated
objects over one table.  This witness has an additional exact bridge.  For a
periodic window define its normalized singleton-owner occupation by

```text
mu_n(j) =
  Pr(the terminal coalition is {j}) /
  Pr(the terminal coalition is a singleton).
```

The denominator is positive.  Since all four hazards agree at every phase,
the four singleton probabilities agree phase by phase and hence after summing
over all repetitions.  Therefore

```text
mu_n = (1/4,1/4,1/4,1/4) = lambda
```

for every `n`, exactly rather than only in the limit.

Moreover, the maximum phase hazard in `W_n` is `p_n -> 0`.  The conditional
singleton probabilities for four players and for the three refusing-player
opponents consequently tend uniformly to one.  Hence

```text
periodic delivery_3(W_n) -> m_3(lambda) = 9/8,
periodic refusal_3(W_n)  -> R_3(lambda) = 7/6.
```

The packet defect is therefore the limiting refusal obstruction.  It does
not contradict `W`; it supplies its refusal branch.

## What is absent in the general pair

The supplied reductions assert no map from their extracted packet to their
canonical windows.  For arbitrary `P` and `W` data on one table, the smallest
useful extra datum is an occupation bridge along a subsequence `n_k`:

1. the roots in `W_(n_k)` are uniformly small;
2. the normalized singleton-owner terminal measures `mu_(n_k)` converge to
   the packet mass `lambda`;
3. the nonsingleton terminal mass vanishes, also after the stabilized player
   is forced to Continue.

These conditions imply, for each `i` with `lambda_i < 1`,

```text
delivery_i(W_(n_k)) -> m_i(lambda),
refusal_i(W_(n_k))  -> R_i(lambda).
```

They are enough to make the packet defect interact with a stabilized
**refusal** branch.  The interaction reinforces obstruction.  No analogous
equation follows for a stabilized phase-stop branch.

The exact ternary residual problem is therefore `P x W x O`, where `O` is the
occupation bridge above (and is expected, if true, to be derived from the
selected tail `T`):

> Given the `T`-generated canonical windows and a normalized packet from the
> same counterexample seam, must some window subsequence satisfy `O` for that
> packet?  If so, does the stabilized branch become refusal, or, in the
> phase-stop case, what additional Bellman-prefix datum converts the stopping
> phase value into a packet coordinate?

It would be incorrect to add `periodic delivery -> z` to `O`.  At the strict
packet player, the legitimate small-hazard limit is `m_i(lambda)`, while the
packet condition has `z_i < m_i(lambda)`.  In this witness specifically,
`z_3 = 1` but periodic delivery tends to `9/8`.  Identifying `z` with honest
delivery would silently insert precisely the annotation/payoff equality that
the master question forbids.

## Scope checks

- The construction has four players, matching the cardinal lower bound, but
  it is not a full counterexample and does not establish cardinal-minimality.
- The proof is exact and rational; no numerical tolerance or reconstruction
  is used.
- Naive player extension need not preserve the table-wide packet property,
  because new pure or boundary packets can appear.  The result is not claimed
  to survive arbitrary player extension.
- No cap realization, prefix attachment, annotation/payoff equality, or
  universal terminal-instability claim is used.

The arithmetic certificates are checked in `PWPacketWindowConsistency.lean`.
