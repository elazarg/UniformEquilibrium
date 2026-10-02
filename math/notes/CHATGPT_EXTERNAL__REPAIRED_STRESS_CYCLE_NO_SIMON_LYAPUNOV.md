# Repaired four-player stress cycle has no strict Simon Lyapunov potential

Author: `CHATGPT_EXTERNAL`
Status: `PROOF_DRAFT`

## Exact question

This gives the candidate-level negative answer explicitly accepted by
[`../questions/SIMON_LYAPUNOV_CERTIFICATE.md`](../questions/SIMON_LYAPUNOV_CERTIFICATE.md):
an exact positive-variation cycle in the full production correspondence of a
natural rational quitting table.

## Exact table

Let `I=Z/4Z`. The nonempty-coalition rewards are

```text
{0}       (1,3,2,0)       {0,1}     (2,0,1,1)
{1}       (0,1,3,2)       {1,2}     (1,2,0,1)
{2}       (2,0,1,3)       {2,3}     (1,1,2,0)
{3}       (3,2,0,1)       {0,3}     (0,1,1,2)
                           {0,2}     (0,1,0,1)
                           {1,3}     (1,0,1,0)
{0,1,2}   (0,0,0,1)       {1,2,3}   (1,0,0,0)
{0,2,3}   (0,1,0,0)       {0,1,3}   (0,0,1,0)
{0,1,2,3} (0,0,0,0)
```

This is the repaired stress family `F'(2,1)`, represented in the repository
by `RepairedFourPlayerStress.stressWeight`.

Put `R^k=r({k})` and

```text
v^0=(1,2,2,1),  v^1=(1,1,2,2),
v^2=(2,1,1,2),  v^3=(2,2,1,1).
```

## Carrier membership

Modulo four,

```text
v^k=(8R^k+4R^(k+1)+2R^(k+2)+R^(k+3))/15.
```

Thus every `v^k` lies exactly in the feasible convex hull. Every own singleton
payoff is one, and the table's punishment floor satisfies `chi_i<=1`. Since
all coordinates of the four points are one or two, every `v^k` is exactly
individually rational. Hence all four points lie in `K_(1/2)`.

## Four correspondence edges at epsilon one-half

For each `k`, let only player `k` Quit with probability `1/2`. Then

```text
v^k=(1/2)R^k+(1/2)v^(k+1).
```

The active owner is exactly indifferent. Relative to `k`, the forced-Quit
payoff, forced-Continue payoff, and their difference for the four cyclic
positions are

```text
i       Quit      Continue    Quit-Continue
k       1         1            0
k+1     1/2       2           -3/2
k+2     1/2       2           -3/2
k-1     3/2       1            1/2.
```

Thus every support clause of the full correspondence holds at tolerance
`epsilon=1/2`, including the passive-player inequalities. In directed order
the graph contains

```text
v^0 -> v^3 -> v^2 -> v^1 -> v^0.
```

Every edge has Euclidean production cost `sqrt(2)`. If a function `Phi` and
`c_0>0` satisfied

```text
Phi(y) <= Phi(x)-c_0*c(x,y)
```

on every edge, summing over the cycle would give
`0<=-4*c_0*sqrt(2)`, a contradiction. Hence no function whatsoever satisfies
the requested strict edge inequality, and in particular no finite-cell Simon
Lyapunov certificate exists for this table at `epsilon=1/2`.

## Subdivision for every positive tolerance

Fix `epsilon>0`. Choose `N` sufficiently large, put

```text
beta=2^(-1/N),  h=1-beta<=epsilon,
```

and replace the phase from `v^(k+1)` to `v^k` by

```text
x^k_m=(1-beta^m)R^k+beta^m v^(k+1),  0<=m<=N.
```

Then `x^k_0=v^(k+1)`, `x^k_N=v^k`, and

```text
x^k_(m+1)=hR^k+beta*x^k_m.
```

This is the exact Bellman edge obtained when only `k` may Quit, with
probability `h`. All microstates remain exactly feasible, individually
rational, and coordinatewise at least one. The owner remains indifferent.
The successor and opposite passive players have nonpositive Quit advantage,
bounded above by `-h`, while the predecessor's Quit advantage is at most
`h<=epsilon`; its Continue value is at least
`2*beta^N=1`, while forced Quit pays `1+h`.

The `4N` microedges therefore form a positive-cost cycle in `G_epsilon`.
Each collinear phase still has total variation `sqrt(2)`, so the whole cycle
has variation `4sqrt(2)`. Thus the same table admits no strict Simon Lyapunov
potential at any positive tolerance.

## Scope and checks wanted

- This is a complete candidate-level falsification, not a positive
  certificate and not a universal no-certificate theorem for all games.
- Audit the exact full-correspondence orientation and production cost.
- Audit the carrier punishment-floor bound and all passive row inequalities.
- Audit the microedge predecessor bound and phase closure.
- Compare the result with the existing repaired-stress circulation and generic
  positive-cycle obstruction to identify the exact new packaging.
