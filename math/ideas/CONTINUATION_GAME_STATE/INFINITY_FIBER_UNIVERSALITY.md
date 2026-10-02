# Universality of the Response-Graph Infinity Fibre

The interval and isolated-spike examples do not exhaust the possible boundary
behaviour.  Already in a two-player quitting game, the fibre of a completed
pure-time response graph over infinity can be an arbitrary compact subset of
a reward interval, subject only to containing its two endpoint values.

This is an ordinary-mathematics result and has not been checked in Lean.

## Theorem

Fix real numbers `a < b` and a nonempty compact set

```text
K subset [a,b],   a in K,   b in K.
```

There is one two-player quitting reward table and a sequence of actual
behavioral profiles whose player-`i` completed response graphs converge to

```text
{(d,b) : d is finite} union ({infinity} times K).                 (1.1)
```

The reward table depends only on `a,b`, not on `K`.

## Construction

Let the players be observer `i` and opponent `j`.  Give `i` rewards

```text
r_i({i})   = b,
r_i({j})   = a,
r_i({i,j}) = a.
```

The prescribed strategy of `i` is immaterial; take it to be Never.  We now
construct the stopping law of `j`.  Put

```text
K_0 = { (y-a)/(b-a) : y in K } subset [0,1].
```

This is compact and contains `0,1`.  Choose finite sets

```text
F_n subset K_0,   {0,1} subset F_n,
Hausdorff(F_n,K_0) < 1/n.
```

List the distinct elements in decreasing order:

```text
1 = y_(n,0) > y_(n,1) > ... > y_(n,m_n) = 0.
```

Choose an integer `N_n -> infinity`.  Let `j` stop at date `N_n+k` with
probability

```text
y_(n,k-1) - y_(n,k),    1 <= k <= m_n.
```

These probabilities are nonnegative and telescope to one, so this is an
actual finite-support stopping law and hence has a behavioral hazard
realization.

## Exact response values

If `i` quits at finite date `t`, it receives `b` exactly when `j` stops later;
if `j` stops at or before `t`, including a tie, it receives `a`.  Therefore

```text
V_i^n(t)
  = a + (b-a) Pr(T_j^n > t).                                     (2.1)
```

Never receives `a`.  Before `N_n`, the value is `b`.  As `t` crosses the
successive support dates, the tail probabilities are precisely

```text
y_(n,0), y_(n,1), ..., y_(n,m_n).
```

Consequently the set of all heights in the `n`-th graph is exactly the affine
copy of `F_n`.

## Graph limit

For each fixed finite date `d`, eventually `d < N_n`, so

```text
V_i^n(d) = b.
```

Conversely, given `y in K`, put `u=(y-a)/(b-a)` and choose `u_n in F_n` with
`u_n -> u`.  A date at or just after the corresponding support atom has
response height

```text
a + (b-a)u_n,
```

and that date tends to infinity because it is at least `N_n`.  Hence every
point of `{infinity} times K` occurs in the lower graph limit.

For the upper limit, take any convergent sequence of graph points.  If their
dates have a bounded subsequence, discreteness makes the date eventually
constant and the height tends to `b`.  If their dates escape, their heights
belong to the affine copies of `F_n`, whose Hausdorff distance from `K` tends
to zero.  The limiting height therefore belongs to `K`.

These lower- and upper-limit statements, in a compact metric hyperspace, prove
the Hausdorff convergence (1.1).

## Consequences

1. A boundary response fibre need not be connected, an interval, finite, or a
   finite union of intervals.
2. No encoding by only the minimum, maximum, connected hull, or a uniformly
   bounded list of coalition-labelled bubble values can encode every fibre.
3. The hyperspace in the completed response-graph state is not merely a
   convenient overapproximation.  Without extra source restrictions it is
   already forced by two-player timing geometry.
4. The all-Continue fixed point from
   `ALL_CONTINUE_BOUNDARY_FIXED_POINT.md` can carry an arbitrary compact
   inherited spectrum at infinity.

The theorem does not imply that every compact graph-valued state is jointly
realizable across all players.  It proves universality of one player's single
infinity fibre, which is enough to rule out the natural bounded-complexity
encodings based on finitely many selected fibre values.
