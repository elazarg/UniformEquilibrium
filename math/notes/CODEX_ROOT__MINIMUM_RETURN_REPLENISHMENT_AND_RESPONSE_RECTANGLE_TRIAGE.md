# Minimum-return replenishment and response rectangle: initial triage

## Status

Initial assessment only. This is not an export candidate and has not received
independent review.

The incoming `GPT_MIN_RETURN` argument has nonzero value. Its cleanest content
is an exact cross-frame debt ledger and a way to replace an increase of an
unrestricted cap by a four-profile behavioral payoff rectangle. It does not
yet prove a renewable transition or a Fin4 paid-response-cycle consumer.

The later assertion that the rectangle becomes an iterable positive one-date
endpoint walk is presently unsupported: localization of a *cross-difference*
to the marked Boolean action does not by itself preserve the absolute payoff
gain of the response against the target profile.

## Question

Suppose a fixed payer `p` occurs along a minimum-return forced-pair family.
At frame `n`, let `A_n` be the comparison profile and `B_n` its paid endpoint,
and assume

```text
g_n = d_p(A_n) - d_p(B_n) >= c > 0.
```

Can the forced compensation between consecutive independently selected frames
be converted into an executable charged return or a renewable finite-rank
transition?

## Exact replenishment ledger

Define the signed cross-frame replenishment

```text
R_n = d_p(A_(n+1)) - d_p(B_n).
```

Then

```text
d_p(A_(n+1)) = d_p(A_n) - g_n + R_n,
```

so for every `N`,

```text
d_p(A_N)
  = d_p(A_0) - sum_(n<N) g_n + sum_(n<N) R_n.
```

Nonnegativity of debt gives

```text
sum_(n<N) R_n >= N*c - d_p(A_0).
```

Thus repeated fixed payer subtraction forces signed cross-frame replenishment
with asymptotic average at least `c`. This is a useful exact diagnosis, but it
is not a contradiction: the packet provides no equality `A_(n+1) = B_n`, no
ordered behavioral transition from `B_n` to `A_(n+1)`, and no bounded budget
for the sum of the `R_n`.

In particular, convergence of the post-date tail debt to the global minimum
does not imply that either whole marked-row profile is near the minimum. A
pure nonempty coalition at the marked row screens baseline play from that
tail.

## Behavioral response rectangle on the minimum-fiber arm

Assume now that actual comparison and endpoint profiles `X_n,Y_n` have total
debts tending to the same positive minimum `D_*`, differ only in payer `p`'s
strategy, and satisfy

```text
g_n = U_p(Y_n) - U_p(X_n) >= c > 0.
```

Because changing `p`'s prescribed strategy leaves `p`'s best-response cap
unchanged,

```text
d_p(Y_n) - d_p(X_n) = -g_n.
```

For sufficiently large `n`, equality of the limiting total debts implies

```text
sum_(i != p) (d_i(Y_n) - d_i(X_n)) >= 3*c/4.
```

In Fin4, after a subsequence one fixed responder `r != p` therefore satisfies

```text
d_r(Y_n) - d_r(X_n) >= c/4.
```

Choose a `c/8`-best complete behavioral response `rho_n` for `r` against
`Y_n`. The definition of the two unrestricted caps gives the literal
four-profile inequality

```text
[U_r(Y_n[r <- rho_n]) - U_r(X_n[r <- rho_n])]
  - [U_r(Y_n) - U_r(X_n)]
  >= c/8.
```

This conclusion contains no cap. It shows that cross-coordinate compensation
can be witnessed by actual complete behavioral strategies rather than hiding
only in a supremum. With the incoming constants

```text
c = lambda * D_* / 3,
```

the rectangle premium is at least

```text
lambda * D_* / 24.
```

This part is mathematically useful, subject to attaching the comparison and
endpoint convergence along the same checked subsequence.

## Objection to the claimed one-date iteration

When the marked target coalition is nonsingleton, the *difference between the
two response payoffs* is screened from the post-date tail and depends only on
whether the responder survives to the marked date and on its Boolean action
there. This can localize or amplify the four-corner cross-difference.

It does not follow that the resulting deterministic one-date strategy retains
the responder's absolute profitable-deviation gain against `Y_n`. An
approximately best response to `Y_n` may use an earlier stopping date; replacing
it by "Continue until the mark, then choose one Boolean endpoint" can change
its payoff against both `X_n` and `Y_n` while preserving only their difference.

Therefore the following stronger claims are not yet justified:

```text
the response rectangle is a positive one-date edge;
the same construction can be iterated as a serial pure-endpoint walk;
every resulting edge has the stated absolute gain floor.
```

A repair needs either:

1. an inequality proving that one marked-date Boolean endpoint is itself
   profitable against `Y_n` by a fixed amount; or
2. a consumer formulated directly for the four-corner rectangle premium,
   without relabeling it as an ordinary paid edge.

## Source audit performed for this triage

The relevant checked declarations inspected were:

- `QuittingMarkedPairMinimumReturnActualizer.wholeDebt_tendsto` and the literal
  source/target profile accessors in
  `Research/Quitting/NormalizedPassportMinimumReturn.lean`;
- the Fin4 actual-source adapters in
  `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`;
- `ConcentratedCollisionThreeRoleEndpointLaw`, including
  `source_on_minimum_fiber`, `mover_drop`, `recipient_rise`, and
  `target_fiber_or_ascent`, in
  `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`; and
- `ConcentratedCollisionFourRole.ThreeRoleLimitChord` in
  `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`.

These checked objects already retain a minimum-fiber source limit, an endpoint
limit, mover debt loss, and recipient debt rise. They do not provide the
renewable chronological edge asserted by the incoming argument.

## Next concrete check

Test whether pure nonsingleton screening plus the existing recipient-rise
bound implies a fixed profitable marked-date endpoint for the recipient, not
merely a positive rectangle cross-difference. A small exact reward-table
regression should be attempted before proposing that lemma universally.
