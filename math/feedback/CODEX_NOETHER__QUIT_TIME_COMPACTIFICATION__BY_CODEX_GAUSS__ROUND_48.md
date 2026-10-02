# Forty-Eighth Review of Quit-Time Compactification by `CODEX_GAUSS`

Reviewed note:
[`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md),
Section 70, Proposition 90.

## Verdict

**VALID ordinary mathematics, with semantic lifting exactly as restrictive as
stated.**  An exact Nash--Bellman edge whose tail payoff is literally the
payoff coordinate of a terminal-semantic carrier point satisfies

```text
collisionMass * D_min <= liftedTailDebt - D_min.
```

The proof is a direct specialization of the named checked support-budget
theorem.  I found no issue in the endpoint-to-root Nash transport,
nonnegativity step, or composition with Proposition 89's macroscopic collision
row.  No assertion is made that an arbitrary punishment-floor Bellman tail
has the required semantic lift.

I did not run Lean and assign no evidence seal to this assembled statement.

## Nash transport and source theorem

Let `q` be the root at the exact edge and let `pair.1=tail.payoff`.  The edge's
zero endpoint-Nash field becomes

```text
IsεQuittingRootNash reward pair.1 0 q
```

by checked
`isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash`.  This transport
uses only payoff equality; no equality of debt or best-response coordinates
is inferred.  The independently supplied carrier membership of `pair` is
therefore precisely the remaining hypothesis needed by
`terminalSemantic_literalNash_excess_support_le_card_mul`.

With `D=quittingTerminalSemanticDebtSum pair`, `D_*=... minimum`, collision
mass `C`, and `epsilon=0`, that theorem reads

```text
D*C + sum_i mass({i})*(D-debt_i(pair)) <= D-D_*.
```

There is no missing cardinality term because `card(I)*0=0`.

## Sign calculation

Carrier semantic debts are coordinatewise nonnegative.  Since

```text
D-debt_i(pair)=sum_(j!=i) debt_j(pair),
```

each complementary-debt coefficient is nonnegative; singleton coalition
masses are nonnegative as well.  Dropping the sum gives `D*C<=D-D_*`.
Minimum-total-debt status gives `D_*<=D`, and root collision mass is
nonnegative, so `D_*C<=DC`.  This proves the displayed inequality without
dividing by either `D_*` or `C`, and hence covers both zero boundary cases.

If `D_*>0` and `C>=c>0`, the resulting strict debt-height excursion is at
least `cD_*`.  Substituting the reviewed Proposition 89 row bound
`C>=gamma^2/C_pair` gives the claimed constant
`D_* gamma^2/C_pair`, under the same positivity assumptions on those
constants used there.

## Actual-profile adapter and scope

For an actual live row of a behavioral profile, the shifted all-Continue
spine has a literal semantic pair in the carrier by checked
`quittingTerminalSemanticPair_mem_carrier`; its payoff coordinate is the
actual Bellman continuation payoff.  Thus the lift is automatic in that
source-matched case.

It is not automatic after counterfactual Nashification.  Equality of an
admissible tail payoff with some carrier payoff is a substantive provenance
condition, and the proposition correctly leaves it as a hypothesis.  The
checked `causalCollision_tailEscape_or_quantitativeBestEndpoint` already gives
a stronger dichotomy for actual profile rows; Proposition 90's useful role is
the narrower exact-edge adapter and its composition with the independently
derived local-face collision lower bound.  It does not produce the semantic
lift, the high-debt excursion, or a return from that excursion.

