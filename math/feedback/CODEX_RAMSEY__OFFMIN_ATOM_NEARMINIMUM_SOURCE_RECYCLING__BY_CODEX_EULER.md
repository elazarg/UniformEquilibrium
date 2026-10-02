# Independent review of off-minimum atom near-minimum source recycling

Reviewer: **CODEX_EULER**

Source:
[`CODEX_RAMSEY__OFFMIN_ATOM_NEARMINIMUM_SOURCE_RECYCLING.md`](../notes/CODEX_RAMSEY__OFFMIN_ATOM_NEARMINIMUM_SOURCE_RECYCLING.md)

Verdict: **PASS, internal only.**  The independent marginal graft, all four
coupling constants, literal `lambda^4 m` atom provenance, near-minimum
all-Continue freezing, same-source paid port, and half-reset transfer
constants are correct.  The imported atom necessarily vanishes in the
unconditional return-to-minimum construction, so this does not satisfy a
`FIN4_BT` output.

## 1. Claim checked

Given an actual off-minimum profile `eta` with a positive stage atom and an
actual near-minimizing sequence `pi_n`, independently mix each of the four
complete marginal stopping laws with `eta` weight `lambda_n`.  The note
claims that the resulting literal product profiles:

- return semantically to the positive global minimum;
- retain the imported atom with mass at least `lambda_n^4 m`;
- lie in the checked unique-all-Continue cap tube;
- carry the arbitrary-profile full-gap paid cap port; and
- admit a half best-response reset with gain at least `gamma/4`, aggregate
  opponent transfer at least `gamma/8`, and a fixed recipient transfer at
  least `gamma/24`, while retaining half the imported atom.

## 2. Independent product graft and constants

The construction is a literal product behavioral profile.  Each player
privately selects the `pi` or `eta` complete-law branch; no public or
correlated whole-profile coin is introduced.

For prescribed payoff, a coupled outcome can differ from `pi` only when at
least one of four branch coins selects `eta`.  The union bound is `4 lambda`
and the payoff range diameter is `2M`, proving

```text
|Delta U_i| <= 8M lambda.
```

For one fixed deviation by player `i`, only the three opponent laws matter.
The mismatch bound is therefore `3 lambda`, uniformly over the deviating
behavioral strategy, and

```text
|Delta deviationPayoff_i| <= 6M lambda.
```

Taking the unrestricted supremum preserves this bound, so the cap estimate
is genuinely all-behavior.  Subtraction yields `14M lambda` per debt
coordinate, and summing four absolute coordinate differences yields the
stated `56M lambda` total-debt bound.  No independence is incorrectly used
after conditioning on a unilateral deviation.

## 3. Exact atom provenance

On the latent branch event where all four independent coins select `eta`,
which has probability `lambda^4`, the complete clock vector has exactly the
law of `eta`.  Its contribution to the nonnegative stage cylinder `(t,S)` is
`lambda^4 m`; all mixed branch patterns can only add mass.  Thus the atom is
literal at the same stage and coalition, not merely a terminal-law lower
bound.

The parallel `(1-lambda)^4` retention of a `pi`-side marked atom is justified
by the same expansion.

## 4. Near-minimum tube and same-source paid data

Take `pi_n` far enough that its excess is at most `delta_n/2`, and choose
positive `lambda_n` with `56M lambda_n<=delta_n/2`.  Global minimality and
the coupling estimate give

```text
0 <= e_n:=D(rho_n)-D_* <= delta_n -> 0.
```

The hypotheses of
`exists_pos_nearMinimum_capNash_eq_allContinue_radius` are therefore met;
every exact cap root against the displayed cap of this same actual `rho_n`
is all Continue.  Separately,
`HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort` applies to
that same literal `rho_n`, with gain exactly `gamma`.  The note correctly
does not identify the port's paid observer, time, or coalition with the
imported atom labels.

## 5. Half-reset constants and retention

The terminal gap gives a player `w_n` with `d_w_n(rho_n)>=gamma`.  Use
`e_n` itself in the near-minimum hypothesis of
`exists_halfStoppingLawReset_nearMinimum_transfer_and_globalRetention`.
Its checked fields give

```text
g_n >= d_w_n(rho_n)/4 >= gamma/4,
g_n <= e_n + sum_{j!=w_n} Delta d_j.
```

Since `e_n<gamma/8`, the opponent sum is at least `gamma/8`.  With three
opponents, one change is at least `gamma/24`; finite subselection fixes both
the mover and recipient labels.  The theorem's pointwise stage retention
gives

```text
StageMass(chi_n,t,S) >= StageMass(rho_n,t,S)/2
                       >= lambda_n^4 m/2.
```

All these outputs are co-realized at the same source `rho_n`; there is no
cross-source identification.

## 6. Pure-Never common-delay qualification

If the near-minimum branch has pure-Never marginal compact limits, delaying
the fixed `eta` profile behind the inert-word length makes all of its fixed
finite marginal masses vanish too.  The delay preserves `eta`'s terminal law
and prescribed payoff.  It preserves its unrestricted caps precisely because
the inserted all-Continue dates add only singleton deviations and the
assumed all-Continue cap inequality bounds those by the old caps.  This is
the correct qualification; weak convergence to Never alone would not
preserve semantic pairs.

## 7. Exact limitation and recommendation

Because `delta_n->0` and `56M lambda_n<=delta_n/2` with `M>0`, necessarily
`lambda_n->0`.  The only unconditional imported-atom floor is therefore
`lambda_n^4m/2->0`.  The paid gain and recipient transfer remain fixed, but
their labels are not aligned with the vanishing imported atom and the reset
target need not lie on the minimum fiber.  Consequently the construction
does not give fixed causal charge, a punishment-floor Bellman edge,
cumulative near-return, or iterable rank descent.

This is a genuine source-recycling theorem and a useful exact adapter, but it
reaches the already maintained transfer seam.  Keep internal unless a later
consumer controls the mixed branch corners strongly enough to retain a
nonvanishing atom or directly uses the fixed paid transfer without such an
atom.

## 8. Delta: fixed-weight strengthening

The same proof has a valid fixed-scale variant.  Choose one constant
`lambda in (0,1)` so small that, with some positive slack,

```text
56M lambda < min(epsilon_freeze, gamma/8).
```

Then take `pi_n` sufficiently near the minimum.  For all large `n`, the
fixed-weight grafts satisfy

```text
D(rho_n)-D_* < min(epsilon_freeze,gamma/8),
StageMass(rho_n,t,S) >= lambda^4 m > 0.
```

The checked half-reset theorem is pointwise: it needs only
`D(rho_n)<=D(candidate)+e_n` for the displayed positive error `e_n`; it does
**not** require `e_n->0`.  Consequently the same actual sources have unique
all-Continue cap roots, a full-gap paid port, half-reset gain at least
`gamma/4`, aggregate opponent transfer at least `gamma/8`, a fixed recipient
at least `gamma/24`, and retained stage atom at least `lambda^4m/2`.

This is strictly stronger than the vanishing-weight statement as a
fixed-scale **source packet**.  It still is not a current `FIN4_BT` consumer:

- the imported atom labels remain unrelated to the paid mover and recipient;
- the independent mixed branch patterns destroy the off-minimum atom's
  loss-free same-stage toggle provenance;
- for a nonsingleton imported atom, the checked macroscopic causal dispatch
  yields only the already maintained fixed tail-excursion versus fixed
  reached-gain/transfer split; and
- for a singleton atom, outsider regularization does not force the required
  conditional-mass sign threshold.

Thus fixed `lambda` removes the *vanishing-scale* objection but not the
prescribed-payoff/Bellman or incidence-alignment seam.  The source theorem
should be strengthened to record this fixed-weight corollary, while its
status remains internal absent a new consumer.

## 9. Author-incorporation delta

**Final delta verdict: PASS.**  The current source note now states the
fixed-weight result as the main theorem and retains `lambda_n -> 0` only as a
sufficient optional route to exact minimum convergence.  This is the correct
logical scope: the one-sided `56 M lambda` estimate cannot make vanishing
weight necessary in a table with cancellation.

The new signed-atom corollary is also exact.  The half-reset target is
literally `Function.update rho_n w mixedStrategy`, so the positive recipient
change in (5.7) enters
`hasQuittingEndpointDebtRecipientAtom_of_pos`.  Since Fin4 has sixteen
terminal outcomes, its two decoder branches give respectively

```text
(gamma/24)/(2*16) = gamma/768,
(gamma/24)/(4*16) = gamma/1536.
```

The note correctly stops there: the decoder's terminal label `T` is not the
imported stage coalition `S`, and even `T=S` would give a signed endpoint-law
atom rather than a prescribed-payoff Nash--Bellman edge.  The nonsingleton
collision comparison `lambda^8 m^2 D_*/8` versus
`56 M lambda + o(1)`, and the resulting impossible universal requirement
`448 M < lambda^7 m^2 D_*`, are arithmetically and logically correct.  The
packet remains **PASS, internal only**.
