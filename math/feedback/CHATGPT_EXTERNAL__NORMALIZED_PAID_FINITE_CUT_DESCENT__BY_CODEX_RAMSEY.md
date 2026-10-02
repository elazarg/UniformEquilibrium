# Review of `CHATGPT_EXTERNAL__NORMALIZED_PAID_FINITE_CUT_DESCENT`

Reviewer: `CODEX_RAMSEY`

## Verdict

**Finite-cut theorem: PASS.  Unconditional well-founded/infimum closure:
FAIL.**

The current note honestly records this distinction.  Its normalized paid-row
identity and its finite labelled-mass cut are valid.  The advertised
contradiction from `inf M_theta` is not valid with the source-dependent
quantity `mu(sigma)`.  Neither Fin4 cardinality nor the full-gap paid row
uniformizes that quantity, and the inert `A=0` arm is outside the signed-label
producer altogether.

## 1. Exact normalized-mark identity

Put

```text
D_N = total semantic debt of x_N,
P_N = joint suffix reach,
R_N = paid observer's opponents-only reach,
Delta_0 = the exact difference of the original two pure-time payoffs,
Delta_N = the exact difference of their depth-N shifts.
```

The checked declarations give

```text
D_N=P_N D_0,
P_N<=R_N,
Delta_N=R_N Delta_0.
```

Here `D_0>0` follows from
`QuittingPaidCapLiftedSource.initialDebt_pos`, so
`theta=Delta_0/D_0` is legal.  Since `Delta_0>0`,

```text
Delta_N=R_N Delta_0
       >=P_N Delta_0
       =theta D_N.                                     (1.1)
```

This uses the exact payoff difference, not merely the row's stored lower
bound `gain`.  The shifted row keeps the observer, orientation, relative
delay and literal profile provenance by
`pureTimePayoff_sub_shift` and the `ShiftedPaidRow` accessors.  Because
`D_N>=D_*>0`, `(1.1)` also gives `Delta_N>=theta D_*`.

One proof-writing point should remain explicit in any theorem statement:
membership in the marked class is defined using the **actual witness
difference** `Delta_N`.  The currently checked `ShiftedPaidRow` stores the
weaker canonical gain `reachFloor*source.gain`.  Repackaging the same shifted
witnesses with gain `Delta_N` is elementary from `edge_identity` and
`gain_le_liveMass`, but it is a small wrapper not presently named.

## 2. Exact finite-cut descent

Let `T` be one fixed nonempty coalition and write

```text
m_n(T)=quittingRootCoalitionMass(q_n,T).
```

Assume

```text
0<mu<=tsum_n m_n(T).
```

The terms are nonnegative.  Hence for every `0<lambda<1`, convergence of the
partial sums supplies a finite `N` with

```text
lambda*mu <= sum_(n<N) m_n(T).                          (2.1)
```

The pointwise coalition bound in
`PunishmentFloorSummablePortLabel.lean` gives

```text
m_n(T)<=a_n,
```

where `a_n` is the cap root's absorption.  Finally
`QuittingPaidCapLiftedSource.minimum_mul_partialAbsorption_le_debtDrop`
gives

```text
D_* sum_(n<N) a_n <= D_0-D_N.
```

Combining with `(2.1)` yields the exact surviving conclusion

```text
D_N <= D_0-lambda*D_*mu.                               (2.2)
```

The endpoint `x_N` is an actual finite behavioral prefix, not the semantic
limit.  Its exact witness difference obeys `(1.1)`, so it remains in the
same `M_theta`.  With `lambda=1/2`, the strict decrement is `D_*mu/2`.

For a signed port produced by a nonzero cap displacement `rho`, one may take

```text
L=2^(card I)-1,
mu=rho/(2*M*L),
D_N<=D_0-D_*rho/(4*M*L).                               (2.3)
```

For Fin4, `L=15`.  This is the strongest unconditional finite-cut theorem
available from that signed port.

## 3. The infimum choice is circular

Let

```text
d_theta=inf {D(sigma): sigma in M_theta},
kappa(sigma)=D_*mu(sigma)/2.
```

Infimum approximation says that for each **fixed constant** `epsilon>0`
there exists `sigma` with `D(sigma)<d_theta+epsilon`.  It does not produce

```text
D(sigma)<d_theta+kappa(sigma)/2,                       (3.1)
```

because the right-hand tolerance is learned only after `sigma` is selected.

A one-dimensional exact model exposes the failure.  Take debts

```text
M=(D_*,D_*+1],
d_theta=D_*,
successor(D)=D_*+(D-D_*)/2,
kappa(D)=(D-D_*)/2.
```

Every point has a positive strict descent by `kappa(D)`, but no finite
iteration reaches the infimum.  The proposed selection `(3.1)` would require

```text
D-D_* < (D-D_*)/4,
```

which is impossible.  This is exactly the logical shape of a displacement
and mass floor tending to zero near the infimum.

There is an even more source-native version of this obstruction.  If `x_N`
is used as a renewed cap-lift source, determinism of the checked root selector
makes its new cap orbit the tail of the old one.  Therefore its displacement

```text
rho_N=||b_infinity-b_N||_infinity
```

tends to zero.  The available signed-label lower bound

```text
mu_N=rho_N/(2*M*L)
```

accordingly tends to zero, while `(1.1)` preserves the same normalized paid
density.  Thus degeneration is already built into the proposed regeneration,
not merely allowed by an abstract example.

## 4. Compactness and attainment do not follow

The semantic carrier is finite-dimensional and bounded, but the proposed
`M_theta` is a class of **actual behavioral profiles with two pure-time
witnesses**.  The witness times are unbounded.  Along the checked cap port,
the first-disagreement date is shifted outward by `N`; a convergent semantic
subsequence need not retain any one finite witness pair.  Consequently the
existential witness condition is at best a countable union over clock pairs,
not automatically closed.  Compactness and attainment of `d_theta` have not
been established.

Even an attained minimum would only help after excluding the inert case at
that minimizer.  If the minimizing port has `rho=0`, the signed-label theorem
has no positive input and produces no `mu`.

## 5. The `A=0` arm is a genuine missing case

The exported exact trichotomy proves that `A=0` forces every cap root to be
all Continue and fixes all cap, prescribed and debt coordinates while the
paid row persists.  In this arm

```text
rho=0,
mu=rho/(2*M*L)=0.
```

Therefore the finite-cut theorem, whose premise is `mu>0`, says nothing.
Positive paid density is algebraically compatible with this arm.  Any global
closure must separately eliminate the inert stall or attach a different
well-founded move to it.

## 6. Fin4 and paid-label provenance do not uniformize `mu`

Fin4 replaces the finite label factor by `15`; it does not lower-bound
`rho`.  A full-gap row may give `Delta_0>=Gamma` and hence a positive lower
bound on normalized paid density after using the reward/debt bounds, but no
checked identity bounds cap displacement below by that density.  The exact
cap/prescribed surcharge seam allows `rho=0` with the row intact.

The independent label screen
[`CODEX_RAMSEY__RANK_ONE_PAID_TANGENT_LABEL_NONIDENTIFICATION.md`](../notes/CODEX_RAMSEY__RANK_ONE_PAID_TANGENT_LABEL_NONIDENTIFICATION.md)
also blocks the most natural attempted Fin4 repair.  The pair-base producer
may choose its full-gap observer outside both the unique minimum-debt reset
mover and a positive tangent recipient.  For the curvature row, positive
tangent and positive curvature supports can be disjoint.  Thus paid density
cannot presently be charged to the coordinate producing `rho` by a forced
label coincidence.

This label mismatch is not itself a small-`rho` counterexample, but it proves
that the existing Fin4 provenance supplies no bridge from the paid row to a
uniform displacement floor.

## 7. Strongest surviving theorem and required extra input

The valid result is the conditional finite-cut theorem `(1.1)--(2.2)`:

> A paid cap source with a supplied positive fixed-label total mass `mu`
> admits, for every `0<lambda<1`, an actual finite prefix in the same
> normalized paid class whose total debt drops by at least
> `lambda*D_*mu`.

This is a useful strict descent on each positive-displacement slice.  It is
not well-founded over the union of slices.

The infimum proof becomes valid under either of the following genuinely new
inputs:

1. a uniform `mu_*>0` for every renewed source in `M_theta`;
2. compactness and attainment of the marked minimum, plus exclusion of
   `rho=0` at every minimizer; or
3. a natural-valued rank decrease handling `rho=0` and arbitrarily small
   positive `rho`.

None is supplied by the current Fin4 same-source composite.

## Sources checked

- `StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`:
  `quittingCapLiftedPrefixProfile_debt_eq_suffixReach_mul`,
  `suffixReach_le_observerReach`, `pureTimePayoff_sub_shift`,
  `minimum_mul_partialAbsorption_le_debtDrop`, and `ShiftedPaidRow`;
- `Quitting/Bellman/Finite/PunishmentFloorSummablePortLabel.lean`:
  `coalitionMass_le_absorptionMass` and
  `SummableChargeSignedTerminalPort.mass_lower`;
- [`PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL.md`](../exports/PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL.md);
  and
- `StoppingLaw/Endpoint/FinFourSameSourcePaidResetCapPort.lean`.
