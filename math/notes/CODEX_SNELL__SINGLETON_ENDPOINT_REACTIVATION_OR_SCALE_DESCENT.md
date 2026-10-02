# Singleton endpoints force reactivation or a lower-scale Never descent

Author: `CODEX_SNELL`

## Status

**Proof draft, ordinary mathematics, not checked in Lean.**  This note starts
after the reviewed source-preserving chronological Never descent in
[`CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT.md`](CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT.md).
It uses the positive global minimum of total terminal debt for the first time.

At any resulting singleton leading-hazard endpoint, either the endpoint stays
a fixed distance above the minimum, the last leading owner has a positive
literal Never cap exposing the next hazard scale, or a nonowner has a positive
literal Quit-at-zero cap.  The latter is a source-attached, fully reached paid
first-disagreement row.  The alternatives are exact at every sufficiently
large finite index; the displayed constants are limiting lower bounds.

This trichotomy does not yet produce a terminal approximation.  In the
Quit-at-zero arm, later responders see a sure quitter and the singleton-owner
transition becomes a coalition-toggle problem.  The checked duplicated-cyclic
regression shows why the singleton matrix alone supplies no monotone cyclic
order.

## Sources inspected

- The input chronology and exact finite-index cap meaning are Theorem 3.1 and
  Lemma 2.2 of
  `CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT.md`.
- Behavioral pure-time completeness is
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.
- The exact first-disagreement factorization is
  `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`.
- The finite-response-cycle boundary is formalized by
  `FinFourPureTimeExactResponseCycle` and its exact cross-cap ledger in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourPureTimeExactResponseCycleExternality.lean`.
- The full-core duplicated-cyclic matrix declarations are in
  `UniformEquilibrium/Quitting/Classification/LCP/StandardQSideExample.lean`.

A narrow search found no existing theorem computing all four unrestricted
debt limits at a singleton endpoint while retaining the ancestry through the
preceding Never deletions.

## 1. Singleton endpoint with full ancestry

Let `I=Fin 4`, let `sigma_n` be the actual period-one tropical source, and
let `K=supp(lambda)`.  Suppose `|K|=2` or `|K|=3`.  Apply the reviewed
chronological descent:

- when `|K|=2`, make one support owner Never;
- when `|K|=3`, make the selected two support owners Never in the proved
  cap-attaining order.

Write the resulting actual stationary profile as `tau_n`, and let `k` be its
unique remaining leading owner.  Every original zero-share outsider retains
its positive source hazard.  Thus, at every finite `n`, `tau_n` is
almost-surely absorbing.  If `g_n` is the total hazard of all players other
than `k`, then

```text
x_(n,k)>0,      g_n/x_(n,k)->0.                       (1.1)
```

The terminal law and payoff satisfy

```text
Law(tau_n)->delta_{ {k} },
U(tau_n)->r({k}).                                     (1.2)
```

The complete source ancestry is literal:

```text
sigma_n -- one or two exact-cap Never updates --> tau_n. (1.3)
```

No profile in (1.3) is a counterfactual sibling of its predecessor.

For any actual profile `rho`, let

```text
d_i(rho)=W_i(rho)-U_i(rho),
D(rho)=sum_i d_i(rho),
D_*=inf_rho D(rho).                                   (1.4)
```

Assume the counterexample-facing global field

```text
D_*>0.                                                (1.5)
```

## 2. Exact debt limits at the singleton endpoint

### Lemma 2.1 (nonowner column formula)

For every fixed `ell!=k`,

```text
d_ell(tau_n) -> max(0,s_ell-r_ell({k}))
              =max(0,-A_(ell,k)).                    (2.1)
```

If the limit is positive, then for all sufficiently large `n` literal
Quit-at-zero attains player `ell`'s complete unrestricted cap exactly.

#### Proof

Against `tau_(n,-ell)`, player `k` has hazard asymptotically larger than the
total hazard of every other opponent.  Literal Never therefore pays
`r_ell({k})+o(1)`.  Quit at date zero pays `s_ell+o(1)`, since the probability
of a simultaneous opponent Quit is `o(1)`.  Stationarity gives the exact
pure-time envelope

```text
(1-a_n^t) NeverValue + a_n^t QuitNowValue             (2.2)
```

for every finite deterministic time `t`.  Pure-time extremality makes the
maximum of these two endpoints the complete behavioral cap.  The prescribed
payoff tends to `r_ell({k})` by (1.2), proving (2.1).  A strict limiting
separation makes Quit-at-zero the exact maximizing endpoint for all large
`n`.

### Lemma 2.2 (owner lower-scale formula)

After passage to a subsequence, player `k`'s debt has a limit

```text
d_k(tau_n)->beta_k>=0.                                (2.3)
```

If `beta_k>0`, then literal Never attains player `k`'s complete unrestricted
cap exactly for all sufficiently large `n`, and its actual gain converges to
`beta_k`.

#### Proof

The bounded literal Never payoffs against the retained lower-scale outsiders
have a convergent subsequence.  Quit-at-zero tends to `s_k`, while (1.2)
makes the prescribed payoff tend to the same `s_k`.  The exact stationary
pure-time envelope again says that the complete cap is the maximum of
Quit-at-zero and Never.  A positive limiting debt can therefore only be a
strict Never-over-Quit separation.  This proves exact eventual cap attainment
and (2.3).

Combining the two lemmas gives the complete identity

```text
D(tau_n) -> beta_k + sum_(ell!=k) max(0,-A_(ell,k)).  (2.4)
```

Unlike a local endpoint-Nash residual, (2.4) includes arbitrary behavioral
deviations and the clocks escaping into the lower hazard scale.

## 3. Positive-minimum trichotomy

### Theorem 3.1 (off-minimum, scale descent, or paid reactivation)

After a further subsequence, exactly one of the following exhaustive forms
can be selected.

1. **Fixed off-minimum excursion.** There is `eta>0` such that

   ```text
   D(tau_n)>=D_*+eta                                  (3.1)
   ```

   for every sufficiently large `n`.

2. **Near-minimum lower-scale descent.** One has `D(tau_n)->D_*`, and the
   remaining leading owner satisfies

   ```text
   beta_k>=D_*/4.                                     (3.2)
   ```

   For all sufficiently large `n`, its literal Never strategy is the exact
   unrestricted cap, gains at least `D_*/8`, and deletes the last leading
   hazard.  The resulting profile exposes only the original zero-share
   outsiders' lower-scale hazards.

3. **Near-minimum paid reactivation.** One has `D(tau_n)->D_*`, and there is
   one fixed nonowner `ell!=k` such that

   ```text
   -A_(ell,k)>=D_*/4.                                 (3.3)
   ```

   For all sufficiently large `n`, Quit-at-zero is `ell`'s exact unrestricted
   cap and gains at least `D_*/8`.  Its first disagreement with the prescribed
   strategy is date zero, reached with probability one.  Hence the checked
   first-disagreement factorization produces a literal paid row with full
   source reach and the entire gain, attached through (1.3) to the original
   soft source.

#### Proof

Since `D(tau_n)>=D_*`, pass to a subsequence on which
`D(tau_n)-D_*` converges.  A positive limit gives arm 1.  Otherwise
`D(tau_n)->D_*`.  Equation (2.4) and (1.5) show that one of its four
nonnegative summands is at least `D_*/4`.  If it is `beta_k`, Lemma 2.2 and a
factor-two finite-index loss give arm 2.  Otherwise stabilize a nonowner
label attaining the maximum and apply Lemma 2.1, giving arm 3.  Date zero has
live probability one, so no reach or conditional-normalization loss occurs
in its first-disagreement row.

The three descriptions separate the off-minimum case first.  Arms 2 and 3
may both be available at the same near-minimum endpoint; the theorem selects
one and does not assert logical disjointness of their raw inequalities.

## 4. Why the paid reactivation is not yet a singleton-owner cycle

In arm 3, installing `ell`'s cap makes `ell` Quit surely at date zero.  The
terminal law is close to singleton `ell`, but a later player who Quits at date
zero **joins** that sure quitter.  Its payoff is therefore a nonsingleton
reward `r({ell,m})`, not its solo payoff.  Thus the tempting iteration

```text
singleton k -- negative A_(ell,k) --> singleton ell
```

does not commute with actual response chronology.  After the first
Quit-at-zero update, the correct finite state is the current sure quitting
coalition, and subsequent responses are coalition toggles.

The duplicated-cyclic regression from the input note makes this failure
exact.  Its leading three-cycle has, after the two Never deletions, a first
removed player with Quit-now gain tending to one.  Installing that response
enters the finite pure-coalition response graph; exact strict response cycles
are compatible with the same full-core, standard-Q, and no-homogeneous
singleton matrix.  Finiteness of the player labels therefore supplies
recurrence, not a monotone cyclic-order rank.

## 5. The role of positive global minimum

The local equations (1.1)--(2.4) do not encode that `D_*` is the infimum over
**all** actual behavioral profiles.  The duplicated-cyclic table satisfies
the same local equations and has order-one debt at the displayed singleton
endpoint, but its all-Never profile has debt zero.  Consequently, for any
formal number `delta` below the displayed endpoint debt, that regression also
satisfies the local inequality

```text
D(tau_n)>=delta                                       (5.1)
```

while failing the global assertion `delta<=inf_rho D(rho)`.

This is the exact abstract obstruction to extending the regression to
`D_*>0`: producing a genuine game with positive global infimum would itself
produce a Fin4 counterexample.  No local completion can honestly assert it.
Any consumer of arms 2 or 3 must use a global comparison which either

- constructs a lower-debt actual profile from the scale descent or response
  cycle;
- proves the displayed endpoint lies a fixed distance above the global
  minimum; or
- types the reached Quit-at-zero row into an existing chronological
  Nash--Bellman consumer without losing the source ancestry.

The current checked first-disagreement and paid-port machinery supplies the
last row but not its renewable return to the same minimum source.  Thus arm 3
lands at the maintained paid-port/source-reentry waist, while arm 2 supplies
a genuine finite hazard-scale descent whose later reactivation remains open.

## Scope and nonclaims

- The theorem concerns the singleton endpoints obtained from support sizes
  two and three.  The support-four descent stops at two leading owners and is
  not silently included.
- All deviations and caps are unrestricted behavioral ones; stationarity is
  used only for the prescribed profiles and the exact pure-time envelope.
- The positive-minimum field is used only after the complete cap limits have
  been computed.
- Arm 3 is a genuine source-attached paid first-disagreement row, but not yet
  a Nash--Bellman edge, paid splice, or terminal equilibrium.
- Arm 2 lowers the current leading hazard scale but does not prove that
  previously removed players stay solved.
- No positive-minimum counterexample, monotone rank, or uniform-equilibrium
  payoff is claimed.

## Next exact question

Can the full source ancestry (1.3), together with near-minimality and the
unit-reached Quit-at-zero row in arm 3, force the response coalition to leave
the minimum fibre before it can close a strict toggle cycle?  Equivalently,
can an entirely minimum-fibre sure-coalition response cycle coexist with the
positive global terminal-debt floor?
