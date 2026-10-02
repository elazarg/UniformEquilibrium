# Paid row exact-port alternative

Authors: external `ChatGPT` contribution supplied by the user; export
assembly and source audit by `CODEX_ROOT`

Independent review:
[`CODEX_ROOT`](../feedback/CHATGPT_EXTERNAL__PAID_PROVENANCE_ORBIT_DICHOTOMY__BY_CODEX_ROOT.md)

## Exact statement

Let `I` be a nonempty finite player set and let `r` be a finite quitting-game
reward table.  Let `xPaid` be an attained behavioral profile carrying a paid
first-disagreement row for an observer `j` and a gain `g>0`.  Write

```text
u0(i) = terminalPayoff(r,xPaid)(i).
```

Assume the explicit port hypothesis

```text
punishmentValue(r,i) <= u0(i)                    for every i.       (F)
```

Then there are actual behavioral profiles `X_n`, payoff vectors `u_n`, and
product roots `q_n` such that

```text
X_0 = xPaid,
X_(n+1) = rootThenContinuation(q_n,X_n),
u_n = terminalPayoff(r,X_n),
q_n is an exact Nash root against u_n,
punishmentValue(r,i) <= u_n(i)                    for every n,i.    (O)
```

The original paid profile, its two pure-time witnesses, its first-disagreement
identity, and any other immutable paid provenance therefore remain one named
literal suffix of every `X_n`.  Define the literal absorption charge

```text
a_n = 1 - product_i Pr[q_n(i)=Continue].
```

The single marked orbit has the following exhaustive alternative.

1. **Cumulative-charge return.**  The series `sum_n a_n` is not summable.
   For every `C>0` and `eta>0` there are `m<n` on this same orbit with

   ```text
   C <= sum_(k=m)^(n-1) a_k,
   |u_n(i)-u_m(i)| < eta                            for every i.
   ```

   Hence the game has a uniform-equilibrium payoff.

2. **Summable exact port.**  The series `sum_n a_n` is summable.  There is a
   payoff `v` such that

   ```text
   u_n -> v,
   q_n -> all-Continue,
   punishmentValue(r,i) <= v(i),
   r_i({i}) <= v(i)                                for every i.
   ```

   Thus `(v,all-Continue)` is an exact floor-admissible Nash--Bellman
   self-loop.  The literal terminal-semantic pairs of `X_n` also converge to
   an all-Continue fixed semantic port.

If a terminal exploitability witness is additionally supplied, every selected
exact floor root has positive joint Continue probability.  In the summable
arm the infinite product of those joint Continue probabilities is positive.
Consequently `xPaid` is reached from every finite prefix with positive
probability and has positive limiting reach through the whole marked port.

This is the previously isolated `PaidRowExactPortAlternative`.  The floor
condition `(F)` is part of its input, not a conclusion.

## Conjecture-facing change

The paid route previously contained a separate unresolved exact-port item:
starting with an actual floor-safe paid profile, construct one source-matched
exact orbit and show that it either returns with cumulative charge or reaches
a summable all-Continue port.  The theorem closes that item completely and in
a stronger one-orbit form.  Compactness never selects a replacement source.

The remaining upstream obligation is strictly narrower: starting from the
actual normalized-curvature paid witness, prove `(F)`, replace its receiving
profile by an attained floor-safe paid profile without losing the paid mark,
or turn failure of `(F)` into debt/support-rank descent or a cumulative-charge
near-return.  The later summable-port restart remains separate.

## Definitions, probability, information, and agency

All roots are simultaneous product distributions.  `rootThenContinuation`
executes the displayed root at one date and, after the all-Continue outcome,
literally runs the supplied continuation profile.  No public selector or
additional observation is introduced.

The paid first-disagreement row concerns unrestricted pure stopping times in
the actual suffix `xPaid`; the standard pure-time reduction makes it relevant
to unrestricted behavioral deviations.  Its live mass is retained only as
paid provenance.  It is never identified with an orbit edge's absorption
charge.

The payoff vectors in `(O)` are literal prescribed terminal payoffs of the
profiles `X_n`, not artificial cap annotations.  Exact root Nash is imposed
against those same payoff vectors.  The floor is the behavioral punishment
floor used by the exact admissible relation.

## Source correspondence

The proof uses the following checked declarations.

- `QuittingStoppingLawCurvaturePaidWitness` and
  `exists_quittingStoppingLawCurvaturePaidWitness` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvatureStrategicDispatch.lean`
  already retain the paid row and both source and receiving near-optimality
  inequalities.  They do not provide `(F)`.
- `quittingTerminalSemanticPair_rootThenContinuation` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` proves that
  literal profile splicing is exactly semantic prefixing.
- `exists_quittingPunishmentFloorInfiniteOrbit_anchored` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ChargedSoloBlockerRepayment.lean`
  constructs an exact infinite floor orbit from an arbitrary boxed floor-safe
  payoff and an exact initial root.
- `QuittingPunishmentFloorInfiniteOrbit.uniformPayoff_or_summableChargeAllContinuePort`
  in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorInfiniteOrbitChargeDichotomy.lean`
  is the checked charge-or-stall dichotomy.
- `Math.exists_close_pair_with_large_charge_gap_of_compact` in
  `MathUE/DivergentChargeRecurrence.lean` supplies cofinal cumulative-charge
  recurrence on a compact payoff image.
- `QuittingTerminalExploitabilityWitness.exactFloorRoot_quitProbability_lt_one`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ChargedSoloBlockerRepayment.lean`
  supplies strict marginal Continue probability under the terminal witness.

The new mathematical content is the literal-profile packaging: anchor the
checked exact floor orbit at the prescribed payoff of `xPaid`, realize every
successor by prefixing its selected root to the preceding actual profile, and
carry the immutable paid suffix through the already checked charge dichotomy.
This is not a restatement of the weaker eventual paid-row wrapper, which
forgets the port and does not construct a literal orbit.

No external-paper claim is used.

## Proof

### 1. Construct the marked orbit before splitting

Set `X_0=xPaid` and `u_0=U(xPaid)`.  Terminal rewards are bounded, so `u_0`
lies in the canonical forward carrier.  By `(F)`, it is floor-safe.  Choose an
exact product Nash root `q_0` against `u_0`.

Inductively, after `X_n,u_n,q_n` are chosen, put

```text
X_(n+1) = rootThenContinuation(q_n,X_n),
u_(n+1) = rootSuccessorPayoff(r,u_n,q_n),
```

and choose an exact Nash root `q_(n+1)` against `u_(n+1)`.  Literal payoff
prefixing gives `U(X_(n+1))=u_(n+1)`.  The exact Nash--Bellman predecessor
lemma preserves the canonical box and punishment floor.  This is the
recursive construction underlying
`exists_quittingPunishmentFloorInfiniteOrbit_anchored`, now accompanied by
the actual profiles `X_n`.

Repeated shifting through the newly prefixed all-Continue outcomes removes
the roots in reverse order and leaves `X_0=xPaid`.  Therefore the paid row and
all its witnesses stay attached to one literal suffix.  No compactness or
subsequence choice has yet occurred.

### 2. Nonsummable charge

The payoff sequence lies in a fixed compact cube.  If `sum_n a_n` diverges,
the checked divergent-charge recurrence theorem gives, for arbitrary
`C,eta>0`, two indices `m<n` with endpoint distance below `eta` and charge gap
at least `C`.  The intervening roots form one exact floor-admissible segment
of the already constructed orbit.  Taking any fixed `C` and applying the
checked cumulative-charge lasso consumer gives a uniform-equilibrium payoff.

### 3. Summable charge

If `sum_n a_n` converges, the exact Bellman increment satisfies

```text
|u_(n+1)(i)-u_n(i)| <= 2M a_n.
```

Thus `u_n` is Cauchy and converges to a payoff `v`.  Each marginal Quit
probability is at most `a_n`, so `q_n` converges to all Continue.  Closedness
preserves the punishment floor.  Passing to the limit in the exact Nash
inequalities gives `r_i({i})<=v(i)` for every player.  These singleton
inequalities are precisely exact Nash of all Continue against `v`, and its
Bellman successor is `v`; hence `(v,all-Continue)` is the asserted exact
self-loop.

For the full semantic statement, let `Z_n=Sem(X_n)`.  Exact Nash prefixing
makes every debt coordinate nonnegative and nonincreasing along the prefixed
sequence.  Hence the debts converge; together with `u_n->v`, this gives
`Z_n->Z_infinity`.  The terminal-semantic carrier is closed, and the
all-Continue prefix fixes `Z_infinity`.

### 4. Positive reach under a terminal witness

Under the terminal witness, the strict floor-root theorem gives
`Pr[q_n(i)=Quit]<1` for every `n,i`.  Finiteness of the player set makes each
joint Continue factor positive.  In the summable arm the product of
`1-a_n` is positive.  This is exactly the probability of surviving all
prefixed roots and reaching the paid suffix, proving the strengthened marked
port assertion.

## Boundary tests

- **Required floor.**  Best-response caps always dominate punishment values,
  but prescribed payoffs need not.  Substituting the cap for `u0` destroys the
  literal payoff-prefix identity.  Therefore `(F)` cannot be silently removed.
- **Sure early absorption.**  A summable charge sequence may contain one term
  equal to `1`.  Without the terminal-witness strict-survival hypothesis, the
  paid profile remains a formal suffix but need not have positive reach.
- **Diffuse divergence.**  Charges `a_n=1/(n+2)` have no persistent
  single-edge lower bound, yet the cumulative-return arm applies.
- **Summable stall.**  Charges `a_n=2^(-n-1)` are compatible with positive
  limiting survival and belong to the exact-port arm.
- **No live-mass substitution.**  The paid row's survival-to-disagreement
  probability may be positive while every later exact-orbit absorption charge
  is arbitrarily small.  The proof never compares these quantities.

## Adapter and consumer

The theorem's actual-data adapter is an attained paid behavioral profile whose
prescribed payoff satisfies `(F)`.  Its named source structure can reuse
`QuittingStoppingLawCurvaturePaidWitness`; a new wrapper need only add the
floor proof and marked literal-orbit fields.

The divergent arm is consumed by
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` and
`quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`
in `UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`.
The summable arm is the exact port consumed by the still-open paid port-restart
problem.

This packet does not claim an adapter from every normalized-curvature paid
witness to `(F)`.

## Checked Lean realization

The game-independent positive-survival lemma is
`Math.exists_pos_le_prod_one_sub_of_summable` in
`MathUE/SummableChargeSurvival.lean`.

The literal source, orbit, and port are checked in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidRowExactPortAlternative.lean`:

- `QuittingPaidRowFloorSafeSource` retains the attained paid profile, the
  literal paid row, positive gain, and the explicit floor hypothesis `(F)`;
- `QuittingPaidRowMarkedExactOrbit` retains the root-prefixed behavioral
  profiles and proves their literal terminal payoffs equal the exact orbit
  annotations;
- `QuittingPaidRowMarkedExactOrbit.exists_close_payoff_pair_of_not_summable_absorption`
  gives the arbitrary cumulative-charge close returns on the same orbit;
- `QuittingPaidRowMarkedExactOrbit.SummableSemanticPort` retains convergence
  of the full terminal-semantic pairs to an all-Continue fixed port;
- `QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative` is the
  source-facing charge-or-port capstone; and
- `QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness`
  adds positive limiting reach of the paid suffix under a terminal
  exploitability witness.

`QuittingStoppingLawCurvaturePaidWitness.nonempty_markedExactOrbit_of_floor`
is the normalized-curvature adapter.  Its floor argument is explicit and is
not inferred from paid provenance.

Evidence seals: `M`, `L`, and `A` hold for the conditional floor-safe source.
The nonsummable arm has the checked uniform-payoff consumer `C`; the summable
arm stops at the exact semantic port and positive paid-suffix reach and has no
restart consumer here.

## Scope and nonclaims

This result does not prove that the normalized-curvature receiving profile is
floor-safe, does not convert paid live mass into absorption, does not restart a
summable port, and does not by itself close the paid exit or the finite-quitting
conjecture.  It closes the independently named `PaidRowExactPortAlternative`
and leaves the upstream floor adapter and downstream port restart explicit.
