# Same-source paid cap port: surcharge recycling boundary

Author: `CODEX_RAMSEY`

Status: **proved ordinary mathematics; independent review requested.**  This
note does not discharge the paid branch.  It gives an actual-data quantitative
split at every row of the checked Fin4 same-source paid/reset cap port and
identifies the exact reason that neither the cap roots nor their literal
best-endpoint repairs supply a well-founded global descent.  The obstruction
is the continuation-option surcharge, which can remain positive while root
absorption is zero.

Primary checked input:
[`PAID_CAP_LIFTED_SUMMABLE_PORT.md`](../formalized/PAID_CAP_LIFTED_SUMMABLE_PORT.md),
especially its Fin4 same-source paid/reset adapter.

Earlier law-enriched refinement:
[`CODEX_RAMSEY__LAW_ENRICHED_PAID_CAP_PORT_RESET_DICHOTOMY.md`](CODEX_RAMSEY__LAW_ENRICHED_PAID_CAP_PORT_RESET_DICHOTOMY.md).

Question:
[`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md).

## 1. Source audit and notation

Fix a bounded Fin4 quitting reward table, a terminal exploitability witness,
and pairwise distinct labels `o,b1,b2`.  Apply the checked
`FinFourSameSourcePaidResetCapPort`.  Write

```text
sigma_0 = the actual pair-base stationary paid source,
sigma_(n+1) = rootThenContinuation(q_n,sigma_n),
X_n = Sem(sigma_n) = (U_n,B_n),
d_(n,i) = B_n(i)-U_n(i),
a_n = absorption(q_n),
c_n = 1-a_n,
S_n = product_(m<n)c_m.
```

Let `j` be the selected paid observer/debtor, `Gamma>0` the terminal gap,
and

```text
D_* = global minimum total terminal debt,
D_0 = total debt of X_0,
sigma = D_*/D_0,
g = sigma Gamma.
```

The checked adapter gives `d_(0,j)>=Gamma`, `sigma>0`, and

```text
S_n>=sigma,
d_(n,i)=S_n d_(0,i),
sum_n a_n<infinity.                                      (1.1)
```

The coordinate identity follows by induction from
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`;
the total-debt and survival statements are the named cap-port theorems.
In particular,

```text
d_(n,j)>=g>0 for every n,                                (1.2)
positiveDebtSupport(X_n)=positiveDebtSupport(X_0).        (1.3)
```

The equality in `(1.3)` is important: the positive survival floor rules out
zero scaling.  Thus the cap lift itself cannot lower debt-support cardinality.

For each `n`, let

```text
L_n = quittingRootCoordinateNashDefect reward U_n q_n j,
H_n = quittingRootContinuationOptionSurcharge reward X_n q_n j.
```

Here `L_n` is a literal prescribed-tail endpoint defect, while `H_n` is the
increase in the best pure endpoint when only the continuation coordinate is
raised from `U_n(j)` to `B_n(j)`.  They are not absorption masses.

The source files inspected narrowly for this note were:

- `Diagnostics/Quitting/StoppingLaw/Endpoint/
  FinFourSameSourcePaidResetCapPort.lean`;
- `Diagnostics/Quitting/StoppingLaw/Endpoint/
  PaidCapLiftedSummablePort.lean`;
- `Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`;
- `Diagnostics/Quitting/Collision/SingletonPacket/
  PairBasePaidResetEndpointSeam.lean`;
- `Diagnostics/Quitting/TerminalSemanticLiteralSourceReturnNoGo.lean`; and
- `Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`.

The local cap-to-prescribed criterion in Section 38 of
[`CODEX_CEDAR__PAID_ROW_REENTRY.md`](CODEX_CEDAR__PAID_ROW_REENTRY.md)
was also checked.  The new content below is only its quantitative iteration
on the actual Fin4 paid cap port and the resulting nonsummable ledger/no-go.
The maintained `docs/FRONTIER.md` already records the qualitative fact that a
positive literal defect gives an executable unilateral deviation without a
strict total-debt descent; Proposition 3.1 only makes its exact marked-debt
account uniform along this particular port.

## 2. Persistent paid-observer reconciliation

### Theorem 2.1 (uniform literal-defect/surcharge account)

For every `n`,

```text
L_n>=0,  H_n>=0,
L_n+H_n=c_n d_(n,j)=d_(n+1,j)>=g.                       (2.1)
```

Consequently, at every row,

```text
L_n>=g/2  or  H_n>=g/2.                                 (2.2)
```

Moreover, if the same selected cap root `q_n` is exact Nash against the
prescribed tail `U_n`, then

```text
L_n=0,
H_n=d_(n+1,j)>=g.                                       (2.3)
```

**Proof.**  Carrier debt nonnegativity gives `H_n>=0`, and coordinate Nash
defects are nonnegative.  The checked exact reconciliation identity is

```text
literalDefect_j + surcharge_j
  = capDefect_j + c_n d_(n,j).
```

The selected `q_n` is exact cap--Nash, so its cap defect is zero.  The
cap-prefix coordinate debt identity identifies the remaining term with
`d_(n+1,j)`, and `(1.2)` supplies the lower bound.  This proves `(2.1)` and
`(2.2)`.  Exact Nash at `U_n` is exactly `L_n=0`, proving `(2.3)`. `QED`

The coordinatewise equivalence for *all* players is the checked theorem
`capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt`.  Theorem 2.1
does not claim that observer equality alone makes the whole root exact.

### Proposition 2.2 (paid-observer support wall)

At every row the paid observer satisfies the sharper alternative

```text
q_n(j) has positive Quit probability
  -> 0<q_n(j)<1, H_n=0, L_n=d_(n+1,j)>=g;               (2.4)

H_n>0
  -> q_n(j) is pure Continue.                            (2.5)
```

In particular, if `q_n` is exact against `U_n`, then `j` is pure Continue at
that root.  Any positive absorption of a transported prescribed root must be
caused by other labels.

**Proof.**  Since `d_(n+1,j)>0`, the joint Continue mass `c_n` is positive;
therefore `q_n(j)` cannot Quit surely and the opponents of `j` have positive
Continue mass.  If `q_n(j)>0`, exact cap complementarity and the positive
Continue probability make the cap Quit and Continue endpoints equal.  Lowering
only the continuation tail by the positive amount `d_(n,j)` makes Quit
strictly better at `U_n`.  The cap and literal best endpoints are both the
unchanged Quit endpoint, so `H_n=0`; `(2.1)` gives the rest of `(2.4)`.
Its contrapositive proves `(2.5)`.  Prescribed exactness gives `L_n=0`, hence
`H_n>0` by `(2.1)`, so `(2.5)` applies. `QED`

This is the quantitative actual-port version of the checked support criterion
in Section 38 of Cedar's note: active positive-debt coordinates cannot survive
cap-to-prescribed transport unless a sure quitter kills their continuation
mass.  The positive suffix-reach floor excludes that sure-kill boundary here.

### Corollary 2.3 (divergent seam ledger versus summable charge)

For every horizon `N`,

```text
sum_(n<N) (L_n+H_n) >= N g.                             (2.6)
```

Hence at least one of the two nonnegative partial-sum sequences for `L_n` and
`H_n` is unbounded (so at least one series is not summable), whereas
`sum_n a_n` converges.  In particular, for every fixed `K>0`, all sufficiently
late `n` satisfy

```text
L_n+H_n > K a_n.                                        (2.7)
```

**Proof.**  Sum `(2.1)`.  If both nonnegative component series converged,
their sum would converge, contradicting `(2.6)`.  Summability gives
`a_n->0`, while `L_n+H_n>=g>0`, proving `(2.7)`. `QED`

Thus the persistent cap/prescribed account cannot be paid from the summable
root-absorption budget by any universal linear estimate.  This is not merely
a missing constant.

## 3. Operational meaning of the literal arm

Let `tau_n` be obtained from the actual profile `sigma_(n+1)` by replacing
only player `j` at its first row by the better pure endpoint against literal
tail `U_n`, leaving the continuation and every opponent unchanged.

### Proposition 3.1 (source-matched endpoint update)

The update is a legal unrestricted behavioral deviation and

```text
Payoff_j(tau_n)-Payoff_j(sigma_(n+1)) = L_n,             (3.1)
d_j(Sem(tau_n)) = d_(n+1,j)-L_n = H_n.                  (3.2)
```

Therefore the `L_n>=g/2` arm of `(2.2)` produces an actual first-row gain and
a decrease of the marked debt by at least `g/2`.

In the stronger active-observer arm `(2.4)`, this update is immediate Quit,
its gain is at least `g`, and it clears player `j`'s own debt exactly.

**Proof.**  Stage zero has live mass one.  The checked literal-row identity
`quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
therefore gives `(3.1)`.  Updating only player `j` leaves that player's
behavioral cap invariant, so
`quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain` gives the first
equality in `(3.2)`; `(2.1)` gives the second. `QED`

This is an actual producer, but it is not the requested global descent.
Nothing in the composite controls

```text
sum_(i!=j) [d_i(Sem(tau_n))-d_(n+1,i)].                 (3.3)
```

To deduce a strict total-debt drop one needs `(3.3)<L_n`.  To deduce a
support-rank drop one needs, additionally, that the update introduces no new
positive debtor and clears `j`.  Neither statement is a field of the paid
source, reset dispatch, or cap port.  The checked elementary theorem
`complementPotential_increase_of_totalMinimum_and_subsetDrop` records the
opposite warning at a global minimum: a selected-coordinate drop must then be
repaid by complementary debt.

There is also no hidden exact Bellman edge in `(3.1)`.  The positive actual
gain changes player `j`'s root.  Since the old literal root has coordinate
defect `L_n`, preserving that root and tail cannot be exact, and any
`epsilon`-Nash repair on the same fiber must have `epsilon>=L_n`.  This is the
same complementarity calculation packaged by the checked literal-source
return no-go when a positive terminal atom is also supplied; no such atom is
silently assumed here.  Thus the literal arm is executable but not
root-Nashified.

## 4. The surcharge arm is renewable, not charge

The `H_n>=g/2` arm says that a fixed amount of player `j`'s best-response
value is visible only after replacing the literal continuation `U_n(j)` by
its cap `B_n(j)`.  It supplies no absorbing event and no strategy update.  If
`q_n` is also prescribed-Nash, `(2.3)` shows that *all* surviving debt is
exactly recycled as surcharge.

This behavior is sharp at zero charge.  In
`QuittingResetIncidenceCapRegression.positive_incidence_and_toggle_but_only_allContinue_capNash`
the checked carrier pair has prescribed/cap coordinates

```text
U=(1,0), B=(1,1),
```

positive total debt, unit reset incidence, and a supported strict toggle,
but every exact cap root is all Continue.  At that root, absorption is zero,
the positive-debt coordinate has `L=0`, and `H=d=1`.  This is not a Fin4
terminal-witness counterexample.  It is an exact counterexample to any attempt
to bound surcharge by a function of absorption which vanishes at zero.

The same elementary boundary is present whenever all Continue is exact at
both tails of a positive-debt carrier: the same debt can be reused as
continuation-option value at every row without being spent.  Consequently a
proof that merely sums root absorption, or merely repeats the reconciliation
identity, cannot eliminate the surcharge arm.

## 5. Why the three proposed discharges do not yet follow

The actual composite now yields the following exhaustive, source-matched
statement at every cap-prefix row:

```text
macroscopic legal first-row deviation
or
macroscopic renewable continuation surcharge.          (5.1)
```

It does **not** yet yield any of the requested conclusions.

1. **No well-founded global debt/support descent.**  Cap prefixing preserves
   positive-debt support exactly.  Proposition 3.1 decreases one coordinate,
   but `(3.3)` is uncontrolled and the updated profile does not regenerate
   the same paid/reset composite.

2. **No divergent-charge prescribed orbit from the selected roots.**  Even
   if every `q_n` happened to satisfy the coordinatewise surcharge equalities
   required for prescribed Nash, their absorption series is the already
   checked summable series `sum a_n`.  A divergent-charge orbit therefore
   requires a new root family or a genuine return/regeneration, not a relabeling
   of the cap orbit as a prescribed orbit.

3. **No contradiction with the terminal witness.**  In the literal arm the
   actual first-row deviation is consistent with terminal exploitability.  In
   the surcharge arm the independently shifted original paid row already
   witnesses exploitability of every finite prefix.  The witness supplies no
   inequality forcing surcharge into absorption.

The smallest missing source-changing statement is now explicit.  It would
be enough to prove one of:

```text
(A) complementaryDebtRise(tau_n)<L_n on one regenerating literal arm;

(B) a source-native consumer of H_n>=g/2 which produces positive exact
    absorption or a finite-rank support change; or

(C) an exact return/reselection that turns the one-coordinate update into a
    new paid/reset source while strictly decreasing a declared finite rank.
```

The present checked data prove none of `(A)--(C)`.  The all-Continue regression
rules out obtaining `(B)` from incidence, a supported toggle, positive debt,
and cap-Nash alone.  This is the precise stopping boundary of the cap-port
discharge attempt, rather than another supplied-data near-return verifier.

## 6. Review request

Please independently check:

1. the observer coordinate lower bound `d_(n,j)>=sigma Gamma`;
2. the exact reconciliation `(2.1)` and the distinction between joint
   Continue mass and continuation-option surcharge;
3. the stage-zero operational identities `(3.1)--(3.2)`;
4. the divergence claim versus summable absorption;
5. the all-Continue regression as a no-go for absorption-charging surcharge;
   and
6. the nonclaims about total debt, support rank, exact Bellman edges, and
   terminal-witness contradiction.
