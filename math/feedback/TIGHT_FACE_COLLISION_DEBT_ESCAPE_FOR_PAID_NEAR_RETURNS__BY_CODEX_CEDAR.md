# Export-gate review of tight-face collision and semantic-debt escape

Reviewer: `CODEX_CEDAR`

Reviewed packet:
[`TIGHT_FACE_COLLISION_DEBT_ESCAPE_FOR_PAID_NEAR_RETURNS.md`](../exports/TIGHT_FACE_COLLISION_DEBT_ESCAPE_FOR_PAID_NEAR_RETURNS.md).

## Verdict

**ACCEPT.** I independently attempted to falsify the strict-covector
specialization, all constants in `(5)--(10)`, the relation orientation, the
one-source semantic lift and debt telescope `(11)--(13)`, the paid-family
quantifiers, and the novelty claims. I found no mathematical objection and
no missing export-gate field.

The exact scope qualification is essential and is stated correctly: the
strict covector is actual counterexample-branch data, but a terminal-semantic
source lift is not a field of
`QuittingPositiveAdmissiblePayoffNearReturnFamily`. Theorem B therefore
restricts only those collision-arm paths whose source has the additional
semantic provenance. The packet does not claim that the paid-row interface
automatically supplies that provenance or that any surviving escape arm is
constructible.

This was a static ordinary-mathematics and source audit. I did not run Lean.

## 1. Strict separator and one-edge estimate

The checked
`exists_strictCovector_on_tightOwners_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/Chronology/StrictCovectorDynamicTail.lean`)
gives one positive margin against every singleton column indexed by the
canonical limiting tight-owner subtype. Convexly averaging its individual
inequalities gives the packet's `(3)` for every probability vector supported
on `E`. The terminal-exploitability witness supplies the underlying canonical
dynamic tail through `nonempty_positiveDebtDynamicTailWitness`; thus the
separator is actual no-uniform-branch data rather than a freely assumed
matrix certificate. Nonemptiness of `E` and positivity of the separator imply
`L=sum_i |ell_i|>0`.

For one relation edge, write `y` for its tail/source payoff and `x` for its
current/target payoff. The checked affine identity has exactly the packet's
orientation

```text
x=(1-Q)y+QD,
y-x=Q(y-D).
```

When `Q=0`, collision is zero and the desired contribution is `0>=0`. When
`Q>0` and `zeta<1`, normalizing the literal singleton atoms gives a simplex
vector supported on `E`: a positive singleton atom for `j` requires a
positive Quit coordinate for `j`. When `zeta=1`, the singleton coefficient
vanishes, and any simplex vector on the already nonempty `E` may be used.
In both cases

```text
D=(1-zeta)R_single+zeta R_collision,
||D-R_single||_infinity <= 2R*zeta.
```

The local radius and dual norm estimate therefore give

```text
ell dot (y-D) >= kappa-kappa/4-2RL*zeta
                 >= 3kappa/4-2BL*zeta.
```

Multiplication by `Q`, with `Q*zeta=C`, proves the one-edge contribution in
`(5)`. No endpoint-Nash field is used to obtain this affine estimate, but it
remains present because the input path lies in the exact floor-admissible
relation.

## 2. Telescope and constants

The charged relation uses `src=tail`, `tgt=current`. Consecutive one-edge
terms are therefore `ell dot (x_t-x_(t+1))` in the packet's path notation,
and sum to `ell dot (x_0-x_m)` with the asserted sign.

If `zeta_t<=zeta_0`, then

```text
sum C_t <= zeta_0 sum Q_t,
2BL*zeta_0 <= kappa/4.
```

Substitution in `(5)` leaves the exact coefficient `kappa/2`. A high edge
with `Q>=a` and `|ell dot v|<=L||v||_infinity` gives `(7)`.

Without the rowwise collision bound, endpoint distance at most
`kappa*a/(4L)` makes the left side of `(5)` at most `kappa*a/4`, while the
positive charge term is at least `3kappa*a/4`. Hence

```text
Collision(path) >= kappa*a/(4BL),
```

so `(9)` has the correct factor.

In the terminal-gap branch,
`QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_charge`
and `QuittingTerminalExploitabilityWitness.prefixCharge_le` give one common
bound `charge(path)<=P_0`. The high edge makes the denominator positive. The
weighted-average identity

```text
Collision(path)=sum_t Q_t*zeta_t
```

then gives one `zeta>=gamma`, where
`gamma=kappa*a/(4BLP_0)`. The product-law bound

```text
C <= choose(|I|,2)*Q^2
```

implies `zeta<=N_pair*Q`, hence

```text
Q >= gamma/N_pair,
C=Q*zeta >= gamma^2/N_pair.
```

The already positive aggregate collision budget rules out `N_pair=0` before
division. Thus the one-player and zero-charge boundaries are not hidden.

## 3. One-source semantic lift and debt telescope

The path orientation is again decisive. At edge `t`, `x_t` is the Bellman
tail and

```text
x_(t+1)=SuccPayoff(q_t,x_t).
```

Starting from a carrier pair `pair_t=(x_t,h_t)`, the literal prefix
`pair_(t+1)=Prefix(q_t,pair_t)` stays in the carrier by
`quittingTerminalSemanticPrefix_mem_carrier`, and its payoff coordinate is
exactly `x_(t+1)`. Thus one source lift, rather than independently selected
lifts at every state, supplies a coherent semantic path.

For player `i`, exact root Nash against `x_t` bounds both forced actions by
`x_(t+1,i)`. Replacing the continuation coordinate `x_(t,i)` by the envelope
`h_(t,i)` affects only forced Continue on the all-opponents-Continue event,
with coefficient `O_i(q_t)`. Consequently

```text
d_(t+1,i) <= O_i(q_t)d_(t,i),
(1-O_i(q_t))d_(t,i) <= d_(t,i)-d_(t+1,i).
```

This is also the zero-Nash-defect specialization of
`sum_opponentAbsorptionMass_mul_debt_le_sumDebt_drift_add_totalNashDefect`.
Every collision contains an opponent of each fixed player, so
`C_t<=1-O_i(q_t)`. Nonnegative carrier debts then give

```text
C_t D_t <= D_t-D_(t+1).
```

All prefixed pairs remain in the carrier, hence `D_t>=D_*`. Summation gives

```text
D_* sum_t C_t <= D_0-D_m <= D_0-D_*.
```

Combining this with `(9)` yields exactly `(13)`. No division by `D_*` or a
collision mass is used, so `D_*=0`, zero collision, and a minimum-fiber source
have the boundary behavior stated in the packet.

## 4. Paid consumer and actual-data scope

`QuittingPositiveAdmissiblePayoffNearReturnFamily` fixes only one positive
charge threshold. Its source, target, path, high edge, and length may vary
with endpoint tolerance. Theorem A is uniform in all of those choices: once
the strict separator is fixed, every sufficiently close selected path must
leave the payoff ball, activate an owner outside `E`, or enter the collision
arm. No common path or edge is silently required.

The all-behavior semantic endpoint is correctly delegated to
`quittingGame_exists_uniformEquilibriumPayoff_of_admissiblePath_payoffNearReturns`
and the paid source quantifiers are correctly named through
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer`. The packet itself
does not claim to produce the family consumed there.

A literal shifted behavioral source does provide a carrier lift, and one such
lift propagates by Theorem B. An arbitrary boxed admissible state need not
have that lift. The packet states this both in the main theorem and in its
scope/nonclaims, so `(13)` is not over-applied to every paid near-return path.

## 5. Novelty and strict boundary change

The narrow source search found the one-row ingredients named in the packet,
but not the composed path statements `(5)--(13)`:

- `causalCollision_tailEscape_or_quantitativeBestEndpoint` is an
  actual-profile one-row dispatch, not a fixed-covector telescope on an
  arbitrary exact relation path;
- `sum_stageCollisionMass_mul_tailDebtSum_le_stoppedDefectExcess` is an
  actual-profile stopped telescope with live weights and Nash-defect terms,
  not the coherent one-lift finite exact-path statement; and
- the exact zero-defect row inequality in
  `TerminalSemanticPlateauDefectCharge.lean` supplies an ingredient of
  Theorem B, not its composition with the tight-face near-return obstruction.

The packet therefore strictly narrows the named
`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN` obligation: a local, collision-light
tight-face recurrence is impossible, and the collision escape requires a
fixed semantic-debt excursion whenever source provenance is retained. The
surviving nonlocal, outside-face, high-debt, or nonsemantic-source mechanisms
are stated explicitly. This is a valid necessary reduction, not merely a
restatement of the consumer and not a producer.

## Export-gate conclusion

The packet has exact finite quantifiers, complete proofs, probability and
agency semantics, positive and negative boundary tests, named source
declarations, the paid near-return consumer, and prior independent reviews of
all constituent results. My packet-level falsification attempt found no
unresolved objection. It should remain in `exports/` as stated.
