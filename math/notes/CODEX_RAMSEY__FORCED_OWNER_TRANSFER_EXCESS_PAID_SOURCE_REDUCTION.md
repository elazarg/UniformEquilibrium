# Forced-owner transfer excess has a source-native paid witness

Author: `CODEX_RAMSEY`

Status: **reviewed ordinary-mathematics theorem; REVISE -> PASS; internal**.
The theorem restores a literal source packet and quantitatively
controls the off-minimum excess in the mover-dominated transfer arm.  Its
checked downstream output is debt descent or paid inertness, not yet a
FIN4_BT conclusion.

This note continues Proposition 8.1 of
[`CODEX_MINER__SIGNED_CAUSAL_RECTANGLE_ORIENTATION_COMPILER_BOUNDARY`](CODEX_MINER__SIGNED_CAUSAL_RECTANGLE_ORIENTATION_COMPILER_BOUNDARY.md)
and the independently reviewed root localization in
[`CODEX_MINER__FIN4_FORCED_OWNER_TRANSFER_ROOT_LOCALIZATION`](CODEX_MINER__FIN4_FORCED_OWNER_TRANSFER_ROOT_LOCALIZATION.md).
The common-chord minimum-fiber consumer is separately reviewed in
[`CODEX_EULER__MAXIMUM_SUPPORT_COMMON_CHORD_EXCHANGE_COLLAPSE`](CODEX_EULER__MAXIMUM_SUPPORT_COMMON_CHORD_EXCHANGE_COLLAPSE.md).

## 1. Question and result

Let `a` be surely quitting at one actual Fin4 root, and suppose the forced-
owner outsider defect at that root is `F>0`.  The checked half-endpoint
adapter selects an outsider `w!=a` with root defect exactly `F`, changes only
`w` halfway toward its best endpoint, and gives either strict total-debt
descent or aggregate opponent transfer.

The selected normalized source need not be near the positive global minimum.
Nevertheless its excess is not anonymous.  The source itself carries a paid
first-disagreement row whose charge is at least one eighth of its total debt,
and hence at least one eighth of its excess over the global minimum.  More
precisely:

- if the sure owner's source debt exceeds `F`, the paid row belongs to the
  owner;
- otherwise it belongs to the same mover `w`, and in the transfer arm the
  transfer is at least one sixteenth of the source excess.

Thus the forced-root transfer survivor is not merely a static debt edge.  It
regenerates a literal source-matched paid-cap packet.  The checked paid-cap
trichotomy then gives charged return, quantitative cap-debt descent, or inert
stall; a terminal exploitability witness excludes charged return.  No current
theorem excludes the remaining inert arm.

There is also a sharper full-endpoint fork. Moving `w` all the way to the
same best endpoint either strictly decreases total debt or satisfies the
checked, same-source full transfer inequality for debtor `w`. Since the
sure-quitting owner `a!=w` occurs in every terminal outcome, the source law
has unit opponent-containing mass for `w`. In the non-descent branch the
checked Fin4 transfer theorem therefore returns either matched
recipient/incidence or the exact two-opponent separator. This removes the
half-reset's factor loss and resolves its incidence ambiguity into that
checked dichotomy, but still supplies no sign turning either output into a
Nash--Bellman edge.

## 2. Exact local theorem

Let the player type be `Fin 4`, let `reward` be any quitting reward table,
and let

```text
root : Fin 4 -> PMF Bool,
continuation : (quittingGame reward).BehaviorProfile,
a : Fin 4,
root a = PMF.pure true.
```

Put

```text
Sprof = quittingRootThenContinuationProfile reward root continuation,
S     = quittingTerminalSemanticPair reward Sprof,
F     = quittingForcedOwnerOutsiderDefect reward root a.
```

Assume `F>0`.  Choose `w!=a` attaining `F`, let `action` be its best endpoint,
and let `Hprof` be the literal half-endpoint update at that root.  Write

```text
g = F/2,
R = sum_(j!=w) (d_j(H)-d_j(S)).
```

Then:

1. `d_w(S)=F` and `d_w(H)=d_w(S)-g`.
2. Either

   ```text
   D(S)-D(H)>g/2,                                      (2.1)
   ```

   or `R>=g/2`.
3. In both alternatives there are a label `k` in `{a,w}` and a literal
   `QuittingPaidFirstDisagreementRow reward Sprof k p` with

   ```text
   p = max(F,d_a(S))/2 > 0,
   D(S) <= 8p.                                        (2.2)
   ```

   Consequently, for every positive global-minimum reference `X_*`,

   ```text
   D(S)-D_* <= 8p.                                    (2.3)
   ```

4. In the transfer arm, if `d_a(S)<=F`, one may take `k=w`, `p=g`, and

   ```text
   D(S)-D_* <= 8g <= 16R.                             (2.4)
   ```

5. Let `E` be the semantic pair after the full best-endpoint update of the
   same `w`. Then either `D(E)<D(S)`, or the exact source/target/law data
   satisfy the hypotheses of the checked Fin4 matched-incidence versus
   two-opponent-separator theorem, with debtor `w` and receiver lower bound
   `F/3` in the separated branch.

All profiles and rows are literal.  No compact representative or
independently selected singleton-base source replaces `Sprof`.

## 3. The sure-owner debt identity

Because `a` Quits surely,

```text
quittingStationaryContinueMass root = 0.
```

The exact arbitrary-root recursion
`quittingTerminalDeviationDebt_rootThenContinuation_eq_capDefect_add_continueMass_mul`
therefore gives, for every player `i`,

```text
d_i(S)=quittingRootCoordinateNashDefect reward B(continuation) root i.
                                                               (3.1)
```

For `i!=a`, the tail term is killed already at date zero.  The checked
`quittingRootCoordinateNashDefect_eq_forcedOwnerGain` identifies `(3.1)`
with the corresponding forced-owner one-stage coordinate defect.  Hence

```text
0<=d_i(S)<=F                  for every i!=a.          (3.2)
```

Choose `w` at the maximum.  The existence theorem
`exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge`, invoked
with `eta=F`, and
`quittingForcedOwnerOutsiderCoordinateDefect_le` give equality:

```text
d_w(S)=F.                                             (3.3)
```

The partial-best-endpoint payoff identity and own-envelope invariance give

```text
d_w(H)=d_w(S)-F/2.                                    (3.4)
```

Summing coordinate changes yields the exact account

```text
D(H)-D(S)=-g+R.                                       (3.5)
```

Splitting at `R=g/2` proves item 2.  Notice that retaining `R>=g/2`, rather
than weakening it immediately to the packet's uniform `q/8` floor, is what
makes the source-excess comparison in `(2.4)` possible.

## 4. Paid-row construction and the factor eight

Let `h=d_a(S)`.  There are only three outsiders in Fin4, so `(3.2)` gives

```text
D(S)<=h+3F.                                           (4.1)
```

Set `p=max(F,h)/2`.  Then `h<=2p` and `F<=2p`, whence

```text
D(S)<=2p+6p=8p.                                       (4.2)
```

It remains to attach the scalar `p` to a literal row on `Sprof`.

### 4.1 Mover-dominated case

If `h<=F`, then `p=F/2=g`.  At a sure-owner root, `w`'s two deterministic
date-zero endpoint payoffs are its entire unrestricted choice: Continue is
equivalent to `Never`, since `a` terminates the play immediately.  The
selected endpoint is the better one.  Since the prescribed root payoff is a
convex combination of the two endpoints and its defect is `F`, the oriented
endpoint payoff difference is at least `F`, hence at least `p`.

Use `some 0` and `none` in the profitable orientation in
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`.  This gives
a literal paid row on `Sprof` for `w` with gain `p`.  In the transfer arm,
`R>=g/2`, and `(4.2)` gives

```text
D(S)-D_*<=D(S)<=8g<=16R.
```

The row observer is exactly the half-reset mover.

### 4.2 Owner-dominated case

If `F<h`, then `p=h/2`.  The source prescribes `a` to Quit at date zero, so
its payoff is the pure-time payoff at `some 0`.  Its unrestricted debt is
`h`, and
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`
gives a deterministic pure time whose payoff exceeds the source payoff by
`h/2`.  Pair that time with `some 0` and apply the same first-disagreement
decoder with gain `p`.

This row is again on the exact forced source.  Its observer is `a`, not the
half-reset mover; this is the honest price of allowing the owner's suffix
deviation debt to dominate the source excess.

Together the two cases prove `(2.2)--(2.4)`.

## 5. Checked paid-cap consumer

Let `X_*` be a positive global minimum carrier point.  The row just built,
together with `X_*`, packages a `QuittingPaidCapLiftedSource` whose profile is
literally `Sprof`, whose gain is `p`, and whose observer is the selected
`k in {a,w}`.  The checked `nonempty_summablePort` and `exactTrichotomy`
give

```text
ChargedNearReturn or QuantitativeDebtDescent or InertStall.     (5.1)
```

If a terminal exploitability witness is present, `ChargedNearReturn` is
impossible because it stores a uniform-equilibrium payoff.  Thus the exact
consumer output is

```text
QuantitativeDebtDescent or InertStall.                          (5.2)
```

In the mover-dominated transfer arm this consumer is attached simultaneously
to:

- the original forced source;
- the same mover as the half reset;
- a paid row of gain `g`;
- the literal half-reset target; and
- the normalized bound `D(S)-D_*<=16R`.

This is stronger than merely decoding an endpoint recipient atom.  It still
does not turn that atom into a recipient deviation, and a cap-inert port has
zero Nash--Bellman charge despite the source-native paid row.

### 5.1 The full endpoint supplies the checked transfer hypothesis

Let `Eprof` be the literal update of `w` all the way to the same selected best
endpoint and let `E` be its semantic pair. The sure-owner debt identity still
applies, while `w` now plays a maximizing endpoint. Hence

```text
d_w(E)=0.                                                   (5.3)
```

Writing

```text
R_full = sum_(j!=w) (d_j(E)-d_j(S)),
```

the exact coordinate account is

```text
D(E)-D(S)=-F+R_full.                                       (5.4)
```

Consequently either `D(E)<D(S)`, a literal strict total-debt descent, or

```text
d_w(S)=F <= R_full.                                        (5.5)
```

Define the literal source mass by

```text
mass := quittingTerminalOutcomeMass reward Sprof.
```

It lies in the standard simplex by
`quittingTerminalOutcomeMass_mem_stdSimplex`. Because `a` Quits surely at
date zero with `a!=w`, this mass has no `none` outcome and every
positive-mass terminal coalition contains `a`. Thus

```text
quittingTerminalOpponentContainingMass w mass=1.           (5.6)
```

In the second branch `(5.5)--(5.6)` are literally the transfer and incidence
hypotheses of
`exists_matched_transfer_incidence_or_twoOpponent_separator`; under the
terminal witness, the Fin4 wrapper
`exists_matched_transfer_incidence_or_twoOpponent_separator_fourPlayers`
applies. It yields either a recipient whose positive debt change and positive
source-law incidence use the same label, or distinct receiver and incidence
labels. Since `card(univ.erase w)=3` for `Fin 4`, the latter receiver's change
is at least `F/3`.

This is a checked geometric consumer of the full endpoint, not a
re-extraction. It does **not** say that the recipient's terminal reward sign
is profitable, that the endpoint is on the minimum fiber, or that either
separator branch is iterable from `Eprof`.

## 6. Why this does not yet close the transfer survivor

The result removes two possible ambiguities:

1. the forced normalized source has a paid event of controlled size on its
   own literal law; and
2. when the mover rather than the owner dominates, the off-minimum excess is
   controlled by the same aggregate transfer.

What remains is exact.  `QuantitativeDebtDescent` is a genuine strict
cap-orbit debt decrease, but its size is not bounded below by `p` or `R` and
its limit need not reach the global minimum fiber.  In `InertStall`, all
selected cap roots are all Continue; the paid row and the half-reset edge
survive only as prescribed-payoff/deviation data, not as a positive-charge
Nash--Bellman edge.  The endpoint-recipient sign is still an externality.

Accordingly this note does **not** claim a finite transfer cycle, a support
rank decrease, a prescribed-payoff exact return, or a uniform payoff.  The
strictly smaller remaining obstruction is:

```text
a source-native paid inert stall with charge p >= (D(S)-D_*)/8,
and, in the mover-dominated arm, a co-realized half-reset transfer
R >= (D(S)-D_*)/16 whose recipient sign is not executable.       (6.1)
```

Equivalently, using the full endpoint, the residual is strict total-debt
descent or a checked matched-incidence/two-opponent separator on the literal
source law. Existing compilers still require a profitable oriented row or a
regenerated near-minimum source; neither follows from positive debt change
and incidence alone.

## 7. Source and novelty audit

Declarations inspected:

- `quittingStationaryContinueMass_eq_zero_of_owner_eq_pure` in
  `Quitting/Boundary/Repair/AtomicBlockerPaidGeometry.lean`;
- `quittingTerminalDeviationDebt_rootThenContinuation_eq_capDefect_add_continueMass_mul`
  in `Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`;
- `quittingRootCoordinateNashDefect_eq_forcedOwnerGain` and
  `exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge` in
  `Diagnostics/Quitting/TerminalSemanticAtomicBlockerResetAdapter.lean`;
- `quittingForcedOwnerOutsiderCoordinateDefect_le` in
  `Quitting/Boundary/Repair/AtomicBlockerPaidGeometry.lean`;
- `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`
  in `Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean` and
  `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
- `QuittingStoppingLawCurvaturePaidWitness.nonempty_capLiftedSummablePort`
  and, more primitively, `QuittingPaidCapLiftedSource.nonempty_summablePort`
  in `StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`; and
- `QuittingPaidCapLiftedSource.exactTrichotomy` in
  `StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`;
- `exists_matched_transfer_incidence_or_twoOpponent_separator` in
  `Diagnostics/Quitting/TerminalSemanticPlateauDebtTransfer.lean`; and
- `exists_matched_transfer_incidence_or_twoOpponent_separator_fourPlayers`
  in `Diagnostics/Quitting/Collision/DebtTransferCardinality.lean`.

The generic fact that a large total debt has a large coordinate is not new.
The useful new alignment is specific to the forced-owner source: the only
two candidate paid labels are the forced owner and the exact half-reset mover;
in the mover-dominated branch the literal paid row, reset edge, and excess-
to-transfer estimate are all co-realized.

Independent review:
[`CODEX_EULER`](../feedback/CODEX_RAMSEY__FORCED_OWNER_TRANSFER_EXCESS_PAID_SOURCE_REDUCTION__BY_CODEX_EULER.md),
verdict **REVISE -> PASS** after the two exposition repairs incorporated
above. The audit independently checked `(3.1)--(3.5)`, both pure-time rows,
constants `8` and `16`, the paid-cap trichotomy, and the full-endpoint
identities and Fin4 transfer invocation.
