# Rank-one paid/tangent label non-identification

Author: `CODEX_RAMSEY`

Status: **internal negative screen.**  The checked Fin4 data do not identify
the full-gap paid label with either the unique minimum-debt reset mover or a
positive tangent recipient.  For the curvature-paid row, the reset mover is
already shared by construction, but the paid curvature observer need not be
a positive tangent recipient.  This note records the two distinct seams and
stops; it proves no new consumer, descent, or uniform payoff.

Primary boundary:
[`PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL.md`](../exports/PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL.md).
The inert arm keeps the cap roots all Continue and transports the paid row,
but adds no new label equality.

## 1. Exact question and the two meanings of “paid row”

Fix a Fin4 quitting table with a terminal exploitability witness and a
positive-minimum tangent family `frontier`.  Suppose

```text
frontier.positiveDebtSupport = {e}.
```

Then `e` is the only possible tangent/reset mover.  The checked diagonal
estimate makes its tangent entry strictly negative, while
`QuittingPositiveMinimumDebtTangentFamily.exists_positiveOffDiagonal`
selects some `r != e` with

```text
t_e(e)<0,                 t_e(r)>0.                    (1.1)
```

There are two different paid objects in the current route.

1. `exists_eventually_paidFirstDisagreement` in
   `StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean` changes the same
   stopping law of mover `e` and produces a paid first-disagreement row for
   a curvature observer `o != e`.  Thus its **mover is already `e` by
   construction**.  The open identification is `o=r`.
2. `FinFourSameSourcePaidResetCapPort` carries the independent full-terminal-
   gap row produced by pair-base stationary debt localization.  Its row has
   one self-deviating observer/debtor `j`; the structure
   `QuittingPaidFirstDisagreementRow` stores no second external mover.  The
   checked field is only

   ```text
   j in {baseFirst,baseSecond}.                         (1.2)
   ```

   This full-gap row is not the curvature row merely because both are called
   paid.

## 2. Curvature observer need not be a positive tangent recipient

For an off-minimum full-replacement cluster, write `t` for the mover column
and `c` for its nonnegative curvature.  The checked identities used by the
paid decoder are

```text
c_i >= 0,               c_e=0,
dC_i=d0_i+t_i+c_i,
sum_i c_i=D(C)-D(B0)>0.                                (2.1)
```

Rank one adds `d0_e>0`, `d0_i=0` for `i!=e`, and inactive-coordinate
nonnegativity gives `t_i>=0` for `i!=e`.  None of these assertions says that
the positive supports of `t` and `c` intersect.

The following exact four-coordinate account is a minimal countermodel to
that proposed implication:

```text
labels:       e=0, r=1, o=2, p=3,
d0:           (1, 0, 0, 0),
t_e:          (-1, 1, 0, 0),
c:            (0, 0, 1, 0),
dC=d0+t_e+c:  (0, 1, 1, 0).                            (2.2)
```

It has flat tangent sum, the exact negative diagonal, nonnegative inactive
tangents, zero mover curvature, nonnegative endpoint debt, and endpoint
excess `D(C)-D(B0)=1=sum c`.  The unique positive tangent recipient is `r`,
whereas the unique observer satisfying the curvature-average lower bound
`c_o >= 1/3` is `o`.  Hence the checked numerical hypotheses can force
`o != r` even on Fin4 and at rank-one minimum support.

This is a counterexample to the **interface implication**, not a constructed
quitting table or a counterexample to the uniform-equilibrium conjecture.
No existing regression file was found that realizes all of `(2.2)` together
with a Fin4 terminal witness.  The checked two-player regression
`FlatRecipientIncidenceRegression.simultaneous_flatPassport_recipient_without_incidence`
independently confirms the same general warning: a positive debt recipient
of an actual flat reset need not carry the desired co-realized law incidence.

The precise missing curvature lemma is therefore

```text
exists o != e, 0<t_e(o) and 0<c(o).                    (2.3)
```

Neither rank one, Fin4 cardinality, flatness, nor endpoint separation proves
`(2.3)`.  A strategic relation between tangent transfer and curvature—not
another averaging argument—is required.

## 3. The checked Fin4 full-gap producer permits explicit anti-alignment

The full-gap row is even less constrained.  The exact theorem
`QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch`
accepts:

```text
* any supplied positive global minimum;
* any prescribed reset owner; and
* any distinct two-player base disjoint from that owner.
```

Given the rank-one labels `e` and `r` from `(1.1)`, let `{b1,b2}` be the two
remaining Fin4 labels:

```text
{b1,b2}=univ\{e,r}.
```

Apply the theorem with reset owner `e` and base `{b1,b2}`.  The resulting
actual stationary target has:

```text
debt_e(target)=0,
Inc_(e,b1)(target law)=1,
a full-gap row for j,
j in {b1,b2}.                                           (3.1)
```

Consequently

```text
j != e and j != r.                                     (3.2)
```

The generic `FinFourPairBasePaidResetTarget.capLiftedSource` and its
`nonempty_summablePort` retain this exact row.  If that selected port lands
in the inert all-Continue arm, the exported trichotomy shifts and preserves
the same row; it does not change `(3.2)`.

Thus the checked producer itself gives a conditional, same-table
anti-aligned selection.  This does **not** prove that the inert arm actually
occurs under the complete ambient hypotheses.  It proves that occurrence of
that arm would not retroactively identify its independently selected
pair-base paid label with `e` or `r`.

Choosing a base containing `e` does not repair the issue: localization only
says that `j` is one of two base labels, not which one.  Choosing a base
containing `r` has the same defect.

## 4. Why reselecting the terminal-gap debtor does not close the seam

At actual tangent sources converging to a rank-one base, continuity makes
every inactive player's semantic debt tend to zero.  Since the terminal-gap
deviation has fixed positive gain, sufficiently late re-extraction localizes
its debtor to `e`.  This produces a new full-gap row whose self-deviating
observer is `e`.

That observation is not the needed co-realization.  The newly extracted row
belongs to the chosen tangent source.  It does not retain the old pair-base
law, unit incidence, fixed-law returned point, curvature observer, or inert
cap-port chronology.  Replacing the inherited row by it is exactly the
source-reselection step whose provenance is missing.

The finite separator theorem
`exists_matched_transfer_incidence_or_twoOpponent_separator` in
`TerminalSemanticPlateauDebtTransfer.lean` gives the same boundary in a
different language: a positive transfer recipient either meets positive
same-law incidence, or distinct receiver and quitter labels witness the
separator.  Only cardinality at most two rules out the separator.  Fin4 does
not.

## 5. Verdict and minimal missing implication

**Verdict: NO forced label coincidence from the checked data.**

For the curvature-paid row, the mover/reset-owner equality is definitional;
the unproved step is the positive-support intersection `(2.3)`.  For the
pair-base full-gap row, even the observer equality fails: the arbitrary-base
Fin4 constructor permits `(3.2)`.

Any useful closing result must add at least one genuinely source-matched
statement:

```text
* the curvature-paid observer has positive tangent, or
* the inherited full-gap observer equals the unique minimum debtor, or
* the two-opponent separator is consumed by a charged/floor-safe compiler.
```

The current declarations establish none of these.  This is the minimal
label-identification obstruction; no further label-only alignment is pursued
here.

## Sources inspected

- `StoppingLaw/OffDiagonal/SlopeFrontier.lean`:
  `exists_positiveOffDiagonal`, `oneDebtOwner_dichotomy`;
- `StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean`:
  `FullReplacementCluster.curvature`,
  `exists_curvature_ge_opponentAverage`, and the paid-row decoder;
- `Collision/SingletonPacket/PairBaseStationaryDebtLocalization.lean`;
- `Collision/SingletonPacket/PairBasePaidResetAlignment.lean`:
  `nonempty_finFourPairBasePaidResetTarget` and
  `exists_finFour_pairBasePaidResetDispatch`;
- `StoppingLaw/Endpoint/FinFourSameSourcePaidResetCapPort.lean`;
- `TerminalSemanticPaidFirstDisagreement.lean`;
- `TerminalSemanticPlateauDebtTransfer.lean`; and
- `TerminalSemanticSimultaneousRecipientIncidenceRegression.lean`.
