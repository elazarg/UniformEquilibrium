# Independent falsification and novelty audit: Fin4 same-source paid/reset cap port

**Reviewer:** CODEX_EULER  
**Target:** `notes/CHATGPT_EXTERNAL__FIN4_SAME_SOURCE_PAID_RESET_CAP_PORT.md`  
**Date:** 2026-08-25  
**Verdict:** **MATHEMATICAL PASS as an immediate composition of checked Lean declarations, with two terminology repairs.  Do not create a new mathematical export.  Add a small checked bridge declaration and update the frontier/status documentation instead.**

## 1. Exact claim audited

Fix a reward table on `Fin 4`, a terminal exploitability witness `W`, and
pairwise distinct labels

```text
owner, baseFirst, baseSecond : Fin 4.
```

The proposal claims that one may choose a positive global minimum of total
terminal-semantic debt, use
`W.exists_finFour_pairBasePaidResetDispatch` to obtain one actual stationary
pair-base target, take the full-gap paid row already stored on that same
target profile, and feed it directly into `QuittingPaidCapLiftedSource`.
The generic `nonempty_summablePort` theorem should then give the cap-Nash
prefix chronology, exact debt scaling, summable absorption, a positive suffix
reach floor, shifted paid rows, and the semantic all-Continue limit port.

I checked this composition against:

- `PositiveMinimumSemanticDebt.lean`;
- `PairBaseStationaryDebtLocalization.lean`;
- `PairBasePaidResetAlignment.lean`;
- `PaidCapLiftedSummablePort.lean`;
- `formalized/PAID_CAP_LIFTED_SUMMABLE_PORT.md`;
- `formalized/PAID_ROW_EXACT_PORT_ALTERNATIVE.md`; and
- the maintained question
  `questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`.

## 2. Positive minimum from the witness

There is no missing existence premise.  The witness gives

```text
W.not_exists_uniformEquilibriumPayoff
```

and, on the inhabited type `Fin 4`,

```text
not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
```

produces

```text
minimum : QuittingTerminalSemanticPair (Fin 4)
hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward
hminimum : ∀ candidate ∈ carrier,
  DebtSum minimum ≤ DebtSum candidate
hminimumPos : 0 < DebtSum minimum.
```

Equivalently, positivity can be checked directly from
`W.terminalGap_le_terminalSemanticDebtSum` and `W.terminalGap_pos` once a
compact-carrier minimum has been selected.  Hence the composite does not need
a tangent family, a principal set, or a lasso to obtain its positive minimum.

The word **attained** needs care.  The minimum is attained in the compact
closed semantic carrier.  It need not equal the semantic pair of one actual
behavioral profile.  All checked dispatch and cap-lift declarations accept
this carrier point, so no mathematical gap results, but the packet should say
“a positive global minimum carrier point,” not “an attained behavioral
minimum.”

## 3. Arbitrary labels and the paid debtor

The hypotheses required by
`QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch`
are exactly

```text
owner ≠ baseFirst,
owner ≠ baseSecond,
baseFirst ≠ baseSecond.
```

Thus the advertised arbitrary pairwise-distinct label choice is valid.  The
returned `target : FinFourPairBasePaidResetTarget ...` uses one actual
stationary profile `target.profile` and its actual terminal law `target.mass`.
On that same profile/law it gives:

- zero debt for the preselected `owner`;
- unit opponent incidence from `baseFirst` to `owner`; and
- a selected debtor
  `d := target.localization.debtor` with
  `d ∈ {baseFirst,baseSecond}` and
  `W.terminalGap ≤ debt(target.semanticPair,d)`.

The theorem

```text
target.paid_row : Nonempty
  (QuittingPaidFirstDisagreementRow reward target.profile d W.terminalGap)
```

supplies exactly the required paid row after one classical choice.  Its gain
is `W.terminalGap`, which is positive.  No observer conversion is needed.

One label nonclaim must remain explicit: the paid observer `d` is selected
from the forced base.  It is not the preselected reset owner and is not an
arbitrarily prescribed one of the two base labels.  Since the owner is
disjoint from the base, `d ≠ owner` does follow.

## 4. Reset provenance and exact source matching

The returned fixed-law dispatch has the shape

```text
dispatch : QuittingFixedLawResetDispatch
  minimum target.semanticPair target.mass
  owner baseFirst returned.
```

Thus `target.profile` is the actual paid-row profile and the actual reset
**target/law**.  The dispatch source is the global minimum carrier point
`minimum`; the separately selected returned pair is `returned`.

This is the second terminology repair.  Calling `target.profile` the “reset
source” is ambiguous and, in the checked dispatch arguments, literally
wrong.  The valid same-source assertion is:

> one actual stationary profile is simultaneously the paid-row source, the
> cap-lift terminal suffix, and the fixed-law reset target/law.

The cap-lift sequence starts from exactly `target.profile`, not from
`returned`.  The reset dispatch itself is not inserted into the cap-prefix
chronology.  No identity between the cap-port limit and `returned` is proved.

## 5. Direct construction of the cap-lifted source

After choosing `row : QuittingPaidFirstDisagreementRow reward target.profile
d W.terminalGap`, define

```text
source : QuittingPaidCapLiftedSource reward := {
  minimum := minimum
  minimum_le := hminimum
  minimum_pos := hminimumPos
  profile := target.profile
  observer := d
  gain := W.terminalGap
  gain_pos := W.terminalGap_pos
  row := row
}
```

Every field is supplied literally.  In particular:

- `QuittingPaidCapLiftedSource` does not require a curvature witness;
- it does not require the prescribed payoff of `target.profile` to dominate
  punishment;
- it does not require the paid observer to equal the reset owner;
- it does not require `returned` or `dispatch`; and
- it does not require a new source-membership proof for the actual profile.

The dispatch is therefore valuable retained provenance but is logically dead
input for `source.nonempty_summablePort`.  This is not a defect; it precisely
shows that the generic cap lift accepts the same profile already produced by
the reset alignment theorem.

## 6. Floors and unrestricted behavioral semantics

The floor claim is correctly located on the cap annotations.  At prefix
depth `n`, the Bellman value is the all-behavior envelope

```text
B(quittingCapLiftedPrefixProfile reward target.profile n).
```

The checked theorem
`quittingPunishmentValue_le_terminalSemanticEnvelope` puts this envelope
above every behavioral punishment value.  The chosen root is exact Nash
against that envelope, so the cap values form an exact punishment-floor
infinite Nash--Bellman orbit.

This does **not** prove that the prescribed payoff
`U(target.profile)` is floor-safe.  The parallel literal chronology carries
the paid rows on its prescribed coordinates, while the floor relation uses
the cap coordinates.  This separation is the central content of the already
formalized cap-lift theorem and must not be collapsed in the composite.

The paid-row construction and debt coordinates use unrestricted unilateral
behavioral best responses.  Prefixing is by simultaneous product roots;
there is no public correlating device or restricted controller class.

## 7. Quantitative port output

Write

```text
D_* = DebtSum minimum,
D_n = DebtSum(Sem(prefixProfile n)),
c_n = stationaryContinueMass(prefixRoot n),
alpha_n = rootAbsorptionMass(prefixRoot n) = 1-c_n.
```

The checked declarations give, exactly,

\[
D_{n+1}=c_nD_n,
\qquad
D_N=D_0\prod_{n<N}c_n. \tag{7.1}
\]

Theorems `minimum_mul_partialAbsorption_le_debtDrop` and
`debtDrop_le_initial_sub_minimum` give

\[
D_*\sum_{n<N}\alpha_n
 \le D_0-D_N
 \le D_0-D_*. \tag{7.2}
\]

The source theorem `reachFloor_le_suffixReach` gives

\[
\prod_{n<N}c_n\ge D_*/D_0>0. \tag{7.3}
\]

Therefore absorption is summable.  For every finite depth, the original
paid witnesses shifted past the outer roots yield a paid row on the literal
prefix profile with gain at least

\[
(D_*/D_0)\,W.terminalGap. \tag{7.4}
\]

The observer remains `d`.  The live-mass scaling uses the observer-deleted
outer survival, which is at least joint survival; it is not identified with
root charge.

Finally `nonempty_summablePort` gives both the exact floor-safe cap
all-Continue port and convergence of the actual terminal-semantic pairs to an
all-Continue fixed semantic carrier point.  Every finite prefix literally
retains `target.profile` as a suffix with reach bounded by (7.3).  The limit
is not a behavioral profile which begins that suffix after infinitely many
dates.

The note uses `q_n` for joint Continue mass.  Since the checked source also
uses `q_n` informally for the entire root, formalization should call this
scalar `c_n` or `continueMass_n` to avoid a type ambiguity.  The displayed
identities themselves are correct.

## 8. Falsification and boundary checks

I found no missing adapter premise.  The following apparent failures are
already handled by the exact scope:

1. **Prescribed floor failure:** harmless, because the cap orbit—not the
   prescribed profile chronology—is placed in the floor relation.
2. **Paid debtor differs from owner:** harmless for the generic cap source;
   it stores an arbitrary observer.  It matters only for downstream consumers
   and must remain recorded.
3. **Minimum not behaviorally attained:** harmless; both the reset dispatcher
   and cap source accept a carrier minimum.  It forbids calling the minimum an
   actual profile.
4. **Reset returned pair differs from paid target:** harmless for the cap
   lift, but the port does not repair that chronology or make a return.
5. **Zero minimum:** excluded by `W.not_exists_uniformEquilibriumPayoff` and
   the checked positive-minimum equivalence.
6. **Zero initial target debt:** impossible because `D_*>0` and global
   minimality give `D_0>=D_*>0`; independently the paid debtor carries the
   full terminal gap.
7. **Arbitrary labels:** valid only in the stated pattern—arbitrary reset
   owner and arbitrary disjoint unordered base, with the actual paid debtor
   subsequently selected inside that base.

## 9. Novelty and “Gap 1 closed” verdict

No named theorem combining these two modules was found.  Nevertheless, there
is no new mathematical lemma in the composite:

- `PairBasePaidResetAlignment.lean` already produces the one actual profile
  and law carrying reset-owner data and the paid row;
- `PaidCapLiftedSummablePort.lean` already accepts **any** attained paid
  profile/row plus a positive global minimum and produces the full port; and
- `formalized/PAID_CAP_LIFTED_SUMMABLE_PORT.md` already records the debt,
  reach, shifted-row, floor, and convergence conclusions.

Thus “Gap 1 closed” is accurate only if **Gap 1** is defined narrowly as:

> align one pair-base fixed-law reset target with the attained paid profile
> used as the cap-lift suffix.

At that interface level the answer is genuinely yes, for every allowed label
triple, and it bypasses any hard-principal/lasso selection that was being used
solely to obtain this co-realization.

It is not a new frontier theorem relative to the combined checked corpus; it
is an omitted bridge/status consequence.  It does not close the maintained
paid route, because it supplies none of:

- a restart of the summable port;
- a positive cumulative-charge payoff near-return;
- an exact paid Bellman edge;
- a chronological use of the fixed-law reset dispatch inside the cap orbit;
- identification of `returned` with a cap-prefix state or the port limit;
- total-debt/support descent; or
- a uniform-equilibrium payoff.

The current question already names the downstream “same-source paid-port
discharge” as open.  That remains the exact live obligation.

## 10. Recommendation

**Do not assemble a new export packet.**  It would duplicate two already
formalized results and fail the export queue's source-novelty requirement.
The mathematically useful action is to add one short checked bridge theorem,
probably in a file importing both
`PairBasePaidResetAlignment.lean` and
`PaidCapLiftedSummablePort.lean`, and then update `docs/FRONTIER.md` and
`questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md` to record the exact narrow
alignment consequence.

A suitable checked wrapper should retain, in one dependent structure or
existential package:

1. `minimum`, its carrier membership, global minimality, and positivity;
2. `target`, `returned`, and the fixed-law `dispatch`;
3. the selected debtor `d`, `d ∈ {baseFirst,baseSecond}`, and the chosen
   `target.paid_row`;
4. the explicitly constructed `QuittingPaidCapLiftedSource` whose profile is
   definitionally `target.profile`; and
5. one `QuittingPaidCapLiftedSource.SummablePort` for that source.

The finite quantitative equations need not be duplicated as structure
fields: they are already theorem methods of the retained cap source.  The
wrapper's value is exact provenance and discoverability, not new proof
content.

After the two terminology repairs—carrier-attained minimum, and reset
target/law rather than reset source—the composite is fully correct.
