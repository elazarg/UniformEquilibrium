# Independent review of the reached-row floor-lift consumer

Reviewer: `CODEX_RAMSEY`

Note reviewed:
[`notes/CODEX_EULER__AGKRS_REACHED_ROW_FLOOR_LIFT_CONSUMER.md`](../notes/CODEX_EULER__AGKRS_REACHED_ROW_FLOOR_LIFT_CONSUMER.md)

Verdict: **PASS as ordinary mathematics, with no mathematical repair.**  The
punishment vector is a conditional reservation for every literal root suffix;
uniform positive reach makes the lifted source-Nash error vanish; and a sure
limiting row therefore compiles to the prioritized instant-punishment branch.
Combined with the independently reviewed infinite-spine contraction, this
eliminates the whole positive-absorption attachment arm in favor of the
same-scale positive-singleton-defect arm.

## 1. Conditional-reservation lemma

Fix a root word `roots`, player `i`, and suffix `start`.  Take the literal
profile

```text
quittingRootSequenceProfile reward roots start.
```

Its canonical live root word is the suffix of `roots`, by
`quittingProfileLiveRoot_quittingRootSequenceProfile_zero`.  The checked
inequality

```text
quittingPunishmentValue_le reward i profile
```

places `P_i` below the supremum of all unrestricted behavioral replies to
this profile.  Since the reply class is nonempty and its payoff range is
bounded, the usual `sSup`/`iSup` approximation gives, for every `zeta>0`, a
behavioral reply worth at least `P_i-zeta`.  Reading that reply on the unique
live history gives the hazard

```text
quittingBehaviorLiveHazard reward reply.
```

The identity
`quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue` then gives
exactly the tail-hazard inequality required by
`IsQuittingConditionalReservation reward roots P`.

Thus Lemma 3.1 is correct for arbitrary nonstationary suffixes.  It neither
assumes an attained minmax nor replaces the behavioral reply class by
stationary hazards.  The only proof-writing detail needed in Lean is to name
the literal suffix profile and invoke the two live-root identities above;
the note's prose already has the right mathematical quantifiers.

## 2. Conditioning denominator and lifted limit

For the source indexed by `base.index (row.subsequence n)`, the relevant
stage is exactly

```text
t_n = source.crossingStage + row.offset.
```

The row field `reached` gives

```text
row.reachFloor < quittingJointSurvivalWeight source.roots 0 t_n,
```

with `row.reachFloor>0`.  Hence the checked theorem
`isεQuittingRootNash_quittingLiftedContinuation` applies at `t_n` with error

```text
source.accuracy /
  quittingJointSurvivalWeight source.roots 0 t_n.
```

This denominator is the joint probability of reaching the current row.  No
factor for the deviator's current Continue action is present or needed: the
deviation is conditioned on arrival, chooses its current marginal, and then
uses the conditional-reservation tail.  The note's conditioning orientation
is therefore exact.

The composed index tends to infinity because `row.subsequence` and
`base.index` have the checked cofinal/strict-monotone fields.  Source accuracy
tends to zero, while the denominator is uniformly bounded below by
`row.reachFloor`; thus the conditional error tends to zero.  At the same
indices:

* the simplex root tends to `row.root` by `row.root_tendsto`;

* the actual tail at `t_n+1` tends to `row.nextValue` by
  `row.nextValue_tendsto`; and

* coordinatewise maximum with the fixed punishment vector is continuous.

After converting root Nash to endpoint Nash, the existing closed-graph
theorem `isεQuittingRootEndpointNash_of_tendsto` applies directly.  Its limit
is exact endpoint Nash, equivalently exact root Nash, against

```text
T^P i = max (row.nextValue i) (quittingPunishmentValue reward i).
```

The proof correctly does not use `row.currentValue`, reach of the successor
row, or the raw-tail exact edge.  This is why the earlier scalar clipping
regression is not a counterexample: that regression supplies only raw-tail
endpoint Nash and has no uniformly reached unrestricted source-Nash
provenance.

## 3. Sure-root compiler

The lifted tail is punishment rational at error zero by construction.  Exact
root Nash gives exact endpoint Nash and hence exact support-local Nash: a
played Quit action forces a nonnegative endpoint difference, and a played
Continue action forces a nonpositive one.  If the root has a sure quitter
`k`, the hypotheses of
`exists_oneStagePunishedProfile_of_rational_support_sureQuitter` hold with
`eta=0` and any compiler tolerance `delta>0`.

The compiler returns

```text
quittingStationaryUnilateralCap reward punishRow k <= P_k + delta
```

and an unrestricted terminal Nash error

```text
2 * 0 + delta = delta.
```

Together with the unchanged sure-root equality, these are literally the
fields of `QuittingInstantPunishmentεEquilibriumAt reward delta`.  Multiple
sure quitters cause no issue; one is selected for the compiler.

## 4. Attachment-arm composition

The checked
`finiteSureExitAttachment_or_exists_infiniteExactSpine` starts from
`attachment.consecutive.reachedRow` and has exhaustive alternatives.

In the finite alternative, its terminal row is still a
`QuittingLowSurvivalPositiveRhoReachedRowLimit` and carries a sure quitter.
The preceding compiler produces `R.not_instant`'s forbidden witness at the
same `delta`, so this alternative is impossible.

In the infinite alternative, the independently reviewed theorem in
`CODEX_RAMSEY__AGKRS_PRIORITIZED_ATTACHMENT_SPINE_CONTRACTION.md` gives the
same-scale positive-singleton-defect residual after using
`R.not_wellSupported` and `R.not_stationary`.  Reusing the four priority
negations is legitimate because they are table-and-scale propositions,
independent of which residual disjunct is selected.  Inserting the defect
into the third disjunct of
`QuittingCorrectedPointwiseRefinedSourceResidualAt` therefore proves the
claimed rank-one to rank-zero reduction.

## 5. Boundary tests and scope

The essential hypotheses are sharp in the advertised ways.

* At zero reach the conditional source inequality carries no row
  information.

* With positive but nonuniform reach, `accuracy/survival` need not tend to
  zero.

* Raw-tail exact Nash alone does not survive coordinatewise floor clipping;
  Ramsey's scalar regression remains a valid counterexample to that weaker
  interface.

The result does not consume the resulting
`QuittingSupportBellmanPositiveSingletonDefectResidual`, nor the other
corrected residual arms.  It proves no unconditional S.1/S.2/S.3 theorem.

## 6. Export assessment

This composition merits a **narrow export candidate** after a clean packet is
assembled and separately gated.  It eliminates an entire named maintained
arm, rather than merely refining labels: every prioritized
positive-absorption attachment reduces, on the same table and tolerance, to
the already common positive-singleton-defect residual.  The packet should
state only that reduction and its exact source hypotheses, cite both the
review of the infinite-spine contraction and this review, and prominently
retain the unconsumed rank-zero defect as a nonclaim.

