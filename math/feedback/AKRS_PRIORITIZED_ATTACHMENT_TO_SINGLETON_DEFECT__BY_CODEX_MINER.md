# Whole-packet gate: prioritized attachment to singleton defect

Reviewer: `CODEX_MINER`

Packet reviewed:
[`AGKRS_PRIORITIZED_ATTACHMENT_TO_SINGLETON_DEFECT.md`](../exports/AGKRS_PRIORITIZED_ATTACHMENT_TO_SINGLETON_DEFECT.md)

Verdict: **ACCEPT after one mandatory strategy-semantics wording repair; do
not return to notes.**  The mathematical composition is complete.  The finite
and infinite alternatives are exhaustive, both are handled at the original
`delta`, and the resulting defect is inserted into a new prioritized residual
with all four same-scale priority negations copied literally.  No claim from
the unreviewed Section 8 of Euler's note entered this packet.

Mandatory repair before formalizer handoff: in `Definitions and assumptions`,
replace the sentence saying that deviations in (B) are unrestricted
behavioral deviations.  The predicate

```text
IsQuittingRootNash reward T^P 0 q
```

quantifies over one-stage marginal replacements `dev : PMF Bool`, not complete
behavioral strategies.  Its **derivation** uses the source's unrestricted
behavioral Nash inequality by combining a current marginal deviation with an
unrestricted suffix reply, and the sure-row compiler's terminal conclusion is
again unrestricted behavioral Nash.  The packet's proof uses this distinction
correctly elsewhere; only that summary sentence conflates the interfaces.

With that wording fixed, I find no unresolved mathematical or export-gate
objection.

## 1. Exact source coverage

The statement is conditional on an explicit

```text
attachment :
  QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual
    reward (1/2)
```

on the same table as
`R : QuittingPrioritizedRefinedSourceResidualAt reward delta`.  It does not
pretend that this witness is exclusive inside the inclusive corrected
residual.  The theorem only needs its existence.

The checked declaration

```text
attachment.consecutive.
  finiteSureExitAttachment_or_exists_infiniteExactSpine
```

starts at `attachment.consecutive.reachedRow` and has exactly two outputs:
a finite reachable terminal row with a sure quitter, or an infinite sequence
of successor reached rows.  Thus the packet accounts for every extension of
the supplied attachment.  It neither drops the finite arm nor silently adds
the all-Continue source arm.

The attachment's `absorption_pos` and `obstruction` fields are not used after
the iterable `consecutive` datum is supplied.  This is harmless weakening in
the proof, not missing source coverage: the theorem is stated for the full
attachment structure and consumes a field it already carries.

## 2. Finite arm

The punishment vector `P_i=quittingPunishmentValue reward i` is a conditional
reservation for every literal root sequence.  For a fixed suffix profile,
`quittingPunishmentValue_le` puts `P_i` below the unrestricted behavioral
best-reply supremum.  Supremum approximation and the live-root payoff identity
produce the hazard tail required by `IsQuittingConditionalReservation`; no
best response or punishment infimum is assumed attained.

For a reached row, its field `reached` supplies one fixed positive
`reachFloor`, not merely pointwise positive survival.  Applying
`isεQuittingRootNash_quittingLiftedContinuation` at

```text
t_n = source.crossingStage + row.offset
```

therefore gives error `source.accuracy/survival_n`, bounded above by
`source.accuracy/reachFloor`.  The composed source indices are cofinal, so
this tends to zero.  The root, next-tail, and coordinatewise floor lift
converge on the same nested subsequence.  Closedness of the finite root-Nash
inequalities yields exactly

```text
IsQuittingRootNash reward
  (fun i => max (row.nextValue i) P_i) 0
  (quittingRootOfSimplex row.root).
```

The terminal row of the finite attachment is still a reached-row-limit and
has a checked sure quitter.  The lifted continuation is zero-error punishment
rational.  Exact root Nash gives exact support-local Nash.  Applying
`exists_oneStagePunishedProfile_of_rational_support_sureQuitter` with
`eta=0` and compiler tolerance `delta` returns terminal Nash error
`2*0+delta=delta` and the required punishment cap.  This is literally
`QuittingInstantPunishmentεEquilibriumAt reward delta`, contradicting
`R.not_instant`.  The finite arm is therefore eliminated at the original
scale.

The conditioning denominator is correct: it is joint survival to the row.
There is no extra factor for the deviator's prescribed current Continue
probability, because the constructed deviation chooses its current marginal
after conditioning on arrival and then uses an unrestricted suffix response.

## 3. Infinite arm

For

```text
spine : QuittingLowSurvivalPositiveRhoInfiniteExactSpine
  attachment.consecutive.reachedRow,
```

write `V_n=(spine.row n).currentValue`, keep the simplex root
`s_n=(spine.row n).root`, and decode `q_n=quittingRootOfSimplex s_n`.  The
checked `spine.edge n` has the required chronological orientation

```text
V_n = quittingRootSuccessorPayoff reward V_(n+1) q_n,
```

with `q_n` exact endpoint Nash against `V_(n+1)`.  The packet correctly keeps
the simplex and PMF roots distinct.

The reached-row carrier boxes bound every value.  Exact endpoint Nash gives
zero-error support-local Nash and hence support error `delta` because
`delta>0`.  The checked bounded support--Bellman split therefore returns:

1. `QuittingWellSupportedAbsorbingSequenceAt reward delta`, contradicted by
   `R.not_wellSupported`; or
2. `QuittingSupportBellmanPositiveSurvivalBoundary reward delta`.

Applying `stationary_or_defect` to the second output gives either global
stationary existence, whose value at this same positive `delta` contradicts
`R.not_stationary`, or precisely

```text
Nonempty
  (QuittingSupportBellmanPositiveSingletonDefectResidual reward delta).
```

Thus the infinite arm also reaches the claimed codomain at the original
scale.

## 4. Same-scale prioritized reconstruction

The corrected residual is the inclusive disjunction

```text
all-Continue source OR attachment OR singleton defect.
```

Inserting the produced defect into its third disjunct changes neither the
reward table nor `delta`.  The four remaining fields of
`QuittingPrioritizedRefinedSourceResidualAt` are propositions only about that
table and scale.  Copying

```text
R.not_stationary
R.not_instant
R.not_wellSupported
R.not_generated
```

is therefore type-correct and mathematically exact.  Only the residual
witness is changed.  The local arm rank `attachment:1 -> defect:0` strictly
decreases, while the packet correctly states that rank zero remains
unconsumed and that this is not a terminating proof of AGKRS Theorem 3.4.

## 5. Review provenance and Section 8 exclusion

Euler's independent review of Ramsey's original note PASSed the infinite
spine contraction but correctly kept its then-surviving finite floor-deficit
arm internal.  Ramsey's later independent review of Euler's reached-row
floor-lift PASSed the missing finite consumer and explicitly checked its
composition with the infinite theorem.  These reviews cover the two pieces
used by the packet.

Euler's later Section 8 proposed extending the same argument to the
all-Continue positive-rho arm.  The packet does **not** state that extension:
its hypotheses require the positive-absorption attachment, its adapter begins
at `attachment.consecutive`, and its scope explicitly leaves the all-Continue
source arm open.  No unreviewed Section 8 theorem, source dispatch, or full
prioritized normal form appears in the proof or Lean handoff.

## 6. Boundary and novelty gate

The zero-reach, nonuniform-reach, raw-tail clipping, multiple-sure-quitter,
and one-player tests match the actual proof dependencies.  In particular the
raw-tail scalar regression does not refute the source-derived lift: it lacks
uniform reach and the unrestricted source-Nash provenance used to pay the
lift.

The packet is not duplicated by
`PositiveJointSummablePortPhantomReduction.lean`.  That route has a different
source and no prioritized attachment provenance, even though both routes can
reach the same raw singleton-defect type.  The newly observed diagonal
terminal-semantic closure of positive-joint endpoints likewise concerns
uniform-payoff existence and does not supply this same-scale AGKRS attachment
normalization.

After the one wording repair, the packet meets the narrow export gate: it
removes the entire prioritized positive-absorption attachment as an
independent source obligation, while preserving the rank-zero defect and all
other branches as explicit nonclaims.

