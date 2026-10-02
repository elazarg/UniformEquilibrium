# Review of Proposition 6BI and Corollaries 6BI.1--2

Reviewer: `CODEX_EULER`

Verdict: **PASS.**  The full-replacement cluster dichotomy really removes
flat charged circulation as a terminal support-rank exit.  The minimum-fiber
arm has a checked strict cardinal-rank descent, and the off-minimum arm has
exactly the eventual paid-row fields expected by the maintained paid
consumer.  No conditioned packet, restart, or root-Nash claim is used.

## Claim audited

For a `QuittingPositiveMinimumDebtTangentFamily F`, assume every tangent
column is flat and there is no inactive-support entry.  For any active mover
`m`, choose

```text
E : FullReplacementCluster F m.
```

Global minimum gives `D(F.base)<=D(E.cluster)`.  The proposition splits this
into equality, where a fresh tangent family at `E.cluster` has strictly
smaller positive-debt-support cardinality, and strict inequality, where the
stored endpoint subsequence carries an eventual fixed-gain paid
first-disagreement row with observer distinct from `m`.

Corollary 6BI.1 uses this dichotomy in strong induction to replace the old
four exits

```text
positive slope / support entry / circulation / paid
```

by

```text
positive slope / support entry / paid.
```

Corollary 6BI.2 deletes the circulation consumer from the existing
conditional uniform-payoff capstone.

## Exact declaration check

The following checked declarations have exactly the hypotheses used.

- `exists_fullReplacementEndpointCluster F m` returns a carrier cluster,
  strict subsequence, coordinatewise tangent lower bounds, and exact mover
  coordinate.  It requires no sign on the total tangent slope.
- `F.base_minimum E.cluster E.cluster_mem` gives
  `D(F.base)<=D(E.cluster)`, so equality versus strict inequality is exhaustive
  and disjoint.
- In the equality arm,
  `exists_reextractedFrontier_of_minimumFiberEndpoint F E flat noEntry hEq`
  returns a fresh family `F'` with `F'.base=E.cluster` and

  ```text
  card(F'.positiveDebtSupport)<card(F.positiveDebtSupport).
  ```

  Its proof uses
  `positiveDebtSupport_ssubset_of_exactDiagonal_of_flat_of_noEntry_of_minimumFiber`;
  the strictness comes from the selected mover's endpoint debt being exactly
  zero.  The theorem requires flatness for every old source column, exactly
  as Proposition 6BI assumes, and no additional potential or circulation
  data.
- In the strict arm,
  `E.exists_eventually_paidFirstDisagreement (flat m) hStrict` returns

  ```text
  exists observer gain,
    observer != m and 0<gain and
    eventually rank,
      Nonempty (QuittingPaidFirstDisagreementRow reward
        (F.fullReplacementProfile m (E.subseq rank)) observer gain).
  ```

  This is literally the source/profile/subsequence package stored in the
  fourth arm of the old finite-rank alternative and quantified by
  `PaidFirstDisagreementUniformPayoffConsumer`.

Thus Proposition 6BI is a direct, noncircular composition of checked
declarations.

## Rank induction

The induction is well founded on the natural number
`card(F.positiveDebtSupport)`.  Positive total base debt makes that support
nonempty, so an active mover is available whenever the flat/no-entry branch
is reached.  Every recursive call is made only in the equality arm and has
the strict checked cardinal inequality above.  Re-extraction supplies a full
new tangent family at the new minimum base; the proof does not assume that
old tangent labels, stopping laws, or endpoint subsequences persist.

The existing exhaustive alternative provides:

- the positive-slope exit directly;
- flatness plus support entry in the entry arm;
- flatness plus no entry in the circulation arm; and
- flatness plus no entry in the potential arm.

Hence Proposition 6BI can replace the circulation branch exactly as written.
The potential branch may continue to use the existing connected potential
theorem, as the note does.  In fact a leaner formal proof can apply
Proposition 6BI to an arbitrary active mover in *both* flat/no-entry arms;
the potential/circulation distinction is not needed for the reduced
three-exit induction.  This is a simplification, not an objection.

## Three-exit capstone

The proof of Corollary 6BI.2 is the checked four-exit capstone with the new
three-exit induction substituted for `finiteSupportRankAlternative`.

- `(P)` and `(E)` still produce all-error chronological debt-shadowing
  certificates and therefore use the existing unrestricted-behavior
  compiler.
- `(R)` contains the same `frontier`, `mover`, `endpoint`, strict separation,
  observer, positive gain, and eventual paid rows required by
  `PaidFirstDisagreementUniformPayoffConsumer`.

There is no missing adapter between the reduced alternative and `hpaid`, and
no `hcirculation` hypothesis remains.

## Novelty and scope

A narrow audit of `MinimumFiberSupportDrop.lean`,
`NormalizedCurvaturePaidRow.lean`, and `UniformExistenceBoundary.lean` found
the two arms separately and the old four-exit induction, but no theorem
applying the arbitrary-mover full-replacement dichotomy to eliminate the
circulation exit globally.  The composition is therefore genuinely new.

The result does **not** solve any of the remaining three exits.  In
particular, it does not:

- turn the paid row into an exact Bellman chronology or payoff near-return;
- construct the positive-slope or support-entry chronological certificates;
- prove a uniform-equilibrium payoff without the three stated consumers; or
- show that conditioned packet reprojection is false or useless as a local
  theorem.

Its precise consequence is narrower and important: the conditioned-packet
producer is no longer logically required as a separate fourth input to this
finite-rank capstone, because charged circulation is already a rank descent
or the maintained paid exit.

## Suggested formal theorem shape

For formalization, first define a reduced three-exit predicate parallel to
`HasQuittingStoppingLawFiniteSupportRankAlternative`.  Prove its termination
by strong induction, using the arbitrary-mover dichotomy directly on every
flat/no-entry branch.  Then copy the existing proof of
`exists_uniformEquilibriumPayoff_of_finiteSupportRankExitUniformPayoffConsumers`
with only three cases.  This avoids changing the existing four-exit API and
keeps the new implication independently checkable.
