# Focused feedback on Section 34 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_EULER`

## Scope and verdict

I independently checked only Section 34 against
`capNashPrefix_resetExcursion_exact_account`,
`exists_resetFace_minimizer_with_unique_allContinue_capNash`, the
`FullReplacementCluster` declarations, and the fixed-law/global comparison in
`RectangleResetFaceMinimizer.lean`.

**Verdict: the reset-face account and cap barrier are valid, but two scope
phrases should be weakened.**  Equality of total debt at the returned point
does not by itself prove a positive-support cardinality drop, and the named
fixed-law premium dichotomy is presently rectangle-specific rather than a
generic theorem for every paid full-replacement cluster.

## Exact valid application

For the full-replacement cluster `F`, the mover debt is exactly zero.  This is
the named theorem `FullReplacementCluster.mover_debt_eq_zero`; equivalently it
follows by combining endpoint convergence with
`fullReplacement_moverDebt_le_lambda_sq` and vanishing scale.

Applying `exists_resetFace_minimizer_with_unique_allContinue_capNash` with

```text
source=base, target=F, who=m
```

is legitimate: `base` is a positive global minimum, `F` belongs to the
terminal semantic carrier, and `d_m(F)=0`.  It returns `R` with

```text
d_m(R)=0,
D(base)<=D(R)<=D(F),
sum_{j!=m}(d_j(R)-d_j(base))
  =D(R)-D(base)+d_m(base)>=d_m(base).                (34.1)
```

It also returns exact cap-Nash uniqueness: every exact product root against
`B(R)` is all-Continue, and prefixing `R` by all-Continue fixes `R`.  Thus the
off-minimum arm is indeed a zero-charge rigid cap barrier.

The semantic minimizer has no field retaining the behavioral endpoint law,
paid first-disagreement witnesses, or a reached Bellman path.  Therefore the
claim that paid-law provenance is lost in the passage `F -> R` is an exact
interface audit.

## Required qualification 1: minimum fiber is not yet support drop

If `D(R)=D(base)`, then `R` is another global minimum and `m` is absent from
its positive-debt support because `d_m(R)=0<d_m(base)`.  This much is exact.
It is not, from the reset-face theorem alone, a strict support-cardinality
drop: debt can move into coordinates that were zero at `base`.

The named strict-subset theorem in `MinimumFiberSupportDrop.lean` additionally
uses a `FullReplacementCluster` endpoint together with flat tangent, no-entry,
and minimum-fiber hypotheses.  The constrained minimizer `R` returned here is
not asserted to be that endpoint and Section 34 does not restate those extra
hypotheses.  Replace

```text
precisely a minimum-fiber support drop
```

by

```text
a minimum-fiber return with the mover removed from positive support;
turning this into the finite support-rank drop requires the existing
flat/no-entry support-control hypotheses or a fresh re-extraction argument.
```

## Required qualification 2: law premium is branch-specific

`QuittingStoppingLawRectangleMinimizerBridge.aligned_or_lawPremium` proves the
aligned-or-positive-premium dichotomy for the rectangle joint-atom package,
where a fixed-law minimizer and a global reset-face minimizer are both
constructed.  It does not state that every generic paid first-disagreement
full-replacement cluster has such a fixed-law minimizer or a positive premium.

Accordingly, the generic paid-source conclusion is:

```text
semantic minimization may discard the paid endpoint law; no theorem here
shows that retaining that generic law has zero cost.
```

In the rectangle orientation one can strengthen this to the checked
aligned-or-positive-premium alternative.  The proposed “premium funds an
excursion” route is exact only after that branch-specific premium has been
produced; for the generic paid cluster it remains a suggested analogue, not a
source-level dichotomy already supplied by the named theorem.

With these two qualifications, Section 34 is a correct source-level reduction
and does not claim a new theorem.
