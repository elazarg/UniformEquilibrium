# AGKRS corrected four-way extraction: exact refusal boundary

**Author:** CODEX_SOURCE_GATE  
**Status:** archived alternative proof architecture; the direct chronological
AGKRS forward theorem already proves the result independently of this route  
**Date:** 2026-08-30

## 1. Historical architecture and verdict

The two predicates studied by the archived alternative architecture in
[`AGKRS_CORRECTED_SIMON_ROUTE_SOURCE_COMPACTIFICATION.md`](../archive/AGKRS_CORRECTED_SIMON_ROUTE_SOURCE_COMPACTIFICATION.md)
were:

```text
QuittingPayoffTable.HasCorrectedPointwiseFourWayExtraction
HasDiffuseStationarilyGeneratedCompactification.
```

There are two different conclusions.

1. The reviewed ordinary-mathematical forward trichotomy in
   [`AGKRS_FORWARD_TRICHOTOMY_BY_REFUSAL_COMPACTIFICATION.md`](../formalized/AGKRS_FORWARD_TRICHOTOMY_BY_REFUSAL_COMPACTIFICATION.md)
   implies the first predicate immediately: a fixed global S.1, S.2, or S.3
   branch supplies its pointwise member at every requested positive error;
   the fourth disjunct is unused.
2. The same refusal compactification does **not** prove the second predicate
   as it is currently typed.  Applied to an actual diffuse
   stationary-prefix family, it produces

   ```text
   S.1 or S.2 or well-supported S.3,
   ```

   whereas `HasDiffuseStationarilyGeneratedCompactification` omits S.2.
   Its terminal-jump case is precisely S.2.  Pointwise positive live mass
   does not remove that case.

The exact source-faithful statement delivered by refusal is therefore the
conditional compactification

```text
DiffuseGenerated reward ->
not InstantExistence reward ->
StationaryExistence reward or WellSupportedExistence reward.
```

This is also exactly what the fixed-branch caller needs: when branch
selection reaches the diffuse fourth output, the instant branch has already
failed.  The present dependency API forgets that negative fact and asks for
a stronger unconditional two-way implication.

I do not claim that the existing unconditional predicate is false.  I found
no game satisfying the diffuse premise while failing both S.1 and S.3.  I
prove below that neither the checked diffuse fields nor the refusal topology
can discard S.2, and isolate the weaker sufficient interface that preserves
the actual logic of the caller.

## 2. Exact declarations inspected

The following were read at their defining declarations.

* `QuittingPayoffTable.HasCorrectedPointwiseFourWayExtraction` and
  `HasDiffuseStationarilyGeneratedCompactification` in
  `UniformEquilibrium/Quitting/Classification/Existence/AGKRSTheorem34Dependencies.lean`.
* `fixedCorrectedQuittingBranch_of_pointwiseAlternative` and
  `fixedThreeQuittingBranches_of_pointwiseAlternative_of_diffuseCompactification`
  in `UniformEquilibrium/Quitting/Classification/Existence/CorrectedFixedBranch.lean`.
* `QuittingDiffuseStationarilyGeneratedApproximateEquilibriaAt`,
  `QuittingDiffuseStationarilyGeneratedApproximateEquilibria`, and
  `quittingInstant_or_diffuseStationarilyGenerated` in
  `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedBranch.lean`.
* `QuittingDiffuseStationaryPrefixFamily`,
  `exists_quittingDiffuseStationaryPrefixFamily`, and
  `quittingInstantPunishment_of_stationaryPrefix_liveMass_tendsto_zero` in
  `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedWitnessRegimes.lean`.
* `QuittingPositiveJointPrefixReachSource`,
  `QuittingUniqueExceptionalOwnerSource`,
  `HasPositiveJointPrefixReachAttachment`, and
  `HasUniqueExceptionalOwnerAttachment` in
  `UniformEquilibrium/Quitting/Classification/Existence/DiffuseStationaryPrefixSourceAttachments.lean`.
* `QuittingPayoffTable.correctedPointwiseAlternative_or_sourceResidualAt` in
  `UniformEquilibrium/Quitting/Classification/Existence/CorrectedPointwiseSourceBoundary.lean`
  and the priority-safe refinement
  `QuittingPayoffTable.fixedCorrectedBranches_or_cofinally_prioritizedResidual`
  in `UniformEquilibrium/Quitting/Classification/Existence/PrioritizedRefinedSourceBoundary.lean`.

I also checked the two independent reviews of the refusal proof and the
separate continuous-clock and discretization audits.  All claims below that
invoke the full refusal compactification remain ordinary mathematics, not
new Lean-checked declarations.

A final source audit against the pinned `AKRS.tex` confirms that the
support-preserving cell witness used by the decoder is real: its singleton
ratios give positive product hazard for player `i` exactly when the cell has
positive singleton-`i` increment, while matching total absorption keeps every
hazard strictly below one.  The audit found only inessential constant
bookkeeping in the exported presentation: the displayed `K_d` omits a
dimension factor from the technical lemma, and the small-jump scale is
asymptotic to `1/(k-1)`, not literally `1/k`.  Replacing the displayed bound
by `C_d/k` after reindexing repairs it and leaves uniform convergence
unchanged.  This does not create a new mathematical branch or affect any
interface conclusion below.

## 3. Dependency A is a corollary of the reviewed direct trichotomy

Write `T(table)` for the forward conclusion

```text
table.StationaryεEquilibriumExistence or
table.InstantPunishmentεEquilibriumExistence or
table.SequentiallyεPerfectAbsorbingExistence.
```

The checked arbitrary-Never equivalences used by
`threeBranches_of_correctedExtraction_of_compactification` identify these
three table-level branches with the zero-Never stationary, instant, and
well-supported branches.  Each branch existence predicate quantifies over
every positive error and its pointwise predicate is monotone in the error.
Consequently

```text
T(table) -> table.HasCorrectedPointwiseFourWayExtraction.
```

Indeed, assume `ApproximateEquilibriumExistence`, fix `epsilon>0`, and case
split on `T(table)`.  Select the pointwise stationary, instant, or
well-supported witness at `epsilon`; inject it into the corresponding one of
the first three disjuncts.  No stationarily generated witness is required.

The reviewed refusal packet, with the harmless decoder constant correction
just noted, proves `ApproximateEquilibriumExistence -> T(table)` in ordinary
mathematics.  Thus it proves Dependency A as an ordinary corollary.  This is
not yet a Lean producer: its absorption-clock compactness, positive-rate
refusal passage, and support-preserving S.3 decoder are not all implemented
in the checked source.

There is also an important route qualification.  This derivation does not
consume the `QuittingCorrectedPointwiseRefinedSourceResidualAt` returned by
the checked Simon-facing extraction.  It reselects a vanishing-error sequence
of the original approximate equilibria and proves the final three-way result
directly.  Therefore it supplies the proposition `HasCorrectedPointwiseFourWayExtraction`
extensionally, but it is not an adapter from the checked refined residual
objects.  The existing support--Bellman terminal-mismatch regression shows
why such an objectwise adapter cannot merely reinterpret a boundary
annotation as the payoff of its literal suffix.

## 4. What refusal gives from the actual corrected fourth output

Let

```text
hgenerated : QuittingDiffuseStationarilyGeneratedApproximateEquilibria reward.
```

Choose the actual family supplied by
`exists_quittingDiffuseStationaryPrefixFamily hgenerated`.  Its row `n` is
the literal history-independent profile

```text
stationary root n through horizon n, then punishment n,
```

and is unrestricted root-sequence `2*error n`-Nash.  The errors tend to zero.
Thus the refusal compactification can be run on these exact source profiles;
no fresh equilibrium selection is needed.  Every place at which the direct
proof uses global Nash, prescribed terminal law, a suffix, or a refusal
deviation refers to this one family.

The result is the source-faithful alternative

```text
DiffuseGenerated reward ->
StationaryExistence reward or
InstantExistence reward or
WellSupportedExistence reward.                 (R3)
```

The proof is exactly the reviewed direct proof with its initial sequence
chosen from `family.nash`:

1. if all solo rewards are nonpositive, all-Continue gives S.1;
2. otherwise late absorbing completion and absorption-clock compactness give
   a limit chronology;
3. the global refusal ledger supplies the continuous singleton support
   equality;
4. a terminal limit jump gives S.2 from a matching actual source row; and
5. without a terminal jump, the support-preserving decoder gives
   well-supported S.3.

The source's extra prefix and punishment fields are preserved but are not
needed by the continuous/no-terminal consumer.  They matter in the terminal
case: the matching row and the suffix Nash estimate used to justify replacing
the continuation by a fresh approximate min--max punishment remain
source-provenant.  The final S.2 punishment itself need not equal the source
suffix.

Therefore (R3), together with `not InstantExistence reward`, gives the exact
two-way conclusion requested after branch priority:

```text
DiffuseGenerated reward ->
not InstantExistence reward ->
StationaryExistence reward or WellSupportedExistence reward.   (R2-away)
```

This is a complete ordinary proof of the source-faithful **away-from-instant**
compactification, conditional only on the already reviewed refusal theorem.

## 5. Why the current unconditional Dependency B does not follow

The current definition is

```text
DiffuseGenerated reward ->
StationaryExistence reward or WellSupportedExistence reward.   (B)
```

From (R3), proving (B) still requires the separate implication

```text
DiffuseGenerated reward ->
InstantExistence reward ->
StationaryExistence reward or WellSupportedExistence reward,
```

or some argument ensuring that refusal never selects the terminal-jump arm.
Neither statement is present in the inspected sources.

The latter possibility is ruled out by the exact boundary test below.

### Zero-payoff terminal-jump regression

Take any nonempty finite player set and set every nonempty-coalition reward
equal to zero.  Fix a player `p`.  For each `n`, let the repeated product root
have

```text
Pr_p(Quit) = 1 - 1/(n+2),
Pr_j(Quit) = 0 for j != p,
```

take horizon `2`, and take the punishment sequence to be all-Continue.  Every
prescribed and deviating terminal payoff is zero.  Hence:

* the full prefix-then-punishment profile is exact Nash against every
  behavioral deviation;
* the punishment cap is exact for every possible punished label;
* the one-row joint live mass is `1/(n+2)>0`; and
* that live mass tends to zero.

Choosing any positive error sequence tending to zero makes these rows a
literal `QuittingDiffuseStationaryPrefixFamily`.  Its first product roots
converge to a sure quitter and its absorption clocks have a terminal product
jump.  This is precisely the regime consumed by the checked theorem
`quittingInstantPunishment_of_stationaryPrefix_liveMass_tendsto_zero`.

The example is not a counterexample to (B): the zero game also has S.1 and
S.3.  It is a sharp no-go to the missing inference

```text
positive live mass in every diffuse witness -> no terminal limit jump.
```

Neither `1<horizon` nor unrestricted Nash repairs that inference.  A uniform
positive lower bound on live mass would remove this particular regime, but
that bound is absent from `QuittingDiffuseStationarilyGeneratedApproximateEquilibria`.

## 6. The exact API repair

Define the weaker dependency

```text
HasDiffuseStationarilyGeneratedCompactificationAwayFromInstant reward :=
  QuittingDiffuseStationarilyGeneratedApproximateEquilibria reward ->
  not QuittingInstantPunishmentεEquilibriumExistence reward ->
  QuittingStationaryεEquilibriumExistence reward or
    QuittingWellSupportedAbsorbingSequenceExistence reward.
```

Then refactor the fixed selector so that its final branch retains the failed
earlier cases, for example

```text
StationaryExistence or InstantExistence or WellSupportedExistence or
  (DiffuseGenerated and not StationaryExistence and
    not InstantExistence and not WellSupportedExistence).
```

The proof of `fixedCorrectedQuittingBranch_of_pointwiseAlternative` already
has these three negations in scope before it constructs the diffuse output;
the present result type simply drops them.  With the retained `not Instant`
field, `(R2-away)` is exactly sufficient to recover the same three-branch
capstone.  No stronger unconditional (B) is logically needed.

This repair has two advantages.

1. It matches the actual source proof: the terminal-jump branch is not
   asserted impossible; it is contradicted by the retained global failure of
   S.2.
2. It isolates the real mathematical formalization task: implement the
   refusal compactification on one `QuittingDiffuseStationaryPrefixFamily`,
   with output S.1/S.2/S.3, rather than attempt to prove an unmotivated
   diffuse-plus-S.2-to-S.1/S.3 conversion.

## 7. Exact failure of the earlier export as an answer to the maintained question

The reviewed export is a valid ordinary proof of the theorem-level forward
trichotomy, subject to its explicitly recorded non-Lean status.  It was not,
however, a proof of both maintained dependency predicates:

* it implies Dependency A only after using its already-final three-way
  conclusion, rather than consuming the checked refined Simon residual; and
* on a diffuse actual source it retains a terminal-jump S.2 case, while the
  current Dependency B has no S.2 output.

That is the exact interface failure.  It is not a newly discovered flaw in
the refusal inequality, the small-mass continuous argument, or the
support-preserving decoder.  The proof and the question have different
codomains at the corrected fourth-output seam.

## 8. Next formalizable question

The smallest honest target is:

> From one `QuittingDiffuseStationaryPrefixFamily reward`, formalize the
> reviewed refusal compactification and return S.1, S.2, or well-supported
> S.3, using only its literal `family.nash` profiles.  Then retain `not S.2`
> in the fixed-branch selector and eliminate the terminal-jump output.

This would close the corrected fourth-output seam actually encountered by
the capstone.  Proving the current unconditional
`HasDiffuseStationarilyGeneratedCompactification` should remain a separate
strengthening unless an independent argument dispatches diffuse sources that
also admit S.2.
