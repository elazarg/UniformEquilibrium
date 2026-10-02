# AGKRS prioritized refined-source closure audit

## Status

**Internal obstruction audit; no consumer proved.**  I found no contradiction
between approximate-equilibrium existence and the supplied prioritized
residual.  More importantly, the checked positive-survival regression gives
an exact interface countermodel to the tempting step that would identify a
Bellman boundary annotation with the payoff of its literal source suffix.
The four priority fields are negative predicates and do not repair this
missing source closure.

This note does **not** construct a `QuittingPrioritizedRefinedSourceResidualAt`
in a counterexample game.  It therefore neither refutes AGKRS Theorem 3.4 nor
shows that a prioritized residual is inhabited.  It isolates why the present
fields do not themselves yield the needed branch-valued consumer.

## Question checked

Let `reward` be a finite quitting reward table, let `delta > 0`, and suppose

```text
R : QuittingPrioritizedRefinedSourceResidualAt reward delta.
```

Can one contradict `R` merely by combining approximate-equilibrium existence
with the three corrected residual arms and the four pointwise exclusions
stored in `R`?

The desired consumer would have to produce one of

```text
QuittingStationaryεEquilibriumExistence reward,
QuittingInstantPunishmentεEquilibriumExistence reward,
QuittingWellSupportedAbsorbingSequenceExistence reward.
```

This is exactly the first hypothesis required by
`theorem3_4_of_prioritizedSourceClosures`.

## Sources inspected

- `UniformEquilibrium/Quitting/Classification/Existence/
  PrioritizedRefinedSourceBoundary.lean`
  - `QuittingPrioritizedRefinedSourceResidualAt`
  - `QuittingPayoffTable.fixedCorrectedBranches_or_cofinally_prioritizedResidual`
- `UniformEquilibrium/Quitting/Classification/Existence/
  PositiveRhoLandingClassificationBoundary.lean`
  - `QuittingCorrectedPointwiseRefinedSourceResidualAt`
  - `QuittingLowSurvivalPositiveRhoAllContinueSourceResidual`
  - `QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual`
  - `QuittingSupportBellmanPositiveSingletonDefectResidual`
- `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/
  CompactSpineSurvivalBoundary.lean`
  - `QuittingSupportBellmanPositiveSurvivalBoundary`
  - `PositiveSingletonSuffixDefect`
  - `CompactSpineSurvivalBoundaryRegression.
    exists_positiveSurvival_supportBellmanSpine_with_terminal_mismatch`
- `UniformEquilibrium/Quitting/Classification/Existence/
  RefinedSourceResidualRegression.lean`
  - `stationaryExistence_and_refinedSourceResidualAt`
- `Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`
  - `theorem3_4_of_prioritizedSourceClosures`

## 1. Exact logical shape of the prioritized object

The residual field is the inclusive disjunction

\[
 \mathsf{AllCSource}(1/2)\;\vee\;
 \mathsf{PositiveAbsorptionAttachment}(1/2)\;\vee\;
 \mathsf{PositiveSingletonSpineDefect}(\delta).
\]

The other four fields say only that, at the same displayed scale `delta`, no
stationary, instant-punishment, well-supported absorbing, or stationarily
generated pointwise witness exists.  They do not supply a new profile, a
punishment continuation, an absorbing completion, or an equality between a
Bellman annotation and a behavioral payoff.

The cofinal extraction theorem chooses `delta` below four pre-existing
failure scales.  It does not couple the witnesses underlying the four
negations to the source object stored in `residual`.

Consequently there is no hidden contradiction of the form

```text
R.residual -> QuittingStationarilyGeneratedApproximateEquilibriaAt reward delta.
```

Such an implication would already consume the prioritized arm, and none of
the inspected declarations states it.

## 2. What each corrected arm actually supplies

### 2.1 Zero-absorption positive-rho arm

`QuittingLowSurvivalPositiveRhoAllContinueSourceResidual` does retain an
actual landing family and proves that `base.actualTail` is a uniform
equilibrium payoff.  Its limiting root is all-Continue and its exact endpoint
support inequalities are written against that tail.

This is semantic delivery, not any of the three AGKRS classified forms.  The
conversion

```text
uniform equilibrium payoff -> S.1 or S.2 or S.3
```

is essentially the classification problem, not a local consequence of the
source certificate.  In particular, `not_generated` supplies no positive
continuation with which to realize the limiting tail in a finite stationary
prefix.

### 2.2 Positive-absorption attachment arm

The compact root has positive absorption and exact support optimality, but
the surviving obstruction is precisely

\[
  \texttt{predecessorValue}\ne\texttt{actualTail}
  \quad\text{or}\quad
  \exists i,\ P_i<0.
\]

The stationary consumer in the same source file requires recurrence
`predecessorValue = actualTail` together with the boundary packet.  The
prioritized negations neither orient nor eliminate the mismatch and do not
raise a negative punishment coordinate.  Thus this arm also contains no
stationary fixed point by itself.

### 2.3 Positive-survival support--Bellman arm

Here the distinction is sharpest.  The object has bounded values `value t`,
roots `roots t`, exact Bellman recursion, `delta`-support optimality, summable
absorption, and a boundary annotation `boundary`.  It also has

\[
  value_t(i) = TerminalValue_t(i) + Survival_t\,boundary_i.
\]

Positive tail survival means that `boundary` need not be the payoff of the
literal suffix profile.  For the selected positive-singleton player `i`, the
checked `PositiveSingletonSuffixDefect` states that the literal suffixes are
eventually not even `r_i({i})/2`-Nash and supplies an unrestricted behavioral
deviation attaining that fixed gain.

So this source is deliberately **not** an approximate-equilibrium source.  It
cannot be fed to a terminal-Nash or generated-prefix consumer without an
additional boundary-realization theorem.

## 3. Exact interface regression

The checked namespace `CompactSpineSurvivalBoundaryRegression` provides the
minimal example.

- There is one player.
- The unique nonempty terminal reward is `1`.
- Every root is all-Continue.
- The displayed Bellman value is constantly `1`.
- Every row is exact support-optimal against the displayed tail.
- Absorption is identically zero and survival after every restart is `1`.

Thus the source has an exact bounded support--Bellman spine with positive
survival.  But the production terminal payoff of every literal suffix is
`0`, whereas the displayed value is `1`.  Quitting immediately earns `1`, so
the literal suffix has exploitability exactly `1`.

This calculation is formalized by

```text
CompactSpineSurvivalBoundaryRegression.
  exists_positiveSurvival_supportBellmanSpine_with_terminal_mismatch
```

and is packaged into a positive-singleton refined residual at every
nonnegative tolerance by

```text
RefinedSourceResidualRegression.refinedSourceResidualAt.
```

The same one-player table has the exact stationary branch (Always Quit), so
it is **not** a prioritized-residual counterexample.  That qualification is
essential.  What it refutes is the proposed interface implication

```text
support--Bellman source data
  -> its literal suffix profiles realize the annotated values
  -> stationarily generated approximate equilibria.
```

Priority correctly removes this particular game by selecting S.1 first, but
the negative priority fields contain no operation that repairs the failed
middle arrow in a different game.

## 4. Why approximate-equilibrium existence does not close the mismatch

Approximate-equilibrium existence supplies some behavioral profile at each
positive tolerance.  The support-spine residual supplies a different,
source-matched sequence of literal suffix profiles.  No checked declaration
identifies either the law or the continuation payoff of these two selections.

In the regression the separation is maximal: the equilibrium selection is
Always Quit, while the residual source is Always Continue.  Therefore a
compactness argument on the existence witnesses may select the classified
profile and lose the residual source; a compactness argument on the residual
source preserves the phantom boundary and loses terminal Nash.  The four
pointwise exclusions only say that the former selection cannot already land
in four named shapes at scale `delta`; they do not align it with the latter.

## 5. Strongest valid conditional closure statement

The data missing from the support-spine arm can be stated without another
case split:

> One needs a source-matched absorbing or punishment continuation whose
> actual continuation payoff realizes the Bellman boundary (with an error
> controlled at the same scale), while preserving the rowwise support
> inequalities along the retained prefix.

With such a continuation, finite Bellman substitution would turn a long
retained prefix into either a completely absorbing well-supported sequence
or a stationarily generated punishment prefix.  Without it, the exact
identity above leaves the nonvanishing term
`Survival_t * boundary`, and the one-player regression shows that term can be
the entire displayed value.

This is not claimed as a new theorem: the exact quantitative hypotheses
needed to transport unrestricted deviations through the splice have not been
proved here.  It is the minimal source-closure interface that a genuine
`hprioritized` consumer must provide.

## 6. Verdict

No contradiction follows from the presently exposed fields, and no
well-founded rank is visible: the three residual arms have different source
types, while the four priority fields are pure exclusions.  The strongest
rigorous outcome of this audit is the exact checked interface countermodel in
Section 3 and the identification of boundary realization/source matching as
the missing datum.

This note is not export-ready.  A future positive result must either:

1. construct the source-matched absorbing/punishment continuation above;
2. show that a prioritized residual forces one of the existing closure
   consumers by an independent quantitative argument; or
3. produce an actual finite game satisfying the full prioritized object and
   then analyze all three AGKRS global branches.

