# AGKRS fourth output: direct payoff consumption and the normality no-go

Author: `CODEX_STRENGTHEN`

Status: **complete direct-payoff reduction plus a sharp source-local no-go;
ordinary synthesis of named checked declarations, not a new proof of the
AGKRS S.1/S.2/S.3 trichotomy.**

## Question

For a finite quitting reward table, can Simon's corrected fourth output be
consumed without first proving the full AGKRS three-branch compactification?
More specifically:

1. does a genuine stationarily-generated family already yield a uniform
   payoff;
2. which arms of
   `QuittingCorrectedPointwiseRefinedSourceResidualAt` already yield one; and
3. does playerwise punishment normality repair the remaining source, perhaps
   through the normal S.3 delayed-switch theorem?

The answers are:

- **yes** to (1), by an existing checked two-theorem composition, with no
  normality assumption;
- **the first two arms** of the refined residual have checked source-selected
  uniform payoffs; and
- **no source-local repair follows from normality** for the third arm.  An
  exact punishment-normal one-player regression has the third residual at
  every nonnegative tolerance while its retained roots are all Continue, its
  survival is one, and its literal suffix exploitability is one.

Thus the normal delayed-switch theorem is a downstream consumer of S.3, not a
producer from the corrected fourth output.  It does not close the surviving
positive-singleton phantom-boundary seam.

## Declarations inspected

Checked declarations and definitions:

- `QuittingStationarilyGeneratedApproximateEquilibriaAt`,
  `QuittingStationarilyGeneratedApproximateEquilibria`, and
  `quittingApproximateEquilibriumExistence_of_stationarilyGenerated` in
  `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedBranch.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence`
  in the same file, and
  `quittingApproximateEquilibriumExistence_iff_exists_uniformEquilibriumPayoff`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumUniformPayoffEquivalence.lean`;
- `QuittingPayoffTable.approximateEquilibriumExistence_iff_zeroNever` in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/ArbitraryNeverExtraction.lean`;
- `QuittingCorrectedPointwiseRefinedSourceResidualAt`,
  `QuittingLowSurvivalPositiveRhoAllContinueSourceResidual.isUniformEquilibriumPayoff`,
  and the three refined residual arms in
  `UniformEquilibrium/Quitting/Classification/Existence/PositiveRhoLandingClassificationBoundary.lean`;
- `QuittingLowSurvivalPositiveRhoCompactLimit.isUniformEquilibriumPayoff_actualTail`
  in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/PositiveRhoSourceTerminalConsumer.lean`;
- `QuittingSupportBellmanPositiveSurvivalBoundary`, its exact
  annotation/terminal identity, and `PositiveSingletonSuffixDefect` in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/CompactSpineSurvivalBoundary.lean`;
- `RefinedSourceResidualRegression.refinedSourceResidualAt` and
  `stationaryExistence_and_refinedSourceResidualAt` in
  `UniformEquilibrium/Quitting/Classification/Existence/RefinedSourceResidualRegression.lean`;
- `StationaryPrefixEndpointDecouplingRegression.punishmentValue_eq_one` in
  `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedPositiveLiveLimit.lean`;
- `QuittingPrioritizedRefinedSourceResidualAt` and
  `QuittingPayoffTable.fixedCorrectedBranches_or_cofinally_prioritizedResidual`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/PrioritizedRefinedSourceBoundary.lean`; and
- `fixedCorrectedQuittingBranch_of_pointwiseAlternative` in
  `UniformEquilibrium/Quitting/Classification/Existence/CorrectedFixedBranch.lean`.

The independently reviewed delayed-switch theorem is now checked and recorded
in
[`NORMAL_S3_DELAYED_SWITCH_UNIFORM_PAYOFF.md`](../formalized/NORMAL_S3_DELAYED_SWITCH_UNIFORM_PAYOFF.md).
The already reviewed ordinary forward-trichotomy proof is
[`AGKRS_FORWARD_TRICHOTOMY_BY_REFUSAL_COMPACTIFICATION.md`](../formalized/AGKRS_FORWARD_TRICHOTOMY_BY_REFUSAL_COMPACTIFICATION.md).
Its formalization record now points to the checked Lean realization.

## Theorem A: the genuine fourth branch already has a checked direct consumer

Let (I) be finite and let (r) be a quitting reward table.  If

```text
QuittingStationarilyGeneratedApproximateEquilibria r
```

holds, then there is a payoff (v) such that

```text
(quittingGame r).IsUniformEquilibriumPayoff none v.
```

No punishment-normality hypothesis is needed.

### Proof

The checked declaration

```text
quittingApproximateEquilibriumExistence_of_stationarilyGenerated
```

turns the generated family into
`QuittingApproximateEquilibriumExistence r`.  Quantitatively, for a requested
error \(\varepsilon>0\), it invokes the generated family with punishment error
and equilibrium slack both \(\varepsilon/4\).  The returned literal stationary
prefix followed by its actual punishment sequence is an
\((\varepsilon/2)\)-Nash root sequence, hence an \(\varepsilon\)-Nash sequence.
The Nash inequality is against every unilateral hazard sequence, equivalently
every behavioral replacement on the unique live history.

Then

```text
quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence
```

selects one fixed payoff from the terminal approximate equilibria.  This is
exactly the desired conclusion.  `QED`

The same conclusion follows from the diffuse generated family by forgetting
its extra positive one-stage live-mass field.  It also follows directly from
the AGKRS table premise after zero-Never normalization, by
`QuittingPayoffTable.approximateEquilibriumExistence_iff_zeroNever` and the
checked approximate-equilibrium/uniform-payoff equivalence.  That latter
observation explains why uniform-payoff existence alone is not a solution of
the stronger structural AGKRS classification question.

### Fixed-scale boundary

One fixed witness

```text
QuittingStationarilyGeneratedApproximateEquilibriaAt r delta
```

only supplies errors asymptotic to `delta`.  It does not by itself give
arbitrarily accurate terminal Nash profiles.  The all-positive-`delta`
quantifier in `QuittingStationarilyGeneratedApproximateEquilibria` (or a
cofinal family with `delta -> 0`) is essential to Theorem A.

## Theorem B: exact source-only reduction of the refined residual

For every finite player type, reward table (r), and tolerance (delta),

```text
QuittingCorrectedPointwiseRefinedSourceResidualAt r delta
```

implies

```text
(exists v, (quittingGame r).IsUniformEquilibriumPayoff none v)
or
Nonempty (QuittingSupportBellmanPositiveSingletonDefectResidual r delta).
```

This implication uses the actual source retained by the first two arms.  It
does not use a background approximate-equilibrium hypothesis and does not use
punishment normality.

### Proof

Unfold the refined residual and split its three arms.

1. Given
   `residual : QuittingLowSurvivalPositiveRhoAllContinueSourceResidual r (1/2)`,
   take \(v=\texttt{residual.base.actualTail}\).  The checked
   `residual.isUniformEquilibriumPayoff` proves the first disjunct.
2. Given
   `residual : QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual r (1/2)`,
   its field `residual.base` is a literal
   `QuittingLowSurvivalPositiveRhoCompactLimit`.  Take
   \(v=\texttt{residual.base.actualTail}\) and apply the checked
   `residual.base.isUniformEquilibriumPayoff_actualTail`.  Neither the
   recurrence mismatch nor the negative-punishment alternative erases this
   source-tail conclusion.
3. The last arm is already the second displayed disjunct.

These cases are exhaustive.  `QED`

Theorem B is the strongest immediate source-local payoff reduction visible in
the refined interface.  A narrow exact-name search found no existing named
wrapper with this codomain, although both positive conclusions used in its
proof are checked.

## Theorem C: punishment normality does not repair the last source locally

There exists a finite punishment-normal quitting game such that, for every
\(\delta\ge 0\),

```text
QuittingCorrectedPointwiseRefinedSourceResidualAt r delta
```

holds through the positive-singleton-defect arm, while the roots retained by
that arm are not completely absorbing and their literal suffixes stay a fixed
positive distance from terminal Nash.

### Exact regression

Use the one-player type `PUnit` and the unit reward table

```text
StationaryPrefixEndpointDecouplingRegression.reward,
```

whose unique terminal reward is (1).  The checked theorem
`punishmentValue_eq_one` gives

\[
 \chi=1=r(\{*\}) .                                      \tag{1}
\]

Thus the unique player is punishment-normal, with equality.

For every \(\delta\ge 0\), the checked
`RefinedSourceResidualRegression.refinedSourceResidualAt` supplies the refined
residual through a
`QuittingSupportBellmanPositiveSingletonDefectResidual`.  Its underlying
checked regression has

\[
 x_t=\text{all Continue},\qquad
 V_t=1,qquad
 S(t,\infty)=1                                           \tag{2}
\]

at every date.  Hence every literal suffix terminal payoff is (0), while
Quit immediately yields (1).  Its unrestricted terminal exploitability is
therefore exactly (1).  In particular:

- the stored root sequence is not completely absorbing;
- its displayed Bellman annotation is not its actual suffix payoff;
- its literal suffixes are not terminal \(\varepsilon\)-Nash for any
  \(0\le\varepsilon<1\); and
- punishment normality does not change any of these facts.

The same game has the exact stationary branch by
`stationaryExistence_and_refinedSourceResidualAt`.  Consequently it is not a
counterexample inhabiting `QuittingPrioritizedRefinedSourceResidualAt`, whose
priority fields exclude S.1.  It is instead the sharp counterexample to every
*source-local* implication of the form

```text
punishment normality + positive-survival support--Bellman residual
  -> the retained roots realize their annotation
  -> the retained roots are S.3 or terminal approximate Nash.
```

Priority can choose the separate stationary profile in this example; it does
not turn the all-Continue residual chronology into that profile.

## Direct S.1 and S.2 tests

No direct S.1 or S.2 projection survives the exact interfaces.

- A stationarily-generated witness repeats one root only through a finite
  horizon and then uses an arbitrary behavioral punishment sequence.  It is
  therefore not a stationary profile.  The checked
  `quittingInstant_or_diffuseStationarilyGenerated` split obtains S.2 only
  when sure first-stage quitting occurs cofinally; its diffuse arm deliberately
  retains positive one-stage survival and is not S.2.
- In the positive-absorption refined arm, the checked stationary consumer
  needs temporal recurrence
  `base.predecessorValue = base.actualTail` and the stationary boundary
  packet.  The sharp residual retains precisely nonrecurrence or a negative
  punishment coordinate.  Normality \(\chi_i\le r_i(\{i\})\) implies neither
  recurrence nor \(\chi_i\ge0\).
- In the support--Bellman arm, the checked stationary zero-solo consumer
  applies when every singleton self-reward is nonpositive.  The remaining
  defect stores a player with strictly positive singleton reward, so that
  consumer has already been exhausted.

Thus the source-selected uniform payoffs in Theorem B are genuine semantic
consumers, but they do not secretly satisfy the stronger S.1 or S.2 output
types.

## Why the normal delayed-switch theorem does not bridge the seam

The normal delayed-switch theorem assumes an already supplied S.3 witness:
one completely absorbing infinite product-row sequence whose every row is
approximately perfect against its **literal actual suffix value**.  It then
changes the tail after a finite survival crossing and proves terminal Nash
against unrestricted behavioral deviations.

Neither input is present in the surviving defect arm:

1. positive limiting suffix survival gives summable absorption rather than
   complete absorption; and
2. the exact identity is

   \[
    V_t=U_t+S(t,\infty)b,                               \tag{3}
   \]

   where (V_t) is the Bellman annotation, (U_t) is the actual suffix
   payoff, and the nonvanishing boundary term may be all of (V_t).

The unit regression has (V_t=1), (U_t=0), (S=1), and (b=1), so it
meets punishment normality while failing both delayed-switch inputs
maximally.  Normality supplies playerwise inequalities
\(\chi_i\le r_i(\{i\})\); it does not supply one common source-matched tail
whose payoff vector realizes (b).

There is also no useful detour in the genuine generated branch: Theorem A
already returns a uniform payoff directly, without first manufacturing S.3.
Conversely, a uniform payoff is not known to imply S.1, S.2, or S.3, so this
direct consumer does not prove the AGKRS structural trichotomy.

## Priority-safe conclusion

For a prioritized residual at scale (delta), the fields
`not_wellSupported` and `not_generated` explicitly forbid same-scale S.3 and
stationarily-generated outputs.  A new global S.3 producer would contradict
those fields directly; the delayed-switch payoff consumer is not needed for
that contradiction.  The problem is producing the source-matched S.3 data,
not consuming it after production.

Accordingly the corrected fourth-output boundary reduces as follows:

```text
genuine stationarily-generated family
  -> checked unrestricted approximate equilibria
  -> checked uniform payoff;

refined residual
  -> source-selected uniform payoff
     or positive-survival positive-singleton defect;

positive-singleton defect + punishment normality
  -/-> source-boundary realization or S.3 by the retained roots.
```

The reviewed refusal-compactification export claims the stronger full forward
S.1/S.2/S.3 trichotomy by a different ordinary-mathematics route.  The present
note neither reproves nor challenges that packet.  At the current checked
declaration boundary, Theorems A and B are payoff consumers, not a replacement
for `HasCorrectedPointwiseFourWayExtraction` or
`HasDiffuseStationarilyGeneratedCompactification`.

## Lean handoff

Only one small wrapper appears genuinely missing:

```text
theorem uniformPayoff_or_positiveSingletonDefect_of_refinedSourceResidualAt
    (residual : QuittingCorrectedPointwiseRefinedSourceResidualAt reward delta) :
    (exists payoff,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) or
    Nonempty
      (QuittingSupportBellmanPositiveSingletonDefectResidual reward delta)
```

Its proof is the three-case split in Theorem B.  The stationarily-generated
payoff theorem should be used by composition, not duplicated unless a short
discoverability alias is desired.

For the no-go, a useful checked regression wrapper would state

```text
RefinedSourceResidualRegression.allNormal_and_refinedResidual_and_sourceGap
```

by combining `punishmentValue_eq_one`, `refinedSourceResidualAt`, and the
existing constant-all-Continue suffix calculations.  This is documentation
and API hardening, not a new mathematical consumer.

## Strongest surviving obligation

After Theorem B, the only source-local payoff seam is:

> Given a **prioritized, cofinal** positive-singleton support--Bellman defect,
> use its additional actual AGKRS source provenance to construct one common
> absorbing or punishment continuation realizing the boundary at vanishing
> error, or prove that branch priority forces a different classified output.

Punishment normality alone is insufficient.  The missing field is
source-matched boundary realization (or an eliminative substitute), not a
consumer of an already available S.3 sequence.
