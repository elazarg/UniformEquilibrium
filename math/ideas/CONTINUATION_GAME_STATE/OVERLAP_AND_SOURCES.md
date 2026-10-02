# Source Audit and Overlap

## Bounded source set inspected

The exploration used the following repository declarations and modules.

### Finite semantic prefix

`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`

* `quittingTerminalSemanticPair`
* `quittingTerminalSemanticPrefix`
* `quittingTerminalSemanticDebt_prefix_eq_blockAct`

This is the existing finite-dimensional `(U,B)` state.  Its cap formula is
the maximum-height projection of the response-graph formula in this note.

### Pure-time extremality and stopping-law mixture

`UniformEquilibrium/Quitting/Cycles/InfinitePureTimeExtremality.lean`

* `quittingRootSequencePureTimeTerminalValue`
* `quittingRootSequenceHazardTerminalValue_eq_hazardBellman`
* `exists_quittingRootSequencePureTimeTerminalValue_ge_sub`

`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`

* `quittingPureTimeBehaviorStrategy`
* `sSup_range_quittingTerminalPayoff_update_eq_pureTime`

`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`

* `quittingRootSequenceHazardTerminalValue_eq_expect_stoppingLaw`
* `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime`

These checked results justify treating a player's arbitrary behavioral
strategy as a stopping-law mixture of deterministic deadlines and Never.

### Compact stopping laws

`MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`

* `CompactStoppingTime`
* `CompactStoppingLaw`
* `compactStoppingLawEquivPMF`

`UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`

* `quittingHazardStoppingLaw`
* `quittingBehaviorStoppingLaw`

The compact stopping-law space supplies the natural actual-profile quotient,
but its weak topology does not make relative first-arrival evaluation
continuous.

`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`

* `quittingTerminalPayoff_update_compactStoppingLawProfile_finiteTime_tendsto`
* `eventually_forall_abs_quittingTerminalPayoff_update_pureTime_sub_lt`
* `quittingContinuationBestResponseValue_compactStoppingLawProfile_tendsto`
* `QuittingOpponentTightAtLawSequence.of_properOpponentLimit`

These declarations contain most of the analytic ingredients for
`FIXED_DEADLINE_HORIZONTAL_CONTINUITY.md`: a fixed proper replacement clock is
a tight opponent for every other player, while the replaced player's own cap
is invariant under changing its prescribed strategy.

`Research/Quitting/FiniteClockTerminalSemantics.lean`

* `quittingStoppingLawProfile`
* `quittingBehaviorStoppingLaw_stoppingLawProfile`
* `quittingFiniteClockSemanticReachable`

This Research module already owns exact independent stopping-law
reconstruction and confirms that the law-vector viewpoint is part of the
current finite-clock programme.  The response-graph state proposed here is a
completion of its strategic evaluation data, not an alternative behavioral
model.

### Marked absorption completion

`UniformEquilibrium/Quitting/AbsorptionPath/MetrizableMarkedAbsorptionPath.lean`

* `FiniteMarkedAbsorptionPath`
* `finiteMarkedStageGraph`
* `MetrizableMarkedAbsorptionPath`
* `metrizableLaw`
* `metrizableStageGraph`

`UniformEquilibrium/Quitting/AbsorptionPath/MetrizableMarkedAbsorptionDecoder.lean`

* `metrizableObstacleCap`
* `continuous_metrizableObstacleCap`

`UniformEquilibrium/Quitting/AbsorptionPath/MetrizableMarkedAbsorptionComposition.lean`

* `metrizableCompositionRelation`
* `MetrizableCompositionWitness`
* `metrizableAssociativityRelation`

This machinery already uses the central hyperspace idea: retain the complete
marked-stage graph, complete its obstacle cap continuously, and represent
composition by a correlated closed ternary relation.  The response graph here
is a smaller profile-tail object with a particularly simple exact one-root
shift law.  It is not a replacement for the richer marked cylinder.

### Existing no-go

`UniformEquilibrium/Quitting/Boundary/Repair/ObstacleMassDescentCounterexample.lean`

* `not_exists_obstacle_as_function_of_accumulatedMass`

That file already recommends carrying the stopping obstacle as a completed
hypograph of the full chronological trace.  The response-graph construction
implements this recommendation for the complete pure-time payoff trace rather
than only the accumulated absorption coordinate.

## Relation to `QuittingPayoffTable`

A quitting payoff table contains rewards for nonempty quitting coalitions and
a payoff at Never.  If one adjoins a variable all-Continue payoff vector `v`,
the current one-stage table is

```text
G_v(S) = r(S) for S nonempty,
G_v(empty) = v.
```

For a root `x`, the Bellman equation is

```text
v_current = E_x G_(v_tail).
```

Therefore a “matrix state” whose only changing row is all Continue is exactly
the ordinary payoff-vector Bellman state.  Adding the unrestricted cap gives
the existing `(U,B)` semantic state.  Changing any nonempty row would change
the original quitting game and would require a separate compiler back to the
fixed reward table.

## What appears new here

The following package was not found as a named repository object:

```text
closed graph of all pure-time response values
+ cap as graph maximum
+ exact affine shift under one root prefix.
```

It is closely aligned with, and partly anticipated by, the marked-absorption
hyperspace and obstacle no-go.  It should be viewed as a focused specialization
with a transparent transition law, not as a wholly separate compactness
programme.
