# Transition record

This is the sole repository document for historical and reproducibility facts
about the extraction of UniformEquilibrium from the GameTheory monorepo. All
other documentation describes only the current project.

## Reproducibility boundary

- Source repository revision:
  `171e014480bfd59f09403abc68af45b7f2c44fb5`.
- Pinned GameTheory revision after prerequisite ports:
  `02898a2d8b918f9b106a683420ca78c99867560e`.
- Toolchain: `leanprover/lean4:v4.32.2`.
- Synchronizer: `scripts/sync_from_source.py`.
- Source history was not imported.
- At this checkpoint the new repository deliberately has no initial commit and
  no remote. Only `.gitmodules` and the GameTheory gitlink are staged.

The source working tree also contained two relevant uncommitted documentation
changes. The L4/L5 actual-row localization status from
`docs/uniform-equilibrium/FRONTIER.md` is represented in `docs/FRONTIER.md`.
The complete `docs/uniform-equilibrium/QuittingProofFrontier.json` ledger is in
`docs/QuittingProofFrontier.json`, with evidence paths rewritten for the new
layout. Its added transition records are:

- `DROP-BARRIER-ELEMENTARY-BOUNDARY-FAMILY`;
- `LOCALIZE-L4-OUTSIDER-AT-ACTUAL-SOURCE-ROW`;
- `DROP-L5-TAIL-CLUSTER-SPLIT-FOR-ACTUAL-ROW-DEVIATION`;
- `DROP-SINGLETON-DEBT-AXIS-AND-STATIC-SOURCE-MATCH`; and
- `NOGO-PACKET-PRESERVING-LITERAL-SOURCE-RETURN`.

## Production source disposition

The source revision contains 917 UniformEquilibrium Lean paths when the root
umbrella is counted. Six generated `native_decide` certificate leaves were
excluded, leaving 911 source paths materialized in the new production tree:

- `UniformEquilibrium/Quitting/Examples/BlockPair/`
  `K11DyadicPhaseGroupZeroTwo.lean`;
- `UniformEquilibrium/Quitting/Examples/BlockPair/`
  `K11DyadicPhaseGroupThreeFive.lean`;
- `UniformEquilibrium/Quitting/Examples/BlockPair/`
  `K11DyadicPhaseGroupSixEight.lean`;
- `UniformEquilibrium/Quitting/Examples/BlockPair/`
  `K11DyadicPhaseNine.lean`;
- `UniformEquilibrium/Quitting/Examples/BlockPair/`
  `K11DyadicPhaseTenRootZero.lean`; and
- `UniformEquilibrium/Quitting/Examples/BlockPair/`
  `K11DyadicPhaseTenRootOne.lean`.

Two conjecture modules are target-owned overlays so open statements remain
proposition definitions rather than placeholder proofs:

- `UniformEquilibrium/Conjecture/UniformExistenceConjecture.lean`;
- `UniformEquilibrium/Quitting/Conjecture/Basic.lean`.

One GameTheory source module was rehomed because it belongs to the UE
diagnostic surface:

```text
GameTheory/Concepts/Correlation/PrivateRecommendationTargetSeparator.lean
  -> UniformEquilibrium/Diagnostics/PrivateRecommendationTargetSeparator.lean
```

## Mathematical library disposition

Fifteen generic modules owned by this research project moved to `MathUE`:

```text
AnalyticConeDichotomy
AnalyticConeLift
AnalyticFiniteRayMaximum
AnalyticMixedObstruction
CyclicMaxAffineBound
GradedConvolution
InfinitesimalRatFunc
Interval/PolynomialKrawczyk
Interval/PolynomialLipschitz
Interval/ScalarDyadicPolynomial
LinearAlgebra/CyclicSchur
LinearAlgebra/FiniteRayMaximum
LinearAlgebra/OwnerObstructionCokernel
Probability/AnalyticChargedCirculationFixedCoordinate
RamifiedBinomialBranch
```

The synchronizer preserves them through these explicit source roots and their
transitive `Math.*` dependencies:

```text
Math.AnalyticConeLift
Math.AnalyticFiniteRayMaximum
Math.CyclicMaxAffineBound
Math.GradedConvolution
Math.InfinitesimalRatFunc
Math.Interval.PolynomialKrawczyk
Math.Interval.ScalarDyadicPolynomial
Math.KrawczykBridge
Math.LinearAlgebra.CyclicSchur
Math.LinearAlgebra.OwnerObstructionCokernel
Math.Probability.AnalyticChargedCirculationFixedCoordinate
Math.RamifiedBinomialBranch
```

Three reusable modules belong to GameTheory instead:

- `Math/Minimax/DiscountedShapleyIdealObstruction.lean`;
- `Math/OnlineLearning/FixedShare.lean`;
- `Math/Probability/GeneratorRecurrentReduction.lean`.

They were committed in GameTheory as `f3eb38a` (`Port generic mathematical
infrastructure`). `GameTheory.lean` then exported the discounted Shapley
obstruction in `02898a2` (`Export discounted Shapley obstruction`). The earlier
UE prerequisite port and Lean 4.32.2 requirement are in `2ee854b`.

## Research disposition

Trust-clean experimental Lean was placed under `Research` and made reachable
from `Research.lean`. Forwarding-only shims were omitted when their declarations
already belonged to production. The current
`Research/General/KrawczykPolynomialLipschitzPrototype.lean` remains outside the
umbrella because it uses a dual-interval derivative interface not provided by
the current math library.

The maintained period-eleven entry point is
`Research.Quitting.BlockPair.K11`. Redundant `K11` filename prefixes were
removed inside the `K11/` directory without renaming declarations. Its 40
implementation modules are all reachable from the umbrella:

```text
ActiveEquationSemanticAdapter       ClearedSemantic
ConditionalAbsorption               ConditionalBlock
ConditionalBlockData                ConditionalData
ConditionalExactNash                ConditionalNash
ConditionalPackage                  ConditionalProfile
ConditionalStrategicCompiler        ConditionalUniformPayoff
ContinueMassPhase                   ContinueMassRoot
CycleProduct                        CyclicNumeratorAlgebra
CyclicNumeratorEvaluation           EndpointSemantic
EndpointSemanticOne                 EndpointSemanticThree
EndpointSemanticTwo                 EndpointSemanticZero
EvalImmediateReward                 FourPlayerExpectation
ImmediateSemantic                   ImmediateSemanticOne
ImmediateSemanticThree              ImmediateSemanticTwo
ImmediateSemanticZero               JacobianCache
KrawczykConditionalConsumer         KrawczykConditionalData
KrawczykConditionalSemantic         NumeratorAlgebra
NumeratorEvaluation                 PhaseArithmetic
PhaseValueRecurrence                Preconditioner
RowZeroCacheData                    RowZeroSemantic
```

### Period-eleven quarantine

The following source modules were not admitted because they contain
`native_decide` certificate leaves or depend on them:

```text
BlockPairK11Preconditioner.lean
K11ConditionalAdmissible.lean
K11PhaseSummaryAllAgreement.lean
K11PhaseSummaryCache.lean
K11PhaseSummaryGroupNine.lean
K11PhaseSummaryGroupNineTen.lean
K11PhaseSummaryGroupSixEight.lean
K11PhaseSummaryGroupTen.lean
K11PhaseSummaryGroupThreeFive.lean
K11PhaseSummaryGroupZeroTwo.lean
K11PhaseSummaryNineImmediateOne.lean
K11PhaseSummaryNineImmediateThree.lean
K11PhaseSummaryNineImmediateTwo.lean
K11PhaseSummaryNineImmediateTwoThree.lean
K11PhaseSummaryNineImmediateZero.lean
K11PhaseSummaryNineImmediateZeroOne.lean
K11PhaseSummaryNineSurvival.lean
K11PhaseSummarySemantic.lean
K11PhaseSummaryTenFactorOne.lean
K11PhaseSummaryTenFactorThree.lean
K11PhaseSummaryTenFactorTwo.lean
K11PhaseSummaryTenFactorZero.lean
K11PhaseSummaryTenImmediateOneSums.lean
K11PhaseSummaryTenImmediateOneTermGroups.lean
K11PhaseSummaryTenImmediateThreeSums.lean
K11PhaseSummaryTenImmediateThreeTermGroups.lean
K11PhaseSummaryTenImmediateTwoSums.lean
K11PhaseSummaryTenImmediateTwoTermGroups.lean
K11PhaseSummaryTenImmediateTwoThree.lean
K11PhaseSummaryTenImmediateZeroOne.lean
K11PhaseSummaryTenImmediateZeroSums.lean
K11PhaseSummaryTenImmediateZeroTermGroups.lean
K11PhaseSummaryTenMaskGroupEightEleven.lean
K11PhaseSummaryTenMaskGroupFourSeven.lean
K11PhaseSummaryTenMaskGroupTwelveFifteen.lean
K11PhaseSummaryTenMaskGroupZeroThree.lean
K11PhaseSummaryTenQuitFactors.lean
K11PhaseSummaryTenSurvivalLower.lean
K11PhaseSummaryTenSurvivalProducts.lean
K11PhaseSummaryTenSurvivalUpper.lean
K11RowZeroCachedInclusion.lean
K11RowZeroCacheProof.lean
K11RowZeroDerivativeShard0.lean
K11RowZeroNodeCongruence.lean
K11RowZeroPhaseZeroOpponentScalarTrace.lean
K11RowZeroPhaseZeroOtherScalarTrace.lean
K11RowZeroPhaseZeroScalarTrace.lean
K11RowZeroRecurrenceCongruence.lean
K11RowZeroScalarRecurrence.lean
K11RowZeroScalarShard0.lean
```

These trust-clean source files were also omitted because their dependencies are
quarantined or because they are generated audit/probe artifacts rather than
maintained interfaces:

```text
K11ColumnZeroPhase8910Leaves.lean
K11ColumnZeroProjection.lean
K11ColumnZeroStructuralZero.lean
K11ConditionalCompilerAudit.lean
K11ConditionalCompilerOleanAudit.lean
K11ConditionalDataAudit.lean
K11KrawczykConditionalConsumerAudit.lean
K11OpponentPhaseSummaryPrototype.lean
K11PhaseSummaryCenter29.lean
K11PhaseSummaryCenter30.lean
K11PhaseSummaryTenAllAgreement.lean
K11PhaseSummaryTenAllAgreementAudit.lean
K11PhaseSummaryTenAxiomAudit.lean
K11PhaseSummaryTenFactorData.lean
K11PhaseSummaryTenImmediateOne.lean
K11PhaseSummaryTenImmediateOneData.lean
K11PhaseSummaryTenImmediateThree.lean
K11PhaseSummaryTenImmediateThreeData.lean
K11PhaseSummaryTenImmediateTwo.lean
K11PhaseSummaryTenImmediateTwoData.lean
K11PhaseSummaryTenImmediateZero.lean
K11PhaseSummaryTenImmediateZeroData.lean
K11PhaseSummaryTenMaskProbabilities.lean
K11PhaseSummaryTenMaskProbabilityData.lean
K11PhaseSummaryTenSurvival.lean
K11RowZeroActiveCoordinateDAG.lean
K11RowZeroColumns123Semantic.lean
K11RowZeroJacobianScalarTraceCoord1.lean
K11RowZeroJacobianScalarTraceCoord2.lean
K11RowZeroJacobianScalarTraceCoord3.lean
K11RowZeroJacobianScalarTraceShared.lean
K11RowZeroPhaseOnePayloadProbe.lean
K11RowZeroPhaseScalarPayloadProbe.lean
K11RowZeroPhaseZeroCoord1LiteralShared.lean
K11RowZeroPhaseZeroOtherScalarProbe.lean
K11RowZeroProductionImportProbe.lean
K11RowZeroRawSemanticCacheAudit.lean
K11RowZeroScalarRecurrenceAudit.lean
```

The source `K11ConditionalCompiler.lean` was omitted because
`ConditionalPackage.lean` exposes the same `compile` theorem through the
compositional chain; importing both redeclares the theorem in one namespace.
The included `Preconditioner.lean` keeps the exact data but replaces one
reducible generated check with kernel reduction. No `.olean`, cache, generated
JSON certificate, or Python cache was copied.

## Questions, manuscripts, and supporting documents

### Source-only idea locators

The source monorepo used `ideas/` for exploratory claims. That directory was
not extracted. Backticked `ideas/...` paths retained in historical audits and
experiment reports are provenance locators at the source revision named above,
not live target-repository documentation or current open obligations. When the
adjacent source checkout is available they resolve under
`../../GameTheory/ideas/` relative to this repository.

New work follows the target workflow instead: unresolved derivations belong in
GitHub Discussions, bounded obligations in Issues, and checked integration in
Pull Requests. The durable contract is [`docs/PIPELINE.md`](docs/PIPELINE.md).

The live reverse questions became stable task packets under `Reverse/Tasks`:

- Q188: paid root-or-tail transport;
- Q189: cancellation-safe aggregation;
- Q190: singleton-toggle chronology;
- Q191: singleton tight minimum face;
- Q192: four-by-four Q classification;
- Q193: four-player debt invariant; and
- Q194: semialgebraic barrier completeness, including the Palm/spine reduction.

Question archives, answer logs, and orchestration traces were not copied.

The three top-level TeX manuscripts under the source `ephemeral/` directory
were renamed and placed under `docs/manuscript/`:

```text
QuittingGameFourPlayerPeriodTwoCalibration.tex
  -> FourPlayerPairedSingletonCalibration.tex
QuittingGameFrontierExactGap.tex
  -> SemanticGapForFiniteQuittingGames.tex
QuittingGameSemanticFrontierGuide.tex
  -> SemanticFrontierGuide.tex
```

The semantic guide in the target already defines `B_i` at first use. The
four-player and semantic-gap manuscripts differ from their source inputs only
in intentional presentation cleanup.

## Verification at the checkpoint

- All 911 expected production source paths are present.
- The trust check passed over 1,372 Lean files.
- Static import resolution found no unresolved local imports.
- No non-import Lean code line exceeds 100 characters.
- Every period-eleven implementation module is reachable from its umbrella.
- All 44 evidence paths in the frontier ledger resolve.
- No full project build was run.
