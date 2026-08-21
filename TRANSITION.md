# Transition record

This is the sole repository document for historical and reproducibility facts
about the extraction of UniformEquilibrium from the GameTheory monorepo. All
other documentation describes only the current project.

## GameTheory semantic rewrite

The `migration/game-theory-rewrite` branch advances the GameTheory gitlink from
`02898a2d8b918f9b106a683420ca78c99867560e` to
`47b1c3dc1afa9f9e3e2639aa9d94cbf1d390f892`. The `v1-final` tag remains the
source reference for declarations absent from the rewritten library.

Forty game-independent modules moved from the v1 source surface into
`MathUE`. Seventy-three proof-facing modules moved into
`UniformEquilibrium/ProofView`; their declarations retain the mathematical
names used by the project. `UniformEquilibrium/ProofView/Native` supplies the
finite-PMF, public-history, execution, payoff, unilateral-deviation, and
uniform-payoff equivalences with GameTheory's canonical stochastic runner.
The bridge proves an exact iff for the central uniform-equilibrium-payoff
predicate rather than relying on source-level compatibility.

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
UniformEquilibrium/ProofView/Concepts/Correlation/PrivateRecommendationTargetSeparator.lean
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
already belonged to production. The source
`Research/General/KrawczykPolynomialLipschitzPrototype.lean` is not retained as
a forwarding module; its surviving generic interface is maintained in
`MathUE/Interval/PolynomialLipschitz.lean`.

The final ownership normalization retained only genuine experimental deltas.
`Research.Quitting.OwnerSoloCertification` and
`Research.General.CycleStrataGlobalFeedback` import their production or
`MathUE` owners and contain only their ownerwise/stagewise and
landed-stratum/phase-conflict results, respectively. The five phase/refusal
declarations formerly in
`Research.Counterexamples.Pairwise.CP172ExtractedClaims` are owned by
`UniformEquilibrium.Quitting.Classification.SingletonPacketDefectAlgebra`; the
Research file was removed without a compatibility API. The CP172 extraction
report remains an experiment record pointing to the canonical best-response,
collision, annotation, and packet-algebra owners.
`PaidNonexactCapStackAccount` and `Question175OwnerNeverFloor` likewise use the
canonical cap-debt and coalition-toggle declarations instead of copied bodies.
The stale Research-only `FullRateStationaryVerifier` forwarding module was
removed; the maintained full-rate verifier remains under
`UniformEquilibrium.Quitting.Stationary`.
The promoted `CancellationSafeAggregationStationaryRegression` and generic
`SharedPunishmentCycle` files were removed, as were three declaration-free
`*AxiomAudit` shims; the exhaustive generated `AxiomAudit.lean` owns project
axiom coverage.

The maintained period-eleven entry point is
`Research.Quitting.BlockPair.K11`. Redundant `K11` filename prefixes were
removed inside the `K11/` directory without renaming declarations. Its local
manifest records the exact Research inventory.

The later lane split kept the parameterized Krawczyk data, semantic checker,
and exact-zero consumer in Research while moving the four concrete payloads
and their sole instance assembly to `Experiments/certsearch/block_pair/K11/`:

```text
UniformEquilibrium/Quitting/Examples/BlockPair/K11DyadicData.lean
  -> Experiments/certsearch/block_pair/K11/DyadicData.lean
Research/Quitting/BlockPair/K11/Preconditioner.lean
  -> Experiments/certsearch/block_pair/K11/Preconditioner.lean
Research/Quitting/BlockPair/K11/JacobianCache.lean
  -> Experiments/certsearch/block_pair/K11/JacobianCache.lean
Research/Quitting/BlockPair/K11/RowZeroCacheData.lean
  -> Experiments/certsearch/block_pair/K11/RowZeroCacheData.lean
```

No Research or production module imports the concrete evidence lane. The
Research checker takes preconditioner injectivity directly and proves a unique
canonical residual zero in the certified ball, including interval-box
membership. The concrete assembly is `checkedK11KrawczykData`; no forwarding
declarations preserve the old data locations.

The parallel `ConditionalStrategicCompiler.lean` was later removed in favor of
the stronger compositional route ending at `ConditionalPackage.lean`; the
compositional compiler derives the cleared equation, recurrence, and absorption
facts which the parallel compiler accepted as hypotheses. The duplicate
`ActiveEquationSemanticAdapter.lean` was also removed. `RowZeroSemantic` now
uses the canonical production theorem in
`UniformEquilibrium.Quitting.Examples.BlockPair.K11ActiveEquationInterval`.
The six-module scalar numerator chain (`PhaseArithmetic`, `NumeratorAlgebra`,
`NumeratorEvaluation`, `CyclicNumeratorAlgebra`, `CycleProduct`, and
`CyclicNumeratorEvaluation`) was removed after its sole downstream use was
rewired to the stronger canonical recurrence in
`UniformEquilibrium.Quitting.Examples.BlockPair.K11System`.

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
No `.olean`, cache, original generated JSON certificate, or Python cache was
copied.

### Period-eleven generated-data provenance

The surviving `Preconditioner.lean` header named
`q117_krawczyk_certificate.json` and
`q117_emit_lean_preconditioner.py`. Neither named artifact was present in this
repository or the adjacent migrated source working tree at
`/mnt/d/workspace/games/UniformEquilibrium` during the provenance audit. The
`RowZeroCacheData.lean` header likewise named `q117_verify.py`, which was not
present. `DyadicData.lean` and `JacobianCache.lean` had no surviving source-data
or producer record. The complete tree of source revision
`171e014480bfd59f09403abc68af45b7f2c44fb5` was also searched in the current
`GameTheory` submodule. It contains neither named q117 artifact nor a matching
K11 JSON, Python, dyadic-data, Jacobian-cache, row-zero-cache, or preconditioner
path.

The four checked-in Lean payload files are consequently classified as migrated
evidence without a reproducible original producer. The structured record
`Experiments/certsearch/block_pair/k11_generated_data_manifest.json` stores
full-file hashes and formatting-independent logical hashes of the exact dyadic
box, preconditioner, Jacobian, and row-zero cache payloads.
`scripts/check_k11_generated_data.py` deterministically checks those hashes,
the payload shapes, dyadic precisions and scale, interval ordering, matrix row
routing and final constructors, and the row-zero absolute-sum cache. It is a
freshness and integrity check only: it neither reconstructs the missing JSON
nor recomputes any payload from the game data. Thus the record does not supply
independent numerical provenance, an adapter from recovered source data, or
any stronger mathematical claim than the existing conditional Lean consumers.

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

The certsearch reference tables retain the following source locators:

- `G_EPS` at `ε = 1/10` came from
  `ideas/AbsorbingCycleCarrier/APublishedWeightSitsInTheCycleExistenceHole.md`;
- `Q154_WEIGHT` and the label `B_ij = r_i({j}) - r_i({i})` came from
  `questions/Question154-DoRelaxedCyclesDivergeWithoutAnExactOne.md`, section
  2, equation (9);
- `TWO_PLAYER_COUNTEREXAMPLE` is owned by
  `UniformEquilibrium/Quitting/Boundary/Repair/DisjunctionCounterexample.lean`;
- `FTV_WEIGHT` is the unperturbed table in
  `UniformEquilibrium/Quitting/Examples/Cyclic/ThreePlayer/AdmissibleCycle.lean`;
- `HOSTILE_WEIGHT` is owned by
  `UniformEquilibrium/Quitting/Punishment/IsolatedPunishmentCeiling.lean`;
- the circulation mode was launched from
  `ideas/QuittingGameConjecture/SingletonFaceCirculationsSteerOrbits.md`;
- the repaired four-player follow-up was
  `questions/Question160-TheFourPlayerCyclicFamilyPhaseDiagram.md`; and
- the earlier `Experiments/BackwardStableComplementarity.lean` locator is now
  owned by
  `UniformEquilibrium/Quitting/Root/EndpointBackwardStability.lean`.

The pairwise-consistency campaign was launched from
`questions/Question172-BoundedBellmanChargeVersusTerminalInstability.md`.
That source packet was provenance, not an implementation dependency, and the
question archive was not extracted. Its earlier collision-mass locator
`Math/PMFProduct/CollisionMass.lean` is now owned by
`MathUE/PMFProduct/CollisionMass.lean`.

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

## Experiment lane transition

The registered Base suite now owns the reproducible programs and their paired
reports. Three formerly report-only scripts were registered as `E34`--`E36`:

```text
Experiments/Base/cap_nash_endpoint_transport_search.py
Experiments/Base/minimum_plateau_q_budget_search.py
Experiments/Base/semantic_final_regime_search.py
```

Five bounded standalone programs were moved from `Experiments/Base/` to
`Experiments/Probes/`; their old extraction paths were:

```text
Experiments/Base/backward_absorption_gamma_eta.py
Experiments/Base/harmonic_module_audit.py
Experiments/Base/homotopy_germ_endgame.py
Experiments/Base/owner_cokernel_typed_holonomy.py
Experiments/Base/reset_return_selection_search.py
```

The standalone Krawczyk certifier moved from
`Experiments/Base/krawczyk_cycle_certifier.py` to
`Experiments/certsearch/krawczyk_cycle_certifier.py`, and the certsearch bridge
was updated to consume its new path. Earlier E66 prose named the nonexistent
top-level path `Experiments/krawczyk_cycle_certifier.py`; the extracted tracked
file was the Base path above. No compatibility aliases are retained.

The concrete arithmetic replay
`Research/Semantics/SemanticFinalRegimeArithmetic.lean` moved beside its
source experiment as `Experiments/Base/SemanticFinalRegimeArithmetic.lean`.
It checks selected scalar instances and is experimental evidence rather than a
reusable Research interface.

Thirty-two Research modules whose declarations used `Experiments.*` or
`GameTheory.Experiments.*` namespaces were normalized to `Research.*` without
aliases. Their theorem statements and bodies were unchanged.

At source checkpoint `42459d79`, three then-local prototypes were checked with
targeted Lean invocations, not a full build:

```text
Experiments/DiscreteHazardStopping.lean
Experiments/PhaseOccupationDuality.lean
Experiments/QuittingSharedPunishmentCycle.lean
```

Their maintained mathematical owners are now
`MathUE/Probability/DiscreteHazardStopping.lean`,
`MathUE/Probability/PhaseOccupationDuality.lean`, and
`MathUE/CyclicExposure.lean`. The interim evaluation and promotion order were
not retained as current documentation.

## Verification at the checkpoint

- All 911 expected production source paths are present.
- The trust check passed over 1,372 Lean files.
- Static import resolution found no unresolved local imports.
- No non-import Lean code line exceeds 100 characters.
- Every period-eleven implementation module is reachable from its umbrella.
- All 44 evidence paths in the frontier ledger resolve.
- No full project build was run.

## Literature lane flattened (2026-08-19)

`Research.Literature` was renamed to `Literature` and the lane flattened: the
`Literature/Papers/` directory was removed with each paper record moving to
`Literature/<Paper>.lean`, namespaces `Literature.Papers.*` and
`Research.Literature.*` becoming `Literature.*`; the aggregate `All.lean` and
`Coverage.lean` were deleted with the generated manifest `Literature.lean`
taking reachability duty; and the active claim-consumer modules
(`Research/Literature/SolanAndVieille2001/`, `Research/Literature/Sorin1986/`)
were merged into their paper files. In the same restructuring Research became
a terminal lane (imported nowhere outside itself), forcing the promotion of
the Experiments-consumed Research closure into `UniformEquilibrium` and the
demotion of the K11 conditional chain into `Experiments`.
