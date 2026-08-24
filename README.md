# UniformEquilibrium

`UniformEquilibrium` is a Lean research project aimed at solving—or, failing
that, sharply characterizing—the uniform-equilibrium conjecture family for
finite stochastic games. It develops formal constructions, obstructions,
examples, and existence results on top of the pinned `GameTheory` submodule.

A uniform-equilibrium payoff is one fixed payoff target such that, for every
positive accuracy, some behavioral profile both approaches that target and
caps every unilateral behavioral deviation over every sufficiently long finite
horizon. The profile may depend on the accuracy; the target may not.

## Status at a glance

<!-- BEGIN GENERATED STATUS -->
This table is generated from [`docs/ProjectStatus.json`](docs/ProjectStatus.json).

| Claim | Status | Exact declaration | Scope |
| --- | --- | --- | --- |
| Finite stochastic games with state-independent action sets | Open proposition | [`uniformDeviationCapConstructorConjecture`](UniformEquilibrium/Conjecture/UniformExistenceConjecture.lean) | General finite stochastic-game existence; padding state-dependent actions is not silently semantics-preserving. |
| All finite quitting games | Open proposition | [`quittingUniformEquilibriumPayoffConjecture`](UniformEquilibrium/Quitting/Conjecture/Basic.lean) | The quitting specialization is distinct from the general conjecture. |
| Two-player finite quitting games | Unconditional theorem | [`quittingGame_exists_uniformEquilibriumPayoff_twoPlayer`](UniformEquilibrium/Quitting/Classification/TwoPlayer/Existence.lean) | All reward tables and all unilateral behavioral deviations. |
| Three-player finite quitting games (`Fin 3`) | Unconditional theorem | [`quittingGame_exists_uniformEquilibriumPayoff_threePlayer`](UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean) | All reward tables on the concrete player type `Fin 3`; reindexing is recorded separately. |
| Terminal approximate Nash existence and uniform-payoff existence | Equivalence theorem | [`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`](UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean) | Finite quitting games; terminal approximate profiles are required at every positive error. |
| Quitting-game nonexistence and a fixed terminal exploitability gap | Equivalence theorem | [`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`](UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean) | A counterexample must quantify over every behavioral profile. |
| Reduced finite support-rank alternative | Conditional structural theorem | [`reducedSupportRankAlternative_of_positiveMinimumDebt`](UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean) | Every supplied positive minimum of terminal semantic debt reaches positive total slope, zero-debt support entry, or an off-minimum actual replacement endpoint with an eventually paid first-disagreement row. Flat charged circulation is no longer an independent terminal branch: it gives strict positive-debt-support descent or the existing paid-row exit. The three remaining producer obligations are not solved. |
| Four-player quitting counterexample residual | Unconditional alternative theorem | [`uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual`](UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean) | For every supplied finite coordinate bound, a Fin 4 reward table has a uniform-equilibrium payoff or, on the same table, a terminal exploitability witness, full recursive normal core, all-player punishment normality, a normalized singleton packet with full support and an explicit positive coordinate floor, and ResidualHardClass. Thus the projective-Q-bar chamber is solved; the hard residual is not. |
| Finite principal dispatch in the four-player hard residual | Conditional structural theorem | [`hardPrincipalDispatch`](UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardPrincipalDispatch.lean) | Every supplied quantitative full-support hard residual has a size-two mutually harmful principal with outside positive helpers, or a size-three principal with an external positive helper or cyclic orientation and nonpositive determinant. This is singleton-matrix structure, not a semantic consumer. |
| Paid-chain refinement of the four-player strict-toggle residual | Conditional structural theorem | [`fullSupport_fullNormalCore_with_paidRefinedCycle_of_finFour`](UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictToggleLargeBasePaidChain.lean) | A bounded Fin 4 table with a terminal exploitability witness supplies, on the same table, full normal core, a quantitative full-support packet, and an actual reachable strict-toggle cycle. Its large-base branch is exactly a two-plus-two partition and enters the checked pure-or-mixed paid normal chain; the singleton-base and empty-base gaps remain. |
| Two-cycle lasso and hard-principal alignment | Conditional structural theorem | [`exists_collisionGeometry_with_alignedTwoCycleHardPair_or_long`](UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/TwoCycleLassoHardPairAlignment.lean) | Every supplied Fin 4 hard residual has collision-anchored marked preemption geometry such that each of the eight two-cycle constructors uses its literal cycle pair as the nonprojective card-two crossing, or the geometry is one of the nine length-three/four cases. This formalizes alignment bookkeeping; it eliminates no semantic case and supplies no strategy consumer. |
| Three-cycle lasso and hard-principal incidence | Conditional structural theorem | [`markedThreeCycleHardPrincipalIncidence_or_nonThree`](UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/ThreeCycleLassoHardPrincipalIncidence.lean) | Each of the six marked length-three constructors enters a same-label external-helper, negative-determinant hard-cycle, or outsider-containing hard-principal alternative with exact owner/collider incidence. This is finite singleton-matrix structure, not a semantic consumer. |
| Four-cycle lasso and hard-principal alignment | Conditional structural theorem | [`markedFourCycleHardPrincipalAlignment_or_nonFour`](UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FourCycleHardPrincipalAlignment.lean) | Each of the three rooted four-cycle constructors sends every selected hard pair or triple to a shorter strict preemption cycle or a literal unique-outside helper, retaining the collision-marker position. Together with the two- and three-cycle theorems this covers all seventeen marked constructors, but closes no semantic chamber. |
| Large-base paid stationary semantic handoff | Conditional structural theorem | [`exists_largeBasePaidStationaryHandoff`](UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean) | On four players, every supplied support-two paid-chain residual admits a reselected singleton-owner stationary source with debt concentrated at that owner. Repairing the owner transfers the terminal gap to a free player and yields a literal paid first-disagreement row. The endpoint dispatch now gives localized floor failure or a literal exact infinite floor orbit whose finite segments satisfy the collision budget. Charged payoff recurrence would yield a uniform payoff, so a terminal witness forces every fixed absorption threshold eventually to disappear; no payoff near-return is produced. |
| Rooted-two atomic collision and stationary two-debtor handoff | Conditional structural theorem | [`ownerLeaveCollisionChain_outsiderJoin_or_stationaryTwoDebtorHandoff`](UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/LeaveJoinStationaryTwoDebtorHandoff.lean) | In the Fin 4 hard residual, punishment normality first forces a full-terminal-gap collision at every singleton. The rooted-two owner-leave arm then either retains a full-gap enlarged-pair outsider join or constructs an actual stationary source with a quantitative pair/triple atom, two all-behavior solved punishment-floor-safe coordinates, debt on at most the other two labels, and a literal paid first-disagreement row. No checked consumer turns that source into a Bellman return, terminal approximate Nash profile, or uniform payoff. |
| Stationary paid carrier linear debt moat | Conditional quantitative no-go theorem | [`source_debt_or_absorption_le_four_mul_error_div`](UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/StationaryPaidCarrierLinearDebtMoat.lean) | The actual stationary two-debtor source composes with the complete Fin 4 minimum-fiber basin: either its semantic debt is uniformly above the global minimum or every approximate root at its literal prescribed payoff pays linearly for absorption. Exact roots in the low-debt arm are the all-Continue identity, and exact charged punishment-floor paths require the off-minimum arm. This is an obstruction consumer, not a charged-root or payoff-return producer. |
| Pair-base paid/reset endpoint boundary | Conditional structural and no-return theorem | [`QuittingTerminalExploitabilityWitness.nonempty_finFour_pairBasePaidResetEndpointBoundary`](UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointEdge.lean) | On Fin 4, the actual pair-base paid/reset target either violates the punishment floor at one forced-Quit base coordinate or supplies an exact punishment-floor endpoint edge at its aligned prescribed payoff. The floor violation gives a source-matched Quit-now-to-Never paid row and a zero-debt unilateral repair of that coordinate, but preserves no other Nash or floor data. The endpoint edge has positive absorption unless singleton domination makes it the literal all-Continue self-loop. Under a terminal-exploitability witness every positive such edge has a fixed payoff neighborhood which no later reachable admissible state can re-enter, so the checked payoff-return consumer is unavailable. Separately, cap-Nash converts to prescribed-payoff Nash exactly when option surcharge equals survival-weighted debt; the positive-survival reset branch does not satisfy the simpler support-killing criterion. No uniform payoff follows. |
| Strict minimum-plateau isolation in a four-player counterexample | Conditional counterexample reduction | [`exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff`](UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean) | If a reward table on literal Fin 4 has no uniform-equilibrium payoff, every pair in one compact global positive-minimum terminal-semantic debt fiber is punishment-normal and uniformly strictly above every own singleton reward. Their prescribed-payoff projection lies in one open tube on which all-Continue is the unique exact product root, and every carrier tail below one fixed excess-debt threshold enters that tube. Thus a positively absorbing exact carrier-tail root pays the threshold. This does not control approximate roots whose incidence tends to zero, construct a nonlocal incoming tail, or prove the four-player conjecture. |
| Exact Nash--Bellman paths ending in an all-Continue basin | Conditional no-go theorem | [`quittingAnchoredPath_backward_rigidity_of_unique_allContinue`](UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRigidity.lean) | For any supplied payoff set on which all-Continue is the unique exact endpoint-Nash product root, every finite exact anchored Nash--Bellman path ending there is constant and has zero absorption. Checked corollaries exclude absorbing cyclic continuation, give a terminal-seam distance floor for charged blocks, and make every exact infinite path converging to an interior point constant from time zero. The theorem says nothing about approximate roots or an incoming edge whose continuation tail lies outside the basin. |
| Linear absorption defect in a strict all-Continue basin | Conditional quantitative no-go theorem | [`exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`](UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean) | Every hypothetical no-uniform Fin 4 table has one bounded open neighborhood of its complete prescribed minimum-fiber projection and one positive constant charging root absorption linearly by literal total Nash defect at every scale. Along exact-successor paths ending near that fiber, a sufficiently small aggregate declared-error budget keeps every node local and bounds total absorption and path diameter; any first exit pays a fixed aggregate-error toll. The theorem produces no path and does not control a nonlocal incoming continuation or a nonvanishing aggregate-error budget. |
| Carrier-source fixed-charge debt-or-error gate | Conditional quantitative no-go theorem | [`debt_or_error`](UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourCarrierSourceChargeDebtErrorGate.lean) | For every positive charge threshold in a hypothetical no-uniform Fin 4 table, a finite approximate successor path beginning at the prescribed payoff of an actual terminal-semantic carrier either starts a fixed debt distance above the global minimum or spends a fixed aggregate root-error budget. Exact charged punishment-floor paths therefore cannot start on the minimum fiber. The full-replacement paid profiles are eventually off-minimum, but no checked theorem identifies a near-return path source with those profiles or constructs a return. |
| Fin4 charged blocker closure boundary | Conditional quantitative obstruction theorem | [`stationaryHandoff_or_exactRepayment_and_paidResetBoundary`](UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ChargedSoloBlockerClosureDispatch.lean) | At every positive charged solo-blocker gate, the pair-premium arm now enters an actual pair-base or leave-join stationary two-debtor source with a terminal-gap paid row; otherwise every anchored exact floor orbit repays a fixed amount in the blocker coordinate. Independently, an actual pair-base profile co-realizes a paid row and fixed-law reset target from the global minimum. The gate's literal exact root has zero semantic-debt drop, the paid debtor and reset owner differ, and the dispatch prefixes a separate returned pair without constructing an endpoint-Nash punishment-floor edge or return path, so no uniform payoff follows. |
| Fin4 solo-wall dispatch and pair-base handoff | Conditional structural reduction | [`not_exists_outwardUniformSoloCarrierChain_of_normal`](UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourSoloWallDispatch.lean) | From a unique-debtor exact solo gate, a uniform opponent-absorption floor gives strict carrier-debt descent; otherwise finite solo prefixes reach a first outsider wall, while compactification and punishment normality exclude indefinite uniformly interior solo continuation. A pair premium at the wall now yields an actual singleton-base, leave-join, or pair-base stationary source. The pair-base source has quantitative off-base absorption, a heavy strict-superset atom, both free coordinates solved against unrestricted deviations, base-localized debt, and a literal paid row. It is freshly reselected rather than chronologically reached, and no payoff return follows. |
| Terminal exploitability gaps for four-player full-core deadlock completions | Unconditional family theorem | [`HasTerminalExploitabilityGap.fullCoreDeadlock_le_sharperBound`](UniformEquilibrium/Diagnostics/Quitting/FullCoreDeadlockDebtBound.lean) | For arbitrary nonsingleton coalition rewards, every terminal exploitability gap over a completion of the displayed normalized singleton matrix is at most 1227/96755; this does not prove that the gap vanishes or produce a uniform equilibrium. |
| Exact uniform equilibrium for the literal full-core deadlock completion | Unconditional theorem | [`reward_isUniformEquilibriumPayoff_jointBlock`](UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockJointBlockEquilibrium.lean) | The named zero-multiquitter completion FullCoreDeadlock.reward has an exact uniform-equilibrium payoff, certified by a three-phase product block with supports {0}, {2}, and {1, 3}; arbitrary full-core completions retain only the separate 1227/96755 bound. |
| Uniform equilibrium on a rational polyhedral full-core deadlock slice | Conditional family theorem | [`isUniformEquilibriumPayoff_of_isDeadlockRationalJointBlockCompletion`](UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockRationalPolyhedralBlock.lean) | For any baseline s, including negative coordinates, a completion satisfying IsDeadlockRationalJointBlockCompletion reward s has target deadlockRationalBlockValue s. The predicate fixes the full-core singleton matrix, requires reward({1,3}) = s, and imposes eight explicit collision-cap inequalities; it describes an unbounded nonlocal polyhedral slice, not all full-core completions. |
| Finite reward-range sufficient condition for stationary quitting equilibria | Conditional theorem | [`exists_uniformEquilibriumPayoff_of_conditionalFaceGapRange`](UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean) | Strict lower and weak upper conditional reward-range comparisons yield a stationary behavioral terminal Nash and a uniform-equilibrium payoff; the hypotheses are a sufficient source-data condition, not a universal classification. |
| Cycle-balanced fixed-sign quitting influence tables | Unconditional family theorem | [`quittingGame_exists_uniformPayoff_of_cycleBalancedSignConsistentInfluence`](UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean) | Fixed positive, negative, or absent pair influences, with positive sign product on every directed simple influence cycle, produce a literal sure-exit coalition and a uniform-equilibrium payoff against all unilateral behavioral deviations. Within the fixed-sign class, absence of every sure-exit coalition forces a negative simple influence cycle. |
| Acyclic augmented solo-preemption tables | Unconditional family theorem | [`exists_uniformEquilibriumPayoff_of_acyclic_augmentedSoloPreemption`](UniformEquilibrium/Quitting/Classification/Existence/AcyclicSoloPreemption.lean) | For every nonempty finite player type, acyclicity of the strict solo-preemption graph augmented by own-singleton sign edges gives either exact all-Continue play or arbitrarily accurate solo-owner stationary profiles with a fixed singleton target and explicit q times pair-premium exploitability bound. Thus this architecture has a uniform-equilibrium payoff and cannot force positive designated pair masses; directed augmented cyclicity is necessary, not sufficient, for the incentive-gadget route. |
| Participant-only quitting tables and passive-reward obstruction | Unconditional family theorem | [`exists_stationary_uniformEquilibriumPayoff_of_participantOnly`](UniformEquilibrium/Quitting/Classification/Existence/ParticipantOnlyStationary.lean) | Every finite quitting table whose absent-player reward coordinates vanish has an exact stationary terminal Nash profile against all unilateral behavioral deviations and a uniform-equilibrium payoff. For an arbitrary table, a stationary profile has terminal exploitability at most twice the empty-safe passive reward magnitude, so any universal terminal gap gamma requires passive magnitude at least gamma/2. This does not give exact equilibrium existence for arbitrary tables. |
| Six-player one-pair mass ledger and direct target lock | Unconditional quantitative theorem | [`integerReward_exploitability_ge`](UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean) | A complete Fin 6 integer table forces terminal exploitability at least 31(1-a)/66 and hence the exact first-pair and leftover bounds; bounded outsider-coordinate completions retain robust estimates. Every actual behavioral profile satisfies the sharp two-pair square-root clock inequality, so the second-pair upper bound is unconditional. Every direct cross-penalty completion nevertheless has a pure exact target equilibrium and uniform payoff, so no positive second-pair mass is forced. |
| Literal strict finite odd interval-blocker cores with arbitrary outside-player payoffs | Conditional family theorem | [`isUniformEquilibriumPayoff_of_literalStrictFiniteOddIntervalBlockerCore`](UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCoreRowAdapter.lean) | For every embedded odd cyclic core of finite size at least three, the literal row-extrema sandwich L_i^+ < C_i^- <= C_i^+ < H_i^- yields an exact stationary all-behavior uniform-equilibrium payoff. Core continuation rewards may vary by terminal coalition inside their separated band; arbitrarily many outside players and every outside-player reward coordinate remain unrestricted. The constant-passive theorem remains a separately checked special case. Overlapping or weak bands and arbitrary negative influence cycles are not covered. |
| Strategically precompact watchdog and proper-tail boundary | Conditional obstruction theorem | [`exists_lateOrNeverMass_escape_of_not_properStrategicallyApproximable`](UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean) | Strategically totally bounded deviation families cannot force a fixed all-profile gain, and one arbitrary nonprecompact player range is still harmless, so a surviving selector needs two distinct identities with fixed late-finite mass. Conditional on failure of proper strategic approximation, a range has fixed late-or-Never escape; a strategically totally bounded such range contains a nonproper essential Never witness. The compact stopping-law barycenter is checked, but the proper-sentinel compact Nash theorem still lacks a joint weak-continuity lemma, so failure of proper approximation is not proved for every selector identity. |
| Finite quitting games with projective-Q-bar normalized singleton matrix | Unconditional family theorem | [`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell`](UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean) | Ambient projective Q-bar yields a uniform-equilibrium payoff against every unilateral behavioral deviation. The punishment-normal path decoder is constructed through the deleted-survival Snell fork; this does not cover ResidualHardClass. |
| At-most-one-owner calendars on the Solan--Vieille boundary table | Unconditional obstruction | [`Schedule.one_over_sixtyEight_lt_literal_exploitability`](UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardSemantic.lean) | Every arbitrary finite or infinite deterministic calendar with at most one positive quitting hazard per date has literal all-behavior terminal exploitability E satisfying 1 <= 14 E^2 + 67 E and hence E > 1/68. This rules out that strategy architecture on one residual-hard table; the same game has a checked two-owner uniform equilibrium. |
| Supplied finite-orbit obstruction in quitting-game semantics | Conditional obstruction | [`not_exists_uniformEquilibriumPayoff_of_suppliedSimonNecessity`](UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SuppliedCorrespondence.lean) | The production-semantic individually rational, near-feasible finite-orbit carrier is equivalent to the corresponding arbitrarily-large finite-variation condition. HasQuittingSimonFiniteCellLyapunovCertificate and its direct obstruction adapter consume supplied exact finite-cell data; the combined terminal-gap capstone additionally assumes SuppliedQuittingSimonFiniteOrbitNecessity, exclusion of stationarily generated approximate equilibria, exclusion of instant punishment, and one positive Lyapunov scale. The necessity implication, certificate, and chronological strategy remain unproved. |
| Sorin's absorbing-game uniform-payoff segment | Unconditional theorem | [`isUniformEquilibriumPayoff_pair_value`](UniformEquilibrium/Examples/Sorin/UniformPayoffSegment.lean) | Every payoff (a, 2(1-a)) with 1/2 <= a <= 2/3 is realized against all unilateral behavioral deviations; the account strategy may depend on the requested accuracy. |

Declaration kind and umbrella reachability are checked by the documentation gate. Compilation truth still comes from the relevant Lean check or CI run.
<!-- END GENERATED STATUS -->

The table indexes declaration kind and source reachability; it is not a Lean
build report. See [`docs/STATUS.md`](docs/STATUS.md) for that distinction and
[`docs/FRONTIER.md`](docs/FRONTIER.md) for the current dependency boundary and
nonclaims.

## What is worth looking at?

- **Finite stochastic and quitting games:** the integrated development contains
  semantic bridges, exact positive cases, obstruction theorems, and explicit
  fences against false strategy-class completeness claims.
- **Reusable formal mathematics:** [`MathUE/`](MathUE/) contains project-owned
  probability, topology, curve-selection, interval-certification, linear-
  algebra, occupation-flow, and charged-path results independent of the main
  game-semantic layer.
- **Selected theorem statements:** [`Theorems/`](Theorems/) gives short,
  reader-facing restatements of results such as charged-path/potential duality,
  bounded-discrepancy circulation, collision-mass bounds, phase-occupation
  duality, cyclic exposure, and flow holonomy. Canonical proofs remain in their
  original modules.
- **Examples and diagnostic counterexamples:** the integrated tree includes the
  Big Match, Sorin examples, pure-externality cycles, vanishing-discount
  diagnostics, and counterexamples to proposed certificate or continuity
  principles.
- **Computational evidence:** [`Experiments/`](Experiments/) contains
  reproducible exact and numerical searches, including exact-rational CEGIS.
  Its reports are evidence, not proofs.
- **Backward proof search:** [`Reverse/`](Reverse/) works from checked consumers
  toward precise remaining mathematical obligations.
- **Literature coverage:** [`Literature/`](Literature/) provides one plain Lean
  audit file per paper. Root files have complete statement coverage; incomplete
  papers remain explicitly under `Literature/future/`.

The repository is organized for mathematical discovery, verification, and
systematic audit, not as a stable downstream library. It makes no compatibility
promise for internal modules.

## Where to start

| Interest | Entry point |
| --- | --- |
| Exact semantic and quantifier contract | [`docs/SEMANTICS.md`](docs/SEMANTICS.md) |
| Headline declaration index | [`docs/STATUS.md`](docs/STATUS.md) |
| Current mathematical boundary | [`docs/FRONTIER.md`](docs/FRONTIER.md) |
| Integrated interfaces and exact nonclaims | [`docs/TOOLKIT.md`](docs/TOOLKIT.md) |
| Reader-facing theorem catalog | [`Theorems/README.md`](Theorems/README.md) and [`Theorems/Catalog.lean`](Theorems/Catalog.lean) |
| Integrated game-semantic areas | [`UniformEquilibrium/README.md`](UniformEquilibrium/README.md) |
| Experiments and their commands | [`Experiments/README.md`](Experiments/README.md) |
| Current reverse-search questions | [`Reverse/Tasks/README.md`](Reverse/Tasks/README.md) |
| Research and formalization method | [`docs/PROGRAM.md`](docs/PROGRAM.md) and [`docs/PIPELINE.md`](docs/PIPELINE.md) |
| Extraction and repository provenance | [`TRANSITION.md`](TRANSITION.md) |

Integrated Lean is the source of exact theorem truth. `STATUS.md` is a generated
declaration index and `FRONTIER.md` is the current mathematical synthesis;
neither substitutes for compilation. Experiments, Research files, comments,
and paper summaries do not become theorems by proximity.

## Repository map

- `UniformEquilibrium/` contains the integrated game-semantic development.
- `MathUE/` contains game-independent mathematics owned by this project.
- `Theorems/` is a correction-friendly showcase delegating to canonical proofs.
- `Literature/` contains plain paper-audit files and incomplete future stubs.
- `Research/` contains compileable Lean not yet incorporated into the
  integrated development.
- `Experiments/` contains reproducible counterexample and certificate searches.
- `Reverse/` contains backward proof-search tasks and evidence.
- `docs/` contains the mathematical frontier, methodology, and architecture.
- `GameTheory/` is a pinned git submodule and is not modified here.

The submodule is the dependency boundary. Project-specific generic mathematics
belongs in `MathUE`; the game-semantic layer depends on GameTheory interfaces.
`MathUE` may use Mathlib and GameTheory's generic mathematics, but not
game-semantic `GameTheory.*` modules.

## Lean entry points

The whole integrated development, including `MathUE`, is available through:

```lean
import UniformEquilibrium
```

The game-independent and featured-theorem surfaces can also be loaded directly:

```lean
import MathUE
import Theorems
```

These umbrellas are project-wide build and navigation boundaries, not stable
external APIs. Individual modules use narrow imports to keep focused checks
small.

## Trust and verification

Project Lean sources reject `sorry`, `admit`, explicit axiom declarations,
`native_decide`, `implemented_by`, unsafe declarations, and partial
definitions. They also reject project-owned `set_option` commands and global
linter weakening. Every project library builds with warnings as errors. Open
claims remain definitions of propositions until a kernel-checked proof is
available.

The generated `AxiomAudit.lean` imports every project-owned Lean module and
checks every project-owned declaration transitively. It permits only the
standard `propext`, `Quot.sound`, and `Classical.choice` axioms. As a default
Lake target, it covers orphaned Research and experiment modules as well as the
main umbrellas.

Lean 4.32.2 is the required toolchain. Lean 4.32.0 is excluded because of a
kernel soundness bug.

From a fresh checkout:

```sh
git submodule update --init --recursive
python scripts/generate_axiom_audit.py --check
lake build
python scripts/check_import_graph.py
python scripts/check_proof_duplicates.py
python scripts/check_trust.py
python scripts/check_docs.py
```

`lake build` performs the Lean compilation check. `check_trust.py` is a lexical
escape-hatch scan and is not a substitute for compilation. The static
duplicate check rejects long exact Research copies of maintained MathUE or
UniformEquilibrium declaration bodies; it is a narrow ownership ratchet, not a
semantic proof-equivalence test. Do not run
`lake update` during ordinary setup; it is reserved for intentional dependency
or manifest work.

## Reuse

The project is MIT-licensed; see [`LICENSE`](LICENSE). Definitions, proofs,
mathematics, and tooling may be copied or adapted under that license. Because
the project has no stable API or release surface, citations should identify the
exact declaration or module used, together with the relevant mathematical
source where applicable.
