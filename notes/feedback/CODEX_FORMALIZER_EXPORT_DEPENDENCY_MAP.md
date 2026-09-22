# Export queue: first missing Lean dependencies

This is a static dependency audit of the fifteen packets in `math/exports/`,
not a packet ranking or a new mathematical proof. “Checked” below refers to
the named production declarations, not to the packet in full. Packet count
is a poor priority proxy: several packets share one interface, while some
already have their main conclusion in production.

| First missing theorem or adapter | Packets grouped at that boundary | Checked production foothold |
| --- | --- | --- |
| Actual stationary quotient local-degree comparison, followed by original-player Bellman decoding | `STATIONARY_RESPONSE_QUOTIENT_DEGREE_ESCAPE`; `GUARDED_CROSSED_RESPONSE_DEGREE_ESCAPE` has a distinct crossed-map root/guard adapter | `quittingSingletonMatrix_mulVec_blockLift_eq_quotient` and `quittingQuotientStationaryClippedMap_eq_self_iff` (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`), `BoxComplementarityProblem.exists_solution_not_mem_closure_of_localDegree_ne_one` (`MathUE/Topology/BoxComplementarityDegreeEscape.lean`), and `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts` (`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`). The quotient algebra and generic degree escape do not yet compute the *actual quotient map's* local degree or turn its fixed point into the full original-player endpoint certificate. |
| Positive-withdrawal mixed private-clock gain comparison and fixed-target extension | `WITHDRAWAL_AND_DEADLINE_QUIET_EXTENSIONS`; the narrower `ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO` instead needs its all-parent-approximants quantile rigidity and robust unchanged-child cap gap | `DeadlineWithdrawalRewardCertificate` and its zero-withdrawal debt theorem (`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRaw.lean`), the stopping-law update/deviation-cap identities (`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`), and `exists_uniformEquilibriumPayoff_eq_on_image_of_terminalNash_lift` (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalNashLift.lean`). `DeadlineWithdrawalMixedLaw.lean` is in progress, not counted as a checked input here. The adaptive-child packet is a separate impossibility result, not a required premise for withdrawal. |
| Strict-deficit exact all-suffix limit and residual quantitative selectors | `PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS`, `FINITE_CALENDAR_PAYOFF_EXCLUSION_RAW_TABLE_TESTS`, `FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION`, `SINGLE_PIVOT_SECANT_COLLAR_AND_STRICT_PRESSURE` | Finite-calendar payoff compression, raw PD/GE/WE recognition, executable rational finite-word selection, complete cap/debt control, and weak-subset UE are already checked through `quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff` (`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffClosure.lean`), `forall_finiteCalendarRawPayoff_iff_forall_actualTerminalPayoff` (`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPredicates.lean`), `exists_literal_capThreshold_block_debtSum_le_quadraticDrop` (`UniformEquilibrium/Quitting/Paths/FiniteSoloCapThresholdDescent.lean`), and `exists_uniformEquilibriumPayoff_of_actualWeakSubsetExclusion` (`UniformEquilibrium/Quitting/Paths/FiniteWordWeakSubsetSelection.lean`). The strict-deficit packet's *single infinite word exact at every suffix* is separate from finite approximate selection. The single-pivot secant/tilted common-calendar source remains a further, counterexample-side theorem, not a consequence of finite-calendar payoff compression, which does not preserve caps. |
| New screened-minimum/fiber algebra and source transport | `GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR`, `MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION`, `THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS` | `minimumTerminalSemantic_maximumDebt_allPlayersTie` (`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`), `minimumTerminalSemantic_exploitabilitySingletonMargin` (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`), and `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin` (`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`) provide minimum and actual-source interfaces. The first new steps differ: degree-six screened-root nonvanishing, four-coordinate singleton stretch, and signed affine-row comparison, respectively. None may assume a selected counterexample fiber or hazard as a certificate field. |
| Constructed raw cycle/periodic family beyond existing compilers | `THREE_PLAYER_CYCLE_PASSIVE_ROW_EXTENSION`, `PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION` | `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`) already gives the first packet's full raw-table UE class; its optional fixture degree, sharp calendar, and neighborhood outputs remain. The paired-collision packet still needs its parameter-specific IVT root and periodic/stationary disjunction; `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance` (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`) is the existing fixed-target consumer, not a rate producer. |
| Full exact-root potential restriction and shape arguments | `REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS`, `QUITTING_POTENTIAL_SHAPE_EXCLUSIONS` | `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential` (`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`) and the robust charged relation supply the existing conditional certificate interface. The first missing reusable step is the full-exact-edge restriction with collision-adjusted singleton probes; reflection, quasiconvexity, curvature, and degree exclusions then diverge. These are necessary-shape reductions, not a polynomial producer or a solved-game class. |

## Next source-complete Lean tasks with broad reuse

1. Prove the actual quotient-map local-degree comparison, with its chart and
   isolating region produced from RI and R0, as specified in the packet and
   `notes/feedback/CODEX_FORMALIZER_RESPONSE_QUOTIENT_CHART_COMPARISON.md`.
   This connects checked raw quotient algebra to checked generic degree escape;
   the original-player Bellman adapter remains a separate next dependency.
2. Finish the positive-withdrawal private-clock expectation/gain identity and
   its complete-deviation comparison from the literal N/F/J reward rows.
   This extends the checked zero-withdrawal cone and can feed the existing
   fixed-target child-to-parent lift. Do not treat the current in-progress
   mixed-law module as checked until its own Lean check passes.
3. Prove the strict-deficit construction's one actual infinite root sequence
   with exact terminal Nash at every suffix under the packet's nonnegative
   singleton hypothesis. Reuse the checked finite-word cap recurrence and
   finite-law adapters, but do not infer cap convergence from payoff-only
   finite-calendar compression. This is the missing shared output of the two
   payoff-exclusion packets, beyond their already checked approximate-UE
   consequences.

The first two tasks have direct strategic consumers. The third is a stronger
chronological output for an already solved sufficient class, not a new
unconditional uniform-equilibrium theorem.
