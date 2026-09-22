# Export queue: first missing Lean dependencies

This is a static dependency audit of the fifteen packets in `math/exports/`,
not a packet ranking or a new mathematical proof. “Checked” below refers to
the named production declarations, not to the packet in full. Packet count
is a poor priority proxy: several packets share one interface, while some
already have their main conclusion in production.

| First missing theorem or adapter | Packets grouped at that boundary | Checked production foothold |
| --- | --- | --- |
| Crossed-map local degree, guarded interior root, and distinct raw classes | `GUARDED_CROSSED_RESPONSE_DEGREE_ESCAPE`; quotient producer in `STATIONARY_RESPONSE_QUOTIENT_DEGREE_ESCAPE` is now checked | `exists_uniformEquilibriumPayoff_finFour_of_responseInvariant_degree_ne_one` (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientNormalCompletion.lean`) closes the arbitrary signed Fin4 quotient criterion without a supplied punishment plan. `quittingCrossedClippedMap` and `quittingCrossedClippedMap_eq_self_iff` (`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponse.lean`, `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseFaces.lean`) are the checked crossed-map foothold. The crossed local-degree and guard-to-original-equilibrium adapters are still separate. |
| All-evaluation family corollaries, necessity, and downstream raw applications | `WITHDRAWAL_AND_DEADLINE_QUIET_EXTENSIONS`; `ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO` remains an independent impossibility result | `exists_uniformEquilibriumPayoff_eq_on_child_of_deadlineWithdrawalFamily` (`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalFixedTarget.lean`) now closes the substantive multiple-outsider fixed-target extension from literal raw certificates and an actual child UE target. `quittingLiftDeletedProfile_evaluatedDebt_of_deadlineWithdrawalFamily` (`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalMultipleOutsiderFamily.lean`) gives simultaneous evaluated debt comparison. Explicit max/sum corollaries, terminal pathwise necessity, Section 5 security, and the Fin4 child-existence consumer remain. The adaptive-child packet does not supply them. |
| Full two-branch rational weak-subset selector and single-pivot secant source | `PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS`, `FINITE_CALENDAR_PAYOFF_EXCLUSION_RAW_TABLE_TESTS`, `FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION`, `SINGLE_PIVOT_SECANT_COLLAR_AND_STRICT_PRESSURE` | `exists_strictDeficitExactSuffix_allTerminalNash` (`UniformEquilibrium/Quitting/Paths/StrictDeficitExactSuffixNash.lean`) closes the single common-depth infinite all-suffix exact Nash conclusion under nonnegative singleton rewards. The existing executable rational weak-subset selector assumes strict preemption of all designated owners; its full stationary-exit/charged-step two-branch selector remains separate. The single-pivot secant/tilted common-calendar source is also separate; finite-calendar payoff compression does not preserve caps. |
| New screened-minimum/fiber algebra and source transport | `GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR`, `MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION`, `THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS` | `minimumTerminalSemantic_maximumDebt_allPlayersTie` (`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`), `minimumTerminalSemantic_exploitabilitySingletonMargin` (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`), and `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin` (`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`) provide minimum and actual-source interfaces. The first new steps differ: degree-six screened-root nonvanishing, four-coordinate singleton stretch, and signed affine-row comparison, respectively. None may assume a selected counterexample fiber or hazard as a certificate field. |
| Constructed raw cycle/periodic family beyond existing compilers | `THREE_PLAYER_CYCLE_PASSIVE_ROW_EXTENSION`, `PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION` | `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`) already gives the first packet's full raw-table UE class; its optional fixture degree, sharp calendar, and neighborhood outputs remain. The paired-collision packet still needs its parameter-specific IVT root and periodic/stationary disjunction; `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance` (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`) is the existing fixed-target consumer, not a rate producer. |
| Full exact-root potential restriction and shape arguments | `REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS`, `QUITTING_POTENTIAL_SHAPE_EXCLUSIONS` | `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential` (`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`) and the robust charged relation supply the existing conditional certificate interface. The first missing reusable step is the full-exact-edge restriction with collision-adjusted singleton probes; reflection, quasiconvexity, curvature, and degree exclusions then diverge. These are necessary-shape reductions, not a polynomial producer or a solved-game class. |

## Next source-complete Lean tasks with broad reuse

1. Prove the crossed-response map's local degree from the literal swapped
   derivative, then transport the exported face guards to an interior
   absorbing original-game root. The quotient degree machinery is reusable
   topology but not a quotient RI theorem for this different map. The
   signed Fin4 quotient criterion is already checked.
2. Record the explicit all-evaluation max/sum consequences of the checked
   deadline-withdrawal family, then the pathwise necessity and source's
   security/Fin4 applications. Do not reprove the multiple-outsider
   fixed-target UE extension, which is now checked.
3. Complete the rational weak-subset two-branch selector, preserving one
   source/profile chronology across the stationary-exit and charged-step
   cases. The strict-deficit infinite all-suffix theorem is now checked and
   does not need to be reproved. The single-pivot source remains a different
   counterexample-side task.
