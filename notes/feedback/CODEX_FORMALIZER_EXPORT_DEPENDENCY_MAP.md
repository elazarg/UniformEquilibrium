# Export queue: first missing Lean dependencies

This is a static dependency audit of the fifteen packets in `math/exports/`,
not a packet ranking or a new mathematical proof. “Checked” below refers to
the named production declarations, not to the packet in full. Packet count
is a poor priority proxy: several packets share one interface, while some
already have their main conclusion in production.

| First missing theorem or adapter | Packets grouped at that boundary | Checked production foothold |
| --- | --- | --- |
| Punishment completion for a normal negative singleton-block owner; distinct crossed-map root/guard adapter | `STATIONARY_RESPONSE_QUOTIENT_DEGREE_ESCAPE`; `GUARDED_CROSSED_RESPONSE_DEGREE_ESCAPE` | `exists_original_stationaryBellmanRoot_of_quotientDegree_ne_one` (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientBellman.lean`) now constructs the positive-absorption original-player Nash–Bellman root from the raw quotient degree test. `exists_uniformEquilibriumPayoff_of_responseInvariant_singletonSign` (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientStrategic.lean`) closes nonnegative singleton-block owners and the no-singleton-block case. The signed Fin4 conclusion requires completion for a normal negative sole owner; the crossed-map packet has its own root/guard producer. |
| Multiple-outsider certificate family and fixed-target terminal Nash-lift consumer | `WITHDRAWAL_AND_DEADLINE_QUIET_EXTENSIONS`; `ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO` remains an independent impossibility result | `deadlineWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt` and `deadlineWithdrawal_quietLift_totalBehaviorDebt_le_weighted_childDebt` (`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalFullBehavioralDebt.lean`) prove the literal positive-withdrawal D bound at every nonnegative antitone evaluation for one outsider and every actual child profile. A family of certificates, one per outsider, and the fixed-target extension are not yet proved. The adaptive-child packet does not supply either. |
| Full two-branch rational weak-subset selector and single-pivot secant source | `PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS`, `FINITE_CALENDAR_PAYOFF_EXCLUSION_RAW_TABLE_TESTS`, `FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION`, `SINGLE_PIVOT_SECANT_COLLAR_AND_STRICT_PRESSURE` | `exists_strictDeficitExactSuffix_allTerminalNash` (`UniformEquilibrium/Quitting/Paths/StrictDeficitExactSuffixNash.lean`) closes the single common-depth infinite all-suffix exact Nash conclusion under nonnegative singleton rewards. The existing executable rational weak-subset selector assumes strict preemption of all designated owners; its full stationary-exit/charged-step two-branch selector remains separate. The single-pivot secant/tilted common-calendar source is also separate; finite-calendar payoff compression does not preserve caps. |
| New screened-minimum/fiber algebra and source transport | `GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR`, `MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION`, `THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS` | `minimumTerminalSemantic_maximumDebt_allPlayersTie` (`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`), `minimumTerminalSemantic_exploitabilitySingletonMargin` (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`), and `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin` (`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`) provide minimum and actual-source interfaces. The first new steps differ: degree-six screened-root nonvanishing, four-coordinate singleton stretch, and signed affine-row comparison, respectively. None may assume a selected counterexample fiber or hazard as a certificate field. |
| Constructed raw cycle/periodic family beyond existing compilers | `THREE_PLAYER_CYCLE_PASSIVE_ROW_EXTENSION`, `PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION` | `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`) already gives the first packet's full raw-table UE class; its optional fixture degree, sharp calendar, and neighborhood outputs remain. The paired-collision packet still needs its parameter-specific IVT root and periodic/stationary disjunction; `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance` (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`) is the existing fixed-target consumer, not a rate producer. |
| Full exact-root potential restriction and shape arguments | `REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS`, `QUITTING_POTENTIAL_SHAPE_EXCLUSIONS` | `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential` (`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`) and the robust charged relation supply the existing conditional certificate interface. The first missing reusable step is the full-exact-edge restriction with collision-adjusted singleton probes; reflection, quasiconvexity, curvature, and degree exclusions then diverge. These are necessary-shape reductions, not a polynomial producer or a solved-game class. |

## Next source-complete Lean tasks with broad reuse

1. Compose the positive-absorption stationary root with a normal negative
   singleton owner's punishment completion, then use the existing Fin4
   no-UE normality consequence. The quotient degree producer and the
   singleton-sign/no-singleton-block consumers are checked; the normal-owner
   bridge is the exact remaining strategic dependency for the signed class.
2. Lift the one-outsider deadline-withdrawal debt bound to a family of
   outsider certificates, then prove the fixed-target terminal Nash-lift
   consumer. The private mixed law, full evaluated behavioral comparison,
   and actual one-outsider child-profile bound are checked; none alone
   supplies the fixed-target parent payoff.
3. Complete the rational weak-subset two-branch selector, preserving one
   source/profile chronology across the stationary-exit and charged-step
   cases. The strict-deficit infinite all-suffix theorem is now checked and
   does not need to be reproved. The single-pivot source remains a different
   counterexample-side task.
