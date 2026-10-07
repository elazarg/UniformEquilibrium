# Export packet dependencies and completion obligations

This is a dependency audit of the packets in `math/exports/`,
not a packet ranking or a new mathematical proof. “Checked” below refers to
the named production declarations, not to the packet in full. Packet count
is a poor priority proxy: several packets share one interface, while some
already have their main conclusion in production. The table identifies first
dependencies, not complete packet coverage. The claim inventories below
record broader retirement obligations after reading those packets in full.

Source-audit caveat: `math/SOURCES.md` and `math/GOAL.md` still describe
Literature as unbuilt. The current default build includes its library;
intentional open paper claims remain marked by `sorry`. Root `AGENTS.md`
and each exact declaration govern the status, including separate transitive
axiom checks for Literature proofs. The conference navigation files were
not edited here.

Retired packets pass complete-claim review, the full silent default build,
the exhaustive axiom audit, and repository script gates. Pending packets
remain where their inventories list missing conclusions or verification.
The crossed-response inventory has checked declarations for all its claims
and passes the full integration gate. Quotient ambient, homogeneous and no-UE
consequences also pass the full build and exhaustive audit. Simon's
new declarations pass a separate transitive standard-axiom check; its
unconditional source obligations are recorded separately below.
The paired-collision packet has complete coverage and is retired to
`math/formalized/PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION.md`.
The passive-row cycle packet also passes its complete-claim review, full silent
build and exhaustive axiom audit. It is retired unchanged to
`math/formalized/THREE_PLAYER_CYCLE_PASSIVE_ROW_EXTENSION.md`, with SHA-256
`c98745d49e7aa6516ebb297f067970b9d9c29a599b05952f71768b15c66bef85`.
The crossed-response packet is retired unchanged to
`math/formalized/GUARDED_CROSSED_RESPONSE_DEGREE_ESCAPE.md`, with SHA-256
`95737353231b3f4838257faf5c56efaf23fde44879ae0f0bb2e498255ec8f6f6`.
The withdrawal and deadline packet passes complete-claim review, the full silent
default build, exhaustive production axiom audit, script gates and actual
executable smoke tests. It is retired unchanged to
`math/formalized/WITHDRAWAL_AND_DEADLINE_QUIET_EXTENSIONS.md`, with SHA-256
`3e89c60d59766effbbc8851786fc3c6b57ede8f1a2bf24fb3591e3ac243f402f`.
The cap-threshold packet also passes complete-claim review, the full silent
default build, exhaustive production axiom audit and all repository script
gates. It is retired unchanged to
`math/formalized/FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION.md`,
with SHA-256
`b884b8848472a5aabafbec2b900362254d0b138f84170cb9ce9223a8358630a7`.
The finite-calendar raw-table and actual-selector/exact-suffix packets pass
complete-claim review, the full silent default build, exhaustive production
axiom audit, repository script gates and executable experiment checks. They
are retired unchanged to
`math/formalized/FINITE_CALENDAR_PAYOFF_EXCLUSION_RAW_TABLE_TESTS.md` and
`math/formalized/PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS.md`,
with respective SHA-256 values
`f086d1f2d1e1520898f7f229cd44a8e66067315567484d071489fc0ad630fcef` and
`d2a00f73137fe0a847ed6480daa3a64efd6f25bfd7faedb8b70290a9fddbb245`.
The quotient packet passes complete-claim review, the full silent default build,
exhaustive production axiom audit, repository script gates and executable
experiment checks. It is retired unchanged to
`math/formalized/STATIONARY_RESPONSE_QUOTIENT_DEGREE_ESCAPE.md`, with SHA-256
`49f0efacc29a683d421c82180f4781376a43a36e6c824f2468a8856af71136ac`.
The adaptive unchanged-child packet passes complete-claim review, the full
silent default build, exhaustive production axiom audit and repository script
gates. It is retired unchanged to
`math/formalized/ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO.md`, with SHA-256
`8d49397b8c06b185d99d71cc03d8abe98ad95d47c9030ac413a910462df6a52f`.

| First missing theorem or adapter | Packets grouped at that boundary | Checked production foothold |
| --- | --- | --- |
| Completed unchanged-child obstruction | `ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO` | `AdaptiveChildCenter.profile_exactTerminalNash` and `AdaptiveChildCenter.target_isUniformEquilibriumPayoff` (`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenter.lean`) prove the center's positive equilibrium. `exists_actual_quantile_rigidity` (`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterQuantileRigidity.lean`) passes its silent named check for the original full sequence and internally selected unbounded cutoffs. The four actual restriction estimates, positive parent-plus-child floor, reward-neighborhood transfer and nearby one-date producer pass the named `AdaptiveChildCenterNearbyHorizons` check, including the same selected profile before every accuracy and exact Nash at every finite horizon. Literal center, half-scaling, unchanged-law and larger-radius stationary consumers also pass their named checks. Complete-claim review and the full silent integration gate pass; the packet is retired unchanged. Capped-clock certificate infeasibility does not prove the unchanged-child obstruction. |
| Single-pivot secant and tilted common-calendar source | `SINGLE_PIVOT_SECANT_COLLAR_AND_STRICT_PRESSURE` | Both payoff packets are complete and retired, including accepted raw sources, exact laws/full caps, the printed half-cap rates, selected-word pivot optimum, and all literal fixtures. The single-pivot secant/tilted common-calendar source remains a separate construction; payoff compression does not preserve caps. |
| New screened-minimum/fiber algebra and source transport | `GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR`, `MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION`, `THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS` | `minimumTerminalSemantic_maximumDebt_allPlayersTie` (`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`), `minimumTerminalSemantic_exploitabilitySingletonMargin` (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`), and `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin` (`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`) provide minimum and actual-source interfaces. The first new steps differ: degree-six screened-root nonvanishing, four-coordinate singleton stretch, and signed affine-row comparison, respectively. None may assume a selected counterexample fiber or hazard as a certificate field. |
| Rational rejection and literal potential fixtures | `REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS`, `QUITTING_POTENTIAL_SHAPE_EXCLUSIONS` | The common exact-root exclusion, adaptive reflection, quadratic and multi-affine exclusions, and restricted same-polynomial characterization pass the full integration gate. Face-only additive and regular scalar-composition exclusions, monotone-transform transfer, the same-polynomial quantitative characterization and positive charge normalization pass silent named, separate standard-axiom and full integration checks. The rational exact one-quitter rejection producer passes its silent named, exhaustive axiom and full integration checks. The literal shape fixtures also pass silent named, separate standard-axiom and full integration checks; the shape packet's mathematical content is complete. The reflection packet's rational approximate robust rejection and exhaustive search also pass those checks; the paired-example, integral, normalization, same-segment and boundary claims pass the full silent integration gate, completing the reflection packet's mathematical content. These are necessary-shape reductions, not a solved-game class. |

## Adaptive-child obstruction: known-proof dependencies

`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`
already identifies arbitrary independent finite/Never laws with actual
behavioral payoffs and unrestricted response caps, and bounds changes with
the queried player's replacement held fixed. Quantile rigidity does not
require another behavioral representation or coupling theorem. Its generic
prerequisites are first-crossing existence from the Never deficit,
conditioning-versus-original total variation, and an exact one-atom
pushforward payoff identity. All three must retain unbounded clocks.

The center's `unique_completelyMixed_active_probabilities`
(`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenter.lean`) does not
cover the initially possible boundary limits. The export's elementary endpoint
case splits supply the missing unconditional auxiliary Nash uniqueness proof.
The generic clock prerequisites and this boundary-case uniqueness proof pass
their silent named checks and the full integration gate. They retain zero
cutoffs, arbitrary finite-or-Never laws, absolute dates after conditioning,
and zero or unit moved-atom mass. The checked source chain covers actual
anchor membership and cap, the internally selected unbounded
first quantile, prescribed and endpoint payoff errors with constants 14 and 10,
and their endpoint-regret consequence with constant 24. First-quantile selection,
the row, payoff and regret owners pass their silent named checks.
They retain the original
profile and reconstructed Quit-at-cutoff or Never deviations, conditioning only
the unchanged opponents for the deviation bound. The sequence-rigidity theorem
passes its silent named check and retains those same profiles and their
internally selected, unbounded cutoffs, not a limiting stopping law.
The independently reviewed deletion argument
passes Lean with all four actual restriction estimates and the center's
universal positive paired floor. Deleting the anchor uses an
actual move of one existing atom to the next date, preserving every other atom
and Never, with its actual gain tending to one eighth.

Only these four estimates yield the universal positive parent-plus-child
exploitability floor. The existing reward-robustness theorem then transfers
that floor to a neighborhood. The packet's nearby one-date equilibrium with
interior active probabilities passes its named dependency check.
Its same-profile horizon addition retains
one internally selected profile before every accuracy and proves exact Nash
at every finite horizon, including zero; its silent named Lean check passes.
An existing stationary solution is not a replacement for these conclusions.

## Next source-complete Lean tasks with broad reuse

1. Connect the quotient's produced absorbing stationary exact equilibrium to
   the checked withdrawal quiet lift. The no-singleton-block branch supplies
   the actual child profile and full behavioral caps; normality completion
   need not supply such a stationary child. This join needs no positive
   singleton pivot. Reuse the checked ambient degree construction, whose
   degree identity covers the entire nonzero root set without finiteness or
   regularity. Algebraic equilibrium selection and accuracy-only rational
   search remain distinct tools; neither computes a prescribed real target.
2. Reuse the checked real and rational selectors, stage, dyadic bound and
   quantitative all-suffix consumer. Both payoff packets' complete-claim
   reviews and full integration gate pass. Cap-threshold stopping and
   payoff-threshold stopping are different predicates. The single-pivot
   secant source remains a different counterexample-side task.

### Reusable connections beyond the exported conclusions

The indexed-family theorem
`quittingGame_uniformPayoffWitnesses_of_terminalTargetAcceptance_family`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
retains the selected actual profile. Its checked constant-family facade
`quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact`
in the same file exposes same-profile horizon witnesses for arbitrary exact
terminal Nash, without stationarity or absorption assumptions. The shared
two-pair compiler and the below-singleton source use this interface.

The complete-law bounds
`quittingTerminalOutcomeOperationalDistance_le_sum`,
`abs_quittingStoppingLawExpectedPayoff_sub_le_terminalOutcomeDistance`, and
`abs_quittingContinuationBestResponseValue_sub_le_opponentStoppingLaws`
(`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`)
suggest a quantitative extension of the adaptive unchanged-child obstruction.
The proposed regret-floor loss is at most twice a child reward bound times
the sum of complete survivor-law distances, in addition to the child's Nash
error. These distances include every finite date and Never. This composed
extension is not proved here; finite-coordinate convergence alone does not
give such a bound. The exact-law adaptive packet passes its full gate and is retired.

Post-completion discovery also identified three minor theorem surfaces not
yet implemented: localization of every nearby active zero by the reward
perturbation radius; convergence of the original center approximate-terminal-
equilibrium sequence's payoff to `(1, 0, 0, 1)`; and one eventual threshold for
all four literal child deletions, including a varying deleted player. The
existing quantile and payoff estimates support these proposed compositions.
None asserts convergence of stopping dates or a full stopping profile, or
uniqueness of the uniform-equilibrium payoff set.

The checked nearby one-date producer selects one profile before every horizon
and accuracy and proves exact Nash at every finite horizon. Its cutoff proof
also suggests a stagewise deviation bound and nonnegative weighted-evaluation
consumers; those facades remain unimplemented. Weighted delivery would scale
the terminal target by the total weight after stage zero. A proposed relaxation
of the one-date producer's radius from `< 1/8` to `< 1/4` is supported by its
existing arithmetic but is not checked and does not enlarge the independently
selected paired-floor neighborhood.

Exact absorbing stationary roots produced by the response-quotient sign,
no-singleton-block, or joining-infeasibility routes can feed
`quietLift_fixedTarget_of_withdrawalFutureJoin_absorbingStationary`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalAbsorbingStationaryChild.lean`).
A direct source-producing composition remains to be written. Normality-only
quotient completion preserves a value, not necessarily the same exact Nash
profile, and cannot replace these inputs.

### Shared finite-selector construction

The checked shared construction takes an actual rational finite source word,
a positive reward bound and working accuracy, and tests its actual cap margins.
In the charged branch, the canonical rational auxiliary-root selector must
produce the root internally. The existing below-singleton absorption bound
and auxiliary total-debt ledger then supply the absorption and strict debt
drop for the literal prefixed word. A selected root, successful search,
favorable continuation or cap vector is not additional source data.

The concentrated branch retains the actual weak-exclusion owner. A passing
positive singleton-column test gives a finite solo exit at the requested
accuracy. Otherwise the new block stops at the first actual payoff/debt
threshold, preserving the old word as its tail. Failure of that column test
does not imply strict preemption, so the existing preemptor cap scan cannot
replace this construction. Its affine ledger and logarithmic horizon bound
are reusable only after deriving their before-hit conditions from the actual
payoff thresholds. Charged steps and these blocks precede the dyadic stage
and raw-predicate consumers; no minimum semantic pair is substituted for the
actual finite source.

The branch, stage and dyadic declarations below implement these requirements
and pass named checks. The real-valued qualitative dispatcher and existing
cap-threshold blocks remain their canonical owners.

### Distinct completion obligations for the three selector packets

The shared source construction does not close these packets by itself.
Complete-claim review separates their remaining obligations:

- `FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION` already has
  the real and rational first-cap blocks, quadratic minimum collar,
  square-root payoff envelope and table-dependent preempted selector. Its
  rational unpreempted exit, prescribed two-branch dispatcher, rational
  same-word menu and all three actual-source regressions pass named checks.
  The real same-word menu join and full integration gate also pass. This packet
  does not require the reward-uniform dyadic bound from the other two packets.
- `FINITE_CALENDAR_PAYOFF_EXCLUSION_RAW_TABLE_TESTS` has its exact payoff
  calendar realization, raw polynomial recognition and all seven boundary
  examples. Its selection section also requires the shared rational
  payoff-threshold stage and dyadic date bound, the specified unpreempted
  exit, and the same-source quantitative suffix and accepted-source joins.
  It does not require the other packet's determinant-table fixture.
- `PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS` requires those
  shared stage, dyadic and same-source suffix results. Its separate literal
  obligations are the determinant-attaining laws, the complete reward-bound-21
  table and its exact root/comparison statements, the first-payoff-hit-155
  regression, and the signed two-player family with no exact terminal Nash.
  Approximate or uniform equilibrium existence is not negated by that last
  example.

The positive-column rational exits, actual charged source step, generic
real payoff-threshold ledger and rational payoff-threshold block pass silent
named builds. The fixed-level stage also passes its silent named check,
including actual source renewal, internally proved termination and its date
bound. The dyadic aggregation passes its separate silent named check,
including the absolute reward-uniform date bound, actual same-word full debt,
exact independent finite/Never laws and fixed-payoff existence from rational
finite-word exclusion. The reciprocal rates of the existing real/rational
renewals also pass their separate named check, including zero initial debt
and the actual full behavioral debt of the same computed word.
The same-source quantitative suffix join also passes its named check in
`UniformEquilibrium/Quitting/Paths/StrictDeficitExactSuffixHorizon.lean`:
it retains both original diagonal limit families, every exact-Nash suffix,
the prescribed horizon bound, full reply error and the same-profile fixed
payoff target. The rational unpreempted exit passes its named check and
silent bounded runtime tests, including zero and one-player boundaries.
The literal actual-payoff supremum envelope also passes its named check,
including internally selected minimizers for nonnegative singleton tables
and arbitrary signed Fin4 tables. All three cap-threshold regressions pass
their named checks, including the signed first-hit-30 debt increase.
The prescribed rational preemption dispatcher and both rational and real
same-word menu joins also pass their named checks. The real join needs no
preemption or rationality premise. The shared constructions pass the full
integration gate. The cap packet is retired after complete-claim review;
the finite-calendar packet's seven literal source joins and full integration
gate also pass. Its complete-claim source audit found no missing conclusion.
The payoff packet's literal fixtures and both remaining
compositions also pass their targeted checks: the printed two-pair reciprocal
constants and the selected-word optimal pivot-repair bound by full total debt.

The accepted-source joins retain the returned raw reciprocal or Boolean
acceptance, designated singleton signs, actual rational selector and exact
independent finite/Never laws. `exists_finFour_finiteWord_exactLaws_of_rawPayoffExclusion`
(`UniformEquilibrium/Quitting/Paths/FinFourRawPayoffExclusionFiniteLaws.lean`)
also selects a real word internally from any accepted P/G/W source and retains
its complete payoff/cap pair with strict debt below the requested error.
`exists_finiteCalendarRawStrict_sameProfile_quantitativeUniform`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarStrictDeficitSuffixHorizon.lean`)
retains the original same-diagonal exact suffix family and same-profile target,
with all-singleton nonnegativity explicit. No compressed payoff witness supplies
the response caps. All seven joins pass their silent named checks.

`SignedTwoPlayerExactNashNonattainment.not_exact_terminal_nash`
(`UniformEquilibrium/Quitting/Examples/SignedTwoPlayerExactNashNonattainment.lean`)
passes its named check for every parameter strictly between zero and one.
It rules out exact terminal Nash for all behavioral profiles, not approximate
or uniform equilibrium existence. `TwoPairCrossMassSharpProfiles.actual_determinant_eq`
(`UniformEquilibrium/Quitting/Paths/TwoPairCrossMassSharpProfiles.lean`)
passes its named check, retaining the literal independent date-zero-or-Never
laws, sure date-one laws, both closed parameter endpoints and actual law
round trips. The separate all-Never determinant boundary is also checked.

## Complete-claim audit: finite-calendar raw-table packet

The packet's useful mathematical conclusions have checked production owners.
Independent complete-claim review found no remaining theorem obligation. The
full integration gate passes; the unchanged packet is retired to `math/formalized/`.

| Source conclusion | Checked owner and retained scope |
| --- | --- |
| Actual payoff closure and sparse laws | `exists_sparse_finiteCalendarLaws_of_mem_closure_actualPayoff` (`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffClosure.lean`) preserves the whole payoff, with a common twenty-date Fin4 calendar and at most five atoms per player including Never. It does not preserve caps. |
| Raw table, polynomial coordinates and word equivalence | `quittingFiniteCalendarRawPayoff_eq_terminalPayoff` (`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPayoff.lean`) and the raw/joint polynomial owners retain actual ties, strict tails and Never; the finite-word equivalence transports payoff predicates only. |
| Exact acceptance and rejection | The raw strict, weak-subset and group decision owners, reciprocal recovery and rejection-witness owners retain the returned parameters. Group rejection is a separate rejecting law for each parameter, not one law for all parameters. |
| Accepted rational sources | `rationalFiniteWordOwnerExclusion_and_signs_of_rawWeakSubsetDecision`, `rationalFiniteWordStrictDeficit_of_returned_rawStrictReciprocal`, and `finiteWordGroupExclusion_of_returned_rawGroupReciprocal` (`UniformEquilibrium/Quitting/Paths/FiniteCalendarAcceptedSelectorSources.lean`) supply the original selectors from literal acceptance. |
| Strict-deficit suffixes | `exists_finiteCalendarRawStrict_sameProfile_quantitativeUniform` (`UniformEquilibrium/Quitting/Paths/FiniteCalendarStrictDeficitSuffixHorizon.lean`) retains one diagonal, every exact-Nash suffix, complete replies and the same fixed payoff. All-singleton nonnegativity remains explicit. |
| Executable weak-subset selection | `executableRationalFiniteCalendarRawWeakSubsetSelection_finiteLaws_and_bound` (`UniformEquilibrium/Quitting/Paths/RationalFiniteCalendarWeakSubsetSelection.lean`) retains the actual word, rational finite/Never atoms, full debt and absolute dyadic date bound. No computation-time bound is asserted. |
| All real accepted sources | `exists_finFour_finiteWord_exactLaws_of_rawPayoffExclusion` (`UniformEquilibrium/Quitting/Paths/FinFourRawPayoffExclusionFiniteLaws.lean`) internally selects one word with strict debt below the requested error and the same laws/full pair. Its uniform-payoff consumer selects one target before accuracy. |
| Literal comparisons | The strict-deficit/zero, weak-beyond-group, group-beyond-deficit, failed-predicate exact-Nash and equal-payoff/different-cap owners cover every printed example. The correlated row lottery is not called an independent strategy. |
| Fixed-weight chamber connection | `exists_actualGroupExclusion_of_nonnegativeWeightChamber` (`UniformEquilibrium/Diagnostics/Quitting/NonnegativeWeightChamberGroupExclusionSource.lean`) derives actual group exclusion from the fixed-weight moment inequality; it does not assume separate singleton signs. |

## Complete-claim audit: actual-selector and exact-suffix packet

The shared selector, strict-deficit diagonal, group recurrence, charged/EXIT
stage, dyadic bound and fixed-target consumers are the same owners used above.
The packet's additional literal obligations and full integration gate pass.
The unchanged packet is retired to `math/formalized/`.

| Additional source conclusion | Checked owner and retained scope |
| --- | --- |
| Half-cap exact/rational rates | `quittingGroupExclusionExactWordDebt_half_raw_reciprocal` and `executableRationalGroupExclusionDebt_half_raw_reciprocal` (`UniformEquilibrium/Quitting/Paths/FiniteCalendarHalfGroupExclusionRates.lean`) give the actual selected debts with constants `32 M + 3 D0` and `128 M + 15 D0`, including zero initial debt. |
| Same selected word's pivot optimum | `exists_finFour_selectedWord_pivotRepairMinimizer_of_rawPayoffExclusion` (`UniformEquilibrium/Quitting/Paths/FiniteCalendarSelectedWordPivotRepair.lean`) produces the canonical optimum for that word's same nonpivot laws, at most its full total debt. An unused date covers the empty word. |
| Sharp determinant laws | `TwoPairCrossMassSharpProfiles.actual_determinant_eq` (`UniformEquilibrium/Quitting/Paths/TwoPairCrossMassSharpProfiles.lean`) retains actual independent laws and both parameter endpoints; the all-Never boundary is separate. |
| Literal reward-bound-21 table | `CrossMassDeterminantFixture.exact_word_pair` (`UniformEquilibrium/Quitting/Examples/CrossMassDeterminantFixture.lean`) gives actual payoff and full cap `(53/33,-20/11,2/3,14/11)`. All fifteen rows, class comparisons, finite laws and the hull separator failure have literal declarations. |
| Actual payoff-hit regression | `CrossMassPayoffThresholdRegression.first_payoff_hit` and `actual_final_debt_zero` (`UniformEquilibrium/Quitting/Examples/CrossMassPayoffThresholdRegression.lean`) retain the old two-row tail, first hit 155, the entire ledger and the final 158-date word. This is not cap-threshold stopping. |
| Signed exact nonattainment | `SignedTwoPlayerExactNashNonattainment.not_exact_terminal_nash` (`UniformEquilibrium/Quitting/Examples/SignedTwoPlayerExactNashNonattainment.lean`) covers all behavioral profiles and every parameter in `(0,1)`. It does not exclude approximate or uniform equilibrium. |

## Complete-claim audit: cap-threshold packet

All useful claims in `FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION`
are covered by checked production declarations. Complete-claim review and
independent review of the real same-word menu found no outstanding objection.
The full silent default build, exhaustive permitted-axiom audit, repository
script gates and the unpreempted exit's bounded runtime checks pass.

| Packet output | Canonical owners |
| --- | --- |
| Actual full-cap prefix, auxiliary defect budget and absorption floors | `TerminalDebtPrefix`, `TerminalSemanticPair`, `AuxiliaryNashDefectBudget`, `BelowSingletonRootAbsorption` |
| Real T1 and rational T1q, retained old source and first-hit ledger | `TerminalSemanticSoloCapThreshold`, `FiniteSoloCapThresholdDescent`, `ExecutableRationalCapThresholdBlock` |
| T2 at every positive minimizing pair; arbitrary signed Fin4; actual-payoff supremum envelope | `TerminalSemanticPreemptedOwnerQuadraticMargin`, `TerminalSemanticActualPayoffEnvelope` |
| Both actual rational selection branches, zero debt and every positive accuracy; reciprocal renewal and T3 dates | `RationalUnpreemptedSoloExit`, `RationalWeakExclusionTwoBranchSelection`, `SelectedOwnerReciprocalEnvelope`, `ExecutableRationalSelectedOwnerRates` |
| Same real/rational word, independent finite/Never laws, full pair, menu/pivot errors and horizons | `LiteralFiniteWordMenuRealization`, `FinFourWeakExclusionFiniteMenu`, `FinFourRationalWeakExclusionFiniteMenu` |
| One fixed target before accuracy | `FiniteWordWeakExclusionSelection`, `ExecutableRationalWeakSubsetDyadicSelection`, `TerminalUniformPayoffSelection` |
| Literal first cap hits at 59 and 30, signed debt increase, and below-singleton skip | `CapThresholdFinFour`, `CapThresholdFinThree`, `CapThresholdInitialSkip`, `CapThresholdRegressionCommon` |

These module names identify the owners in the corresponding production
subtrees; exact public declarations are recorded in `docs/TOOLKIT.md`.
The packet does not assert weak exclusion for arbitrary Fin4, renewable debt
decrease when the cap margin exceeds total debt, realization of every carrier
point, cap attainment, arithmetic complexity, or computation of a fixed target.

## Complete-claim audit: guarded crossed-response packet

The main strict and finite-raw producers, matrix-free one-sided alternative,
finite-raw weak boundaries, and literal examples have checked declarations.
The following broader results and source adapters also pass named checks.
The full silent default build, exhaustive axiom audit and repository script
gates pass. Complete-claim review found no uncovered packet claim.

| Source claim | Checked coverage |
| --- | --- |
| Section 4, weaker matrix region | Matched by the general zero-diagonal R0 row-swap theorem (`MathUE/LinearProgramming/RowSwapR0Restriction.lean`) and `quittingCrossedSingletonMatrix_degree_eq_one_of_sourceGuards_no_uniformPayoff` (`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseR0Restriction.lean`), passing a silent targeted check. Selected reciprocity and strict external signs suffice; positive inverse is not assumed. |
| Section 5, rational implementation | Actual rational cap evaluation, eventual accuracy-only grid search, and approximate-Nash censoring pass targeted checks. Their actual finite-law composition passes its named check in `UniformEquilibrium/Quitting/Stationary/RationalSearchFiniteCensor.lean`, under general real-height source guards and both strict finite raw branches. Exact laws, full semantic pair, selected-value delivery and signed horizon bounds are retained. No prescribed-payoff oracle or complexity claim is introduced. |
| Section 6.2, weak polynomial faces | Matched by `exists_stationary_uniformPayoff_witnesses_of_weakHalfPolynomialGuards` (`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialProducer.lean`), passing a silent targeted check. Actual weak polynomial faces replace sufficient finite rankings and Bernstein hypotheses; the literal perturbation derives external signs and reciprocity, and selects one fixed original-game target with actual stationary witnesses. No exact boundary attainment is asserted. |
| Sections 7 and 9, full reward neighborhoods | Matched by `halfCeiling_fullRewardBall_stationaryTerminalNash_uniformPayoff` and `unitCeiling_fullRewardBall_stationaryTerminalNash_uniformPayoff` (`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseFullRewardNeighborhood.lean`), passing silent named checks. The literal radii are `1 / 100` and `1 / 1000` in the ordinary sixty-coordinate reward metric; every actual new table has its own derived matrix positivity, guards and equilibrium. |
| Section 7, quantitative coefficient display | Exact reward-coordinate norm equalities and Bernstein uniqueness pass the named check in `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseHalfCoefficientNorms.lean`; this is stronger than the coefficient-error upper bound alone. |
| Section 7, coordinate freedom | Recipient-row shifts, twenty-two independent outsider-recipient nonsingleton coordinates, and the nonempty open convex selected slice with forty-two strict affine constraints pass targeted checks in `UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseCoordinateFreedom.lean` and `UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseSelectedPolyhedron.lean`. Every own singleton value is allowed. Never remains zero; arbitrary-profile strategic equivalence is not asserted. |
| Sections 8 and 9, literal consequences | Robust partition and all-relabel weak-half exclusions, the unguarded-root counterexample, and actual strict coordinate/weighted payoff exclusions pass targeted checks. The six literal residual witnesses, all fifteen toggle owners/gains, attained margins, and eight singleton-test failures among fourteen canonical maps are checked in the named example modules. A passing singleton derivative test does not imply response invariance. |
| Sections 2 and 4, signed ambient estimates | `exists_quittingCrossedResponse_quadratic_bound` and `exists_quittingCrossedSingleton_minMap_margin` (`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseAmbientEstimates.lean`) pass their silent named check. The shared quadratic bound applies on a whole signed ambient ball; R0 coercivity is global, including zero dimension. |
| Section 6.3, unchanged sure-owner profile | `stationaryTerminalNash_or_sureSolo_everyHorizon_of_oneSidedWeakUnitRawGuards` (`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitFiniteHorizon.lean`) passes the exact same-profile all-horizon check, including horizon zero and positive-horizon delivery. Nonnegative owner payoff is retained; the signed punishment branch is not stationary Nash. |
| Section 10, no-UE restrictions | The all-relabel contrapositives pass the named check in `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseNoUERestrictions.lean`. The total-box and origin-ball ambient normalizations pass their named check in `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseAmbientNormalizations.lean`. No passing pair for arbitrary tables is asserted. |

The normalized and ambient annular degree interfaces cover the entire nonzero
root set without finiteness or regularity. Literal local-ball and total-box
wrappers and Bernstein uniqueness are checked; no parallel construction is
needed.

## Complete-claim audit: withdrawal and deadline packet

The interfaces below match the source scopes in
`WITHDRAWAL_AND_DEADLINE_QUIET_EXTENSIONS`. All packet claims have checked
declarations and actual-source adapters under their stated hypotheses. Actual
profile/law producers, existential rational wrappers and executable source
selectors remain separate interfaces. The full default build, exhaustive
production axiom audit, repository script gates and actual executable smoke
tests pass. The packet is retired unchanged; no general Fin4 result or runtime
complexity bound follows from these class-specific and bounded checks.

`WithdrawalBoundaryExamples.patient_deadline_incomparable_on_fixed_twoPlayerChild`
(`UniformEquilibrium/Quitting/Examples/WithdrawalRawIncomparability.lean`)
proves both raw-cone separations on the same child subset and player labels.
The two reward tables need not have identical restricted child payoffs.
These are raw-certificate exclusions, not no-equilibrium results.

An additional checked consequence not stated in the withdrawal packet is
`quietLift_fixedTarget_of_withdrawalFutureJoin_absorbingStationary`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalAbsorbingStationaryChild.lean`).
For an actual absorbing stationary child that is exact Nash against complete
behavioral deviations, any number of quiet outsiders with the five F/J
certificate kinds preserve that same exact equilibrium. The lifted profile's
actual payoff is one fixed UE target agreeing with every child coordinate.
Absorption internally removes the joint-Never residual; no positive singleton
pivot or singleton-sign premise is needed. This does not produce such a child
for an arbitrary table or assert an all-evaluation comparison.

| Source claims | Implementation boundary |
| --- | --- |
| Sections 1-4, pointwise characterization | The same-fixed-weights patient and ordinary deadline iff statements and attained-floor witnesses pass targeted checks and the full integration gate. They characterize the stated pointwise comparisons, not UE or every possible quiet extension. |
| Section 3.2, evaluated cancellation | `cancellationWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt` (`UniformEquilibrium/Quitting/Classification/QuietExtension/CancellationWithdrawalFullBehavioralDebt.lean`) retains actual independent private cancellation: earlier clocks survive, clocks at or after a finite deadline become Never, and a Never deadline is the identity. Raw N/F/J certificates give full behavioral debt for every actual child profile and nonnegative antitone evaluation, with summed weights and the zero-based floor. `exists_uniformPayoffWitnesses_eq_on_child_of_cancellationWithdrawalFamily` (`UniformEquilibrium/Quitting/Classification/QuietExtension/CancellationWithdrawalFixedTarget.lean`) retains literal quiet lifts and a fixed agreeing target; its Fin4 wrapper obtains the low-player child target internally. |
| Section 5, rational security | `exists_rational_deadlineWithdrawalSecurityRestartLaw_terminal_floor` (`UniformEquilibrium/Quitting/Classification/QuietExtension/RationalSecurityHazard.lean`) passes its silent named check. Arbitrary real rewards and every positive real error produce one positive rational hazard and the same actual geometric law before all future opponent tuples, with literal rational atoms, no Never mass and the terminal LP-value-minus-error guarantee. The exact rational LP optimizer/value under rational reward data remain separate checked results. Real positive approximation and envelope continuity supply the rational-hazard producer; no rational-data premise or new LP/stopping-law construction is needed. |
| Section 5, security examples | `zeroSecurity_evaluated_floor_strict_improvement`, `zeroSecurity_half_evaluated_guarantee`, `positiveSecurity_optimal_hazard_iff`, and `positiveSecurity_first_restart_date_payoff` (`UniformEquilibrium/Quitting/Examples/DeadlineSecurityPairExamples.lean`) pass the silent named module check. Complete literal two-player child tables supply both displayed LP calculations and actual same-law guarantees. The `(0,-1,1)` half law secures zero for all nonnegative antitone evaluations; `(1,1,0)` has value one only at hazard zero, while the positive law's worst future-date payoff is exactly `1-h` and its payoff on opponent Never is one. Actual Never on joint Never pays zero. No nonattainment theorem for all private plans or positive all-evaluation security is claimed. |
| Section 6, omitted Never row | `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` and `withdrawalFutureJoin_quietLift_outsideDebt_le_of_positiveSingleton` (`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`) cover all five kinds with residual times actual child joint-Never; a positive actual child singleton charges residual/singleton to a pivot. Patient Never bonus and sum-versus-max rules remain literal. `exists_uniformPayoffWitnesses_eq_on_child_of_withdrawalFutureJoinFamily` (`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`) retains actual quiet profiles and a fixed target; its Fin4 wrapper obtains the child target internally. These relaxations are terminal-only, including both security variants; outsider-only reward shifting retains the joint-Never correction, not arbitrary-profile strategic equivalence. |
| Section 7, rational feasibility and executable coefficients | `exists_rational_cancellationWithdrawalRewardCertificate` (`UniformEquilibrium/Quitting/Classification/QuietExtension/RationalCancellationWithdrawalWeights.lean`) and `exists_rational_withdrawalFutureJoinRewardCertificate` (`UniformEquilibrium/Quitting/Classification/QuietExtension/RationalWithdrawalFutureJoinWeights.lean`) rationalize actual raw feasibility, supplementing the six other variants with equality/zero weights, empty rows and zero-hazard optima retained. `selectNonnegativeRationalFeasible` and `selectRationalPrimalDual` (`MathUE/LinearProgramming/ExecutableRationalSelection.lean`) compute rational feasible data/zero-gap optimizer pairs with erased real feasibility proofs. Exact finite candidate tests precede exhaustive fallback without weakening acceptance. Actual reward coefficients/floors/security, sum/max weights, patient bonus, residual and positive-pivot correction compute rational K before accuracy; selected real weights/optimizers/caps are not inputs. No practical search complexity or infeasibility decision is asserted. |
| Section 7, finite-law enumeration | `rationalQuittingFiniteWordBoundedSearch_eventually_succeeds_of_terminalApproximation` (`UniformEquilibrium/Quitting/Root/RationalFiniteWordSearch.lean`) and `rationalQuittingFiniteWordSearchOfCardLeThree_finiteLaws` (`UniformEquilibrium/Quitting/Root/RationalLowPlayerFiniteWordSearch.lean`) derive target-free rational word search from actual existence and full-cap finite approximation, retaining zero players/dates, gap/late replies and Never. `ExecutableWithdrawal.fullWord_finiteLaws` and `ExecutableWithdrawal.futureJoinWord_finiteLaws` (`UniformEquilibrium/Quitting/Classification/QuietExtension/ExecutableWithdrawalQuietFiniteWords.lean`) compute source K before accuracy, query the actual labeled child at accuracy/K, and retain the SAME dates/atoms and literal Never outsiders with full parent terminal debt below accuracy. Require a rational table, nonempty child/outsiders, child count at most three and raw feasibility; F/J-only correction requires a positive actual child singleton. `exists_rationalWithdrawalFutureJoin_quietFiniteWordLaws` (`UniformEquilibrium/Quitting/Classification/QuietExtension/RationalWithdrawalFutureJoinQuietFiniteWords.lean`) is a separate existential rational wrapper, not the computable weights/K selector. No fixed real target or calendar/complexity bound is computed. |
| Sections 8.1--8.4, exact boundary examples | `WithdrawalBoundaryExamples.patientOnly_no_deadlineCertificate` and `WithdrawalBoundaryExamples.deadlineOnly_no_patientCertificate` (`UniformEquilibrium/Quitting/Examples/WithdrawalRawIncomparability.lean`) use complete literal tables and passing certificates to separate the cones. `patient_horizon_three_bound_fails` (`UniformEquilibrium/Quitting/Examples/PatientWithdrawalFiniteHorizonBoundary.lean`) retains the actual stage-average comparison; `patient_discounted_stage_bound_fails` (`UniformEquilibrium/Quitting/Examples/PatientWithdrawalDiscountedStageBoundary.lean`) retains the SAME actual child/lift and full debt for standard normalized discounted stage payoffs at every 0<d<1. `WithdrawalBoundaryExamples.neverResidual_outsideDebt_eq_residual_times_childJointNever` (`UniformEquilibrium/Quitting/Examples/WithdrawalNeverBoundary.lean`) gives all-five F/J systems at zero weights, child debt zero/joint-Never one, actual outside debt/residual one, and no positive singleton. Raw certificate infeasibility and patient finite/discounted comparison failures are not no-UE. |
| Section 8.5, sparse-calendar missed reply | Already matched by `displayed_replyValues`, `behaviorDeviationPayoffCap_false_eq_half`, and `behaviorCap_sub_sparseTestedReplyCap_eq_half` (`UniformEquilibrium/Quitting/Examples/SparseCalendarReplyGap.lean`). The existing module also handles the actual third Never-player extension. Reuse it; no second proof is needed. |
| Section 9, strict patient class | All literal rows and margins, all fourteen robust advancing-only full/F-J certificate obstructions, the full sixty-coordinate radius `1 / 100` with fresh floors, and the actual exact equilibrium/full response values pass silent named checks. `StrictPatientWithdrawal.degree_response_and_uniformPayoff_of_dist_lt` (`UniformEquilibrium/Quitting/Examples/StrictPatientWithdrawalFullScope.lean`) combines the same actual-table class conclusions; `StrictPatientWithdrawal.actualValue_uniformPayoff` (`UniformEquilibrium/Quitting/Examples/StrictPatientWithdrawalOneDateProfile.lean`) retains one literal profile for every accuracy. |
| Sections 10.1-10.3, strict deadline class | The translated literal table with Never still zero, actual row margins, all-evaluation debt consumers and full sixty-coordinate radius `1 / 512` pass the named full-scope check. `StrictDeadlineWithdrawal.actualValue_uniformPayoff` (`UniformEquilibrium/Quitting/Examples/StrictDeadlineWithdrawalOneDateProfile.lean`) passes its separate named check, retaining one exact terminal equilibrium profile at all accuracies and the distinct Never/late values. `StrictDeadlineWithdrawal.every_proper_child_split_exclusions_of_dist_lt` (`UniformEquilibrium/Quitting/Examples/StrictDeadlineWithdrawalAdvancingExclusions.lean`) passes its named check: seven children have genuine N-only full-certificate obstructions and seven have F/J obstructions; no F/J failure is asserted for the negative-singleton children. |
| Section 10.4, collision freedom | `StrictDeadlineWithdrawal.exists_actualCompletion_uniformPayoff` (`UniformEquilibrium/Quitting/Examples/StrictDeadlineWithdrawalCompletionRegion.lean`) passes its silent named check. Every arbitrary signed thirty-three-vector is retained with all sixteen singleton entries fixed; eleven actual outsider entries and a fixed UE target are produced internally. The exact passing region is nonempty, open and convex in those eleven coordinates for each fixed child vector. The chart is injective and covers the entire fixed-singleton fiber; no small-ball or all-completions claim is made. |
| Section 11, degree and partition comparisons | Both the patient radius `1 / 100` and deadline radius `1 / 512` full-scope modules pass silent named checks: exact determinant/inverse and inverse-distance bound, intrinsic degree one on every bounded open origin neighborhood, and injectivity for every response-invariant block map. UE uses the independent patient or deadline row producer, not degree one. |

The core fixed-target compilers already retain actual quiet profiles and obtain
the proper Fin4 child's payoff internally. They must be reused for the strict
class conclusions, rather than replaced by a supplied equilibrium or a second
uniformization argument. Completing cancellation alone does not retire this
packet: Sections 7--11 contain independent claims.

### Class connections identified for small followup adapters

These are implementation tasks inferred from checked owners, not additional
checked public theorems or packet seals.

- Expose the exact singleton matrix of every deadline completion, not only
  the small reward ball. `StrictDeadlineWithdrawal.completionReward_singleton`
  (`UniformEquilibrium/Quitting/Examples/StrictDeadlineWithdrawalCoordinateCompletion.lean`)
  fixes all sixteen singleton coordinates. The existing matrix and ambient
  degree owners can therefore be reused for arbitrary values in all forty-four
  collision coordinates. This does not globalize the small-ball response
  exclusions or infer UE from degree; UE still uses the passing completion region.
- Expose rationality of the explicit `feasibleOutside` section in
  `UniformEquilibrium/Quitting/Examples/StrictDeadlineWithdrawalCompletionRegion.lean`
  from rational child parameters. Finite floor/gain arithmetic supplies this;
  no LP search or continuous equilibrium-payoff selection is needed.
- Specialize the deadline all-evaluation comparison to the actual finite-horizon
  evaluation. The existing exact payoff and full-cap bridges retain the same
  profile and horizon, so no terminal approximation error should be introduced.
  The evaluation's antitonicity needs a discoverable lemma. This specialization
  does not apply to patient or terminal-only omitted-Never comparisons.

## Screened-root source dependencies

`GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR` needs its
degree-six algebraic exclusion and actual-source adapter, not another full-cap
proof. `oneDateProductQuittingContinuationBestResponseValue_oneDateThenNever_sureQuitter`
(`UniformEquilibrium/Diagnostics/Quitting/OneDateProductRootCaps.lean`) already
computes the complete behavioral cap when an opponent is sure to quit.
`Fin4FreeRewardCoordinate` and `card_fin4FreeRewardCoordinate`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Chart.lean`) supply the
fifty-six non-own-singleton coordinates. The existing chart fixes one specific
own-singleton vector; the packet instead varies those four entries directly
while holding the other fifty-six fixed. Recipient-row translation is not that
fiber: it changes the fixed coordinates as well.

The dependency order is:

1. Extend the existing coordinate chart to that direct own-singleton fiber.
2. Derive actual screened debt branches and four-corner bilinear rows, then
   extract a literal action label from positive equal debts. Reuse the complete
   cap and root-defect identities; do not assume a favorable root or cap field.
3. Supply the game-independent signed-maximal-minor exclusion for a three-by-four
   matrix and a rank-one kernel vector, including rank-deficient cases. The
   consumer must not supply a chosen invertible minor.
4. Construct the twenty-four degree-six factors, the packet's bounded
   nonvanishing witnesses, and their degree-144 product.
5. Connect polynomial nonvanishing to every actual screened root, then obtain
   density and the later compact-gap consequences.

These are implementation obligations, not checked completion claims. The
existing cap and chart results do not supply polynomial nonvanishing. A debt
identity or a generic minor lemma alone does not seal the exclusion.
Independently reviewed drafts cover that chain through actual-source exclusion:
the joint direct own-singleton chart, actual full-debt branch selection,
four-corner coefficient rows, generic signed-minor/Segre exclusion, sorted
six-pair enumeration, all twenty-four integer factors, their product, bounded
rational per-factor witnesses, and exact degrees six and 144. They still need
Lean checks. The actual chart preserves the other fifty-six reward coordinates;
the branch and corner adapters retain boundary hazards and derive their
coefficients from the table. Each factor has its own bounded witness; no single
table is asserted to witness all factors at once.

Independently reviewed, unapplied drafts now cover the next source steps:
compact direct-fiber extrema, polynomial nonvanishing density and rational
selection, zero-singleton/Never exclusion, and fixed-table and fiber-uniform
near-minimum singleton collars. These are not checked declarations. The
rational-source join selects one free-coordinate vector, maximizing singleton
vector and rational gap, then retains all three while selecting one collar
before every allowed singleton vector and actual near-minimum profile. Its
positive-gap threshold is explicit; it does not give uniform constants as
the gap tends to zero.
Section 5.1's additional rationalization of all sixty entries has a staged
producer. A separate same-table join retains its four rational own singletons,
perturbs only the free block to impose polynomial nonvanishing, and preserves
at least one quarter of the positively scaled source infimum. It then selects
a real singleton maximizer and a rational gap on that same free block. Root
source review passes; these drafts still need Lean and integration checks.
The maximizing singleton vector is not asserted rational.

The finite log-sum-exp value, entropy, local first-derivative and second-derivative
formulas pass the silent named `MathUE.Analysis.FiniteLogSumExp` check. They reuse
the canonical arbitrary-score exponential probabilities. Their transitive axiom
checks use only the three permitted standard axioms, and the full integration
gate passes. This generic calculus does not select the actual tester family
or construct a calendar.
The compact minimum-envelope right-derivative theorem passes its silent named
check and separate standard-axiom checks. It retains every old minimizer and
internally selects one attaining the least actual derivative; no favorable
minimizer or uniform differentiability certificate is supplied. Its index may
be any nonempty compact topological space, not only a compact metric space.
The full integration gate passes for both analytic additions.
The checked common-calendar source constructs the actual tester family:
zero, every owner's finite dates through the common endpoint, and separate
Never replies. Its maximum equals full behavioral exploitability, retaining
the signed singleton correction for late finite replies. It internally selects
a compact smooth minimum and computes that same profile's positive weights,
their sum-one identity, and the entropy inactivity bound.
`maximum_quittingCommonCalendarTesterGain_eq_exploitability`
(`UniformEquilibrium/Quitting/Paths/CommonCalendarTesterPool.lean`) and
`exists_quittingCommonWindowSmoothMinimum_with_weights`
(`UniformEquilibrium/Quitting/Paths/CommonCalendarSmoothMinimum.lean`) pass
silent named checks. Their actual pure-reply chart reuses the existing finite
payoff polynomial and full behavioral cap owners. The source does not supply
the tilted parameter, outer maximization or enlarged-calendar comparison.
The remaining common-calendar consumer needs projected four-coordinate
gradient selection, a same-table calendar telescope, and the silent shift
with its retained tester weights. The independent
harmonic restriction and literal boundary/noncoverage examples are separate
packet obligations. The reviewed collar does not supply these constructions.
The calendar's uniform cap moat concerns every near-minimizer of maximum debt
at the varying reward table.
`nearMinimumTerminalSemantic_cap_sub_singleton_ge`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCapNashNearMinimum.lean`)
instead assumes a global sum-debt floor and sum-debt excess. That theorem
cannot be applied by substituting maximum debt for its stated hypotheses.
`hasEscapeAwareQuantileClockCompression_of_normalized`
(`UniformEquilibrium/Quitting/Paths/CommonQuantileClockTransport.lean`)
and `escapeAwareQuantileClock_normalized_quantitative_bracket`
(`UniformEquilibrium/Quitting/Paths/CommonQuantileClockApproximation.lean`)
provide the integrated full-cap finite-clock approximation.
`exists_fin4_calendarUniformStoppingLaws_exploitability_le`
(`UniformEquilibrium/Quitting/Paths/QuantitativeFiniteClockSource.lean`)
passes its silent named check. Under the unit reward bound and a prescribed
depth at least nine, it internally selects one actual independent law tuple
before every larger calendar. Its unrestricted behavioral exploitability is
at most the actual behavioral infimum plus
`24 / (((clock - 1) / 8 : Nat) : Real)`, which tends to zero.
`exists_fin4_finiteClockStoppingLaws_exploitability_le` in the same owner
gives support `8 * j + 1` and error `24 / j` at every positive level.
Never remains literal, and the same laws and full behavioral caps are
retained on larger calendars. This does not assert a zero infimum or produce
the tilted tester weights. Membership stretch retains
the original table's ancestry; generic polynomial selection may choose a new
fiber, so those two producers cannot be interchanged. The opposed-reversal
consumer reuses the checked coherent exclusion and first reversal, adding only
the signed affine comparison needed for a second distinct, oppositely reversing
owner. None of these source steps is discharged by the polynomial alone.

The opposed-reversal consumer does not depend on the common-calendar weights.
`exists_sureOwner_strictOptionalReversal_of_membershipStretch_positiveMinimum_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/ThreeSureMembershipReversal.lean`)
already gives one reversing sure owner. The packet requires two distinct
owners with opposed orientations. Its separate route needs the internally
selected worst table and stretched singleton-fiber maximum, the signed
affine-row comparison, and the actual old-table root consumer. In the weak
same-root cases, old global attainment must be proved before invoking the
old table's all-player-tie theorem.
The all-case signed-row comparison in `MathUE/SignedAffineRowComparison.lean`
and actual full-debt adapter in
`UniformEquilibrium/Diagnostics/Quitting/SingleOptionalMembershipRows.lean`
are proved in Lean. The checked
`exists_opposedSureOwner_optionalReversals_of_membershipStretch_positiveMinimum_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/ThreeSureOpposedMembershipReversals.lean`)
produces two distinct sure owners with opposed strict signs at both tables.
Independent static review passes. The common-probability algebra reuses
`MathUE/SignedEndpointStretch.lean`; the root adapter derives old global
attainment before invoking all-player ties. These declarations consume the
source hypotheses rather than constructing the worst table or its fiber.
`opposedRegressionEnvelope_exact_minimum`
(`MathUE/SignedAffineRowRegression.lean`) checks the exact `25/99` old-envelope
minimum over every legal probability, strictly above the new `1/4` contact.
It is an affine-row regression, not a positive-gap game.
The raw worst-table and literal stretched-fiber source is now proved by
`exists_membershipStretch_singletonFiber_source_of_positiveInf`
(`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchWorstTableSource.lean`).
`exists_membershipStretch_source_strictSureCoalitionGap_of_positiveInf_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchSureCoalitionSource.lean`)
supplies the quantitative floor over all eleven nonsingleton coalitions,
unchanged under arbitrary own-singleton reselection. The final
`exists_membershipStretch_source_opposedReversals_of_no_uniformPayoff_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchOpposedSource.lean`)
joins both conclusions at the same internally selected source, before every
attained root request. This covers the three-sure packet's raw source and
opposed-owner conclusion. The larger singleton-fiber source packet still
requires its projected normal, common-calendar weights, silent shift,
and fixed-table accuracy/depth producer; the strict coalition floor alone
does not supply those fields. Packet lifecycle remains math's responsibility.

### Connections from the completed three-sure implementation

These are proof-supported follow-ups, not yet checked declarations:

- The opposed final rows and attained-minimum ties give strict quantitative
  mixing: if `m` is the final infimum and `p` the optional Quit probability,
  then `m/2 < p < 1-m/2`. Each negative endpoint gives a strict inequality;
  unit rewards bound the opposite gap by two. This strengthens genuine
  mixing without constructing a three-sure minimum.
- The exact pure-set semantic-pair theorem in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean` extends the coalition
  floor to every continuation after that same nonsingleton pure root.
  It does not exclude arbitrary staggered deterministic quitting times.
- Stopping-law exploitability congruence transfers the opposed-root result
  to other behavioral presentations of the same stopping-law family.
  The representation remains a premise, not a produced source.
- Reward robustness preserves a coalition separation `margin` at nearby
  tables with lower bound `margin - 4*delta`: both profile exploitability
  and the actual infimum change by at most `2*delta`. Positive separation
  requires `4*delta < margin`; no UE counterexample robustness follows.

### Two-player premium cores with strict leave preference

`exactRootSuccessor_mem_singletonLowerBoundary_of_twoPlayerPremiumCore_strictLeave`
(`UniformEquilibrium/Quitting/Classification/TwoPlayerPremiumCoreExactRootBoundary.lean`)
proves the new packet's raw exact-root return, for arbitrary finite players.
The proof handles positive outsider hazards first, then reuses the canonical
paired-root endpoint formulas and exact supported-action equality. Only the
leaving core player's annotation floor is needed; the second core floor can
be omitted. Outsider hazards, arbitrary passive rewards and larger-coalition
core premiums are retained. The shared constant-participant endpoint helper
lives in `UniformEquilibrium/Quitting/Root/OpponentCoalitionPayoff.lean`.
`not_isQuittingFullExactRootPotential_of_twoPlayerPremiumCore_strictLeave`
(`UniformEquilibrium/Quitting/Classification/TwoPlayerPremiumCoreSmoothDrift.lean`)
is proved in Lean using the existing singleton-face drift and lower-boundary
minimum signs. The stronger one-floor return allows lowering another binding
coordinate, even the second core coordinate. Differentiability at boundary points
suffices; neither a neighborhood C¹ hypothesis nor an outsider-only perturbation
is needed.
`exists_uniformEquilibriumPayoff_of_twoPlayerPremiumCore_strictLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/TwoPlayerPremiumCoreUniformPayoff.lean`)
is proved in Lean for nonnegative-singleton four-player tables, composing the
actual polynomial producer and zero-solo branch. The concrete packet table,
its raw-class checks, UE consequence and product-low failure are checked in
`UniformEquilibrium/Quitting/Examples/TwoPlayerPremiumCoreStrictLeave.lean`.
`quittingSingletonMatrix_eq`, `normalCore_eq_univ`, `matrix_isR0`,
`matrix_r0Degree_eq_one`, and `matrix_isStandardQ`
(`UniformEquilibrium/Quitting/Examples/TwoPlayerPremiumCoreStrictLeaveMatrix.lean`)
pass the silent named check. The actual singleton matrix has full recursive
normal core and no nonzero homogeneous LCP solution. Its entire root set at
offset `(1,-1,-1,-1)` is the singleton `(0,1,1,1)`, with inactive residual two
and active determinant seven. The canonical actual-root sum gives degree one,
and the existing degree theorem supplies standard Q. The remaining principal
Q-bar and inverse tests, response-partition and proper-child certificate
screening claims are not supplied; this is not a whole-packet seal.

## Greatest premium core: structural and exact-root prerequisites

`finiteCoalitionPremiumCore_eq_empty_iff`
(`MathUE/FiniteCoalitionPremiumCore.lean`) identifies the greatest finite
trap union with the obstruction to support peeling, for an abstract positive
coalition relation. Its actual reward adapter is
`quittingPremiumCore_eq_empty_iff_weakSupportPeeling`
(`UniformEquilibrium/Quitting/Classification/QuittingPremiumCore.lean`).
The same adapter gives outsider flatness only on the outsider's extension
of a nonempty core, under nonnegative participant premiums.
`quittingPremiumCore_pair_reward_gt_singleton`
(`UniformEquilibrium/Quitting/Classification/QuittingPremiumCorePair.lean`)
derives the literal strict pair premiums from a pair core without adding
nonnegative-premium hypotheses.

`exactRootSuccessor_active_eq_singleton_of_support_not_premiumTrap`
(`UniformEquilibrium/Quitting/Classification/QuittingPremiumCoreExactRoot.lean`)
uses the actual support and exact coalition masses to obtain an active
singleton binding for every nonempty nontrap support. Signed annotations
and singleton rewards remain allowed.
`exactRootSuccessor_mem_singletonLowerBoundary_of_pairPremiumCore_strictLeave`
(`UniformEquilibrium/Quitting/Classification/QuittingPremiumCoreStrictLeave.lean`)
excludes the remaining pair support using strict leave preference and only
the first annotation floor. It retains all outsider hazards and full exact
Nash, without global outsider flatness. Its conclusion is the singleton
lower-boundary return, not full bounded-L return. These exact-root units alone do not
supply a size-at-most-two UE theorem,
or the mutual-join branch and its degree/index analysis.

## Signed common-leaver return and analytic criterion

`not_isQuittingFullExactRootPotential_of_protectedSingletonReturnDomain`
(`UniformEquilibrium/Quitting/Projective/ProtectedSingletonReturnDomainSmoothDrift.lean`)
is proved in Lean for arbitrary finite signed reward tables under an explicit
compact return-region hypothesis. The singleton lower boundary lies in the
region, whose points obey the protected floor and have some coordinate at
or below its singleton. Absorbing exact roots must return there from every
boxed protected annotation, not just annotations already in the region.
Continuity is required only on this region and differentiability only at
the singleton lower boundary. The proof localizes an actual region minimum
to that boundary and retains the literal signed charge `3 * M + bound`.
The lower-boundary special case derives continuity from differentiability,
so it adds no regularity hypothesis to the earlier nonnegative criterion.

`exactRootSuccessor_protected_sublevel_of_commonLeaver_strictLeave`
(`UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`)
is a checked actual reward source: only the protected player's participant
premiums are nonnegative, every strict premium trap contains that player,
and strict leave comparisons cover each nonempty coalition in the remaining
actual core. It retains all outsider hazards and full exact Nash, giving the
protected floor and some weak singleton sublevel, not all-player floors.
`not_isQuittingFullExactRootPotential_of_commonLeaver_strictLeave`
(`UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaverSmoothDrift.lean`)
instantiates the compact criterion on the actual protected sublevel domain.
Continuity on that domain and differentiation only on the singleton boundary
suffice, without the packet's C1-neighborhood assumption.

`exists_uniformEquilibriumPayoff_of_commonLeaver_strictLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/CommonQuittingPremiumLeaverUniformPayoff.lean`)
and `exists_uniformEquilibriumPayoff_of_commonLeaver_weakLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/CommonQuittingPremiumLeaverRewardClosure.lean`)
are checked actual Fin4 consumers with nonnegative own singleton rewards.
The strict case uses the shared polynomial/zero-singleton producer; the weak
case perturbs only the protected player's passive rewards, preserves all
participant rewards and the exact trap/core inventory, and applies fixed-target
reward closure. No nonnegative premium condition is added for other players.
`exists_uniformEquilibriumPayoff_of_pairPremiumCore_weakLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/QuittingPremiumCoreUniformPayoff.lean`)
and its strict-leave counterpart are checked thin instances for an actual
two-player greatest core, with nonnegative own premiums and singleton rewards.
They do not supply the mutual strict-join branch or a general core-size theorem.
The packet's signed counterroot and rational-fixture screen obligations
remain separate; these theorems are not a whole-packet seal.

`CommonLeaverSignedPremiumFixture.exists_uniformEquilibriumPayoff_strict` and
`CommonLeaverSignedPremiumFixture.exists_uniformEquilibriumPayoff_weak`
(`UniformEquilibrium/Quitting/Examples/CommonLeaverSignedPremiumFixture.lean`)
apply these actual consumers to the literal signed Section 6 table. The
fixture proves its participant premium classification, exact traps and
three-player greatest core, protected common leaver, strict leave, negative
outsider premium and product-low obstruction. The weak application follows
the same strict comparisons, not a separate equality-boundary regression.
The Section 5 signed counterroot and the matrix, inverse, response-partition
and child-screen separation obligations remain unfinished.

`exactRootSuccessor_mem_protectedSetBox` and
`exactRootSuccessor_mem_protectedSetSublevelDomain`
(`UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`)
produce the support-specific packet's raw protected floors and signed sublevel
return. Every actual trap supplies a protected leaver with all nonempty
opponent-coalition comparisons. Protected floors hold at every boxed source;
absorbing sublevel return additionally requires protected floors at the source.
The old common-leaver interface delegates the canonical support-sum proof
without changing its public hypotheses.

`not_isQuittingFullExactRootPotential_of_convexReturnDomain`
(`UniformEquilibrium/Quitting/Projective/ConvexReturnDomainSmoothDrift.lean`)
provides the signed generic analytic step for an actual compact convex return
region containing the singleton upper box. All boxed exact roots return to
that region; positive-absorption exact roots from the region also return to a
singleton sublevel. Compact localization supplies an actual lower-boundary
minimum with zero absorption on its entire exact Nash fiber. The convex
segment-or-coordinate-sign cone and absorption-scaled Taylor argument use
continuity only on the sublevel region and ambient differentiability only on
the singleton lower boundary, not derivative continuity or a neighborhood C1
hypothesis. No individual successor floors or participant sign condition is
part of this generic analytic interface.

`not_isQuittingFullExactRootPotential_of_supportSpecific_strictLeave`
(`UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeaversSmoothDrift.lean`)
instantiates that theorem from the actual protected-set raw return. It works
for every finite nonempty player type with signed singleton rewards and no
protected-set nonemptiness assumption. Shared minimum and downward-charge
proofs preserve the older nonconvex compact-return theorem's public telescope.
`exists_uniformEquilibriumPayoff_of_supportSpecific_strictLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/SupportSpecificQuittingPremiumLeaversUniformPayoff.lean`)
is the actual Fin4 consumer with nonnegative own singletons. Its weak companion
`exists_uniformEquilibriumPayoff_of_supportSpecific_weakLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/SupportSpecificQuittingPremiumLeaversRewardClosure.lean`)
uses all-passive perturbations and canonical reward closure to obtain one fixed
original target. Arbitrary real perturbations preserve participant entries,
traps, the greatest core and maximal protected set; positive perturbations
strictify the same weak leavers. Maximal-protected-set wrappers supply their
participant tests internally. These strategic consumers do not assert a weak
analytic exclusion.

The weighted-floor raw chain supplies the corresponding premises separately:
`HasWeightedQuittingTrapLeavers`
(`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`)
requires the same positive-on-trap, zero-outside weight to pass global inserted
premium tests for every coalition and all proper nonempty leave comparisons.
The full-coalition identities retain all atoms, including the empty one.
`exists_successor_le_singleton_of_weighted_strictLeave`
(`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapReturn.lean`)
handles the all-sure support separately and internally proves actual trap
exclusion and absorbing sublevel return. The canonical region is a closed
convex intersection of valid halfspaces, not asserted to be a finite polytope.
`exists_uniformEquilibriumPayoff_of_weightedTrap_strictLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversUniformPayoff.lean`)
is the actual Fin4 consumer with nonnegative own singletons. Its weak companion
`exists_uniformEquilibriumPayoff_of_weightedTrap_weakLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversRewardClosure.lean`)
retains the same raw weights under all-passive perturbation and obtains one
original fixed target by reward closure. Arbitrary real perturbations preserve
the valid-weight family and the canonical domain at any fixed box bound, not
the computed reward-bound constant. No weak analytic exclusion is claimed.
Packet-specific reductions and fixtures remain separate obligations.

The boxed-Nash-charge packet now has an actual raw Fin4 payoff producer.
`exists_uniformEquilibriumPayoff_of_boxedQuittingNashCharges`
(`UniformEquilibrium/Quitting/Classification/Existence/BoxedQuittingNashChargesUniformPayoff.lean`)
passes its silent named check. It assumes nonnegative own-singleton rewards,
an arbitrary coordinate reward bound, and literal coefficient tests with a
strict charge margin for every premium trap. All-sure withdrawal and mixed-sure
support are dispatched before division. Actual odds, cardinal-layer grouping,
the generic mean bound and finitely many strict trap margins produce one common
box before every annotation; exact Nash roots and absorption are supplied
internally. Trap-free reward tables are included vacuously. No strategic or
return certificate is a raw input.
`Math.NextToTopSymmetric.value_le_sum_pow_div_card_pow`
(`MathUE/FiniteNextToTopSymmetricMean.lean`) now proves its literal next-to-top
elementary symmetric bound for every finite inventory of at least three
coordinates, including boundary and zero vectors. The supplied compact-maximum
averaging proof is formalized, not replaced by a Fin4-only estimate.
The analytic return theorem retains arbitrary finite players, signed rewards,
continuity on the same boxed sublevel domain and differentiation only on the
singleton lower boundary. The semantic payoff consumer is Fin4.
`QuittingTrapChargeCoefficients.threshold_of_cardinality_three` and
`QuittingTrapChargeCoefficients.threshold_of_cardinality_four`
(`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeOdds.lean`)
give the literal rational and square-root thresholds. The complete Section 6
and Section 7 tables supply participant/trap/core censuses, exact coefficient
layers, thresholds 90 and 348 times the square root of 45, and actual payoff
consumers in `UniformEquilibrium/Quitting/Examples/BoxedNashChargeTripleFixture.lean`
and `UniformEquilibrium/Quitting/Examples/BoxedNashChargeFullCoreFixture.lean`.
`eventually_full_potential_exclusion_fixed_box` and
`eventually_positive_fullSingletonRaise_uniformPayoff_neighborhood`
(`UniformEquilibrium/Quitting/Examples/BoxedNashChargeNeighborhoodFixtures.lean`)
give an actual signed analytic neighborhood at fixed box five and positive
interior UE tables by raising exactly the three zero own-singletons. The
proper-triple table has a full reward-coordinate UE neighborhood; the original
full-core table's UE neighborhood retains the nonnegative-singleton slice.
The raw finite strict tests preserve actual traps and one fixed coordinate
bound, strictly above the tables' attained maxima.
`exists_box_potential_exclusion_of_boxedQuittingNashCharges`
(`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`)
exposes the signed arbitrary-finite raw analytic producer, selecting the box
before every potential with continuity on the same sublevel domain and ambient
differentiability only on the singleton lower boundary. Its selected-root
producer needs no comparison between the reward bound and return box; the
analytic consumer retains the strict comparison. The literal triple and full
tables now exclude all pure stationary terminal Nash profiles, including all-Never, and
any nonnegative weighted singleton floor asserted for every product law must
have zero weights, in
`UniformEquilibrium/Quitting/Examples/BoxedNashChargeFloorAndPureExclusions.lean`.
These tests need no supplied Nash root or weight normalization. Unbounded
annotation counterroots, every proper-child debt witness and matrix/response
exclusions remain obligations. The boxed-charge packet is
not sealed by its main payoff result alone. The game-independent binary coalition encoder
`Math.FiniteCoalition.binaryCode_injective` (`MathUE/Finset/CoalitionBinaryCode.lean`)
is extracted from the existing reward-table owner; its private aliases retain
their scopes and the fixtures no longer depend on unrelated example theorems.
`quittingRoot_activeHazards_lt_one_of_leave_sums`
(`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`)
is a useful stronger reusable source lemma: actual support size at least two
and the stated leave tests suffice, without premium, charge or source-floor
hypotheses. This does not enlarge the raw charge class by itself.
No equality-margin weak theorem is inferred from the packet's nonstrict
coefficient bounds and strict charge margin. The global two-joint cyclic-child
packet shares the child complementarity and actual outer-exit adapters with
the one-joint packet; its nonlinear two-row selector is a separate source unit.
The signed pair-core same-sign packet likewise requires its literal signed
source adapters; none follows merely from these protected-set consumers.
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_on_subbox`
(`UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`)
now supplies the conditional Fin4 consumer for a chosen returning exact root
at every strictly-below-singleton source in the same boxed sublevel domain.
Its box bound may lie strictly above the reward bound and at most two above it.
The generalized
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_of_reward_bound`
in the same file accepts any coordinate reward bound, with the box strictly
above it and no larger than the canonical sum bound plus two. It restricts the
same canonical polynomial rather than strengthening the packet's charge tests.
Canonical compact-minimum localization and downward charge use existential
return; their old universal wrappers retain their original scopes. Only the
universal minimum wrapper concludes zero absorption for every exact root at
the minimum. The signed-pair raw producer now performs the pure-pair split
explicitly; mixed-trap composition remains separate. A pure exact pair is a
direct UE alternative, not silently asserted to satisfy chosen return.

The mixed-premium-trap packet shares the actual boxed charge producer for
larger traps and the full clipped-map/local nonlinear index adapter for signed
pairs. It requires finite negative-index sums and source tie polynomials, not
a unique-root shortcut. Its weak step uses localized zero-gap passive
singleton perturbations with charge and reward-bound margins; the uniform
all-passive increment closure above is not that adapter.

`exists_ambientDegree_eq_sign_det_of_hasFDerivAt_on_nhds`
(`MathUE/Topology/AmbientDegreeNonlinearLocalIndex.lean`) now derives local
isolation and determinant-sign degree from an actual nonsingular derivative,
with continuity only on a neighborhood and differentiation only at the zero.
It includes dimension zero and assumes neither coercivity nor a supplied
isolating region. `quittingFullClippedEndpointMap_hazardOfRoot_eq_self_iff_isZeroNash`
(`UniformEquilibrium/Quitting/Root/FullClippedEndpointMap.lean`) supplies the
literal full-cube fixed-point bridge, including sure and inactive hazards.
The polynomial endpoint gaps are smooth on all real hazards.
`pairNash_hasFDerivAt_and_negative_det_fullClippedDisplacement`
(`UniformEquilibrium/Quitting/Root/PairFullClippedJacobian.lean`) now supplies
the actual full ambient pair derivative, including identity inactive rows.
`signed_pair_core_badRoot_hasFDerivAt_and_negative_det`
(`UniformEquilibrium/Quitting/Classification/SignedPairCoreBadRoot.lean`)
internally supplies actual support, properness and every inactive strict gap;
actual bad-root uniqueness is also checked. The actual composition is
`exists_exactRoot_singletonSublevel_of_signed_pair_core`
(`UniformEquilibrium/Quitting/Classification/SignedPairCoreSelectedReturn.lean`):
it supplies a second full-clipped fixed point and uses bad-root uniqueness to
produce a selected returning exact root when pure pair Nash is excluded.
`exists_uniformEquilibriumPayoff_of_signed_pair_core_strictSameSign`
(`UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreUniformPayoff.lean`)
splits that alternative from a direct pure-set sure exit, without a supplied
strategy, selected-root or index certificate. The generic
`isUniformEquilibriumPayoff_setReward_of_pureSetNash`
(`UniformEquilibrium/Quitting/Root/PureSetNashSureExit.lean`) works for every
finite coalition of size at least two, without reward signs or core premises.
No annotation avoidance is needed for the signed-pair branch. The generic
`not_all_fixedPoints_have_negative_det_finite`
(`MathUE/Topology/AmbientDegreeNegativeFixedPointObstruction.lean`) derives its
finite census internally by compactness and nonlinear isolation, and contradicts
degree one when every actual cube fixed point has negative determinant.
Dimension zero and arbitrary finite coordinate types are included.
`tripleNash_hasFDerivAt_and_negative_det_fullClippedDisplacement`
(`UniformEquilibrium/Quitting/Root/TripleFullClippedJacobian.lean`) computes the
actual full ambient triple derivative and negative sum of the two directed
cycle products, retaining all inactive directions. The literal cross-partial
and odds-ratio source is in
`UniformEquilibrium/Quitting/Root/TripleEndpointPartials.lean`. Generic
own-coordinate and proper-support derivative proofs live once in the canonical
full derivative owner; the old signed-pair weak consumer passes its regression.
The actual joining-attractive triple source is recorded below; general
mixed-sign raw classification and composition remain separate.
`exists_fixedPoint_ne_of_negative_det_finite`
(`MathUE/Topology/AmbientDegreeUniqueFixedPointIndex.lean`) now derives an actual
second fixed point using nonlinear local index and excision in an expanded
ambient chart, including cube boundary coordinates. The weak raw consumer
`exists_uniformEquilibriumPayoff_of_empty_or_signed_pair_core_weakSameSign`
(`UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreRewardClosure.lean`)
accepts nonnegative own singletons and either an empty core or an exact pair
core with nonnegative joining-gap product. It perturbs only the two specified
passive singleton entries, not every passive reward, preserves all participant
entries/traps/core, and supplies one original target by actual reward closure.
It is not a theorem for every core of size at most two, or a weak analytic return
theorem. The mixed-sign triple-core packet shares the needed finite-index census
and actual full-clipped derivative infrastructure, rather than inheriting this
unique-bad-root argument. The triple packet additionally requires
its full three-player negative determinant, sure cascade and pair-tie/source
restoration, with the pure-core alternative separated. These are now supplied
for the joining-attractive source by
`exists_uniformEquilibriumPayoff_of_joiningAttractive_core`
(`UniformEquilibrium/Quitting/Classification/Existence/JoiningAttractiveCoreUniformPayoff.lean`)
and its actual weak consumer
`exists_uniformEquilibriumPayoff_of_weakJoiningAttractive_core`
(`UniformEquilibrium/Quitting/Classification/Existence/JoiningAttractiveCoreRewardClosure.lean`).
Only nonnegative own singletons, computed core cardinality three and literal
strict or weak insertion comparisons are inputs. Bad-root support, sure
cascade, pair tie avoidance, full negative Jacobians and the internal census
obstruction supply selected return; compact simplex projection restores it
at every real source strictly below some own singleton, including boxed
boundaries. Weak closure decreases only
core-player passive entries on nonempty subsets of that player's erased core,
preserving participants, own singletons, traps and core for every real shift.
It gives one original-game target, not a weak analytic return theorem.
This localized perturbation is not the uniform all-passive increment consumer.
The packet's rational table and variants, actual bad triple counterroot,
weighted aggregate-leave and matrix/response separations remain separate.
The attractive packet explicitly makes no all-fourteen-child-debt assertion.
Its singleton matrix shares the boxed/signed-pair Gamma, whose positive balance
charge gives degree one, not the negative-charge cyclic degree-zero theorem.
The literal nonlinear response identity depends on the full reward table and
cannot be inferred from its singleton matrix alone.
`quittingPairInactiveGapNumerator_update`
(`UniformEquilibrium/Quitting/Root/PairInactiveGapNumerator.lean`) now derives
the literal cleared four-atom inactive endpoint numerator and its own
annotation slope, the negative product of the two joining gaps. When that
product is nonzero, the canonical coordinate-affine density lemma gives
simultaneous avoidance of finitely many such zero sets in every nonempty open source set;
unused core players remain among inactive recipients. This is source-generic
annotation avoidance, not a root classification, Jacobian sign or degree sum.

`eventually_exactRoot_absorption_lt_of_exact_fiber_absorption_zero` and
`tendsto_exactRoot_absorption_zero_of_exact_fiber_absorption_zero`
(`UniformEquilibrium/Quitting/Root/CompactExactNashFiberMoat.lean`) give uniform
small absorption for all nearby exact roots and vanishing absorption for
arbitrary exact-root selections over convergent sources. Their hypothesis is
zero absorption on the exact limiting fiber, not a unique all-Continue root.
The diagnostic unique-all-Continue moat is a thin scope-preserving instance.

## Larger-eigenvalue signed four-cycle source

`largerTargetValue_isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Cycles/SignedFourCycleLargerCertificate.lean`)
computes positive masses, exact singleton balances and one fixed behavioral
equilibrium target from actual signed singleton rows and `LargerTests`.
The positive singleton determinant supplies negative characteristic value at
one internally; the transfer lower-right entry exceeds one and the opposite
ratios alternate negative/positive/negative/positive. The eigenvalues straddle
one, so this is distinct from the unchanged smaller-branch `StrictTests`.
Own singletons and nonsingleton rewards remain arbitrary signed reals.
`exists_uniformEquilibriumPayoff_of_reindexed_signedFourCycle_larger`
(`UniformEquilibrium/Quitting/Classification/Existence/SignedFourCycleLargerUniformPayoff.lean`)
returns a fixed target to the original relabeled game. The common positive-mass,
Bellman and balanced-certificate proofs live once in the branch-independent
owners; the old smaller finite-early-absorption consumer retains its scope.
The reward-only predicate `HasReindexedLargerSignedFourCycleSingletonTable`,
its openness theorem and
`exists_uniformEquilibriumPayoff_of_reindexedLargerSignedFourCycleSingletonTable`
(`UniformEquilibrium/Quitting/Classification/Existence/SignedFourCycleLargerUniformPayoff.lean`)
derive all data internally from polynomial strict matrix tests and return one
original-game target. The full rational fixture, stationary exclusions,
fourteen child witnesses and class comparisons remain packet obligations.
Fixture smaller-root exclusion must cover every
labeling and positive row scaling; terminal affine transport is not silently
assumed because Never remains zero. Zero/sure stationary boundaries and each
child's complete behavioral cap, late singleton and Never choices must be
included. The new fixture matrix is not the shared boxed/attractive Gamma.

The shared positive-charge matrix is supplied once by
`matrix_r0Degree_eq_one`
(`MathUE/LinearProgramming/CyclicChildSharedFixture.lean`). Its literal regular
offset has exactly the root `(0, 1, 1, 1)`, inactive residual two and active
determinant seven. The child inverse and pivot inverse row are computed in the
same owner; the latter has a negative entry. Literal full-core and explicitly
relabeled proper-triple reward-table bindings are supplied by
`full_singletonMatrix_degree_eq_one` and
`triple_relabel_singletonMatrix_degree_eq_one`
(`UniformEquilibrium/Quitting/Examples/BoxedNashChargeSharedMatrix.lean`).
`only_nonnegative_child_inverse`
(`MathUE/LinearProgramming/CyclicChildSharedFixtureScreens.lean`) singles out
deleted player zero, whose passive inverse row fails nonnegativity. The full
inverse has a negative entry, there is no mutually positive singleton pair,
and the principal zero-three block is not standard Q. These are matrix screens,
not a conflation of standard Q with projective Q or behavioral child witnesses.
`full_excludedPartition_not_responseInvariant` and its triple counterpart
(`UniformEquilibrium/Quitting/Examples/BoxedNashChargePartitionScreens.lean`)
exclude thirteen displayed partitions. The remaining named pivot partitions
are excluded by the actual nonlinear axis responses in
`full_pivotPartition_not_responseInvariant` and its triple counterpart
(`UniformEquilibrium/Quitting/Examples/BoxedNashChargeAxisResponse.lean`).
`full_block_injective_of_responseInvariant` and its triple counterpart
(`UniformEquilibrium/Quitting/Examples/BoxedNashChargeArbitraryPartitionExclusion.lean`)
now exclude every nondiscrete response-invariant block map into any label type.
The shared row-sum algebra forces injectivity or the pivot/child partition;
actual full-table nonlinear responses exclude the latter. The canonical
finite-label compression preserves every block equality, dispatches an empty
player set internally and requires neither finite nor surjective original
labels. The existing response lift, invariance and row-sum definitions now
accept arbitrary labels; their finite-dimensional derivative proof is reused.
Behavioral children and debt/quiet-extension witnesses remain separate, as do
projective-Q criteria not implied by the standard-Q block screen.

## Generic positive-inverse family dependencies

`hasStrictlyPositiveInverse_of_zMatrix_positive_vector`
(`MathUE/LinearProgramming/ZMatrixPositiveVector.lean`) derives an actual
strictly positive inverse from nonpositive off-diagonal entries, a positive
vector with strictly positive image and irreducibility of the displayed
normalized matrix. Diagonal positivity, contraction and nonsingularity are
derived internally using the canonical Neumann-series owner; the matrix index
may be empty. Irreducibility remains an explicit mathematical hypothesis,
not a literal matching-graph producer.
`exists_uniform_positive_inverse_entry_bounds_on_compact`
(`MathUE/LinearProgramming/CompactPositiveInverseBounds.lean`) derives uniform
positive lower and finite upper entry bounds for a continuous-on-compact
positive-inverse family, including empty parameter/index cases.
`Math.CrossedMatching.hasStrictlyPositiveInverse_variableMatrix_of_standardQ`
(`MathUE/LinearProgramming/CrossedMatchingPositiveInverse.lean`) now supplies
the literal crossed-matching matrix family: strict singleton matching signs
and standard Q produce the positive vector, graph and actual inverse
internally. The scheduled-pair premium need only exceed its harmful singleton
comparison; passive rewards are arbitrary signed reals and odds are arbitrary
finite nonnegative coordinates. Continuous-on-cube inverse families have
uniform positive lower and finite upper entry bounds. This is an actual matrix
source adapter, not the final odds root or matching-game payoff producer.

`Math.CrossedMatching.scaled_eigenpoint_sum_lt_bound`
(`MathUE/LinearProgramming/CrossedMatchingOdds.lean`) bounds every strictly
positive scaled eigenpoint of the literal raw-data odds map for a scale in `(0,1]`; the
displayed eigenpoint equality remains its hypothesis. It does not produce
that point. `Math.exists_fixedPoint_of_normalized_radial_map`
(`MathUE/Topology/NormalizedRadialFixedPoint.lean`) supplies the generic
normalized direction/radius Brouwer step under explicit compact-convex
direction, shell continuity, positive mass, normalized-cone, inner and outer hypotheses.
`Math.exists_positive_fixedPoint_of_coordinate_radial_bounds`
(`MathUE/Topology/PositiveCoordinateRadialFixedPoint.lean`) assembles the finite
positive-coordinate cone and inner radius from explicit entrywise field and
weight estimates. `Math.CrossedMatching.exists_positive_odds_of_matching_standardQ`
(`MathUE/LinearProgramming/CrossedMatchingPositiveOdds.lean`) discharges these
conditions from the actual matching data and returns positive odds satisfying
the original passive equations. The game source
`GameTheory.PairedCycle.CrossedMatching.exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`) uses the
original-game non-Q alternative or this root to obtain a fixed payoff target.
Its standard-Q branch also retains exact terminal Nash and the same selected
profile for every accuracy's horizon witnesses. Literal twelve joining caps
provide the passive Quit bounds; signed own-singletons and unmentioned
collisions remain unrestricted. The weak source uses reward closure, not an
assertion that a single limiting profile satisfies the strict construction.

`Math.CrossedMatching.exists_positive_odds_of_positive_inverse`
(`MathUE/LinearProgramming/PositiveInverseTwoPairOdds.lean`) supplies a distinct
odds producer from a zero-diagonal positive-inverse matrix, negative scheduled
entries, nonnegative premiums and nonpositive passive increments. No favorite
matching signs or Q hypothesis is inferred. The actual-game adapter is now
`exists_exact_cycle_of_positive_inverse_all_initial`
(`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`), with
one produced odds vector before all initial phases. Strict, weak and inverse
sources also have arbitrary-label transport. The pure scheduled-pair cap
source uses the generic `oneDateThenNever_exactHorizon_of_sureExitSet`
(`UniformEquilibrium/Quitting/Root/PureSureSetExactHorizons.lean`) and retains
exact terminal Nash, every finite horizon and a fixed original-game target.
The quantitative cycle facades
`exists_quantitative_cycle_of_standardQ` and
`exists_quantitative_cycle_of_positive_inverse`
(`UniformEquilibrium/Quitting/Cycles/CrossedMatchingFiniteHorizon.lean`)
produce one hazard vector before all initial phases and positive horizons.
Delivery is bounded by `M*C/N` and every behavioral gain by `2*M*C/N`,
with printed factor-two weakenings. The weak reward-closure result does not
assert a proper quantitative cycle. Full packet separation obligations remain separate.

`GameTheory.CrossedMatchingFixture.exact_terminal_and_fixedProfile`
(`UniformEquilibrium/Quitting/Examples/CrossedMatchingFixture.lean`) supplies
the complete rational table, explicit positive odds and passive equations,
both phase vectors and literal active/passive endpoints. It identifies the
actual terminal payoff and retains exact terminal Nash and one profile for
all accuracies at sufficiently long horizons, at either initial phase.
The strict raw-source region is open in the full reward-table coordinates
and contains this table, yielding actual nearby UE targets.
`principal_det_eq`, `matrix_positive_inverse` and `matrix_r0Degree_eq_one`
(`UniformEquilibrium/Quitting/Examples/CrossedMatchingFixtureMatrix.lean`)
bind the actual singleton matrix, all fifteen nonempty principal determinant
rows, R0 and positive inverse to degree one; the full determinant is
`33583397/20480`. This is not a no-UE obstruction.
`exists_unsafe_witness_for_every_proper_child`
(`UniformEquilibrium/Quitting/Examples/CrossedMatchingFixtureChildren.lean`)
supplies actual selected stationary Nash witnesses for all fourteen proper
nonempty children, zero joint Never mass, literal profitable quiet-lift
deviations and failure of every real weighted child-debt sum plus finite signed
Never charge. The exact gains are `177/32`, `113/14` or `1/2`; no claim is made
about every child equilibrium.
`finiteAverage_delivery_le` and `finiteAverage_deviation_gain_le`
(`UniformEquilibrium/Quitting/Examples/CrossedMatchingFixtureFiniteHorizon.lean`)
give the stronger fixture bounds `77/N` and `154/N` for every initial phase,
positive horizon and full behavioral replacement, with printed `154/N` and
`308/N` weakenings. One rational hazard vector supplies both phase-dependent
profiles, each retained before all accuracy quantifiers.
`affine_responseInvariant_injective_of_nonzero_scale`
(`UniformEquilibrium/Quitting/Examples/CrossedMatchingFixtureResponseQuotients.lean`)
excludes all nondiscrete maps into `Fin k` under arbitrary shifts and nonzero
signed scales, solely for actual response invariance. The canonical
pair-valued row-sum/displacement criterion and its normalized-ratio corollary
are in `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
`not_exact_stationaryNash_of_three_proper_support` and
`not_exact_stationaryNash_reindex_of_three_proper_support`
(`UniformEquilibrium/Quitting/Examples/CrossedMatchingFixtureStationary.lean`)
exclude actual stationary terminal Nash on proper three-player supports,
including relabelings. The payoff is actual, not a supplied continuation;
full-support stationary profiles are not excluded. Other source comparisons
still remain; these are not packet completion.

## Below-singleton joint-phase raw producer

`GameTheory.PairedCycle.BelowSingleton.exists_exact_terminal_and_fixedProfile_of_rawFamily`
(`UniformEquilibrium/Quitting/Cycles/BelowSingletonJointPhaseSource.lean`)
implements the raw rate producer, endpoint calculations and qualitative
equilibrium conclusions of `BELOW_SINGLETON_JOINT_PHASE_UNIFORM_EQUILIBRIUM`:
literal signed singleton and scheduled-pair identities, positive row scales,
the three common scalar inequalities and all twelve joining caps produce a
root in `(1/2,1)` internally. The canonical prescribed-interval cubic theorem
is reused by `Math.PairedBelowSingleton.exists_selected_root`
(`MathUE/PairedBelowSingletonScalar.lean`); no supplied root or Nash selection
is an input. Actual passive endpoint calculations feed
`GameTheory.PairedCycle.twoPair_exact_terminal_and_fixedProfile`
(`UniformEquilibrium/Quitting/Cycles/TwoPairExactCertificate.lean`). The result
identifies the original game's terminal vector, proves exact behavioral
terminal Nash and retains the same cyclic profile for every accuracy's
eventual horizon Nash and target delivery. Both phase values are strictly
below own singletons; their signs and all unmentioned rewards are unrestricted.

The literal fifteen-row table, selected survival `2/3`, phase vectors, active
endpoints `19/30`, passive Continue `19/20`, passive Quit `1/3` and gap `37/60`
are supplied by `active_endpoints`, `passive_continue_eq`, `passive_quit_eq`,
`passive_gap_eq` and `exact_terminal_and_fixedProfile`
(`UniformEquilibrium/Quitting/Examples/BelowSingletonJointPhaseFixture.lean`).
`oddsResponse_hasFDerivAt` and `oddsJacobian_det`
(`UniformEquilibrium/Quitting/Examples/BelowSingletonJointPhaseJacobian.lean`)
derive the actual four independent odds derivative and determinant
`267486337/26873856`, not an equal-odds or three-active proxy.
`exists_reward_supnorm_radius`
(`UniformEquilibrium/Quitting/Examples/BelowSingletonJointPhaseLocalPersistence.lean`)
produces a positive uniform radius in all sixty raw entries. The actual IFT
branch retains the strict passive Quit and both-phase singleton gaps; nearby
tables need no family equalities or supplied joining caps. The selected odds
give actual terminal values, exact terminal Nash, same-profile horizon
witnesses and UE for both initial phases, with no common horizon threshold
claimed across nearby tables.

`finiteAverage_delivery_le_timeConstant` and
`finiteAverage_deviation_gain_le_timeConstant`
(`UniformEquilibrium/Quitting/Cycles/BelowSingletonJointPhaseFiniteHorizon.lean`)
give the stronger all-initial delivery `M*C/N` and complete behavioral regret
`2*M*C/N`, where `C = 1 + 2/(1-t^3)` and `N > 0`. The packet's printed
`2*M*C/N` and `4*M*C/N` are thin weakenings, not optimality claims. The raw
producer selects its root before every reward-bound and horizon quantifier;
signed own rewards are allowed. Its clock source is actual live Cesaro mass;
the separately stated expected deleted-opponent exit-time bound remains separate.

`quietLift_gain_gt_weighted_childDebt_add_never_of_exact_child`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/PureAbsorbingChildDebtObstruction.lean`)
packages the shared semantic obstruction: actual exact child Nash gives zero
complete debts, actual joint Never zero kills any finite signed Never charge,
and an explicit positive outsider deviation exceeds every real weighted sum.
The literal all-fourteen-child profiles and table gains are not supplied by
this conditional helper.

Those literal outputs are supplied separately by
`exists_unsafe_witness_for_every_proper_child` and
`childQuietLift_quitNow_gain_eq`
(`UniformEquilibrium/Quitting/Examples/BelowSingletonJointPhaseChildren.lean`).
Canonical proper-coalition coverage proves the result for every nonempty
proper subset, not just four deletions. The two opposite-pair children have
gain `100`, all other selected witnesses gain `1/2`, and actual child Nash
and zero Never mass defeat every real weighted debt sum and finite signed
Never charge. Literal joining/withdrawal rows also defeat all nonnegative
weights, for arbitrary singleton fallbacks at most one on the child members;
omitted coordinates are unrestricted. These are existential unsafe witnesses,
not universal assertions about child equilibria.

The shared `finiteAverage_delivery_le_of_opponentLiveCesaro_bound` and
`finiteAverage_deviation_gain_le_of_exact_terminalNash_and_opponentLiveCesaro_bound`
(`UniformEquilibrium/Quitting/Cycles/PeriodicFiniteHorizonRate.lean`)
compose the actual clock budget with canonical delivery/deviation estimates.
The delivery theorem requires no Nash premise; the regret theorem uses exact
terminal Nash. This factor-two improvement over the printed constants applies
to signed rewards and every initial phase at positive horizons.

`twoPair_policy` and `twoPair_terminalPayoff_eq`
(`UniformEquilibrium/Quitting/Cycles/TwoPairExactCertificate.lean`) separate
policy and actual terminal realization from Nash: only passive Continue
identities are needed for these two consumers; passive Quit caps enter Nash.
This supplies the source-faithful invalid-root comparison rather than merely
rejecting an endpoint certificate. `not_terminalNash` and
`selected_exact_terminal_and_fixedProfile`
(`UniformEquilibrium/Quitting/Examples/BelowSingletonJointPhaseSecondRoot.lean`)
use the modified table with all twelve caps `13/15`. The internally selected
small root in `(0,1/20)` realizes `W`, while actual date-zero Quit delivers
`Q > 13/15 > W` against the same opponents. Both initial profiles fail
terminal Nash. The modified game's valid `2/3` root still supplies exact
terminal and fixed-profile horizon equilibrium; its passive gap is `13/540`.
No target non-UE conclusion is inferred from the bad profile.
`affine_responseInvariant_injective_of_nonzero_scale`
(`UniformEquilibrium/Quitting/Examples/BelowSingletonJointPhaseResponseQuotients.lean`)
covers every label type through canonical finite compression. Nonzero signed
scales and arbitrary shifts preserve this response-only exclusion. Actual
all-sure displacement is grand reward minus recipient-withdrawal reward,
by `quittingDiscountedDisplacement_one_eq_grand_sub_withdrawal`
(`UniformEquilibrium/Quitting/Root/FinFourEndpointRowSum.lean`), not minus
the own singleton. The two fixture facades reuse the same generic criterion.

The packet remains incomplete: separately stated expected-exit-time bound,
other raw-criterion, matrix and stationary separations remain
separate. The matching packet's
inverse and Brouwer route is distinct from this scalar IVT route; the
source-free `TwoPairOddsValues` identities and actual two-pair compiler are shared.

## Mixed-sign triple source boundary

`mixedSignTripleNash_hasFDerivAt_and_negative_det`
(`UniformEquilibrium/Quitting/Classification/MixedSignTripleCoreJacobian.lean`)
derives the actual full ambient derivative from the literal seven strict tests
and two equality constraints at a proper full-triple exact root, retaining
strict gaps for every inactive player. The canonical full endpoint expansion
also covers zero and sure hazards, and the sure classification derives the
allowed pure-pair alternative. The complete raw strict consumer is now
`exists_uniformEquilibriumPayoff_of_mixedSignTriple_core`
(`UniformEquilibrium/Quitting/Classification/Existence/MixedSignTripleCoreUniformPayoff.lean`):
actual pair/full-core branch assembly, derived Jacobians, internal census and
closed selected-return restoration discharge its source hypotheses. It splits
the pure-pair alternative from all real strict-deficit sources in the no-pure
branch; the final Fin4 consumer requires only nonnegative own singletons,
computed core equality and the raw strict comparisons/equalities.
`exists_uniformEquilibriumPayoff_of_weakMixedSignTriple_core`
(`UniformEquilibrium/Quitting/Classification/Existence/MixedSignTripleCoreRewardClosure.lean`)
supplies a fixed original-table target on the weak boundary. Exactly seven
passive entries change, preserving both equalities and all participant coordinates,
own-singleton payoffs, traps and core. Computed core cardinality three is retained in the
weak theorem to derive distinct labels; weak signs alone do not do so.
`not_isQuittingFullExactRootPotential_of_mixedSignTriple_core`
(`UniformEquilibrium/Quitting/Projective/MixedSignTripleCoreSmoothDrift.lean`)
supplies signed finite-table potential exclusion with continuity on the actual
boxed sublevel domain and differentiability only on its singleton lower
boundary. Its pure-set alternative uses
`not_isQuittingFullExactRootPotential_of_pureSetNash`
(`UniformEquilibrium/Quitting/Projective/PureSetExactRootPotentialExclusion.lean`),
which needs only that coalition's actual reward in the box, not a bound on
the whole table or analytic regularity. Packet fixtures and remaining
separations remain explicit obligations; the main criterion does not seal them.
The shared negative-bad-root obstruction and excluded-root dense restoration
live in `exists_exactRoot_singletonSublevel_of_dense_sources_excluding_root`
(`UniformEquilibrium/Quitting/Root/NegativeBadRootSelectedReturn.lean`); the
joining-attractive consumers remain thin same-scope instances. Excluding a
designated root does not assert that it is pure.

## Pending pivot and solo-refinement source dependencies

`rationalizedQuadraticRoot_spec` (`MathUE/RationalizedQuadraticBracketRoot.lean`)
is checked under positive bracket length, negative constant and positive
upper-endpoint value, without a sign condition on either higher coefficient.
It supplies a unique root inside that bracket, an explicit positive denominator
and discriminant, and a positive derivative at the selected root, not global
monotonicity or uniqueness among all positive roots. Its closed-interval
companion supplies continuity through zero endpoints under positive endpoint
linear coefficients and continuous polynomial coefficients, including the
zero-leading-coefficient case. This is a scalar producer, not a game pivot.

The queued `OPPOSITE_SIGN_MATCHING_PHASE_UNIFORM_EQUILIBRIUM` branch can reuse
`rationalizedQuadraticRoot_spec` with its positive leading coefficient,
literal linear coefficient and negative constant, and the packet's cap.
`continuousOn_rationalizedQuadraticRoot` in the same file permits pointwise
nonzero denominator without requiring the linear coefficient positive.
Bracket signs supply that denominator; no new quadratic-selection foundation
or Q/inverse argument is needed. The actual raw source adapter is not supplied here.

For the queued `NEGATIVE_PREMIUM_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM` packet,
the same bracket theorem applies with leading coefficient `-alpha`, linear
coefficient `beta`, constant `-gamma` and the printed pivot cap. On its
parameter half-open interval, bracket signs give denominator nonvanishing;
at the right endpoint the constant is zero and the linear coefficient is
positive. Use `continuousOn_rationalizedQuadraticRoot` and
`rationalizedQuadraticRoot_constant_zero`, not the closed-interval facade
that asks both endpoint constants to vanish. A subsequent scalar IVT and
actual K=3 game adapter remain to be implemented. The packet's large-parameter
child-only branch does not require a proper pivot, and its cyclic child
screen cannot be replaced by the pure-child obstruction above.

`selectedBalanceRoot_spec` and `selectedBalanceRoot_continuous_endpoints`
(`MathUE/CyclicChildJointPhaseAlgebra.lean`) produce the cyclic-child packet's
literal collision-adjusted scalar root and proper solo rates, continuously
through both zero endpoints. Positive cycle and harm parameters, nonpositive
collision rewards, nonnegative eta and positive cycle gap suffice. The actual
inverse supplies the literal positive balance vector; the denominator identity
and computed cap give the quadratic signs internally.
`selectedBalanceRoot_crossing_and_unique` in that owner exposes the actual
positive quadratic crossing and unique nonlinear balance root inside that cap.
No favorable root or inverse-weight certificate is supplied.

`MixedCycleSoloMesh.isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Cycles/MixedCycleUniformPayoff.lean`) is a checked
conditional compiler for literal mixed-cycle source data. It constructs actual
roots and phase values, refines only solo rows, and keeps every retained root
once with quiet padding. Arbitrary finite phase inventories, repeated owners,
nonzero singleton levels and empty solo phases are allowed. Only solo masses
must be proper; retained rows may have sure hazards. Policy and all-player
Continue equalities, singleton floors, retained Quit caps and playerwise
opponent contraction remain explicit source fields. The selected coarse
initial target stays exact at every scale and precedes accuracy; full behavioral
terminal caps use one error, not a period-amplified sum. The actual period is
the coarse phase count times the scale, including quiet slots.

`JointPhaseData.rootRatio_zero`, `JointPhaseData.secondRatio_zero`,
`JointPhaseData.thirdRatio_zero` and `JointPhaseData.exists_pivot`
(`MathUE/CyclicChildJointPhasePivot.lean`) produce the literal canceled
normalized ratios and continuous pivot selection from raw cyclic-child scalar
parameters. Both pivot endpoint values are exact; IVT selects the interior
hazard without a monotonicity assumption or a supplied selector.

`CyclicChildJointPhase.sourceCertificate` and
`CyclicChildJointPhase.exists_uniformPayoff`
(`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean`) now
derive every coarse source field from the five literal reward rows and six
retained outsider joining caps. All unspecified coalition rewards remain
arbitrary, including solo joining premiums. Policy and all-player Continue
identities use the original signed collision rewards. The participant
endpoints are equal; the outsider Quit expansion retains all four opponent
atoms. Singleton floors require positive xi, v below one and u at most one
plus xi, not a positive pivot numerator or R above one. Opponent contraction
comes from a genuinely different solo owner for each player, not its own
hazard. The internally selected proper cycle supplies one exact initial
target before refinement accuracy, and the canonical consumer caps every
behavioral replacement. The game-semantic result permits eta zero, extending
the packet's positive-eta premise without altering its other raw assumptions.

This cycle source covers R strictly between the literal pivot endpoints.
`exterior_positiveOffset_solution_iff` and `exteriorMatrix_det`
(`MathUE/CyclicChildComplementarity.lean`) now classify every regular-offset
root and prove the exact determinant for an arbitrary exterior row. Positive
offset child activation and homogeneous propagation need no coefficient sign
assumption; canonical inverse identification uses only a nonzero child gap.
`exists_uniformPayoff_of_resonance`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildSingletonAdapter.lean`)
internally constructs the homogeneous witness from literal raw singleton rows
and gives actual Fin4 UE at the lower endpoint. The thin original-table facade
of the same name (`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSingletonExits.lean`)
supplies those rows itself. `exists_uniformPayoff_of_passiveThreshold`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildPassiveInverseExit.lean`)
internally transports the actual deleted-child inverse and outside-row weights
and supplies UE from the three literal passive numerator tests, including
equality. Its two-threshold specialization uses v below one; harm parameters
are unrestricted for this exit. `exists_uniformPayoff_of_passiveExit` in the
original-table facade supplies the literal packet threshold. Off-endpoint R0
is checked; the packet's explicit finite-law and quantitative constants and
stress fixtures remain separate.
`exterior_r0Degree_eq_zero` (`MathUE/CyclicChildExteriorDegree.lean`) now
computes the low exterior degree from the canonical complete two-root census:
the first inactive residual is one, and the active determinants have opposite
signs. `exists_uniformPayoff_of_below_resonance`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildLowDegreeExit.lean`)
transports that result from literal singleton rows to an actual original-game
uniform payoff, without a supplied R0, degree, root set or child strategy.
`exists_uniformPayoff_all_pivots`
(`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSingletonExits.lean`)
combines low, resonance, high and actual interior producers for every real R.
Both literal threshold comparisons are checked; u may exceed one, subject only
to u at most one plus xi. Eta may be zero. This closes the packet's main raw
UE class, not its remaining prescribed calendar/law constants or stress tests.
The same raw singleton low, resonance and passive exits supply outer branches
for the global two-joint and zero-premium packets. Their different joint rows,
caps and internally constructed selectors remain separate actual source units;
the one-joint all-pivot facade is not a theorem for those classes.
The shared padded compiler uses the actual three-times-scale period, not the
packet's minimal one-plus-twice-scale period.
The global two-joint packet also requires weakening the shared refinement
floor contract to the two endpoints of each refined solo row. A retained joint
row uses its literal Quit cap and exact Continue equality, not an all-player
singleton floor; the supplied source can fail such a floor there. The current
all-phase floor interface is not silently a producer for that packet.
The two-outsider-buffer packet requires a separate monotone rational selector
and its small-parameter ratios; the quadratic formula covers only its empty
repeated-phase specialization, not the whole source. Positive joint outsider
caps must be bounded by the current continuation, not by zero or a singleton.
In the repeated-solo packet the
outsider cap is paid by a positive continuation buffer, not cancellation by
negative collision rewards. These remaining game-facing source units are
queued, not checked or
supplied by the common-leaver results above.

## Proof-mining connections not yet formalized

These are proposed follow-ups, not new checked conclusions or packet seals.

- The ambient homotopy and R0 margin APIs should give degree constancy along
  any continuous path of R0 matrices and local constancy on the whole R0
  locus. No zero-diagonal, strict-support, or nonsingular-principal-minor
  restriction is needed for that degree claim. Exact support inventories
  still retain their own stronger hypotheses.
- Compact target selection can retain cofinal actual-family indices and
  arbitrary eventual constraints, rather than discarding them at the final
  existential selection. This would preserve independently shrinking hazard
  caps at one fixed target. Finite quiet-law conversion also needs the actual
  cyclic certificate and contraction data, not just a small-hazard existence
  statement. No uniform weak-boundary calendar bound follows.
- The paired quotient class can be enlarged to a relative-open class of
  response-invariant centered tables with nearby quotient matrices, instead
  of fixing its singleton matrix exactly. This is relative openness within
  the centered response-invariant class, not openness under arbitrary
  symmetry-breaking perturbations.
- Immediate opponent screening should strengthen same-profile uniformization
  to exact Nash at every finite horizon, without singleton-sign assumptions.
  The proposed source condition is zero stationary all-Continue mass for
  every player's deleted opponents, as supplied by at least two sure quitters.
  Every unilateral response then absorbs at date zero, so prescribed payoff
  and full cap should scale by the evaluation's date-zero weight. Reuse
  `quittingBehaviorEvaluatedDeviationPayoffCap_eq_pureTime`
  (`UniformEquilibrium/Quitting/Paths/EvaluatedPureTimeCap.lean`) and the actual
  finite-stage identity. This is not proved here and does not apply to a
  single negative sure owner whose Never response removes the screening.
- `lcpResidual_quittingBlockLift_zero`
  (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientHomogeneous.lean`)
  should extend to block-constant offsets. The corresponding feasibility iff
  concerns lifted points only; it would not identify all full-game LCP
  solutions with quotient solutions or equate full and quotient degrees.
- Public bounded-evaluation payoff and cap bounds need only an evaluation
  between zero and one, as the pure-time envelope already proves. The older
  antitone bounds retain the sharper date-zero factor and should not be
  weakened. Equality of actual stopping-law tuples transports evaluated
  payoffs and caps; terminal semantic-pair equality alone does not record
  dates and cannot justify that transport.

Further source-based mining identifies these small adapters, none implemented
by the mining pass:

- `QuittingThreePlayerStrategyClass.of_card_le_three`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazardAllSigns.lean`)
  and the raw quiet-lift debt bounds should retain a parent stationary-or-small-hazard
  strategy alternative, with an independent requested hazard budget. Deleted
  players remain literal Always Continue. The stationary alternative need not
  have small hazards, and fixed-target selection retaining that budget is a
  separate refinement.
- `exists_rational_minPrimalOptimal`
  (`MathUE/LinearProgramming/RationalOptimization.lean`) can optimize the
  certificate's amplification, not just find feasible rational weights.
  Patient amplification uses the sum of both response weights; deadline
  amplification uses their pointwise maximum, represented by epigraph
  variables. A feasible raw system and factor at least one give feasibility
  and the objective lower bound. Exact rational primal and dual optimizers
  would certify optimality, not provide an executable solver or certify an
  arbitrary game.
- `quittingResponseInvariantOnUnitCube_iff_finite_coefficients`
  (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientPolynomial.lean`)
  can expose response invariance as the kernel of one finite linear map of
  reward coordinates, hence a closed linear subspace. The centered permutation
  identity already needs only one recipient's additive row offset; a
  subgroup-orbit adapter need not expand the coalition sums again.
- `exists_quittingQuotientResponse_ambient_quadratic_bound`
  (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientAmbientEstimates.lean`)
  can drop its response-invariance and representative hypotheses by applying
  the analytic remainder theorem to the already general quotient derivative.
  Strategic decoding still needs response invariance; this is only an
  analytic API strengthening.
- `halfCeilingValue_weighted_strictly_above_singleton`
  (`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponsePayoffExclusions.lean`)
  holds for every nonzero nonnegative weight at one same actual Nash payoff.
  It therefore also defeats profile-dependent normalized exclusion weights.
  The existing raw-calendar/actual-payoff equivalence should give the
  corresponding raw exclusion counterexamples without new payoff calculations.
  That exact equivalence preserves payoff only, not full caps; approximate
  equilibrium calendars instead use the existing full-profile approximation.

Further cross-branch reuse opportunities remain unimplemented joins:

- `exists_uniformEquilibriumPayoff_of_finFour_rawSignFreeWeakSubsetExclusion`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourSignFreeWeakSubsetUniformPayoff.lean`)
  can feed `rationalQuittingFiniteWordSearchOfUniformPayoff_finiteLaws`
  (`UniformEquilibrium/Quitting/Root/RationalFiniteWordSearch.lean`) for rational
  Fin4 tables. This gives a route from sign-free exclusion to terminating
  full-cap strategy search. It does not remove the designated-owner signs
  from the quantitative dyadic algorithm, prove exact terminal Nash, or
  compute a fixed uniform target.
- `quittingStrictDeficitExactSuffix_finitePureTime_le`
  (`UniformEquilibrium/Quitting/Paths/StrictDeficitExactSuffixNash.lean`) already
  bounds every finite reply on the signed source diagonal. The canonical
  `quittingCompactStoppingLawProfile_cap_le_finiteBound_add_opponentNeverProduct_mul_negPart`
  (`UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`)
  identifies the remaining full-cap correction as opponent Never mass times
  the negative part of the player's singleton. An actual-source adapter can
  retain the same diagonal and expose that correction. Joint absorption does
  not make it vanish; exact suffix Nash requires its actual vanishing.
- The exact finite-calendar payoff image and the existing algebraic-witness
  theorem can give algebraic marginal atoms realizing an attainable rational
  payoff of a rational table, with Never included. This is a payoff-only
  existence adapter, not cap preservation, rational-atom realization or an
  executable real-root encoder.

The whole-R0 degree proposal can use `r0Margin_pos_iff_isR0Matrix`
(`MathUE/LinearProgramming/R0Margin.lean`), the intrinsic origin-degree bridge,
and `ambientDegree_homotopy`
(`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`). It need not retain
the strict principal-support inventory used by existing stronger neighborhood
theorems. The cofinal selection proposal can expose the strict subsequence
already constructed by terminal target selection, requiring an actual selected
index beyond any requested bound. No common target across different games or
uniform weak-boundary calendar complexity follows from these proposals.

The crossed packet's algebraic source and accuracy-only rational search are
checked. The first encodes the literal bounded nonzero fixed-point conditions
and uses the original-game endpoint consumer, permitting nonisolated roots.
The second retains all-deleted-clock contraction and evaluates the actual
stationary payoff and complete behavioral cap, including zero and sure hazard
faces. It is not the one-stage grid selector against a supplied tail.
Neither supplies a practical complexity bound or a prescribed-target oracle.

## Reusable serialization result beyond the literal paper instance

`isAsymptoticNash_quittingSerializedRoots`
(`UniformEquilibrium/Quitting/Root/SequentialSerializationEquilibrium.lean`)
applies to every bounded Fin4 reward table with unit own singleton payoffs.
The actual source equilibrium error and hazard bound are independent:
the four-substage profile has error at most `error + 32 * M * hazardBound`.
The comparison includes Never and all behavioral deviations and does not
assume certain absorption. It requires an actual small-hazard source;
it neither constructs that source nor replaces an arbitrary multi-owner
calendar by an exact single-owner equilibrium. The literal Solan--Vieille
Lemma 9 follows without unfinished imported proofs, as confirmed by its
separate axiom check.

## Source-complete dependency follow-ups

The patient terminal converse and attained-floor witnesses now pass targeted
checks. They use shared deterministic response-gain witnesses, rather than a
second unrestricted-cap proof. The old deadline necessity interface delegates
to the same witnesses and its refactor passes its targeted check.
The evaluated cancellation operation, actual product marginal and full-debt
consumer use their own literal raw rows and zero-based floor, not the positive
patient Never alternative.

The fixed-target lifting compiler now exposes actual lifted profiles through
terminal target selection and uniformization. At every positive accuracy,
the selected uniform profile itself is a quiet lift of a child profile, for
all sufficiently long horizons and one fixed agreeing parent target. The four
reward-certificate families and their Fin4 consumers instantiate this constraint.
The generic construction is
`exists_uniformPayoffWitnesses_eq_on_image_of_terminalNash_lift`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalNashLift.lean`),
with old payoff-existence statements obtained by projection, not a second
uniformization proof.

The Never charge, full-cap finite-calendar approximation, and exact rational
finite-word payoff/cap evaluator already exist. Reuse
`prod_stoppingLaw_none_mul_singleton_le_terminalDebt`
(`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`) and
`rationalQuittingFiniteWordSemanticPair`
(`UniformEquilibrium/Quitting/Root/RationalFiniteWordSemantics.lean`).
Rational density, law-to-hazard encoding and exhaustive finite-word termination
retain the selected child word in the parent Never lift. Executable source K
is computed before accuracy from the actual rational coefficients; it is not
extracted from a selected real certificate or favorable strategic cap.

For the crossed-response total-degree identity, complementary-region
additivity and excision are already available in `MathUE/Topology/`.
`exists_globalCrossed_localDegree_eq_r0Degree`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseEscape.lean`)
now delegates to the same-radius closed-ball isolation and local-degree
bundle; its complement is identified with the entire nonzero fixed-point set.
The intrinsic ambient construction and its chart-comparison adapter are also
checked in `MathUE/Topology/AmbientDegree.lean`. This supplies the ambient
interpretation of the fixed-chart invariant; it does not assert uniqueness
against an independently implemented degree operation.

Solan--Vieille's exact paper-order Lemma 10 is checked.
`singletonReward_le_nashError_div_never`
(`UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumVanishingNeverAlternative.lean`)
already supplies its exact Never-mass estimate. The other two assertions
use zero collision, exact boundary payoff identities, and singleton mass sums
in `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryPerturbedEstimates.lean`.
The literal `lemma12` and `corollary13`
(`Literature/future/SolanAndVieille2002a.lean`) pass their targeted build and
separate axiom check, with the paper's domain and constants.
`of_normalizedThreePlayer`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazard.lean`)
constructs the stationary-or-small-hazard strategy alternative for three
players with unit own singleton payoffs. Positive scaling and arbitrary
player-type transports are checked in
`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazardTransport.lean`:
these scoped transports retain their sign hypotheses. The unrestricted
`QuittingThreePlayerStrategyClass.of_card_le_three`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazardAllSigns.lean`)
now passes its named check and assembles the remaining signed three-player
cases from the stationary LCP gate and full normal-core directed-cycle
classification. The literal Literature `proposition1` and its separate
standard-axiom check pass. This retains actual stationary roots or actual
uniformly small-hazard sequences, not merely small-player UE existence.

## Shared stationary-witness follow-up

`exists_uniformPayoff_stationaryTargetAcceptance_of_terminalApproximations`
(`UniformEquilibrium/Quitting/Stationary/StationaryTerminalPayoffSelection.lean`)
already constructs contracting stationary terminal approximants at one fixed
target.
`exists_uniformPayoff_stationaryWitnesses_of_terminalApproximations`
(`UniformEquilibrium/Quitting/Stationary/StationaryUniformPayoffWitnessSelection.lean`)
now retains members of that same family as terminal and uniform finite-horizon
witnesses. Both weak-boundary adapters pass their targeted checks in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakBoundaryWitnesses.lean`.
The target is fixed before the accuracy; at each accuracy the same contracting
stationary root supplies both conclusions. This does not assert a common
contraction rate or exact stationary equilibrium attainment.

## Complete-claim audit: stationary-response quotient packet

Every useful claim in the frozen export has a production owner passing its
targeted compiler check. The raw absorbing Bellman-root producer, signed Fin4
UE consequence, paired centered-row class, and paired/full matrix degree
calculations retain their stated hypotheses. Entire-nonzero-set normalized
and intrinsic ambient degree do not assume isolated or finitely many roots.
Normal completion retains the same produced Bellman value; normality is
needed only for negative singleton-block owners. The full silent default build,
exhaustive production axiom audit, repository script gates and executable
experiment checks pass. The packet is retired unchanged to `math/formalized/`.

| Source claim | Checked coverage |
| --- | --- |
| Section 1, raw response identity | `quittingResponseInvariantOnUnitCube_iff_forall_ambient` (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientAmbientIdentity.lean`) and `quittingResponseInvariantOnUnitCube_iff_finite_coefficients` (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientPolynomial.lean`) pass named checks. The latter uses reward-independent finite monomial sets and coefficients linear in actual reward entries, retaining arbitrary finite players and zero block dimension. No executable arbitrary-real decision is asserted. |
| Sections 3 and 4.2--4.4 | Whole-signed ambient quadratic remainder, literal total-box degree one, origin coordinate-box degree kappa, and entire-nonzero annulus degree one minus kappa pass named checks in `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientAmbientEstimates.lean` and `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientAmbientDegree.lean`. Zero dimension and nonisolated roots are retained. The paired literal entire-fiber degree-two specialization passes its targeted check in `UniformEquilibrium/Quitting/Examples/BlockPair/PairedResponseQuotientAnnulus.lean`; it is not a root-count theorem. |
| Theorem B, sign and no-singleton-block branches | `terminalNash_and_sameProfileUniform_of_nonzero_quotientFixedPoint_singletonSign` (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientSameProfile.lean`) passes its targeted check for every actual nonzero quotient root. Its existence and no-singleton-block consumers retain the produced root, actual payoff, exact terminal Nash and same-profile long-horizon witnesses. |
| Theorem B, normality branch | Matched by the targeted-checked singleton-normality completion, retaining the actual root payoff as fixed target. Normality is needed only for negative singleton-block owners. |
| Optional sole-owner exclusion | `boundary_and_sameProfileUniform_of_nonzero_quotientFixedPoint_soloQuitterInfeasibility` (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientSoloQuitterInfeasibility.lean`) passes its targeted check. It reuses the canonical opponents-only joining inequalities for every negative singleton-block owner and every hazard in `(0,1]`, deriving the Never boundary internally. |
| Sections 1 and 6, counterexample consequences | `finFour_responseQuotient_r0Degree_eq_one_of_no_uniformPayoff` and `finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse` (`UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`) pass the silent named check. Homogeneous complementarity is transported by the actual block lift, and full singleton R0 is supplied by the same no-UE assumption. The raw inverse criterion needs no input R0 and permits zero inverse entries. |
| Section 6, symmetry | `responseInvariant_of_reward_subgroup_automorphisms` (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientPlayerOrbits.lean`) and the same-table no-UE consumers in `UniformEquilibrium/Diagnostics/Quitting/FinFourOrbitResponseQuotientCriterion.lean` pass targeted checks for every subgroup of full reward-table automorphisms. |
| Section 2, paired class | `isPairedCenteredCompletion_iff_exists_coordinates` and `pairedCompletionReward_injective` (`UniformEquilibrium/Quitting/Examples/BlockPair/PairedResponseQuotientCoordinates.lean`) give an exact chart with 33 free nonsingleton coordinates and four signed own-singleton levels, reconstruction, literal coordinate counts and a UE consumer for every input. The paired source and ambient owners give the sign-only same-profile stationary corollary, unique offset-minus-one LCP solution and literal degree two. `pairedAsymmetricCompletionReward_properties` (`UniformEquilibrium/Quitting/Examples/BlockPair/PairedResponseQuotientAsymmetry.lean`) changes one nonsingleton entry, preserving the class and singleton data while destroying full swap covariance. |
| Section 5, quantitative evaluation | `abs_finiteAveragePayoff_sub_terminal_le_opponentLiveCesaro` (`UniformEquilibrium/Quitting/Cycles/PeriodicFiniteHorizonRate.lean`) and the stationary facade retain every complete update with signed playerwise error M/[H(1-alpha)] and regret 2M/[H(1-alpha)]. `abs_discountedPayoff_update_stationary_sub_terminal_le_opponentGap` (`UniformEquilibrium/Quitting/Stationary/DiscountedRate.lean`) gives normalized discounted error M(1-d)/(1-alpha), including d=0. `discountedPayoff_update_solo_owner_le_add_one_bound_error` (`UniformEquilibrium/Quitting/Stationary/SoloDiscountedRate.lean`) retains the separate one-M nonnegative owner bound using joint hazard, not an unavailable owner-deleted contraction. `exists_soloPunishmentPrefix_estimates_of_punishmentIR` (`UniformEquilibrium/Quitting/Punishment/SoloPunishmentPrefix.lean`) internally chooses one actual punishment row before every prefix length K, with delivery 2M rho, owner cap v+error, outsider cap v+2M rho, owner debt error+2M rho and outsider debt 4M rho, where rho=(1-h)^K. Its nonnegative-owner facade derives the signed IR premise; the existing solo completion remains the fixed-target UE consumer. |
| Section 7, literal algebraic fixture | `PairedCubicStationaryExample.root_sameProfileUniform` (`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicStationaryExample.lean`), the actual three-variable Jacobian in `UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicActiveJacobian.lean`, and `PairedCubicStationaryExample.exists_local_stationary_branch` (`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`) pass named checks. They retain all fifteen reward rows, algebraic root brackets, complete behavioral caps, the strict inactive sign and an internally produced open branch over all sixty raw reward coordinates. Its target is fixed before accuracy for each table; no numerical radius, common target across tables or branch uniqueness is asserted. |
| Section 7, fixture consequences | `PairedCubicStationaryExample.not_exact_terminalNash_pureTime` and its canonical and normalized variants (`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicDeterministicObstruction.lean`) cover every deterministic first-quit clock, including arbitrary later dates and Never, from literal profitable membership toggles. `PairedCubicStationaryExample.canonicalReward_not_swapCovariant` and `normalizedReward_singleton` (`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicRewardClasses.lean`) retain the actual canonical and normalized reward tables; the stationary root/cap transport uses the canonical recipient shift and positive scaling, not arbitrary-profile translation invariance. |
| Section 8, boundary tests | `NegativeSoloStationaryBoundary.exploitability_positive`, `exploitability_boundary`, `punishmentValue_one`, and `soloCriterion_iff` (`UniformEquilibrium/Quitting/Examples/NegativeSoloStationaryBoundary.lean`) pass their targeted check with canonical full exploitability. `PairedAdditiveStationaryBoundary.upperFaceRoot_terminalNash_sameProfileUniform` and `upperFaceRoot_completeCap_eq_payoff` (`UniformEquilibrium/Quitting/Examples/BlockPair/PairedAdditiveStationaryBoundary.lean`) cover both entire upper faces, including proper-support endpoints; singular/R0 matrices, an infinite fiber and its entire-set degree are checked. `Math.LinearProgramming.SwapTwoNonnegativeInverse.not_isR0Matrix` (`MathUE/LinearProgramming/Examples/SwapTwoNonnegativeInverse.lean`) accompanies the nonnegative inverse and unique inhomogeneous solution. |

The ambient source adapters reuse the shared intrinsic construction and
its chart comparison; they do not prove uniqueness against an independently
implemented Brouwer degree. Canonical R0 bounds, local indices, degree sums
and stationary complete-response caps remain the owners for later consumers.
Source-correspondence prose and nonclaims require no extra theorem.
Arbitrary refinement of a response-invariant partition is not asserted by the
packet; a general block-splitting theorem is not a retirement requirement.

## Potential packets: checked dependencies and remaining obligations

The common exact-root restriction, collision-adjusted probes, unit face drift,
minimum localization and matrix-free quasiconvex exclusion pass the full
integration gate.
The actual textbook-Q analytic branch, quantitative mixed-curvature account,
negative-Hessian bound and their generic owners pass silent named checks.
Their full integration gate passes. Adaptive reflection, quadratic
and multi-affine exclusions, the directional third-derivative bound and the
same-polynomial characterization also pass named and separate standard-axiom
checks. Weakly monotone or antitone C¹-transform transfer also passes its named
dependency check, separate standard-axiom check and full integration gate.
Flat outer-function pieces are allowed on the whole inner image.
The two potential packets also have additional obligations.
These are formalization dependencies of their supplied proofs, not new
mathematical conjectures.

1. Strengthen unit face drift using actual perturbed robust successors.
   The derivative's coordinate absolute-value sum must occur in the resulting
   inequality. Keep the same source, exact root, absorption and boxed target;
   unit exact-root drift alone does not provide this term. The actual adapter
   in `UniformEquilibrium/Quitting/Projective/RobustPotentialSingletonFaceDrift.lean`
   passes its silent named check.
2. Derive face-only additive and scalar-composition exclusion. The latter
   cannot assume global monotonicity: its derivative sign on the lower-boundary
   image must follow from the actual positive face drift and connectedness.
   Equality on a closed box also requires boundary derivative identification.
   The generic exclusions and actual translated-potential adapter pass silent
   named checks. The actual representation exclusions require only a
   nonnegative simplex with nonnegative matrix image, not standard Q.
   The same-polynomial quantitative characterization also passes its silent
   named check, retaining one expression and tolerance for all added
   nonseparability and curvature conclusions. Their separate transitive axiom
   checks use only the three permitted standard axioms, and the full
   integration gate passes.
3. Produce the simplex witness from the actual textbook-Q problem and join
   the Fin4 no-UE normal-core, reindexing and normalized-matrix owners. A
   supplied favorable simplex point is not the producer.
   The strategic prerequisites already exist:
   `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`
   (`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`)
   supplies standard Q on the normal core, and
   `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
   (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`)
   identifies that core with all four players. The literal matrix transport
   and Q-predicate bridges are assembled in the checked producer below.
   Normalizing an actual standard LCP solution at right-hand side minus one
   yields a simplex vector with strictly positive matrix image. It does not
   yield homogeneous complementarity; `SingletonLCPFeasible` is a different
   predicate and is excluded on the no-UE branch.
   `isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`
   (`UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`) and its
   internally produced strict-image simplex pass the silent named check.
   The same-witness nonseparability and quantitative polynomial joins also
   pass their named, separate standard-axiom and full integration checks.
4. Prove the signed mixed-curvature account at every minimum on the singleton
   rectangle, using the fundamental theorem along actual reset segments.
   Compactness must supply the attained mixed-partial maximum and quantitative
   bound. The actual adapter in
   `UniformEquilibrium/Quitting/Projective/RobustPotentialMixedCurvature.lean`
   passes its silent named check. A supplied curvature bound cannot replace
   this calculation.
5. Prove the negative Hessian eigenvalue bound from actual Hessian symmetry,
   its spectral interpretation and quadratic convexification. The final
   face-only contradiction uses the textbook-Q analytic branch, not the
   matrix-free full-root exclusion.
   The checked generic and actual declarations supply the actual Riesz Hessian,
   genuine least eigenvalue, internally attained box-times-sphere minimum,
   box-only quadratic convexification, and the stated negative-eigenvalue
   bound for the same potential and tolerance.
   `quittingRobustPotential_finFour_negativeHessianEigenvalue`
   (`UniformEquilibrium/Quitting/Projective/RobustPotentialNegativeHessian.lean`)
   passes its silent named check and obtains ambient Q from bare no-UE.
   The quantitative polynomial characterization now applies this result to
   the same expression and tolerance produced by the original characterization.
6. `exists_rational_exact_solo_rejection_of_standardQ_quasiconvex`
   (`UniformEquilibrium/Quitting/Projective/RationalExactSoloRejection.lean`)
   passes its silent named check. Closed-face rational approximation and the
   collision-adjusted probe retain exact source Nash, the literal successor,
   positive absorption and the strict three-quarter drop bound. Exhaustive axiom
   and full silent integration checks pass. The five shape fixture owners also
   pass those checks, completing the shape packet's mathematical content.
   A general approximate Nash selector does not supply this witness.
7. The reflection packet's rational approximate robust rejection and exhaustive
   finite-budget search are proved and integrated. Their silent named checks,
   returned-pair consumer, separate standard-axiom checks and full build pass.
   `exists_rational_robust_rejection_of_excluded_polynomial`
   (`UniformEquilibrium/Quitting/Projective/ExcludedPolynomialRationalRejection.lean`)
   internally selects one rational source/root pair satisfying every player's
   strict absorption-relative regret bound. The executable search accepts
   non-strict regret bounds. Its
   `rationalQuittingPotentialRejectionSearch_sound`
   (`UniformEquilibrium/Quitting/Projective/RationalPotentialRejectionSearch.lean`)
   retains the actual returned pair's probabilities, literal source and exact
   successor. Eventual success is proved for every supplied positive rational
   tolerance. Neither theorem asserts rational exact Nash or an effective cutoff.
   The paired-example and midpoint-integral joins pass their silent named checks,
   full silent default build and exhaustive production axiom audit.
   `pairedFacePotential_boundedCompletion_not_fullRoot`
   (`UniformEquilibrium/Quitting/Examples/PairedFacePotentialBoundedCompletion.lean`)
   retains every unit-bounded nonsingleton completion. The same polynomial's
   actual canonical Hessian and internally selected non-top minimizing vertex
   are proved in `MathUE/Analysis/Examples/PairedFacePotentialGeometry.lean`.
   `midpoint_thirdDerivative_integral_identity`
   (`MathUE/Analysis/MidpointThirdDerivativeIntegral.lean`) supplies the literal
   integral identity, the two half-interval formulas, and exact weighted kernel
   mass.
8. Join the exclusions to the original existential polynomial characterization
   for the same internally selected expression and tolerance. The reflection
   packet needs full exact-root drift on box three; the smaller-box adapter
   only yields box two and is insufficient for its reflection argument.
   `quittingGame_noUniformPayoff_iff_noSureRoot_and_restricted_rationalPotential`
   (`UniformEquilibrium/Quitting/Projective/RestrictedPolynomialForwardCharacterization.lean`)
   passes its silent named and separate standard-axiom checks. In the bounded
   nonnegative-singleton class with one positive singleton, the original
   producer supplies one expression and tolerance. The same expression has
   degree at least three and is not multi-affine; at each global minimum one
   common boundary minimizer and direction give reflection and a directional
   third derivative at least three times the gap. No minimum interiority or
   fixed Hessian sign is assumed. The shape packet's nonseparability and
   quantitative curvature joins pass named and separate standard-axiom checks
   on the same once-selected expression and tolerance. The reflection packet's
   decision-preserving signed normalization also passes its silent named check.
9. Preserve no-UE through literal common positive reward scaling, produce the
   bound-one table from the existing single-pivot normalization, and apply
   the characterization afresh. Reuse the checked general stochastic-game
   affine-payoff transport rather than repeat its behavioral UE proof.
   Common scaling includes the live state and preserves zero Never payoff.
   The actual pivot and integer divisor must be produced from arbitrary real
   source rewards; a rational scale does not make those rewards rational.
   The resulting counterexample-existence equivalence is existential over
   tables, not a per-table UE equivalence for terminal-only translation.
   `exists_finFourBoundedSinglePivotPolynomialObstruction_of_no_uniformPayoff`
   (`UniformEquilibrium/Diagnostics/Quitting/FinFourBoundedSinglePivotPolynomialObstruction.lean`)
   now produces all these objects internally; its converse and existential
   decision equivalence are proved for the same literal certified table.
   Its expanded source-facing consumer, full silent default build and exhaustive
   production axiom audit also pass.

The coupled-cubic shape example, midpoint integral identity and charge-coefficient
rescaling have explicit checked coverage. Reflection boundary fixtures are also
implemented. The complete-claim review matches all source results, including
strict rise/fall and radial reversal on the same segment without C³, and the
same-segment directional third-derivative conclusion with C³. The paired
polynomial's nonquasiconvexity on the singleton box is stated explicitly.
The complete-claim source audit also covers every numbered result and fixture,
not just the headline exclusions. In particular,
`quittingRobustPotentialWithCharge_mixedCurvature`
(`UniformEquilibrium/Quitting/Projective/RobustPotentialChargeScale.lean`)
retains arbitrary finite player types and signed singleton data; the Fin4
facade is not the only coverage. Exact rational solo rejection is distinct
from positive-tolerance approximate robust rejection and its exhaustive search.
The same-polynomial restrictions and decision-preserving fresh-polynomial
normalization retain their separate source scopes. All mapped production
owners are imported by the exhaustive axiom audit and pass the full build.
The exports' presence remains an independently managed mathematical lifecycle
fact, not an unfinished formalizer claim; no export was moved by this audit.

## Complete-claim audit: reflection potential packet

The packet remains in the independently managed `math/exports/` folder.
Its mathematical claims are matched to the following production declarations.
The full silent default build and exhaustive production axiom audit pass;
the source selector for the nonnegative-singleton packet passes the same gate.

| Source claim | Lean coverage |
| --- | --- |
| Quadratic and multi-affine exclusions | `not_isQuittingFullExactRootPotential_totalDegree_le_two` (`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialQuadraticExclusion.lean`) and `not_isQuittingFullExactRootPotential_multiAffine` (`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMultiAffineExclusion.lean`) retain real coefficients and the full exact-root relation. |
| Every minimum's reflection and rise/fall | `IsQuittingFullExactRootPotential.exists_rise_and_fall` (`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialReflection.lean`) retains the quantitative gap, adaptive boundary minimum, negative slope, boxed reflection and segment, and strict interior peak on that same direction. |
| C³ directional bound and exact integral | `IsQuittingFullExactRootPotential.directionalThirdDerivative` (`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialThirdDerivative.lean`) retains the same reflected direction and peak; `midpoint_thirdDerivative_integral_identity` (`MathUE/Analysis/MidpointThirdDerivativeIntegral.lean`) gives the literal identity and kernel mass. |
| Weak monotone scalar transforms | `not_isQuittingFullExactRootPotential_monotone_polynomial_transform` (`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMonotoneTransformExclusion.lean`) covers flat pieces and both monotonicity directions. |
| Rational approximate rejection and exhaustive search | `exists_rational_robust_rejection_of_excluded_polynomial` (`UniformEquilibrium/Quitting/Projective/ExcludedPolynomialRationalRejection.lean`) and the soundness/eventual-success theorems in `UniformEquilibrium/Quitting/Projective/RationalPotentialRejectionSearch.lean` retain the supplied tolerance, exact successor and actual returned pair. |
| Same-polynomial semantic equivalence | `quittingGame_noUniformPayoff_iff_noSureRoot_and_restricted_rationalPotential` (`UniformEquilibrium/Quitting/Projective/RestrictedPolynomialForwardCharacterization.lean`) retains one produced expression and tolerance, canceled degree, non-multi-affinity, and all minimum conditions. |
| Actual decision-preserving normalization | `exists_finFour_no_uniformPayoff_iff_exists_boundedSinglePivotPolynomialObstruction` (`UniformEquilibrium/Diagnostics/Quitting/FinFourBoundedSinglePivotPolynomialObstruction.lean`) internally produces the pivot, integer divisor, scaled table and fresh certificate from arbitrary real no-UE rewards. |
| Boundary groups | `CollisionAdjustedProbeBoundary.lean`, `ReflectionBoundaryArithmetic.lean`, `ConstantSignedNormalTable.lean`, the paired potential geometry/completion owners, and `FullExactRootPotentialChargeScale.lean` cover the collision, adaptive cap, sign, normality, face-only and charge boundaries. Their full paths are listed in the toolkit. |

These are restrictions on possible potential certificates, not an additional
solved-game class or a resolution of the surviving polynomial alternative.

## Complete-claim audit: passive-row cycle packet

This is static declaration matching, not additional compiler evidence.
The raw strict/weak inverse class, arbitrary-child nonnegative row inheritance,
strict cyclic labeling, degree-one fixture and its full open reward
neighborhood are matched. All strategy, calendar, comparison, falsifier
and ambient-degree conclusions pass their targeted and full silent checks.
The complete packet is retired unchanged to `math/formalized/`.

| Source claim | Remaining obligation |
| --- | --- |
| Theorem 1, quiet strategies | Matched by `exists_quietFiniteTimingUniformWitnesses_of_raw_nonnegativeInverse_triple` (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/WeakInversePassiveRowQuietWitnesses.lean`): one original-game target, actual finite timing laws, and every outside player at Never and Always Continue at every history. |
| Strict target and Proof Sections 2-3 | Matched by `exists_labeledCycle_uniformPayoff_of_strictInverse_passiveRows` (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/StrictInversePassiveRowCycle.lean`), its raw counterpart, and `rightPassiveCoarse_floor_iff` (`UniformEquilibrium/Quitting/Classification/ThreePlayer/CyclicPassiveCoarseFloors.lean`). Label, actual rates, certificate and phase-zero target remain correlated; the outside-floor iff permits arbitrary signed weights. |
| Proof Section 4 | Variable phase subdivision, exact survival products and conditional values, owner equality and full behavioral cap pass targeted checks in `UniformEquilibrium/Quitting/Cycles/RationalSingletonCalendar.lean`. Its hazards are rational functions of the coarse hazards, not necessarily rational numbers for arbitrary real coarse input. |
| Proof Section 5 | Exact censor payoff factor, full-cap/debt estimates including Never, and the date-count bound are checked in `UniformEquilibrium/Quitting/Cycles/RationalSingletonFiniteCalendar.lean`. Exact rational clock masses and the executable calendar-to-law adapter are checked. `exists_rationalClocks_of_raw_strictInverse_triple` (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RationalRawPassiveRowClocks.lean`) supplies the raw-table rational coarse-hazard producer. `exists_rationalClocks_log_bound_of_raw_strictInverse_triple` (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RationalPassiveRowCalendarBound.lean`) supplies the fixed-input asymptotic calendar bound. Rationality is required only for singleton rewards; labels are existential, not a canonical executable raw-table selector. |
| Proof Section 6 | Matched by the targeted-checked arbitrary-signed full-cap and regret bounds in `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineSignedHorizonError.lean`. These do not compare a late negative deviation with its own terminal payoff. |
| Proof Section 7 | Matched by the same quiet-witness producer: literal nearby strict tables, original-game Nash transfer on the same profiles, and retained-family compact target selection. The selected laws precede every valid reward bound and horizon; the shared signed consumer supplies `max 1 (ceil (4 * M * (deadline + 1) / accuracy))`. No uniform weak-boundary calendar complexity is asserted. |
| Fin4 counterexample consequence | Matched by `raw_inverse_test_failure_of_no_uniformEquilibriumPayoff` (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`), for every selected triple in any finite parent player type. |
| Named class comparisons | Matched in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/PassiveRowFourMatrixComparisons.lean`: full determinant and inverse, projective Q-bar failure, absence of negative Hamiltonian cycles and signed four-cycle data under every relabeling. Tournament exclusion is stronger than the packet: fractional tournaments with parameter at least one are excluded. |
| Ambient degree and open class | Matched by `ambientDegree_lcpMinMap_zero_eq_r0Degree` (`MathUE/LinearProgramming/R0AmbientDegree.lean`), the bounded-offset comparison in `MathUE/LinearProgramming/R0AmbientOffsetDegree.lean`, and `exists_open_ambient_degree_one_uniformPayoff_class` (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/PassiveRowFourAmbientDegreeNeighborhood.lean`). One full reward-table open class has both the literal ambient degree-one property and a uniform-equilibrium payoff. Degree one alone is not the equilibrium criterion. |
| Four attempted falsifiers | Matched in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/PassiveRowJoiningBoundary.lean`, `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/PermutationInverseClockBoundary.lean`, and `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonTripleInverse.lean`. Joining gains use actual values for every positive phase-length vector and the exact tolerance-selected calendars; the coarse gain is explicitly positive. Every paired-matrix principal triple has the stated negative inverse entry. |

The signed horizon task has a reusable starting point:
`expectedStagePayoff_update_le_cutoffTerminal_add_opponentLiveTail`
(`UniformEquilibrium/Quitting/Punishment/NegativeSoloUniformization.lean`)
has no singleton-sign hypothesis. Its actual cutoff replacement is covered
by the same full terminal cap; the finite opponent-tail sum then supplies
the horizon error. This avoids an invalid comparison with a late negative
deviation's own terminal payoff.

The eleven-support inventory and open-neighborhood proof are reused, not
duplicated. The ambient comparison supplies the packet's literal minimum-map
interpretation. Rational labels remain existential; no uniform weak-boundary
calendar complexity or degree-one-only equilibrium criterion is asserted.

`exists_realFiniteCalendar_log_bound`
(`UniformEquilibrium/Quitting/Cycles/RealSingletonCalendarLogBound.lean`)
supplies the fixed-input asymptotic bound for real singleton data. It fixes
the certificate, reward bound, constant and threshold before accuracy and
uses one actual finite profile for every opponent cutoff, terminal regret,
delivery and both date-count bounds. Exact rational cutoff search remains
unchanged; its estimates delegate to `MathUE/PowerCutoffLogBound.lean`.

### Passive calendar dependencies already available

The rational subdivision needs a chronological adapter to the existing periodic
interfaces. The following declarations supply its semantic consumers:

- `isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue`
  (`UniformEquilibrium/Quitting/Cycles/CyclicSupersolution.lean`) accepts arbitrary
  finite periodic roots, exact Continue recursions, a single Quit error and
  opponent contraction. It gives the full behavioral cap with the packet's
  error `2 * M * δ`; no per-date error accumulation is needed.
- `eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff`
  (`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`) identifies the
  produced periodic values with actual terminal values.
- `quittingTerminalPayoff_cyclicFiniteProfile_mul_card`
  (`UniformEquilibrium/Quitting/Cycles/CyclicFiniteWord.lean`) gives the exact
  payoff after any number of complete cycles followed by all Continue. It
  requires no Nash premise and supplies the packet's censor identity.
- `abs_quittingContinuationBestResponseValue_literalRootStack_sub_le`
  (`UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean`) bounds a
  change of full suffix cap by opponent-deleted prefix survival. A reward
  bound and the cyclic-word survival identity give the censor cap error.
- `exists_finiteDeadlineTimingProfile_cyclicFinite_exact`
  (`UniformEquilibrium/Quitting/Cycles/CyclicFiniteMenu.lean`) realizes the same
  finite cyclic profile by independent finite-date-or-Never laws, preserving
  stopping laws, the full semantic pair and every pure-date response payoff.
  Its public conclusion does not certify rational masses.

The checked construction uses the exact rational hazards
`q / (n - l * q)`, variable phase lengths, and their ordered cyclic succession.
The existing equal-length geometric subdivision is not that construction.
Mathlib's `finSigmaFinEquiv` implements ordered prefix-sum flattening.
The successor, product and actual-value adapters are checked in
`UniformEquilibrium/Quitting/Cycles/VariableSingletonCalendar.lean`;
the tolerance-selected calendar delegates to that construction.
Rational stopping masses, verified cutoff selection, the explicit date
bound and its fixed-input asymptotic estimate now have actual-data producers.
The cap, censor-payoff and independent-law foundations above should be reused.

## Shared ambient-degree library

The shared construction is checked by targeted and full silent builds.
`ambientDegree` and `ambientDegree_eq_of_extension`
(`MathUE/Topology/AmbientDegree.lean`) accept an open bounded region,
a field continuous on its closure, and a target excluded from the frontier
image. The enclosing rectangle and extension are constructed internally.
Empty regions, zero dimension and nonisolated fibers are included.

`localDegree_ofAmbientMap_chart_independent`
(`MathUE/Topology/BoxComplementarityRectangularChartIndependence.lean`)
compares the unchanged actual field in arbitrary positive rectangles.
Its compact-tube argument controls moving source preimages; fixed-region
homotopy invariance alone would not suffice.
`localDegree_ofAmbientMap_eq_of_extensions`
(`MathUE/Topology/BoxComplementarityAmbientExtension.lean`)
proves extension independence from agreement on the source closure.

`ambientDegree_homotopy`
(`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`) uses one
joint time-space extension. Closure extensionality, excision, disjoint
root-cover additivity and arbitrary-domain identity normalization are
proved in `MathUE/Topology/AmbientDegreeProperties.lean`. These supply the
standard defining properties of Brouwer degree. Uniqueness against another
implementation is not proved. No finite-fiber, regularity, differentiability
or supplied degree-equality hypothesis is added.

`ambientDegree_lcpMinMap_zero_eq_r0Degree`
(`MathUE/LinearProgramming/R0AmbientDegree.lean`) identifies the canonical
R0 integer on every bounded open neighborhood of the origin.
`exists_radius_above_ambientDegree_lcpMinMap_eq_r0Degree`
(`MathUE/LinearProgramming/R0AmbientOffsetDegree.lean`) supplies one actual
source containing every zero for every bounded offset. Its literal
offset-minus-one corollary covers the passive packet's degree calculation.

`exists_quittingCrossedAmbientAnnulus_degree_eq_one_sub_r0Degree`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseAmbientDegree.lean`)
constructs an actual bounded annulus whose zero fiber is the entire nonzero
crossed fixed-point set and whose degree is one minus the crossed R0 degree.
Frontier avoidance and strict chart enclosure are derived. The quotient's
actual-source adapter is checked in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientAmbientDegree.lean`;
the shared foundation need not be rebuilt.

`exists_quittingCrossedOmegaAnnulus_degree_eq_one_sub_r0Degree`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseOmegaDegree.lean`)
passes its targeted silent build on the literal `(-1,2)^n` source. Excision
through the actual intersection with the radial annulus keeps the entire
nonzero fiber. This is not a finiteness or regularity statement about roots.

## Complete-claim audit: paired collision reward packet

This inventory follows the complete packet, including its exact finite-law
conclusions. All claims below pass their targeted checks. Independent
read-only review found no remaining claim-level obligation. The full integration
gate passed; the packet is retired to `math/formalized/` without content changes.

| Source claim | Completion obligation |
| --- | --- |
| Sections 1-2, literal source and exits | Targeted checks pass for the fifteen reward vectors, twelve varying pair-member coordinates, constant singleton matrix, signed `c ≤ 1` and pure `c ≥ 4` consumers. |
| Sections 3-4, produced rates | Both scalar intermediate-value constructions, positive denominators and interior-rate bounds pass targeted checks. The final existence theorem constructs its rates from `1 ≤ c ≤ 2`, rather than accepting them as a hypothesis. |
| Section 5, infinite equilibrium | Phase/owner endpoints, prescribed recursions, strict quiet joins, actual payoff identification, every suffix's unrestricted behavioral cap and the same profile's uniform payoff pass targeted checks. |
| Section 5, infinite horizon rate | `PeriodicRates.profile_horizonDeviation_absolute_uniform`, `allSuffix_horizonDeviation_absolute`, and the delivery/Nash consumers pass the targeted check in `UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardHorizon.lean`. Absolute terminal-to-average error is at most `(8000/271)/N` for every complete deviation and suffix; regret is at most `(16000/271)/N`. |
| Section 5, exact finite laws | `PeriodicRates.finiteProfile_payoff_eq`, `finiteProfile_completeCap`, `finiteProfile_exploitability_eq`, `finiteProfile_exploitability_le_geometric`, the three `finiteStoppingLaw` mass lemmas, `finiteStoppingLaw_eq_censor`, and `exists_finiteTimingLaws_exact` pass the targeted check in `UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardFiniteCalendar.lean`. The cap is the full behavioral supremum, and a retained first-active date attains it. |
| Section 5, finite horizons | The literal `8K/N` delivery and deviation comparison, `16K/N` regret charge, `max 1 ceil(32K/ε)` threshold, and actual finite-law witnesses at one fixed target pass the targeted finite-calendar check. `exists_one_periodicRates_all_finiteCalendar_accuracies` selects rates before every accuracy. The censored opponents retain positive Never mass. |
| Section 6, stationary branch | Targeted checks pass for actual Quit and Continue sums, interval endpoint signs, produced common hazard, full behavioral cap, Bellman value and fixed uniform payoff for `2 ≤ c ≤ 4`. |
| Sections 2 and 7, exclusions | Targeted checks pass for pure-clock obstruction, the punishment-value bound, all-rate solo joining, capped-joint and low-active failures, every relabeling's raw-region failure, and weak singleton payoff-exclusion failure in `UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardBoundary.lean`. `normalPlayer` in `UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardFiniteCalendar.lean` supplies the literal normality corollary. |
| Sections 1 and 8-9, assembled conclusion | Targeted check passes for the four actual exits for every real input parameter on the same table, retaining overlapping endpoints and arbitrarily negative parameters. This does not cover arbitrary collision rewards. |
| Section 8, parameter-one calibration | `PeriodicRates.profile_at_one`, both rate and phase-value identifications, and the sharper isolation intervals pass the targeted check in `UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardCalibration.lean`. The result identifies actual profiles, not only matching tables or equations. |

The existing periodic compiler, complete stationary cap, finite cyclic-word
payoff identity, independent finite-clock realization, and finite-deadline
horizon estimates should be reused. The sharper finite cap equality needs
both its before/after-support upper bound and an actual retained active-date
response attaining the initial value. Neither a supplied cap field nor a
generic error bound proves that equality.

## Nonnegative-singleton finite quiet lifts

`NONNEGATIVE_SINGLETON_FINITE_QUIET_LIFTS` is partly implemented.
`exists_terminalProfile_smallExploitability_smallNever_of_nonnegativeSingleton`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/NonnegativeSingletonEarlyAbsorption.lean`)
passes its silent named check. From player count at most three, one nonnegative
own singleton and any positive delta, it selects an actual original-game profile
with exploitability at most delta plus delta squared and joint Never probability
at most delta. No child target or favorable profile is input, and no upper
restriction on delta is needed for this producer.

The scalar late-Never estimate is already
`prod_stoppingLaw_none_mul_singleton_le_terminalDebt`
(`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`).
The perturbation selector reuses it rather than repeating the limit argument.
`IsεAsymptoticNash.of_nonnegative_reward_perturbation`
(`UniformEquilibrium/Quitting/Terminal/TerminalPayoffRewardOrder.lean`)
gives the sharp one-delta transport for any nonnegative reward perturbation,
retaining the same actual profile and every behavioral replacement.

The original-table withdrawal/debt adapter, finite censoring, and
`prod_censorLateFiniteStoppingLaw_none_le`
(`MathUE/ProbabilityMassFunction/LateFiniteStoppingLawJointNever.lean`)
then give finite quiet witnesses. The existing
`quittingGame_exists_uniformPayoffWitnesses_of_terminalNash_family`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
selects one fixed target while retaining members of that actual family.
The residual-preserving multiple-outsider aggregation and finite quiet family
remain implementation work. The existing product-Never censor bound charges
twice the late mass; selecting total late mass below delta squared divided by
two preserves the packet's stated constants without weakening its conclusion.
The specified-child-target extension must not be weakened: the packet only
selects a child target and includes a counterexample to preserving arbitrary ones.
The original reward certificates remain unchanged throughout the perturbation.

## Literature dependency boundary: Sorin's feasible faces

`proposition_4` (`Literature/Sorin1986.lean`) proves the exact discounted
feasible-set identity below the reciprocal player-count threshold. Its stages,
residuals and actual behavioral profile are selected internally from the
connected one-stage payoff set. The silent paper build, actual-profile consumers,
separate standard-axiom checks and full build pass. The same checks retain
`proposition_6` and the completed behavioral `proposition_15`.
This closes discounted feasibility at that threshold, not equilibrium existence
for the remaining paper results.

`proposition_7` (`Literature/Sorin1986.lean`) passes the silent named paper
build and a separate transitive axiom check using only the three permitted
standard axioms. For a one-dimensional feasible face and rates
`0 < δ < λ ≤ 1`, inclusion of its actual discounted feasible payoffs at
rate δ in those at rate λ implies that the whole face is feasible at δ.
The endpoints, maximal gap, actual profiles and continuation replacements
are derived internally. The conclusion concerns feasible payoffs, not
equilibrium existence.

`proposition_8`, `proposition_9`, and `proposition_9_all_face_dimensions`
(`Literature/Sorin1986.lean`) also pass that named build and separate
transitive axiom checks. The last declaration strictly strengthens the
printed face induction by removing its extra restriction that the face
dimension be smaller than the player count. Its horizon-size and actual
feasible-set inclusion hypotheses remain. The discounted folk theorem,
planar simple-connectedness argument and remaining convergence results
are not supplied by these feasible-face theorems.

## Literature dependency boundary: Sorin's discounted equilibrium matrix

`asymmetricStationaryProfile_isDiscountedNash` and
`asymmetricAlternatingProfile_isDiscountedNash` (`Literature/Sorin1986.lean`)
construct the two original critical-rate branches with full behavioral deviation
caps and exact printed payoffs. Equality belongs to the stationary branch;
negative payoffs and loss parameters beyond the payoff gap are retained.
The silent paper check, actual-profile boundary consumers, separate standard-axiom
checks and full build pass, including the Proposition 15 regression.
The above-critical uniqueness assertion in `concluding_remark_4` is not proved
by those two critical-rate existence results.
The source's route decreases the loss parameters to their common minimum and
invokes symmetric uniqueness. The missing adapter must justify the required
equilibrium and payoff comparison for arbitrary full-history strategies;
pointwise ordering of payoff tables does not establish it. No preserved draft
or existing declaration supplies this comparison. This records the proof
dependency, not a refutation of the paper's conclusion.

A read-only elementary strategy audit rules out interpreting the printed
page-160 reduction as preservation of every identical equilibrium profile.
Take `α = 0`, `β = 2`, `x = 10`, `y = 1`, and rate `3/5`, above the critical
rate `1/2`. Prescribe mutual Defect until the first Cooperate, then reward that
initial cooperator with permanent opponent Cooperate while it Defects.
In the original game a unilateral first Cooperate has discounted payoff at
most `-(3/5) * 10 + (2/5) * 2 = -26/5`; delay or mixing cannot improve the
zero on-path payoff. After reducing both losses to one, the same deviation
instead earns `-(3/5) + (2/5) * 2 = 1/5`. This calculation is not a checked
Lean theorem here and does not refute the payoff-set statement: stationary
mutual Defect still attains its zero target in the reduced game. A valid
payoff-transfer or strategy-transformation source is needed, not generic
pointwise reward monotonicity. The original `concluding_remark_4`
(`Literature/Sorin1986.lean`) remains unproved.

`FiniteStageGame.discountedPayoff_afterHistory_mem_equilibrium` and
`FiniteStageGame.exists_discountedBestResponse` (`Literature/Sorin1986.lean`)
pass the silent named paper build and separate standard-axiom checks. Root
discounted Nash implies Nash of the same actual continuation at every reached
history with positive remaining discount. The exact unilateral splice gain
identity also retains unreachable branches and zero discount; child Nash is
not inferred there. The best-response theorem internally constructs its
compact unilateral carrier and both exact Kuhn payoff transfers for every
full behavioral opponent profile and every paper discount rate, including
the current-stage endpoint. These are not assumed optimal-response data.

The actual four-history first-stage matrix is constructed from these internally
selected replies. Its mixed-payoff identity and Nash property derived from
the original profile pass their silent named check and separate standard-axiom
check. Unsupported branch pairs remain independent individual best-response
values, not jointly feasible or equilibrium continuation pairs. The reusable
initial-branch strategy changes the initial mixture and supplies a complete
reply at every first history, including branches newly reached by the deviation.

The generic scalar escape inequality also passes its silent named check and
standard-axiom check. Its non-strict fourfold factor gives strict improvement
when the original escape product is positive; a strict fourfold estimate is
not claimed at boundary equality. The actual reached-child adapter and compact
upper inclusion pass their silent named check and separate standard-axiom checks.
`prisonersDilemma_discountedEquilibriumPayoffs_subset_criticalSet` and
`prisonersDilemma_criticalSet_subset_discountedEquilibriumPayoffs`
(`Literature/Sorin1986.lean`) prove both inclusions for the actual discounted
equilibrium-payoff set. The printed punishment profiles have complete
behavioral deviation bounds. The literal `proposition_15` passes the silent
named paper check and a separate transitive check using only the three
permitted standard axioms. It does not depend on unfinished Literature proofs.

The support-local discounted Bellman bound passes its silent named dependency
check. The state-only theorem now delegates to its common expected-value
telescope. All-child Nash gluing also passes its silent named check and separate
standard-axiom check, including initially off-path children and zero discount.
The literal punishment profiles for all square vertices, the full square and
both outer segments pass the silent named paper check and separate standard-
axiom checks. Closed mixing endpoints and every initially off-path child are
retained. The full integration gate passes for these additions;
Sorin's other unfinished paper results are separate obligations.

The supplied constant approximate punishment trigger is implemented as
`exists_constantApproxPunishmentTrigger` (`Literature/Sorin1986.lean`). It
selects actual approximate min--max opponents internally, follows one prescribed
calendar, delivers its discounted series at every valid rate, and bounds every
supported off-calendar stage under every full behavioral deviation. The
generic punishment stage cap is shared with the existing vanishing-punishment
trigger. This is a prerequisite for the supplied periodic strict-IR discounted
Nash construction, not a proof of the remaining discounted folk-theorem clause.

`exists_discountedNash_allSmallRates_of_strictIR` and its metric-delivery facade
(`Literature/Sorin1986.lean`) select one actual profile before all sufficiently
small rates, with exact Nash against unrestricted behavioral deviations. The
internal periodic calendar, strict phase slack, and supported-history Bellman
cap are constructed from the fixed strictly individually rational target.
`property_4_discounted_of_fullDimensional` in the same paper owner then proves
Hausdorff convergence to the weakly individually rational feasible payoff set:
the ambient-ball hypothesis supplies a strict point, and a compact finite cover
makes the rate threshold uniform over all targets. The same proof is factored through the stronger
`property_4_discounted_of_exists_strictIR` in that owner: a single feasible
all-strict point suffices, without ambient full dimensionality. Its weak-target
profile facade still selects one exact Nash profile before all small rates.
This does not handle a flat security coordinate without a strict point.
`exists_discountedNash_eq_allRates_of_IR_singleton` and
`property_4_discounted_of_IR_singleton` in the same owner prove the singleton
weak-IR branch. One actual stage Nash is selected internally, and its same
stationary repetition is exact Nash with exact target delivery at every valid
rate. The previous discounted-inclusion proof delegates to that shared
stationary-profile theorem.

`FiniteStageGame.exists_flatFace_calendar` (`Literature/Sorin1986.lean`)
selects an actual nonempty finite pure calendar for a supplied feasible target
whose flat coordinate equals security, under the global pure-stage cap at
that security level. Every calendar date preserves the flat coordinate
exactly, while the full cycle-average payoff approximates the target.
Its silent named paper check, separate standard-axiom check, and full
integration build pass. This theorem is the actual source-calendar producer.
`exists_discountedNash_close_allSmallRates_of_flatFace_strictActive`
in the same owner consumes that source internally. When every player is the
flat or active coordinate and the target has strict active security slack,
it selects one actual profile before all sufficiently small positive rates,
with exact flat delivery at every valid rate and exact Nash against every
full behavioral replacement at small rates. Its metric target approximation,
silent named check, and separate standard-axiom check pass. This facade does
not itself supply weak-active targets without strict slack.
`exists_discountedNash_close_allSmallRates_of_mem_IR_of_flatFace` in the same
owner supplies those targets by flat-preserving convex mixing. The actual
two-player geometry selects the strict, singleton or flat branch internally.
`exists_discountedNash_flatDelivery_allRates_of_mem_IR_of_flatFace` in that
owner retains exact flat delivery at every valid rate for the same selected
weak-target profile, alongside exact Nash and metric approximation at all
sufficiently small rates. The earlier facade projects this stronger owner;
its delivery calculation is not duplicated. The named check and separate
standard-axiom check pass.
`property_4_discounted` and its delegating `lemma_2`
(`Literature/Sorin1986.lean`) are proved in Lean under the original corrected
disjunction: the weakly IR feasible set is full dimensional or there are
exactly two players. The literal Hausdorff conclusion retains a rate threshold
uniform over all targets, obtained from the actual pointwise profile producer
and a shared compact finite cover. Their silent named paper check and separate
standard-axiom checks pass. Other unfinished Sorin claims remain separate.

`CompactContinuousGame.pair_returnConnector_homotopic` and
`CompactContinuousGame.exists_pairPayoffField_range_eq`
(`Literature/Sorin1986.lean`) instantiate the supplied Proposition 11 fiber
connector argument in the actual two-player payoff image. The generic
`returnConnector_homotopic_of_same_value`
(`MathUE/Topology/SeparatelyAffineFiberConnectors.lean`) stays in the image
subtype and requires neither mixer reversal nor a winding construction.
Their named checks and separate standard-axiom queries pass. The original
`proposition_11` remains unproved: planar winding and the final image-topology
bridge are not supplied by this bounded connector unit.

`CoveringLoopFamily.endpoint_isLocallyConstant`
(`MathUE/Topology/CoveringLoopFamilyEndpoint.lean`) constructs the actual
covering-lift endpoint observable in a discrete fiber, for arbitrary parameter
spaces. `coveringEndpoint_eq_of_compact_incidence`
(`MathUE/Topology/CoveringImageIncidence.lean`) consumes that observable through
the canonical compact image incidence and quotient-fiber collision, retaining
an explicit same-parameter relative-homotopy premise.
`SeparatelyAffinePair.prefixReturnFamily`
(`MathUE/Topology/SeparatelyAffineImageLoopFamily.lean`) supplies the literal
continuous prefix-plus-return image-loop family and its same-time image
homotopies from the affine source. `SeparatelyAffinePair.liftPath_imageLoop_apply_one`
(`MathUE/Topology/SeparatelyAffineCoveringEndpoint.lean`) composes those actual
homotopies with the compact-incidence covering endpoint law.
`SeparatelyAffinePair.exists_closed_logarithmic_lift`
(`MathUE/Topology/SeparatelyAffineComplexLoopLift.lean`) specializes it to the
exponential covering of the punctured complex plane, producing a continuous
logarithmic lift with equal endpoints for every translated image loop.
This is not a nullhomotopy in the original image. The planar bridge to Sorin's
Proposition 11 remains separate; no integer index oracle is assumed.

`circle_logarithm_endpoint` and `not_exists_closed_circle_logarithm`
(`MathUE/Topology/ComplexCircleLogarithmObstruction.lean`) identify every
continuous logarithm of an actual scaled one-turn circle with its initial
value plus the explicit lift, giving nonzero endpoint displacement. Arbitrary
scale is allowed; existence already excludes zero. `exists_path_to_first_closedSet_hit`
(`MathUE/Topology/PathFirstClosedSetHit.lean`) constructs an actual clipped path
whose range stays in the original range intersected with the union of the
closed set and the starting complement path component. It needs no metric or separation
assumption. Neither result is the planar image-nullhomotopy theorem.

`CompactContinuousGame.feasiblePathImageFill_spec`
(`Literature/Sorin1986.lean`) now computes a compact, path-connected, locally
path-connected fill between the actual real path image of Icc 0 1 and the
game's feasible payoff carrier. Its silent paper and separate permitted-axiom
checks pass. The generic carrier is not assumed locally path connected.
`continuous_of_null_closed_patches`
(`MathUE/Topology/NullFamilyPasting.lean`) supplies actual continuity for
parameterized null families in pseudometric spaces without local finiteness,
disjointness or compactness. The general planar disk model remains unproduced.

`exists_normalized_disk_embedding`
(`MathUE/Complex/NormalizedDiskEmbedding.lean`) and
`exists_disk_embedding_norm_deriv_gt`
(`MathUE/Complex/DiskEmbeddingDerivativeImprovement.lean`) pass silent named
checks: actual disk normalization and an omitted-point derivative improvement
are supplied for open simply connected proper complex domains. The first
reuses a pinned private source via supported import-all, not an external draft
dependency. Apache attribution, license text and immutable provenance are
retained. The actual maximizing and surjective consumers are recorded below.
The non-injective continuous boundary extension needed for general component
frontiers remains separate;
no Jordan-boundary or whole-feasible-carrier LPC assumption is inserted.
`Math.Analysis.exists_finset_eq_prod_smul_nonzero`
(`MathUE/Analysis/AnalyticCompactZeroFactorization.lean`) supplies the actual
finite-zero analytic-order factorization on a compact preconnected set, in
general normed-field/vector-valued scope without a completeness assumption or
zero-set oracle. `circleIntegral_logDeriv_eq_finsum_analyticOrderNatAt`
(`MathUE/Complex/CircleArgumentPrinciple.lean`) derives the circle multiplicity
formula from analytic closed-disk data and nonzero boundary values, including
radius zero. `eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn` and
`eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn`
(`MathUE/Complex/HurwitzLimit.lean`) give the actual zero-free and injective-limit
alternatives for a nontrivial countably generated filter on an open preconnected
complex domain. Pinned codiscrete-zero and circle-integral convergence APIs are
reused, not duplicated. Their source adaptations retain Apache attribution and
the immutable upstream provenance.
`Math.ComplexAnalysis.exists_normalized_disk_derivative_maximum`
(`MathUE/Complex/NormalizedDiskDerivativeMaximum.lean`) constructs an actual
maximizer from equicontinuity, compact exhaustion, Ascoli and the injective-limit
theorem. `Math.ComplexAnalysis.exists_bijOn_unitBall_map_eq_zero`
(`MathUE/Complex/NormalizedDiskBijection.lean`) supplies the normalized
holomorphic disk bijection for arbitrary chosen base points in open simply
connected proper complex domains. The named dependency closure passes silently.
General non-injective boundary extension and planar disk models remain separate;
these analytic results do not seal Sorin's Proposition 11.
The source-backed remaining route is recorded in
`notes/feedback/CODEX_FORMALIZER_SORIN_PLANAR_NULLHOMOTOPY_DEPENDENCIES.md`.
`isPathConnected_selectedComponentFill` (`MathUE/Topology/SelectedComponentFill.lean`)
constructs actual paths in an arbitrary selected union of full complement
components. Its closedness requires ambient local path-connectedness;
compactness additionally requires a compact ambient carrier. The path result
instead uses ambient path-connectedness and a closed path-connected source.
`locallyPathConnectedSpace_selectedComponentFill`
(`MathUE/Topology/SelectedComponentFillLocallyPathConnected.lean`) proves local
path-connectedness from ambient local path-connectedness, a closed source and
local path-connectedness of that source subtype. No finite selected family,
metric, separation or global connectedness premise is added. The actual
canonical loop-fill instantiation is supplied by the compact-carrier owner
above; only the general planar disk model remains separate.

Primary-source discovery located the two-player flat-security prescription in
[Tomala, *Jeux répétés* (2006)](https://www.numdam.org/item/10.5802/xups.2006-02.pdf),
Theorem 3.8, pp. 38--39. If the IR set is a
singleton, repeat a stage Nash equilibrium. Otherwise a coordinate flat at
security is globally maximal, and the periodic construction need not punish
that player's deviations. The actual calendar and trigger producers are
checked in the same paper owner. Its loose approximation constants are not
copied; the existing separate-margin and compact-cover arguments retain weak
IR targets. [Sorin's 1992 survey](https://perso.imj-prg.fr/sylvain-sorin/wp-content/uploads/sorin-pub/92.HandGT.pdf),
Theorem 2.2, states the discounted convergence
result under the weaker alternative that one strict IR feasible point exists.
The full-dimensional theorem delegates to that generalization by deriving
the strict point from its ball hypothesis.

## Shape connections available from existing proofs

The following are read-only proof-mining findings, not newly checked declarations.
They require short formalization or public adapters, not new substantive mathematics.

1. A boxed global minimum of a full exact-root potential has a strict singleton
   gap and only the all-Continue exact root. These are proved by
   `IsQuittingFullExactRootPotential.minimum_above_singleton` and
   `IsQuittingFullExactRootPotential.minimum_exactRoot_absorption_eq_zero`
   (`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMinimum.lean`).
   Applying `exists_open_linearAbsorptionDefect_of_compact_strictAllContinue`
   (`UniformEquilibrium/Quitting/Root/StrictAllContinueBasinLinearAbsorptionDefect.lean`)
   to the singleton minimum gives an open neighborhood and positive linear
   absorption-defect constant. If the player count times the robust tolerance
   is strictly below that constant, every robust edge sourced there has zero
   absorption and identical source and target. No such smallness is established
   for the original supplied tolerance.
2. The proof of
   `exists_rational_exact_solo_rejection_of_standardQ_quasiconvex`
   (`UniformEquilibrium/Quitting/Projective/RationalExactSoloRejection.lean`)
   admits any prescribed positive drop ratio and external positive rate ceiling:
   choose one rational face point with drift below half the ratio, then a
   positive rational rate below the ceiling in the eventual quotient interval.
   It also internally retains endpoint bounds of reward bound plus one,
   before weakening them to plus two. A stronger public theorem should expose
   these conclusions without claiming an effective radius or denominator bound.
3. The matrix-free exact-root quasiconvex rejection can be applied to the
   potential divided by any positive charge coefficient. This gives a positive
   exact edge whose drop is below that coefficient times absorption, with no
   Q hypothesis. Unlike the rational solo construction, it does not give
   arbitrarily small absorption or a one-quitter root. The existing normalization
   is `isQuittingFullExactRootPotentialWithCharge_iff_div`
   (`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialChargeScale.lean`).

## Nonnegative-singleton quiet-lift implementation

`exists_quietProfiles_smallExploitability_smallNever_of_withdrawalFutureJoinFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`)
constructs original-game child profiles internally and evaluates their literal quiet
parent lifts. The finite maximum certificate-weight and Never-residual bounds are
selected before every positive scale; the full parent exploitability bound is
`factor * (delta + delta²) + residual * delta`, and child joint Never is at most
`delta`. The five original F/J certificate kinds remain independent across outsiders.
The specified-child-target theorem still requires a strictly positive singleton.
`exists_finiteQuietProfiles_of_withdrawalFutureJoinFamily` and
`exists_uniformFiniteQuietFamily_of_withdrawalFutureJoinFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFiniteQuietSource.lean`)
produce actual positive-deadline independent child menus, the packet's two numerical
bounds, and one fixed parent target with witnesses retained from one indexed finite
quiet family. Both full regret and child joint Never tend to zero. The generic
and Fin4 existence facades include zero singleton rewards; the Fin4 proper-child
cardinality restriction is proved internally. All certificates use original rewards.
`UniformEquilibrium/Quitting/Classification/QuietExtension/QuietLiftFiniteCensor.lean`
supplies the exact whole-family censor commutation and parent/child discarded-mass
identity, reusing the existing exploitability-congruence theorem.
`smallPivotRepairValue_of_nonnegativeSingleton_withdrawalFamily` and the literal
normalized Fin4 facade
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalSmallPivotRepairSource.lean`)
select actual finite nonpivot laws with arbitrarily small repair-LP objective.
The existing exact finite-menu quiet transport and objective/exploitability consumer
are reused; no optimal-pivot compatibility hypothesis is supplied.
`smallPivotRepairValue_of_deleted_nonnegativeSingleton_withdrawalFamily` in the
same source owner permits any eligible deleted set and any parent repair pivot.
The pivot need not belong to that set or equal the selected child singleton.
Its Fin4 existential-singleton facade needs only one nonnegative survivor.
The omitted-Never supplied-profile boundary is fully covered by
`UniformEquilibrium/Quitting/Examples/WithdrawalNeverBoundary.lean`.
`NegativeSingletonQuietBoundary.debts_eq_childClockMasses`,
`NegativeSingletonQuietBoundary.quietLift_exploitability_ge_half`, and
`NegativeSingletonQuietBoundary.outsiderQuitProfile_exactNash`
(`UniformEquilibrium/Quitting/Examples/NegativeSingletonQuietBoundary.lean`)
give literal complete-debt identities, the uniform half-regret quiet obstruction,
and a separate exact parent equilibrium, with all five original zero-weight
certificates and a literal Fin4 specialization. No no-UE claim follows.
The literal Fin4 prescribed-child-target boundary is covered by
`PrescribedChildTargetQuietBoundary.one_le_three_exploitability_add_childPayoffs`,
`PrescribedChildTargetQuietBoundary.not_tendsto_zero_regret_and_childPayoffs`, and
`PrescribedChildTargetQuietBoundary.no_quiet_uniformWitnesses_extending_zeroChild`
(`UniformEquilibrium/Quitting/Examples/PrescribedChildTargetQuietBoundary.lean`).
The unrestricted quantitative bound uses the two actual child Never deviations
and the outsider's exact full debt. The uniform obstruction retains the original
quiet witnesses. The same module verifies all five zero-weight outsider
certificates, the actual restricted child's all-Never zero-payoff equilibrium,
and both alternative exact quiet parent equilibria. The separate three-player
presentation is not duplicated: the packet's literal Fin4 instance is used.
`quittingTerminalPayoff_soloStoppingLaw_eq`
(`UniformEquilibrium/Quitting/Paths/SoloStoppingLawPayoff.lean`) is the reusable
arbitrary-law observer payoff identity behind the two Never deviations.

## Quiet-source proof-mining findings

These are connections supported by existing proofs, not checked new declarations:

- Expose the zero restricted-child target as a literal uniform-equilibrium payoff
  from `childAllNever_exactNash`, and retain the displayed alternative quiet
  parent profiles through the existing fixed-family uniformization theorem.
  These would complement, not weaken, the checked quiet-witness obstruction.
- Strengthen `exists_finiteQuietLift_of_profile`
  (`UniformEquilibrium/Quitting/Classification/QuietExtension/QuietLiftFiniteCensor.lean`)
  with the already available coordinatewise payoff error `2 * bound * tolerance`.
  The core censor theorem supplies it for the same selected finite laws.
  This does not permit preserving the forbidden arbitrary zero-child target.
- Derive reward-bound nonnegativity from the absolute reward bound in the finite
  censor and source interfaces. A source pivot or nonempty player set supplies a
  singleton at which to evaluate the bound.
- Extract the constant nonnegative payoff-coordinate cap and debt calculation
  from `outsiderDebt_eq_liveMass`
  (`UniformEquilibrium/Quitting/Examples/PrescribedChildTargetQuietBoundary.lean`).
  For constant terminal coordinate `c ≥ 0`, legal immediate Quit attains cap `c`
  and exact debt is `c` times joint Never, for every actual profile. This also
  removes the corresponding positive-coordinate duplication in the negative
  singleton boundary example.

## Further shape proof-mining findings

These are proposed adapters from existing proofs, not checked new declarations:

- A C² full-root potential has a negative minimum canonical Hessian eigenvalue
  on its singleton box without a standard-Q or singleton-sign hypothesis.
  Combine the existing nonquasiconvexity theorem with the Hessian-floor convexity
  theorem at coefficient zero and minimum eigenvalue attainment.
- Rational quasiconvex polynomial candidates of arbitrary degree admit robust
  approximate rejection and eventual search without standard-Q or singleton signs.
  Combine the matrix-free positive exact-root rejection with rational robust
  approximation and the existing exhaustive search theorem. This does not promise
  an exact rational Nash row.
- The monotone-transform exclusion can use an outer function Lipschitz on the
  inner polynomial's image instead of C¹ on an open interval. The current proof
  uses C¹ only to obtain that Lipschitz bound, so an extracted adapter also covers
  monotone piecewise-linear transforms and clipping.

## Completion criterion

Packet completion requires matching every mathematical conclusion above to an
integrated checked declaration or an explicitly checked composition, with
the packet's hypotheses, quantifiers, strategy restrictions and numerical
bounds. Definitions and standard background may reuse existing interfaces;
they do not require duplicate proofs. A conditional compiler is not an
actual-data producer, and payoff existence is not a retained-strategy theorem.
The first-dependency table by itself supplies no retirement evidence.
Files under `math/` remain under mathematical-workspace ownership. Formalizer
completion records do not authorize moving, staging or committing those files.
