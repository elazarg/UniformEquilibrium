# Export packet dependencies and completion obligations

This is a static dependency audit of the fifteen packets in `math/exports/`,
not a packet ranking or a new mathematical proof. “Checked” below refers to
the named production declarations, not to the packet in full. Packet count
is a poor priority proxy: several packets share one interface, while some
already have their main conclusion in production. The table identifies first
dependencies, not complete packet coverage. The claim inventories below
record broader retirement obligations after reading those packets in full.

The new production declarations below pass both their targeted checks and the
full silent default build, including the regenerated exhaustive axiom audit.
Trust, umbrella/import boundaries, proof duplicates, telescope redundancy and
documentation checks pass. A packet remains pending where its claim inventory
lists unimplemented conclusions.

| First missing theorem or adapter | Packets grouped at that boundary | Checked production foothold |
| --- | --- | --- |
| Ambient-degree identification and remaining example refinements | `GUARDED_CROSSED_RESPONSE_DEGREE_ESCAPE`; quotient producer in `STATIONARY_RESPONSE_QUOTIENT_DEGREE_ESCAPE` is checked | The strict unit and half-ceiling raw producers construct actual stationary terminal Nash and UE from finite reward comparisons, including reconstruction of the half-ceiling residual coefficients. Both nonnegative-inverse boundary branches select one fixed original-game target (`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakBoundaryTarget.lean`). `exists_uniformPayoff_of_oneSidedWeakUnitRawGuards` (`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`) supplies the matrix-free sixteen-comparison Fin4 class, including signed sole-owner completion. Both literal table roots, exact full caps, and specified UE targets are checked (`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseExactRoots.lean`), together with pure-clock, raw-class, and partition separations. `halfCeilingRoot_isHorizonNash` (`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseFiniteHorizon.lean`) supplies the literal horizon bound. The fixed-chart normalized total nonzero-set degree is checked in `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseTotalDegree.lean`; ambient Brouwer identification, full reward neighborhoods, child-LP certificates, and censored-law estimates remain. The arbitrary signed quotient criterion is independent: `exists_uniformEquilibriumPayoff_finFour_of_responseInvariant_degree_ne_one` (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientNormalCompletion.lean`). |
| Quotient-wide consequences and literal fixtures | `STATIONARY_RESPONSE_QUOTIENT_DEGREE_ESCAPE` | The signed paired centered-row UE class and paired/full matrix degree calculations are checked. The entire nonzero-set normalized degree theorem and `exists_stationaryBellmanRoot_uniformPayoff_of_responseInvariant_singletonNormality` (`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientNormalCompletion.lean`) pass targeted checks. The latter retains the produced Bellman value as the fixed target, requiring normality only for negative singleton-block owners. Ambient degree identification, quotient counterexample consequences, quantitative conclusions, coordinate freedom, and algebraic and boundary fixtures remain. |
| Evaluated cancellation and packet refinements | `WITHDRAWAL_AND_DEADLINE_QUIET_EXTENSIONS` | Ordinary deadline, evaluated-security deadline, terminal-security deadline and patient fixed-target extensions are checked. Patient terminal necessity and the shared-witness deadline refactor pass targeted checks. The patient full-debt comparison uses the sum of its two response weights, and the terminal patient Never floor is not the evaluated zero-based floor. All four extensions consume raw reward certificates and preserve the actual quiet lift; none supplies certificates for arbitrary Fin4 tables. Evaluated cancellation, Never relaxations, rational enumeration, and strict examples/neighborhoods remain. |
| Actual quantile rigidity and robust unchanged-child obstruction | `ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO` | `AdaptiveChildCenter.profile_exactTerminalNash` and `AdaptiveChildCenter.target_isUniformEquilibriumPayoff` (`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenter.lean`) prove the center's positive equilibrium. The center data and capped-clock certificate infeasibility are also integrated. The packet's universal positive parent-plus-child exploitability floor still needs its actual quantile-rigidity sequence, all four restriction estimates including the adjacent-date atom move, and the reward-neighborhood transfer. Capped-clock infeasibility does not prove this stronger unchanged-child obstruction. |
| Full two-branch rational weak-subset selector and single-pivot secant source | `PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS`, `FINITE_CALENDAR_PAYOFF_EXCLUSION_RAW_TABLE_TESTS`, `FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION`, `SINGLE_PIVOT_SECANT_COLLAR_AND_STRICT_PRESSURE` | `exists_strictDeficitExactSuffix_allTerminalNash` (`UniformEquilibrium/Quitting/Paths/StrictDeficitExactSuffixNash.lean`) closes the single common-depth infinite all-suffix exact Nash conclusion under nonnegative singleton rewards. The existing executable rational weak-subset selector assumes strict preemption of all designated owners; its full stationary-exit/charged-step two-branch selector remains separate. The single-pivot secant/tilted common-calendar source is also separate; finite-calendar payoff compression does not preserve caps. |
| New screened-minimum/fiber algebra and source transport | `GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR`, `MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION`, `THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS` | `minimumTerminalSemantic_maximumDebt_allPlayersTie` (`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`), `minimumTerminalSemantic_exploitabilitySingletonMargin` (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`), and `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin` (`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`) provide minimum and actual-source interfaces. The first new steps differ: degree-six screened-root nonvanishing, four-coordinate singleton stretch, and signed affine-row comparison, respectively. None may assume a selected counterexample fiber or hazard as a certificate field. |
| Exact finite laws and remaining raw-class refinements | `THREE_PLAYER_CYCLE_PASSIVE_ROW_EXTENSION`, `PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION` | The passive raw inverse UE class and its open full-matrix degree-one fixture are checked. Variable-phase calendar values, full-response bounds, censor estimates, date counts and arbitrary-signed finite-horizon bounds pass targeted checks. Executable rational clocks still need their adapter check, and rational coarse-hazard production remains separate. `exists_uniformEquilibriumPayoff` (`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardExistence.lean`) now constructs the parameter-specific periodic/stationary/pure alternatives for every real parameter; no rate or strategy is supplied. Exact censored cap equality, explicit finite laws/horizon constants and class exclusions remain separate claims. |
| Full exact-root potential restriction and shape arguments | `REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS`, `QUITTING_POTENTIAL_SHAPE_EXCLUSIONS` | `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential` (`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`) and the robust charged relation supply the existing conditional certificate interface. The first missing reusable step is the full-exact-edge restriction with collision-adjusted singleton probes; reflection, quasiconvexity, curvature, and degree exclusions then diverge. These are necessary-shape reductions, not a polynomial producer or a solved-game class. |

## Next source-complete Lean tasks with broad reuse

1. Complete the crossed-response ambient-degree identification, neighborhood and
   child-LP certificates, and censored-law estimates. Its matrix-free Fin4
   producer, both nonnegative-inverse boundary branches, literal roots and
   caps, horizon bound, separation results, and fixed-chart total nonzero-set
   degree are checked. The degree identity does not require isolated or finitely
   many nonzero roots; ambient Brouwer identification remains separate.
2. Complete the separate evaluated cancellation variant, Never-row relaxations,
   rational calendar enumeration, and strict
   separating examples. Ordinary, all-evaluation truncated-security,
   untruncated terminal-security, and patient extensions construct their child
   target from the one-, two-, and three-player existence results. They require
   raw reward-table certificates, not selected strategies or cap bounds. The
   patient full-debt bound adds the two response weights; the deadline
   maximum-weight consumer cannot replace it. Patient terminal necessity and
   its attained-floor witnesses pass their targeted checks.
3. Complete the rational weak-subset two-branch selector, preserving one
   source/profile chronology across the stationary-exit and charged-step
   cases. The strict-deficit infinite all-suffix theorem is now checked and
   does not need to be reproved. The single-pivot source remains a different
   counterexample-side task.

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
The evaluated cancellation variant needs its own literal operation and reward
rows; it cannot reuse the positive patient Never floor.

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
Rational density, law-to-hazard encoding, and exhaustive enumeration
termination remain distinct source obligations.

For the crossed-response total-degree identity, complementary-region
additivity and excision are already available in `MathUE/Topology/`.
`exists_globalCrossed_localDegree_eq_r0Degree`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseEscape.lean`)
now delegates to the same-radius closed-ball isolation and local-degree
bundle; its complement is identified with the entire nonzero fixed-point set.
The resulting fixed-chart normalized integer degree must not be described
as ambient Brouwer degree without the additional identification and chart
adapter; `BoxComplementarityProblem.localDegree` makes that distinction explicit
(`MathUE/Topology/BoxComplementarityStabilizedLocalDegree.lean`).

Solan--Vieille's exact paper-order Lemma 10 is checked.
`singletonReward_le_nashError_div_never`
(`UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumVanishingNeverAlternative.lean`)
already supplies its exact Never-mass estimate. The other two assertions
use zero collision, exact boundary payoff identities, and singleton mass sums
in `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryPerturbedEstimates.lean`.
The literal `lemma12` and `corollary13`
(`Literature/future/SolanAndVieille2002a.lean`) pass their targeted build and
separate axiom check, with the paper's domain and constants. Proposition 1
still needs its literal
stationary-or-small-hazard strategy dichotomy; small-player UE existence
alone does not establish that source statement.

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

This is static declaration matching, not additional compiler evidence.
The packet is not complete. Its raw absorbing Bellman-root producer, signed
Fin4 UE consequence, paired centered-row class, and paired/full matrix degree
calculations are matched. Targeted checks also cover entire-nonzero-set
normalized degree and normal completion at the same produced Bellman value,
with normality needed only for negative singleton-block owners. Ambient degree
identification remains separate. The remaining claims are broader than the
examples and coordinate count alone.

| Source claim | Remaining obligation |
| --- | --- |
| Section 1, raw response identity | Expose cube-to-ambient polynomial identity and finite linear reward-coefficient tests. The existing cube identity and block row-sum adapter remain reusable. |
| Theorem A and Section 4.4 | Closed-ball isolation and the general entire-nonzero-set normalized degree theorem pass targeted checks. The literal paired value-two specialization and ambient-degree identification remain. |
| Theorem B, sign and no-singleton-block branches | Retain the produced block-constant root, actual terminal payoff, exact terminal Nash and uniformity of that same profile in one public conclusion. |
| Theorem B, normality branch | Matched by the targeted-checked singleton-normality completion, retaining the actual root payoff as fixed target. Normality is needed only for negative singleton-block owners. |
| Optional sole-owner exclusion | Translate the scalar linear system into exclusion of negative sole-owner roots and prove the stated conclusion for every nonzero root. |
| Sections 1 and 6, counterexample consequences | Prove quotient R0 inheritance through the homogeneous block lift, degree-one necessity under no Fin4 UE, and the weak nonnegative-inverse test. |
| Section 6, symmetry | Package response invariance for orbit partitions of every subgroup of the full reward-table automorphism group. Centered permutation covariance is already available. |
| Section 2, paired class | Construct the 33 free nonsingleton coordinates and four free own-singleton levels; expose the sign-only exact-stationary corollary, unique inhomogeneous LCP solution, and strict inclusion beyond full swap symmetry. |
| Section 5, quantitative evaluation | Expose the printed finite-horizon and discounted clock bounds, nonnegative sole-owner discounted bound, and common-prefix punishment debt/target estimates. Qualitative UE does not state these constants. |
| Section 7, literal algebraic fixture | Certify the full reward table, both unique bracketed algebraic roots, residuals, exact payoff, strict inactive inequality and nonsingular active Jacobian. Then prove full 60-coordinate neighborhood persistence. |
| Section 7, fixture consequences | Certify every profitable membership toggle and all-Never response; preserve the root/cap under the canonical recipient shift and positive scaling, without claiming arbitrary-profile translation invariance. |
| Section 8, boundary tests | Formalize the negative sole-owner cap discontinuity and punishment value, singular quotient with nonisolated upper-boundary roots, and weak-inverse example that is not R0. |

The packet's standard ambient Brouwer-degree interpretation still needs the
shared identification/chart adapter. Fixed-chart normalized integer degree
is not silently that identification. Canonical R0 bounds, local indices,
degree sums and stationary complete-response caps should be reused, not
reproved. Source-correspondence prose and nonclaims require no extra theorem.

## Complete-claim audit: passive-row cycle packet

This is static declaration matching, not additional compiler evidence.
The raw strict/weak inverse class, arbitrary-child nonnegative row inheritance,
strict cyclic labeling, literal degree-one fixture and its full open reward
neighborhood are matched. The packet is not complete.

| Source claim | Remaining obligation |
| --- | --- |
| Theorem 1, quiet strategies | Retain outside players' Never actions in the selected uniform witnesses. The weak reward-perturbation proof currently forgets this profile restriction at payoff selection. |
| Strict target and Proof Sections 2-3 | Identify the displayed odds/rates/singleton-only target with the existing cyclic compiler and expose the outside-floor iff for this three-axis cycle. |
| Proof Section 4 | Variable phase subdivision, exact survival products and conditional values, owner equality and full behavioral cap pass targeted checks in `UniformEquilibrium/Quitting/Cycles/RationalSingletonCalendar.lean`. Its hazards are rational functions of the coarse hazards, not necessarily rational numbers for arbitrary real coarse input. |
| Proof Section 5 | Exact censor payoff factor, full-cap/debt estimates including Never, and the date-count bound pass targeted checks in `UniformEquilibrium/Quitting/Cycles/RationalSingletonFiniteCalendar.lean`. Exact rational clock masses pass their law check. The executable calendar-to-law adapter, rational coarse-hazard production and fixed-input asymptotic calendar bound remain. |
| Proof Section 6 | Matched by the targeted-checked arbitrary-signed full-cap and regret bounds in `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineSignedHorizonError.lean`. These do not compare a late negative deviation with its own terminal payoff. |
| Proof Section 7 | Carry quiet actual families through literal weak-inverse reward perturbation, compact fixed-target selection and uniformization. No uniform weak-boundary calendar complexity is asserted. |
| Fin4 counterexample consequence | Expose the raw criterion's contrapositive for every admissible triple and its remaining row. |
| Named class comparisons | Certify the displayed full determinant/inverse, projective Q-bar failure, absence of negative Hamiltonian cycles under every relabeling, and tournament-family exclusion. |
| Four attempted falsifiers | Certify the missing-outside-floor gain, coarse positive joining gain, explicit permutation-inverse boundary family, and paired full-matrix example with no admissible triple. |

The signed horizon task has a reusable starting point:
`expectedStagePayoff_update_le_cutoffTerminal_add_opponentLiveTail`
(`UniformEquilibrium/Quitting/Punishment/NegativeSoloUniformization.lean`)
has no singleton-sign hypothesis. Its actual cutoff replacement is covered
by the same full terminal cap; the finite opponent-tail sum then supplies
the horizon error. This avoids an invalid comparison with a late negative
deviation's own terminal payoff.

The existing eleven-support degree-one fixture inventory and open-neighborhood
proof need no duplicate construction. As above, the ambient degree interpretation
is separate. The packet's exclusions and limitations must remain explicit.

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

The remaining construction uses the exact rational hazards
`q / (n - l * q)`, variable phase lengths, and their ordered cyclic succession.
The existing equal-length geometric subdivision is not that construction.
Mathlib's `finSigmaFinEquiv` already implements ordered prefix-sum flattening;
only the required successor and product adapters need to be supplied.
Rational stopping masses, the verified cutoff selection, the explicit date
bound and its fixed-input asymptotic estimate remain producer obligations.
The cap, censor-payoff and independent-law foundations above should be reused.

## Complete-claim audit: withdrawal and deadline packet

This is static declaration matching, not additional compiler evidence.
The patient, ordinary deadline, evaluated-security deadline and terminal-security
deadline comparisons and fixed-target consumers are matched. Their uniform
witness conclusions retain the actual quiet lift at every requested accuracy.
Ordinary deadline pointwise necessity and its shared-witness refactor pass
their targeted check. Patient necessity also passes its targeted check.
The packet is not complete.

| Source claim | Remaining obligation or matched reuse |
| --- | --- |
| Sections 1-4, patient terminal characterization | The same-fixed-weights pointwise iff and attained-floor witnesses pass targeted checks. This is not a characterization of UE or of every quiet extension; final integration gates remain. |
| Section 3.2, evaluated cancellation | Construct the future-cancellation law, zero-based floor rows, deterministic evaluated comparison and full behavioral debt/family consumers. Deadline atom withdrawal and terminal patient limits do not supply this operation. |
| Section 5, rational security | Expose rational optimal values/optimizers and positive rational approximation at a zero optimizer. The existing real continuous-envelope optimizer and actual security plans remain reusable. |
| Section 5, security examples | Certify the two displayed two-player examples, including the distinction between positive terminal security and the evaluated nonpositive floor. |
| Section 6, omitted Never rows | Retain the joint-Never residual for patient, deadline, security and cancellation routes. Charge it using a positive child singleton and produce the terminal-only relaxed fixed-target/Fin4 consequences. The advancing-only relaxation is narrower. |
| Section 7, rational row feasibility | Encode patient/deadline/security rows over the paired weights, certify rational floors and specialize the existing real/rational finite-inequality equivalence. |
| Section 7, actual finite-law search | Supply the complete rational product-law dovetail, unrestricted-cap acceptance and termination from child UE. Scan every consecutive date, one post-calendar date and Never, including calendar length zero; preserve strict acceptance and the computed parent amplification. This is target-free, not an algorithm for an arbitrary specified real target. |
| Sections 8.1-8.2, incomparable cones | Certify both literal tables, their positive raw certificates and the incompatible inequalities excluding the other criterion. |
| Section 8.3, evaluated patient falsifier | Certify the actual horizon-three, discounted and terminal full caps. A profitable sample response alone does not give the displayed complete regret values. |
| Sections 8.4-8.5 | The missing-Never table is matched by `CappedClockMissingNeverFixture`; the sparse-date gap and full cap are matched by `SparseCalendarReplyGap`. These calculations need no duplicate proofs. |
| Section 9, strict patient class | Certify the literal table, floors, weights, exact slacks, debt coefficients and all fourteen advancing-only proper-child obstructions. Prove their persistence on the specified full reward neighborhood of radius `1/100`. |
| Section 9.3, actual patient-center profile | Certify the displayed date-zero profile and every prescribed, Quit-zero, Never and later response value, then reuse exact terminal Nash and same-profile uniformization. |
| Section 10, strict deadline class | Certify the literal translated table with Never unchanged, exact rows and mixed-response probabilities, every proper-child advancing-only obstruction, and persistence on the specified full reward neighborhood of radius `1/512`. |
| Section 10.3, actual deadline-center profile | Certify all displayed complete response values, retaining the sure owner's distinct Never and later-date payoffs, then reuse the existing Nash/uniformization consumers. |
| Section 10.4, collision freedom | Construct completions for all 33 freely assigned child-recipient nonsingleton coordinates, with a nonempty open region in the remaining eleven coordinates. This does not assert every completion passes. |
| Section 11.1, matrix properties | Identify both centers with the existing paired matrix, then prove positive inverse/determinant and degree one throughout the specified numerical neighborhoods. Reuse the existing matrix and R0 degree proofs. |
| Section 11.1, response partitions | Certify both literal residual witnesses, the reward perturbation constants and exclusion of every nondiscrete response-invariant partition throughout both neighborhoods. Matrix degree alone does not imply these conclusions. |

Rational feasibility can reuse
`exists_rationalNonnegativePotential_iff_exists_realNonnegativePotential`
(`MathUE/DirectedTransport/FiniteInequality/Nonnegative.lean`). The finite-law
search can reuse full-cap finite-menu approximation, rational simplex density,
the consecutive-calendar full reply cap and the exact rational finite-word
semantic evaluator. Existing reciprocal-parameter and supplied-iteration scans
are not the packet's exhaustive rational-law producer.

`patientWithdrawalOwnNeverAlternative`, `patientWithdrawalFloor` and
`patientWithdrawalGainFloor`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalRaw.lean`)
already cover the finite patient floors, including a one-player child.
The deadline zero floor has the corresponding inserted zero alternative.
The independent clock representation, full behavioral caps, general Never
charge, existing security-plan construction, and low-cardinality child
existence are matched foundations, not further proof tasks.

## Complete-claim audit: paired collision reward packet

This inventory follows the complete packet, including its exact finite-law
conclusions. The parameterized table, low-parameter and pure exits, scalar
rate construction, stationary and periodic branches, all-parameter consumer,
and class comparisons have implementation drafts. The parameterized source
table, scalar rates, stationary and periodic branches, all-real-parameter
existence consumer, and class exclusions pass their targeted checks. Exact
finite-law claims and a literal normality corollary remain. The packet is not
complete.

| Source claim | Completion obligation |
| --- | --- |
| Sections 1-2, literal source and exits | Targeted checks pass for the fifteen reward vectors, twelve varying pair-member coordinates, constant singleton matrix, signed `c ≤ 1` and pure `c ≥ 4` consumers. |
| Sections 3-4, produced rates | Both scalar intermediate-value constructions, positive denominators and interior-rate bounds pass targeted checks. The final existence theorem constructs its rates from `1 ≤ c ≤ 2`, rather than accepting them as a hypothesis. |
| Section 5, infinite equilibrium | Phase/owner endpoints, prescribed recursions, strict quiet joins, actual payoff identification, every suffix's unrestricted behavioral cap and the same profile's uniform payoff pass targeted checks. |
| Section 5, exact finite laws | Construct the independent finite-date-or-Never marginals with the displayed rational-in-the-rates masses. Prove the exact prescribed payoff factor, the full cap equality `B_i^K = v_i`, and maximum debt `C^K max_i v_i`. A generic censor cap estimate is weaker than this equality. |
| Section 5, finite horizons | Prove the literal `8K/N` delivery and deviation comparison, `16K/N` regret charge, and accuracy-dependent finite-law witnesses at one fixed target. The censored opponents have positive Never mass; they are not geometrically absorbing. |
| Section 6, stationary branch | Targeted checks pass for actual Quit and Continue sums, interval endpoint signs, produced common hazard, full behavioral cap, Bellman value and fixed uniform payoff for `2 ≤ c ≤ 4`. |
| Sections 2 and 7, exclusions | Targeted checks pass for pure-clock obstruction, the punishment-value bound, all-rate solo joining, capped-joint and low-active failures, every relabeling's raw-region failure, and weak singleton payoff-exclusion failure in `UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardBoundary.lean`. Package the value bound and unit own singleton as a literal normality corollary. |
| Sections 1 and 8-9, assembled conclusion | Targeted check passes for the four actual exits for every real input parameter on the same table, retaining overlapping endpoints and arbitrarily negative parameters. This does not cover arbitrary collision rewards. |

The existing periodic compiler, complete stationary cap, finite cyclic-word
payoff identity, independent finite-clock realization, and finite-deadline
horizon estimates should be reused. The sharper finite cap equality needs
both its before/after-support upper bound and an actual retained active-date
response attaining the initial value. Neither a supplied cap field nor a
generic error bound proves that equality.

## Retirement criterion

Retirement requires matching every mathematical conclusion above to an
integrated checked declaration or an explicitly checked composition, with
the packet's hypotheses, quantifiers, strategy restrictions and numerical
bounds. Definitions and standard background may reuse existing interfaces;
they do not require duplicate proofs. A conditional compiler is not an
actual-data producer, and payoff existence is not a retained-strategy theorem.
The first-dependency table by itself supplies no retirement evidence.
