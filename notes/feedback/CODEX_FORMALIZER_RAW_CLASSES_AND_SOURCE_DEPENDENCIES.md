# Raw existence classes and counterexample-source dependencies

This is a formalization dependency audit of the packets named below, not a
proof-completion record. The packet arguments have been read in full. New
conclusions remain to be proved in Lean unless an existing declaration is
explicitly identified. No packet is closed by this audit.

## Independent branches

| Packet family | Mathematical output | Main formalization dependency |
| --- | --- | --- |
| Capped clocks and withdrawal | Raw reward criteria extending child uniform payoffs, including signed rewards | Actual private-clock replacements and full-regret comparison |
| Three-player cycle passive rows | Uniform payoff from an inverse-positive triple and nonnegative outside row coefficients | Extend the existing balanced cycle; strictify the weak inverse boundary |
| Stationary-response quotient | Absorbing stationary Nash–Bellman root; signed Fin4 uniform payoff | Constructed integer degree, quotient lift, and original-player endpoint adapter |
| Guarded crossed response, A–C | Interior stationary equilibrium and weak-boundary approximations | Constructed integer degree and raw guards excluding artificial roots |
| Guarded crossed response, D | Fin4 uniform payoff from sixteen weak reward comparisons | Finite outsider joining-game Nash and existing signed punishment consumers |
| Generic screened-root exclusion | Generic fiber, strict screened-root gap, and positive total singleton mass near minimum | Bilinear cofactor obstruction, exact product-base realization, and compactness |
| Single-pivot secant | One fixed source with a positive pivot mass bound and negative pivot response pressure | One-coordinate full-cap secant and scalar common-calendar selection |
| Potential-shape exclusions | Necessary shape and curvature properties of a full-root potential | Collision-adjusted singleton probes and finite-dimensional analysis |

The degree-free branches need not wait for integer degree. Conversely, a
matrix-free existence result does not replace a stronger stationary conclusion.

## Quiet extensions

Sources:

- `CAPPED_CLOCK_DEVIATION_DOMINATION_AND_QUIET_EXTENSION.md`;
- `WITHDRAWAL_AND_DEADLINE_QUIET_EXTENSIONS.md`.

The common implementation starts with the deterministic first-outcome
comparison under the raw Never, future, and joining rows. It then constructs
private pushforward laws and integrates separate unilateral experiments.
The common sampled outside deadline is a proof coupling, not public
correlation in the played profile.

The deterministic comparison is proved by
`cappedClockActualEvaluatedOutsideGain_le_weighted_actualChildGain`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`).
Its `CappedClockParentRewardCertificate` reads the three inequalities from
the parent reward table. The conclusion uses actual first stopping times
and coalitions, including ties and joint Never, for every nonnegative
antitone evaluation and arbitrary signed rewards. Terminal domination is
its specialization, `cappedClockActualOutsideGain_le_weighted_actualChildGain`
in the same file.

`cappedClockStoppingLaw` constructs the independent minimum pushforward;
`quittingBehaviorStoppingLaw_cappedClockStrategy` realizes it by an actual
behavioral strategy, and `cappedClockStoppingLaw_survival` proves the
product formula for inclusive survival
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockStoppingLaw.lean`).
`expect_cappedClockStoppingLaw_of_bounded` in that file supplies the bounded
iterated-expectation identity.

`expect_cappedClockActualEvaluatedOutsideGain_le_sum_childExpectations`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockExpectationDomination.lean`)
integrates the gain inequality over any coupled child/outsider clock law.
Reward and evaluation bounds supply summability internally. This stronger
integration statement does not make correlated clock laws legal profiles;
the behavioral application uses independent laws.
The finite sum is interchanged with expectation using
`expect_finset_sum_of_bounded`
(`MathUE/ProbabilityMassFunction/FiniteSumExpectation.lean`).

`map_pmfPi_cappedClockParentSourceLaws_quiet` and
`map_pmfPi_cappedClockParentSourceLaws_cappedChild`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockParentLawPushforward.lean`)
identify the exact product laws after discarding the outsider clock, or first
using it to cap one child. The latter replaces precisely that child's marginal
by the compiled minimum law.

`expect_parentSource_cappedChild_eq_stoppingLawExpectedPayoff` and
`cappedChild_stoppingLawExpectedPayoff_le_behaviorDeviationCap`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockActualPayoffAdapter.lean`)
identify the capped-child expectation with an actual behavioral deviation
payoff and bound it by the full behavioral cap.
`outsideBehaviorDeviationDebt_le_weighted_childBehaviorDeviationDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockFullBehavioralCap.lean`)
then bounds the outsider's full terminal deviation debt by the weighted
survivor debts at the reconstructed quiet parent profile. It first bounds
every outsider strategy and then takes the supremum. Neither cap attainment
nor a supremum/expectation interchange is assumed.

`quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockChildDeletionAdapter.lean`)
transports this bound to the actual Never lift of any child behavioral
profile, with the child game's unrestricted debts on the right side.
`quittingBehaviorStoppingLaws_liftDeletedProfile_eq_quiet` in the same file
supplies the actual-law identification. The relaxed Never-row criterion and
the remaining packet conclusions are not supplied by this debt theorem;
neither packet is closed yet.

The child-game adapter reuses
`quittingTerminalPayoff_liftDeletedProfile`,
`quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation`, and
`quittingBestReplyValue_liftDeletedProfile`
(`UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`).
They already preserve survivor payoffs and full behavioral best-response
values under the Never lift. `quittingBestReplyValue`
(`UniformEquilibrium/Quitting/Stationary/MinMax.lean`) and
`quittingBehaviorDeviationPayoffCap`
(`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`) describe
the same supremum, using indexed-supremum and range-supremum notation.
`quittingBehaviorDeviationDebt_liftDeletedProfile` and
`quittingBehaviorStoppingLaw_liftDeletedProfile` in the deletion-lift file
expose debt and stopping-law preservation directly.
`quittingTerminalPayoff_eq_of_behaviorStoppingLaws_eq` and
`quittingBehaviorDeviationPayoffCap_eq_of_behaviorStoppingLaws_eq`
(`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`)
transport payoff and full-cap conclusions between arbitrary actual profiles
with equal complete stopping laws. No equality on unreachable histories is
required.

For fixed targets,
`exists_uniformEquilibriumPayoff_eq_on_image_of_terminalNash_lift`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalNashLift.lean`)
extracts one parent payoff from a payoff-preserving profile lift with a fixed
multiple of terminal Nash error. It preserves every mapped coordinate of
the specified child target. The player map need not be injective.
`isεAsymptoticNash_quietLift_of_cappedClockCertificate` and
`exists_uniformEquilibriumPayoff_eq_some_of_cappedClockCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockFixedTargetQuietExtension.lean`)
apply this construction to the actual Never lift, with common error factor
the maximum of one and the sum of certificate weights.
`exists_uniformEquilibriumPayoff_eq_on_survivors_of_blockDispensable`
(`UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`) uses the
same generic compactness theorem with factor one and its existing
dispensability hypothesis. The capped-clock criterion does not assume or
claim that deletion gate.

The raw four-player consumer
`quittingGame_exists_uniformEquilibriumPayoff_of_finFour_cappedClockCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockFinFourExistence.lean`)
requires only a certificate on the reward table reindexed around a specified
owner. It supplies child existence using
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three`
(`UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`) directly on
the survivor type after proving its cardinality, then applies fixed-target
quiet extension and reindexes the resulting parent payoff back to Fin4.
No child strategy or equilibrium witness is an extra premise. For specified targets,
`isUniformEquilibriumPayoff_of_reindex`
(`UniformEquilibrium/Quitting/Classification/PlayerReindexNaturality.lean`)
already supplies payoff-preserving reindexing.

The advancing-only theorem is an all-evaluation specialization of both
withdrawal criteria. The patient and deadline criteria themselves are
incomparable. Patient withdrawal controls terminal regret with summed
coefficients. Deadline withdrawal controls nonincreasing evaluations with
maximum coefficients, using disjoint private-clock events. The patient
payoff limit must not be replaced by the payoff of its limiting Never law.

Reuse `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws` and
`quittingBehaviorDeviationPayoffCap_eq_pureTime`
(`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`).
Reuse `prod_stoppingLaw_none_mul_singleton_le_terminalDebt`
(`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`) for the
terminal relaxation. Low-cardinality child existence and target-preserving
terminal uniformization are existing consumers, not new premises to assume.

## Stationary residual and degree

Sources:

- `STATIONARY_RESPONSE_QUOTIENT_DEGREE_ESCAPE.md`;
- `GUARDED_CROSSED_RESPONSE_DEGREE_ESCAPE.md`;
- `THREE_PLAYER_CYCLE_PASSIVE_ROW_EXTENSION.md`.

Do not define another stationary residual polynomial.
`quittingFaceNumerator`
(`UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean`) is the required
residual. The zero-discount displacement and its existing ambient derivative
provide another presentation of the same polynomial. The absorbing stationary
payoff identity needs an adapter: a theorem requiring strictly positive
discount cannot simply be specialized to zero.

The crossed packet's Theorem D first fixes one player sure and a second at
Never, and produces the outsiders' finite joining Nash equilibrium. A nonzero
outsider hazard supplies deleted-clock contraction. The sole-owner branch
supplies all outsider no-join inequalities. Under no Fin4 uniform payoff,
`finFour_punishment_le_singleton_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`)
then supplies the owner inequality consumed by
`isUniformEquilibriumPayoff_soloReward_of_instantPunishment`
(`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`). This proves
existence without degree or a matrix assumption. It does not assert exact
stationary attainment in the negative sole-owner branch.

The triple-row extension likewise has a degree-independent existence proof.
Its cycle should extend `BalancedSingletonCycleCertificate`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`), not
duplicate the cycle compiler. Nonnegative outside coefficients need not sum
to one. The example's integer-degree calculation is a separate conclusion.

The checked topology endpoint is
`IsContinuousBoxComplementarityFamily.eventually_localSignedCount_endpoints_eq`
(`Research/Topology/BoxComplementarityLocalSignedHomotopy.lean`): equality
at every sufficiently fine common resolution.
`BoxComplementarityProblem.eventually_localSignedCount_eq`
(`Research/Topology/BoxComplementarityFloorRefinementSignedTransport.lean`)
also compares arbitrary independently sufficiently fine resolutions.
`BoxComplementarityProblem.localDegree` and
`IsContinuousBoxComplementarityFamily.localDegree_endpoints_eq`
(`Research/Topology/BoxComplementarityStabilizedLocalDegree.lean`) package
the resulting integer and its homotopy invariance on a common isolating region.
Affine normalization and approximation independence remain separate
obligations. The refinement specification belongs with
`CODEX_FORMALIZER_SIGNED_LOCAL_DEGREE_SPEC.md` and
`CODEX_FORMALIZER_SIGNED_DEGREE_DISCOVERY_MAP.md`.

## Two different singleton-source selections

Sources:

- `GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md`;
- `SINGLE_PIVOT_SECANT_COLLAR_AND_STRICT_PRESSURE.md`.

The generic route uses 24 bilinear-branch cofactor factors to exclude equal
positive complete debts at every two-sure product root. The all-player tie
theorem turns this into a strict gap on an entire own-singleton fiber.
At a zero-singleton carrier minimum, prove zero Never before applying
`exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
(`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`).
Compact positivity then supplies the near-minimum singleton-mass bound.

The single-pivot secant bypasses that polynomial and product-base argument
for its pivot-specific mass bound. It selects a descending tilted window,
not a maximizer over the whole singleton fiber. Its pressure is strictly
negative for the pivot; the generic source has a nonpositive total pressure.
Neither output silently includes the other selection's fields.

Both use common-calendar optimization and the complete finite-clock
approximation in `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`.
That dependency must be coherently promoted before a production module
imports it. The selected fixed table precedes every accuracy and depth.
Weights transported from nearby tables need not be fresh softmax weights
at the final table.

The pivot delay preserves its own cap and loses a positive amount of pivot
singleton mass, but can increase outsider debts. No renewable descent or
uniform-equilibrium proof follows without controlling those debts.

## Potential exclusions

Sources:

- `QUITTING_POTENTIAL_SHAPE_EXCLUSIONS.md`;
- `REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md`.

Share the collision-adjusted single-quitter probe and minimum-localization
lemmas. The first packet excludes quasiconvex full-root potentials without
a matrix assumption. Its separate face-only exclusion and quantitative
curvature consequences have additional matrix hypotheses. The second packet
excludes quadratic and multiaffine potentials under its nonnegative
singleton normalization and gives a reflection constraint.

Face-only inequalities and the full exact-root inequality are different
premises. Rational approximate-root witnesses must not be described as exact
roots. These exclusions restrict a potential certificate; they do not
exclude every polynomial degree or prove arbitrary Fin4 existence.
