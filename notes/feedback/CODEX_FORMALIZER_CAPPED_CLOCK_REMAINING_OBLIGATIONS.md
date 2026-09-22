# Capped-clock packet: remaining formalization obligations

The source is
`math/exports/CAPPED_CLOCK_DEVIATION_DOMINATION_AND_QUIET_EXTENSION.md`.
The packet is not fully formalized. The integrated interfaces and source
constructors are described in [the toolkit](../../docs/TOOLKIT.md).

## Checked scope

The deterministic and expected-clock inequalities allow general nonnegative
nonincreasing evaluations. So does the actual full behavioral-cap comparison
at reconstructed quiet parent profiles, by
`outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockEvaluatedFullBehavioralCap.lean`).
Its right side contains survivor debts in the parent game.
`quittingBehaviorEvaluatedDeviationDebt_liftDeletedProfile`
(`UniformEquilibrium/Quitting/Classification/PlayerDeletionEvaluatedPayoff.lean`)
preserves survivor debts under the existing Never lift for arbitrary clock
evaluations and arbitrary deleted-player predicates.
`quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockEvaluatedChildDeletionAdapter.lean`)
combines these results for every actual child behavioral profile, with debts
in the literal deleted child game on its right side. Its evaluation is
nonnegative and nonincreasing. The terminal adapter supplies the checked
fixed-target quiet-extension and four-player existence theorems.

`quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_error`
in the same evaluated child-deletion adapter transports a common reward-row
error to the actual Never lift and unrestricted behavioral debts. It charges
the row error times the evaluation at time zero, not twice that amount.
The `quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_rowError`
corollary charges just the row error when the evaluation at zero is at most
one. Separate Never/future/joining errors share the deterministic proof in
`CappedClockPointwiseDomination.lean`; the older Never-only theorem retains
its sharper clock-dependent correction. The cap transport factors through
one common-allowance argument instead of duplicating the exact proof.

The raw reward criterion has exact real and rational LP alternatives. Its
zero-weight case is equivalent to exact singleton block dispensability.
`cappedClockExpectedActualGain_le_iff_rewardRows`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockExpectationNecessity.lean`)
characterizes universal terminal expectation domination by the same fixed
nonnegative weights and reward rows. Dirac laws supply necessity; this is
not a necessity theorem for arbitrary behavioral debt comparisons.
The paired-family constructor preserves arbitrary nonsingleton coordinates
of the three surviving players and supplies a uniform-equilibrium payoff.
Every member fails exact singleton block deletion for every player.
The family and its deletion-3 child admit no balanced singleton cycle of any
period, by `not_nonempty_balancedSingletonCycleCertificate` and
`not_nonempty_balancedSingletonCycleCertificate_deleteThree`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedCycleExclusion.lean`).

The explicit positive fixture's one-date profile, followed by Never, has
both terminal payoff and unrestricted behavioral best-response value
`![13 / 9, 2, 2 / 3, 4 / 3]`. Its literal semantic results are
`CappedClockPairedFixtureTerminal.profile_terminalPayoff`,
`CappedClockPairedFixtureTerminal.profile_continuationBestResponseValue`, and
`CappedClockPairedFixtureTerminal.profile_exactTerminalNash`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedFixtureTerminal.lean`).
The module passed a silent named build.

The complete pure-date reply values are also proved in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedFixturePureReplies.lean`:
`pureReplyValue_zero`, `pureReplyValue_some_succ`, and `pureReplyValue_none`
distinguish immediate quitting, every strictly later finite date, and Never.
This module passed a silent named build and reuses the canonical root-prefix
payoff identities; it does not restrict the full behavioral caps above.

The exact Never, future, and joining margins, and every singleton deletion's
own payoff, continue floor, and joining cap, are proved in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedFixtureSlacks.lean`.
`futureSlack_eq_certificateMargin` and `joinSlack_eq_certificateMargin`
identify the displayed numbers with the actual weighted reward-row expressions.
The module passed a silent named build.

The reusable pure-clock obstruction is also proved:
`HasQuittingPureTimeMembershipToggleGap.exists_behaviorDeviation`
(`UniformEquilibrium/Quitting/Paths/PureTimeMembershipToggleObstruction.lean`)
turns one solo escape and a joining or nonterminal leaving gain at every
nonempty coalition into an actual behavioral deviation against every complete
pure-clock profile. The same gain lower bound holds at arbitrary deterministic
dates and Never. A positive gap excludes exact terminal Nash in this pure
class; no exclusion of mixed behavioral profiles is asserted.
`CappedClockPairedFixtureNoPureTerminal.membershipToggleGap_one` and
`CappedClockPairedFixtureNoPureTerminal.exists_behaviorDeviation_gain_one`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedFixtureNoPureTerminal.lean`)
give the fixture's literal row certificate and a gain of at least one against
every complete pure-clock profile. Both modules passed silent named builds.

Reward-neighborhood statements are proved in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedFixtureRobustness.lean`:

- `certificate_of_reward_close` preserves the actual weight-two certificate
  for entrywise radius below one sixth, with singleton coordinates allowed
  to vary. `exists_uniformEquilibriumPayoff_of_reward_close` consumes it to
  supply a fixed uniform payoff for each nearby game.
- `not_isεAsymptoticNash_zero_of_reward_close` excludes every complete pure
  clock at radius below one half. `profile_terminalNash_of_reward_close`
  instead concerns the fixture's one mixed profile, whose error against all
  behavioral deviations is at most twice the radius. It is not asserted to
  remain an exact equilibrium or realize the nearby game's uniform payoff.
- `not_nonempty_balancedSingletonCycleCertificate_delete_of_reward_close`
  excludes every period on every principal player restriction below radius
  one half. The parent exclusion is also proved.
- `not_blockDispensable_of_reward_close` and
  `not_cappedJointExit_of_reward_close` exclude exact singleton deletion and
  the capped joint-exit hypothesis below radius one. The latter uses the
  packet's coalition `{0,2}` witness, not a claim about other hypotheses of
  the cited theorem.

The module passed a silent named build and independent declaration-level
review. The generic membership-toggle reward transport is shared through
`HasQuittingPureTimeMembershipToggleGap.of_reward_close`
(`UniformEquilibrium/Quitting/Paths/PureTimeMembershipToggleObstruction.lean`).

`AdaptiveChildCenterCappedClockObstruction.not_nonempty_cappedClockParentFutureJoinCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/AdaptiveChildCenterCappedClockObstruction.lean`)
proves that every deletion of the existing adaptive-child center table fails
the weighted future/join system, even without its Never row. The raw
certificate also fails for every deletion. The proof reuses
`AdaptiveChildCenter.reward`; its already proved equilibrium and uniform
payoff do not need a second construction. This module passed a silent named
build and independent declaration-level review.

`CappedClockMissingNeverFixture.futureJoinCertificate`,
`CappedClockMissingNeverFixture.childProfile_exactTerminalNash`, and
`CappedClockMissingNeverFixture.liftedProfile_outsiderDebt_eq_one`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockMissingNeverFixture.lean`)
give the packet's one-child counterexample without Never protection. The
child's rewards are zero, the future/join weights are zero, and the actual
quiet lift has outsider debt exactly one. `neverExcess_eq_one` identifies
the omitted row's positive residual. The literal fixture passed a silent
named build. Its Never-law identity is shared with the deletion machinery
through `quittingBehaviorStoppingLaw_pureTime_never`
(`UniformEquilibrium/Quitting/Paths/StoppingLawReconstruction.lean`).

`SparseCalendarReplyGap.replyValue_eq`
(`UniformEquilibrium/Quitting/Examples/SparseCalendarReplyGap.lean`) proves
the complete pure-date reply formula for the literal sparse stopping-law
profile: date one gives one half, date two gives minus one half, and every
other finite date and Never give zero. `displayed_replyValues` recovers the
five entries in the packet. `profile_payoff_false_eq_zero` and
`behaviorDeviationPayoffCap_false_eq_half` in the same file give the actual
prescribed payoff and unrestricted behavioral cap. `sparseTestedReplyCap_eq_zero`
and `behaviorCap_sub_sparseTestedReplyCap_eq_half` show that testing only
Never and dates zero, two, and three misses a gain of exactly one half.
These proofs passed a silent named build and reuse the existing
product-of-pure-laws mixture identity and pure-time extremality theorem.
The literal third-player extension is also proved there:
`extendedReplyValue_eq_replyValue` preserves every deterministic reply,
`extendedProfile_child_behaviorCap` preserves both old players' unrestricted
behavioral caps, and `extendedBehaviorCap_sub_sparseTestedReplyCap_eq_half`
retains the same half-unit gap in the extended game.
`extendedProfile_fresh_stoppingLaw` identifies the fresh player's actual law
with Never. These declarations passed a silent named build and independent
declaration-level review. Equal-reward transport of pure-time reply payoffs
is shared through `quittingTerminalPayoff_update_pureTime_profileOfRewardEq`
(`UniformEquilibrium/Quitting/Classification/PlayerReindexNaturality.lean`).

The consecutive-calendar repair is already proved by
`quittingContinuationBestResponseValue_finiteDeadlineTimingProfile_eq_max`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineFullReplyCap.lean`).
It identifies the unrestricted behavioral cap with the maximum over all
dates below the deadline and Never, together with the one late-row value.
`quittingFiniteDeadlineTimingProfile_pureTime_eq_never_add_of_le` in the
same file shows that every finite date at or after the deadline realizes
that late row. Thus the deadline itself completes the consecutive menu,
including when the deadline is zero. The separate sparse-calendar rule
is proved by
`exists_mem_quittingFiniteOpponentAtomGapReplyMenu_payoff_eq` and
`exists_mem_quittingFiniteOpponentAtomGapReplyMenu_payoff_eq_cap`
(`UniformEquilibrium/Quitting/Terminal/FiniteOpponentAtomGapReplyMenu.lean`).
The concrete menu consists of Never, zero, the opponent atoms, and their
immediate successors. Every deterministic reply has an equal-payoff menu
representative, and the unrestricted behavioral cap is attained in the menu.
The calendar need cover only opponents' finite atoms; the responder's
original law is unrestricted. These declarations passed a silent named build.
`exists_mem_quittingFiniteOpponentAtomGapReplyMenu_actual_payoff_eq_cap`
in the same file states attainment for any actual behavioral profile whose
opponents' stopping laws satisfy the calendar condition. It passed a silent
named build and reuses canonical stopping-law reconstruction. The law-level
menu proofs also passed independent static review. These are terminal-payoff
statements; moving a reply within a gap need not preserve a time-weighted
evaluation.

The strict three-cycle algebra is proved in
`MathUE/LinearProgramming/ThreeCycleInverseFormulas.lean`.
`directedCycleMatrix_inverse` gives the actual inverse, including the
singular zero-inverse convention. `columnWeight_vecMul` and
`columnWeight_balances` give its column-sum identities.
`fractions_pos_lt_one_add_eq_one`, `prod_survivalFraction`, and
`cycle_productRatio_mem_Ioo` prove the algebraic absorption/survival
fractions and their strict product contraction. The existing three-player
Q classification uses the same matrix definition. These formulas passed a
silent named build. Their identification with the blocks of an arbitrary
actual infinite schedule is supplied by the path results below.

`weight_le_inverseRow_of_singletonFutureRows` and
`inverseRow_nonneg_of_singletonFutureRows`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockInverseRowObstruction.lean`)
prove the inverse-row obstruction from singleton future inequalities alone.
The child may have any finite cardinality; its inverse need only be
nonnegative, not strictly positive. The weight comparison even permits
signed weights, while nonnegativity is used for the inverse-row sign
conclusion. Both existing capped-clock certificate types have direct
corollaries. Neither joining nor Never protection is needed by the core
result. The module passed a silent named build and independent static review.

`NormalizedSingletonPath.exists_active_owner_ne` and
`NormalizedSingletonPath.exists_first_owner_change`
(`MathUE/LinearProgramming/ThreeCyclePathRigidity.lean`) rule out a final
single-owner block and construct the first finite owner change for arbitrary
finite player sets. Their data are a normalized nonnegative recurrence,
hazards strictly below one, exact active-coordinate equalities, and vanishing
tail survival. Zero-hazard gaps are unrestricted; finite blocks are not a
premise. `exists_first_cyclic_owner_change` in the same file proves the
forced cyclic direction for the strict three-cycle matrix and the two zero
coordinates at the switching boundary. These declarations passed a silent
named build; the generic path proofs also passed an independent
declaration-level review.

`ThreeCycleInverseFormulas.exists_vertex_after` in the same file proves that
each of the three weighted simplex vertices is reached at a finite date
after every starting date. It constructs the visits from three finite cyclic
owner changes. `dotProduct_nonneg_on_tail_iff` consequently characterizes
nonnegativity of an arbitrary signed row on the entire tail by nonnegativity
of all three coefficients. These declarations passed a silent named build
and independent declaration-level review.

`NormalizedSingletonPath.value_eq_survival_affine_of_same_owner` in the same
file merges any finite same-positive-owner window into its exact affine
recurrence, allowing zero-hazard gaps and zero-length windows.
`ThreeCycleInverseFormulas.survivalFraction_le_window_survival` gives the
partial-block survival lower bound, and `window_survival_eq_survivalFraction`
gives equality at the complete-block endpoints.
`exists_vertex_after_with_survival_ge` constructs a visit to every requested
vertex from every starting date with survival at least the product of the
three canonical fractions. The initial positive date is chosen minimally,
so its preceding zero-hazard gap costs no survival. These declarations
passed silent named builds. The finite recurrence and block bounds also
passed independent static review.

`normalizedSingletonPathOfRootSequence`
(`UniformEquilibrium/Quitting/Paths/NormalizedSingletonPath.lean`) constructs
that path from the actual terminal payoffs of an arbitrary finite embedded
child in the parent game. Initial absorption and hazards below one give
absorption at every suffix. The actual singleton recurrence and column
balance give weighted surplus one; singleton floors and exact active ties
then supply the normalized nonnegative path. No periodicity or vertex visits
are assumed. `quittingRootSequenceSingletonSurplus_weightedSum_eq_one`
in the same file proves the normalization identity even for signed weights,
without singleton floors or active ties.
`quittingRootSequenceSingletonSurplus_eq_of_row_span` transports any signed
linear relation among the child singleton rows to actual parent surpluses;
`quittingRootSequenceSingletonSurplus_eq_inverseRow` specializes it to the
actual inverse. Both apply to every parent coordinate and require neither
singleton floors nor active ties. The row-span theorem also applies to
singular child matrices when the stated row relation holds; invertibility
is needed only for the inverse formula. These adapters passed silent named builds
and independent declaration-level review.
`quittingRootSequence_singletonFloor_on_tail_iff_inverseRow_nonneg_of_strictThreeCycle`
(`UniformEquilibrium/Quitting/Paths/StrictThreeCycleSingletonFloor.lean`)
combines these results for an actual embedded strict three-cycle child.
For every parent player and every starting date, its continuation stays
above its own singleton payoff on the entire tail exactly when all entries
of its actual inverse row are nonnegative. The player need not be outside
the child. The theorem passed a silent named build and independent static
review. The generic
solo-root recognizer has one canonical owner in
`UniformEquilibrium/Quitting/Stationary/SingletonStationaryRoot.lean`.

`quittingBehaviorDeviationDebt_ge_of_strictThreeCycle`
(`UniformEquilibrium/Quitting/Terminal/StrictThreeCycleDeadlineResponseDebt.lean`)
gives the actual outside player's unrestricted behavioral response-debt
bound at the initial profile. The lower bound is the canonical survival
product times the positive part of its inverse-row deficit minus twice
the reward bound times the hazard bound. The proof uses an actual
deterministic deadline on this same schedule. It passed a silent named
build and independent static semantic review. Public deadline-witness
and arbitrary-start statements remain to be exposed.

## Work still needed

The terminating child-first rational search and its original-parent consumer
are proved in Research, including exact Never preservation and rational
amplification selection. Their scope is recorded in
[the rational producer note](CODEX_FORMALIZER_CAPPED_CLOCK_RATIONAL_PRODUCER.md).
The response-debt bound is proved at the initial profile. Its positive
deterministic-deadline witness and its arbitrary-start version on the same
fixed schedule still need public statements.
The matrix algebra, forced vertex visits, and actual continuation-floor
equivalence are proved as described above. Its hypotheses concern an exact
balanced singleton schedule, not all child equilibria or approximate ties.

A declaration-level audit also identified three useful source conclusions
that still need explicit adapters:

- Compose the existing three-player cyclic labeling theorem with strict
  inverse positivity, rather than asking callers for standard-Q and
  homogeneous-solution exclusions separately. The matrix classification
  itself is already proved in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicLabelAdapter.lean`;
  the inverse-positive implications are in
  `UniformEquilibrium/Quitting/Classification/LCP/PositiveInverse.lean`.
- Apply the actual path results to a periodic balanced certificate on the
  **child** reward and its parent Never lift. Actual-value uniqueness and
  periodic absorption are already available in the cycle machinery. A
  certificate on the full parent would assume the outsider floor being tested.
- Expose the full-child joining obstruction and construct a reward change
  at the outsider's full-parent collision coordinate that violates it while
  preserving singleton entries. This is separate from the paired-family
  obstruction to balanced cycles.

These are missing Lean compositions or finite-table constructions from the
packet, not missing source mathematics. They must not be replaced by an
implicit appeal to the reader to assemble the required conclusion.

The strict inverse-row work uses the existing three-cycle labeling,
singleton-versus-quit payoff estimate, and survival-weighted deviation
transport. Both the survival lower bound and its initial-profile full-debt
consumer are proved without supplied vertex visits or periodicity. The
remaining adapters must retain that scope.

These are known results supplied by the packet. This record does not assert
that the weighted criterion covers every four-player game, that its weights
are optimal, or that a finite-calendar implementation is complete without
testing the intervening gaps.
