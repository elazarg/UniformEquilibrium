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

## Work still needed

The terminating child-first rational search and its original-parent consumer
are proved in Research, including exact Never preservation and rational
amplification selection. Their scope is recorded in
[the rational producer note](CODEX_FORMALIZER_CAPPED_CLOCK_RATIONAL_PRODUCER.md).
The remaining packet work is:

1. Formalize the missing-Never example with zero child singleton and the
   sparse-calendar missed response with its consecutive repair.
2. Formalize the auxiliary strict inverse-row sharpness theorem: the positive
   inverse classification, forced vertex visits and block survival, the
   continuation-floor equivalence, and the quantitative response-debt bound.
   Its hypotheses concern an exact balanced singleton schedule, not all child
   equilibria or approximate ties.

The strict inverse-row work can reuse the existing three-cycle labeling,
periodic escort transitions, singleton-versus-quit payoff estimate, and
survival-weighted deviation transport. What remains includes the universal
infinite schedule's finite owner blocks, forced vertex visits, and uniform
survival lower bound. A theorem assuming the vertex visits or restricting
the schedule to a finite period would not cover the packet's statement.

These are known results supplied by the packet. This record does not assert
that the weighted criterion covers every four-player game, that its weights
are optimal, or that a finite-calendar implementation is complete without
testing the intervening gaps.
