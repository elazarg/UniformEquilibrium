# Deadline withdrawal: source and semantic scope

The source is `math/formalized/WITHDRAWAL_AND_DEADLINE_QUIET_EXTENSIONS.md`,
especially its raw deadline rows and all-evaluation debt comparison. The
canonical chain defines the actual atom withdrawal, constructs its legal
mixed stopping-law response, and transports the literal reward inequalities
to complete behavioral debts and fixed-target quiet witnesses. Its hypotheses
are finite raw reward-table inequalities, not supplied strategies, payoff
caps or favorable continuation profiles.

## Actual operation and deterministic comparison

`deadlineWithdrawnClock`, `deadlineWithdrawalZeroFloor`,
`deadlineWithdrawalGainFloor`, and `DeadlineWithdrawalRewardCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRaw.lean`)
are the canonical source definitions. At a finite outsider deadline, withdrawal
replaces only the child's exact deadline atom by Never. It leaves every other
child clock unchanged; an outsider Never deadline is the identity. The floor
is the minimum of zero and all nonempty passive child-coalition rewards. It is
not the patient variant's unrestricted passive floor.

The certificate keeps separate nonnegative advance and withdrawal weights and
the literal D-N, D-F and D-J reward rows. For a singleton withdrawal, the
nonpositive zero-or-passive floor handles both later absorption and Never.
`deadlineWithdrawalActualEvaluatedChildGain_tie_ge_floor`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalPointwise.lean`)
uses the actual first date and coalition, including singleton and nonsingleton
ties.

`deadlineWithdrawalActualEvaluatedOutsideGain_le_weighted_childGains`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalDomination.lean`)
proves the deterministic comparison for every tuple and deadline under every
nonnegative antitone evaluation. It covers outsider arrival before, at, and
after the first child absorption, and the Never case. The gains are actual
evaluated pure-clock payoffs, not numerical bounds attached to a certificate.

## Disjoint-event maximum transport

`deadlineMixedPrivateClockLaw_gain_identity`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalMixedLaw.lean`)
constructs the legal one-site response with coefficient `max(a_i,b_i)`.
On the private event that the child's clock is later than the deadline, it
advances with probability `a_i/max(a_i,b_i)`; on the disjoint exact-deadline
atom, it withdraws with probability `b_i/max(a_i,b_i)`. Otherwise it keeps
the original clock. Zero maximum and outsider Never are handled separately.
This disjoint-event identity, not a generic convexity estimate, supplies MAX.

The original child laws and a fresh independent outsider-clock replica give
the actual private replacement. It reads only the responding child's clock
and its private replica, never opponent clocks.
`deadlineMixedPrivateReplacement_parentProduct`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalProductLaw.lean`)
and `deadlineMixedPrivateReplacement_parentMarginal`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalMixedMarginal.lean`)
identify its independent product and the single changed marginal.
`deadlineMixedPrivateReplacement_integratedGain`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalMixedGain.lean`)
retains the exact weighted gain after bounded expectation integration.

## Complete behavioral debt and shared quiet lift

`deadlineWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt` and
`deadlineWithdrawal_quietLift_totalBehaviorDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalFullBehavioralDebt.lean`)
take the unrestricted behavioral deviation supremum, including Never, and
identify the same actual quiet lift with the literal deleted child. The
outsider debt is bounded by the sum of `max(a_i,b_i)` times the child debts.
The total-debt coefficient on each child is `1+max(a_i,b_i)`. The desired
debt inequality and cap are conclusions, not assumptions.

`quittingLiftDeletedProfile_evaluatedDebt_of_deadlineWithdrawalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalMultipleOutsiderFamily.lean`)
uses that SAME full quiet lift for every outsider's child-plus-one experiment.
It preserves each child debt exactly. Each outsider has its own literal raw
certificate; this does not restrict the family to one deleted player.

`quittingBehaviorEvaluatedMaxDebt_liftDeletedProfile_le_of_deadlineWithdrawal`
and `quittingBehaviorEvaluatedTotalDebt_liftDeletedProfile_le_of_deadlineWithdrawal`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalFamilyDebtBounds.lean`)
give the family maximum and sum bounds. The maximum factor is the maximum of
one and the outsider sums of MAX weights. The sum bound accumulates one plus
all outsider MAX weights on each preserved child debt.

## Actual source and fixed-target consumers

`exists_uniformPayoffWitnesses_eq_on_child_of_deadlineWithdrawalFamily` and
`exists_uniformEquilibriumPayoff_eq_on_child_of_deadlineWithdrawalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalFixedTarget.lean`)
preserve EVERY specified actual child uniform-equilibrium target. One parent
target is selected before accuracy; each accuracy uses an actual child profile,
its literal Never lift, and all sufficiently long horizons. All deleted players
literally prescribe Continue. The child target is not recomputed for each
accuracy.

`quittingDeleteReward_finFour_exists_uniformEquilibriumPayoff` and
`quittingGame_exists_uniformPayoffWitnesses_of_finFour_deadlineWithdrawalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalFinFourExistence.lean`)
construct the child target from the actual restricted signed reward table for
every nonempty proper child of a four-player game. The raw certificate family
then constructs the parent target and actual quiet witnesses; no good child
strategy or cap is supplied. The companion
`quittingGame_exists_uniformEquilibriumPayoff_of_finFour_deadlineWithdrawalFamily`
in the same file projects these witnesses to the usual fixed-target conclusion.

## Scope and nonclaims

The raw rows define a sufficient class, not certificates for every reward
table or unrestricted four-player existence. The simultaneous all-evaluation
bounds apply to each nonnegative antitone evaluation; they do not assert one
universal child strategy for all evaluation-dependent equilibrium tasks.
Fixed-target witnesses may depend on accuracy, while their target may not.
No executable prescribed real target, weak-boundary complexity bound, or
strategy convergence follows from these consumers.

The security enhancement uses a separate actual restart and security-LP chain;
see [the security dependency record](CODEX_FORMALIZER_WITHDRAWAL_SECURITY_DEPENDENCIES.md).
Evaluated cancellation uses its own response and the sum of its weights, not
the deadline-withdrawal MAX argument. Neither enhancement is obtained by
silently substituting a floor into the ordinary atom-withdrawal proof.
