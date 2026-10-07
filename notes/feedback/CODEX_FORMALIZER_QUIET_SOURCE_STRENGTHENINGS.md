# Quiet-source proof-derived strengthenings

Read-only proof mining of the completed NONNEGATIVE_SINGLETON_FINITE_QUIET_LIFTS
source. The following are proposed APIs directly supported by inspected proof
bodies, not newly checked theorems. They add no arbitrary-game existence or
prescribed-child-target claim.

## Independent perturbation and Nash scales

In `exists_terminalProfile_smallExploitability_smallNever_of_nonnegativeSingleton`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/NonnegativeSingletonEarlyAbsorption.lean`),
replace the chosen perturbed Nash accuracy delta² by independent eta > 0 and the
singleton bump by b > 0. Under the same at-most-three-player and nonnegative
selected singleton s hypotheses, the existing proof supplies one actual
original-game profile with exploitability at most eta+b and joint Never at most
eta/(s+b). `prod_stoppingLaw_none_mul_singleton_le_terminalExploitability`
(`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`) supplies the
denominator estimate; the same nonnegative reward-perturbation theorem transfers
the unchanged laws. Original five-kind certificates are applied only afterward.
Combining the existing original-table debt aggregation and a censor tolerance tau
allows independent regret, absorption, and tail budgets. The low-player source
hypothesis is not removed.

## One censor before every valid reward bound

In `exists_finiteQuietLift_of_profile`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/QuietLiftFiniteCensor.lean`),
both the cutoff and finite mixed laws are chosen solely from the original stopping
laws and positive tolerance tau; the reward bound is used afterward. A minimal
stronger interface orders its quantifiers as: for every original child profile
and tau > 0, there exist one positive deadline and one finite family such that,
for every valid bound M, their parent regret is at most original parent regret +
4*M*tau. The same chosen family retains the joint-Never estimate and the exact
censored stopping-law equality already established inside the proof. This is a
same-witness quantifier gain, not a uniform bound on the required deadline.

## Expose the actual legal gain limit

The proof of
`neverMass_mul_opponentNeverProduct_mul_singleton_le_terminalDebt`
(`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`) contains
convergence of the actual `moveNeverToFinite T` unilateral gain to Q*s. Expose
that limit using `quittingTerminalPayoff_moveNeverToFinite_sub_eq` and
`quittingTerminalPayoff_update_finiteTime_tendsto_of_profile`. It gives: for every
positive error there exists N such that every T >= N produces a legal
same-profile replacement whose gain differs from Q*s by less than that error.
Finite intersection gives one N simultaneously for every player. No sign
restriction is needed for the limit itself. This does not assert attained best
response, an effective deadline, or unchanged play under the deviation.

## Sharp joint-Never censor control

`censorLateFiniteStoppingLaw_none_toReal_eq`
(`MathUE/ProbabilityMassFunction/ExactLateFiniteCensor.lean`) gives the exact
marginal Never increment. Substituting it into the existing product-difference
estimate used by `prod_censorLateFiniteStoppingLaw_none_le`
(`MathUE/ProbabilityMassFunction/LateFiniteStoppingLawJointNever.lean`) yields
joint Never after censoring at most original joint Never plus the summed
discarded finite masses, instead of twice that sum. This removes the loss from
the generic total-variation singleton estimate. It does not remove the genuine
original-table Never residual or the sign/target-selection boundary examples.
