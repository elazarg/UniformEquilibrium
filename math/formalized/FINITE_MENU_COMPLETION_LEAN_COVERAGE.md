# Finite-menu punishment completion: Lean coverage

Packet: `FINITE_MENU_PUNISHMENT_COMPLETION_AND_EARLY_ABSORPTION_CHARACTERIZATION.md`.
Frozen SHA-256:
`c8861a4160c0bf77da4fff22e2961b6cf63980e70656e4277b73edf8b15c3ef6`.

Paths below are relative to `UniformEquilibrium/`.

## Actual punishment approximation

`quittingFiniteMenuPunishmentValue` and its attained minimizer
(`Quitting/Punishment/FiniteMenuPunishmentValue.lean`) use actual independent
finite timing laws. `quittingFiniteMenuPunishmentValue_eq_operator_iterate`,
`quittingFiniteMenuPunishmentValue_succ`,
`tendsto_quittingFiniteMenuPunishmentValue`, and
`tendsto_quittingFiniteMenuPunishmentDeficit`
(`Quitting/Punishment/FiniteMenuPunishmentRecursion.lean`) prove the scalar
recursion and convergence to unrestricted punishment for signed rewards.
The operator's monotonicity, nonexpansiveness, and invariant reward interval
are proved in `Quitting/Punishment/FiniteMenuPunishmentOperator.lean`.
No effective convergence rate or increasing iteration from zero is assumed.

## Same-prefix completion and early absorption

`exists_finiteMenu_samePrefix_completion`
(`Quitting/Punishment/FiniteMenuCompletion.lean`) takes actual displayed-menu
Nash comparisons and small joint reach. It keeps every history before the
cutoff, chooses one fixed exceptional punishment target, and bounds every
behavioral deviation by the exported error
`error + 2Mρ + max(2M√ρ, deficit(H) + slack)`.
Deleted-opponent reach is controlled separately, not replaced by joint reach.

`HasQuittingFiniteMenuEarlyAbsorption`
(`Quitting/Terminal/FiniteMenuEarlyAbsorption.lean`) states all four source
quantifiers using actual timing laws and the actual joint survival clock.
`exists_uniformEquilibriumPayoff_of_finiteMenuEarlyAbsorption`
(`Quitting/Terminal/FiniteMenuEarlyAbsorptionCompletion.lean`) produces one
fixed uniform payoff for arbitrary finite nonempty signed quitting games.
`exists_uniformEquilibriumPayoff_iff_finiteMenuEarlyAbsorption_of_singleton_pos`
(`Quitting/Terminal/FiniteMenuEarlyAbsorptionNecessity.lean`) proves equivalence
when at least one own singleton is positive.

Necessity uses the literal stopping-law censoring and full-error estimates in
`Quitting/Paths/LateFiniteStoppingLawCensor.lean`, fixed-family cutoff selection
in `MathUE/ProbabilityMassFunction/LateFiniteStoppingLawCensor.lean`, and
`prod_stoppingLaw_none_mul_singleton_le_terminalDebt`
(`Quitting/Terminal/SingletonJointNeverDebt.lean`). The finite-menu realization
and actual survival adapters retain the requested deadline quantifiers.

## Boundary statements

`Quitting/Classification/OnePlayer/FiniteMenuPunishment.lean` proves the
one-player punishment and positive-deadline finite-menu values are the maximum
of the singleton and zero. `Diagnostics/Quitting/FiniteMenuBoundaryRegressions.lean`
proves the negative one-player game has UE but fails early absorption.
The positive-singleton converse includes one-player games; it does not assume
that a distinct opponent exists.

`Diagnostics/Quitting/TwoClockFiniteMenuRegression.lean` proves exact finite
menu Nash, prescribed payoff one, omitted-date payoff three halves, and full
debt one half for the packet's literal two-clock family. Its actual-clock
theorems cover the whole requested interval. `hasFiniteMenuEarlyAbsorption`
proves all source quantifiers for this family; `completed_fullCap_false`
proves that replacing the prescribed tails by Never gives full cap one.
The same file proves finite-menu punishment at horizon one is two thirds,
whereas full punishment is one.

`Diagnostics/Quitting/FiniteMenuSignedZeroBoundaryRegression.lean` proves the
two-player constant negative table has finite-menu value zero at deadline zero
and value minus one at every positive deadline, equal to full punishment.
Its generic zero-reward theorems give zero finite-menu and full punishment,
zero payoff, and zero unrestricted exploitability for every profile.

## Scope

This is a source-to-equilibrium completion and a positive-singleton
characterization, not a producer of early absorption for arbitrary games.
The two-clock family explicitly shows why an unchanged finite-menu source
need not already be an unrestricted approximate equilibrium. All deviations
are complete unilateral behavioral replacements, and all randomization is
private and independent. No subgame-perfection conclusion is claimed.

## Verification

The integrated full `lake --quiet --iofail build` passed with no Lean output,
including the final signed/zero boundary module and exhaustive axiom audit.
The current 2882-module inventory passed trust and import checks; documentation
checks also passed. The preceding integration checkpoint passed 113 script
tests and all 33 experiment-registry execution checks. Independent source
review covered the main completion and the complete packet clause map.
