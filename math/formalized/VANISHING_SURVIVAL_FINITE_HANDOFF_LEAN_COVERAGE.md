# Vanishing-survival finite-source cap handoff: Lean coverage

The packet `FIN4_VANISHING_SURVIVAL_FINITE_SOURCE_CAP_HANDOFF.md` is implemented
under its stated source and exploitability-gap hypotheses. It does not prove
those hypotheses or uniform-equilibrium existence for arbitrary Fin4 games.

## Literal source and paid rows

`UniformEquilibrium/Diagnostics/Quitting/FinFourVanishingSurvivalFiniteSourceCapHandoff.lean`
contains `FirstStationaryRootZeroBranch.nonempty_finiteSourceCapHandoff` and
`FinFourFiniteSourceCapHandoff`. Its tail, root, prefixed profile, response, and
child retain the actual selected source. `payoff_gain_eq_source_debt`,
`half_minimum_le_payoff_gain`, and `child_owner_debt_eq_zero` give the exact
owner update. `exists_distinctTerminalGapPaidRows` produces one `PaidRows`
object with a common nonowner observer, full-gap row, actual reached row,
source support, and the stated survival and live-mass lower bounds.

`FirstStationaryRootZeroBranch.nonempty_fixedObserverPaidRows`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourVanishingSurvivalFixedObserver.lean`)
fixes that observer along a strict subsequence. Both rows remain fields of
the same dependent paid-row object at each selected index.

## Punishment floor and existing orbit consumer

`owner_punishment_le_child_payoff` and `floorSafeMarkedOrbit_or_underfloor`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourVanishingSurvivalFloorPortHandoff.lean`)
prove the owner's floor and the alternative between a displayed distinct
underfloor player and a floor-safe source at the literal child. The latter
uses the existing marked exact-orbit consumer, retaining its uniform-payoff
or summable semantic-port alternative and positive paid-suffix reach.
No uniform lower bound across different source indices is asserted.

## Nearly sure roots and all cluster points

`forceSureOwner_weighted_endpoint_regrets`
(`UniformEquilibrium/Quitting/Root/ForcedQuitEndpointStability.lean`)
proves both finite weighted regrets with error four times the payoff bound
times the owner's Continue probability. Signed reward and continuation
bounds are explicit. The generic sure-opponent screening theorem was moved
here from its previous diagnostics module rather than copied.

`FirstStationaryRootZeroBranch.finite_forceSureOwner_weighted_regrets` and
`FirstStationaryRootZeroBranch.singletonBase_error_tendsto_zero`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourNearSureRootApproxSingletonBase.lean`)
specialize to actual source tails, derive their bound, and show that the
error vanishes. Exact induced-Nash membership is asserted at the retained
limit, not at finite nearly-sure roots.

`FirstStationaryRootZeroBranch.clusterPoint_mem_singletonBaseNashSet`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourNearSureRootClusterPoint.lean`)
also quantifies any convergent strict subsequence of the forced free points
and proves its limit belongs to the singleton-base Nash set.

## Boundaries

The packet supplies neither an underfloor repair nor a charged-return theorem.
It does not assert that the literal child is stationary, regenerate the
near-minimum source, or turn per-orbit positive reach into a uniform bound.
The imported orbit consumer is reused, not reproved.

The Lean modules are reachable through the production and diagnostics umbrellas.
Targeted checks use warnings as errors; the integration gate additionally runs
the silent full build, exhaustive axiom audit, trust, import, and documentation
checks before the unchanged packet is moved into this directory.
