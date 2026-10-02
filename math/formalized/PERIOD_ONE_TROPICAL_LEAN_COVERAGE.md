# Period-one tropical source: Lean coverage

Packet: [FIN4_PERIOD_ONE_TROPICAL_TWO_NEVER_REDUCTION.md](FIN4_PERIOD_ONE_TROPICAL_TWO_NEVER_REDUCTION.md).
Moved unchanged from `exports/`; SHA-256
`6a4e7c3fb5d0e8af44b76e4d4aed8d08365a5c61c7787da808f3877a358eba02`.

## Source and conclusions

`exists_periodOne_tropical_twoNever_escape_of_fourPlayer_noUniformPayoff` in
[`PeriodOneVanishingHazardEndpointLimits.lean`](../../UniformEquilibrium/Quitting/Cycles/PeriodOneVanishingHazardEndpointLimits.lean)
constructs the source and all endpoint limits from the absence of a
four-player uniform-equilibrium payoff and any positive error sequence
converging to zero. It does not assume the limiting endpoint payoffs or debts.

- The `PeriodOneVanishingHazardSource` and `PeriodOneNormalizedSourceLimit`
  fields in
  [`FourPlayerPeriodOneVanishingHazardSource.lean`](../../UniformEquilibrium/Quitting/Cycles/FourPlayerPeriodOneVanishingHazardSource.lean)
  retain the actual interior stationary profiles, approximate endpoint Nash
  roots, exact Bellman returns, complete debt bounds, and strict common
  subsequence with vanishing total hazard and convergent direction and payoff.
- `limitValue_eq_singletonDirectionPayoff` and
  `exists_positive_commonMinimum_and_totalEndpointRegretDensity_tendsto` in
  [`PeriodOneVanishingHazardLimitLaw.lean`](../../UniformEquilibrium/Quitting/Cycles/PeriodOneVanishingHazardLimitLaw.lean)
  prove the singleton-mixture law, positive minimum margin, support
  complementarity, and endpoint-regret-density limit.
- `selectedCompleteBehavioralCap_eq_max_quitNow_never` in
  [`PeriodOneVanishingHazardTerminalCap.lean`](../../UniformEquilibrium/Quitting/Cycles/PeriodOneVanishingHazardTerminalCap.lean)
  identifies the complete cap at each finite selected profile.
- `neverLimit_eq_opponentSingletonLottery`,
  `selectedQuitNowPayoff_tendsto`, `selectedNeverPayoff_tendsto`,
  `eventually_selectedNever_attains_completeCap`,
  `selectedCompleteDebt_tendsto`, and
  `selectedOutsiderDebt_tendsto_zero` in the endpoint-limit module prove
  the exported cap and debt limits. The eventual exact cap attainment by
  Never holds for outsiders as well as positive-share owners.
- `exists_two_fixed_neverDebtors` retains two distinct labels and one
  positive gain floor on the same actual source profiles. In a four-player
  simplex, these two positive coordinates exclude singleton support.

## Boundary

This is a reduction under the no-uniform-payoff hypothesis. It does not
establish that hypothesis, construct chronological deletions from the two
same-source responses, or consume the resulting support cases. The separate
off-minimum paid-port packet remains responsible for that chronology.

## Verification

The endpoint-limit module passed its targeted Lean check and named dependency
build. The integrated full `lake build`, including the exhaustive axiom audit,
passed with 11435 jobs. Trust, import-graph, documentation, duplicate-proof,
reward-bound, and redundant-hypothesis checks passed.
