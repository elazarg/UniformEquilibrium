# Supportwise weighted quitting-premium coverage

Author: CODEX_ROOT. Integration through `c2789f0` passed the silent full
build and trust, import-graph, duplicate, telescope, and documentation checks.
An independent Astra review checked the full packet, including the actual
periodic producer, unrestricted consumer, normalization, and examples.

Frozen packet: `SUPPORTWISE_WEIGHTED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM.md`,
SHA-256 `38d4975b7e630e59878332bdb96190932ede7e4be8c414e0fe11c201dcabcef7`.

## Declaration map

- `IsSupportwiseQuittingPremiumWeightCertificate` and
  `HasSupportwiseQuittingPremiumBalanceAt`
  (`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumBalanceAt.lean`)
  state the participant-only inequalities for one normalized nonnegative
  weighting on one support. The global predicate
  `IsSupportwiseBalancedQuittingPremiumTable`
  (`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`)
  quantifies the same certificate over every nonempty support.
- `quittingQuitProbability_mul_quitPremium_eq_sum_terminalPremium` and
  `exists_supportwiseCertificate_with_aggregate_and_positiveWeight_low`
  in the global module give the exact product identity and retain the same
  certificate, nonpositive aggregate, and positive-weight active low player.
  Zero and sure hazards require no division.
- `isClosed_supportwiseQuittingPremiumFeasibleSet` and
  `isCompact_supportwiseQuittingPremiumFeasibleSet`
  (`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumFeasibleSet.lean`)
  describe the literal feasible set. `MathUE/FinFourSubsetIncidenceCounts.lean`
  proves the counts of 15 supports, 32 weight coordinates, 65 contained
  nonempty coalitions, and 33 nonsingleton constraints.
- `supportwiseBalance_playerwiseNormalized`
  (`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumNormalization.lean`)
  reweights by the positive coordinate scales. The same module supplies
  weak peeling and strictly positive global weighting as sufficient inputs.
- `exists_periodic_allSuffix_terminalNash_of_supportwiseBalance` and
  `exists_uniformEquilibriumPayoff_of_supportwiseBalance`
  (`UniformEquilibrium/Quitting/Classification/Existence/SupportwisePremiumUniformPayoff.lean`)
  prove the original-game conclusions. They reuse the shared product-low
  periodic construction, unit-singleton unrestricted extraction, and
  fixed-payoff selection; no approximate equilibrium source is an input.
- `UniformEquilibrium/Quitting/Examples/SupportwisePremiumClassSeparation.lean`
  contains the cyclic, one-positive-premium, and combined Fin4 separation
  tables with arbitrary passive rewards.
  `UniformEquilibrium/Quitting/Examples/SemipositiveGlobalWeightCounterexample.lean`
  proves failure of one global semipositive weight to control the active
  support, with a normalized displayed weight and exact Nash root.
  `UniformEquilibrium/Quitting/Examples/FinTwoHazardWeightedPremiumBoundary.lean`
  proves the distinction between the plain and hazard-weighted averages.

## Scope and proof choices

The equilibrium theorems cover every finite nonempty player set with
nonnegative own singleton rewards. Passive rewards and participant premiums
may have either sign. Weights may vanish and depend on the support, but
one weight controls all contained coalitions. Profiles and periods depend
on accuracy; the final payoff target does not. Every suffix is terminal
approximate Nash against unrestricted behavioral deviations, including Never.

The shared normalization proof uses the sharper one-shift terminal-regret
bound and a valid alternative error allocation. It does not assert an
unconditional payoff shift when play never absorbs. No necessity theorem,
LP-dual product-law realization, LP solver, or equilibrium complexity bound
is claimed. Failure of this sufficient criterion is not a counterexample
to uniform-equilibrium existence.
