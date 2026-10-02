# Ordered quitting premiums: Lean coverage

Author: CODEX_ROOT. Coverage audit on 2026-09-07.
Frozen packet SHA-256:
`a42680e45fe7a8a373337a624808eefee1fc5a3b53507eda32cb5a7e5e7f3b6e`.
The packet is preserved byte-for-byte; this record supplies its Lean status.

The geometry, punishment, and fixed-box consumer are full-build checked and
pushed in `68a8ccc`. The literal Section 9 fixtures are pushed in `94d58d2`
after a silent full build, together with trust, import-graph, proof-duplicate,
redundant-telescope, documentation, and diff checks. All listed modules are
reachable from the production umbrella and included in the axiom audit.
The Astra agent independently audited the boxed converse's hypotheses,
inactive-player inequalities, and empty-player case; that review was static.
Root reviewed the new proof sources before the full builds.

## Main theorem and ordering

`weakQuittingPremiumSupportPeeling_iff_playerRanking`
(`UniformEquilibrium/Quitting/Classification/QuittingPremiumSupportPeelingOrder.lean`)
proves the exact equivalence between weak support peeling and a full
positive-premium player ranking. Negative participant premiums and all
passive entries remain unrestricted.

`exists_periodic_allSuffix_terminalNash_of_weakPremiumSupportPeeling` and
`exists_uniformEquilibriumPayoff_of_weakPremiumSupportPeeling`
(`UniformEquilibrium/Quitting/Classification/Existence/QuittingPremiumSupportPeelingUniformPayoff.lean`)
provide the actual periodic every-suffix unrestricted terminal approximate
equilibria and one fixed uniform-equilibrium payoff, for arbitrary finite
nonempty player sets with nonnegative singletons. The corresponding
player-ranking theorems are in the same module. They reuse the stronger
supportwise and product-low producers, not a supplied sequence assumption.

The source chain constructs the charged root and finite mesh cycle, compares
the annotation to actual periodic tail payoffs, invokes the existing
unit-singleton full-response extraction, and removes normalization with the
absorption-weighted Never correction. The nonnegative shift transfer in
`UniformEquilibrium/Quitting/Terminal/TerminalAffineNashTransfer.lean`
costs at most the shift, strengthening the packet's safe twice-shift bound.
No fixed period or executable root-selection algorithm is asserted.

## Auxiliary root characterization and drift obstruction

`weakPeeling_iff_every_boxedExactRoot_singletonLowerBoundary` and
`exists_exactRoot_strictSingletonInterior_of_not_weakPeeling`
(`UniformEquilibrium/Quitting/Classification/NonnegativePremiumBoxBoundary.lean`)
give both directions on every padded reward box under nonnegative own
premiums. The converse constructs one common small hazard and the actual
indifference continuation, with every successor coordinate strictly above
its singleton and below the upper cap. The continuation is a payoff
annotation, not an asserted realizable behavioral tail. A separate
nonnegative-bound or nonempty-player premise is unnecessary.

`not_differentiable_absorptionDrift_of_nonnegative_productLow`
(`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSmoothDrift.lean`)
proves the full-box drift exclusion. Differentiability at every box point
suffices, strengthening the packet's continuously differentiable
neighborhood hypothesis. It permits signed singleton levels and assumes no
convexity. The generic geometry is in
`MathUE/Analysis/LowerBoxBoundarySmoothDrift.lean`; the actual single-binding
root is constructed in
`UniformEquilibrium/Quitting/Root/SingletonBoundaryExactRoot.lean`.

These auxiliary results retain nonnegative own premiums. They do not extend
the boundary conclusion to the main signed-premium class.

## Fixed-radius packets and unrestricted punishment

`quittingPunishmentValue_eq_singleton_of_nonnegativePremium`
(`UniformEquilibrium/Quitting/Classification/NonnegativePremiumPunishment.lean`)
identifies the full behavioral punishment value with each nonnegative
singleton. The same module supplies the singleton lower bound without a
singleton-sign hypothesis. Normality alone at a nonnegative singleton needs
no premium-sign assumption, by `isQuittingNormalPlayer_of_singleton_nonneg`
(`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`).

`hasFloorFreeAbsorptionWeightedFiniteForwardPackets_of_nonnegative_weakSupportPeeling`
(`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowForwardPackets.lean`)
supplies the Fin4 packets for every positive accuracy and nonnegative
requested charge in one fixed reward-bound-plus-two box. Signed singleton
levels are allowed for this floor-free conclusion. The proof uses the
existing smooth-capacity separator directly; polynomial re-encoding is not
needed for the result.

`hasAbsorptionWeightedFiniteForwardPackets_of_nonnegative_weakSupportPeeling`
and `exists_uniformEquilibriumPayoff_of_nonnegative_weakSupportPeeling_viaForwardPackets`
(`UniformEquilibrium/Quitting/Classification/NonnegativePremiumForwardPacketConsumer.lean`)
restore floors in that same radius and yield the independent Fin4 uniform
payoff route when singletons are nonnegative. No degree or packet-length
bound is asserted.

## Exact Section 9 tests

- Items 1--3: `UniformEquilibrium/Quitting/Examples/OrderedPremiumBoundaryFixtures.lean`
  contains the literal two-recipient triple, its valid player order and
  co-member graph two-cycle; the exceptional pair and triple rows; failure
  of peeling; every-continuation exact root Nash; strictly interior
  successors; and unrestricted stationary terminal Nash. The triple table
  has exactly baseline rewards at every pair.
- Item 4: `UniformEquilibrium/Quitting/Examples/OrderedPremiumNegativeBoundary.lean`
  contains the literal negative-premium table, weak peeling, every-tail
  exact root, zero successor below player zero's singleton, unrestricted
  punishment equal to zero, and actual terminal Nash.
- Items 5--6: `UniformEquilibrium/Quitting/Examples/OrderedPremiumPassiveSeparation.lean`
  contains the zero-premium family with arbitrary passive rewards, every
  supplied player-order rule, nonnegative-singleton uniform payoff, and
  zero-singleton all-Continue exact Nash. Its passive-singleton replacement
  preserves every participant entry and weak peeling, creates every
  distinct-player preemption edge, and gives a literal Fin4 two-cycle.

## Seals and remaining scope

The packet has mathematical evidence, checked Lean declarations, actual
table-to-profile production, and the fixed-target consumer: M, L, A, C for
its stated sufficient class. The root geometry and signed-singleton
floor-free route retain their separate hypotheses. Failure of peeling is
not nonexistence of equilibrium. None of these results settles arbitrary
Fin4 tables, removes nonnegative singletons from the main class theorem,
or supplies a uniform period bound.
