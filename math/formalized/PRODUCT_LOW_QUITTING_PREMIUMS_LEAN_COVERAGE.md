# Product-low quitting premiums: Lean coverage

The packet `PRODUCT_LOW_QUITTING_PREMIUMS_STRICT_EXTENSION_UNIFORM_EQUILIBRIUM.md`
is implemented, including its rational/algebraic recognition claims and boundary
examples. The final additions are in commit `36e9ced`. The full
`lake --quiet --iofail build` passed silently, including the exhaustive axiom
audit. Documentation, 113 script tests, 33 experiment reproductions, import
reachability, duplicate-proof, reward-bound, redundant-hypothesis, trust, and
whitespace checks passed on the final source snapshot. The boundary and
algebraic interfaces also received independent static review.

The packet was moved here byte-for-byte; its SHA-256 is
`836eb376e4f26b6b4ee7f865759ab2cf5c99e10ead3bc75e91b24c91ec0475a7`.

All game declarations below are in namespace `GameTheory`, unless the stated
module supplies a more specific namespace. Paths begin at the repository root.

## Sections 1–2: raw predicates and sufficient-condition inclusion

- `HasProductLowQuittingPremium`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`)
  quantifies over every actual independent product root with positive absorption
  and requires one and the same player to be active and have Quit payoff at most
  its own singleton. It does not restrict passive rewards or singleton signs.
- `IsSupportwiseBalancedQuittingPremiumTable` and
  `quittingQuitProbability_mul_quitPremium_eq_sum_terminalPremium`
  (`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`)
  give the exact supportwise condition and product identity. The own-Quit
  probability factor is retained.
- `hasProductLowQuittingPremium_of_supportwiseBalance`
  (`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumProductLow.lean`)
  is the literal inclusion from supportwise balance to product-low premiums.
- `hasProductLowQuittingPremium_iff_hazard`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumInwardViolation.lean`)
  identifies the product-root predicate with its closed-unit-cube hazard formula.

## Sections 3–4: exact family, every face, and separation

The declarations in this section lie in `GameTheory.ProductLowFinFourFamily`,
in `UniformEquilibrium/Quitting/Examples/ProductLowFinFourFamily.lean`.

- `premium` and `reward` implement the exact displayed family. The underlying
  `rewardOfOwnPremium` uses supplied passive coordinates whenever the observer
  is not a participant. `premium_singleton`, `reward_singleton`, and
  `reward_sub_singleton` connect the construction to actual singleton premiums.
- `quitPremium_formula` identifies all four actual Quit premiums with the
  explicit polynomial vector `quitPremiumPolynomial`, for every product root.
  Its third coordinate uses Continue probability, equal to one minus Quit
  probability. No open-cube restriction or division by a hazard is used.
- `exists_active_quitPayoff_le_singleton` handles all eight exact core-support
  cases and `hasProductLowQuittingPremium` packages the result. These cover all
  fifteen nonempty supports and sure-Quit boundaries. Nonnegative scales suffice;
  positive scales are only needed for the strict separation conclusions.
- `properSupport_hasSupportwiseCertificateAt` gives a normalized certificate
  on every nonempty proper support for positive scales.
- `not_fullSupportBalanceAt` and `not_supportwiseBalance` prove full-support and
  global failure for every positive-scale family member, independently of
  singleton levels and passive rewards.

In namespace `GameTheory.ProductLowPremiumBoundaryIdentities`, in
`UniformEquilibrium/Quitting/Examples/ProductLowPremiumBoundaryIdentities.lean`:

- `dualPremium_identity` is the exact integer combination with coefficients
  two, one, three, one and value equal to the coordinate scale.
- `dualMass_nonneg`, `dualMass_sum_one`, and the four named atom evaluations
  establish the normalized correlated coalition law.
- `dualMass_not_independent` excludes every independent Bernoulli coalition law,
  including boundary parameters. It uses positive Continue factors forced by
  the displayed atoms and contradicts the zero empty-coalition mass.
- `sum_dualMass_mul_participantPremium` gives the expected raw family premium
  as `scale player / 7`. On all positive-mass atoms the raw premium is zero for
  nonparticipants, so this agrees mathematically with the participant premium.
  `sum_dualMass_mul_actualParticipantPremium` in this same canonical module
  records the explicit participant indicator and actual reward-minus-singleton
  values, summed over nonempty terminal coalitions, with arbitrary passive rewards.

## Section 5: algebraic scope and exact boundary fixtures

- `quittingProductLowPremiumPolynomial` and
  `eval_quittingProductLowPremiumPolynomial`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumPolynomial.lean`)
  are the existing joint reward-hazard source with its actual evaluation bridge.
- `quittingFixedRewardPremiumPolynomial` specializes that source by replacing
  reward coordinates with the actual real reward entries;
  `eval_quittingFixedRewardPremiumPolynomial` recovers the actual hazard premium.
  `degreeOf_quittingFixedRewardPremiumPolynomial_le_one`,
  `degreeOf_quittingFixedRewardPremiumPolynomial_self`, and
  `totalDegree_quittingFixedRewardPremiumPolynomial_le`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumHazardDegree.lean`)
  prove multiaffinity, zero own-hazard degree, and total hazard degree at most
  the number of opponents. These are not joint reward/hazard degree claims.
- `not_hasProductLowQuittingPremium_iff_exists_inwardViolation`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumInwardViolation.lean`)
  gives an actual violating root with no sure quitter. Its proof preserves the
  original positive support; the equivalence suffices for the packet's boundary
  feasibility reduction.
- `decideHasProductLowQuittingPremium_eq_true_iff`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumDecision.lean`)
  proves exact executable rational-table recognition, including the empty-player
  case. It does not decide uniform-equilibrium existence.
- `isSemialgebraic_hasProductLowQuittingPremium_rewardTables`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumSemialgebraic.lean`)
  states the accepted set in the free real reward coordinates, without a
  singleton sign condition.
- `decideHasProductLowQuittingPremiumAtIsolatedRoots_eq_true_iff`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumIsolatedRootDecision.lean`)
  is the game-specific exact decision theorem on certified real-algebraic reward
  entries. It holds for every actual reward table satisfying the explicit
  coordinatewise `CertifiedIsolatedRootQuittingReward.Denotes` relation, without
  a singleton-sign or nonempty-player hypothesis.
- `quittingRewardTableVariableList`, `quittingRewardTableVariableIndex`,
  `quittingRewardTableVariableList_get_index`,
  `quittingRewardTableVariableIndex_get`, and the parameter encode/decode theorems
  (`UniformEquilibrium/Quitting/Root/RewardTableParameters.lean`) implement an
  executable deterministic enumeration, sorting by binary coalition code and
  then observer. The decision does not use the noncomputable coordinate
  equivalence of the semialgebraic presentation.
- `isolatedRootProductLowParameterFormula_holdsAt_iff` in the same algebraic
  module universally binds only the leading hazard block and preserves the
  trailing reward parameters. Its Boolean procedure consumes rational syntax and
  certified rational root descriptions, never the denoted real reward values.
  Empty players are included: there is no active hazard, so the implication is true.
- `decideAtIsolatedRoots_eq_true_iff` and
  `exists_isolatedRootParameterEnvironment`
  (`MathUE/RealQuantifierElimination/IsolatedRealRootParameters.lean`) ensure the
  interpretation relation is nonvacuous for certified parameters.
  `isAlgebraic_iff_exists_isolatedRealRootData` and
  `exists_certifiedIsolatedRootParameters`
  (`MathUE/RealQuantifierElimination/IsolatedRealRootCoverage.lean`) supply
  existence of encodings for arbitrary real-algebraic values and finite tuples.
  This encoding existence is not an executable encoder from unencoded real inputs.
- `exists_certifiedIsolatedRootQuittingReward_of_isAlgebraic` and
  `CertifiedIsolatedRootQuittingReward.exists_denotedReward`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumIsolatedRootCoverage.lean`)
  supply the literal same-actual-table adapters: every coordinatewise algebraic
  reward table admits certified inputs denoting that very table, and every
  certified input denotes a simultaneous actual real reward table. The proofs
  use the deterministic parameter index inverses and the generic existence
  theorems; neither implements an encoder from arbitrary real values. Both
  statements include the empty-player case without an extra hypothesis.

The literal boundary declarations now present are:

- `quitPremiumPolynomial_allQuit`, `quitPremium_allQuit_formula`,
  `quitPremiumPolynomial_onlyThree_active_zero`, and
  `quitPayoff_onlyThree_eq_singleton`
  (`UniformEquilibrium/Quitting/Examples/ProductLowPremiumBoundaryIdentities.lean`,
  namespace `GameTheory.ProductLowPremiumBoundaryIdentities`). The only-three
  fixture chooses certain Quit for player three; the general family formula
  also covers any positive probability for that sole active player.
- `halfRoot_quitPremium` and `not_hasProductLowQuittingPremium`
  (`UniformEquilibrium/Quitting/Examples/PureCoalitionLowProductFailure.lean`,
  namespace `GameTheory.PureCoalitionLowProductFailure`) give the original Fin3
  cyclic-pair counterexample.
- `everyPureCoalition_reward_has_low_participant`,
  `inactiveFourthHalfRoot_quitProbability`,
  `inactiveFourthHalfRoot_absorptionMass`,
  `inactiveFourthHalfRoot_quitPremium`, and `not_hasProductLowQuittingPremium`
  (`UniformEquilibrium/Quitting/Examples/PureCoalitionLowProductFailureFinFour.lean`,
  namespace `GameTheory.PureCoalitionLowProductFailureFinFour`) give an actual
  Fin4 table with arbitrary passive data, exact active support zero/one/two,
  absorption mass seven eighths, and active Quit premiums one quarter. Coalitions
  containing player three have zero participant premiums in this extension.
- `finTwo_quitPremium_formula` and `finTwo_not_hasProductLowQuittingPremium_iff`
  (`UniformEquilibrium/Quitting/Classification/FinTwoProductLowPremiumCriterion.lean`)
  hold for arbitrary signed Fin2 reward tables. Combining the latter with
  `productLow_iff_supportwiseBalance_finTwo`
  (`UniformEquilibrium/Quitting/Classification/FinTwoProductLowSupportwiseEquivalence.lean`)
  gives the packet's failure criterion for both conditions.

## Section 6: normalization and actual equilibrium consumers

- `quittingPlayerwiseUnitNormalization_singleton`
  (`UniformEquilibrium/Quitting/Root/PlayerwiseUnitNormalization.lean`) includes
  zero singleton levels through a strictly positive absorbing-reward shift.
- `hasProductLowQuittingPremium_playerwiseUnitNormalization` and
  `hasLowActiveQuittingRootQuitPayoff_iff_productLow`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`)
  supply the exact existing unit-root producer hypothesis.
- `quittingTerminalPayoff_playerwiseAffine`
  (`UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean`) contains the
  actual absorption-probability correction, so Never remains zero.
- `quittingRootSequence_allSuffix_terminalNash_playerwiseScale` and
  `quittingRootSequence_allSuffix_terminalNash_of_nonnegative_terminalShift`
  (`UniformEquilibrium/Quitting/Terminal/TerminalAffineNashTransfer.lean`) keep the
  same root sequence and every suffix, and quantify over arbitrary behavioral
  deviations without imposing absorption on them.
- `exists_periodic_allSuffix_terminalNash_of_productLowPremium` and
  `exists_uniformEquilibriumPayoff_of_productLowPremium`
  (`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`)
  prove the general nonnegative-singleton conclusions for every finite nonempty
  player type. The proof uses the sum of shifted coordinate scales instead of
  their maximum, a valid tighter normalized-error choice.
- `ProductLowFinFourFamily.exists_periodic_allSuffix_terminalNash` and
  `ProductLowFinFourFamily.exists_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Examples/ProductLowFinFourFamily.lean`) are actual
  family consumers, not supplied-equilibrium or chronology certificates.
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
  selects the fixed target in the original game's payoff cube before accuracy.
- `exists_periodic_allSuffix_terminalNash_of_productLowPremiumDecision` and
  `exists_uniformEquilibriumPayoff_of_productLowPremiumDecision`
  (`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumDecisionUniformPayoff.lean`)
  connect a true rational-table decision to those same actual consumers under
  nonnegative own singleton rewards. They do not implement strategy extraction.

## Nonclaims retained

Failure of product-low or supportwise balance does not imply nonexistence of
uniform equilibrium. There is no general Fin4 solution, necessity theorem,
retained absorption floor for the extracted equilibrium, efficient decision
bound, or algorithm on unrestricted unencoded real inputs. The general
finite-quitting conjecture is not settled by this packet.
