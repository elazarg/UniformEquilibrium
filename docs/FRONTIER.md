# Uniform-equilibrium mathematical frontier

This file states the current mathematical dependency boundary. Exact theorem
truth belongs to Lean declarations under their imports; the generated
declaration index is [`STATUS.md`](STATUS.md). Detailed compiler interfaces are
in [`TOOLKIT.md`](TOOLKIT.md), and the mechanically maintained quitting leaf
ledger is [`QuittingProofFrontier.json`](QuittingProofFrontier.json).

This is not a chronology. Explicitly historical mathematical synthesis is
scoped under [`audits/`](audits/README.md); repository-transition provenance,
old source paths, and extraction decisions belong only in
[`../TRANSITION.md`](../TRANSITION.md).

## Exact questions

The project distinguishes two existence propositions:

1. existence of a uniform-equilibrium payoff for finite stochastic games with
   state-independent action sets; and
2. existence for every finite quitting game.

The second is a strict specialization and is not a known normal form for the
first. Padding state-dependent action sets can introduce observable duplicate
labels and is not silently semantics-preserving. See
[`SEMANTICS.md`](SEMANTICS.md) for the exact quantifier and model contract.

Current proposition and capstone declarations are generated in
[`STATUS.md`](STATUS.md). The declaration index does not substitute for a Lean
build.

## Semantic waist for quitting games

For finite quitting games, the decisive positive interface is terminal
approximate Nash existence at every positive error. The integrated selection
theorem turns such a family into one fixed uniform-equilibrium payoff, and the
reverse implication also holds. Terminal verification, fixed-target selection,
and uniform finite-horizon delivery are separate proof obligations.

The decisive negative interface is a fixed positive terminal exploitability
gap against every behavioral profile. Excluding stationary, periodic,
finite-public, or bounded-controller profiles is only a screen unless a theorem
transfers it to the full behavioral class.

Thus the two accepted endpoints are:

```text
terminal approximate Nash profiles at every positive error
                           |
                           v
              uniform-equilibrium payoff

fixed positive terminal gain against every behavioral profile
                           |
                           v
             no uniform-equilibrium payoff
```

## Established construction boundary

The integrated corpus contains several sound ways to reach the positive
endpoint from supplied structured data:

- target-anchored and diagonal terminal tails;
- support-retaining paths and periodic witnesses;
- essential adaptive-potential systems;
- signed and single-seam projective lassos;
- sufficiently charged finite forward packets;
- punishment-completed absorbing cycles; and
- bounded multi-owner face circulations.

These are conditional producer/compiler strata at their stated inputs. None is
silently a universal grammar for all quitting equilibria. Their exact inputs,
outputs, and nonclaims are indexed in [`TOOLKIT.md`](TOOLKIT.md).

The development also contains sound diagnostics and no-go theorems. A
counterexample to one certificate language closes that route; it does not prove
nonexistence of equilibrium unless it reaches the all-behavior terminal-gap
interface.

The full-core deadlock completion family has a sharper integrated carrier
constraint.
[`IsFullCoreDeadlockCompletion.globalDebtFloor_le_sharperBound`](../UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockSharperBound.lean)
constructs an actual carrier point of total semantic debt exactly
`1227/96755` and therefore bounds every global debt floor by that value. The
The terminal exploitability witness consumer
[`HasTerminalExploitabilityGap.fullCoreDeadlock_le_sharperBound`](../UniformEquilibrium/Diagnostics/Quitting/FullCoreDeadlockDebtBound.lean)
then bounds every terminal exploitability gap on this family by `1227/96755`,
with the stored gap of a terminal exploitability witness as a direct corollary.
This statement ranges over arbitrary nonsingleton coalition rewards; it does
not produce a uniform-equilibrium payoff for that whole family.

The named zero-multiquitter completion is stronger.  The theorem
[`FullCoreDeadlock.reward_isUniformEquilibriumPayoff_jointBlock`](../UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockJointBlockEquilibrium.lean)
proves an exact uniform-equilibrium payoff for `FullCoreDeadlock.reward`.
Its certificate is a three-phase product block with supports `{0}`, `{2}`, and
`{1, 3}`; the last phase is a genuine double-quit phase, so it is not a
reduced singleton lasso.  No analogous equilibrium conclusion is claimed for
the arbitrary full-core completions covered by the `1227/96755` bound.

The checked rational strengthening covers an unbounded, nonlocal polyhedral
slice.  `IsDeadlockRationalJointBlockCompletion` and
`isUniformEquilibriumPayoff_of_isDeadlockRationalJointBlockCompletion`
(`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockRationalPolyhedralBlock.lean`)
allow an arbitrary baseline `s`, including negative coordinates, while fixing
the full-core singleton matrix, requiring the `{1,3}` reward to equal `s`, and
imposing eight explicit collision-cap inequalities.  Every such completion
has target `deadlockRationalBlockValue s`.  This is a sufficient polyhedral
slice and does not cover all full-core completions.

The stationary construction boundary also has a checked finite source-data
adapter.  `exists_uniformEquilibriumPayoff_of_conditionalFaceGapRange`
(`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`)
turns strict lower and weak upper reward-range comparisons into a stationary
uniform-equilibrium payoff.  The five-player regression in
`UniformEquilibrium/Diagnostics/Quitting/Regression/ConditionalFaceGapFivePlayer.lean`
has direct checked face signs and an exact stationary certificate, while
showing that the coarse range hypotheses are not necessary.  This remains a
conditional stationary class, not a producer for arbitrary quitting games.

The flat stopping-law charged-circulation branch now has a frozen actual-source
reset-cube adapter.  Integer rounding gives a balanced finite packet with
`O(1/N)` prefix control (`exists_frozenBalancedResetPacket` in
`UniformEquilibrium/Diagnostics/Quitting/Frozen/BalancedResetPacket.lean`).  Radial scaling absorbs
real circulation coefficients into legal stopping-law weights; the six frozen
modules under `Diagnostics/Quitting/Frozen/` place these resets in one literal
cube, expose the joint and deleted-player clocks, and retain the exact
`O(lambda²)` face remainder.  The strongest static dispatch is
`exists_fixed_frozenRadialStrategicLabel_of_scaleNormalizedLiminfLower` in
`UniformEquilibrium/Diagnostics/Quitting/Frozen/RadialCurvatureStrategicDispatch.lean`, which returns the oriented
strategic square alternative.  These are frozen-source certificates: they do
not provide a chronological carrier path or a renewal return.

Terminal differences between two pure-time witnesses also have an exact
reached-history decoder.
[`quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul`](../UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean)
covers both finite later dates and `Never`, so the source-to-reached-history
transport itself is no longer a gap. What remains is the game-facing
composition of a localized cap square with the appropriate branch consumer,
and, in the common-passport branch, a chronological carrier-path producer
whose ordered Bellman blocks have vanishing Green ratios and divergent
opponent exposure. The static cube does not supply that chronology.

## Current proved dependency DAG

The maintained ledger is now a dependency DAG, not a history of named search
leaves. It begins at positive minimum terminal semantic debt, records the
exact-diagonal stopping-law extraction and finite support-rank exit, and then
shows both the four tagged exit arms and the checked consumers beyond the
remaining producer gaps.

Finite support-rank termination leaves positive total slope, zero-debt support
entry, flat charged circulation, or an eventually paid first-disagreement row.
These are mathematically distinct tags, not an asserted equivalence. There is
also a stronger branch-independent adapter: every extracted frontier already
has fixed vanishing-debt atom access. In the support-entry arm the actual
zero-debt recipient can be retained as the atom observer.

Two concrete routes remain explicit. On the atom route, one local theorem must
produce actual reached-port packets with retained labels, exact source and
successor anchors, and an operationally sublinear seam-plus-radius-loss
modulus. A separate external source/payoff-to-candidate adapter must provide
the small-debt compiler seed, unless it returns a solved-game disjunct.
Budget-stable compatible iteration after those inputs is checked. The all-frontier
chronological consumer is not the missing local theorem:
`vanishingDebtAtomChronologicalConsumer_iff_exists_uniformEquilibriumPayoff`
proves that it is exactly equivalent to uniform-payoff existence for each
reward table. It is retained as the global integration contract.

On the paid route, an eventually paid row must be re-entered with one fixed
positive charge threshold, while the source, target, path, and charged edge
may vary with endpoint tolerance and endpoint payoff vectors become
arbitrarily close. Fixed-edge payoff closure and exact return to the full tail
state are stronger special cases. The chronological and payoff-near-return
consumers themselves are proved in Lean.

Seals use the independent `M`/`L`/`A`/`C` language of
[`STATUS.md`](STATUS.md). An `L` seal on an open producer arrow means its
proposition interface is checked, not that the implication has been proved.

<!-- BEGIN GENERATED OPEN LEAVES -->
This dependency table is generated from [`QuittingProofFrontier.json`](QuittingProofFrontier.json).

| From | Status | To | Seals | Checked declaration or open interface |
| --- | --- | --- | --- | --- |
| `POSITIVE-MINIMUM-DEBT` | `proved` | `EXACT-DIAGONAL-FRONTIER` | `M`, `L`, `A` | [`GameTheory.finiteSupportRankAlternative_of_hasPositiveMinimumTerminalSemanticDebt`](../UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean) |
| `EXACT-DIAGONAL-FRONTIER` | `proved` | `FINITE-SUPPORT-RANK-EXIT` | `M`, `L`, `A` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.finiteSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean) |
| `FINITE-SUPPORT-RANK-EXIT` | `proved-branch` | `POSITIVE-TOTAL-SLOPE` | `M`, `L` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.HasQuittingStoppingLawFiniteSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean) |
| `FINITE-SUPPORT-RANK-EXIT` | `proved-branch` | `ZERO-DEBT-SUPPORT-ENTRY` | `M`, `L` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.HasQuittingStoppingLawFiniteSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean) |
| `FINITE-SUPPORT-RANK-EXIT` | `proved-branch` | `FLAT-CHARGED-CIRCULATION` | `M`, `L` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.HasQuittingStoppingLawFiniteSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean) |
| `FINITE-SUPPORT-RANK-EXIT` | `proved-branch` | `PAID-FIRST-DISAGREEMENT-ROW` | `M`, `L`, `A` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.HasQuittingStoppingLawFiniteSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean) |
| `EXACT-DIAGONAL-FRONTIER` | `proved` | `VANISHING-DEBT-ATOM-ACCESS` | `M`, `L`, `A` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.nonempty_vanishingDebtAtomAccess`](../UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean) |
| `ZERO-DEBT-SUPPORT-ENTRY` | `proved` | `VANISHING-DEBT-ATOM-ACCESS` | `M`, `L`, `A` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.exists_vanishingDebtAtomAccess_of_supportEntry`](../UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean) |
| `VANISHING-DEBT-ATOM-ACCESS` | `open-producer` | `CHRONOLOGICAL-DEBT-SHADOWING` | `M`, `L`, `C` | [`GameTheory.QuittingBudgetStablePacketSystem.exists_chronologicalDebtShadowingCertificate_of_seed`](../UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean) |
| `PAID-FIRST-DISAGREEMENT-ROW` | `open-producer` | `POSITIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN` | `M`, `L`, `A` | [`GameTheory.QuittingPositiveAdmissiblePayoffNearReturnFamily.exists_tightFace_escape`](../UniformEquilibrium/Diagnostics/Quitting/Chronology/TightFacePaidNearReturnRestriction.lean) |
| `CHRONOLOGICAL-DEBT-SHADOWING` | `proved-consumer` | `UNIFORM-EQUILIBRIUM-PAYOFF` | `M`, `L`, `C` | [`GameTheory.quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`](../UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean) |
| `POSITIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN` | `proved-consumer` | `UNIFORM-EQUILIBRIUM-PAYOFF` | `M`, `L`, `C` | [`GameTheory.quittingGame_exists_uniformEquilibriumPayoff_of_admissiblePath_payoffNearReturns`](../UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean) |

The open producer arrows are:

- `VANISHING-DEBT-ATOM-ACCESS` to `CHRONOLOGICAL-DEBT-SHADOWING`: Missing: construct a two-tier input for the checked budget-stable iteration theorem. The actual reached-port packet system must retain two fixed actual labels, give exact literal source/successor anchoring, one globally bounded annotation family, and an operationally sublinear seam-plus-radius-loss modulus. Separately, an external source/payoff-to-candidate adapter must provide the compiler's small-debt seed, unless a solved-game disjunct is returned. A positive-minimum actual port cannot itself be that seed, and semantic closeness cannot pay the resulting fixed debt gap. Once both tiers are supplied, `exists_chronologicalDebtShadowingCertificate_of_seed` recursively selects compatible blocks and proves every same-root survival law. A universal exact-spine two-label selector is impossible even for two players.
- `PAID-FIRST-DISAGREEMENT-ROW` to `POSITIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN`: Missing: fix one positive charge threshold while making endpoint payoff vectors arbitrarily close. Every such family must leave the separated tight-face payoff neighborhood, activate a Quit owner outside that face, or contain a nonperturbative collision row; a source-matched collision path additionally pays a fixed positive terminal-semantic debt excursion above the minimum fiber.

The DAG nodes have these mathematical meanings:

- `POSITIVE-MINIMUM-DEBT`: The attainable terminal semantic carrier has strictly positive minimum total debt; for a nonempty finite player type this is equivalent to nonexistence of a uniform-equilibrium payoff.
- `EXACT-DIAGONAL-FRONTIER`: A positive minimum supplies one positive-minimum tangent family whose active mover diagonal is exactly minus base debt and whose full-replacement mover debt tends to zero.
- `FINITE-SUPPORT-RANK-EXIT`: Repeated minimum-fiber re-extraction terminates because positive-debt support cardinality strictly decreases, or an explicit finite-support-rank alternative is reached.
- `POSITIVE-TOTAL-SLOPE`: One active mover has strictly positive total tangent slope.
- `ZERO-DEBT-SUPPORT-ENTRY`: A flat active tangent column has a positive coordinate at an actual zero-debt recipient.
- `FLAT-CHARGED-CIRCULATION`: The flat tangent columns admit normalized positive charged balance.
- `PAID-FIRST-DISAGREEMENT-ROW`: An off-minimum full-replacement cluster carries a fixed-gain exact paid first-disagreement row eventually along one retained subsequence.
- `VANISHING-DEBT-ATOM-ACCESS`: Every extracted positive-minimum tangent family has a fixed positive off-diagonal observer and an eventually available atom alternative whose endpoint observer debt tends to zero. In the support-entry branch the actual zero-debt recipient can be retained.
- `CHRONOLOGICAL-DEBT-SHADOWING`: Certificates at every positive accuracy compile to terminal approximate Nash profiles and one uniform-equilibrium payoff.
- `POSITIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN`: A fixed positive charge threshold, with source, target, path, and charged edge allowed to vary with endpoint tolerance, and endpoint payoff vectors converging arbitrarily closely, compiles to a uniform-equilibrium payoff.
- `UNIFORM-EQUILIBRIUM-PAYOFF`: Existence of one fixed payoff target satisfying the uniform finite-horizon equilibrium contract.

<!-- END GENERATED OPEN LEAVES -->

A change to this DAG belongs first in `QuittingProofFrontier.json`. The
generated block above must not be hand-edited. Earlier named-leaf censuses,
issue mappings, strengthening chronology, and keep/drop records are
repository-transition provenance and belong only in `TRANSITION.md`, not in
the live mathematical ledger.

## Serious routes that remain available

- **Positive construction:** produce one of the inputs accepted by an
  integrated compiler, or add a new compiler whose output reaches terminal
  approximate Nash existence.
- **Reached-source packet construction:**
  `exists_frozenRadialLiteralFiniteProfilePackets` constructs the frozen-source
  core of the conditioned packet problem on the flat charged-circulation
  branch. It gives literal roots from the actual profile, exact semantic-prefix
  provenance, two fixed active movers with a common hazard coefficient, and a
  global bound. At the actual all-Continue successor,
  `frozenRadialLiteralPacket_twoLabel_availableConditionedKernel` identifies
  both retained live hazards with exact posterior mixtures and gives positive
  two-sided availability when the prior weights are strict and both component
  survivals are positive. `abs_frozenRadialReachedWeight_sub_le` gives the
  sharp denominator-dependent posterior-loss estimate. Strict circulation
  weights and the source-to-inner survival comparison now sharpen this to
  `exists_frozenRadialStrictPackets_available_or_exploitablySourceKilled`:
  every sufficiently late literal packet either has the positive-radius
  conditioned kernel or one of its two original source marginals surely quits
  before the cutoff while retaining a fixed positive deviation debt. This is
  not restartability. The killed-source alternative still needs a strategic
  dispatch or a different source, and the available alternative still needs
  identification with a later frozen source and replacement. Alignment with
  the atom mover/observer labels also remains open. The separate
  artificial-candidate anchor remains Tier II.
- **Four-player analytic dispatch:** on a packet with exactly two supported
  owners, `exists_uniformEquilibriumPayoff_of_support_eq_pair_of_first_noHarm`
  closes either aligned no-harm chamber. Under a counterexample witness,
  `exists_crossedSpectators_of_finFour_support_eq_pair` proves that the two
  remaining players have opposite strict singleton preferences between the
  supported owners. Thus the crossed-spectator chamber is the exact unresolved
  support-two case. In that chamber
  `supportOwners_negative_or_crossedSpectators_preempt` forces, for each
  supported owner, either a full terminal-gap negative-solo alternative or a
  strict preemption edge from the oppositely aligned spectator. The checked
  LCP screen also excludes three of the six possible two-player
  nonprojective principal faces. The exact collision-rate layer now removes the
  real parameter: strict owner differences force rate zero or one, while the
  equality face is equivalent to the finite division-free sign/cross-product
  test `finiteAffineIntervalFeasible_iff`. Under a terminal witness,
  `generic_supportPair_collisionDefects` turns failed strict-sign repairs into
  literal positive spectator join defects, and
  `isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin` either promotes such
  a join to a sure-exit set or exposes a further strict toggle. These checked
  finite faces are now collected symmetrically by
  `nonempty_finFourCrossedSupportTwoFiniteResidual`. Positive lower- and
  upper-endpoint spectator defects anchor a reachable simple selected-toggle
  cycle through `exists_reachableStrictToggleSimpleCycle_of_lowerSpectatorDefect`
  and its upper-defect analogue. The cycle is even and has length between four
  and sixteen. It is only a static reward-table cycle: no checked theorem turns
  it into a quitting chronology or an equilibrium certificate. A full `Fin 4`
  singleton dispatch still needs that consumer and the support-three and
  support-four packet cases.
- **Fused four-player counterexample restrictions:** positive packet support
  is punishment-normal, and
  `exists_normal_packetPair_not_mutuallyPreempting` selects two positive
  packet atoms with positive reciprocal normalized-matrix sum that cannot
  strictly preempt one another in both directions at the terminal gap. Full
  recursive normal core upgrades the principal returned-block obstruction to
  `hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample`, with
  no off-core support restriction. A canonical positive-debt tail also has one
  strict covector, summable absorption, and eventual positive suffix survival.
  These restrictions are simultaneous, not contradictory: no checked adapter
  turns that tail or packet into returned blocks with little-o Bellman and
  endpoint error.
- **Simon viability route:** `markovReturnPotential` constructs the canonical
  target-stopped return potential, and
  `exists_statewiseMarkovVariationBudget_of_returnBound` compiles the
  supportwise nonreturn estimate into the statewise Poisson certificate used
  by `finiteExpectedSpaceTimeMarkovVariation_le_card`. The checked
  three-state regression `not_supportwise_returnBound` proves that bounded
  backward harmonicity does not imply that pointwise estimate. The exact
  source-state decomposition
  `finiteExpectedSpaceTimeMarkovVariation_eq_sum_stateOwned`, the canonical
  stopped-return visit charge bound
  `finiteExpectedMarkovReturnVisitCharge_le_one`, and the aggregate compiler
  `finiteExpectedSpaceTimeMarkovVariation_le_card_of_visitEpoch` expose the
  exact per-state bookkeeping, but do not supply a valid universal
  factorization.
  The four-state regression
  `ConditionalReturnBoundCounterexample.not_homogeneousBackwardHarmonicRenewalPrinciple`
  proves that bounded backward harmonicity also does not imply the formerly
  proposed one-visit averaged condition `HasConditionalMarkovReturnBound`.
  The seven-state regression
  `SevenStateVisitEpochCounterexample.not_homogeneousBackwardHarmonicVisitEpochPrinciple`
  further refutes the aggregate per-owner visit-epoch principle: its owner
  variation already exceeds one although every finite return-visit charge is
  at most one. Thus `HasMarkovVisitEpochBound` remains a sufficient supplied
  interface, not the honest universal renewal theorem. None of these examples
  refutes Simon's global cardinality bound; the seven-state example only
  exceeds the per-owner constant one. A proof of the global bound must use
  genuinely coupled cross-state information rather than one independent
  return account per state.
  `infiniteExpectedENNVariation_le_of_finite` supplies the generic
  finite-to-infinite monotone-convergence step.
  The generic cylinder-law bridge is checked in
  `MathUE/Probability/FinitePathLawAdapter.lean`:
  `hasAdaptiveFiniteMarginals_of_cylinder` identifies finite marginals from
  exact cylinder masses, and
  `finiteExpectedENNVariation_spaceTime_eq_ofReal` identifies the finite path
  integral with the finite-history PMF account. Simon Lemma 2 still needs the
  global cross-state cardinality estimate. A positive
  restartable graph extension does produce one compatible path with a
  linearly diverging prefix budget and `QuestionOneConclusion`; the seven
  generic hypotheses do not currently imply that restartability or a
  certificate.  This claim is scoped to those hypotheses, not to the direct
  approximate-equilibrium-to-uniform-payoff adapter elsewhere in the quitting
  development.  Full Simon Theorem 3 remains open.
- **Simon survival-crossing repair:** actual floor-clipped attainability by a
  unilateral continuation deviation, simultaneous support purification, and
  the strict first-crossing interval are checked in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SurvivalCrossingRepair.lean`.
  The deviation has payoff at least the clipped floor (whose definition
  contains the explicit slack); no attained best-response supremum is
  asserted.  The purified-row certificate feeds the first-crossing theorem
  directly.  Separately,
  `exists_rootSequence_reached_supportPurification_of_approximateEquilibriumExistence`
  obtains support-optimal purified rows from an actual approximate-equilibrium
  sequence with an explicit product-law modulus, and
  `reached_supportPurifiedPrefix_compatible` in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/FinitePrefixCompatibility.lean`
  recomputes any uniformly reached finite window into an exact Bellman prefix
  with a linear seam bound.
  `lowSurvivalPrefix_or_exists_bounded_supportBellmanSpine_of_approximateEquilibriumExistence`
  in `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/ReachedPrefixCompactification.lean`
  compactifies the fixed-reach prefixes into one bounded support-Bellman spine,
  or retains a literal low-survival approximate prefix.
  `QuittingPayoffTable.approximateEquilibriumExistence_iff_zeroNever` gives the
  exact arbitrary-Never behavioral normalization used by AGKRS, and
  `QuittingPayoffTable.lowSurvivalPrefix_or_exists_boundedSupportBellmanSpine`
  applies this alternative with the canonical reward bound. If the compact
  spine's joint survival vanishes after every restart,
  `quittingWellSupportedAbsorbingSequenceAt_of_boundedSupportBellmanSpine_of_jointSurvival`
  identifies its displayed values with actual suffix payoffs and produces the
  pointwise well-supported branch. On the low-survival source,
  [`QuittingLowSurvivalFirstCrossingSourceAt.repairedSurvivalWindow`](../UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/LowSurvivalSourceAdapter.lean)
  now selects the canonical first crossing,
  transfers reached Nash to its predecessor, purifies the actual row against
  its actual tail, constructs the floor-clipped certificate from the shifted
  source profile, and lands in the repaired survival window. A separately
  supplied source-matched near-total row also compiles to the instant branch.
  No Simon branch follows from low cumulative survival alone: the positive-
  window arm still needs normalized near-feasibility, no-sure-quitter, and a
  uniform survival constant, while the instant arm needs cofinal near-total
  rows. The spine branch still needs the all-restart survival condition (or an
  equivalent semantic boundary); compactification does not supply it. No
  global perfect sequence or finite orbit is produced.
- **Simon compact alternatives:** the near-total-absorption branch is checked
  in `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/CompactQuantitativeAlternatives.lean`:
  `quittingInstantPunishmentεEquilibriumExistence_of_nearTotalSupportRows`
  rounds a sufficiently small Continue coordinate to a sure Quit and produces
  the instant-punishment branch.  The normalized-motion producer, the common
  positive survival constant, and Simon Lemma 2 remain open.
- **Simon positive-absorption splice:**
  `quittingStationarilyGeneratedApproximateEquilibria_of_positiveAbsorptionStationary`
  in `UniformEquilibrium/Quitting/Classification/Existence/PositiveAbsorptionStationarySplice.lean`
  checks that a cofinal family of stationary approximate equilibria with
  positive absorption generates the stationarily generated branch, against
  arbitrary behavioral deviations.  The cofinal positive-absorption
  hypothesis is not automatic in the zero-solo class.  The direct residual
  corollary `quittingApproximateEquilibriumExistence_of_stationarilyGenerated`
  and the direct adapter
  `quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence`
  consume the resulting approximate profiles without requiring a cycle
  classification.
- **Simon equilibrium-to-positive-cycle assembly:** exact charged forward
  packets in one compact carrier close to positive cyclic `F_epsilon` orbits,
  and the periodic support-witness consumer turns those cycles into a
  uniform-equilibrium payoff.  The primary supplied hard-branch conclusion is
  the disjunction `IsQuittingZeroSolo reward ∨
  QuittingSimonArbitrarilyChargedForwardPacketCondition reward`; off zero solo
  it yields the positive-cycle branch.  The audited approximate paths have not
  been seam-exactified into exact packets in one common carrier, so the
  necessity direction remains conditional and no arbitrary-game packet
  producer is available.  This seam adapter is substantive, not a naming or
  bookkeeping step.  Raw packet absorption charge is not Euclidean
  finite-orbit variation and does not automatically supply the finite-
  variation obstruction.
- **Simon stationary gate:**
  `zeroSolo_or_stationarilyGenerated_or_standardQMatrixSide` in
  `UniformEquilibrium/Quitting/Classification/LCP/ZeroSoloGeneratedStandardQ.lean`
  gives the checked trichotomy: every own singleton reward is nonpositive, or
  the stationarily generated residual, or standard-Q.  It uses no
  normal-player or sign-pattern dependency.  The direct residual corollaries
  and the direct approximate-existence-to-uniform-payoff adapter are checked,
  but the standard-Q side and full Simon Theorem 3 remain open.
- **Projective Q-bar principal restriction:**
  `exists_punishmentNormal_singletonPath_of_projectiveQBar` and the ambient
  path/rate interfaces are checked for the punishment-normal principal matrix.
  `quittingPunishmentNormalPathDecoder_of_snell` proves the formerly supplied
  decoder through the exhaustive deleted-survival fork: a positive limit gives
  a normal no-harm singleton owner, while all zero limits give actual
  logarithmically discretized product profiles at one fixed target.
  `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` therefore closes
  the ambient projective-Q-bar branch against every behavioral deviation.
  This does not solve `ResidualHardClass`, whose full matrix is not projective
  Q-bar.
- **Cyclic singleton escort route:**
  `BalancedSingletonCycleCertificate.exists_escortCycle` proves the full escort
  necessity and `hasQuittingCanonicalEqualHazardTailData_iff` gives the exact
  criterion for the canonical equal-hazard tail data. `QuittingCyclicSingletonOpenSignData.isUniformEquilibriumPayoff`
  is a direct arbitrary-behavior producer for the open-sign class at every
  finite cyclic size, with an exact four-player instance in
  `CyclicSingletonFourPlayer.isUniformEquilibriumPayoff`. The escort theorem
  guarantees at least two vertices, not exactly two; neither the arbitrary-
  sign producer nor a semantic adapter for all cyclic matrices is supplied.
- **Solo-hazard boundary obstruction:**
  `Schedule.one_over_sixtyEight_lt_literal_exploitability` checks that every
  finite or infinite deterministic at-most-one-owner calendar on the
  Solan--Vieille boundary table has literal all-behavior terminal
  exploitability strictly above `1/68`.  The proof includes the infinite
  deleted-clock/friction telescope and the stronger quadratic inequality
  `1 <= 14 * E^2 + 67 * E`.  Thus a universal chronological producer cannot
  use only single-owner rows on this residual-hard table.  The packet's
  rational upper schedule and the exact optimal solo-hazard floor remain
  unformalized; the checked two-owner period-two equilibrium is unaffected.
- **Returned-block tangent obstruction:**
  `hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks` proves that
  bounded returned product blocks with vanishing total hazard and aggregate
  Bellman and endpoint regret little-o of that hazard force a homogeneous
  simplex solution of the normalized singleton matrix, with arbitrary varying
  phase counts.  `relativeError_gap_of_noHomogeneous` gives the stronger
  explicit converse scale and relative-error gap from the `R0` margin.
  `ResidualHardClass.exists_pos_ambientNormalCoreReturnedBlock_relativeError_gap`
  uses the exact pure-Continue coordinate-deletion law to transfer this gap to
  ambient blocks whose hazards vanish off the recursive normal core. This is a
  reduction on supplied local blocks, not a block producer, chronology, or
  unrestricted-behavior equilibrium consumer.
- **Strict-covector positive-survival cost:**
  `QuittingConvergentDiffuseExactFloorTail.uniformPayoff_or_exists_strictCovectorPositiveSurvival`
  gives one common normalized covector on every late finite and infinite
  horizon of any convergent diffuse exact floor tail. On the unsolved branch
  it derives summable absorption, suffix survival tending to one, and eventual
  positive Never mass. `QuittingSummableExactValueTail.suffixGain_tendsto_max_solo`
  computes the exact unrestricted behavioral suffix-gain limit as the positive
  part of the solo payoff. The canonical dynamic-tail adapter is checked and
  needs no `ResidualHardClass` hypothesis; attaching or paying a positive-solo
  Never atom remains a producer obligation.
- **Supplied Simon obstruction:** the production correspondence now makes the
  individually rational, near-feasible finite-orbit carrier and its finite-variation
  obstruction explicit. `HasQuittingSimonFiniteCellLyapunovCertificate` and
  its direct obstruction adapter consume supplied exact cell coverage, bounds,
  and descent inequalities; the terminal-gap capstone combines that adapter
  with the separately supplied necessity implication. Rational-polyhedral
  certificates remain generic soundness inputs, and no source certificate,
  strategy extraction, or chronological realization is provided.
- **Repaired-stress certificate no-go:**
  `not_exists_stressSimonStrictPotential` embeds the repaired four-player
  stress circulation into the full production correspondence as a positive-
  cost cycle at every positive tolerance. Consequently
  `not_hasQuittingSimonFiniteCellLyapunovCertificate_stressWeight` excludes
  every positive-coefficient finite-cell Lyapunov certificate for that table.
  This eliminates one candidate for the negative Simon route; it is not an
  obstruction for all quitting games and gives no equilibrium-nonexistence
  conclusion.
- **Sharper charge-tangent dispatch:** every extracted charge-tangent datum
  either already has the complementary singleton-mixture payoff, crosses the
  smaller solo/punishment boundary gap, or has positive tangent on an active
  owner. A terminal-exploitability witness removes the first arm. The two
  remaining alternatives still require their respective chronological or
  admissible-return consumers.
- **Reached-source atom reprojection:** construct one executable finite block
  from one actual reached source while retaining the atom labels and controlling
  prescribed, cap, and deleted-clock errors by one explicit modulus.
- **Budget-stable packet iteration:**
  `exists_chronologicalDebtShadowingCertificate_of_seed` recursively chooses
  successive reached-source packets, keeps their availability radii positive,
  and turns two divergent actual label clocks into all deleted-survival laws.
  It requires a globally bounded actual-port packet system plus a separate
  external small-debt candidate adapter or a solved-game disjunct. A
  positive-minimum actual port cannot itself supply that seed. Producing these
  two-tier inputs remains open; the all-frontier consumer beyond them is a
  conjecture-equivalent reformulation.
- **Paid-row payoff near-return:** fix one positive charge threshold, while
  allowing the source, target, path, and charged edge to vary with endpoint
  tolerance, and make endpoint payoff vectors arbitrarily close. Fixed-edge
  payoff closure and exact return are stronger special cases.
- **Global barrier:** find a forward-invariant coupled semantic barrier with a
  positive debt floor, then consume it through the terminal-gap theorem.
- **Vanishing discount:** decode analytic Bellman data into a strategically
  credible target and executable continuation architecture.
- **Bounded architectures:** verify or synthesize fixed controller classes,
  without inferring completeness for unrestricted behavior.

The current bounded reverse-search questions are indexed in
[`../Reverse/Tasks/README.md`](../Reverse/Tasks/README.md).

## Decisive fences

Any current argument must respect these distinctions:

- quitting games do not settle general finite stochastic games positively;
- a verifier for supplied data is not a producer for arbitrary games;
- an integrated theorem may still be conditional;
- a compact coefficient projection need not be a closed space of realized
  strategic blocks;
- positive debt along one explicit chain is not positivity of the optimized
  minimum;
- terminal, limiting-average, discounted, and uniform finite-horizon notions
  require named bridges; and
- experiments and Research modules are evidence until promoted and consumed.

## What counts as resolution

**Positive quitting resolution:** an unconditional theorem producing terminal
approximate Nash profiles at every positive error for every finite quitting
game, followed by the integrated terminal-to-uniform consumer.

**Negative quitting resolution:** one explicit finite reward table and one
fixed positive gap, with a theorem that every behavioral profile admits a
unilateral terminal gain at least that gap, followed by the integrated
nonexistence transfer.

**Meaningful intermediate resolution:** prove or consume one of the open DAG
arrows, produce a substantial new unconditional class, prove a sharp
nonclosedness or no-go theorem that changes the required state, or connect a
producer to a semantic consumer with an actual-data
adapter.

## Where new ideas live

The extracted repository intentionally has no `ideas/` directory. The project
workflow is:

- unresolved derivations and exploratory proof strategies: GitHub Discussion;
- bounded mathematical or engineering obligations: GitHub Issue; and
- checked integration: Pull Request.

Exact reproducible computations remain in `Experiments/`, compileable but
unsettled Lean remains in `Research/`, and reverse proof-search packets remain
in `Reverse/`. See [`PIPELINE.md`](PIPELINE.md) for the promotion contract.
