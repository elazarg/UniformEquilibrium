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

Two concrete producer arrows remain explicit. Static vanishing-debt atom data
must be serialized into chronological debt-shadowing certificates at every
positive accuracy, or an eventually paid row must be re-entered as one
one fixed positive charge threshold, while the source, target, path, and
charged edge may vary with endpoint tolerance and endpoint payoff vectors
become arbitrarily close. Fixed-edge payoff closure and exact return to the
full tail state are stronger special cases. The chronological and
payoff-near-return consumers themselves are proved in Lean.

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
| `VANISHING-DEBT-ATOM-ACCESS` | `open-producer` | `CHRONOLOGICAL-DEBT-SHADOWING` | `L` | [`GameTheory.VanishingDebtAtomChronologicalConsumer`](../UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean) |
| `PAID-FIRST-DISAGREEMENT-ROW` | `open-producer` | `POSITIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN` | `L` | [`GameTheory.PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer`](../UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean) |
| `CHRONOLOGICAL-DEBT-SHADOWING` | `proved-consumer` | `UNIFORM-EQUILIBRIUM-PAYOFF` | `M`, `L`, `C` | [`GameTheory.quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`](../UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean) |
| `POSITIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN` | `proved-consumer` | `UNIFORM-EQUILIBRIUM-PAYOFF` | `M`, `L`, `C` | [`GameTheory.quittingGame_exists_uniformEquilibriumPayoff_of_admissiblePath_payoffNearReturns`](../UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean) |

The open producer arrows are:

- `VANISHING-DEBT-ATOM-ACCESS` to `CHRONOLOGICAL-DEBT-SHADOWING`: Missing: serialize the static whole-law atom alternatives into executable tails with bounded forcing, vanishing survival, and small initial debt at every accuracy.
- `PAID-FIRST-DISAGREEMENT-ROW` to `POSITIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN`: Missing: fix one positive charge threshold, while allowing the paid-row realization's source, target, path, and charged edge to vary with endpoint tolerance, and make endpoint payoff vectors arbitrarily close.

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
- **Simon viability route:** the conditional finite-horizon core
  `finiteExpectedSpaceTimeMarkovVariation_le_card` bounds expected
  space-time variation from a supplied statewise escape/Poisson certificate.
  Simon Lemma 2 remains open because that escape/Poisson certificate and the
  infinite adapter from return probabilities are not produced.  A positive
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
  directly.  Coordinate closeness and the positive survival lower bound remain
  conditional on supplied endpoint modulus,
  normalized near-feasibility, no-sure-quitter, and corrected uniform-survival
  predicates, with an explicit positive `ρ`.  No global conditioned prefix or
  finite orbit is produced.
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
  path/rate interfaces are checked for the punishment-normal principal matrix,
  and the downstream decoder consumers are checked. The ambient
  omitted-player/minmax lift is checked by
  `ContinuousZeroPerfectSingletonPath.ambientLift`. The central
  `QuittingPunishmentNormalPathDecoder` is not proved: logarithmic-rate and
  integral reconstruction, the deleted-clock Snell identity and
  exceptional-owner split, uniform product-law discretization, and the
  conversion to actual terminal payoffs against every behavioral deviation
  remain open. Thus projective Q-bar is a strong conditional route and forces
  any counterexample surviving the decoder to fail on a normal principal
  subset; it is not yet a theorem for all quitting games.
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
  Principal-reward and recursive-normal-core adapters are checked for literal
  restricted blocks.  This is a reduction on supplied local blocks, not a
  block producer, chronology, or unrestricted-behavior equilibrium consumer;
  ambient zero-off-subset block restriction remains a separate adapter unless
  explicitly supplied.
- **Supplied Simon obstruction:** the production correspondence now makes the
  individually rational, near-feasible finite-orbit carrier and its finite-variation
  obstruction explicit. `HasQuittingSimonFiniteCellLyapunovCertificate` and
  its direct obstruction adapter consume supplied exact cell coverage, bounds,
  and descent inequalities; the terminal-gap capstone combines that adapter
  with the separately supplied necessity implication. Rational-polyhedral
  certificates remain generic soundness inputs, and no source certificate,
  strategy extraction, or chronological realization is provided.
- **Sharper charge-tangent dispatch:** every extracted charge-tangent datum
  either already has the complementary singleton-mixture payoff, crosses the
  smaller solo/punishment boundary gap, or has positive tangent on an active
  owner. A terminal-exploitability witness removes the first arm. The two
  remaining alternatives still require their respective chronological or
  admissible-return consumers.
- **Chronological atom production:** serialize the fixed vanishing-debt atom
  access into executable reached tails satisfying the checked shadowing
  certificate at every positive accuracy.
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
