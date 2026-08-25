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

Two further stationary classes sharpen the incentive-gadget boundary.
`quittingGame_exists_uniformPayoff_of_cycleBalancedSignConsistentInfluence`
(`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`)
constructs a literal sure-exit coalition whenever every pair influence has one
fixed positive, negative, or absent sign and every directed simple influence
cycle has positive sign product. The construction switches polarities within
strongly connected components and freezes the components in condensation
order; no single global polarity is assumed. The converse
`exists_negativeSimpleInfluenceCycle_of_no_sureExitSet` shows that a negative
simple cycle is necessary for any fixed-sign table without a sure-exit
escape. This is an unrestricted-behavior equilibrium theorem, but it says
nothing about influences whose signs change with the coalition background.

The separate augmented solo-preemption graph has an exact checked boundary.
Its bottom vertex points to a player with positive own singleton reward, a
player points to bottom when that reward is negative, and `i -> j` records
that `j` strictly prefers its own singleton to `i`'s singleton row.
`exists_uniformEquilibriumPayoff_of_acyclic_augmentedSoloPreemption`
(`UniformEquilibrium/Quitting/Classification/Existence/AcyclicSoloPreemption.lean`)
proves that acyclicity gives either exact all-Continue play or a solo-owner
stationary family with fixed singleton target and all-behavior exploitability
at most `q * quittingSoloPairPremium`. In the latter family absorption is
almost surely at the owner's singleton, so both designated incentive-gadget
pair masses are zero at every positive rate. Thus a directed augmented cycle
is necessary for that gadget architecture. The theorem neither makes such a
cycle sufficient nor constrains rewards of coalitions with at least three
quitters.

The finite odd negative-cycle boundary also has a checked positive result.
`isUniformEquilibriumPayoff_of_literalStrictFiniteOddIntervalBlockerCore`
(`UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCoreRowAdapter.lean`)
gives an exact stationary all-behavior uniform-equilibrium payoff for every
embedded odd cyclic blocker core of finite size at least three whose literal
row extrema satisfy
`L_i^+ < C_i^- <= C_i^+ < H_i^-`. Core continuation rewards may vary by
absorbing coalition within their separated band. Arbitrarily many outside
players and all their reward coordinates remain unrestricted. The literal
family has `M`, `L`, `A`, and `C`: checked row extrema enter the stationary
certificate, which enters the unrestricted-behavior uniform-payoff consumer.
The constant-passive declarations in
`UniformEquilibrium/Quitting/Classification/Existence/FiniteOddBlockerCoreRowAdapter.lean`
remain a separately checked special case. Neither theorem covers overlapping
or weak bands, same-background signs without the global extrema sandwich, or
arbitrary negative influence cycles.

Participant-only rewards form another checked architecture-level no-go.
`exists_stationary_uniformEquilibriumPayoff_of_participantOnly`
(`UniformEquilibrium/Quitting/Classification/Existence/ParticipantOnlyStationary.lean`)
constructs an exact stationary terminal Nash profile against unrestricted
unilateral behavioral deviations for every finite table whose absent-player
coordinates vanish, and supplies its uniform-equilibrium payoff. For an
arbitrary table, `exists_stationary_isTwoPassiveMagnitudeAsymptoticNash` and
`half_terminalExploitabilityGap_le_quittingPassiveMagnitude`
(`UniformEquilibrium/Quitting/Classification/Existence/ParticipantOnlyPerturbation.lean`)
give a stationary profile with terminal exploitability at most twice the
empty-safe largest passive reward magnitude. Thus a fixed terminal gap
`gamma` requires passive magnitude at least `gamma / 2`. The pointwise source
predicate and participant projection are checked actual-table adapters. The
results have `M`, `L`, `A`, and `C`; they do not give exact equilibrium
existence for arbitrary non-participant-only tables.

The six-player direct cross-penalty architecture now has a checked exact
ledger and matching obstruction.
`integerReward_exploitability_ge` and
`integerReward_mass_and_leftover_of_exploitability_le`
(`UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean`)
show that its complete integer table forces
`Expl >= 31 * (1-a) / 66 >= 31 * ell / 66` for every behavioral profile.
The generic theorem
`exactCoalitionMass_ge_of_targetCrossPenaltyCompletion` takes an explicit
terminal `epsilon`-Nash premise, and the robust `[-1,1]` outsider completion
retains the stated `17/8` mass bounds. Every such completion nevertheless has
the pure first target as an exact all-behavior terminal Nash profile and a
uniform-equilibrium payoff, so it cannot force the second pair. These ledger,
completion, and target-lock results have `M`, `L`, `A`, and `C`.
`sqrt_firstPairMass_add_sqrt_secondPairMass_le_one`
(`UniformEquilibrium/Diagnostics/Quitting/SixPlayerArbitraryProfileClockAdapter.lean`)
constructs the literal live-root clock, proves the two squared-amplitude
identities, and identifies their sums with the actual terminal atoms. Thus
`integerReward_secondPairMass_le` removes the former supplied `hclock`
premise and has `M`, `L`, `A`, and its quantitative `C`. Positive second-pair
production and a fixed exploitability gap remain open.

The watchdog obstruction is also sharper, but stops at a precise topology
lemma. Strategically totally bounded reply families cannot force a fixed
profile-dependent gain, complete such families compile to a uniform payoff,
and allowing one arbitrary nonprecompact player range does not change the
conclusion. Thus every surviving selector has two distinct identities with
fixed late-finite mass beyond every horizon. The new
`exists_lateOrNeverMass_escape_of_not_properStrategicallyApproximable` and
`exists_nonproper_essentialNeverWitness_of_totallyBounded`
(`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`)
show, conditionally on failure of proper strategic approximation, fixed
late-or-Never escape and a nonproper essential Never witness in every
strategically totally bounded range. The compact stopping-law space and its
finite barycenters are checked in
`MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`. The proper-sentinel
compact-game theorem is not checked: it still needs joint weak continuity of
terminal payoff when the sentinel ranges over the convex hull of finitely many
proper laws and all other players range over the full compact law space.
Accordingly, the metric consequences have `M` and `L`, with actual stopping-law
adapters, but the selector-wide proper-sentinel consumer has no `C` seal.

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
shows the three surviving tagged exit arms and the checked consumers beyond the
remaining producer gaps.

Finite support-rank termination leaves positive total slope, zero-debt support
entry, or an eventually paid first-disagreement row. Theorem
`QuittingPositiveMinimumDebtTangentFamily.reducedSupportRankAlternative_of_positiveMinimumDebt`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean`)
removes flat charged circulation as an independent terminal tag: in either
flat no-entry branch, an arbitrary active mover's actual full-replacement
endpoint either lies on the minimum fiber and strictly lowers the finite
positive-debt-support rank, or lies off that fiber and carries the existing
eventually paid row. The three surviving tags are mathematically distinct;
none of their producer obligations is thereby solved. There is also a stronger
branch-independent adapter: every extracted frontier already has fixed
vanishing-debt atom access. In the support-entry arm the actual zero-debt
recipient can be retained as the atom observer. The reduced termination has
`M`, `L`, and `A`; the conditional three-consumer capstone has `M`, `L`, and
`C`. Neither seal set asserts the missing producers.

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

On the paid route, including the former flat-circulation arm after its finite
support descent, the former prescribed-payoff floor obstruction is removed.
At positive minimum debt, every attained paid source has an actual-source
cap-lifted exact orbit: its absorption is summable with a quantitative debt
budget, the unchanged paid suffix has a uniform debt-ratio reach floor, every
finite literal prefix carries a shifted paid row with fixed positive gain,
and the full terminal semantics converge to an all-Continue carrier port. A
nonzero displacement also retains one fixed signed terminal coalition with a
quantitative cumulative mass budget. The remaining downstream step is the
restart or debt/support descent spending this paid or signed summable-port
budget; no such consumer is checked.

For a separate actual carrier-root family with one fixed absorption floor,
`exists_macroscopicDebtDrop_or_chargedSoloBlockerGate` now proves positive
liminf semantic debt descent or a strict-subsequence gate with one mixed solo
debtor and a maximizing punishment-normal blocker. The source-native consumer
`FinFourChargedSoloBlockerGate.pairPremium_or_every_exactRepayment` forces a
fixed pair premium or fixed repayment in that blocker coordinate along every
anchored exact floor orbit. The premium arm is now consumed by
`FinFourChargedSoloBlockerGate.pairBaseHandoff_or_leaveJoinHandoff_or_everyExactRepayment`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ChargedSoloBlockerClosureDispatch.lean`):
it enters an actual pair-base or leave--join stationary source with a
terminal-gap paid row. The other arm remains one-coordinate repayment, and
the gate's literal exact root has zero semantic-debt drop. This is a checked
off-minimum obstruction, not the missing all-coordinate paid return. The
separate pair-base fixed-law reset identifies the returned face's prescribed
payoff exactly with its stationary paid target. The target now has an exact
boundary: a forced-base punishment-floor violation, or an independently
selected exact punishment-floor endpoint edge at that payoff. The former has
a later-receiving paid-row repair; the latter is positive unless it is the
literal all-Continue self-loop. In a counterexample every positive such edge
must escape a fixed payoff neighborhood forever, so it cannot supply the
missing admissible return.

The solo-wall reduction and its formerly missing stationary-source compiler
are now checked. In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourSoloWallDispatch.lean`,
`exists_strictCarrierDebtDescent_of_opponentAbsorptionFloor` gives strict
carrier-debt descent under a uniform opponent-absorption floor, while
`exists_first_soloPrefix_outsiderWall` reaches a first outsider wall along
literal semantic prefixes. Arbitrarily long finite uniform-solo windows
compactify through `exists_uniformSoloSemanticSpine_of_finitePrefixes`, and
`not_exists_outwardUniformSoloCarrierChain_of_normal` excludes the resulting
infinite outward chain by punishment normality. At the wall,
`pairPremium_pairJoin_or_leaveJoinStationaryTwoDebtorHandoff` returns the
existing singleton-base handoff or a full-gap outsider pair-join. The theorem
`nonempty_finFourPairBaseStationaryTwoDebtorHandoff`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseStationaryTwoDebtorHandoff.lean`)
now consumes the join into an actual stationary source with quantitative
off-base absorption, a heavy strict-superset atom, both free coordinates
solved against unrestricted deviations, base-localized debt, and a literal
paid row. These reductions have `M`, `L`, `A`, and exact-dispatch `C`; the
stationary point is freshly selected rather than chronologically reached, so
there is still no payoff-return `C`.

Seals use the independent `M`/`L`/`A`/`C` language of
[`STATUS.md`](STATUS.md). An `L` seal on an open producer arrow means its
proposition interface is checked, not that the implication has been proved.

<!-- BEGIN GENERATED OPEN LEAVES -->
This dependency table is generated from [`QuittingProofFrontier.json`](QuittingProofFrontier.json).

| From | Status | To | Seals | Checked declaration or open interface |
| --- | --- | --- | --- | --- |
| `POSITIVE-MINIMUM-DEBT` | `proved` | `EXACT-DIAGONAL-FRONTIER` | `M`, `L`, `A` | [`GameTheory.finiteSupportRankAlternative_of_hasPositiveMinimumTerminalSemanticDebt`](../UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean) |
| `EXACT-DIAGONAL-FRONTIER` | `proved` | `FINITE-SUPPORT-RANK-EXIT` | `M`, `L`, `A` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.reducedSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean) |
| `FINITE-SUPPORT-RANK-EXIT` | `proved-branch` | `POSITIVE-TOTAL-SLOPE` | `M`, `L` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.HasQuittingStoppingLawReducedSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean) |
| `FINITE-SUPPORT-RANK-EXIT` | `proved-branch` | `ZERO-DEBT-SUPPORT-ENTRY` | `M`, `L` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.HasQuittingStoppingLawReducedSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean) |
| `FINITE-SUPPORT-RANK-EXIT` | `proved-branch` | `PAID-FIRST-DISAGREEMENT-ROW` | `M`, `L`, `A` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.HasQuittingStoppingLawReducedSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean) |
| `EXACT-DIAGONAL-FRONTIER` | `proved` | `VANISHING-DEBT-ATOM-ACCESS` | `M`, `L`, `A` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.nonempty_vanishingDebtAtomAccess`](../UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean) |
| `ZERO-DEBT-SUPPORT-ENTRY` | `proved` | `VANISHING-DEBT-ATOM-ACCESS` | `M`, `L`, `A` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.exists_vanishingDebtAtomAccess_of_supportEntry`](../UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean) |
| `VANISHING-DEBT-ATOM-ACCESS` | `open-producer` | `CHRONOLOGICAL-DEBT-SHADOWING` | `M`, `L`, `C` | [`GameTheory.QuittingBudgetStablePacketSystem.exists_chronologicalDebtShadowingCertificate_of_seed`](../UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean) |
| `PAID-FIRST-DISAGREEMENT-ROW` | `open-producer` | `CUMULATIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN` | `M`, `L`, `A` | [`nonempty_capLiftedSummablePort_of_tangentFamily`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean) |
| `CHRONOLOGICAL-DEBT-SHADOWING` | `proved-consumer` | `UNIFORM-EQUILIBRIUM-PAYOFF` | `M`, `L`, `C` | [`GameTheory.quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`](../UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean) |
| `CUMULATIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN` | `proved-consumer` | `UNIFORM-EQUILIBRIUM-PAYOFF` | `M`, `L`, `C` | [`GameTheory.quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`](../UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean) |

The open producer arrows are:

- `VANISHING-DEBT-ATOM-ACCESS` to `CHRONOLOGICAL-DEBT-SHADOWING`: Missing: construct a two-tier input for the checked budget-stable iteration theorem. The actual reached-port packet system must retain two fixed actual labels, give exact literal source/successor anchoring, one globally bounded annotation family, and an operationally sublinear seam-plus-radius-loss modulus. Separately, an external source/payoff-to-candidate adapter must provide the compiler's small-debt seed, unless a solved-game disjunct is returned. A positive-minimum actual port cannot itself be that seed, and semantic closeness cannot pay the resulting fixed debt gap. Once both tiers are supplied, `exists_chronologicalDebtShadowingCertificate_of_seed` recursively selects compatible blocks and proves every same-root survival law. A universal exact-spine two-label selector is impossible even for two players.
- `PAID-FIRST-DISAGREEMENT-ROW` to `CUMULATIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN`: The former prescribed-payoff floor obstruction is removed. From the actual attained paid source at positive minimum debt, exact cap-Nash prefixes have summable absorption, uniform paid-suffix reach, shifted paid rows with fixed positive gain, and a full terminal-semantic all-Continue limit port. Missing downstream: restart while spending that paid or signed terminal budget, produce cumulative-charge payoff near-return, or strictly decrease debt/support complexity.

The DAG nodes have these mathematical meanings:

- `POSITIVE-MINIMUM-DEBT`: The attainable terminal semantic carrier has strictly positive minimum total debt; for a nonempty finite player type this is equivalent to nonexistence of a uniform-equilibrium payoff.
- `EXACT-DIAGONAL-FRONTIER`: A positive minimum supplies one positive-minimum tangent family whose active mover diagonal is exactly minus base debt and whose full-replacement mover debt tends to zero.
- `FINITE-SUPPORT-RANK-EXIT`: Repeated minimum-fiber re-extraction terminates at positive total slope, zero-debt support entry, or an off-minimum actual replacement endpoint carrying an eventually paid row. Flat charged circulation is absorbed by strict support-rank descent or the paid-row arm.
- `POSITIVE-TOTAL-SLOPE`: One active mover has strictly positive total tangent slope.
- `ZERO-DEBT-SUPPORT-ENTRY`: A flat active tangent column has a positive coordinate at an actual zero-debt recipient.
- `PAID-FIRST-DISAGREEMENT-ROW`: An off-minimum full-replacement cluster carries a fixed-gain exact paid first-disagreement row eventually along one retained subsequence; this also consumes the former flat-circulation terminal arm after finite support descent.
- `VANISHING-DEBT-ATOM-ACCESS`: Every extracted positive-minimum tangent family has a fixed positive off-diagonal observer and an eventually available atom alternative whose endpoint observer debt tends to zero. In the support-entry branch the actual zero-debt recipient can be retained.
- `CHRONOLOGICAL-DEBT-SHADOWING`: Certificates at every positive accuracy compile to terminal approximate Nash profiles and one uniform-equilibrium payoff.
- `CUMULATIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN`: A fixed positive lower bound on total path charge, with source, target, path, and every individual edge allowed to vary with endpoint tolerance, and endpoint payoff vectors converging arbitrarily closely, compiles to a uniform-equilibrium payoff.
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
- **Four-player full-support residual:**
  `uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual`
  gives an unconditional alternative for every reward table on `Fin 4`.
  Either the game has a uniform-equilibrium payoff, or the same table has a
  terminal exploitability witness, full recursive normal core, all-player
  punishment normality, and a normalized singleton packet with support all
  four players and an explicit positive coordinate floor, together with
  `ResidualHardClass`. Packet supports one, two, and three and the
  projective-Q-bar matrix chamber are therefore not live counterexample
  residuals. The remaining nonprojective proper principal has size two or
  three. `FinFourQuantitativeFullSupportHardResidual.hardPrincipalDispatch`
  puts it in a mutually harmful pair with outside positive helpers, a
  three-principal with an external positive helper, or an internally cyclic
  three-principal with nonpositive determinant.

  The same-table theorem
  `QuittingTerminalExploitabilityWitness.fullSupport_fullNormalCore_with_paidRefinedCycle_of_finFour`
  supplies an actual reachable strict-toggle cycle; its large-base arm is a
  disjoint two-plus-two partition and enters the pure-or-mixed paid normal
  chain. The checked
  `QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle.exists_largeBasePaidStationaryHandoff`
  then reselects a singleton sure-Quit owner and an exact three-free-player
  Nash point. At the resulting stationary source only the owner has positive
  debt; replacing that owner by Always Continue repairs it, transfers the
  terminal gap to a free player, and yields a literal paid
  first-disagreement row. The output is either punishment-floor safe or has
  one identified free-coordinate floor loss. It does not connect the original
  paid boundary face to the reselected source or repay the latter loss.

  Punishment normality also forces literal nonsingleton data at every
  singleton. The theorem
  `FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`)
  selects a distinct outsider whose pair-collision gain is at least the same
  terminal gap. In the rooted-two owner-leave arm,
  `ownerLeaveCollisionChain_outsiderJoin_or_thirdLabelHandoff` either retains
  a full-gap outsider join at the enlarged pair or follows the collider's
  full-gap leave by a full-gap join from a genuinely third label. This
  composition has `M`, `L`, `A`, and `C`; its checked consumer is the
  third-label handoff, not an equilibrium construction.

  The further adapter
  `ownerLeaveCollisionChain_outsiderJoin_or_stationaryTwoDebtorHandoff`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/LeaveJoinStationaryTwoDebtorHandoff.lean`)
  either keeps that enlarged-pair outsider join or constructs an actual
  stationary source. Its leaver and joiner have zero unrestricted behavioral
  debt and lie above punishment; the joiner hazard is at least
  `gamma / (gamma + 2*M)`; one literal pair or triple atom has at least half
  that mass; and positive debt lies on at most the spectator and fourth label,
  with a terminal-gap debtor and literal paid first-disagreement row. This
  source has `M`, `L`, and `A`, but not `C`: no checked return or uniform-payoff
  consumer uses it.

  Owner-label selection itself is no longer an obstruction. At any global
  minimum carrier pair, a chosen positive debtor can be used as the reset
  owner in
  `QuittingTerminalExploitabilityWitness.exists_finFour_prescribedOwner_resetDispatch`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourPrescribedOwnerResetAlignment.lean`).
  The selected complementary-pair Nash row is an actual stationary
  semantic-law target with zero debt in that owner and unit incidence in a
  genuine opponent, and it enters the checked fixed-law reset dispatch. For
  any independently preselected label,
  `QuittingTerminalExploitabilityWitness.exists_prescribedOwner_stationaryHandoff`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PrescribedOwnerStationaryHandoff.lean`)
  supplies a uniform positive singleton-base floor gap and an actual paid
  stationary handoff. These two adapters have `M`, `L`, `A`, and `C` for their
  stated dispatches. Their shared label does not make the selected profiles,
  laws, observers, payoffs, or chronological rows coincide; that common-source
  alignment and the all-Continue reset wall remain open.

  A different pair-base construction now co-realizes more data on one literal
  stationary profile. `nonempty_finFourPairBaseStationaryDebtLocalization`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseStationaryDebtLocalization.lean`)
  solves both players outside any prescribed two-player sure-Quit base and
  localizes a terminal-gap debtor and paid row to the base. Choosing the base
  disjoint from a prescribed reset owner gives
  `QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetAlignment.lean`):
  the same actual profile and law have zero owner debt, unit incidence from a
  base opponent, and the base-localized paid row. This has `M`, `L`, `A`, and
  fixed-law-dispatch `C`, but the paid debtor is not the reset owner. The
  dynamic branch prefixes a separately selected returned semantic pair;
  nevertheless `QuittingFixedLawResetDispatch.prescribed_eq_target` and
  `QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch_payoffAligned`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetPayoffAlignment.lean`)
  prove that its prescribed payoff is exactly the payoff of the stationary
  paid target, because both retain the same complete terminal law.
  Moreover,
  `QuittingFixedLawResetDispatch.allContinue_of_target_debt_le_source`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFixedLawMinimumTargetStall.lean`)
  proves that a target no higher in total debt than the global-minimum source
  forces the all-Continue stall.

  `QuittingTerminalExploitabilityWitness.nonempty_finFour_pairBasePaidResetEndpointBoundary`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointEdge.lean`)
  sharpens the remaining edge problem. Either a forced base coordinate lies
  below punishment, or the aligned payoff is the tail of an exact
  punishment-floor-admissible edge. In the first branch,
  `FinFourPairBasePaidResetTarget.exists_other_and_laterPaidRow_and_floorRepair`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseFloorViolationRepair.lean`)
  produces a source-matched `Quit now`-to-`Never` paid row and an actual
  Always-Continue update which repairs that coordinate to zero debt while the
  other base player still Quits surely. It does not preserve the other
  coordinates' Nash or floor equations. In the second branch the edge has
  positive absorption unless every singleton reward is below the aligned
  payoff, in which case it is the literal all-Continue payoff self-loop.
  `QuittingTerminalExploitabilityWitness.exists_payoffEscapeRadius_of_positiveAdmissibleEdge`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointOrbitEscape.lean`)
  shows that, under the counterexample witness, every positive edge has a
  fixed payoff radius which no state reachable after it can re-enter. Thus
  approximate payoff recurrence is not merely unproved on this branch: it is
  impossible.

  The reset's own cap root remains distinct from that independently selected
  endpoint edge. `capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointSeam.lean`)
  identifies its exact conversion condition as coordinatewise equality of
  option surcharge and survival-weighted debt. Positive survival and positive
  returned debt rule out the simpler support-killing converter. A positive
  literal defect gives an executable unilateral deviation, but loses the
  fixed-law paid provenance and does not yield strict total-debt descent.
  `QuittingFixedLawResetAdmissibleClosureSeam` remains the exact conditional
  uniform-payoff interface, but its return-path field is incompatible with
  the positive-edge escape theorem in a counterexample.

  Separately,
  `FinFourQuantitativeFullSupportHardResidual.exists_collisionGeometry_with_alignedTwoCycleHardPair_or_long`
  proves that in each of the eight marked two-cycle preemption constructors,
  the literal cycle pair is itself the hard card-two crossing.
  `FinFourQuantitativeFullSupportHardResidual.markedThreeCycleHardPrincipalIncidence_or_nonThree`
  sends each of the six length-three constructors to a same-label outside
  helper, a negative-determinant hard triple, or a hard principal forced
  through the unique outsider.
  `FinFourQuantitativeFullSupportHardResidual.markedFourCycleHardPrincipalAlignment_or_nonFour`
  sends each of the three rooted four-cycle constructors to a shorter strict
  cycle or a literal unique-outside helper. Thus all seventeen marked
  constructors have checked finite hard-principal incidence, with exact
  owner/collider role data. The toggle cycle and preemption lasso remain
  independently selected, and these structural refinements do not eliminate
  a semantic chamber or produce a strategy.

  The lasso-incidence theorems have `M`, `L`, and `A`, but not `C`. The
  large-base handoff likewise has `M`, `L`, and `A`: its stationary profiles
  and paid row are actual behavioral source objects.
  `LargeBasePaidStationaryHandoff.endpointAtom_floorFailure_or_exactOrbit`
  sends that source to localized floor failure or a literal exact infinite
  floor orbit. More generally, the cap lift sends every attained paid source
  at positive minimum debt to an exact floor-safe cap orbit without requiring
  its prescribed payoff to be floor-safe. The absorption is summable, the
  unchanged paid suffix has a uniform debt-ratio reach floor, and every finite
  prefix retains a uniformly positive shifted paid row. The full terminal
  semantics converge to an all-Continue carrier port. No checked theorem
  restarts from or spends the paid/signed budget of that labelled port.

  There is now a second same-table semantic restriction on every hypothetical
  `Fin 4` counterexample. First,
  `exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`)
  selects a globally minimum positive-debt terminal-semantic pair `(U,B)` with
  `P_i <= s_i < U_i` for all four players. Its complete debt homotopy
  `B - t(B-U)`, `0 <= t <= 1`, lies in one open payoff tube on which
  all-Continue is the unique exact product root. For each fixed positive
  opponent-incidence floor, `exists_open_totalNashDefect_moat_debtHomotopy`
  also gives one open segment tube with a uniform positive Nash-defect moat.

  The stronger capstone
  `exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`)
  uniformizes this strict singleton gap and exact-root tube over the prescribed
  projection of the entire compact global-minimum carrier fiber. It also gives
  one `epsilon > 0` such that every carrier pair with debt below
  `D_* + epsilon` has prescribed payoff in the tube. The consumer
  `minimumFiber_debt_add_epsilon_le_of_carrierTail_exactRoot_absorption_pos`
  proves the contrapositive: a positively absorbing exact root against a
  carrier tail pays at least that fixed excess debt. The no-uniform Fin4
  capstone has `M`, `L`, and `A`; this carrier-tail obstruction is a checked
  `C`, not a uniform-payoff consumer.

  The generic consumers in
  `UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRigidity.lean`
  have `M`, `L`, and `C`. An exact finite Nash--Bellman path whose terminal
  tail is in such a tube is the constant zero-absorption path; an absorbing
  exact cyclic continuation is impossible; charged exact blocks obey the
  corresponding terminal-seam floor; and an exact infinite path converging
  to an interior tube point is constant from time zero. These conclusions are
  tail-oriented and do not exclude an incoming edge whose continuation is
  nonlocally outside the tube.

  The approximate vanishing-incidence gap inside the tube is now quantified.
  `exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`)
  supplies one bounded open neighborhood of the whole prescribed minimum-
  fiber projection and one `c > 0` such that `c * absorption <= total defect`
  for every local product root, at every scale. The successor consumer
  `successorPath_mem_and_absorptionSum_le_of_linearDefect`
  (`UniformEquilibrium/Quitting/Paths/StrictAllContinueBasinSuccessorPath.lean`)
  bootstraps locality from a terminal point near the fiber: a sufficiently
  small aggregate declared-error budget keeps every exact-successor path node
  in the tube and bounds both total absorption and path diameter by that
  budget. Its contrapositive charges a fixed aggregate-error toll for a first
  exit. The Fin4 composition has `M`, `L`, `A`, and `C`, but it produces no
  path and says nothing about a nonlocal incoming continuation or a
  nonvanishing aggregate-error budget. No checked theorem produces the
  nonlocal incoming edge or return needed to close the conjecture.

  The checked barrier
  `fullSupportPacket_standardQ_nonhomogeneous_but_not_cyclic` shows why the
  remaining step is semantic: an actual packet can simultaneously have full
  support, full normal core, internal crossed rows, a standard-`Q`
  nonhomogeneous matrix, and no cyclic open-sign skeleton under any
  relabeling. This barrier is not a counterexample game. The open task is to
  use nonsingleton coalition rewards or actual Bellman/terminal-semantic data
  to consume the full-support residual.
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
- **AGKRS Theorem 3.4 dependency boundary:** the corrected pointwise source
  analysis now leaves exactly three literal residuals: an all-Continue source
  phantom, a positive-absorption sharp attachment failure, or a persistent
  positive-singleton suffix defect. In the diffuse generated branch, positive
  joint reach gives the instant-punishment branch whenever a reached
  punishment-floor endpoint has a sure-exit Nash prefix; otherwise the source
  records that every such endpoint fails that test. A divergent unique-
  exceptional-owner source with nonnegative owner singleton payoff gives the
  stationary branch. The checked Literature capstone
  `theorem3_4_of_refinedSourceClosures` composes the exclusion of exactly these
  source residuals to the literal S.1/S.2/S.3 conclusion. Those exclusions and
  the required exceptional-owner hypotheses remain open, so the unconditional
  general `theorem3_4` is still the sole proof hole in the paper-facing file.
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
- **Paid-row payoff near-return:** fix one positive lower bound on total path
  charge while allowing the source, target, path, and every edge to vary with
  endpoint tolerance, and make endpoint payoff vectors arbitrarily close; or
  source-match a restart/debt descent at the labelled summable all-Continue
  port. Fixed-edge payoff closure and exact return are stronger special cases.
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
