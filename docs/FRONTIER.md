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

The negative endpoint is upward closed under finite passive-player padding.
[`HasTerminalExploitabilityGap.passivePlayerPadding_canonical`](../UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingCanonical.lean)
adds any nonempty finite player block and retains the exact fraction
`penalty / (penalty + card J * canonicalWidth)` of a supplied terminal gap.
The proof projects every actual padded behavioral profile to the old game,
lifts an arbitrary old behavioral deviation, and balances its possible loss
against the aggregate Never gains of the new players. The canonical
nonexistence corollary
[`not_exists_uniformEquilibriumPayoff_passivePlayerPadding_canonical`](../UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingCorollaries.lean)
therefore sends any quitting-game counterexample on `I` to one on `I ⊕ J`.
This is a counterexample transport theorem, not a construction of a
counterexample or a reduction from higher to lower player cardinality.

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

The affine chamber is wider in a different direction.
`quittingGame_exists_uniformPayoff_of_componentwiseWeightedPotential`
(`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`)
assumes that each player's own-membership gain is affine in the background
coalition and that its coefficient matrix has positive symmetrizing weights
inside every directed SCC. A block weighted potential, solved in condensation
order, constructs a literal sure-exit coalition; the resulting pure stationary
profile is exact terminal Nash against unrestricted behavioral deviations.
Cross-component influences and passive reward coordinates are unrestricted.
The checked quadratic adapter covers equal active pair coefficients and the
sign-frustrated all-negative reciprocal triangle, which lies outside the
positive-cycle chamber above. The result has `M`, `L`, `A`, and `C`, but it
does not produce symmetrizability for an arbitrary hard residual or
characterize all quadratic games.

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

The arbitrary-completion obstruction now needs only one protected coordinate.
`exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorMembership`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingleAnchorArbitraryCompletionEscape.lean`)
selects a mixed Nash point for every complementary player while one anchor
Quits surely. Literal membership reward at that anchor makes its exact
stopping-cap screen automatic, and all other reward coordinates are
unrestricted. The resulting stationary profile is exact terminal Nash
against every behavioral deviation and has a uniform-equilibrium payoff. In
the Fin6 specialization,
`exists_targetA_singleAnchor_exactTerminalNash_uniformPayoff_and_secondPairMass_zero`
retains either one coordinate of the first target pair, permits arbitrary
changes to the other five coordinates, and still gives exact zero mass to the
disjoint second pair. Thus a viable two-target gadget must alter both
first-pair coordinates. The separate
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe` theorem
continues to cover general pointwise leave-safe bases of cardinality at least
two. These results have `M`, `L`, `A`, and `C`; failure of either singleton
dominance inequality is not itself a counterexample.

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
endpoint either lies on the minimum fiber and retains a literal strict subset
of the preceding positive-debt support (hence lowers its finite rank), or lies
off that fiber and carries the existing
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
support descent, both the source-floor and arbitrary-profile paid-row gaps are
removed. `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`)
extracts the full weak terminal gap at every literal behavioral profile from
one support atom of the profitable stopping law and one of the prescribed
law. The same file constructs an actual paid cap port and exposes its exact,
pairwise-disjoint trichotomy. Positive total absorption with zero cap
displacement gives cumulative admissible payoff near-returns and a uniform
payoff; under a terminal gap that charged branch is impossible. The surviving
branches are quantitative debt descent and a lossless literal inert stall.

The boundary is now quantitatively tied to excess source debt. Theorems
`QuittingPaidCapLiftedSource.minimum_mul_totalAbsorption_le_excess` and
`minimum_mul_capDisplacement_le_twoRewardBound_mul_excess`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapMinimumFiberContraction.lean`)
give

```text
D_* A   <= D_source - D_*
D_* rho <= 2 R (D_source - D_*).
```

Thus every paid cap port whose actual source lies exactly on the global
minimum-debt fiber is unconditionally inert; no terminal-gap hypothesis is
needed for that last implication. Finally,
`HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapMinimumApproximation`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfilePaidCapMinimumApproximation.lean`)
uses carrier density to produce actual full-gap ports with source debt tending
to `D_*`, total absorption tending to zero, and cap displacement tending to
zero. It does not realize the carrier minimum by a profile. The remaining
downstream step is exactly to consume or regenerate the quantitative descent,
or to consume the literal inert stall.

Changing the paid-row or port selector cannot restore a uniform real descent
step. At every positive debt-drop, absorption, and displacement tolerance,
`HasTerminalExploitabilityGap.exists_profileSequence_eventually_all_paidCapPorts_small`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfilePaidCapUniformStepObstruction.lean`)
retains one actual sequence realizing the minimum and proves that eventually
every profile on it makes every compatible full-gap paid-cap source/port
satisfy all three smallness bounds. Its one-profile consequence and
corollary `not_uniformPositivePaidCapDebtDropSelection` rules out any selector
which maintains one fixed positive total-debt drop over all profiles. The
remaining regeneration must therefore be profile-dependent and nonuniform,
use a genuinely well-founded obstruction, or consume the inert stall; no such
consumer is supplied here.

The varying-source direction is now a checked consumer rather than a prose
possibility.  If a supplied sequence of actual paid cap sources and summable
ports has total absorption eventually bounded below by one fixed positive
constant while its cap displacement tends to zero, then
`QuittingPaidCapLiftedSource.`
`exists_uniformEquilibriumPayoff_of_eventually_totalAbsorption_ge_of_capDisplacement_tendsto_zero`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortSequenceNearReturn.lean`)
selects one source-matched finite prefix at each tolerance and produces a
uniform-equilibrium payoff. The generalized theorem retains every prescribed
positive cumulative charge strictly below the supplied absorption floor; the
former half-floor statement is a convenience specialization. It never
recombines laws, profiles, or endpoints across indices. No current
producer supplies the positive absorption floor; the near-minimum sequence
above instead has absorption tending to zero.

Pointwise positive debt does not repair this attainment gap.  The checked
two-player theorem `attainable_inter_debt_ge_one_not_closed`
(`UniformEquilibrium/Diagnostics/Quitting/PositiveDebtTerminalSemanticNonattainment.lean`)
has literal semantic pairs of debt `1 + 1 / (n + 1)` converging to an
unattained carrier point of debt one.  Its global minimum debt is zero,
witnessed by all-Continue play.  Thus this is a sharp topological fence
against decoding a positive-debt carrier point from debt positivity alone,
not a counterexample and not an obstruction to an attainment theorem that
genuinely uses `D = D_* > 0` or retained chronology.

Compact stopping-law limits now give an exact classification of that
attainment seam. `quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit`
(`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`)
realizes the complete semantic point, including unrestricted behavioral caps,
under opponent tightness; two proper limiting clocks already imply that
condition. Along a fixed selected nonattained minimum sequence at most one
clock is proper. If exactly one is proper, its owner has an exact Never cap, a
negative singleton reward, and a strict cap jump bounded by the product of the
opponents' Never masses. Hence nonnegative singleton rewards leave only the
all-nonproper arm. The theorem neither identifies approximating Never atoms
nor consumes the all-nonproper or mixed-sign unique-proper residual, so it
narrows rather than closes the paid and Fin4 fronts.

The source telescope for this classification is also explicit.
`nonempty_terminalSemanticSelectedLawLimit_of_mem_carrier` retains, for every
terminal-semantic carrier point, actual realizing profiles, one strict
subsequence, semantic convergence along precisely that subsequence, and all
coordinate compact-law limits.  Carrier-level corollaries feed nonattainment
directly into the common late-opponent-tail witness, and feed global
minimality plus nonnegative singleton rewards into one selected all-nonproper
law limit.  These are genuine source adapters, not attainment: no selected
profile equals the carrier point and no approximating Never atom is asserted
to converge.

The scalar and compact minimum notions are now identified exactly.
`quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`)
proves that the infimum of literal behavioral-profile debt equals the debt of
every global minimizer on the terminal-semantic carrier.  For nonempty finite
player types,
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
makes positivity of that literal infimum exactly the no-uniform-payoff
obstruction.  The joint-carrier lift
`exists_minimum_terminalSemanticLawCarrier_of_not_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`)
retains a complete terminal law at such a minimizer.  It is existential and
nonunique: no actual profile attains the minimum.  Generically the law has a
positive-Never or positive-finite-atom dispatch.  In the Fin4 hard residual,
`exists_finFourHardResidual_minimumLaw_causalSuffixAtom`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`)
removes the pure-Never obstruction.  If a minimum law were concentrated at
Never, its reward moment would make the prescribed payoff zero and
punishment-normal minimum separation would make every singleton reward
negative; literal all-Continue would then be exact all-behavior Nash with
zero uniform payoff, contradicting the hard witness.  Hence every such
minimum law has a positive finite atom, and a residual-only adapter feeds it
into arbitrarily deep source-matched cap--Nash chronologies which retain it
in their literal suffix.  The atom is not thereby a prefix-root atom,
Bellman edge, paid row, reset, cumulative charge, or final consumer.

An independent finite-cycle route now has a sharp consumer and sharp producer
barriers.  `quittingCyclic_norm_attachment_and_terminalDebt_le`
(`UniformEquilibrium/Quitting/Cycles/CyclicGreenDebt.lean`) bounds attachment
by `K * delta / rhoMax` and every unrestricted behavioral debt coordinate by
`(K / rho_i) * (epsilon + K * delta / rhoMax)` whenever a supplied finite
product-root word has one positive nonempty opponent-only coalition atom for
each player.  Marked phases may repeat and need not be quiet.  The generic
MathUE classifiers say that atom-cover failure is exactly a common
intersection and that exact scalar phase/seam failure has only three minimal
forms: one impossible phase, two crossed phases, or one phase crossing the
closing seam.  The rational Fin5 regression
`not_exists_phaseSeamSystem_of_lt`
(`UniformEquilibrium/Diagnostics/Quitting/Regression/FinFiveFullFaceSourcePhaseSeam.lean`)
shows that five actual deleted-game exact terminal Nash sources, positive
omitted-player gaps, literal quiet lifts, and mass-`1/2` opponent atoms still
permit a sharp `31/32` phase--seam obstruction.  Its ambient all-Quit profile
has `D_* = 0`; whether positive global minimum debt forces alignment remains
the exact branch-facing question.

The Research same-stage endpoint route now has a checked Fin4 structural
adapter, but not a closure theorem.  The literal closed-segment declarations
`dispatchedClosedSegment_offset_edge_certificate`,
`dispatchedClosedSegment_offset_edge_full_certificate`, and
`dispatchedClosedSegment_offset_literal_profile_update`
(`Research/Quitting/SameStageEndpointMonodromy.lean`) retain a positive edge,
its full routed-target data and literal one-date profile update at each offset.
The edge certificate includes the exact best-action field
`QuittingSameStageEndpointEdge.action_eq_best`;
`dispatchedClosedSegment_player_circulation` gives the exact player
circulation sum over the period.
`finFourTraceCodeSupport_card_eq_period`,
`finFourTrace_stageMass_ge_liveMass`,
`finFourTrace_offset_gain_certificate`, and
`finFourTrace_common_or_complementary_exact`
(`Research/Quitting/FinFourSameStageEndpointMonodromy.lean`) transfer this
literal trace to the ordered Fin4 code, give an all-offset live-mass floor and
a best-action gain of at least `lambda * debt / 8`, and make the
complementary-pair alternative an exact complement equality.  Together with
`finFourTrace_period_le_eight_and_geometry`, they give the support, period,
and common-player/complementary-pair conclusions.  The composition
`quittingPartialPurification_then_finFourSameStage_dispatch` remains
conditional on its carrier/minimum, positive mass, and low-tail hypotheses and
returns either a singleton route or a finite dispatched cycle.

The Research-only capstone
`uniformPayoff_or_nonempty_finFourProducerResidual`
(`Research/Quitting/FinFourProducerAtlas/Coverage.lean`) now reaches those
hypotheses from arbitrary bounded Fin4 data.  It returns a uniform-equilibrium
payoff or one tagged residual carrying the same selected hard residual,
minimum joint-law point, causal finite atom, and source chronology.  The
nonsingleton source theorem
`FinFourMinimumAtomProducer.nonempty_tailEscape_or_lowTailRow`
(`Research/Quitting/FinFourProducerAtlas/Source.lean`) performs the inclusive
high-tail/strict low-tail split on one selected-row family, and
`FinFourLowTailRow.nonempty_leaf`
(`Research/Quitting/FinFourProducerAtlas/Leaves.lean`) sends the low row to a
bounded-purification singleton, terminal-orbit singleton, common-host
monodromy, or complementary-pair monodromy.  The same file's
`FinFourTerminalSingletonProducer.exists_singleton_with_stageMass_floor_and_postDateTail_eq`,
`FinFourMonodromyProducer.edge_gain_floor_mu_square_div_sixty_four`,
`FinFourMonodromyProducer.edge_mover_debt`, and
`FinFourMonodromyProducer.edge_stageMass_noLoss` expose the terminal
singleton's mass floor with preserved post-date semantics, the exact
`mu^2 D_*/64` gain floor, exact mover-debt decrease, and no-loss routing.
The semantic adapter
`FinFourProducerResidual.nonempty_directedNode`
(`Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean`) preserves
the origin tag of either reached-singleton route and normalizes the six leaves
to four data-carrying nodes: minimum-law singleton, concentrated reached
singleton, quantitative tail escape, or monodromy with exact retained
geometry.  `FinFourAtlasConcentratedSingletonEndpoint.postDateTail_eq` derives
the common semantic tail from literal post-date live-root equality, and
`not_commonHost_and_complementaryPair_sameTrace` proves that common-host and
complementary-pair geometry cannot coexist on one fixed trace.  It does not
exclude different traces with different geometries on the same source or
reward table.  Composing this adapter with the six-leaf coverage gives
`uniformPayoff_or_nonempty_finFourAtlasDirectedNode`
(`Research/Quitting/FinFourProducerAtlas/SemanticCoverage.lean`) for arbitrary
bounded Fin4 reward data.

The generic anchored theorem
`exists_quittingAnchoredSingletonClockCompression`
(`Research/Quitting/AnchoredSingletonClockCompression.lean`) removes owner-clock
diffusion without changing the reward table or selecting a semantic point.  A
positive singleton tail after an arbitrary anchor supplies its least supported
owner date and a literal target which changes only that owner, at that date, to
sure Quit.  The target singleton stage mass is exactly the fixed prefix and
opponent exposure by
`quittingStageCoalitionMass_anchoredSingletonQuitProfile_eq_exposure` and is at
least the entire source singleton tail by
`quittingAnchoredSingletonTailMass_le_exposure`.  The stronger normalized
`m / A` lower bound is retained as well.  The exact identities
`quittingAnchoredSingletonQuitProfile_liveRoot_tail_eq` and
`quittingAnchoredSingletonQuitProfile_owner_cap_eq` copy the complete
post-selected-date live-root tail and preserve the owner's unrestricted
behavioral best-response cap.

For one minimum-law singleton source,
`FinFourMinimumAtomProducer.exists_commonChronology_cofinal_ownerCompressedSingleton`
(`Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`)
unpacks one causal profile/root chronology before the resolution quantifier.
For every `0 < lambda < mu` and every requested depth, that same chronology
then supplies a literal owner-compressed endpoint beyond the depth.
`FinFourMinimumAtomProducer.nonempty_ownerCompressedSingletonProducer`
specializes the construction to the atlas scale `mu^2 / 8` while retaining the
full cofinal family.  The additive semantic adapter
`FinFourProducerResidual.nonempty_clockCompressedDirectedNode` stores this
producer together with one depth-zero endpoint, keeps the two old
reached-singleton routes behind their unchanged strong endpoint, and maps the
six residual constructors to three data alternatives: weak concentrated
singleton, quantitative tail escape, or monodromy.  The shared interface
`FinFourAtlasWeakConcentratedSingletonCore.resolution_le_stageMass` exposes the
canonical mass floor, and
`FinFourAtlasWeakConcentratedSingletonCore.postDateTail_eq` exposes the common
semantic tail.  Composing the adapter with the bounded-data producer gives
`uniformPayoff_or_nonempty_finFourAtlasClockCompressedDirectedNode`
(`Research/Quitting/FinFourProducerAtlas/SemanticCoverage.lean`).  This is a
one-way producer normalization, not an equivalence or a consumer of the three
nodes.

The same semantic-coverage module also provides
`FinFourComplementaryPairMonodromyProducer.nonempty_prescribedPairPaidCapSemanticDispatch_reselectingSource`.
It keeps the same reward table, the terminal-exploitability witness stored in
the same hard residual, and one displayed complementary pair as a prescribed
base label.  It reselects the semantic minimum, stationary profile, paid row,
and cap chronology and does not use the monodromy orbit or edge data.  Thus it
is a same-label producer bridge, not a consumer of the monodromy dynamics.
Finally,
`FinFourMonodromyProducer.every_edge_no_literalExactification`
(`Research/Quitting/FinFourProducerAtlas/LiteralNoGo.lean`) excludes only an
exact Nash--Bellman embedding which preserves the displayed root and shifted
tail payoff.  The six-leaf atlas, its four-node view, and the clock-compressed
three-node view have `M`, `L`, and `A`, but no `C`: their constructors are data
alternatives rather than a uniqueness or table-level pairwise-exclusivity
theorem.  The compressed target is not asserted cap--Nash, near-minimal, or
reprojected to the terminal-semantic carrier.  The retained exact cap-root
stack remains a certificate for the unmodified source suffix.  No return,
regeneration, recursive descent, backward compiler, chronology return,
completion closure, or downstream uniform-payoff consumer is supplied.

As a separate Research side result, the Fin4 deletion producer
`finFourDeletionNearCap_collisionDispatch_distinct_with_bounds`
(`Research/Quitting/FinFourDeletionCollisionExpansion.lean`) constructs, from a
terminal exploitability gap and the small-solo-premium inequality, a literal
quiet lift, finite near-cap update, paid nonsingleton atom, and either a tail
bound or an endpoint mover distinct from the deleted player.  The checked
`finFourDeletionNearCap_tailFormula_six` gives the explicit `1/14` tail scale;
the endpoint branch has the exact `1/56` gain, mover-debt subtraction, and
no-loss routed mass.  `Math.FinitePaidCollision.endpoint_scale_of_paid_collision`
(`MathUE/FinitePaidCollision.lean`) supplies the seven-term algebra.  This is
Research evidence, not a new DAG
consumer: it claims no recipient-debt increase, chronology, return, or
uniform-equilibrium payoff.

On `Fin 4`, the source construction is now unconditional from the negative
semantic endpoint. For every terminal exploitability witness and every
prescribed reset owner with a disjoint two-player base,
[`QuittingTerminalExploitabilityWitness.nonempty_finFourSameSourcePaidResetCapPort`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourSameSourcePaidResetCapPort.lean)
selects one positive global-minimum carrier point and one actual stationary
profile and law which simultaneously carry the base-localized full-gap paid
row, the fixed-law reset target, and the unchanged suffix of the cap-lifted
summable port. Thus hard-principal and marked-lasso alignment are unnecessary
for producing this marked port. The fixed-law dispatch's returned pair is
retained but is not the cap suffix or port limit; no prescribed-payoff exact
path, restart, debt descent, or uniform payoff follows.

There is also a stronger prescribed-singleton source. The theorem
`FinFourQuantitativeFullSupportHardResidual.nonempty_paidCapDoublePort`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SingletonBaseResetRepairPaidCapDoublePort.lean`)
starts from the actual quantitative hard residual and any singleton owner.
One actual stationary profile and law carry three solved free coordinates, a
unique full-gap paid debtor, a quantitative strict-superset atom, and a
same-law fixed reset dispatch. Its literal owner repair carries a second paid
row at a distinct observer. Both profiles are cap-lifted from the same
positive minimum. The terminal witness excludes the charged-return branch on
both ports, leaving quantitative descent on the source, quantitative descent
on the repair, or two literal inert stalls. The descent alternatives may both
hold. No descent limit carries regenerated paid/reset provenance, and the two
inert laws are not identified.

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
| `PAID-FIRST-DISAGREEMENT-ROW` | `open-producer` | `CUMULATIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN` | `M`, `L`, `A` | [`GameTheory.HasTerminalExploitabilityGap.exists_profile_all_paidCapPorts_small`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfilePaidCapUniformStepObstruction.lean) |
| `CHRONOLOGICAL-DEBT-SHADOWING` | `proved-consumer` | `UNIFORM-EQUILIBRIUM-PAYOFF` | `M`, `L`, `C` | [`GameTheory.quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`](../UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean) |
| `CUMULATIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN` | `proved-consumer` | `UNIFORM-EQUILIBRIUM-PAYOFF` | `M`, `L`, `C` | [`GameTheory.quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`](../UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean) |

The open producer arrows are:

- `VANISHING-DEBT-ATOM-ACCESS` to `CHRONOLOGICAL-DEBT-SHADOWING`: Missing: construct a two-tier input for the checked budget-stable iteration theorem. The actual reached-port packet system must retain two fixed actual labels, give exact literal source/successor anchoring, one globally bounded annotation family, and an operationally sublinear seam-plus-radius-loss modulus. Separately, an external source/payoff-to-candidate adapter must provide the compiler's small-debt seed, unless a solved-game disjunct is returned. A positive-minimum actual port cannot itself be that seed, and semantic closeness cannot pay the resulting fixed debt gap. Once both tiers are supplied, `exists_chronologicalDebtShadowingCertificate_of_seed` recursively selects compatible blocks and proves every same-root survival law. A universal exact-spine two-label selector is impossible even for two players.
- `PAID-FIRST-DISAGREEMENT-ROW` to `CUMULATIVE-ADMISSIBLE-PAYOFF-NEAR-RETURN`: A positive terminal gap gives a full-gap paid cap port at every literal behavioral profile. Its exact trichotomy closes positive absorption with zero cap displacement through cumulative payoff near-return; the terminal gap excludes that charged branch in a counterexample. The remaining quantitative and inert branches satisfy D_* A <= D_source - D_* and D_* rho <= 2 R (D_source - D_*). An exact-minimum actual source is unconditionally inert. At arbitrary positive tolerances, one near-minimum literal profile makes every compatible source/port have small debt drop, absorption, and displacement, so no selector can maintain one fixed positive real debt-drop step over all profiles. Opponent-tight compact-law limits, and in particular limits with two proper clocks, realize the full semantic point. A fixed nonattained minimum subsequence is therefore all-nonproper or has one proper owner with a negative-singleton Never-cap jump. Missing downstream: consumption of those law-limit residuals, profile-dependent nonuniform or well-founded regeneration, or a consumer of the literal inert stall.

The DAG nodes have these mathematical meanings:

- `POSITIVE-MINIMUM-DEBT`: The literal behavioral-profile debt infimum equals the minimum on the compact terminal-semantic carrier. For a nonempty finite player type, its positivity is equivalent to nonexistence of a uniform-equilibrium payoff; a nonunique complete terminal-law carrier lift of a minimizer is checked. In every nonempty finite punishment-normal game without a uniform-equilibrium payoff, each minimum joint law has a positive finite coordinate and a same-point causal suffix atom. Checked Research consumers send that atom to a positive one-step punishment-prefix charge retaining it or to arbitrarily deep literal all-Continue, zero-charge stacks. The inert arm has pure-Never marginal limits, fails joint and opponent tightness, and forces absorption to vanish for nearby approximate roots through a robust cap moat. Neither arm yet supplies a paid/reset/return cycle, a contradiction, or a uniform-equilibrium payoff; marginal limits do not recover the retained positive joint atom.
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

  Separately, `nonempty_finFourPairBasePaidCapSemanticDispatch`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidCapSemanticDispatch.lean`)
  takes any prescribed two-player base and a terminal-exploitability witness
  to a stationary paid source on exactly that base, a positive global semantic
  minimum, and the summable cap port lifted from the same literal paid row.
  Its hard-residual adapter preserves the reward table and pair label, and
  `uniformPayoff_or_exists_pairBasePaidCapSemanticDispatch` removes even the
  hard-residual and reward-bound inputs.  The semantic minimum, stationary
  profile, paid row, and cap chronology are freshly selected.  Thus this is a
  prescribed-label producer, not an atlas source/trace adapter or monodromy
  consumer, and it supplies no restart, cumulative-charge near-return, or
  uniform-payoff consumer for the port.

  A different pair-base construction co-realizes more data on one literal
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
  Applying the generic cap lift directly to that same stationary target is
  now packaged by
  `QuittingTerminalExploitabilityWitness.nonempty_finFourSameSourcePaidResetCapPort`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourSameSourcePaidResetCapPort.lean`).
  It retains the positive carrier minimum, the reset dispatch and returned
  pair, the actual paid/reset profile and law, the full-gap paid observer in
  the forced base, and the complete summable marked port. The cap chronology
  deliberately bypasses the separately returned pair, so this closes source
  construction and alignment but not the all-Continue-port discharge.
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
- **AGKRS Theorem 3.4 dependency boundary:** a raw refined source residual can
  coexist with exact S.1, as checked by
  `RefinedSourceResidualRegression.stationaryExistence_and_refinedSourceResidualAt`.
  The proof must therefore prioritize classified branches rather than exclude
  every residual.  The priority-safe theorem
  `QuittingPayoffTable.fixedCorrectedBranches_or_cofinally_prioritizedResidual`
  gives a fixed corrected branch, or cofinally many scales where a refined
  source residual remains and all four pointwise branches fail.  The diffuse
  generated branch is now reduced by
  `stationary_or_instant_or_wellSupported_or_noSureExit_or_negativeOwner` to
  S.1, S.2, well-supported S.3, an exact positive-reach endpoint with no
  sure-exit Nash prefix, or a divergent exceptional owner with negative
  singleton self-payoff. Bounded exceptional horizons already give S.2, and
  `QuittingUniqueExceptionalOwnerSource.instantPunishment_or_wellSupported`
  now consumes every divergent exceptional-owner source without using the
  negative-solo field. After a fixed-label selection, a zero one-row live-mass
  limit gives S.2 and an interior limit gives S.3. At unit live mass, immediate
  Quit values converge to the players' own singleton rewards while the actual
  source values converge to the exceptional owner's singleton vector. The
  resulting singleton floor compiles, through a vanishing positive solo
  hazard, to an actual-tail well-supported absorbing sequence. This S.3
  witness need not be terminal Nash when the owner's singleton payoff is
  negative.

  Composing the two residual consumers exposes the cleaner checked capstone
  `quittingDiffuseGenerated_stationary_or_instant_or_wellSupported_or_sourceMatchedPhantom`
  (`UniformEquilibrium/Quitting/Classification/Existence/DivergentExceptionalOwnerS3Dispatch.lean`):
  every diffuse stationarily generated source yields S.1, S.2, well-supported
  S.3, or a source-matched uniform all-Continue phantom. The last package
  retains a strict source subsequence, literal punishment suffixes, fixed
  punished label, their semantic limit endpoint, its no-sure-exit proof,
  summable exact-prefix port, phantom, exact value equality, and uniform-payoff
  certificate. This still does not classify the surviving target as S.1,
  S.2, or S.3.

  The prioritized positive-absorption attachment is no longer an independent
  source obligation.  At every positive prioritized scale,
  `QuittingPrioritizedRefinedSourceResidualAt.sourcePhantom_or_positiveSingletonDefect`
  (`UniformEquilibrium/Quitting/Classification/Existence/PrioritizedAttachmentSingletonDefect.lean`)
  gives the exact normal form: the source-faithful all-Continue positive-rho
  residual or the positive-singleton defect.  A uniformly reached finite
  sure-exit row is exact root Nash after lifting its successor to the
  punishment floor and therefore contradicts the instant-punishment priority;
  the infinite attachment output contracts through the support--Bellman
  boundary.  The reward table, tolerance, and all four priority negations are
  retained.  This reduction has `M`, `L`, `A`, and attachment-arm `C`, but
  neither surviving normal-form arm has a branch consumer. The explicit
  `AllContinueSourceAt` and `PositiveSingletonDefectAt` packages show why the
  final consumer must be eliminative: all three fixed AGKRS branches directly
  contradict their retained same-scale priority negations. Cofinal residuals
  yield either one positive-scale all-Continue source or singleton defects
  cofinally toward zero. Every such residual in fact forces a positive-period
  directed cycle in the finite augmented solo-preemption graph. Turning that
  concrete cyclic architecture into S.3, or eliminating it, is still open.

  The cofinal source provenance has also been retained.
  `nonempty_cofinalPrioritizedPreemptionSeedSequence_of_cofinallyPrioritized`
  (`UniformEquilibrium/Quitting/Classification/Existence/PrioritizedPreemptionSeedBoundary.lean`)
  fixes one positive
  owner/preemptor edge along scales tending to zero and stores the actual
  all-Continue source or singleton defect at every scale. The exact sufficient
  semantic enhancement is `QuittingCofinalPrioritizedSignedLassoBridge`:
  phase roots and values, rotation-uniform signed seams, support rationality,
  and an absorbing phase. Its checked consumer yields S.3 and contradicts
  priority. No theorem produces those phase fields from the static edge, so
  this is the precise remaining prioritized compiler rather than an
  unconditional branch theorem.

  The positive-joint endpoint is now narrowed further by
  `QuittingPositiveJointPrefixReachNoSureExitResidual.wellSupported_or_summableExactPrefixPort`
  (`UniformEquilibrium/Quitting/Classification/Existence/PositiveJointEndpointSequentialReduction.lean`).
  Every reached endpoint starts a canonical exact semantic-prefix orbit.
  Nonsummable absorption gives well-supported S.3 through compact
  single-seam lassos; the only surviving arm is an actual endpoint with no
  sure-exit Nash prefix and a summable exact-prefix all-Continue port.
  `QuittingPositiveJointPrefixReachNoSureExitResidual.wellSupported_or_stationary_or_uniformAllContinuePhantom`
  (`UniformEquilibrium/Quitting/Classification/Existence/PositiveJointSummablePortPhantomReduction.lean`)
  contracts that arm again to S.1 or a data-bearing phantom retaining the
  originating residual, reached endpoint, no-sure-exit proof, summable port,
  exact value identity, and uniform-payoff certificate. At each tolerance the
  same obstruction is the existing positive-singleton defect. The stronger
  `wellSupported_or_stationary_or_sourceMatchedUniformAllContinuePhantom`
  additionally retains the strict producing subsequence and its actual
  punishment-suffix profiles. The older raw corrected-pointwise projection
  still forgets those fields. This is a classified semantic obstruction, not
  yet an S.1/S.2/S.3 consumer.

  The parallel provenance-retaining theorem
  `QuittingPositiveJointPrefixReachNoSureExitResidual.wellSupported_or_endpointBallisticBoundary`
  (`UniformEquilibrium/Quitting/Classification/Existence/PositiveJointSummablePortBallisticDispatch.lean`)
  gives a sharper boundary on the literal endpoint orbit.  Failure of S.3
  supplies one scale `e > 0` such that every finite segment of cumulative
  absorption charge `C > 0` moves some payoff coordinate by more than
  `e * C / (1 + C)`.  Thus a summable port of positive total charge which
  returns to its initial endpoint gives literal well-supported S.3.  Under
  S.3 failure, the only surviving alternatives are a zero-charge constant
  all-Continue orbit or a positive port whose limit is displaced by at least
  `e * A / (1 + A)` and carries one fixed signed terminal coalition.  The
  coalition-mass denominator uses the canonical `quittingRewardBound`, which
  bounds both rewards and orbit annotations.  The actual endpoint,
  no-sure-exit proof, and summable port remain present in both alternatives.
  Neither alternative has a consumer, and real displacement is not a
  well-founded rank.

  The terminal-semantic status of this endpoint and port is nevertheless
  exact.  `QuittingPositiveJointPrefixReachPunishmentEndpoint.`
  `isUniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Classification/Existence/PositiveJointEndpointUniformPayoff.lean`)
  identifies the reached endpoint's prescribed coordinate as a specific
  uniform-equilibrium payoff because the endpoint is already diagonal in the
  literal terminal-semantic carrier.  Every exact semantic-prefix pair stays
  diagonal and in that carrier, and
  `SummableChargeAllContinuePort.limit_mem_diagonal_of_endpoint` together with
  `limit_isUniformEquilibriumPayoff_of_endpoint`
  (`UniformEquilibrium/Quitting/Classification/Existence/PositiveJointExactPrefixOrbitDiagonal.lean`)
  gives the same conclusions for the port limit.  Closure membership does not
  assert realization by one profile.  More generally,
  `isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier`
  (`UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`)
  is the exact fixed-target equivalence.  Its existential form identifies
  target-free approximate-equilibrium existence with diagonal-carrier
  nonemptiness, and the table adapter gives the same characterization of the
  normalized arbitrary-Never AGKRS premise.  These are semantic
  reformulations, not an existence proof for an arbitrary table.

  More importantly here, a specific
  uniform-payoff target is not an S.1/S.2/S.3 classification.  This supplies
  no classification consumer and no new unconditional advance on the
  finite-quitting conjecture: the positive-joint source already carries an
  approximate-equilibrium family with a checked target-free uniform-payoff
  consumer.

  The checked Literature theorem
  `theorem3_4_of_prioritizedAndSummablePortClosures` therefore composes
  consumers for exactly the prioritized corrected-pointwise residual and
  the summable-port residual into the literal S.1/S.2/S.3 conclusion. A
  branch-classification consumer for the retained uniform phantom would
  discharge the latter, but none is known. On the prioritized side, the exact
  surviving obligation is to construct the signed-lasso bridge from the
  cofinal source-matched preemption seed, or otherwise eliminate that seed.
  The ballistic theorem closes only its returned positive-charge subarm and
  quantitatively classifies the rest; the diagonal-payoff theorems do not
  supply a classification branch.  No complete universal consumer and no
  counterexample is known; the unconditional general `theorem3_4` remains the
  sole proof hole in the paper-facing file.
- **Simon compact alternatives:** the near-total-absorption branch is checked
  in `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/CompactQuantitativeAlternatives.lean`:
  `quittingInstantPunishmentεEquilibriumExistence_of_nearTotalSupportRows`
  rounds a sufficiently small Continue coordinate to a sure Quit and produces
  the instant-punishment branch. The normalized-motion producer is now checked
  in `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/NormalizedMotionStationaryPrefixProducer.lean`:
  actual arbitrarily small rational support-local rows with positive absorption
  and strict normalized motion produce the stationary-prefix branch against
  arbitrary behavioral deviations. Its fixed-scale contrapositive asserts no
  feasibility. The positive-solo clause, the common compact-carrier scale, and
  Simon Lemma 2 remain open.
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
- **Local periodic-anchor route:**
  `localPeriodicAnchor_theoremA`
  (`Research/Quitting/LocalPeriodicAnchorObstructions.lean`) turns supplied
  cyclic roots satisfying the numerical minimum-tube, hazard, and positive-
  absorption hypotheses into an unrestricted behavioral gap of
  `eta / (2 * card(I))`. The generic finite-cycle aggregation used there is
  `exists_player_base_ge_eta_div_two_card`
  (`MathUE/FiniteCycleAggregate.lean`). The Fin4 packet-facing adapter
  `finFourPeriodicAnchor_false_of_packet_family`
  (`Research/Quitting/FinFourPeriodicAnchorResidualAdapter.lean`) consumes a
  fixed reward/matrix and returned-block family with individual mesh bounds,
  eventual value/anchor tubes, positive hazards, and vector-norm signed-seam
  convergence; it derives the additive normalized linearization and obtains a
  contradiction with the hard residual. Neither theorem produces cyclic
  roots, returned blocks, or packet hypotheses from an arbitrary game.
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
