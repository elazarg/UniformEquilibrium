# Uniform-equilibrium mathematical frontier

This file states the current mathematical dependency boundary. Exact theorem
truth belongs to Lean declarations under their imports; the generated
declaration index is [`STATUS.md`](STATUS.md). Detailed compiler interfaces are
in [`TOOLKIT.md`](TOOLKIT.md), and the mechanically maintained quitting leaf
ledger is [`QuittingProofFrontier.json`](QuittingProofFrontier.json).

This is not a chronology. Explicitly historical mathematical synthesis is
scoped under [`audits/`](audits/README.md). Old source paths and extraction
decisions are not part of this living mathematical ledger.

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

The Fin4 terminal problem also has an exact executable scale fork, orthogonal
to the chronological proof-search DAG.
[`finFourExactScaleStep`](../Research/Quitting/FinFourExactScaleResolution.lean)
is a total proof-free upper-first stage function, and
[`exists_finFourExactScaleStep`](../Research/Quitting/FinFourExactScaleResolution.lean)
proves that some finite stage emits at every positive rational scale of every
normalized rational table. Upper output is an actual finite-clock product
profile with unrestricted exploitability below `3 * epsilon / 4`; lower output
proves `epsilon / 4` below the global infimum and reaches the checked terminal-
gap/no-uniform-payoff consumer at `epsilon / 8`.

The semantic boundary is literal in both directions.
[`finFourExactScale_infimum_zero_or_lower_event`](../Research/Quitting/FinFourExactScaleResolution.lean)
states that zero infimum yields profiles at every positive real error and one
fixed uniform-equilibrium payoff, whereas positive infimum forces a finite
lower event. The profile may vary with the error; the selected payoff does
not. At the global level,
[`exists_finFourCounterexampleStep_iff_exists_real_infimum_pos`](../Research/Quitting/FinFourCounterexampleSemidecision.lean)
uses positive scaling, 2-Lipschitz reward robustness, normalized rational
approximation, and fair dovetailing to show that existence of a real Fin4
positive-gap table is recursively enumerable.  Separately,
[`FinFourExactScaleCertificate.lower_verifies_infimum_sound`](../Research/Quitting/FinFourIndependentCertificateSoundness.lean)
reads the unrestricted infimum lower bound directly from an accepted finite
tree without trusting or replaying its generator.  For one supplied normalized
rational table with positive unrestricted infimum,
[`exists_finFourFixedTableCounterexampleStep_of_infimum_pos`](../Research/Quitting/FinFourFixedTableCounterexampleSearch.lean)
proves that the table-specific dyadic-scale/local-stage dovetail emits at a
finite stage.  These Research declarations give `M/L/A/C` for the exact search
route at their stated inputs.  They produce no positive-gap table, do not
decide a supplied real table, and give no conclusion from nontermination;
therefore they neither solve the Fin4 conjecture nor close either structural
atlas arrow.

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

The constrained-root normal-work ledger is one such exact Research boundary.
[`constrainedRoot_terminalDebt_eq_normalWork_add_inherited_sub_shield`](../Research/Quitting/ConstrainedRootNormalWork.lean)
and
[`constrainedRoot_totalNormalWork_eq_excessChange_add_killed_add_shield`](../Research/Quitting/ConstrainedRootNormalWork.lean)
decompose the full behavioral semantic debt after prefixing a lower-bounded
one-row root.  The near-minimum estimate
[`nearMinimum_totalNormalWork_ge_kappa_mul_minimum_sub_excess`](../Research/Quitting/ConstrainedRootNormalWork.lean)
uses the exact finite min--max floor, and
[`lowerFaceRemoval_otherDebtChange_sum_eq`](../Research/Quitting/ConstrainedRootNormalWork.lean)
shows that deleting binding mover work produces only an aggregate signed
repayment account.  A positive new coordinate is obtained by
[`lowerFaceRemoval_exists_supportEntry_of_uniqueDebtor`](../Research/Quitting/ConstrainedRootNormalWork.lean)
only under its explicit unique-source-debtor and work-above-excess hypotheses.
The finite backward-row and arbitrary own-strategy cut identities are literal
telescopes, not chronological charge or an oriented flow.

[`exists_quittingLowerBoundConstrainedRoot`](../Research/Quitting/ConstrainedRootExistence.lean)
constructs the compact constrained root against an arbitrary prescribed
continuation, and
[`exists_actual_quittingLowerBoundConstrainedPrefix`](../Research/Quitting/ConstrainedRootExistence.lean)
attaches it to a supplied actual behavioral tail.  This gives `M` and `L`,
with `A` only relative to that supplied tail; it is not a positive-minimum
atlas producer and has no `C`.  The same-table boundary theorem
[`FinFourConstrainedRootNormalWorkRegression.finite_boundaryRegression`](../Research/Quitting/FinFourConstrainedRootNormalWorkRegression.lean)
uses unrestricted behavioral caps: unit debt circulates around four unilateral
updates, while a stationary mixed profile proves that the global carrier
minimum is zero.  It therefore blocks a local rank based only on work, labels,
or debt support, but supplies no positive-minimum counterexample, repayment
orientation or cancellation, renewable consumer, terminal approximation, or
uniform-equilibrium conclusion.

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

Integrated interfaces sharpen the supplied-data stationary-face boundary.
`QuittingPureSingletonChamber` and
`QuittingPurePairChamber`
(`UniformEquilibrium/Quitting/Classification/Existence/SureExitChambers.lean`)
compile literal
sure-exit signs to exact terminal Nash profiles against arbitrary behavioral
deviations and fixed uniform-equilibrium payoffs.
`QuittingInducedOwnerChamber.uniformEquilibriumPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`) delegates
an actual
induced Nash point plus supplied owner-floor and outsider signs to the
singleton-base all-behavior compiler.  The sharper
`QuittingInducedOwnerNeverChamber.terminalNash` retains the actual induced
point and turns supplied owner `Quit >= Continue`, nonpositive solo, and
outsider no-join signs into the literal one-date-then-Never exact behavioral
Nash profile.  The theorem
`exists_uniformPayoff_or_inducedOwnerNever_continue_sub_quit_pos_gap` gives
the corresponding compact alternative: a uniform payoff or one positive
`Continue - Quit` margin on the whole induced Nash carrier.
`QuittingRationalStationaryFaceBox` and
`QuittingRationalStationaryFaceBox.nonempty_stationaryCertificate`
(`UniformEquilibrium/Quitting/Classification/Existence/RationalStationaryFaceBox.lean`)
turn supplied strict
rational-box face signs and a supplied `zero_to_numerator` bridge into an
interior numerator zero and a full exact stationary behavioral certificate.
`Math.Interval.RationalPolynomial.abs_evalReal_le_of_centeredMeanValueNumerator_le`
(`MathUE/Interval/PolynomialLipschitz.lean`) gives the generic whole-box bound
that keeps the factored syntax: two passes of dyadic automatic
differentiation, one for the value envelope at a base point and one for the
gradient row sum on the box, combine into a single scaled integer comparison.
It is a generic finite checker and does not itself inhabit a table-specific
certificate.  Finally,
`QuittingCenteredStationaryFaceCertificate.exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/Existence/CenteredStationaryFaceCertificate.lean`)
is its supplied-certificate stationary consumer.  These generic interfaces have checked
`M/L/C` status, the centered bound through the sharp table's
`abs_evalReal_sharpNormalizedDiagonalErrorPolynomial_le`.

`Math.Interval.RationalPolynomial.abs_evalReal_le_coefficientL1`
(`MathUE/Interval/RationalPolynomialL1.lean`) is a second generic exact
unit-box bound, taken through monomial normalization; in the same file
`Math.Interval.RationalPolynomial.boundedCoefficientL1_eq_coefficientL1`
proves that dense coefficient reflection over any explicit syntactic exponent
box computes that canonical coefficient norm exactly.  Both are checked
general checkers, and neither inhabits a table-specific certificate.  No
declaration outside that module consumes either, so they have `M/L` and
no `C`.

The owner-risky stationary table is represented exactly, and its payoff is
unconditional on the certified parameter range.  `sharpReward`,
`sharpPreconditionerMatrix_det`, `applySharpPreconditioner_injective`, and
`quittingFaceNumerator_sharpReward_eq_formula`
(`UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyStationaryClosure.lean`)
retain the owner-risky
reward family, the exact nonzero preconditioner, and the four division-free
face polynomials; the normalized evaluation and singleton-level cancellation
theorems are also checked.
`abs_evalReal_sharpNormalizedDiagonalErrorPolynomial_le` discharges the four
whole-box diagonal-error bounds by that generic centered mean-value bound,
whose only arithmetic inputs are exact dyadic interval computations on the
normalized unit box.  So `sharpCenteredCertificate`,
`sharpReward_exists_uniformEquilibriumPayoff`, and
`rationalSharpReward_exists_uniformEquilibriumPayoff` take no supplied
arithmetic hypothesis: the stationary uniform-equilibrium payoff holds for
every `0 <= R <= 1/37`, at an arbitrary real singleton level, which cancels
from all four face numerators.  The sharp table thus has `M/L`, with
`sharpReward_exists_uniformEquilibriumPayoff` supplying `C` for its own
stationary payoff on that closed range, and no actual `A`.  The thin
`rationalSingletonTwoChamber` and
`fullBindingSingletonTwoChamber` aliases retain actual safe chambers for two
different previously checked zero-minimum tables.  No theorem identifies
either table with `sharpReward`, transports the maximal ray to the sharp
family, or proves the advertised open reward neighborhood.

The direct screens are also integrated.  `isQuittingSureExitSet_sharpReward_iff`
(`UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskySureExitExclusion.lean`)
classifies every pure sure-exit set; `sharpPurePairDebt_eq`
(`UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyPairDefect.lean`)
gives the exact pair-debt vector; and `existsUnique_isQuittingRootNash`
(`UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyCapLimitRootUniqueness.lean`)
proves existence and uniqueness of all Continue at the solo cap.  The exact
induced-owner margin and zero terminal-debt infimum live in the corresponding
Diagnostics modules, and `checkedScreens`
(`UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourOwnerRiskyCheckedScreens.lean`)
conjoins all of these checked facts.  None identifies this family with a HOPF
or maximal-ray construction.

Two checked facts separate the sharp completion from those two and bound how
it can be fenced.  `forcedPairDebt_sharpLocalForcedPairFragment`
(`Research/Quitting/FinFourSharpPairDefectZeroMinimumExclusion.lean`) computes
the forced pair-defect vector at the pure pair `{0, 3}` as `(0, 1, 1/100, 1)`,
against `(0, 1/100, 1/100, 1)` for both older completions by
`forcedPairDebt_rationalLocalForcedPairFragment` and
`forcedPairDebt_fullBindingLocalForcedPairFragment`.  The marked owner is
slack and the two players outside the pair gain strictly in all three, but
`forcedPairDebt_sharp_zero_and_distinct_pos` and
`forcedPairDebt_older_completions_not_distinct` make those two gains distinct
only for the sharp table.

`isQuittingSureExitSet_empty_of_regression` shows that a table admitting
`FinFourMaximalRayZeroMinimumRegressions.Regression` has the empty coalition
as a sure exit set, through that structure's vanishing-solo field alone.  The
sharp solo vector is `(0, 0, 0, singletonLevel)`, and
`isQuittingSureExitSet_sharpReward_iff`
(`UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskySureExitExclusion.lean`)
makes the empty
coalition the table's only possible sure exit set and only at a nonpositive
level, so `not_nonempty_regression_sharpReward` excludes that structure at
every positive singleton level.  This bounds the fencing structure, not the
exact-cap ray it stores: `QuittingForwardExactCapTail` constrains singleton
rewards only by `singleton_le_capLimit` against the limiting cap and demands
no vanishing anywhere, so nothing here bears on whether the sharp table
carries a maximal-cap ray.

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

The cap-switch boundary of this static geometry is also literal.  The
normalized first-disagreement estimate in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticCapSwitchFriction.lean`
retains both pair-deleted survival and the moved law's inclusive post-mark
tail.  Under a supplied two-edge first-order rectangle,
`exists_quittingCapSwitchFullChordPaidRow_of_firstOrderRectangle`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticCapSwitchFullChord.lean`)
selects one source/full endpoint with paid gain `gamma / (4 * C)` and
pair-deleted survival at least `gamma / (8 * M * C)`.  Reset-cube source
transfer and compact stopping-law extraction retain only a pair-deleted
`Never` product in one selected weak limit.  The exact Fin4 regression in
`UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourCapSwitchAllProper.lean`
has the same first-order counterfactual cap square:
`tendsto_quittingCounterfactualPureTimeCapSquare_div_lambda_neg_one` gives its
ratio to the response scale converging to `-1`, whereas
`tendsto_uniformFixedResponseSquareBound_div_lambda_zero` gives uniform
fixed-response little-o.  Its mark tends to infinity, every displayed opponent
survives to that mark with exact probability one, and its finite-splice error
tends to zero.  Thus this route has `M` and `L`, but no source `A` or downstream
`C`: the selected edge is not chronological or on the minimum fibre, the
compact atom is not an actual terminal-law atom, and no ancestry-preserving
paid-row consumer or uniform-equilibrium payoff follows.

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

Complete stopping-law cap-band redistribution is now a checked local source
adapter. `stoppingLawSourceCapDebt_le_epsilon_add_two_mul_badMass`
(`MathUE/Probability/StoppingLawCapBandRedistribution.lean`) bounds cap debt by
the band width plus twice the reward bound times the complete source-law mass
outside that band; its pushforward preserves every survival prefix through the
selected cut, without finite-support or finite-clock assumptions. At a supplied
actual profile and mover whose debt exceeds a positive band width,
`exists_quittingCapBandFiniteCut`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/CapBandRedistribution.lean`)
selects a source-supported finite cut and reconstructs a literal unilateral
behavioral target. The target preserves the mover's unrestricted behavioral
cap, has debt at most the band width, gains at least source debt minus that
width, and retains exact debt subtraction and the `2 * M` joint-reach bound.
The generic compiler and game adapter have `M` and `L`; the latter is a local
actual-profile `A` after its profile and positive-debt hypothesis are supplied.
There is no source producer and no downstream `C`: these declarations do not
compactify, renew, prove Nash behavior, or produce a uniform-equilibrium
payoff.

The Research atlas now compiles that local adapter through the supplied
full-debt branch.  Starting from a positive global-minimum
`FinFourMinimumAtomProducer` whose four debt coordinates are positive,
`nonempty_finFourFullDebtCapBandTargetDispatch`
(`Research/Quitting/FinFourProducerAtlas/FinFourFullDebtCapBandTargetDispatch.lean`)
compactifies the cap-band targets and returns exactly one of two branches.  A
strict target yields a literal actual-reach paid port.  A target on the same
minimum fibre yields an actual fixed-weight stopping-law chord whose target
positive-debt support is nonempty and has cardinality at most three.  No
finite target or chord profile is asserted to be a minimum.

In the minimum branch,
`nonempty_finFourFullDebtCommonPrefixResponse`
(`Research/Quitting/FinFourProducerAtlas/FinFourFullDebtCommonPrefixResponse.lean`)
places the source, chord, and target tails behind common exact cap--Nash root
words and proves convergence of their complete unrestricted behavioral caps,
prescribed payoffs, and terminal laws.  The paired chronology compiler then
regenerates a producer at the exact target law point with the incoming hard
residual while retaining the literal chord-to-target update as a separate
one-use origin edge.  The selected public paired chronology is not identified
with the regenerated producer's internal chronology.

`nonempty_finFourFullDebtSupportContractedRenewal`
(`Research/Quitting/FinFourProducerAtlas/FinFourFullDebtSupportContractedRenewal.lean`)
starts the neutral renewable trace at that regenerated target and bounds it by
at most two further strict-support descents.  Independently, the strict branch
attaches the existing paid-cap exact trichotomy.  The direct classifier
entrance `finFour_noUniformPayoff_exists_fullDebtTargetDispatch_or_resetRigid`
supplies a same-point producer only in the full-debt arm; its independently
selected residual is not identified with the classifier's internal residual,
and the reset-rigid arm is returned unchanged.  This Research chain has `M`
and `L`, conditional source `A` at that entrance, and branch-local `C` through
the paid-cap or support-contracted-renewal consumers.  It does not consume the
resulting structural terminal exit, prove Nash play or terminal
approximation, or yield a uniform-equilibrium payoff.

The actual premark boundary is also literal.  A supplied
`QuittingActualReachedScreenedEndpointMark` records one complete behavioral
profile, a marked mover endpoint, and a distinct surely quitting screening
player.  Its literal one-date target preserves all other strategy data.
`source_mover_debt_eq_markedToggleGain_add_premarkResidual` and
`markedToggleGain_eq_liveMass_mul_localEndpointGap`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachedPairPremarkResidual.lean`)
give the exact complete-debt split.  Positive residual selects an actual
source-supported paid row strictly before the mark, and a separately supplied
attained positive global minimum attaches that row to the paid-cap trichotomy.
The pure nonempty-host specialization gives the complete signed source-to-target
terminal law and restricted premark response envelope.  The exact Fin4
deleted-reach regression shows that vanishing marked joint reach does not by
itself control a nonmover's complete behavioral cap.  This interface has `M`
and `L`, no source `A`, and branch-local `C` only after the separate minimum is
supplied.  It does not select the mark or minimum, establish chronology,
regenerate a source, or prove Nash play or a uniform-equilibrium payoff.

The moving marked-pair compiler begins from a supplied
`FinFourMovingMarkedPairMinimumSource`.  Its pure host is only required to be
nonempty: when the mover is routed to Continue, the distinct surely quitting
screening player witnesses target nonemptiness.  No support-cardinality result
is inferred from the host size.  The residual split first returns an
off-minimum actual-reach paid port or a minimum-approaching family.  In the
latter arm, one strict refinement compactifies the literal fixed-weight chords;
their target support is nonempty and has cardinality at most three by the
killed-coordinate minimum-fibre geometry.  Common exact cap--Nash prefixes
retain the literal chord-to-target update and converge in prescribed payoff,
unrestricted behavioral cap, debt, and complete terminal law.
`nonempty_finFourMovingMarkedPairSupportDescentAlternative`
(`Research/Quitting/FinFourProducerAtlas/MovingMarkedPairSupportDescentAlternative.lean`)
then returns the paid-port arm or same-residual support-contracted renewal.
This Research compiler has `M` and `L`, no source `A`, and branch-local `C`.
It does not construct the moving family, identify the public paired chronology
with a regenerated producer's internal chronology, consume the terminal exit,
or prove Nash play, terminal approximation, or a uniform-equilibrium payoff.

The reset-rigid positive-Never branch is now a literal supplied-data compiler.
`FinFourEscapeProductRestart.MinimumRestart.sourceAtProduct`
(`Research/Quitting/FinFourProducerAtlas/EscapeProductRestart.lean`) accepts
the exact product minimum with the constant product suffix behind words of
`n + 1` all-Continue exact cap--Nash roots.  The singleton cap bound is derived
inside this equality arm from global minimum semantics; it is not assumed of
the supplied product.  The internal `QuittingMinimumLawCausalSuffixAtom`
retains the exact point, complete law, survival-one prefix, and shifted
positive atom.  The fresh-clock compiler then makes two literal replacements
with quarter-Never reach and gain floors.
`finFourResetRigidEscape_productExit_or_singletonExit_or_supportContraction`
(`Research/Quitting/FinFourProducerAtlas/ResetRigidEscapeSupportContraction.lean`)
returns the product paid exit, singleton paid exit, or existing moving
support-contraction output, and `FinFourResetRigidProducerTransition.rank_lt`
(`Research/Quitting/FinFourProducerAtlas/ResetRigidProducerRank.lean`) proves
the stated one-way phase/support rank.  This chain has `M` and `L`, no
escape-origin source `A`, and branch-local `C` only through the attached paid
and moving consumers.  It constructs neither the product ancestry nor a
terminal atlas exit and yields no Nash-play, terminal-approximation, or
uniform-equilibrium conclusion.

The signed response-cycle compiler keeps its source requirements explicit.
`nonempty_quittingFinFourSignedRetraction`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FinFourSignedRetraction.lean`)
is the source-independent signed debt ledger, and
`nonempty_quittingNearMinimumExactResponseChordCompactification`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticNearMinimumExactResponseChordCompactification.lean`)
compactifies the literal finite chord profiles before deriving their minimum
geometry.  Given a supplied positive minimum producer, its chronology,
cofinal response cycles, and an explicitly selected asymptotic arm,
`nonempty_finFourSelectedCycleContractionResult`
(`Research/Quitting/FinFourProducerAtlas/FinFourSignedCycleContraction.lean`)
returns either one fixed paid label on a strict cofinal subsequence or a
same-residual strict-support minimum child.  The typed paid-row eliminators
retain the exact mover thresholds `epsilon / 16` and `epsilon / 64`, or the
fixed nonmover thresholds `epsilon / 48` and `epsilon / 192`, with their full
reach bounds.  These results have `M` and `L`; the high Research theorem has
conditional source `A` only at those supplied inputs.  It does not produce
the cofinal cycles or selected branch, attach renewal or terminal `C`, or
prove Nash play, terminal approximation, or a uniform-equilibrium payoff.

The debt-ratio chamber now has a literal actual-source interface.
`quittingTerminalExploitabilityInf_sq_div_two_bound_le_debtSumInf_sub`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticDebtRatioSeparation.lean`)
shows that, for reward bound `M > 0` and positive terminal exploitability
infimum `eta`, the total-debt infimum exceeds `eta` by at least
`eta^2 / (2 * M)`. Its square-root companion records the weaker closed-form
separation. The exact-response theorem
`quittingTerminal_exactResponse_debtRatioCrossing`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticDebtRatioResponse.lean`)
retains both displayed ratio comparisons and the positive endpoint debt
increase, but is conditional on a supplied exact response.
`nonempty_quittingDebtRatioApproximateResponseSource` and
`QuittingDebtRatioApproximateResponseSource.ratioCrossing_le_liminf_target_debtExcess`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticDebtRatioCarrierResponse.lean`)
instead select one fixed maximal-debt payer on a cofinal realizing sequence,
attach literal approximate responses with decreasing errors, and transfer the
ratio crossing to the target-debt liminf and an eventual half floor.

For four players,
`exists_eventually_nonempty_finFourDebtRatioResponsePaidCapPort_of_no_uniformEquilibriumPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourDebtRatioChamberPaidCapPort.lean`)
starts from failure of a uniform-equilibrium payoff, a positive reward bound,
the invariant upper chamber `D_* < 2 * eta`, and a prescribed
`0 < gamma < eta`. It chooses the minimum carrier point internally and
eventually attaches a separate actual paid-cap port to every
approximate-response target. The separation supplies the strict lower chamber
`eta < D_*`; no debt-minimum attainment by a behavioral profile is assumed.
These modules have `M`, `L`, and actual-source `A`, but no downstream
`C`: they do not consume the paid-cap trichotomy, force debt descent,
eliminate the inert branch, or prove a uniform-equilibrium payoff.

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

The same selected source now has an exact first terminal-law escape account.
`exists_quittingTerminalSemanticEscapeAccount_of_mem_carrier`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeAccount.lean`)
refines once more by compactness of the finite outcome simplex while retaining
one strict composed source subsequence, the original semantic limit, and every
marginal compact-law limit. The full outcome law converges on that same
subsequence. Every finite coalition mass of the profile reconstructed from the
limiting marginals is bounded by the selected outcome-law coordinate, so their
difference is nonnegative; its total is exactly reconstructed Never mass minus
selected Never mass, and its reward moment is exactly target payoff minus the
reconstructed payoff. The same selected laws also carry exact cap and debt
identities.
`quittingCompactStoppingLawProfile_cap_le_target_add_opponentNeverProduct_mul_negPart_of_lawLimit`
(`UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`)
bounds the reconstructed unrestricted behavioral cap by the selected target
cap plus the opponents' Never product times the singleton reward's negative
part. Thus a nonnegative singleton reward removes the correction.
`QuittingTerminalSemanticEscapeAccount.`
`debtSum_sub_target_eq_escapeSocialReward_sub_capDropSum`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeDebtJump.lean`)
then identifies reconstructed-minus-target total debt with escaped social
reward moment minus the sum of target-to-reconstructed cap drops. Under a
supplied global carrier debt minimum and nonnegative singleton rewards,
`QuittingTerminalSemanticEscapeAccount.`
`capDropSum_nonneg_and_le_escapeSocialReward_of_minimum`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeMinimumConsequences.lean`)
makes those cap drops nonnegative and bounds their sum by escaped social
reward. If no actual profile attains the same minimum debt value,
`reconstructedDebtJump_pos_of_minimumValue_not_attained` makes the debt jump
strict. With a positive reward bound,
`exists_positiveSocialRewardEscape_of_minimumValue_not_attained` selects a
coalition with positive escape mass and positive social reward, retaining the
product lower bound `jump / (2^card - 1)` and escape-mass floor
`jump / ((2^card - 1) * card * M)`. Thus equations (1)--(8) have generic
finite-player `M/L` and a carrier-facing selected/account `A`.
`exists_actualProfile_debtSum_le_of_singleton_nonneg_socialReward_nonpos`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeSocialSignAttainment.lean`)
shows that, when every own-singleton reward is nonnegative and every
coalition's aggregate reward is nonpositive, each carrier point is weakly
debt-dominated by an actual profile. At a supplied global carrier minimum,
`exists_actual_minimum_of_singleton_nonneg_social_nonpos` returns an actual
profile with the same minimum debt value and globally minimal debt. The
minimum account has zero debt jump, zero total and coordinatewise cap drops,
zero escaped social reward, and positive escape mass only on zero-social-
reward coalitions. Under strict aggregate negativity,
`minimum_point_attained_of_singleton_nonneg_social_neg` realizes the supplied
minimizing semantic pair itself. The full packet therefore has `M/L`, the
carrier adapter `A`, and branch-local `C` for weak-sign minimum-value
attainment and strict-sign exact-point attainment. Weak signs do not realize
an arbitrary supplied minimizer, and the positive-social escape arm still has
no `C`. None of these results proves properness or tightness, a Fin4
specialization, terminal Nash play, or a uniform-equilibrium payoff.

The complementary nonnegative-weight chamber is now literal. At an ordinary
positive global carrier minimum,
`minimumTerminalSemantic_nonnegativeWeight_chamber`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`)
turns the singleton margins into a sharp lower bound for every nonnegative
player weight; two positive coordinates make the coefficient of the minimum
debt strictly positive. An incompatible weighted terminal-outcome upper bound
forces zero minimum debt, and
`exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber` then invokes the
checked unrestricted-behavior consumer. On the positive-minimum side,
`minimumTerminalSemantic_exists_jointLawLiftFiniteAtom_weightedSurplus_and_mass_ge`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightLawCertificate.lean`)
selects an actual joint-law lift and one finite atom whose weighted surplus and
mass obey the general `c D / (R T K)` floor; the Fin4 symmetric-bound
specializations give `D / (16R)` and hence `D / (32R)`.

The finite-dimensional boundary is also checked. The generic cone alternative
in `MathUE/LinearAlgebra/FiniteConePositiveAlternative.lean` returns either a
strict positive supported costate or a nonnegative probability improvement
with support bounded by the player support cardinality.
`nonempty_terminalSemanticLawSparseSourceImprovement_of_positiveMinimum`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawSparseSourceImprovement.lean`)
applies this to an actual positive-minimum joint law while retaining the source
atom identities. Its masses are reweighted, so this is law provenance rather
than behavioral realization. The Fin4 sharp regression has exactly four
positive pair atoms and is unrealizable by any behavioral profile or one-date
product root; the two-player regression separately shows that a sparse
positive-social law need not be Nash. Thus the chamber and sparse-law layers
have `M/L` and actual compact-minimum or joint-law `A`; only the zero-minimum
chamber has a downstream `C`. No sparse-law behavioral, chronological, or
uniform-equilibrium consumer is claimed.

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

A separate conditional hull foundation is now literal.
`quittingLawTightCapNashSaturationHull`
(`UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashSaturationHull.lean`)
closes one supplied joint-law origin under exact cap--Nash prefixes and
debt-nonincreasing replacement within one fixed terminal-law fibre.  The hull
is a compact carrier subset only when that origin is already in the joint
carrier.  Given a positive global carrier debt floor and a positive finite
origin atom,
`exists_quittingLawTightCapNashSaturationHull_minimum_retaining_atom` gives a
hull debt minimizer which retains the atom and satisfies the exact
debt-weighted cone inequality.  The companion minimum layer
(`UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashMinimumFace.lean`)
defines the hull's minimum equality level set; “face” does not assert
convexity.  Every point on that level set minimizes debt on its complete
terminal-law fibre.  At positive minimum debt, all Continue is the unique
exact root against the displayed cap, and its semantic/law prefix fixes the
point.  The off-minimum bound
`quittingLawTightCapNashSaturationHull_rootAbsorptionMass_le_debtExcess_div`
and its finite-chain telescopes charge exact-root absorption to debt above
the hull minimum.  Taken alone, this foundation is `M` and `L` but supplies
neither its origin hypotheses nor a downstream consumer.

Global-minimum inheritance is also literal.
`lawTightCapNashMinimum_globalMinimumOriginDebtMoat`
(`UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashGlobalMinimumMoat.lean`)
shows that a positive hull minimum over a globally minimizing carrier origin
has the same total debt as the origin, is itself globally debt-minimal, and
satisfies the all-owner singleton moat with the origin debt on the left-hand
side.  This remains a conditional carrier statement with `M` and `L`: it does
not supply the origin or realize the minimum behaviorally.

The strict carrier classification on that foundation is now literal.
`lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle`
(`UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean`)
uses a supplied positive hull minimum, positive finite atom, and globally
minimal semantic source.  Every selected minimum-face point has full debt
support, a same-law reset-rigid return whose all-Continue prefix fixes the
returned point, or exact singleton/Never support with cap binding and a
binding-collision cycle of period at least two.  Its finite-cap and carrier
ingredients are
`exists_quittingSingletonCollisionGain_pos_of_unique_allContinue` and
`terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward`.

For Fin4,
`finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`)
constructs the origin and positive law-tight minimum, retains a positive
finite atom, exposes both global-minimum statements and their debt equality,
and applies the literal origin-debt moat to the classification.  The
singleton/Never arm has cap equal to its singleton reward, so its owner's moat
would force the positive origin debt to be nonpositive; this deletes that arm
and leaves full debt support or reset-rigid same-law return.  The earlier
`exists_finFourLawTightSaturationMinimum_of_no_uniformPayoff` and
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` declarations are
compatibility projections from this canonical result.  This gives `M`, `L`,
Fin4 source `A`, and branch-local `C` for the singleton/Never exclusion only.
Neither surviving chamber has a behavioral or chronological consumer, and no
contradiction or uniform-equilibrium payoff follows.

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
The stronger theorem
`sameStageEndpointTrace_false_of_visitedSupport_card_le_four`
(`Research/Quitting/SameStageEndpointMonodromyImpossible.lean`) proves that
no such same-stage dispatched trace exists whenever the literal union of its
visited coalitions has cardinality at most four, even if the ambient finite
player type is larger.  The Fin4 adapters
`not_nonempty_finFourMonodromyProducer`,
`not_nonempty_finFourCommonHostMonodromyProducer`, and
`not_nonempty_finFourComplementaryPairMonodromyProducer` therefore eliminate
both monodromy tags using the producer's stored trace alone.  The source- and
witness-preserving eliminator `FinFourProducerResidual.withoutMonodromy` and
the global bounded-data theorem
`uniformPayoff_or_nonempty_finFourProducerResidualWithoutMonodromy` contract
the atlas residual to minimum singleton, purified singleton, terminal
singleton, or quantitative tail escape.  This no-go has `M`, `L`, `A`, and
`C` for literal branch deletion.  It does not consume any surviving tag,
prove a uniform-equilibrium payoff, or complete the atlas; the five-player
sharpness construction stated in the source packet is not checked in Lean.
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
one-way producer normalization, not an equivalence; the two non-singleton
nodes still have no consumer here.

The source-attached strengthening
`FinFourAtlasWeakConcentratedSingletonCore.nonempty_strongConcentratedPacket`
(`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`) takes
the exact weak core at the same `mu^2 / 8` resolution, extracts its singleton
owner `j`, chooses a distinct packet owner `o`, and applies the literal
best-endpoint update.  The original `j` remains in the routed terminal, while
`FinFourAtlasWeakStrongConcentratedPacket.routedTerminal_mode_and_card` records
the honest mode split: Continue leaves the singleton `{j}`, whereas Quit gives
the pair `{o, j}`.  The generic adapter's
`QuittingStageAtomConcentratedPacketAdapter.sourceStageMass_le_targetStageMass`,
`QuittingStageAtomConcentratedPacketAdapter.ownerMarkedDefect_eq_zero`, and
`QuittingStageAtomConcentratedPacketAdapter.targetTail_eq_sourceTail`
(`Research/Quitting/PositiveStageAtomConcentratedPacket.lean`) give no-loss
stage mass, exactly zero marked owner defect, and the unchanged semantic tail;
the owner's unrestricted cap is also preserved.  This is a constant-profile
reprojection packet, not a claim that its full target root is Nash or
near-minimal.

For the diffuse minimum-singleton origin,
`FinFourOwnerCompressedSingletonProducer.nonempty_strongConcentratedPacket`
(`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`) uses
the producer's already fixed chronology: for every `0 < lambda < mu` and every
depth it retains an endpoint beyond that depth and constructs the packet at
exactly `lambda`, without reselecting the chronology.  At the canonical scale,
`FinFourAtlasWeakConcentratedSingletonCore.nonempty_strongConcentratedPacketConsumption`
and
`FinFourAtlasWeakStrongConcentratedPacketConsumption.strategic_or_collisionMinimumResidual`
(`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`)
give the exact downstream contraction.  One arm carries the concentrated
strategic dispatch and the established atomic-toggle-or-deletion interface;
the other retains the same literal packet as a collision-minimum residual.
On Fin4,
`not_hasQuittingExactPlayerDeletionAtGap_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/ExactPlayerDeletionSmallSurvivorNoGo.lean`)
also rules out the deletion certificate at the witness's positive gap.  Thus
the diffuse minimum-singleton obligation is closed as a separate atlas leaf,
but the resulting strong
concentrated-singleton obligation is only contracted, not completed.  The
arbitrary-resolution theorem
`FinFourOwnerCompressedSingletonProducer.nonempty_strongConcentratedPacketConsumption`
provides the same split at every admissible `lambda` and depth on that one
chronology.

A separate fixed-resolution one-row route keeps the same weak core but does
not invoke that consumer.
`FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairPacket`
(`Research/Quitting/FinFourProducerAtlas/ForcedPair.lean`) selects a
table-level full-gap outsider whose best endpoint is Quit, so the literal
singleton becomes a pair carrying the complete reached live mass.  The
forced owner has zero defect at that pair; screening the other three Fin4
coordinates selects a payer with defect at least `D_* / 3`.
`FinFourWeakCoreForcedPairPacket.resolution_mul_terminalGap_le_forcedOwnerGain`
gives the first actual gain floor and
`FinFourWeakCoreForcedPairPacket.canonical_payerGain_floor` gives the paid
endpoint floor `mu^2 * D_* / 24` at the fixed `mu^2 / 8` resolution.  The
named own-debt, full-mass, off-date-profile, and semantic-tail accessors retain
the exact source provenance.  This direct endpoint has `M`, `L`, and `A`; its
separate consumer below supplies `C` only for a collision/minimum-tail
contraction.  It does not make the whole pair target near-minimal or control
the other coordinates' caps.

The one-shot Part A theorem
`FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairResidualCapstone`
(`Research/Quitting/FinFourProducerAtlas/ForcedPairMinimumTailConsumer.lean`)
retains the supplied weak core, selected packet, exact collision residual, and
the residual cluster's equality to the core's actual post-date semantic tail.
Its typed `FinFourWeakCoreForcedPairPacket.TailOutcome` is either strict tail
escape or minimum-tail with payer defect at least `lambda * D_* / 6` and gain
at least `lambda^2 * D_* / 6`.  The underlying packet declarations retain the
stronger `D_* / 3`, `lambda * D_* / 3`, `lambda * gamma`, and canonical
`mu^2 * D_* / 24` bounds, exact own-debt subtraction, and no-loss marked mass.
An arbitrary weak core may still take the strict tail-escape arm.

Part B fixes the source choices before the resolution quantifier.
`FinFourMinimumAtomProducer.nonempty_minimumReturnForcedPairFamilyCapstone`
(`Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`) returns
one `FinFourOwnerCompressedMinimumReturnForcedPairFamilyCapstone`, containing
one chronology and one table-selected outsider before every later
`0 < lambda < mu`.  At each resolution its `ResolutionCapstone` retains a
single moving reprojection packet, an actual collision-minimum residual whose
cluster debt is exactly `D_*`, and one payer fixed across the cofinal strict
subsequence with defect at least `D_* / 3` and gain at least
`lambda * D_* / 3` at every index.  The granular declarations also state the
weaker `lambda * D_* / 6` and `lambda^2 * D_* / 6` packet crosswalk bounds.
`quittingAllContinueProfileSpine_crossTailClosure`
(`UniformEquilibrium/Quitting/Root/SelfTailClosure.lean`) and
`quittingSpineDebtExcess_crossTailClosure`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSelfTailClosure.lean`)
give the literal full post-date spine and exact debt-excess identity used to
eliminate the off-minimum residual arm.  These results have `M`, `L`, `A`, and
`C` for the checked forced-pair collision/minimum-tail contraction.  The
surviving minimum-tail collision residual has no cross-coordinate cap control,
return, regeneration, recursive descent, completion, or uniform-payoff
consumer; its whole pair source is not asserted minimum, near-minimal, or
cap--Nash.

The source-preserving completion atlas now packages this boundary without
discarding which monodromy-free entrance produced it.
`FinFourProducerResidualWithoutMonodromy.exists_cofinalSingletonPacket`
(`Research/Quitting/FinFourProducerAtlas/SourcePreservingSingletonFrames.lean`)
returns the exact residual projection together with one entrance-indexed
cofinal stream.  Its ranks are strictly increasing and tend to infinity, the
retained suffix semantic/outcome laws converge to the one fixed source point,
the literal prefixed debts converge to `D_*`, and every singleton target keeps
the complete post-date behavioral spine.  The selected-row constructors use
exactly their stored rows; the minimum-singleton constructor fixes one
owner-clock chronology before the whole stream.

`FinFourSourcePreservingSingletonFrame.nonempty_forcedPairResidualCapstone`
(`Research/Quitting/FinFourProducerAtlas/SourcePreservingForcedPair.lean`)
then attaches to every literal frame a full-gap forced pair, a paid endpoint,
and its actual collision-minimum residual.  The forced owner has zero marked
defect, the payer has defect at least `D_* / 3`,
`FinFourSourcePreservingForcedPairPacket.canonical_payerGain_floor` gives the
exact `mu^2 * D_* / 24` floor, and
`collisionCluster_eq_framePostDateTail` identifies the compact residual
cluster with that same frame's actual continuation tail.  The full post-date
spine and terminal outcome law are literal equalities, not compact
substitutions.

Finally,
`uniformPayoff_or_sourcePreservingCompletionOutcome`
(`Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`)
maps arbitrary bounded Fin4 rewards to a uniform payoff or one exact-residual
outcome: a source-attached uniform tail escape or a source-attached minimum
return.  A simultaneous finite-label subsequence fixes the singleton owner,
forced owner, payer, and payer action.  `FinFourUniformEscapePacket.tailDebt_floor`
and `FinFourMinimumReturnPacket.tailDebt_tendsto_minimum` state the two literal
tail-debt alternatives.  Repeated `drop` gives checked source-coherent
self-shift trajectories.  `FinFourCompletionMode.reachable_iff_explicit`,
`FinFourCompletionMode.sameComponent_iff_eq`, and
`FinFourCompletionMode.isTerminal_iff` calculate the declared graph's three
singleton SCCs and its two terminal structural components from the
reflexive--transitive closure of the exact edge table.

The two modes now have checked branch consumers in
`Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`.
For every retained escape row,
`FinFourUniformEscapePacket.exists_maximalCapNash_halfFloorDispatch` chooses a
maximal-absorption exact root against that same literal tail.  It has positive
joint Continue mass and gives either a half-floor return-selection certificate
or universal same-tail undercharge, with the remaining all-Continue/blocker
alternative.  `semanticPair_continuationProfile_eq_tail`,
`continuationProfile_outcomeLaw_eq_reference`, and
`returnedProfile_debt_le_minimum_add_halfFloor` expose the actual continuation
profile, its complete law provenance, and the near-minimum debt of a selected
returned profile.  No reset coordinate is supplied, so this is not the later
reset-excursion compiler.

For minimum return, the source-independent
`QuittingMarkedPairMinimumTailSource.nonempty_normalizedThreeRole_or_strictInert`
(`Research/Quitting/FixedPairMinimumTailNormalizedReturn.lean`) derives its own
compact subsequence, full-decoration limit, normalized passport, minimizer,
and actualizer from uniform positive mass/gain floors and tail-debt convergence.
`FinFourMinimumReturnPacket.forcedPairTail_eq_tail` identifies its forced-pair
tail with the same collision tail term by term, while the normalized-family
and actualizer spine accessors retain the literal profiles, dates, root words,
and post-date reference law.  The Fin4 wrapper
`FinFourMinimumReturnPacket.nonempty_normalizedThreeRole_or_strictInert` then
returns actual three-role endpoint-law regeneration/ascent or the strict
normalized inert point.  Equality-arm regeneration preserves the underlying
quantitative hard residual and exact new endpoint law; it does not reproduce
the outer entrance or chronology, and the compact target law need not be the
original source law.

`uniformPayoff_or_sourcePreservingConsumedOutcome` keeps the exact outer
residual as a dependent index while composing both branches.  The completed
atlas reduction therefore has `M`, `L`, `A`, and branch-local `C`, but still no
terminal `C`: `FinFourUniformEscapeCapstone` and
`FinFourMinimumReturnCapstone` remain open.  The self-shifts are recurrence,
not descent; no forced-pair target is asserted minimum, near-minimum, or
full-root Nash; and no cross-coordinate cap bound, reset transfer, terminal
approximation, recursive entrance regeneration, or uniform-equilibrium
completion is proved.

The same actual cofinal forced-pair family now has an independent finite-cycle
contraction.  `exists_finFourMaximumToggle_terminalOrbit_or_closedSegment`
(`Research/Quitting/PaidNonsingletonToggleCycle.lean`) iterates one
deterministic table-level maximum positive toggle from the fixed pair.  It
either reaches a singleton or closes on a simple nonsingleton cycle.
`FinFourMaximumToggleClosedSegment.period_eq_four_or_six_or_eight` gives the
exact Fin4 periods, while `gainAt_floor` and `moverDebt_succ_eq_sub_gain` give
the actual `lambda * D_* / 4` paid floor and exact mover-debt subtraction at
every realized same-date sibling edge.  The reusable complete-profile ledger
`FinFourLiteralSiblingCycle.exists_spectator_debtRise` then produces the sharp
Fin4 divisor `3` without assigning a chronology to those edges.

The actual source adapter `nonempty_forcedPairPaidNonsingletonCycle`
(`Research/Quitting/FinFourProducerAtlas/PaidNonsingletonCycle.lean`) freezes
one cycle edge and one distinct observer along a strict subsequence of the
original forced-pair source indices.  It retains the literal source and target
profiles, original marks, common post-date reference spine, paid edge, and
observer debt increase `lambda * D_* / 12`.
`FinFourForcedPairPaidNonsingletonCycle.atomAlternative` applies the checked
stopping-law decoder with fixed charge `7 * lambda * D_* / 96` and a positive
error tending to zero.  The compact endpoint keeps the actual joint
semantic/law limits and routed-law mass at least `lambda`.
`nonempty_paidNonsingletonCycleOutcome` is exhaustive: a paid singleton, a
strict off-minimum endpoint, or a fresh `FinFourMinimumAtomProducer` at that
same endpoint law with the incoming hard residual unchanged.  This route has
`M`, `L`, and `A`; `C` is present only for the stopping-law atom dispatch and
the equality-arm minimum-source regeneration.  A horizontal sibling edge is
not a transition in one play, and the regenerated chronology need not contain
it.  No strict off-minimum return, renewable rank descent, terminal
approximation, atlas completion, or uniform-equilibrium conclusion is proved.

A normalized-passport layer and its actual Fin4 source adapter are integrated
in Research.
`QuittingMarkedPairDecoratedFamily.rawDecoration_markedMass_eq`,
`QuittingMarkedPairDecoratedFamily.rawDecoration_actualGain_eq`, and
`QuittingMarkedPairDecoratedFamily.descendant_postMarkSpine_eq`
(`Research/Quitting/NormalizedPassportPrefixOrbit.lean`) retain exact
arbitrary-prefix mass and gain scaling and the full post-mark spine for a
supplied decorated family of actual rows.  Compactness of its arbitrary-prefix
closure and normalized slice then gives
`QuittingMarkedPairDecoratedFamily.exists_minimum_normalizedPassportSlice_eq_or_strict_inert`
(`Research/Quitting/NormalizedPassportMinimizer.lean`): a supplied convergent
passport yields a slice minimizer whose debt either returns to the displayed
global minimum, or is strictly larger and admits exactly the all-Continue root
as an exact cap--Nash root.

In the generic equality arm,
`QuittingMarkedPairMinimumReturnActualizer.nonempty_threeRoleEndpointLaw_of_minimumReturn`
(`Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`) selects
actual rows, freezes one mover, recipient, and Boolean endpoint action, and
compactifies the source semantic pairs together with the endpoint semantic
pairs and complete terminal laws.  The retained routed atom has limiting mass
at least the packet resolution.  The endpoint object projects losslessly to
the older `ConcentratedCollisionFourRole.ThreeRoleLimitChord` surface.

The Fin4 adapter
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_normalizedReturnSelection`
(`Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`) constructs the
decorated family from the actual forced-pair rows and derives its compact
subsequence and convergent passport rather than accepting either as supplied
data.  It retains the exact packet and source ranks, finite prefix-root words,
source and target profiles, marked dates, fixed pair and labels, positive mass
and gain floors, zero marked-owner defect, full post-date reference spines,
and whole- and tail-debt limits.
`FinFourMinimumAtomProducer.exists_normalizedReturnSource_for_all_resolutions`
fixes one minimum-atom source chronology and one outsider before every later
`0 < lambda < mu`; the packet, compact subsequence, minimizer, and outcome may
depend on `lambda`.
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_normalizedReturnThreeRole_or_strictInert`
therefore has `M`, `L`, and `A` in both arms.  In the equality arm,
`ConcentratedCollisionThreeRoleEndpointLaw.finFour_mover_drop` and
`ConcentratedCollisionThreeRoleEndpointLaw.finFour_recipient_rise` give the
literal `rho^2 * D_* / 8` mover decrease and `rho^2 * D_* / 64` recipient
increase.  `ConcentratedCollisionThreeRoleEndpointLaw.nonempty_finFourRegenerationOrAscent`
then gives strict endpoint-debt ascent or `C` through exact source regeneration
at the endpoint's own joint semantic/law point.  The regenerated
`FinFourMinimumAtomProducer` retains the incoming hard residual, exact endpoint
point, routed terminal, and terminal-law mass floor.  The strict enlarged-slice
inert arm has no checked downstream consumer.  The minimizer need not belong
to the original cluster or be behaviorally attained, the actualizer's retained
origin ranks need not be cofinal, and its finite root word is not claimed
canonical.  No canonical return ray, chronology return, rank decrease,
recursive closure, strict-inert consumer, or uniform-equilibrium conclusion
follows; an arbitrary public chord without the actual endpoint law cannot be
regenerated.

The strict three-role endpoint-ascent branch now has a literal outgoing
transition.  The production theorem
`nonempty_pureTimeResetArrival_of_uniformDebtFloor`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinitePureTimeResetArrival.lean`)
takes any actual profile to a zero-debt owner with positive incidence in a
distinct opponent along at most `card ι + 3` profitable pure-time updates.
The separate `nonempty_finiteDeadlineIncidenceSelection` retains exact cap
attainment, length at most `deadline + 1`, and total opponent incidence at
least one; with at least two players,
`exists_finiteDeadlineIncidenceSelection_with_selectedOpponent` selects one
opponent coordinate carrying at least `1 / (card ι - 1)`.
`nonempty_actualProfileFixedLawResetHandoff` attaches the arbitrary-profile
path and literal final law to the existing fixed-law reset dispatch.

The finite-clock minimum branch now also has a production-level conditional
reduction.  For a supplied finite-clock positive global minimum,
`finiteClockMinimum_exactCapPurification_or_pureTimeDescentPaidPort`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockMinimumPaidPort.lean`)
first canonicalizes the actual stopping laws without changing the prescribed
payoffs or unrestricted behavioral caps, then follows at most `card ι` exact-cap
pure-time replacements while retaining every pre-exit node on the source debt
fibre.  It returns either a deadline-bounded off-minimum paid row or a canonical
pure-time minimum whose paid row carries the literal ancestry constructed by
deadline descent.  The Fin4 specialization records the bound four.  This has
`M`, `L`, and branch-local `A` for the supplied profile, but no `C`: it neither
produces the finite-clock minimum nor supplies chronology, renewal, a paid-port
consumer, or a uniform-equilibrium payoff.

The arbitrary-clock minimum branch now has its own actual-source adapter,
without assuming a common finite stopping-law calendar.
`minimumRealizingSequence_purify_or_offMinimum`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/ArbitraryClockMinimumPurification.lean`)
uses positive-support pure-clock replacements and finite terminal-semantic
codes to turn any supplied realizing sequence into a canonical minimum or an
actual finite-replacement descendant strictly above it.  The canonical branch
then passes through checked pure-time minimum descent.
`exists_minimumRealizingSequence_offMinimumActualReachPaidPort_of_debtSumInf_pos`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ArbitraryClockMinimumActualReachPaidPort.lean`)
selects the compact minimum and retained actual realizing sequence directly
from positive terminal-debt infimum.  Its off-minimum target carries a
source-supported paid first-disagreement row, debt at least the average
minimum, paid gain at least one quarter of that average, and the literal
`4M`, `8M`, and `32M²` actual-reach floors.  The Fin4 wrapper normalizes these
to `D*/4` and `D*/16`.  This has `M`, `L`, and source `A` on the positive
infimum branch, but no downstream `C`.  Finite replacement ancestry does not
preserve nonmover caps or individual debts and is not a game chronology,
renewal, Nash--Bellman path, paid-port consumer, or uniform-equilibrium
conclusion.

That actual paid port now also enters a finite horizontal response alternative.
`exists_quittingPureTime_capAttainer_mem_inheritedResponseAlphabet`
(`UniformEquilibrium/Diagnostics/Quitting/PureTimeInheritedResponseAlphabet.lean`)
keeps exact pure-time responses inside the initial clocks together with
`Never` and date zero, an alphabet of size at most `card ι + 2`.
`exists_minimumDebtEntrance_xor_offMinimumExactResponseCycle`
(`UniformEquilibrium/Diagnostics/Quitting/PureTimeExactResponseMinimumAlternative.lean`)
therefore sends the deterministic maximal-debt exact-response orbit to exactly
one of its first minimum-debt state or a nontrivial closed segment whose whole
pre-repeat prefix stays strictly above the minimum.  Every edge gains at least
`D*/card ι` and has a fresh paid first-disagreement row.  In Fin4 the orbit
repeats by time `1296`;
on an off-minimum cycle,
`exists_nonmover_payoffFall_and_debtRise_ge_twelfth_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourPureTimeExactResponseCycleExternality.lean`)
gives a nonmover prescribed-payoff fall and a possibly different nonmover debt
rise, each at least `D*/12`, from the exact closed-cycle externality ledger.
`exists_finFourActualSourcePureTimeResponseAlternative_of_debtSumInf_pos`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourActualSourcePureTimeResponseAlternative.lean`)
starts directly from positive terminal-debt infimum, retains the normalized
actual paid port, purifies through at most four support-selected non-worsening
replacements, and records literal ancestry from its actual source to the
initial pure profile and every displayed orbit profile.  Its selected
entrance time or cycle endpoint and period are bounded literally by `1296`.
These results have
`M` and `L`; the direct positive-infimum theorem has source `A`, and attaching
the paid port to the response alternative is a branch-local `C`.  The orbit is
horizontal rather than temporal: it provides no chronology, renewal, Nash or
Nash--Bellman path, preservation of nonmover caps or debts, consumer of the
resulting entrance/cycle, or uniform-equilibrium conclusion.

A separate normalized Fin4 pair compiler is now integrated.
`terminalDispatch_nonempty`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FinFourOrientedMinimumPairChord.lean`)
starts from a supplied positive global-minimum pure pair, the two distinct
outsiders, and a strict incoming triple-to-pair dropout gain.  It returns a
profitable pair-member Never response, a strictly off-minimum join by the
unique remaining outsider, or a same-minimum join.  In the equality arm,
`pairToJoinedTripleChord_debt_eq` gives the exact coordinatewise affine debt
formula, `pairToJoinedTripleChord_debtSum_eq` keeps total debt fixed, and
`quitNowResponse_from_pairToJoinedTripleChord_gain_eq` states the literal
updated-profile gain `(1 - lambda) * D_*`; the midpoint gain is `D_*/2`.  The
one-date profile and update identities are owned by
`UniformEquilibrium/Diagnostics/Quitting/PureCoalitionOneDateNeverAdapters.lean`
and delegate unrestricted behavioral cap formulas to the canonical sure-exit
theory.  This local compiler has `M` and `L`, but no actual-source `A` and no
downstream or renewable `C`.  In particular it does not construct a
positive-time endpoint, tail screen, chronology, renewal, Nash path, terminal
equilibrium, or uniform-equilibrium payoff.

The zero-Never, zero-singleton joint-law face now has an exact production
realization.  For a supplied point of the joint terminal semantic/law carrier,
`exists_twoSureProductRoot_realizing_law_of_mem_terminalSemanticLawCarrier`
(`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`)
constructs one product root with two fixed sure quitters and the exact complete
terminal law.  Under strict singleton margins,
`exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
realizes the complete prescribed-payoff/unrestricted-cap pair and law both by
root-then-Never and stationary repetition; the nonstrict theorem supplies one
all-Continue padding row.  This has `M`, `L`, and branch-local `A` from the
supplied joint carrier point, but no `C`.  It does not produce a positive global
minimum, compose this realization with finite-clock purification, preserve a
fixed calendar intervention law, implement sure-core descent, or prove a
uniform-equilibrium payoff.

For the actual Fin4 endpoint data,
`FinFourThreeRoleAscentResetHandoff.nonempty_of_strict_ascent`
(`Research/Quitting/FinFourProducerAtlas/ThreeRoleAscentResetHandoff.lean`)
selects one common retained rank with strict literal source-to-endpoint debt
ascent and routed terminal mass above half the packet resolution.  Its path
is structurally headed by the fixed recipient's profitable update, has length
at most seven, and ends in a fixed-law reset dispatch based at the unchanged
minimum source.  The recurrent source profiles converge to the endpoint's
`sourceLimit`; Lean identifies only its total debt with the fixed source's
minimum debt, not the two semantic points.  This transition has `M`, `L`,
`A`, and branch-local `C` for the maintained target-ascent item.  It does not
consume either reset-dispatch branch, produce a return or rank descent, or
imply terminal approximation or a uniform-equilibrium payoff.

The minimum-target branch now also has a source-faithful regeneration surface.
`nonempty_sourceFaithfulMinimumCausalization`
(`Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`) keeps one
supplied joint semantic/law realizing family and its literal marked dates,
selecting only finite exact cap--Nash root words and finite cutoffs.  Its
prefix debt returns to the positive global minimum, joint survival tends to
one, the shifted atom identity is exact, and the shifted marked mass is
eventually at least half the supplied floor.  For arbitrary complete
behavioral responses,
`quittingTerminalPayoff_shiftedBehavioralResponse_sub_eq` gives the exact
two-counterfactual payoff contrast multiplied by player-deleted survival;
`FinFourSourceFaithfulMinimumTargetRegeneration.responseMenu_lowerBound_transport`
retains every supplied rankwise menu lower bound with that same multiplier;
`QuittingSourceFaithfulMinimumCausalization.opponentSurvival_tendsto_one`
shows that multiplier tends to one.

At a same-minimum Fin4 three-role endpoint,
`ConcentratedCollisionThreeRoleEndpointLaw.nonempty_sourceFaithful_finFourMinimumTargetRegeneration`
(`Research/Quitting/FinFourProducerAtlas/SourceFaithfulThreeRoleRegeneration.lean`)
uses the nonsingleton routed-mass chain to retain the literal endpoint target
profiles and incoming marks.  The resulting public chronology and
`FinFourSourceFaithfulMinimumTargetRegeneration.next_residual_eq`,
`next_point_eq`, `next_terminal_eq`, `chronology_profile_eq`, and
`chronology_mark_eq` make the provenance literal; `toMinimumTargetRegeneration`
forgets to the older endpoint-law regeneration.  For a singleton incoming
mark, `nonempty_sourceFaithful_reselectedMarkRegeneration` instead keeps every
target profile, the source residual, point, and routed terminal while selecting
new positive finite-window dates; it does not retain the incoming dates or a
uniform per-stage floor.  This source-faithful route has `M`, `L`, and `A`, but
no `C`: no common observer is selected, no paid cycle is oriented, and no
spectator-leakage, renewal, terminal-approximation, or uniform-equilibrium
consumer is proved.

The common-prefix unrestricted-cap transport is now integrated in
`UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean`.
`abs_quittingContinuationBestResponseValue_literalRootStack_sub_max_le`
controls the complete behavioral cap behind a nonempty finite word by the
larger of singleton cash-out and the suffix cap, with error `2 * M` times the
lost opponent-deleted survival.  The joint-survival limit wrapper transports
convergent suffix caps whenever the limiting suffix cap strictly dominates
singleton cash-out.  This is source-independent `M`/`L` only: it supplies no
prefix source, Nash condition, minimum, chronology, renewal, or consumer.

The source-independent chord geometry is now integrated in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticMinimumResponseChord.lean`.
`QuittingMinimumResponseChordLaw.ofProfiles` starts from literal endpoint and
one-player response profiles and their compact joint-law limits.  At equal
global-minimum total debt, `chord_debt_eq_affine`,
`chord_debtSum_eq_endpoint`, and `chord_support_eq_union` make every debt
coordinate, total debt, and positive-debt support exact.  Killing one positive
endpoint coordinate makes the response support a strict subset of the chord
support; in Fin4 it is nonempty of cardinality at most three.  This generic
layer has `M` and `L`, but no source `A` or consumer `C`.

Independently, the supplied Fin4 tangent/full-replacement endpoint has a
quantitative paid-row compiler in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FullReplacementQuantitativePaidPort.lean`.
`QuittingPositiveMinimumDebtTangentFamily.nonempty_finFourFullReplacementQuantitativePaidPort`
selects one fixed nonmover with limit debt at least `D_*/3`, eventual debt at
least `D_*/4`, paid gain `D_*/16`, and the literal `4M`, `8M`, and `32M²`
reach inequalities.  The direct positive-minimum wrapper supplies the compact
minimum, tangent family, mover, and full-replacement cluster, so this leaf has
`M`, `L`, and branch-local `A`.  The replacement is horizontal rather than
chronological; the varying paid rows have no downstream `C`, regeneration,
renewal, or uniform-equilibrium consequence.

A separate conditional response-chord compiler starts from a supplied
`FinFourMinimumResponseRectanglePacket`.  In
`Research/Quitting/MinimumResponseChordLaw.lean`,
`responseAtom_pos_imp_pureTime_ge_mark` uses one positive complete-law
rectangle atom to exclude every finite response before the marked row, and
`quittingStageCoalitionMass_le_update_pureTime_routed` proves literal no-loss
routing for the resulting late-or-Never response.  The Fin4 theorem
`FinFourMinimumResponseRectanglePacket.nonempty_minimumResponseRectangle`
(`Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean`)
freezes the Boolean response mode on a strict refinement of the packet's same
joint-law subsequence.  The routed floor is then derived by
`FinFourMinimumResponseRectangle.routedStageMass_floor`, not supplied as a
post-route certificate.

For every proper parameter,
`FinFourMinimumResponseRectangle.nonempty_minimumResponseChord` constructs one
further actual compact chord.  The exact law and coordinate debts are affine,
the routed law atom has mass at least `theta * lambda`, the mover edge keeps
the floor `g / 2` for
`theta <= g / (2 * (g + 2 * R))`, and the response-square charge is exactly
scaled by `1 - theta`.  Both the response endpoint and chord point are
causalized into `FinFourMinimumAtomProducer` objects with the incoming hard
residual and their own displayed law.  This supplied-packet compiler has `M`
and `L` only.

The actual decoder
`FinFourNormalizedReturnSourceCapstone.nonempty_minimumResponseActualSourceOutcome`
(`Research/Quitting/FinFourProducerAtlas/MinimumResponseChordActualDecoder.lean`)
now supplies `A` from the normalized-return source capstone.  Its equality arm
keeps the actualizer and exact minimum identity, and exhaustively returns
endpoint debt ascent, a routed singleton, a prescribed atom, strict response
ascent, or a compiled minimum rectangle.  In the last arm,
`FinFourMinimumResponseCompiledRectangle.nonempty_chord_with_responseSupportDrop`
constructs every proper chord and proves that its positive-debt support
strictly contains the response support.  The canonical source records the
literal scales `rho^2 * D_* / 8` for mover gain, `rho^2 * D_* / 64` for
endpoint observer debt, `rho^2 * D_* / 128` for decoder charge, and
`7 * rho^2 * D_* / 1024` for the compiled response rectangle.

This actual route starts from the normalized-return equality endpoint; it is
not the advertised paid spectator-cycle decoder.  Compact law points need not
be attained, regenerated chronologies are not asserted to contain the old
response rectangle, and the strict support drop is one-time rather than a
renewable source rank.  No branch here has a checked chronology return,
terminal approximation, recursive consumer, or other `C`.

The integrated maximal-root ledger now applies to that supplied response
rectangle without changing its source.  The selector
`exists_maximalAbsorption_isZeroQuittingRootNash`
(`UniformEquilibrium/Quitting/Root/MaximalAbsorptionNash.lean`) chooses an
absorption-maximal exact root at every endpoint cap.  The exact prefix debt,
charge, and sibling-atom identities in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleMaximalRootLedger.lean`
give playerwise debt scaling, the standalone survival floor
`D_* / (8 * M) <= 1 - a_n`, and the retained lower estimate
`c * D_* / (32 * M) <= 16 * atom`.  Under vanishing absorption,
`quittingRectangleMaximalRootPrefixedEndpoint_tendsto_cluster` retains the
common joint semantic/law limit after the literal maximal-root prefix.  The
ordered capstone
`QuittingStoppingLawRectangleJointAtomLimit.maximalRoot_exactlyOne`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleMaximalRootReduction.lean`)
returns exactly one of a uniformly charged strict subsequence, a minimum-fibre
reset-rigid chamber, or an off-minimum branch with vanishing absorption and
charge; `maximalRoot_threeWay` remains the inclusive eliminator.  The
minimum-fibre arm uses
`totalOpponentIncidence_pos_of_minimumLaw_of_debt_eq_zero`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumOpponentIncidence.lean`).
These declarations have `M`, `L`, and branch-local `A` from the supplied
rectangle, but no `C`: they do not produce the rectangle, renew a row, or
consume a returned branch.  The separate exact regression in
`UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourMaximalRootNegativeOrientation.lean`
shows that a positive displayed signed atom can coexist with zero opponent
incidence and an exact all-Continue root.  It does not assert uniqueness of
that root or furnish a hard-residual source.

The same supplied rectangle now has a four-profile descendant-slice landing.
The generic compact-orbit theorem
`QuittingFourProfileResponseFamily.exists_minimum_normalizedDescendantSlice_eq_or_strict_inert`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFourProfileDescendantSlice.lean`)
retains two independent debt-relative passports: the response/sibling signed
atom and the source/full-replacement actual payoff gain.  Exact cap--Nash
prefix closure makes all Continue the unique exact root at a positive-debt
slice minimizer.  The Fin4 adapter
`QuittingStoppingLawRectangleJointAtomLimit.exists_fourProfileDescendantSliceLanding`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourProfileDescendantSliceLanding.lean`)
selects one common compact subsequence and positive densities.  Its point
either has minimum debt, positive opponent incidence, and a reset-rigid
chamber, or lies strictly off the minimum fibre; zero observer debt and both
positive passport bounds survive in either arm.  The generic layer has `M`
and `L`; the literal rectangle attachment adds branch-local `A`, but no `C`.
Closure gives no finite ancestry code, marked date, stopping law, chronology,
renewal, arm consumer, or uniform-equilibrium payoff.

The same actual forced-pair provenance collapses the normalized passport to
one density.  In
`Research/Quitting/FinFourProducerAtlas/NormalizedInertSingleDensityToll.lean`,
`FinFourNormalizedReturnSelection.carrier_actualGain_eq_gap_mul_markedMass`
proves on the complete closed prefix carrier that actual gain is the fixed
positive pair gap times marked mass.  The generic declarations
`QuittingSingleDensityPassportMinimizer.prefixMap_mem_slice_iff`,
`QuittingSingleDensityPassportMinimizer.rootDefect_ge_min_tent`, and
`QuittingSingleDensityPassportMinimizer.saturation_ratio`
(`Research/Quitting/NormalizedPassportSingleDensityToll.lean`) give the exact
one-density prefix-feasibility criterion, the arbitrary-root tent bound, and
the saturated mass/gain/debt ratios.

The density-to-zero construction in
`Research/Quitting/NormalizedPassportVanishingDensityBoundary.lean` selects
all slice minimizers, one compact subsequence, and one limit internally.
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_normalizedInertVanishingDensityBoundary`
(`Research/Quitting/FinFourProducerAtlas/NormalizedInertVanishingDensityBoundary.lean`)
attaches that construction to the actual Fin4 packet.
`FinFourNormalizedInertVanishingDensityBoundary.outcome` then returns one of
the displayed arms: minimum debt with an internally constructed
positive-density actualizer, zero limiting marked mass and gain, or one fixed
limit satisfying
`D(limit) * Abs(root) <= rootDefect` for every product root.  The limit is
chosen before the root quantifier.  Deterministic Continue trembles make every
finite approximating root have positive joint Continue mass and extend the
same limit-debt coefficient to full-absorption roots by continuity.

This boundary has `M`, `L`, and `A`.  Its positive minimum-return arm has `C`
through the existing actualizer and endpoint-law consumer; the zero-passport
and fixed-cap barrier arms have no `C`.  The scalar construction in
`Research/Quitting/NormalizedPassportZenoBoundary.lean` realizes the prefix
and composed-defect ledgers, unique zero-absorption root, and saturated
half-density step at every finite rank while remaining strictly above its
named tail debt.  It is not a quitting game.  The conditional theorem
`Math.RenewableNormalizedPassportDensity.rank_lt_of_density_le_half` gives a
strict natural-rank decrease only from a supplied renewable absolute density
floor.  No Fin4 theorem supplies that floor or a source-faithful regenerated
source.  The barrier gives no base-cluster return, chronology return, terminal
approximation, recursive closure, or uniform-equilibrium payoff.

Off-minimum carrier points are now actualized without pretending that they
return to the minimum fibre.
`nonempty_quittingMarkedPairCarrierActualizer`
(`Research/Quitting/NormalizedPassportCarrierActualizer.lean`) takes a
positive normalized carrier point whose whole debt is at least the positive
reference debt and selects literal raw descendants with fixed mass and actual
gain floors equal to half the corresponding reference-based density floors.
`QuittingMarkedPairCarrierActualizer.toDecoratedFamily` reassembles those rows
as an executable decorated family, and
`toDecoratedFamily_baseDecoration_tendsto` retains convergence of the complete
raw decoration.  This has `M`, `L`, and `A` relative to the supplied decorated
family and carrier point, but no `C`.  The origin ranks are not proved fixed or
cofinal, and the incoming absolute resolution need not survive.

For any literal finite product-root word,
`quittingTerminalSemanticDebtSum_literalRootStack_eq_weightedLedger_add`
(`Research/Quitting/FiniteWordWeightedCapDefectLedger.lean`) is the exact
chronological telescope: whole debt is the survival-transported suffix debt
plus the prefix-survival-weighted sum of complete-suffix product-root Nash
defects.  `half_minimum_le_weightedLedger_of_prefixSurvival_le` gives the
half-minimum aggregate lower bound from bounded suffix debt and sufficiently
small joint prefix survival, while
`nonempty_reachedPositiveCapDefect_of_prefixSurvival_le` selects an actually
reached row and `exists_positiveCoordinateNashDefect` selects a positive
coordinate there.  These ledger declarations have `M` and `L`, but no
source-facing screening adapter or downstream `A` or `C`.  The selected
coordinate is not a prescribed action, paid edge, executable chronology, or
return consumer; the charge may diffuse over arbitrarily many rows.

The zero-mass boundary now has an actual raw-row interface.
`FinFourNormalizedInertVanishingDensityBoundary.nonempty_actualZenoDeletedSurvivalSource`
(`Research/Quitting/FinFourProducerAtlas/ActualZenoDeletedSurvivalSource.lean`)
selects literal arbitrary-prefix descendants from the same normalized-return
family.  It retains packet and source ranks, both source and target siblings,
the fixed pair and marked owner, the complete postmark reference spine, whole
and tail convergence, and marked mass tending to zero.  The generic identity
`quittingCombinedPremarkWord_opponentSurvival_eq`
(`Research/Quitting/CombinedDeletedSurvivalWord.lean`) factors each combined
deleted clock into the arbitrary new word and immutable base chronology.
`FinFourActualZenoDeletedSurvivalSource.rho_lt_baseOpponentSurvival` gives the
literal base factor floor.  Therefore `newWord_fullyScreened` and
`eventually_newWord_opponentSurvival_lt` transfer a supplied combined
full-screening certificate to eventual uniform low deleted survival of the
new words.

The full source-level split is now literal.
`FinFourActualZenoDeletedSurvivalSource.nonempty_positiveHost_or_fullyScreened`
(`Research/Quitting/FinFourProducerAtlas/ActualZenoHostCompression.lean`)
either selects one fixed host and positive deleted-survival floor on a strict
subsequence, with every other deleted clock tending to zero, or returns full
screening.  In the positive branch,
`FinFourActualZenoPositiveHost.nonempty_fixedEndpoint` freezes the best Boolean
endpoint and routed terminal.  The accessors
`FinFourActualZenoPositiveHost.FixedEndpoint.eta_le_markedMass`,
`markedHostDefect_eq_zero`, `profile_opponent_eq`, and
`postMarkSpine_eq_reference` retain the full host floor, exact zero marked-host
root defect, unchanged nonhost behaviors, and complete postmark behavioral
tail.  The original Zeno, packet, and source ranks remain explicit.

`FinFourActualZenoDeletedSurvivalSource.nonempty_fullyScreenedClearingFamily`
(`Research/Quitting/FinFourProducerAtlas/FullyScreenedFiniteClockClearing.lean`)
then clears every retained actual new word after one strict finite shift.  At
most four iterative edges are paid, each by at least `gamma / 2`; the exact
mover-debt subtraction and marked-mass/historical-gain scaling are retained in
the typed paid ledger.  A host leaf reuses the old forced pair.  A nonsingleton
premark leaf keeps its literal profitable profile, mover, and coalition; only
a singleton leaf uses the outsider endpoint-routing adapter.  Every leaf has
resolution `rho * gamma / (128 * R)`, a distinct terminal member, and a
literal `FullyScreenedClearingPacketResult.consumerResult` in the existing
strategic-singleton-or-collision-minimum compiler.
`FullyScreenedClearingFamily.nonempty_fixedMechanismSubsequence` fixes the
ordered paid labels, exit kind, packet labels, and original premark labels on
one strict refinement while leaving dates and profiles free to vary.

The original screened siblings now also retain their complete source-indexed
semantic comparison.  In
`Research/Quitting/FinFourProducerAtlas/ActualZenoFullyScreenedSiblingCoalescence.lean`,
`abs_sibling_terminalPayoff_sub_le` bounds prescribed-payoff differences by
twice the reward bound times the common-word joint survival,
`abs_sibling_bestResponseValue_sub_le` bounds unrestricted behavioral-cap
differences by twice the reward bound times the corresponding deleted clock,
and `abs_sibling_terminalOutcomeMass_sub_le` bounds every complete outcome-law
coordinate, including `Never`, by the joint survival.  Full screening sends
all three bounds to zero.  The branch-local package
`FinFourActualZenoDeletedSurvivalSource.FullyScreenedCoalescingClearingFamily.semanticLaw_coalescence`
keeps that screening proof and the finite-clearing family on the same actual
Zeno source.

The zero-boundary capstone
`FinFourNormalizedInertVanishingDensityBoundary.nonempty_actualZeno_fixedEndpoint_or_coalescingClearingFamily`
constructs the actual Zeno source and returns exactly the fixed endpoint or
the same-source screened coalescence-and-clearing package.  This contraction
has `M`, `L`, and `A` in both arms.  Only the fully screened clearing branch
has `C`, through the strategic-singleton-or-collision-minimum contraction,
and both consumer outputs remain open.  The positive-host endpoint has no
checked downstream consumer and is not asserted whole-profile near-minimal,
cross-cap coherent, or cap controlled in the other coordinates.

The explicit `H_i = n^-3` zero-minimum boundary regression remains unchecked.
There is no return, regeneration, renewable compression, recursive descent,
terminal approximation, or uniform-equilibrium conclusion.

A separate canonical maximal-prefix ray now consumes the same cofinal
forced-pair source.  The cap-indexed selector `quittingMaximalAbsorptionCapRoot`
and the autonomous orbit in
`Research/Quitting/MaximalCapSemanticPrefixOrbit.lean` make the selected root
word depend only on the current terminal-semantic cap.  The pure-pair base is
fully independent of its counterfactual tail:
`quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
(`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`) gives the exact semantic
pair, and
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.rayBaseOutcomeLaw_eq_pure`
(`Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`) gives
the complete terminal law as the point mass at the fixed pair.  Every debt
coordinate, normalized positive-debt support, shifted marked mass, and copied
outer-word payer gain is transported by the same positive survival factor.

The scalar strict-arm account is exact.
`QuittingMaximalCapSemanticPrefixRayStall.weightedAbsorption_hasSum`,
`QuittingMaximalCapSemanticPrefixRayStall.absorption_tsum_le_exact_debtDrop`,
`QuittingMaximalCapSemanticPrefixRayStall.absorptionTailSum_tendsto_zero`, and
`QuittingMaximalCapSemanticPrefixRayStall.absorptionTailSup_tendsto_zero`
(`Research/Quitting/MaximalCapSemanticPrefixReturn.lean`) give the weighted
debt telescope, the unweighted absorption budget, and vanishing future charge
for that unchanged canonical ray.  For every strictly increasing convergent
joint semantic/law subsequence,
`quittingMaximalCapSemanticPrefixLawPoint_cluster_facts` proves at the same
cluster that debt equals the ray limit `L`, the pair-law mass is at least
`L / D_0`, all Continue is exact cap--Nash, and either it is the unique exact
root or another exact root has positive absorption.

The actual Fin4 capstone
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_maximalPrefixRayMinimumReturn_or_stall`
(`Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`) has
`M`, `L`, and `A` in both arms.  If `L = D_*`, it constructs the moving
reprojection packet at resolution `D_* / D_0` and has `C` through the existing
eventual transfer and fixed-role limit-chord consumers.  If `L > D_*`, it
stores the exact quantitative stall and the same sharp retained-law object,
but has no completion `C`.  This strict branch neither recomputes the ray
after a horizontal endpoint change nor gives support descent, source
regeneration, recursive return, terminal approximation, a uniform-equilibrium
payoff, or a counterexample.

The strict ray's stopping clocks now have a literal source-facing boundary in
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_finFourMaximalPrefixRayClockEscape`
(`Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayClockEscape.lean`).
Every fixed marginal finite head vanishes.  Each member of the retained pair
has zero `Never` mass, late finite mass tending to one, general total
variation tending to one from every fixed stopping law, and no cofinal
general-total-variation convergent subsequence.  Its shifted pair atom has
limiting mass `L / D_0`, bounded below by `D_* / D_0` and lying in `(0,1]`.
The generic fixed-tail and reverse-prefix theorems have `M` and `L`.  This
Fin4 declaration is a Research adapter conditional on the already supplied
producer, forced-pair packet, and strict-stall branch: it adds no unconditional
source `A` and has no downstream `C`.  It proves no convergence in a weaker
topology, compactness failure for another strategy model, terminal
approximation, or uniform-equilibrium conclusion.

The strict arm now has a further actual source split in
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.eventualAllContinue_or_nonempty_strictRayForwardExactCapTail`
(`Research/Quitting/FinFourProducerAtlas/StrictRayTailNormalizedCapFlow.lean`).
A zero selected maximal root is literally all Continue, fixes the autonomous
semantic orbit from that date onward, and is the unique exact root at the
fixed cap.  Otherwise the selected roots form an actual positive-hazard
`QuittingForwardExactCapTail` (`Research/Quitting/ForwardExactCapTailFlow.lean`)
with the same packet source and ray.  Its limiting cap, singleton lower bound,
summable total hazard, exact `QuittingForwardExactCapTail.tailAverage_renewal`,
and eventual binding-support theorem
`QuittingForwardExactCapTail.eventually_currentHazard_supported_binding` are
source-derived.  This layer has `M`, `L`, and `A`, but no `C`.

The all-Continue arm now has a literal finite-clock normal form in
`Research/Quitting/FinFourProducerAtlas/EventualAllContinueStallNormalForm.lean`.
[`FinFourMaximalRayEventualAllContinue.fixedProfile_semantic_eq`](../Research/Quitting/FinFourProducerAtlas/EventualAllContinueStallNormalForm.lean)
retains one actual profile realizing the fixed semantic state, and
[`FinFourMaximalRayEventualAllContinue.exists_fixedProfile_capAttainer`](../Research/Quitting/FinFourProducerAtlas/EventualAllContinueStallNormalForm.lean)
attains every unrestricted behavioral cap at Never or at one finite pure
quitting date.  The generic opponent-barrier theorem gives the stronger
attainment statement at every displayed ray row.
[`FinFourMaximalRayEventualAllContinue.fixedProfile_debt_eq_rayLimit`](../Research/Quitting/FinFourProducerAtlas/EventualAllContinueStallNormalForm.lean)
identifies the fixed debt with `L`, while
[`FinFourMaximalRayEventualAllContinue.fixedProfile_endpoint_debt_eq_sub_add_spectatorLeakage`](../Research/Quitting/FinFourProducerAtlas/EventualAllContinueStallNormalForm.lean)
localizes the paid endpoint obstruction in the signed spectator leakage.
Global minimum gives the exact lower bound in
[`FinFourMaximalRayEventualAllContinue.rayPaidGain_sub_fixedExcess_le_spectatorLeakage`](../Research/Quitting/FinFourProducerAtlas/EventualAllContinueStallNormalForm.lean),
not the upper bound needed for descent.  The endpoint returns to the minimum
fibre only under that separately supplied upper threshold.  This normal form
has `M`, `L`, and `A`, but no `C`; it supplies no leakage orientation,
chronological return, source regeneration, or contradiction.  The packet's
specific rational local-stall regression is checked separately in
`Research/Quitting/FinFourEventualAllContinueLocalRegression.lean`.
[`FinFourEventualAllContinueLocalRegression.pair_semantic_eq`](../Research/Quitting/FinFourEventualAllContinueLocalRegression.lean)
gives exactly `U = (1,4,1,2)` and `B = (3,4,2,2)` with the unrestricted
behavioral cap.  The same table has the paired normalized singleton matrix,
full normal core, `ResidualHardClass`, punishment normality, uniform
full-support singleton mass `1/4`, zero-debt owner `1`, and unit-gain payer
`2`.  The declarations
[`FinFourEventualAllContinueLocalRegression.exactRoot_eq_allContinue`](../Research/Quitting/FinFourEventualAllContinueLocalRegression.lean)
and
[`FinFourEventualAllContinueLocalRegression.maximalPrefixOrbit_pairSemantic_eq`](../Research/Quitting/FinFourEventualAllContinueLocalRegression.lean)
prove the unique exact cap root and immediate constant semantic orbit.
[`FinFourEventualAllContinueLocalRegression.neverPair_globalMinimum`](../Research/Quitting/FinFourEventualAllContinueLocalRegression.lean)
and
[`FinFourEventualAllContinueLocalRegression.neverUniformEquilibriumPayoff`](../Research/Quitting/FinFourEventualAllContinueLocalRegression.lean)
prove that its all-Never profile has global debt minimum zero and is an exact
uniform equilibrium.  Thus this regression has `M`, `L`, `A`, and `C` for its
own explicit table, but cannot supply positive-minimum strict-ray provenance.

`QuittingForwardExactCapTail.tailNormalizedCapFlow`
(`Research/Quitting/ForwardExactCapTailFirstOrder.lean`) now derives the
normalized certificate from the actual ray.  The one-step estimates in
`abs_quittingRootSuccessorPayoff_sub_tail_sub_normalizedSoloFlow_sub_baseline_le`
and
`abs_quittingRootEndpointDifference_sub_solo_sub_tail_sub_collisionFlow_le`
(`UniformEquilibrium/Quitting/Root/FirstOrderProductFlow.lean`) have exact
remainders `2 M epsilon^2` and
`epsilon |cap_i - singleton_i| + 4 M epsilon^2`.  The generic weighted-tail
average and forward-difference telescope are in
`MathUE/Analysis/SummableTailAverage.lean`.
`FinFourStrictRayForwardExactCapTail.analysis` supplies the nested `Analysis`
without an extra error hypothesis, so collision nonpositivity,
complementarity, and diffuse-solo identities now have `M`, `L`, and `A` on
the same source ray.  The normalized analysis itself has no terminal `C`, but
the positive limiting-root branch now has a checked return consumer in
`Research/Quitting/FinFourProducerAtlas/StrictRayPositiveRootReturn.lean`.
`FinFourStrictRayCapLimitJointLaw.nonempty` selects a joint-law cluster from
the same executable ray and proves its cap equals the stored `capLimit`.
`FinFourStrictRayPositiveRootReturn.returnedDebt_eq_limit_sub_charge` gives
the exact debt `L - L * absorption`, with the returned actual carrier point in
`[D_*, L)`.  The theorem
`FinFourStrictRayPositiveRootReturn.nonempty_minimumLawHandoff_or_offMinimumDescent`
either regenerates a fresh `FinFourMinimumAtomProducer` at that exact point
with the same hard residual or retains a strict off-minimum point below `L`.
This is branch-local `C`; the strict descent has no quantitative or renewable
consumer, and no strict-ray contradiction or uniform-equilibrium conclusion
follows.

The supplied full-binding case has a further actual compact reduction in
`Research/Quitting/FinFourProducerAtlas/StrictRayFullBindingDiffuseReduction.lean`.
`QuittingForwardExactCapTail.nonempty_compactHazardCluster` jointly extracts
the current marginal-hazard direction, remaining-tail hazard barycenter, and
renewal ratio along one strict subsequence of the same forward ray.
`FinFourMinimumAtomProducer.not_hasHomogeneous_fullNormalizedSoloMatrix`
transports the hard residual through the literal full-core reindexing.  Hence,
under the explicit hypothesis `flow.forward.bindingFinset = Finset.univ`,
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_compactCluster_ratioLimit_pos_or_currentSupport_card_le_three`
returns one same-flow cluster whose renewal-ratio limit is positive or whose
current-limit positive support is nonempty and has cardinality at most three.
This has `M`, `L`, and `A` relative to the actual source-retaining flow, but no
`C`.  It does not derive full binding, consume either surviving branch, give a
return or rank drop, contradict the strict ray, or produce a uniform-equilibrium
payoff.

Exact finite support now sharpens that compact reduction.  In
`Research/Quitting/FinFourProducerAtlas/FullBindingPointwiseSupportBallistic.lean`,
`compactCluster_ratioLimit_pos_of_eventually_all_currentHazard_pos` is
universal over every compact cluster of the same actual strict ray.  Under
full binding, eventual positivity of all four finite current coordinates
along that cluster forces its renewal-ratio limit to be positive, even when
the limiting current direction has zero coordinates.  The source theorem
`eventually_renewalRatio_ge_pos_of_fullBinding_of_eventually_all_currentHazard_pos`
upgrades eventual finite full support to one `eta > 0` that eventually bounds
the actual renewal ratios below.  The exhaustive
`eventually_renewalRatio_ge_pos_or_exists_frequently_currentHazard_eq_zero`
returns uniformly ballistic renewal or one fixed player whose current hazard
is zero infinitely often.  These results have `M`, `L`, and `A` relative to
the actual source-retaining flow, but no `C`.  Full binding and eventual full
support are not produced, and neither the ballistic nor omitted-player branch
has a checked return, rank decrease, contradiction, or uniform-equilibrium
consumer.

The uniformly ballistic branch now has an exact source-compatible omega
chain.  `Math.Topology.nonempty_sourceOmegaChain` and
`Math.Topology.SourceOmegaChain.sourceFiniteWindow_tendsto`
(`MathUE/Topology/SourceOmegaChain.lean`) extract one bi-infinite compact path
using a common strict center subsequence and retain convergence of complete
consecutive finite source windows.  In
`Research/Quitting/FinFourProducerAtlas/BallisticNormalizedOmegaChain.lean`,
`nonempty_ballisticNormalizedOmegaChain_of_fullBinding_of_eventually_all_currentHazard_pos`
applies that extraction to the same actual strict Fin4 ray.  The resulting
`source_current_tendsto`, `source_tail_tendsto`, `source_ratio_tendsto`,
`renewal`, `work_nonpos`, and `current_work_eq_zero` declarations retain
strict actual dates and the exact renewal, collision-feasibility, and
complementarity identities at every integer node.

The nonnegative half of this chain also has a balanced occupation law.
`FinFourBallisticNormalizedOmegaChain.nonempty_normalizedOccupation`
(`Research/Quitting/FinFourProducerAtlas/BallisticNormalizedOccupation.lean`)
constructs an empirical edge limit; its `marginals_eq` and
`support_subset_ballisticEdgeGraph` give equal state marginals and support on
the exact closed normalized relation.  This chain and occupation have `M`,
`L`, and `A` under the explicit full-binding and eventual finite-support
hypotheses, but no `C`: they contain no absolute product root, payoff vector,
stationary realization, periodic Bellman seam, terminal approximation, or
uniform-equilibrium conclusion.

This lack of a consumer is substantive rather than merely topological.
`BallisticNormalizedSelectedChainRegression.stateAt_edge`,
`stateAt_current_ge_one_eighth`, and `stateAt_not_periodic`
(`Research/Quitting/BallisticNormalizedSelectedChainRegression.lean`) give a
rational-matrix normalized orbit with renewal ratio `1 / 2`, every current
coordinate at least `1 / 8`, and no positive period at any starting index.
`fixedState_edge` simultaneously exhibits a stationary fixed point elsewhere
in the same relation, while `soloMatrix_normalCore_eq_univ`,
`soloMatrix_noHomogeneous`, `soloMatrix_standardQ`, and
`soloMatrix_not_projectiveQBar` retain the full paired-singleton hard class.
The regression has `M` and `L` only: it refutes periodicity of the selected
normalized chain, not existence of another periodic normalized state, and it
is not an actual quitting ray or a positive-minimum source.

The corresponding source-free branch exclusions are false at zero global
minimum debt.  `rationalCardThree` and `fullBindingBallistic`
(`Research/Quitting/FinFourMaximalRayZeroMinimumRegressions.lean`) are two
fully constructed Fin4 tables with actual canonical maximal-prefix rays.  In
the first, the limiting binding set has cardinality three.  In the second,
all four coordinates bind, every current root is supported on the same three
players, and the exact renewal ratio tends to `1 / 2`.  The literal
`LocalForcedPairFragment` is attached to the ray by
`Regression.pair_zero_eq_fragment`; its named accessors retain full mass, the
complete post-date behavioral spine, zero marked debt, and a distinct positive
payer debt.  The selected roots tend to all Continue, whereas the stored
positive root is only an exact root at the same limiting cap, not their limit.
These concrete regressions have `M`, `L`, and `A`, and a checked no-go `C`:
`Regression.neverPair_globalMinimum` gives global debt zero and
`Regression.not_nonempty_minimumAtomProducer` excludes every positive-minimum
source for the same table.  They also have genuine all-behavior equilibrium
consumers: `Regression.neverUniformEquilibriumPayoff` and the rational and
full-binding `...PureSingleton_uniformEquilibriumPayoff` declarations.  Thus
the constructions are boundary examples, not counterexamples or consumers of
the positive-minimum strict-ray branches.

An independent adjacent-deadline layer now isolates the exact finite-game
projective boundary.  The generic declarations
`Math.PMFProduct.pmfTV_pmfPi_le_sum`,
`abs_expect_pmfPi_sub_le_two_mul_sum_pmfTV`,
`pmfPi_map_coordwise_eq_of_maps_eq`, and
`expect_pmfPi_coordwise_eq_of_maps_eq`
(`MathUE/PMFProduct/TotalVariation.lean`) control finite independent products
and identify equality after coordinatewise operational observation.

In `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineAdjacentTotalVariation.lean`,
`QuittingFiniteDeadlineNashProfile.semanticDebt_eq_boundaryGain_pospart`
identifies the unrestricted behavioral debt of a finite-deadline Nash profile
with the positive part of its first excluded pure-time gain.  Literal timing
law inclusion preserves the realized behavioral profile and every old-action
gain, and `quittingFiniteDeadlineTiming_isNash_of_include_isNash` gives the
sound one-way projective implication.  For arbitrary consecutive exact timing
Nash laws,
`quittingFiniteDeadlineTimingProfile_semanticDebt_le_adjacentTV` proves
`d_i <= 4 R * sum_j TV`; the supplied-coordinate converse is
`quittingFiniteDeadlineAdjacentTV_ge_div_of_semanticDebt_ge`.
Operationally equal stopping-time marginals have exactly equal payoffs and
common-action gains, while a gain change only yields some changed observed
marginal through `exists_actionTime_map_ne_of_mixedGain_ne`.

The censor and compatibility layers now sharpen this boundary.  In
`UniformEquilibrium/Diagnostics/Quitting/CensoredFiniteClockOperationalEffect.lean`,
censoring is a
literal retraction and is nonexpansive in total variation;
`pmfTV_quittingFiniteDeadline_include_censor_eq_boundary` identifies its exact
erased boundary mass, and
`quittingFiniteDeadlineAdjacentTV_le_censorBudget` separates boundary
participation from old-clock reshuffling.  The generic
`finiteClockOperationalEffectDistance` is a pseudometric on `Never`, hard
payoff, and hard pure-action-gain observables.
`quittingFiniteRootWordOperationalObservables_mixedTiming_eq` and
`quittingFiniteRootWordOperationalEffectDistance_mixedTiming_eq` identify the
mixed-law gauge with the literal root-word gauge exactly.
`quittingFiniteDeadlineOperationalEffectDistance_zero_retainedTailSemantic_eq`
therefore preserves the complete terminal semantic pair behind every common
behavioral tail at zero mixed-law distance.

The independent adjacent-gap layer makes the finite source and its two local
dispatches literal.  `QuittingAdjacentDeadlineGapSource.of_terminalExploitabilityGap`
(`UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineGapSource.lean`)
attaches any supplied consecutive pair of exact timing Nash laws to the fixed
terminal gap, and `censoredError_or_boundaryParticipation` returns the exact
`gamma / (8 * R)` old-clock-error or new-boundary-participation split.
`quittingAdjacentDeadline_paidOwnEdge_or_paidResponseSquare`
(`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingHybridDispatch.lean`)
then gives either a literal behavioral own-coordinate payoff increase above
`3 * gamma / 4`, with unchanged unrestricted cap and exact debt subtraction,
or a common behavioral boundary-response square of size
`gamma / (4 * (card I - 1))`, hence `gamma / 12` in Fin4.  The square carries
no profitability claim for its mover.

The retained-tail reprojection layer now consumes the same supplied adjacent
source together with one supplied actual tail whose payoff is separated from
every own singleton reward.  The concrete timing laws, behavioral profiles,
and exact support/pass/reverse identities live in
`UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineRetainedTailReprojection.lean`.
In particular, `quittingAdjacentDeadlineOldBoundaryProfile_eq_update` and
`quittingAdjacentDeadlineCensoredGraft_eq_update_participant` expose literal
unilateral behavioral updates.
`quittingAdjacentDeadline_singletonSeparatedTail_dispatch`
(`UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineSingletonSeparatedTailDispatch.lean`)
returns exactly four arms: lossless zero-`Never` response, paid pass response,
paid reverse participant, or the unchanged raw censor-error lower bound.  The
reverse arm preserves the mover's unrestricted behavioral cap and subtracts
the exact payoff gain from its terminal-semantic debt.  In Fin4,
`quittingAdjacentDeadline_singletonSeparatedTail_dispatch_finFour` gives the
literal floor `147 * delta * (gamma / R)^2 / 16384`.

The selected-effect companion
`quittingAdjacentDeadline_operationalEffectDistance_ge_or_paidReverseParticipant_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineSelectedBoundaryEffectDispatch.lean`)
uses a smaller gauge consisting of every `Never` discrepancy and one
normalized observer boundary-gain discrepancy.  This selected gauge is
bounded by, but is not equal to, the full operational-effect distance.  The
Fin4 theorem returns either full operational effect at least
`gamma / (8 * R)` or a paid reverse participant with payoff floor
`27 * delta * (gamma / R)^4 / 4096`.  Under exact equality of the selected
coordinates,
`quittingAdjacentDeadline_paidReverseParticipant_finFour_of_selectedBoundaryCoordinates_eq`
strengthens that floor to `7 * delta * (gamma / R)^3 / 256`.

These compilers have `M/L` at their displayed supplied source and tail.  Their
`A` seal is incomplete: no theorem jointly selects a consecutive exact-Nash
source and a singleton-separated actual tail in the required source-facing
configuration.  The raw censor-error and large selected-effect arms remain
without a downstream `C`.  The compilers assert no minimum-fibre membership,
tail Nash property, chronology, return, renewal, rank, terminal approximation,
or uniform-equilibrium conclusion.

In the boundary-participation arm,
`QuittingFiniteDeadlineBoundaryResponseCollision.of_boundaryParticipation`
and `behavioralStagePairMass_ge_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineBoundaryResponseCollision.lean`)
produce a counterfactual actual behavioral pair-stage atom with floor
`gamma^3 / (32 * R^3)`.  `opponentNever_ge` retains the coordinatewise Never
floors used in that estimate.  This is not a prescribed-play collision and
does not assert that the forced response is profitable.

The sharp limitation is also now a checked concrete regression.
`FinFourCensoredClockNullDirection.regressionCertificate`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourCensoredClockNullDirection.lean`)
packages adjacent exact timing Nash laws with boundary participation `1/6`,
old boundary gain `(1-c)/2`, censored error `c`, canonical terminal-law
equality, zero operational distance, and equal terminal semantics behind every
common retained tail.  Its separate exact terminal Nash tail has singleton
gap one and `D_* = 0`, while
`FinFourCensoredClockNullDirection.exists_censoredError_div_boundaryScale_gt`
shows that the normalized censor ratio is unbounded.  Thus raw censored TV
cannot by itself price strategic effect; this zero-minimum example is neither
a positive-minimum source nor a uniform-equilibrium counterexample.

Separately, `exists_actualNearCarrierTail_of_uniformSingletonGap`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticActualNearCarrierTail.lean`)
selects an actual behavioral profile arbitrarily close in the complete
terminal-semantic pair to any carrier point whose prescribed coordinates are
uniformly separated from their singleton rewards.  It retains half the
singleton gap and an upper debt approximation, but neither identifies the
profile with the carrier point nor places it on a minimum fibre.

`QuittingFiniteDeadlineCompatibleNashFamily`
(`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineProjectiveCompatibility.lean`)
retains one
exact Nash law at every finite deadline and literal successor censoring.
`neverMass_succ_add_boundaryMass`, `boundaryMass_tendsto_zero`, and
`adjacentTV_eq_sum_boundaryMass` give the exact Never telescope and vanishing
adjacent distance.  More generally,
`exists_uniformEquilibriumPayoff_of_arbitrarilySmallAdjacentNashTV` turns
arbitrarily close actual consecutive Nash pairs directly into a uniform-
equilibrium payoff, and
`QuittingFiniteDeadlineCompatibleNashFamily.exists_uniformEquilibriumPayoff`
is the compatible-family specialization.

That specialization is sharpened from existence of some payoff to an
identified profile.
`QuittingFiniteDeadlineCompatibleNashFamily.isZeroAsymptoticNash_limitProfile`
(`UniformEquilibrium/Diagnostics/Quitting/ProjectiveTimingInverseLimit.lean`)
determines one
stopping law on the compactified times for each player whose deadline
truncations are exactly the supplied marginals, and proves the independent
product of those laws an exact terminal Nash profile against every unilateral
behavioral deviation, at error `0`.
`QuittingFiniteDeadlineCompatibleNashFamily.isUniformEquilibriumPayoff_limitProfile`
reads off its prescribed payoff.
`quittingGame_isUniformEquilibriumPayoff_of_adjacentTV_tendsto`
(`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineVanishingAdjacentDistance.lean`)
is the
matching consumer over an arbitrary index filter: consecutive deadline Nash
pairs whose adjacent distance tends to zero, with realized prescribed payoffs
tending to one target, make that target uniform.  Cofinality of the selected
deadlines is not required, because the estimate consumes the vanishing
terminal debt, not growth of the deadline.

These theorems have `M/L/C`, but no `A`: no compatible-family or
semialgebraic minimizer producer is checked.  They do not construct the
positive-minimum reprojection, paid edge/rectangle, or dispatch constants.

A separate generic timing-Nash screen is now integrated in
`UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingNash.lean`
and
`UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`.
For any supplied finite literal root stack satisfying the exact finite-stop
and pass-through timing Nash comparisons over one retained behavioral tail,
`IsQuittingRetainedTailFiniteTimingNash.debt_le_deletedReturn_mul_tailDebt`
transports unrestricted terminal debt by the player-deleted return.
`terminalGap_retainedTailFiniteTimingNash_jointReturn_ge` then combines one
gap-selected host, supplied coordinatewise punishments, and the exact product
inequality to force joint return at least
`gamma^2 / (2 * R * (gamma + 2 * R))`.  This rules out a screened block only
under those supplied hypotheses.

The generic near-minimum rigidity theorem is now sharper.  In
`Research/Quitting/NearMinimumRetainedTailTimingNashIdentity.lean`,
`nonidentity_exactRoot_uniformOpponentAbsorption_ge` gives every coordinate
the same opponent-absorption floor `kappa / (kappa + 2 * M)`, with no
cardinality averaging.  Under positive global minimum and actual tail excess
strictly below `kappa * D_* / (2 * M)`,
`nearMinimum_rootNashAgainstPayoff_eq_allContinue` forces every exact endpoint
Nash root against the tail's prescribed payoff to be all Continue.
`nearMinimum_literalExactRootStack_eq_replicate_allContinue` propagates this
identity backward through a supplied exact credible-suffix root stack.

The actual mixed-law realization is checked in
`UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingRealization.lean`.
`quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff` keeps the fixed
behavioral tail literal in the finite normal form.
`retainedTimingLawTail_isNash_of_isNash_of_positiveContinue` transfers Nash
optimality to every conditioned suffix, while
`retainedTimingCurrentRoot_isZeroEndpointNash_of_isNash` exposes the exact
current endpoint root.  The realization additionally proves literal hard
profile reconstruction, exact retained-graft payoff, finite-date and pass
compatibility, and
`isQuittingRetainedTailFiniteTimingNash_of_mixedNash` without a positivity
hypothesis; positive `Never` mass is used only by
`isQuittingLiteralExactRootStack_of_retainedTailMixedNash` to retain credible
conditional suffixes.  Consequently
`nearMinimum_retainedTailFiniteTimingNash_eq_pureNeverProfile` proves that any
near-minimum mixed Nash law with positive `Never` mass in every marginal is
literally pure `Never`.  This complete generic identity compiler has `M/L`
status.  There is still no Fin4 adapter from the actual minimum source to a
separated tail and coordinate punishments, no theorem turning every selected
mixed Nash law into the retained-tail return-floor certificate and positive
joint `Never` mass, and no eventual source-level identity theorem.  Hence
there is no Fin4 `A/C`; payoff return, cap Nash, recurrence, and uniform
equilibrium remain open.

The strict-ray binding-pair exclusion is now source-attached and
certificate-free.  `quittingEndpointNashBoxBridge`
(`Research/Quitting/Root/EndpointNashBoxComplementarity.lean`) constructs the
canonical Boolean-PMF box bridge at every finite cap, and
`QuittingEndpointNashBoxBridge.isSolution_iff_isZeroQuittingRootNash`
identifies its solutions with exact product-root Nash.  The low reindexing
owners are `MathUE/PMFProduct/Reindex.lean` and
`UniformEquilibrium/Quitting/Root/PlayerReindex.lean`.

Under limiting all-Continue uniqueness on one actual strict flow,
`FinFourStrictRayForwardExactCapTail.bindingFinset_card_ne_two`
(`Research/Quitting/FinFourProducerAtlas/StrictRayBindingCardinalityExplicit.lean`)
selects the late finite cap and common resolution internally.  It normalizes
the binding pair, uses selected-root maximality and cap convergence to
localize every exact root, derives the outsider and collision signs, and
combines the both-active count-two and solo count-zero formulas with eventual
same-grid parity one.  No `ModTwoBoxComplementarityParitySpec`, finite-cap
certificate, or pinned GameTheory Sperner substitute is assumed.  The
source-facing capstone first returns a positive limiting root when uniqueness
fails and otherwise applies this exclusion.  Thus
`positiveAbsorptionExactRoot_at_capLimit_or_bindingFinset_eq_univ_or_card_eq_three`
has `M`, `L`, and `A` on the same actual flow.

The source consumer
`minimumLawHandoff_or_offMinimumDescent_or_ballistic_or_omitted_or_cardThree`
now takes only that flow.  It consumes the positive-root arm into exact
same-residual minimum regeneration or strict off-minimum descent, and the
full-binding arm into uniformly ballistic renewal or one fixed player omitted
infinitely often.  This gives branch-local `C`, while making binding
cardinality three literal.  The returned minimum/descent, ballistic,
omitted-player, and cardinal-three endpoints remain open; no strict-ray
contradiction or uniform-equilibrium conclusion follows.  The older abstract
parity contract remains a checked conditional interface, but it is no longer
an input to the actual-flow consumer.

The generic Sperner approximation and local-count seam is checked in
`Research/Topology/BoxComplementarityCubicalSperner.lean`,
`Research/Topology/BoxComplementaritySpernerApproximation.lean`, and
`Research/Topology/BoxComplementaritySpernerLocalCount.lean`; the concrete
same-grid prism layer is in
`Research/Topology/BoxComplementaritySpernerSubdivisionPrism.lean`.
`boxComplementarity_completeSimplex_card_odd` specializes the pinned strong
cubical Sperner theorem to the reduced box-complementarity labeling at every
positive resolution.  The selected anchor and coordinate-label vertices lie
within one mesh width, and
`BoxComplementarityProblem.isSolution_of_completeSimplexAnchorPoint_tendsto`
turns every convergent vanishing-mesh anchor sequence into an exact solution,
including in dimension zero.  The compact form
`BoxComplementarityProblem.eventually_no_completeSimplexVertexIn_of_compact`
uniformly excludes all vertices of every sufficiently fine complete simplex
from a compact set disjoint from the solution set.
`boxComplementarityLocalCompleteSimplexParity_univ` defines the finite-mesh
local count and proves its global value is one, while
`boxComplementarityLocalCompleteSimplexParity_union_of_disjoint` gives literal
finite-mesh excision.  For every isolating open set,
`BoxComplementarityProblem.exists_isolatingFrontierCollar_eventually_parity_zero`
constructs a positive compact closed frontier collar whose local count is zero
at every sufficiently fine mesh.  The new concrete layer constructs the
ordered-Kuhn cells, externally complete faces, and actual incidence relation.
`KuhnPrismSpatialBoundaryLabeling.leftEndParity_eq_rightEndParity` proves
lateral cancellation and equality of the two end parities, while
`boxComplementarityDiscretePrism_endpointParity_eq` identifies those ends
with the pinned complete-simplex counts of the first and last problems in one
same-resolution family.  The elementary theorem
`kuhnStarSubdivision_completeFacetParity_eq` proves that starring one labeled
simplex preserves its complete-facet count modulo two.  This intermediate seam
has `M` and `L` only.  It does not construct a geometric finite stellar chain
between distinct pinned Kuhn resolutions, transport local anchors or a cleared
collar through such a chain, prove eventual local-parity stability, supply a
regularity bridge or the open parity specification, build a Fin4 finite-cap
certificate, or provide `A` or `C`.

The canonical pair's literal paid endpoint starts with the checked
support-rank handoff supplied by the generic theorem
`exists_minimumEndpointSupportRankHandoff_or_debtAscent`
(`Research/Quitting/StoppingLawMinimumEndpointSupportRankHandoff.lean`)
jointly compactifies the source, endpoint, and their literal half stopping-law
mixture.  At a minimum endpoint the half cluster has coordinate debt equal to
the source/endpoint average and positive-debt support equal to their union.
The payer has positive source debt and zero endpoint debt, so the endpoint
support is a strict subset of the new half parent; the existing tangent-family
extractor and minimum-fibre re-extractor consume this as the first
support-rank handoff.  If the endpoint is not minimal, the same theorem keeps
the strict endpoint-debt ascent instead.

The actual source adapter
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_canonicalPairMinimumEndpointSupportRankHandoff_or_debtAscent_or_rayStall`
(`Research/Quitting/FinFourProducerAtlas/CanonicalPairMinimumEndpointSupportRankHandoff.lean`)
retains the incoming forced-pair source and scalar-ray return or stall.
`rayProfile_payerDebt_eq_rayPaidGain` identifies the copied endpoint gain with
the source payer's whole unrestricted debt, while
`rayPaidTargetProfile_payerDebt_eq_zero` kills that debt at the literal
endpoint.  `exists_canonicalPairEndpointConcentratedPacket_refining` freezes
the finite action/routed label on a refinement of the generic joint-cluster
subsequence, not an unrelated extraction.  The stored composition equality
and endpoint/source convergence accessors retain the same joint clusters;
`CanonicalPairMinimumEndpointSupportRankHandoff.endpointPacket_half_tendsto`
retains the same half cluster, and the named total-debt limits retain either
`D_*` or the strict endpoint value.

The minimum-fibre handoff is now renewable.  In
`Research/Quitting/FinFourProducerAtlas/CanonicalPairEndpointSourceRegeneration.lean`,
`CanonicalPairMinimumEndpointSupportRankHandoff.nonempty_endpointSourceRegeneration`
rebuilds a complete minimum source from the handoff's literal endpoint
profiles and dates.  In
`Research/Quitting/FinFourProducerAtlas/CanonicalPairFullReplacementSourceRegeneration.lean`,
every recursive minimum-fibre endpoint is compactified on the current node's
literal full-replacement profiles, causalized into its own complete source
with the same hard residual, and attached to a tangent family whose
positive-debt support is a strict subset of its parent's support.

`FinFourRenewableMinimumSourceNode.terminalExit_or_nonempty_supportDescent`
(`Research/Quitting/FinFourProducerAtlas/RenewableSourceTrace.lean`)
is the exhaustive one-step dispatch.  Only its minimum-fibre output is
recursive; positive total slope, flat support entry, and an off-minimum paid
first-disagreement endpoint are explicit residual exits.
`canonicalPairRenewableRank` is zero at the residual state, one plus support
cardinality at tangent nodes, and six at the nonrecurring incoming state.
`canonicalPairRenewableTransitionRel_wellFounded` proves the resulting
relation well founded, `FinFourRenewableTrace.descentCount_le_three` gives at
most three recursive node-to-node edges, and
`exists_renewalTerminalExit_sameResidual` retains the incoming hard residual
at the final structural exit.  Thus the fresh half-parent comparison remains
distinct from the old source support, but it no longer terminates the
minimum-fibre branch after one use.

This canonical minimum-endpoint reduction has `M`, `L`, `A`, and branch-local
`C` through `consume_renewalTerminalExit`.  It supersedes the former one-time
handoff boundary only on this actual canonical branch.  The off-minimum
endpoint and inherited strict ray stall still have no terminal consumer, and
positive slope, support entry, and the paid off-minimum exit remain downstream
obligations.  No backward response compiler, terminal approximation,
unconditional uniform-equilibrium payoff, or counterexample follows.

That fibre also carries an exact debt ledger whose consequence is negative.
At a full-replacement endpoint cluster on the minimum total-debt fibre the
active mover's debt is zero at the cluster and positive at the base while
total debt is preserved, so
`QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster.minimumFiber_debtTransfer`
(`Research/Quitting/MinimumFiberDebtTransfer.lean`) makes the aggregate debt
change over the other players exactly the mover's base debt, and
`exists_nonmover_debtChange_moverDebt_div_card_le` selects one nonmover
absorbing at least a `Fintype.card ι - 1`-th part of it.  Hence
`not_forall_debt_le_base`: coordinatewise debt nonincrease across such a seam
is impossible.  `moverDebt_le_sum_positivePart_nonmover_debtChange` bounds the
total positive part of that change below by the mover's base debt, so the
transfer is not uniformly small either, and any backward compiler through this
seam has to carry, cancel, or pay it.  In Fin4,
`FinFourRenewableSupportDescent.exists_nonmover_debtChange_moverDebt_div_three_le`
makes the sharp one-third share literal at every recursive edge, while
`CanonicalPairMinimumEndpointSupportRankHandoff.exists_other_endpointDebtIncrease_div_three`
does the same at the incoming canonical endpoint.
`abs_quittingTerminalSemanticDebt_sub_le_of_forall_deviationGain_abs_le`
turns a uniform full-behavior deviation-gain comparison into a debt-coordinate
comparison.  Source and full-replacement convergence therefore make
`FullReplacementCluster.not_hasVanishingHorizontalDeviationLeak_of_minimumFiber`
a literal no-go: one vanishing error cannot compare every nonmover behavioral
deviation gain across the seam.  The account uses neither flatness of the
tangent column nor absence of entry into the inactive debt support.  Debt is
the gap between the best-response envelope and the prescribed payoff, so this
still bounds no envelope or prescribed-payoff coordinate on its own: raw cap
vectors at the base and cluster are not asserted close or far apart.

The strict endpoint alternative is now normalized without losing that joint
cluster.  In
`Research/Quitting/FinFourProducerAtlas/StrictEndpointNormalizedReturn.lean`,
`CanonicalPairMinimumEndpointDebtAscent.endpointRows` uses the concentrated
endpoint packet's already aligned action, routed terminal, and subsequence
directly.  `FinFourCanonicalPaidEndpointRows.exists_origin_refining` selects
only a further strict subsequence.  The constructor
`CanonicalPairMinimumEndpointDebtAscent.nonempty_strictEndpointOrigin` uses
`FinFourCanonicalPaidEndpointOrigin.wholeSemantic_tendsto` and uniqueness of
limits to prove that the decorated whole limit is exactly the generic
debt-ascent endpoint cluster.  Thus the positive strict gap is source data,
not a comparison between unrelated existential cluster points.

`CanonicalPairMinimumEndpointDebtAscent.nonempty_strictNormalizedReturnOrInert`
then applies the checked normalized-passport minimizer to this coherent
origin.  If its normalized minimum returns to `D_*`, the actualizer supplies
the maintained source-attached strategic-singleton or collision-minimum
residual; in the nonsingleton routed case the stronger three-role endpoint-law
classifier remains available.  If the minimum stays strict, the same
normalized point retains all Continue as its unique exact cap--Nash root.
The headline theorem
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_canonicalPairSupportHandoff_or_strictNormalized_or_rayStall`
is now the literal three-way source interface: minimum-endpoint support
handoff, coherent strict normalized result, or unchanged scalar-ray stall.

This strict-endpoint reduction has `M`, `L`, and `A`.  The normalized equality
arm has `C` to the existing strategic/collision residual, while the
support-handoff arm now feeds the renewable finite-rank reduction above.  The
normalized inert point and ray stall have no `C`.  No copied sibling is
claimed cap--Nash, and there is no terminal approximation, global completion,
unconditional uniform-equilibrium payoff, or counterexample.

There is also an exact screen on one proposed way of changing that unchanged
canonical ray.  `quittingTerminalSemanticPair_literalRootStack_pureSet_screen`
(`UniformEquilibrium/Quitting/Paths/PureNonsingletonCommonPrefixScreening.lean`)
shows that two arbitrary behavioral tails behind the same pure coalition of
cardinality at least two and the same finite literal root word have identical
prescribed payoff and unrestricted behavioral cap.  The named coordinate and
total-debt corollaries give equality and literal zero change, without any
stationarity, finite-support, or cap-attainment hypothesis.

The actual Fin4 adapter in
`Research/Quitting/FinFourProducerAtlas/PureNonsingletonCommonPrefixScreening.lean`
retains one fixed maximal-prefix packet, its `raySource`, index and word, pure
pair, selected reference tail, and scalar debt limit.
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.rayTailReplacementProfile_semantic_eq_orbit`
identifies every post-pair tail replacement with the actual indexed semantic
orbit, while `rayTailReplacementProfile_wholeDebt_tendsto_rayLimit` preserves
the scalar limit even for a varying family of replacement tails.  Before the
outer word, `rayTailReplacementBaseProfile_outcomeMass_eq_pointMass` gives the
Dirac law at the pair; after the word,
`rayTailReplacementProfile_outcomeMass_eq_actual` gives the actual full
terminal-outcome law, which need not itself be Dirac because the outer roots
may absorb.  The coordinate, total-debt, and prescribed-payoff no-go theorems
therefore have `M`, `L`, and `A`, with `C` only as a negative consumer ruling
out tail-only repair behind this unchanged word and pure pair.  They do not
eliminate the strict ray, compare independently selected words, screen a
changed marked root or a non-pure row, cross a pre-mark seam, or produce
chronology return, source regeneration, recursive descent, terminal
approximation, or a uniform-equilibrium payoff.

The static part is now factored at its actual abstraction boundary:
`QuittingTerminalExploitabilityWitness.hasStaticAtomicToggleHandoff`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/UniversalStaticAtomicToggleHandoff.lean`)
constructs a table-level atomic toggle before any profile, date, minimum, or
packet is selected.  The packet-level statement
`hasQuittingConcentratedSingletonStrategicDispatch_iff_terminal_eq`
(`Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`) then says,
under the same distinct-owner and positive vanishing-scale hypotheses, that
concentrated strategic dispatch is exactly the singleton terminal label.  For
the strong Fin4 packet,
`FinFourSingletonStageStrongConcentratedPacket.hasStrategicDispatch_iff_action_eq_false`
and
`FinFourSingletonStageStrongConcentratedPacket.strategicArm_iff_action_eq_false`
identify that label and the complete named strategic arm with Continue mode,
while
`FinFourSingletonStageStrongConcentratedPacket.collisionMinimumResidual_of_action_eq_true`
retains the unchanged source, minimum, terminal, and packet residual in Quit
mode.  The action-indexed result is a selector, not a claim that the collision
residual is absent in Continue mode.  Neither selected arm is consumed here.

The minimal nonsingleton minimum-atom route now reaches that same consumer
without a tail split or a near-minimum selected row.
`quittingTerminalSemanticDebtSum_pureNonsingletonRow_eq_totalDefect`
(`Research/Quitting/PureNonsingletonCollisionScreening.lean`) proves that an
actual pure nonsingleton row screens its continuation from every player's
unrestricted behavioral cap, so its total semantic debt is exactly the sum of
the marked root-coordinate defects.  The Fin4 endpoint
`quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint`
(`Research/Quitting/FinFourPureNonsingletonCollisionScreening.lean`) retains
one first-terminal orbit of at most three strict best-endpoint edges, each with
the exact `L * D_* / 4` reached-live-mass floor, exact mover-debt subtraction,
and no-loss marked mass.  Its terminal state is a pair; one final Continue
route gives a literal singleton whose stage mass is exactly `L`, while
`targetProfile_eq_of_time_ne` preserves the complete behavioral profile at
every other date.  The initial simultaneous pure overwrite and that final
pair-to-singleton route are not asserted profitable or cap--Nash.

For the retained nonsingleton atom,
`FinFourPureNonsingletonStrongConcentratedPacket.canonical_edge_gain_floor`
and
`FinFourMinimumAtomProducer.nonempty_strongConcentratedPacketConsumption_of_nonsingleton`
(`Research/Quitting/FinFourProducerAtlas/PureNonsingletonCollisionScreening.lean`)
keep one actual `SelectedRows` family and rank, state the literal
`mu^2 * D_* / 32` edge floor, and reach the existing source-attached strong
packet and its exact consumer.  No minimum point, atom, selected row, endpoint,
or packet is supplied or reselected.  This gives `M`, `L`, `A`, and `C` through
the unchanged strategic-versus-collision-minimum consumer; it does not consume
the collision-minimum residual, control cross-coordinate cap leakage, or
produce total-debt descent, return, regeneration, a terminal approximant, or a
uniform-equilibrium payoff.

The earlier self-tail route retains stronger continuation provenance and is
not withdrawn.
`QuittingNonsingletonMinimumLawTransfer.SelectedRows.eventually_finFourSelectedSelfTailPassport`
and its cutoff form
`QuittingNonsingletonMinimumLawTransfer.SelectedRows.exists_cutoff_finFourSelectedSelfTailPassport`
(`Research/Quitting/FinFourProducerAtlas/SelfTailContraction.lean`) intersect,
on one fixed selected-row family, the strict `mu^2 / 8` marked-mass floor and
the required debt closeness to the same minimum.  The selected literal
profile is restarted after a finite copy of its actual live roots.
`quittingAllContinueProfileSpine_selfTailClosure`
(`UniformEquilibrium/Quitting/Root/SelfTailClosure.lean`) is equality of the
complete post-date `BehaviorProfile`, not merely equality of its live roots or
terminal semantics.  The row-level declarations
`FinFourSelfTailLowRow.stageMass_eq_selectedStageMass`,
`FinFourSelfTailLowRow.lambda_lt_stageMass`, and
`FinFourSelfTailLowRow.fullSpine_eq_selectedProfile` retain the exact marked
atom, its strict floor, and that full continuation.

The minimal raw passport `FinFourActualLowTailRow` and dispatch theorem
`FinFourActualLowTailRow.nonempty_singletonEndpoint_or_closedSegment`
(`Research/Quitting/FinFourProducerAtlas/ActualLowTail.lean`) use no
`SelectedRows` or copied cap--Nash assertion.  The dependent
`FinFourActualLowTailSingletonOrigin` tag distinguishes a partial-purification
singleton from a terminal-orbit singleton and retains the actual path,
route-source profile and coalition, mover, action, routed-coalition equality,
and no-loss mass comparison.  Its common endpoint field
`FinFourActualLowTailSingletonEndpoint.postDateSpine_eq` preserves the full
post-date behavioral profile in either mechanism.  The only other raw output
is the original dispatched closed trace, which the Fin4 monodromy no-go
eliminates.

Consequently
`FinFourMinimumAtomProducer.nonempty_nonsingletonSelfTailConsumption` and the
cardinality-exhaustive
`FinFourMinimumAtomProducer.nonempty_contractedConsumer`
(`Research/Quitting/FinFourProducerAtlas/SelfTailContraction.lean`) send every
minimum-atom source to one common source-attached strong-packet consumer.
`FinFourMinimumAtomProducer.exists_residual_eq_of_hardResidual`
(`Research/Quitting/FinFourProducerAtlas/Source.lean`),
`exists_finFourMinimumAtomContractedConsumer_of_hardResidual`, and
`uniformPayoff_or_exists_finFourMinimumAtomContractedConsumer_withResidualProvenance`
retain literal equality between the constructed source's hard residual and
the supplied or bounded-data residual.  The route-tagged consumer retains its
construction origin.  Its forgetful projection
`FinFourMinimumAtomProducer.contractedConsumerResult` retains an actual strong
packet whose exact result is the existing strategic dispatch plus
atomic-toggle or exact-deletion handoff, or the unchanged source-attached
collision-minimum residual.  Its action normal form identifies the strategic
arm with Continue and forces that same collision residual in Quit mode, but
does not prove collision absence in Continue mode.  Exact positive-gap player
deletion is independently impossible on Fin4, and the atomic handoff is
already table-level.  Thus quantitative tail escape is eliminated as a
terminal atlas leaf.  This contraction has `M`, `L`, `A`, and `C`, but it
does not resolve the collision-minimum arm or produce return, regeneration,
recursive descent, completion closure, or a new uniform-equilibrium payoff.

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
tail payoff.  For an actual Fin4 monodromy producer this older projection is
vacuous because the producer itself is now impossible.  The original six-leaf
atlas, its four-node view, and the clock-compressed three-node view remain
useful provenance interfaces, but the strongest source-level contraction no
longer treats quantitative tail escape or monodromy as terminal leaves.
Monodromy deletion and the common strong-packet contraction have `M`, `L`,
`A`, and `C`; the open collision-minimum result is not a completion theorem.
The strong target is not asserted full-root Nash or near-minimal, and the
retained exact cap-root stack remains a certificate for the unmodified source
suffix.  No return, regeneration, recursive descent, backward compiler,
chronology return, completion closure, or downstream uniform-payoff consumer
is supplied.

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

- `VANISHING-DEBT-ATOM-ACCESS` to `CHRONOLOGICAL-DEBT-SHADOWING`: Missing: construct a two-tier input for the checked budget-stable iteration theorem. The bare packet structure cannot witness this producer obligation: `nonempty_quittingBudgetStablePacketSystem_iff_two_le_card` proves that it is inhabited for every reward table exactly when the player type has at least two elements, using an unrelated stationary self-loop. The actual reached-port layer must instead retain two fixed actual labels, exact literal source/successor anchoring, one globally bounded annotation family, and an operationally sublinear seam-plus-radius-loss modulus. Separately, an external source/payoff-to-candidate adapter must provide the compiler's small-debt seed, unless a solved-game disjunct is returned. A positive-minimum actual port cannot itself be that seed, and semantic closeness cannot pay the resulting fixed debt gap. Once both tiers are supplied, `exists_chronologicalDebtShadowingCertificate_of_seed` recursively selects compatible blocks and proves every same-root survival law. Moreover, any source-attached marked chain with divergent exposure and summable seams must carry divergent cumulative internal exact-Bellman debt drain by `tendsto_sum_positiveRowCoordinateDebtDrop_atTop`; no checked theorem converts that drain into prescribed-payoff charge or an admissible return. A universal exact-spine two-label selector is impossible even for two players.
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
issue mappings, strengthening chronology, and keep/drop records do not belong
in the live mathematical ledger.

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
  general fixed-law comparison
  `quittingSureBaseRoot_unique_fixedLawDebtMinimizer_of_complement_solved`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFixedLawCapRigidity.lean`)
  proves that a sure-quitting base with solved complement is the unique
  total-debt minimizer on its complete-law fibre.  Therefore
  `FinFourPairBasePaidResetTarget.returned_eq_of_fixedLawResetDispatch`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetCapRigidity.lean`)
  identifies the dispatch's complete returned semantic pair, including every
  unrestricted behavioral-cap coordinate, with the literal stationary paid
  target.  The strengthened
  `fixedLawReset_absorbingChild_or_allContinueFace` makes the remaining split
  literal at that source: a positive-absorption exact cap root has a
  strict-debt prefix whose complete terminal law differs from the target law,
  or all-Continue is an exact cap root fixing the target pair.  This is
  source-attached fixed-law `M/L/A/C`, but only for alignment and the
  branch-local changed-law conclusion; it neither renews the strict child nor
  consumes the all-Continue arm.
  Applying the generic cap lift directly to that same stationary target is
  now packaged by
  `QuittingTerminalExploitabilityWitness.nonempty_finFourSameSourcePaidResetCapPort`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourSameSourcePaidResetCapPort.lean`).
  It retains the positive carrier minimum, the reset dispatch and returned
  pair (now literally equal to the target), the actual paid/reset profile and
  law, the full-gap paid observer in
  the forced base, and the complete summable marked port. The cap chronology
  remains independent of the dispatch child, so this closes source
  construction and fixed-law alignment but not changed-law regeneration or
  the all-Continue-port discharge.
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

  The restart consumers in
  `UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRestartMoat.lean`
  make the corresponding incoming-block restriction literal. A positively
  absorbing finite exact block whose initial value lies on a compact plateau
  inside the tube has a fixed terminal-seam floor. Summable restart seams
  therefore make the aggregate block hazards summable, while bounded block
  displacement converts the seam floor `rho` into the hazard floor
  `rho / (2 * M)`. The Fin4 adapter
  `exists_finFour_minimumFiber_uniformRestartMoat_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberRestartMoat.lean`)
  supplies this moat over every actual minimum-fibre value. For any supplied
  canonical exact spine,
  `finFour_noUniformPayoff_constantAllContinue_or_limit_uniformlySeparated`
  derives marginal-hazard summability from the no-uniform-payoff hypothesis
  and returns either the constant all-Continue spine or a convergent limit
  uniformly separated from the entire minimum fibre. These results do not
  construct the exact spine, rule out either returned alternative, or prove a
  uniform-equilibrium payoff.

  A separate conditional two-cut interface makes one local paid-splice
  consumer literal. In
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumTwoCutPaidSplice.lean`,
  `quittingTerminalSemanticDebtSum_twoCut_eq` is the exact survival-weighted
  debt telescope across two supplied cuts, and
  `QuittingPositiveMinimumTwoCutBlock.totalCharge_add_theta_mul_exitExcess_ge`
  is its arbitrary-survival coercive form. For a supplied uniformly reached
  post-mark block, `offMinimum_or_exists_paidSplice` returns either a strict
  exit above the minimum debt or one fixed coordinate payer with executable
  suffix deviations at every tolerance. The Fin4 specialization gives the
  literal `block.coerciveConstant / 16` suffix gain and debt drop and the
  `block.reachFloor * block.coerciveConstant / 16` parent gain. These results
  have `M` and `L`, with a
  conditional `C` for the supplied block. They have no source `A`: no theorem
  here constructs the cuts, positive hazard or reach floors, source ancestry,
  renewable child, terminal equilibrium, or uniform-equilibrium payoff. A
  signed semantic seam is not consumed by this paid-splice module.

  The silent-padding source modules make one concrete supplied-data route into
  that two-cut interface literal. In
  `UniformEquilibrium/Quitting/Paths/RootSequenceSilentPrefix.lean` and
  `UniformEquilibrium/Diagnostics/Quitting/SilentPaddingTwoCutSource.lean`, a
  leading all-Continue row preserves the complete terminal outcome law,
  including Never, and has exact entry reach one. A positive finite-law atom
  selects a finite hazard window after that artificial row. The common joint
  compactification in
  `UniformEquilibrium/Diagnostics/Quitting/MinimumTailSilentPaddingConsumer.lean`
  fixes the atom and applies the off-minimum-or-paid-splice alternative at
  every sufficiently late retained rank. The Research adapter
  `FinFourMinimumReturnPacket.exists_finiteAtomCompactification_eventually_silentPaddingTwoCutRealization`
  (`Research/Quitting/FinFourProducerAtlas/MinimumReturnPacketSilentPaddingAdapter.lean`)
  supplies this data from the actual minimum-return packet. This route has
  `M` and `L`, Research source `A`, and only the branch-local two-cut `C`. The
  padded row records order, not meaningful chronology; no renewal, Nash
  property, nonpayer cap control, terminal approximation, or uniform-payoff
  conclusion is obtained.

  The separate generic compiler
  `QuittingTerminalSemanticSeamChain.debtSum_eq_totalCharge_add_endpoint_add_weightedSignedSeamError`
  (`UniformEquilibrium/Quitting/Debt/Dynamic/TerminalSemanticSignedSeamTelescope.lean`)
  gives the exact finite signed-debt telescope for supplied semantic prefix
  equations whose expected and decoded children may differ. The absolute
  error requires both prescribed-payoff and unrestricted-cap coordinates;
  a common bound costs `2 * card ι`, or `8` in Fin4.
  `totalCharge_add_coordinateSeamBound_add_theta_endpointExcess_ge` adds the
  seam-stable coercive inequality from scalar endpoint debt floors and a
  survival ceiling. This compiler has `M` and `L`, but no `A` or `C`: no
  theorem constructs an executable chain, attaches behavior or a source
  chronology, produces a renewable child, or derives a terminal equilibrium
  or uniform-equilibrium payoff. Payoff-only seam control is insufficient.

  The finite carrier-cycle specialization is also checked in
  `UniformEquilibrium/Quitting/Debt/Dynamic/TerminalSemanticCarrierCycleSeamToll.lean`.
  `QuittingTerminalSemanticCarrierCycle.sum_signedDebtRebase_eq_sum_netAbsorptionCharge`
  closes the source-debt terms under any supplied finite successor
  permutation. Exact roots charge every absorbed unit of a positive common
  debt floor to the full prescribed-payoff/cap seam, and
  `finFour_debtFloor_div_eight_mul_sum_absorptionMass_le_sum_semanticSupRebase`
  gives the Fin4 factor `1/8`. Approximate roots subtract exactly `card ι`
  times their total declared error. Equal-row/equal-column stationary
  couplings retain the weighted toll, while
  `QuittingTerminalSemanticCarrierOpenChain.debtFloor_mul_sum_absorptionMass_sub_initialExcess_le_sum_signedDebtRebase`
  records that an open chain may spend its initial debt excess once. This
  compiler has `M` and `L`, but no `A` or `C`: the cycle, roots, coupling, and
  debt floor are supplied, and no behavior chronology, renewable transition,
  terminal consumer, Nash profile, or uniform-equilibrium payoff is produced.

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
  exact arbitrary-Never behavioral normalization used by AKRS, and
  `QuittingPayoffTable.stationary_or_vanishingNeverNashFamily` in
  `UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumVanishingNeverAlternative.lean`
  now gives a direct conditional upstream fork: literal S.1, or actual root
  sequences whose global Nash errors and `Never` masses both tend to zero.
  The quantitative input `singletonReward_le_nashError_div_never` is
  dimension-free.  The second arm retains weighted reached-stage and
  positive-reach shifted-tail Nash bounds, not unweighted tailwise Nash,
  complete absorption, or stagewise perfection.  The theorem assumes the
  existing infinite-horizon approximate-equilibrium interface; it is not a
  finite-horizon existence theorem and does not prove that interface for every
  game.
  The independent stopping-law hierarchy in
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean` now makes
  the replacement-order boundary literal:
  `quittingCounterfactualReplacementDetermining_iff` says that all labelled
  pure-intervention coordinates of order `k` determine every one-coordinate
  replacement exactly when `card ι - 1 <= k`.  The actual behavior adapter
  identifies profile replacement with stopping-law coordinate overwrite and
  exposes the exact one-player payoff mixture and pure-time deviation cap.
  This is an architecture restriction, not a suffix compactification: no
  theorem identifies the abstract joint outcome law with the executable
  terminal law, preserves Nash inequalities under replacement, or constructs
  a compact suffix family.
  The independent reverse-prefix clock seam is now literal.  In
  `MathUE/ProbabilityMassFunction/OptionNatEscape.lean`,
  `pmfGeneralTV_tendsto_one_sub_min_of_finiteCoordinates_tendsto_zero`
  computes the exact total-variation limit after every fixed finite atom
  vanishes.  In
  `UniformEquilibrium/Quitting/Paths/ReversePrefixStoppingLaw.lean`, a supplied
  reverse literal root word followed by a supplied behavioral tail has exact
  `Never` transport through the selected player's own Continue product.  If
  the root absorption masses tend to zero and every tail has zero selected
  `Never` mass, `quittingReversePrefix_finiteHead_tendsto_zero`,
  `quittingReversePrefix_lateFiniteMass_tendsto_one`, and
  `quittingReversePrefix_pmfGeneralTV_tendsto_one` give vanishing finite heads,
  unit late-finite escape, and distance one from every fixed stopping law.
  These statements have `M` and `L` for the supplied-root/tail compiler.  They
  do not provide a conjecture-facing source adapter `A` or downstream consumer
  `C`: no positive-minimum exact-prefix ray, Fin4 pair adapter, Nash property,
  terminal atom transport, or uniform payoff follows here.
  The fixed-tail conditional compiler in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashFixedTailPrefixRay.lean`
  constructs one coherent literal prefix ray over every executable tail, with
  each new root exact Nash against the preceding prefix's unrestricted
  behavioral cap.  Its playerwise and total debts scale by the exact joint
  Continue product.  A supplied positive debt floor forces a positive product
  limit and vanishing one-stage absorption.  With a separately supplied
  positive finite tail atom,
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FixedTailCapNashPrefixClockEscape.lean`
  proves exact marginal `Never` convergence and total-variation limits, a
  uniform quantitative late-finite floor, and exclusion of every strictly
  cofinal total-variation-convergent subsequence.  This has `M` and `L` only:
  neither the floor nor atom is produced, the fixed tail and complete prefixes
  are not asserted Nash, and there is no source `A`, consumer `C`, Fin4
  specialization, weak-limit obstruction, or uniform-equilibrium conclusion.
  The qualified obstruction in
  `UniformEquilibrium/Diagnostics/Quitting/CounterfactualSuffixCompactnessNoGo.lean`
  makes the limitation concrete.  Two rational Fin4 independent stopping
  families have the same payoff-vector response law after every current
  one-player replacement after the first-stopping map forgets dates and the
  reward map forgets coalition labels.  A state encoded only by that signature
  cannot realize the stated suffix transitions and successor payoff
  observations.  A separate actual one-stage spike family is uniformly separated
  by its depth-labelled probes.  Therefore no metric encoding of all those
  probes with one common all-depth modulus has sequentially compact image or
  one finite global net at the resulting resolution.  This does not obstruct
  fixed-depth continuity, depth-dependent moduli, or finite programs, and it
  does not prove an equilibrium or a uniform-equilibrium counterexample.
  `nonempty_chronologicalLimit` in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalLimit.lean`
  now sends the vanishing-Never arm through late sure-solo completion and one
  shared strict subsequence of globally normalized chronological marked laws.
  The finite law records the literal root, bounded post-stage tail, and
  discrete nonempty coalition at each absorption clock.
  `le_pathTotal_chronologicalCadlagPath_of_tendsto` proves that the weakly
  decoded càdlàg path satisfies A1.  `HasClockGap.cdf_of_tendsto` preserves
  the canonical finite clock-gap law under weak convergence, and
  `ChronologicalLimit.absorptionPathA2` compiles that law into A2.  Meanwhile,
  `pathJump_chronologicalCadlagPath_eq_clockCoalitionFiber_real` in
  `UniformEquilibrium/Quitting/AbsorptionPath/ChronologicalMarkedRootSequenceJump.lean`
  identifies each decoded source jump with its exact clock--coalition fiber.
  In that file, `exists_dominantClockWindowStage_of_width_lt_real` selects the
  rightmost positive source stage whenever a finite open clock window carries
  more mass than its width, with simultaneous nonnegative coalition residuals
  whose total is strictly smaller than the width.
  `nonempty_chronologicalNullWindowSequence` in
  `UniformEquilibrium/Quitting/AbsorptionPath/ChronologicalMarkedRootSequenceJumpLimit.lean`
  supplies shrinking null-boundary windows and fixed-window Portmanteau
  convergence.  `ChronologicalLimit.nonempty_chronologicalJumpStageLimit` in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalA3.lean`
  then performs one explicit strict rank extraction and one compact root
  subextraction simultaneously for every coalition coordinate.
  `ChronologicalLimit.absorptionPathA3` proves the literal product-root jump
  axiom, including the A1-derived exclusion of a terminal jump.
  `one_sub_upper_mul_collisionCDF_sub_le_choose_mul_clockCDF_sub_sq` in
  `UniformEquilibrium/Quitting/AbsorptionPath/ChronologicalMarkedRootSequenceCollision.lean`
  gives the exact finite quadratic nonsingleton-window estimate, and its
  weak-limit form holds at fixed continuity endpoints.  The clock-gap
  controlled right points then force every nonsingleton lower right
  derivative to vanish.  `ChronologicalLimit.absorptionPathA4` and
  `ChronologicalLimit.isAbsorptionPath` in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalA4.lean`
  prove A4 and the literal A1--A4 conjunction for this same decoded path.
  The finite prefix/tail identity in
  `UniformEquilibrium/Quitting/AbsorptionPath/ChronologicalRootSequenceTail.lean`
  and the shared jump-stage tail extraction in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalJumpPerfection.lean`
  identify the limiting post-stage tail with `absorptionPathPayoff`.
  Reached-stage Nash then closes to exact endpoint Nash at the path's literal
  selected jump root, and `ChronologicalLimit.jumpPerfect` proves the exact
  jump-row component of sequential perfection.
  `QuittingFiniteCDFCut` in
  `UniformEquilibrium/Quitting/AbsorptionPath/FiniteRootSequenceCDFCut.lean`
  gives the exact right staircase inverse of each finite source CDF.
  `ChronologicalLimit.nonempty_chronologicalPathTimeAdjacentCutLimit` in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalSingletonLowerBound.lean`
  uses that inverse and one strict source extraction to make both adjacent
  source clocks and every cumulative coalition coordinate converge at each
  fixed nonterminal path time.  Reached-stage Nash and the finite tail payoff
  identity then prove the literal singleton lower bound at every nonterminal
  continuous-clock path time,
  `ChronologicalLimit.singletonReward_le_absorptionPathPayoff` for every
  player.  The finite refusal-window localization in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalPositiveSingletonRate.lean`
  combines a linear singleton increment, the quadratic collision estimate,
  source-tail clock-diameter control, and the exact Nash refusal telescope.
  At every actual nonterminal path time where a player's singleton coordinate
  has positive right derivative,
  `ChronologicalLimit.absorptionPathPayoff_le_singletonReward_of_pathRightDerivative_pos`
  proves the matching upper bound, while
  `ChronologicalLimit.absorptionPathPayoff_eq_singletonReward_of_pathRightDerivative_pos`
  states the resulting singleton-payoff equality literally.
  `ChronologicalLimit.isSequentiallyPerfectAbsorptionPath` bundles the checked
  jump rows, continuous lower bounds, and active equalities for this same
  actual chronological path.
  On the terminal-jump side,
  `ChronologicalJumpStageLimit.stageContinueMass_tendsto_zero_of_pathTotal_eq_one`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/ChronologicalTerminalJumpS2.lean`
  proves that the actual selected dominant rows have all-Continue mass tending
  to zero whenever one path jump reaches total mass one.  Reached-source Nash
  transfer, near-sure-to-sure perturbation, and the punishment adapter then
  give literal S.2 in
  `ChronologicalLimit.instantPunishmentEquilibriumExistence_of_terminalPathJump`.
  This is an `M`/`L` theorem and an actual-source `A`/`C`, conditional on the
  explicitly supplied terminal jump.
  The published small-cell productization is checked as
  `exists_akrsSmallCellProductization` in
  `MathUE/PMFProduct/SmallCellProductization`.  The production
  partition and decoder in
  `UniformEquilibrium/Quitting/AbsorptionPath/AKRSPartition.lean`,
  `UniformEquilibrium/Quitting/AbsorptionPath/AKRSPartitionSmallCell.lean`,
  `UniformEquilibrium/Quitting/AbsorptionPath/AKRSPartitionDecoder.lean`, and
  `UniformEquilibrium/Quitting/AbsorptionPath/AKRSSequentialPerfectionDecoder.lean`
  copy large jumps, productize small cells, and preserve singleton support.
  They use the exact cell parameter `1 / (resolution - 1)` with the published
  dimension-factor coordinate bound
  `2 ^ Fintype.card ι * parameter * pathCellAbsorption`.  These modules do not
  claim the full weak-convergence conclusion of published Proposition 4.8.
  `exists_wellSupportedAbsorbingSequence_of_sequentiallyPerfectAbsorptionPath`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/SequentiallyPerfectAbsorptionPathS3.lean`
  turns path-total boundedness, sequential perfection at zero, and no terminal
  total jump into the literal well-supported completely absorbing S.3
  sequence.  The source-facing
  `ChronologicalLimit.wellSupportedAbsorbingSequenceExistence_of_noTerminalTotalJump`
  applies that consumer to the actual chronological limit.  Thus the generic
  productization has `M` and `L`, the supplied-path capstone adds conditional
  `C`, and the chronological adapter has `M`, `L`, `A`, and conditional `C`.
  Meanwhile,
  `ChronologicalLimit.completedTerminalOutcomeMass_tendsto` and
  `completedTerminalPayoff_tendsto` identify its clopen endpoint fibers and
  fixed reward moment.  The conditional
  `payoff_isUniformEquilibriumPayoff` then uses the existing terminal-Nash
  compiler.
  `ChronologicalLimit.instantPunishment_or_wellSupportedAbsorbingSequenceExistence`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/ChronologicalAbsorptionPathS2S3.lean`
  performs the exhaustive terminal/no-terminal case split for every actual
  completed chronological source.  Composing it with
  `QuittingPayoffTable.stationary_or_vanishingNeverNashFamily`, the absorbing
  completion, and chronological compactification gives
  `QuittingPayoffTable.stationary_or_instantPunishment_or_sequentiallyPerfectAbsorbing`
  in `UniformEquilibrium/Quitting/Classification/Existence/AKRSTheorem34.lean`.
  This is the literal table-level forward implication of AKRS Theorem 3.4,
  including the empty-player stationary case.  Its premise says that for each
  positive error some arbitrary behavior profile is terminal-payoff
  approximate Nash against every unilateral behavioral replacement.  It does
  not prove that premise for every game, select one fixed payoff target, or
  supply the all-long-finite-horizon control required for uniform equilibrium.
  The reverse S.3 boundary is now stated literally.  If an initially absorbing
  row-perfect source has a nonterminating restarted tail,
  [`QuittingPayoffTable.solo_sub_never_le_of_completelyAbsorbing_not_everyRestart`](../UniformEquilibrium/Quitting/Classification/Existence/AKRSNullTailAlternative.lean)
  bounds every singleton payoff by Never plus the row error.  The inclusive
  theorem
  [`QuittingPayoffTable.allContinueExactNash_or_everyRestartWitnesses`](../UniformEquilibrium/Quitting/Classification/Existence/AKRSNullTailAlternative.lean)
  therefore gives exact all-Continue terminal Nash, or termination after every
  restart for every sufficiently accurate initially absorbing row-perfect
  witness.  Even within the remaining every-tail residue, the restricted predicate
  [`QuittingPayoffTable.HasStationaryExactEveryRestartRowPerfectSource`](../UniformEquilibrium/Quitting/Classification/Existence/AKRSReverseS3Hardness.lean)
  records one stationary exact source, and
  [`universalStationaryExactEveryRestartSource_iff_approximateExistence`](../UniformEquilibrium/Quitting/Classification/Existence/AKRSReverseS3Hardness.lean)
  proves that its universal reverse implication is equivalent to general
  finite-quitting terminal approximate-equilibrium existence.  The hard
  reduction maps `players` to `players ⊕ PUnit`; it is not a same-cardinality
  equivalence.  This eliminates the null-tail subcase and shows that even this
  restricted stationary-exact slice is universally hard.  It does not prove or
  refute journal Theorem 3.4, whose reverse S.3 implication remains open.
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
- **Alternative corrected-source AKRS route:** the direct chronological proof
  above establishes Theorem 3.4 without closing every residual in the older
  corrected-Simon route.  In that alternative route, a raw refined source residual can
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
  final consumer must be eliminative: all three fixed AKRS branches directly
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
  normalized arbitrary-Never AKRS premise.  These are semantic
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
- **Normal sequentially perfect absorbing source compiler:**
  `exists_normalSupportDelayedSwitch` and
  `exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing`
  (`UniformEquilibrium/Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`)
  compile a supplied sequentially row-perfect completely absorbing root
  sequence, under all-player punishment normality, into terminal approximate
  Nash profiles at every positive error. The equivalent well-supported source
  formulation has parallel terminal and uniform-payoff wrappers. The delayed
  switch scans only finitely many rows after the first support-survival
  crossing; a target-closed tail handles the good branch, while all Continue
  handles the branch whose deleted-player survival clocks are all small.
  `exists_uniformEquilibriumPayoff_of_all_normal_of_sequentiallyPerfectAbsorbing`
  then invokes the fixed-payoff terminal selection theorem. In Fin4,
  `FinFourQuantitativeFullSupportHardResidual.exists_uniformEquilibriumPayoff_of_sequentiallyPerfectAbsorbing`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`)
  gets normality from the supplied quantitative hard residual. These results
  have `M` and `L`, source-conditional `A`, and conditional terminal/uniform
  `C`. Neither the generic theorem nor the Fin4 residual produces S.3 or a
  well-supported source; there is no unconditional no-uniform-payoff
  contradiction, stationary-equilibrium theorem, or general stochastic-game
  extension.
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
- **Normal unique-persistent Nash--Bellman spine:**
  `abs_value_sub_soloReward_le_of_bounded_bellman` and
  `IsCanonicalExactQuittingNashBellmanSpine.isUniformEquilibriumPayoff_soloReward_of_persistent`
  (`UniformEquilibrium/Quitting/Classification/Existence/NormalUniquePersistentNashBellmanSpine.lean`)
  show that a nonsummable owner marginal together with a summable owner-deleted
  clock concentrates bounded Bellman values on the owner's singleton vector;
  exact root Nash and owner punishment normality then make that vector a
  uniform-equilibrium payoff.  In the quantitative Fin4 full-support hard
  residual,
  `FinFourQuantitativeFullSupportHardResidual.all_marginalQuitHazards_summable`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardNashBellmanSpine.lean`)
  therefore forces every marginal of every supplied exact spine to be
  summable; `all_marginalQuitHazards_summable_of_no_uniformPayoff` states the
  direct no-uniform-payoff composition.  This is checked mathematics and a
  conditional spine consumer, not a producer selecting the unique-persistent
  branch or a resolution of the hard residual.
- **Unbounded finite exact-block hazard capacity:**
  `HasUnboundedFiniteExactNashBellmanHazardCapacity` and
  `nonempty_finiteExactNashBellmanHazardReturn_of_unboundedCapacity`
  (`UniformEquilibrium/Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`)
  formalize positive-length exact Nash--Bellman blocks and their literal sum
  of marginal Quit probabilities.  Using the game-independent compact return
  theorem in `MathUE/CompactFiniteChargedReturn.lean`, failure of every
  `BddAbove` hazard bound yields, at every positive radius, one block with two
  close ordered annotations and intervening hazard at least one.  This is a
  checked conditional capacity-to-return adapter.  The compact refinement and
  seam ledger in
  `UniformEquilibrium/Quitting/Debt/Dynamic/SummableResidualNashBellmanSpine.lean`
  concatenate those returns into a `QuittingSummableResidualNashBellmanSpine`
  with arbitrarily small total Bellman-plus-Nash residual and at least one
  persistent marginal label.
  `QuittingSummableResidualNashBellmanSpine.exists_uniformEquilibriumPayoff_of_twoPersistent`
  (`UniformEquilibrium/Quitting/Debt/Dynamic/SummableResidualPersistentClosure.lean`)
  consumes one such spine when it has two persistent labels.  If it has only
  one, the all-normal theorem
  `exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity_of_allNormal`
  (`UniformEquilibrium/Quitting/Classification/Existence/AllNormalUnboundedExactBlockHazardCapacity.lean`)
  uses punishment normality and the summable opponent clock to consume the
  owner's singleton payoff.  In Fin4,
  `finFour_exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`)
  obtains all-player normality from the quantitative hard-residual alternative
  under the contrary hypothesis.  Its literal contrapositive
  `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
  says that any Fin4 counterexample has bounded exact-block hazard capacity in
  the canonical reward box.  No theorem produces unbounded capacity from the
  AKRS source or a source trace, identifies a numerical bound in the bounded
  branch, or equates exact-block capacity with source-trace capacity.
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
