# Paired collision completion audit and bounded proof mining

## Scope and evidence

This is a static audit of
`math/formalized/PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION.md` against the
actual declarations and imports listed below. The auditor read the complete
packet, the seven paired-collision modules, the scalar root construction,
and the relevant generic calendar, complete-cap, and horizon consumers.
The auditor ran no Lean or Lake commands and supplies no compiler evidence.

The build owner confirms silent targeted passes for the final finite-calendar,
exact parameter-one calibration and infinite periodic `O(1/N)` modules, using
`LEAN_NUM_THREADS=1 lake --quiet --iofail build` with each named module.
Independent final read-only review found no remaining literal packet claim.
The full default build and exhaustive axiom audit passed silently with
`LEAN_NUM_THREADS=1 lake --quiet --iofail build`. Trust, import boundaries,
duplicates, reward bounds, both redundancy checks, documentation, all script
tests and registered experiments also passed. The packet is retired unchanged
to `math/formalized/`. The auditor's own evidence remains static; these compiler
results are reported by the build owner.

## Main claim coverage

The literal fifteen-row input is `reward`, its parameter-one table equality
is `reward_one`, and its constant singleton comparison matrix is
`singletonMatrix`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardTable.lean`).
All branches retain this same raw table and zero Never convention. No
additive terminal translation is introduced by the family construction.

`exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardExistence.lean`)
assembles all four parameter ranges. `exists_uniformPayoff_of_le_one` and
`surePair_isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardExits.lean`)
supply the signed low-parameter exit and the literal high-parameter target
`(c,c,1,1)`. The low branch permits arbitrarily negative parameters. The
sure-pair endpoint comparisons, actual terminal payoff, exact terminal Nash,
and complete behavioral cap are also exposed in that module.

`exists_admissible_rates`
(`MathUE/PairedPhasePolynomialRoots.lean`) produces both residual zeros with
`1/4 < b < a < 9/10` and `1/2 < a`. Its denominator bounds exclude the
elimination boundaries before defining continuation values. The starting
and ordering roots have the packet's uniqueness by composition with
`startingPolynomial_strictMonoOn` and `orderingPolynomial_strictMonoOn` in
the same file. Uniqueness of the final simultaneous zero is not asserted.

`exists_periodicRates` and `exists_periodicUniformPayoff`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardPeriodic.lean`)
select rates from the parameter alone. The `PeriodicRates` declarations
`phaseA_quitPayoff`, `phaseB_quitPayoff`, `phaseA_continuePayoff`,
`phaseB_continuePayoff`, and `quiet_slacks_pos` evaluate the actual table
and prove all active ties and quiet incentives. `cycle_actualValue` pins
the proposed values to actual play. `profile_isExactTerminalNash`,
`profile_completeCap`, and `allSuffix_isExactTerminalNash` cover complete
behavioral replacements and every live suffix, including Never.

`PeriodicRates.profile_uniformPayoffWitness` in that periodic module retains
the same infinite profile at every accuracy. Its target and rates precede
the accuracy. The finite witness described below also fixes its rates and
target before choosing its cycle count and threshold.

`exists_stationaryHazard`, `commonRoot_quitPayoff`,
`commonRoot_continuePayoff`, and `commonProfile_completeCap_eq_max`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardStationary.lean`)
provide the actual stationary root, its evaluated endpoints, and the exact
full behavioral cap before root selection. The two printed IVT sign
calculations are `stationaryResidual_half` and
`stationaryResidual_four_oneHundredth` in that file. The selected root has
exact terminal Nash and its fixed uniform payoff. No sign assumption on
the selected Quit value is required.

The branch declarations retain closed range hypotheses, so both relevant
constructions apply at `c=1`, `c=2`, and `c=4`. The final existence proof's
preferred branch does not remove those overlaps. Literal input-table
equality can be transported by rewriting; no transformation from an
arbitrary collision table is claimed.

## Independent finite calendars and printed horizon constants

All declarations in this section reside in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardFiniteCalendar.lean`
under `PeriodicRates`, unless another file is specified.

`finiteStoppingLaw_active_toReal`, `finiteStoppingLaw_none_toReal`, and
`finiteStoppingLaw_late_or_inactive` establish the retained geometric
atoms, positive Never masses, and zero inactive or late atoms.
`finiteStoppingLaw_eq_censor` identifies each marginal with its own
censored infinite clock. `exists_finiteTimingLaws_with_masses` produces
actual finite-date-or-Never laws and preserves the complete terminal
semantic pair. The construction uses separate player marginals, not a
jointly coupled clock.

`finiteProfile_payoff_eq` proves the exact renewal identity.
`finiteProfile_completeCap` proves equality of the actual unrestricted
behavioral supremum with the original phase-A target. Its upper bound uses
the generic cap fold with terminal boundary `max 0 solo`; its lower bound
is the legal first active date from `finiteProfile_firstActive_attains`.
Thus after-support dates and Never are covered explicitly by the consumed
cap theorem, not excluded from a retained finite menu.

The generic upper-bound consumer is
`quittingContinuationBestResponseValue_cyclicFiniteProfile_le`
(`UniformEquilibrium/Quitting/Cycles/CyclicFiniteWord.lean`). Actual finite
timing realization is supplied by
`exists_finiteDeadlineTimingProfile_cyclicFinite_exact`
(`UniformEquilibrium/Quitting/Cycles/CyclicFiniteMenu.lean`), including
every pure-date response outside the retained support.

`finiteProfile_debt_eq` and `finiteProfile_exploitability_eq` expose the
exact error, while `finiteProfile_exploitability_le_geometric` proves the
printed bound `8(9/10)^(4K)`. The target remains fixed as `K` changes.

The checked declarations `finiteProfile_horizonDelivery`,
`finiteProfile_horizonDeviation`, `finiteProfile_horizonRegret`, and
`finiteProfile_horizonTargetDelivery` match the printed charges `8K/N`
and `16K/N`. `horizonBoundary_le_half` and
`finiteProfile_uniformPayoffWitness` use exactly
`max 1 ceil(32K/ε)` and a terminal error at most `ε/2`. They apply to
every sufficiently large horizon and every complete behavioral deviation.

The underlying declarations
`abs_finiteAveragePayoff_sub_terminal_quietAfterDeadline_le` and
`finiteAveragePayoff_update_quietAfterDeadline_le_terminal_add`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineHorizonError.lean`)
retain signed terminal rewards and the censored opponents' Never mass.
Only the deviator's own singleton must be nonnegative for the one-sided
deviation comparison. Infinite-opponent geometric contraction is not
applied after censoring. The build owner confirms the final finite-calendar
targeted pass; the auditor's own evidence remains static declaration matching.

## Class and strategy comparisons

`membershipToggleGap`, `not_exactTerminalNash_pureClock`,
`bestReplyValue_allNever`, `punishmentValue_le_one`,
`soloJoiningObstruction_allRates`, `not_cappedJointExit`,
`not_lowActiveQuittingRootQuitPayoff`, `not_pairedCycleRawRegion`, and
`not_pairedCycleRawRegion_relabel`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardBoundary.lean`)
cover the packet's deterministic-clock and source-class comparisons.
The raw-region exclusion quantifies every schedule, and the relabeling
theorem permutes coalition members and recipients together.

`smallHazard_actualPayoff_tendsto` in that boundary file concerns actual
stationary payoffs, not merely a singleton linearization. It gives the
limit `5/4` for every fixed parameter and every player.
`exists_stationaryProfile_all_payoffs_gt_singleton` and
`not_weakSingletonPayoffExclusion` supply the claimed consequence. The
small-hazard witnessing profile is not asserted to be an equilibrium.
`normalPlayer` in the finite-calendar file exposes the punishment-normality
predicate itself using the actual all-Never plan.

## Final quantitative coverage checks

Both additional packet refinements pass their targeted checks.

1. `primary_eq_periodTwoParameter`, `secondary_eq_periodTwoSecondary`,
   `profile_at_one`, `phaseAValue_at_one`, and `phaseBValue_at_one`
   (`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardCalibration.lean`)
   identify both selected rates, both phase values and the actual behavioral
   profile. The old uniqueness proof supplies the identification; no new
   quartic uniqueness argument is duplicated.
2. `profile_horizonDeviation_absolute_uniform`,
   `allSuffix_horizonDeviation_absolute`, and the delivery/Nash consumers
   (`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardHorizon.lean`)
   prove absolute terminal-to-average error at most `(8000/271)/N` for every
   complete behavioral replacement, both phases and every literal suffix.
   The regret bound is `(16000/271)/N`. These reuse the generic cyclic
   opponent-clock estimate and are distinct from the finite-calendar bounds.

Static imports reach the family through
`UniformEquilibrium/Quitting/Examples/BlockPair/All.lean`, imported by
`UniformEquilibrium.lean`. `MathUE.lean` imports the scalar module, and
`AxiomAudit.lean` lists the family modules. These observations establish
source reachability only. All three new modules have targeted compiler
evidence, and the full integration gate also passed.

## Bounded compositional opportunities

These are consequences available by composing existing proofs, not newly
checked declarations from this audit and not additional research claims.

### Post-completion connections

The rational raw-clock producer and its logarithmic calendar bound already
retain actual independent laws, terminal Nash error, terminal delivery and
passive Never marginals. The signed
`isHorizonNash_finiteDeadline_of_terminalNash_signed`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineSignedHorizonError.lean`)
and the delivery theorem
`abs_finiteAveragePayoff_sub_terminal_finiteDeadline_le`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineHorizonError.lean`)
can turn those same laws into explicit fixed-target horizon witnesses.
No singleton-sign hypothesis or new late-negative-singleton argument is
needed. The shared composition is now named
`finiteDeadlineTiming_uniformPayoffWitness_of_terminal_bounds`
in the signed horizon module. It retains the supplied laws and any valid
reward bound, including zero; a separate rational raw-source wrapper remains
available to add without another horizon proof.

`quittingTerminalSemanticPair_rationalFiniteWord_eq_cast`
(`UniformEquilibrium/Quitting/Root/RationalFiniteWordSemantics.lean`)
already connects the executable finite-word evaluator to actual payoff and
the full behavioral cap, including Never and late dates. Identifying the
produced rational calendar word with that input would expose exact computed
caps without another response-cap engine. This requires the entire reward
table to be rational, unlike clock production, which needs only rational
singletons. It does not establish density or termination of arbitrary
enumeration.

`IsεAsymptoticNash.of_reward_close`
(`UniformEquilibrium/Quitting/PayoffProcess/TailStepSelector.lean`)
transfers Nash with error `error + 2 * rewardDistance` on the literal same
behavioral profile. Combined with retained-family payoff selection, every
member's finite support and literal Continue coordinates survive without
strategy convergence or closedness arguments. This is the reuse boundary
for the checked weak-inverse quiet-witness implementation in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/WeakInversePassiveRowQuietWitnesses.lean`.
Its raw theorem fixes the target before accuracy and the finite laws before
every valid reward bound and horizon. It does not provide a computable
weak-boundary target or uniform boundary calendar complexity.

### Additional example consumers

- The checked exact calibration at `c=1` uses
  `secondaryRate_eq_of_secondaryResidual_zero`
  (`MathUE/PairedPhasePolynomialRoots.lean`), followed by
  `periodTwo_secondary_substitution_factorization` and
  `existsUnique_periodTwoParameter`
  (`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`).
  The existing bounds then give `37/50 < a < 3/4` and `1/2 < b`.
  Its sharper inherited brackets are `373/500 < a < 747/1000` and
  `73/100 < b < 74/100`.
- The positive margin in `membershipToggleGap` gives failure of terminal
  ε-Nash for every pure clock whenever `ε < min 1 (4-c)` on `1 ≤ c < 4`.
  A small explicit consumer would materially sharpen the current
  zero-error exclusion. The generic
  `HasQuittingPureTimeMembershipToggleGap.of_reward_close`
  (`UniformEquilibrium/Quitting/Paths/PureTimeMembershipToggleObstruction.lean`)
  also transports the gap to uniformly close reward tables, losing twice
  the coordinatewise perturbation radius. This concerns pure strategies
  only; it supplies no perturbed-table equilibrium producer.
- The actual common-root and sure-pair constructions compose into an
  exact stationary terminal equilibrium and a fixed uniform payoff for
  every `c ≥ 2`. Exposing this source-strategy conclusion could help a
  consumer requiring a stationary witness, but it mainly packages the
  existing split and is less urgent than the quantitative pure-clock
  consumer.
- The generic finite-deadline estimates already apply beyond this family:
  a profile quiet after deadline `d` has delivery charge `Md/N` and
  terminal-to-horizon regret charge `2Md/N`, for reward magnitude bound
  `M`, signed terminal rewards, and nonnegative own-singletons. The paired
  finite-calendar module supplies an actual consumer of those estimates.

No claim here extends the all-parameter existence theorem to arbitrary
passive rewards, triples, own-singleton levels, or the full collision
cylinder. Source-class exclusions do not imply uniform-payoff exclusion.
