# Uniform-equilibrium toolkit

This page organizes the integrated formal corpus by mathematical job. It is a
maintained interface map, not a progress report: headline declarations are in
[`STATUS.md`](STATUS.md), the mathematical boundary is in
[`FRONTIER.md`](FRONTIER.md), and the promotion process is in
[`PIPELINE.md`](PIPELINE.md).

The central distinction is between a **compiler**, which turns a supplied
certificate into a uniform payoff, and a **producer**, which constructs that
certificate from more primitive game data.  A verifier, compactness theorem,
or counterexample restriction is not silently counted as either one.

## Dependency shape

```text
game or analytic data
        |
        v
producer / selector -----> certificate or executable path
                                  |
                                  v
                         verifier / compiler
                                  |
                                  v
                   IsUniformEquilibriumPayoff

closure and transfer tools move proved results between nearby games or
payoff descriptions; diagnostics and no-go results constrain every branch
without producing a witness.
```

## Canonical project entry points

`exists_uniformEquilibriumPayoff_of_productLowPremium`
(`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`)
proves fixed-payoff existence on every finite nonempty player set with
nonnegative singleton rewards whenever each absorbing product root has an
active player's Quit payoff at most its singleton. Its periodic producer
gives unrestricted terminal approximate Nash at every suffix in the original
game. `HasProductLowQuittingPremium`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`)
states this reward-table condition and preserves it under nonnegative
playerwise affine changes of terminal rewards. Positive normalization uses
`UniformEquilibrium/Quitting/Root/PlayerwiseUnitNormalization.lean`.
`hasProductLowQuittingPremium_of_noLargerOwnPremium`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumMonotonicity.lean`)
proves downward closure under every participant's singleton-relative premium,
with arbitrary passive rewards. This need not preserve failure of
supportwise balance.
`not_hasProductLowQuittingPremium_iff_exists_inwardViolation`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumInwardViolation.lean`)
shows that failure can always be witnessed by an actual absorbing product
root with no sure quitter and a strictly positive Quit premium at every
active player. The construction preserves the original active support.
`decideHasProductLowQuittingPremium_eq_true_iff`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumDecision.lean`)
proves that an executable rational-table test returns true exactly when the
original product-low condition holds. The decision procedure uses actual
real quantifier elimination and includes the empty-player case. It has no
efficiency guarantee and does not decide uniform-equilibrium existence.
`decideHasProductLowQuittingPremiumAtIsolatedRoots_eq_true_iff`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumIsolatedRootDecision.lean`)
provides the corresponding executable test for certified algebraic reward
entries. For every actual real table denoted by those entries, its Boolean
answer is true exactly when that table is product-low. The algorithm uses
only rational polynomial coefficients and isolating intervals, not real
comparisons. Both decision procedures share the same hazard-premium formula
implementation.
`exists_certifiedIsolatedRootQuittingReward_of_isAlgebraic`
(`UniformEquilibrium/Quitting/Root/IsolatedRootRewardCoverage.lean`)
proves that every coordinatewise algebraic table has such an encoding of
that same table. The companion denotation theorem rules out vacuous inputs.
Encoding existence is not an algorithm taking unencoded real numbers.
`isSemialgebraic_hasProductLowQuittingPremium_rewardTables`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumSemialgebraic.lean`)
proves that the accepted real reward tables form a semialgebraic set, with
reward entries as free coordinates and no singleton sign restriction.
`degrees_quittingFixedRewardPremiumPolynomial_le`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumHazardDegree.lean`)
bounds the fixed-reward premium's variable multiset by the opponent set.
Thus each hazard has degree at most one, the player's own hazard has degree
zero, and total hazard degree is at most the number of opponents. The
polynomial specializes the joint reward-hazard polynomial and evaluates to
the actual premium at every real hazard vector.
`exists_uniformEquilibriumPayoff_of_productLowPremiumDecision`
(`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumDecisionUniformPayoff.lean`)
connects a true decision to fixed-payoff existence when the player set is
nonempty and own-singleton rewards are nonnegative. The same module gives
periodic all-suffix terminal approximate equilibria. These conclusions are
existence theorems, not executable strategy extraction.

`UniformEquilibrium/Quitting/Examples/ProductLowFinFourFamily.lean` gives
a four-player family with arbitrary singleton levels, positive coordinate
scales, and arbitrary passive rewards. It is product-low, admits a weighting
on every proper support, and fails supportwise balance on the full support.
Nonnegative singleton levels give periodic terminal approximate equilibria
and a fixed uniform payoff for each family member. Product-low and these
existence conclusions also allow zero coordinate scales; the strict
separation assertion requires positive scales. In contrast,
`productLow_iff_supportwiseBalance_finTwo`
(`UniformEquilibrium/Quitting/Classification/FinTwoProductLowSupportwiseEquivalence.lean`)
identifies the two conditions for arbitrary signed two-player tables.
`finTwo_not_hasProductLowQuittingPremium_iff`
(`UniformEquilibrium/Quitting/Classification/FinTwoProductLowPremiumCriterion.lean`)
identifies their failure with both full-coalition premiums being positive.
`UniformEquilibrium/Quitting/Examples/PureCoalitionLowProductFailure.lean`
shows that testing only pure coalitions does not establish product-low:
its three-player half-hazard root has every Quit premium equal to one quarter.
`UniformEquilibrium/Quitting/Examples/PureCoalitionLowProductFailureFinFour.lean`
gives the four-player version with an inactive fourth player, arbitrary
passive rewards, absorption probability seven eighths, and the same active
premiums.
`UniformEquilibrium/Quitting/Examples/ProductLowPremiumBoundaryIdentities.lean`
gives the separating family's positive integer dual combination and a
normalized correlated coalition law which cannot be an independent product
law. Its expected participant premium is one seventh of the coordinate
scale, including an equality stated directly on the actual reward table
with nonparticipants excluded. The same module records the all-Quit premium
vector and the zero active premium when only player three quits.
`exactRootSuccessor_mem_singletonLowerBoundary`
(`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowExactRootBoundary.lean`)
shows that nonnegative own premiums and product-low imply every absorbing
exact root's successor lies above all singleton levels, with an active
coordinate attaining its singleton exactly.
`exactRootSuccessor_mem_singletonLowerBoundary_of_twoPlayerPremiumCore_strictLeave`
(`UniformEquilibrium/Quitting/Classification/TwoPlayerPremiumCoreExactRootBoundary.lean`)
gives the same successor conclusion for two designated premium-bearing players,
with constant participant rewards outside that pair and one core player
strictly preferring the other core's singleton coalition to their pair.
It requires only that leaving player's annotation to meet its singleton floor.
Positive outsider hazards are handled before reducing to the pair; no
product-low condition or restriction on larger-coalition core premiums is
supplied.
`not_isQuittingFullExactRootPotential_of_twoPlayerPremiumCore_strictLeave`
(`UniformEquilibrium/Quitting/Classification/TwoPlayerPremiumCoreSmoothDrift.lean`)
excludes full exact-root potentials differentiable at every singleton lower-boundary
point; no off-boundary differentiability or nonnegative singleton assumption is needed.
`exists_uniformEquilibriumPayoff_of_twoPlayerPremiumCore_strictLeave`
(`UniformEquilibrium/Quitting/Classification/Existence/TwoPlayerPremiumCoreUniformPayoff.lean`)
gives a fixed uniform-equilibrium payoff for the four-player class with nonnegative
singletons. It internally obtains the polynomial obstruction in the positive-singleton
branch and uses the zero-solo theorem otherwise. The literal table in
`UniformEquilibrium/Quitting/Examples/TwoPlayerPremiumCoreStrictLeave.lean`
has such a payoff but fails product-low.
`quittingSingletonMatrix_eq`, `matrix_isR0`, `matrix_r0Degree_eq_one`, and
`matrix_isStandardQ`
(`UniformEquilibrium/Quitting/Examples/TwoPlayerPremiumCoreStrictLeaveMatrix.lean`)
identify its actual singleton comparison matrix, exclude nonzero homogeneous
LCP solutions, and compute canonical degree one from the unique actual root
at offset `(1,-1,-1,-1)`, with inactive residual two and active determinant seven.
Its recursive normal core is full. Principal Q-bar and inverse tests, response
partitions, and child-certificate separation remain outside this checked example.
`quittingPremiumCore_eq_empty_iff_weakSupportPeeling` and
`quittingPremiumCore_outsider_reward_eq_singleton`
(`UniformEquilibrium/Quitting/Classification/QuittingPremiumCore.lean`)
identify the actual greatest premium-trap core and its empty-core peeling
criterion. Under nonnegative participant premiums and a nonempty core,
an outsider is flat only on coalitions inside its own extension of that core;
no global outsider flatness is required.
`quittingPremiumCore_pair_reward_gt_singleton`
(`UniformEquilibrium/Quitting/Classification/QuittingPremiumCorePair.lean`)
derives both strict pair premiums directly from a pair core, without a
nonnegative-premium hypothesis.
`exactRootSuccessor_active_eq_singleton_of_support_not_premiumTrap`
(`UniformEquilibrium/Quitting/Classification/QuittingPremiumCoreExactRoot.lean`)
gives an active binding singleton coordinate for an exact root with nonempty
nontrap support; its annotation and singleton rewards may be signed.
`exactRootSuccessor_mem_singletonLowerBoundary_of_pairPremiumCore_strictLeave`
(`UniformEquilibrium/Quitting/Classification/QuittingPremiumCoreStrictLeave.lean`)
uses the actual pair core, nonnegative participant premiums, strict leave
preference, and only the first annotation floor. Every absorbing exact root
returns above all singleton floors with an active binding coordinate.
This is a lower-boundary return, not a full bounded-L return, a smooth-potential
exclusion, or a uniform-equilibrium theorem for all cores of size at most two.
`not_isQuittingFullExactRootPotential_of_protectedSingletonReturnDomain`
(`UniformEquilibrium/Quitting/Projective/ProtectedSingletonReturnDomainSmoothDrift.lean`)
excludes a full potential under an explicit compact return region between
the singleton boundary and its protected sublevel domain. It requires
continuity only on that region, differentiation only on the singleton boundary,
and root return from every boxed protected annotation. The signed displacement
and endpoint bounds give charge `3 * M + bound`.
`not_isQuittingFullExactRootPotential_of_commonLeaver_strictLeave`
(`UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaverSmoothDrift.lean`)
supplies the actual signed adapter: only the protected player's participant
premiums are nonnegative, all premium traps contain that player, and strict
leave comparisons hold on the nonempty remaining-core coalitions. Other
participant premiums may be signed. The regularity conditions are continuity
on the protected return domain and differentiability on the singleton lower
boundary.
`weakPeeling_iff_every_boxedExactRoot_singletonLowerBoundary`
(`UniformEquilibrium/Quitting/Classification/NonnegativePremiumBoxBoundary.lean`)
proves the converse under nonnegative own premiums on every box strictly
larger than a reward bound. Failure of peeling constructs an actual absorbing
exact root whose continuation lies in that box and whose successor is
strictly above every singleton and strictly below the upper bound.
`hasProductLowQuittingPremium_iff_weakSupportPeeling_of_nonnegative`
(`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSupportPeelingConverse.lean`)
identifies product-low with weak support peeling when every participant's
own premium is nonnegative. The proof tests a literal half-hazard root on
each active support. This equivalence does not require nonnegative
singleton levels or restrict passive rewards.
The same module identifies this condition with supportwise balance and
positive-premium player ranking, and proves that every product-low table
failing supportwise balance has a strictly negative participant premium.

`not_differentiable_absorptionDrift_of_nonnegative_productLow`
(`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSmoothDrift.lean`)
excludes a differentiable potential with full absorption drift on all
absorbing exact Nash edges in a padded box. Differentiability at every box
point suffices; no continuously differentiable neighborhood or convexity is
assumed. Singleton levels may be signed. The same hypotheses give fixed-box
floor-free weighted packets at every positive tolerance and requested charge
for four players in
`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowForwardPackets.lean`.
The radius is one fixed reward bound plus two, independent of both requests.
These floor-free packets do not by themselves supply punishment floors.
`quittingPunishmentValue_eq_singleton_of_nonnegativePremium`
(`UniformEquilibrium/Quitting/Classification/NonnegativePremiumPunishment.lean`)
identifies the unrestricted behavioral punishment value with any nonnegative
singleton reward under nonnegative own premiums. Punishment normality at a
nonnegative singleton needs no premium-sign assumption, by
`isQuittingNormalPlayer_of_singleton_nonneg`
(`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`).
With nonnegative singleton rewards, the same fixed-radius packets acquire
punishment floors and yield a fixed uniform payoff through the weighted
packet consumer in
`UniformEquilibrium/Quitting/Classification/NonnegativePremiumForwardPacketConsumer.lean`.
This route does not use the periodic approximate-equilibrium producer.

`quittingTerminalSemanticDebt_prefix_le_auxiliaryNashDefect`
(`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`) extends the
auxiliary-continuation coordinate debt bound to arbitrary roots with their
literal coordinate Nash defects. Its common-shift sum is
`quittingTerminalSemanticDebtSum_prefix_le_auxiliaryNashDefect`
(`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDefectBudget.lean`).
`UniformEquilibrium/Quitting/Root/BelowSingletonRootAbsorption.lean`
gives exact and approximate absorption floors when one continuation
coordinate lies below its singleton. These are one-step bounds, not
recurrence hypotheses supplied by the game.
`UniformEquilibrium/Quitting/Terminal/PayoffExclusionStrictDeficitStep.lean`
applies them to a strict singleton deficit, with separate exact and
approximate root-defect budgets.
`quittingStrictDeficitExactWords_step`
(`UniformEquilibrium/Quitting/Paths/StrictDeficitFiniteWords.lean`)
constructs successive literal finite words followed by all-Continue and
proves their per-step absorption floor and total-debt contraction.
Its strict-deficit hypothesis ranges only over finite-word profiles,
not all carrier points. The explicit geometric total-debt bound, convergence
to zero, and actual finite-word full behavioral approximate Nash selection
are in `UniformEquilibrium/Quitting/Paths/StrictDeficitFiniteWordRates.lean`.
The same module proves fixed uniform-payoff existence from a positive
finite-word deficit, without imposing singleton signs. Root selection is
noncomputable exact Nash selection; no rational algorithm or exact infinite
all-suffix equilibrium is asserted there.

`executableRationalStrictDeficitFirstWord_nash_and_length`
(`UniformEquilibrium/Quitting/Paths/ExecutableRationalStrictDeficitRates.lean`)
constructs rational words using approximate grid roots and a rational first-hit
search. The same word has total terminal-deviation debt below the requested
rational accuracy and length at most its selected phase. Its geometric debt
envelope uses the existing ordered-field recurrence lemmas; real convergence
is needed only in the termination proof. The exact source adapters in
`UniformEquilibrium/Quitting/Paths/ExecutableRationalStrictDeficitSource.lean`
restrict real finite-word or actual-profile deficit to the rational words,
with one positive margin fixed before accuracy selection. No recognition
algorithm for the source hypothesis or exact infinite all-suffix equilibrium
is supplied by these rational-selection modules.

`exists_strictDeficitExactSuffix_allTerminalNash`
(`UniformEquilibrium/Quitting/Paths/StrictDeficitExactSuffixNash.lean`)
adds the exact infinite conclusion when every singleton reward is
nonnegative: one common sequence of finite-word depths yields one root
sequence with exact terminal Nash at every suffix and a uniform initial
payoff. `exists_strictDeficitExactSuffix_payoffDiagonal`
(`UniformEquilibrium/Quitting/Paths/StrictDeficitExactSuffixDiagonal.lean`)
is the source-derived common-depth payoff and row limit. The finite-word
uniform-payoff result above does not require the singleton-sign assumption.

`exists_strictDeficitExactSuffix_sameProfile_quantitativeUniform`
(`UniformEquilibrium/Quitting/Paths/StrictDeficitExactSuffixHorizon.lean`)
retains that same diagonal, both limit families, Bellman values and every
literal suffix. The row absorption floor `A = gap/(4*M+gap)` gives prescribed
delivery error at most `M/(A*H)` at each positive horizon. Full behavioral
regret is bounded by that error plus `M` times the actual opponent live-tail
Cesàro error, with its Never mass subtracted. No opponent-only geometric
absorption is assumed. The same profile and actual suffix payoff work at
every positive accuracy. The quantitative join passes its silent named
check, the full default build and exhaustive production axiom audit.

`HasQuittingFiniteWordNonconcentratedGroupExclusion`
(`UniformEquilibrium/Quitting/Paths/GroupExclusionFiniteWords.lean`)
requires one fixed concentration bound and permits a different probability
weight at each literal finite-word profile. Under a bound strictly below
one, `quittingGroupExclusionExactWords_step` constructs successive exact
auxiliary roots and proves a quadratic debt decrease at every positive-debt
word. The absorption floor and one-step debt estimate are in
`UniformEquilibrium/Quitting/Terminal/GroupExclusionExactPrefixStep.lean`.
`UniformEquilibrium/Quitting/Paths/GroupExclusionFiniteWordRates.lean`
proves the explicit reciprocal rate, convergence of actual-word total debt
to zero, and terminal approximate Nash selection against unrestricted
behavioral deviations. Its fixed-uniform-payoff consequence requires only
the finite-word exclusion hypothesis and the concentration bound below one;
singleton signs are unrestricted. Root selection is exact and noncomputable;
rational grid selection is a separate construction.

`executableRationalGroupExclusionFirstWord_nash_and_length`
(`UniformEquilibrium/Quitting/Paths/ExecutableRationalGroupExclusionRates.lean`)
constructs a rational first-hit word with complete terminal-deviation debt
strictly below the requested accuracy. Its rational reciprocal envelope bounds the
first phase by the ceiling of its explicit constant divided by accuracy;
the same word has length at most that phase. Exclusion weights are used only
in the correctness proof, not computed by the selector. The actual-profile
and raw-calendar adapters are in
`UniformEquilibrium/Quitting/Paths/GroupExclusionFiniteWordSource.lean`.
These results do not recognize the exclusion hypothesis or construct an
exact infinite all-suffix equilibrium.

`hasQuittingActualNonconcentratedGroupExclusion_half_of_twoPairRewardBounds`
(`UniformEquilibrium/Quitting/Paths/TwoPairGroupExclusion.lean`) supplies the
group-exclusion hypothesis from finite reward-row bounds for two complementary
four-player pairs. The two pair-average singleton levels must be nonnegative;
the favorable-pair bound may have either sign. The theorem uses the actual
pair masses and joint Never mass, not a supplied mass inequality. Its raw
calendar counterpart delegates to the existing representation equivalence.
The stronger stopping-law estimate retains the square root of the joint
Never probability in the sum bounded by one; the resulting finite leftover
bound is in `UniformEquilibrium/Quitting/Paths/BehaviorFirstStoppingPairLaw.lean`.

`quittingBehaviorTwoPair_crossMassDeterminant`
(`UniformEquilibrium/Quitting/Paths/TwoPairCrossMassDeterminant.lean`) bounds
the product of the exact `{0,1}` and `{2,3}` first-quitter masses by the
product of the `{0}`, `{3}`, `{0,3}` mass sum and the `{1}`, `{2}`, `{1,2}`
mass sum. The independent-law theorem retains Never and ties without an
absorption or finite-support hypothesis.
`hasQuittingActualWeakSubsetExclusion_zero_one_of_crossMassBounds`
(`UniformEquilibrium/Quitting/Paths/TwoPairCrossMassRewardExclusion.lean`)
converts the literal reward-row bounds into actual weak exclusion on `{0,1}`;
the same file supplies its raw-calendar counterpart. The two designated
singleton levels and loss coefficients must be nonnegative, but the favorable
coefficients may have either sign. The product bound is retained. These
outputs feed the existing weak-subset finite-word and fixed-payoff consumers.

`Math.PairedAffine.exists_interior_hazards_all_playerGap_zero`
(`MathUE/PairedAffineClearedField.lean`) selects one simultaneous interior
hazard vector for paired affine equations from literal reward intervals.
The field is a multivariate polynomial on the whole coordinate space;
`MathUE/PairedAffineIntervalEstimates.lean` supplies its strict face bounds
and ordered-composition estimates. These are game-independent results.
An actual cyclic strategy and its finite-truncation caps require separate
game-semantic adapters. `UniformEquilibrium/Quitting/Root/PairedProductRoot.lean`
realizes the two-active-player root, identifies its payoff map and all
pure-response endpoints, and proves the inactive-player margin from the
specified reward bounds.
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean` represents an
ordered partition of the entire player set into pairs, constructs the
literal cyclic roots, and selects their hazards from the raw reward region.
`UniformEquilibrium/Quitting/Cycles/PairedCycleValues.lean` identifies the
actual cyclic continuation values with the selected affine values and
bounds every phase's payoff strictly above the singleton and at most
`21/10`.
`GameTheory.PairedCycle.exists_exact_allSuffix_uniformPayoff_of_rawRegion`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleEquilibrium.lean`) constructs
one interior hazard vector from the reward region and an ordered partition
into at least two pairs. The actual cyclic profile is exact terminal Nash
against unrestricted deviations at every literal suffix, and its actual
value at each initial phase is a uniform-equilibrium payoff. The proof
retains the strict inactive-player advantage and opponent-cycle absorption.
`GameTheory.PairedCycle.exists_one_hazards_all_finiteTruncations_of_rawRegion`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleFiniteSource.lean`) retains
that one hazard vector for all initial phases and all positive cycle counts.
After K complete cycles, prescribed payoff is `(1 - C^K) * v`, the full
response cap is `v`, and debt is `C^K * v`, where C is joint cycle survival.
The same truncations approach the fixed periodic target with geometric
error at most `(21/10) * (99/100)^(n*K)`. Exact finite-menu realization,
independent censoring, and the individual geometric stopping-law atoms
are proved in `UniformEquilibrium/Quitting/Cycles/CyclicFiniteMenu.lean`
and `UniformEquilibrium/Quitting/Cycles/PairedCycleStoppingLaws.lean`.
`UniformEquilibrium/Quitting/Cycles/PairedCycleFiniteHorizon.lean` bounds
the same infinite profile's delivery and every unilateral finite-average
deviation by `M*m/((1-(99/100)^(n-1))*H)`. It also proves summability
and the corresponding bound on the live-time tail sum under every
deviation. The raw-region theorem selects one hazard vector before all
positive horizons and uses a bound covering every reward coordinate.
`UniformEquilibrium/Quitting/Cycles/PairedCycleFiniteMenu.lean` combines
the selected cycle's law, payoff, cap, debt, early-attainer and geometric
Nash conclusions for one actual finite menu.
`UniformEquilibrium/Quitting/Cycles/PairedCycleAffineTruncation.lean`
transports positive playerwise affine changes through the infinite cycle,
then truncates the transformed game afresh. The finite prescribed payoff
is the transformed infinite value multiplied by the absorption probability;
there is no unqualified translation identity for its positive Never mass.
For each queried player, the exact finite-cap identity holds if and only
if the transformed initial cyclic value is nonnegative. Under that
condition the exact debt identity holds as well. Nonnegative transformed
singletons are sufficient but unnecessary.
`UniformEquilibrium/Quitting/Cycles/PairedCycleAffineEquilibrium.lean`
states exact terminal Nash at every suffix and the fixed transformed
uniform payoff for the actual infinite profile. Positive scales suffice;
shifts and transformed singleton signs are unrestricted for that result.
`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Pivot.lean` fixes the
ordered pairs `{0,2}`, `{1,3}` and divides only the pivot coordinate by
its singleton, shifting the others without rescaling. Its transformed
initial value is at most `5/3` at the pivot and `6/5` elsewhere.
`fin4PivotValue_gt_singleton_of_selected`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Menu.lean`) proves
that this same transformed value strictly exceeds the canonical singleton
vector `(1,0,0,0)`.
`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Menu.lean` constructs
one menu from the selected hazards, with exact transformed payoff/cap
coordinates and full exploitability at most `(5/3)*(99/100)^(4*K)`.
That same menu satisfies both the restricted-menu and extra late-pivot
inequalities.
`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Source.lean` selects
one hazard vector and one entire menu family from the raw region, before
the accuracy quantifier. The geometric estimates hold at every positive
cycle count; for each accuracy all sufficiently long members of that
same family satisfy both inequalities.
`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Repair.lean` retains
each menu's actual nonpivot laws, obtains a minimizing feasible pivot
repair with no larger geometric regret, and supplies the existing
small-pivot-repair source.
`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Infinite.lean` identifies
the same selected hazards' transformed infinite profile, its exact terminal
Nash property at every suffix, and its fixed uniform-equilibrium payoff.
`UniformEquilibrium/Quitting/Cycles/PairedCycleClassSeparation.lean` proves
that the raw paired region fails product-low quitting premiums and
finite-word weak exclusion. The latter uses one sufficiently long literal
finite truncation whose payoffs exceed every player's singleton.
`UniformEquilibrium/Quitting/Cycles/PairedCycleRegionCenter.lean` and
`UniformEquilibrium/Quitting/Cycles/PairedCycleOpenRegion.lean` give an
explicit center table and a nonempty open subset of the full reward space
satisfying the paired hypotheses. Coordinates not mentioned in those
hypotheses remain unrestricted.
`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Chart.lean` identifies
the canonical singleton affine space with 56 independent real coordinates.
`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4OpenRegion.lean` gives
a nonempty relatively open subset in that space, supplies a literal raw
paired preimage for every point, and proves the small-pivot-repair source
property throughout it.

`exists_first_solo_capThreshold_hit`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticSoloCapThreshold.lean`)
constructs the first cap crossing for repeated solo prefixes of a strictly
preempted owner, assuming all initial cap margins exceed the chosen threshold.
It retains the distinct crossing player, logarithmic step bound, exact
payoff/cap formulas, and total-debt bound by the maximum of source debt and
owner cap margin. The affine formulas hold through the first hit only.
The same module realizes these iterates by literal repeated-root words
over the unchanged source profile; cap attainment is not assumed.
`exists_literal_capThreshold_block_debtSum_le_quadraticDrop`
(`UniformEquilibrium/Quitting/Paths/FiniteSoloCapThresholdDescent.lean`)
attaches an internally selected auxiliary exact Nash row when needed and
constructs the complete finite word. Its total-debt bound is
`C - 3 * C ^ 2 / (32 * M + 6 * C)`, where `C` is the maximum of the old
debt and owner cap margin, and its length is at most one plus the explicit
solo horizon. This is not necessarily descent below the old debt when the
owner cap margin is larger, and does not itself supply a repeatable
weak-exclusion selector.
`UniformEquilibrium/Quitting/Root/RationalApproximateQuittingRoot.lean`
proves existence of rational product roots with arbitrarily small total
Nash defect, allowing real reward and continuation data.
`UniformEquilibrium/Quitting/Paths/RationalAuxiliaryRootDebtDrop.lean`
uses this to produce a rational cap-threshold word with the same row bound
and decrease `3*C^2/(128*M+24*C)`, assuming the derived solo hazard is
rational. These are noncomputable existence results, not executable
rational grid search or a finite-source cap-evaluation algorithm.

`rationalBooleanRootGridSearch_isSome_of_pos`
(`UniformEquilibrium/Finite/RationalBooleanRootGrid.lean`)
proves that an executable exhaustive rational grid search succeeds for every
positive rational accuracy and finite rational Boolean payoff table.
`rationalBooleanRootGridSelector_totalNashDefect_le` bounds the sum of
positive player regrets of the selected product row by that accuracy.
The search uses rational arithmetic and an explicit finite list; its
success proof uses exact mixed-Nash existence and a rounding estimate.
`rationalQuittingRootGridSelector_totalNashDefect_le`
(`UniformEquilibrium/Quitting/Root/RationalQuittingRootGridSelector.lean`)
packages that search result as a rational quitting root and bounds its
actual total Nash defect at the supplied rational continuation payoff.
Coordinate and total defect identities identify the rational acceptance
quantity with the real game semantics.
`quittingTerminalSemanticPair_rationalFiniteWord_eq_cast`
(`UniformEquilibrium/Quitting/Root/RationalFiniteWordSemantics.lean`)
identifies the executable rational payoff/cap fold with the complete
semantic pair of its actual finite root stack followed by Always Continue.
The cap bounds all behavioral responses; its tail boundary is the maximum
of zero and the owner's singleton payoff. Together these supply root search
and exact finite-word evaluation.
`UniformEquilibrium/Quitting/Root/RationalFiniteSourceCapThresholdScan.lean`
adds an executable rational solo-row scan, its earliest threshold index and
a crossing player, with exact real semantic identities. Strict preemption
proves termination and the logarithmic row bound; the scan does not evaluate
real logarithms.
`rationalAuxiliaryRootGridSelector_debtSum_le_quarterQuadraticDrop`
(`UniformEquilibrium/Quitting/Paths/ExecutableRationalAuxiliaryRootDebtDrop.lean`)
proves that the selected rational auxiliary root lowers total semantic debt
to at most `C - 3*C²/(128*M + 24*C)` when the old debt is at most positive
`C` and one cap-to-singleton margin is at most `C/8`. Its search accuracy
controls total Nash defect.
`executableRationalCapThresholdBlock_length_and_debtSum_le`
(`UniformEquilibrium/Quitting/Paths/ExecutableRationalCapThresholdBlock.lean`)
combines the initial-low, solo-crossing, and auxiliary-root branches on the
actual rational source word, with the same debt bound and a literal row bound.
`UniformEquilibrium/Quitting/Paths/ExecutableRationalSelectedOwnerStep.lean`
selects an owner from a designated finite set using the source payoff
inequality, computes a maximum-gap preemptor, and supplies a common positive
rational preemption floor. The floor is literally the minimum, over designated
owners, of their maximum blocker gaps. Blocker selection itself requires only
the reward table and owner; only designated owners need preemption. The block
then lowers actual total debt by `3*D²/(128*M + 24*D)`.
`executableRationalSelectedOwnerFirstWord_debt_and_length_le`
(`UniformEquilibrium/Quitting/Paths/ExecutableRationalSelectedOwnerRates.lean`)
iterates these blocks and searches for the first phase below a positive
rational debt threshold. The same literal word satisfies the debt bound,
an executable rational-ceiling phase bound, and a fixed-table logarithmic row
bound using the common preemption floor. Real logarithms occur only in the
proved row bound, not in the computation. This does not supply the separate
reward-table-uniform accuracy-threshold algorithm.
`executableRationalSelectedOwnerFirstWord_actualDebt_nash_and_length_le`
(`UniformEquilibrium/Quitting/Paths/ExecutableRationalWeakSubsetSelection.lean`)
retains those same roots, phase and date bounds while proving their actual
unrestricted terminal approximate-Nash guarantee. The module also transports
real finite-word and actual-profile weak-subset hypotheses to the rational
selector; it does not decide these hypotheses.

`rationalFiniteSourceChargedWord_spec`
(`UniformEquilibrium/Quitting/Paths/ExecutableRationalChargedSourceStep.lean`)
computes an auxiliary rational root from the actual current word and its
charged cap margin. Its absorption and total-defect bounds give a uniform
positive debt expenditure at a fixed working accuracy. No selected root or
favorable cap vector is supplied.
`executableRationalPayoffDebtThresholdWord_ledger`,
`executableRationalPayoffDebtThresholdWord_endpoint`, and
`executableRationalPayoffDebtThresholdWord_finiteLaws`
(`UniformEquilibrium/Quitting/Paths/ExecutableRationalPayoffDebtThresholdBlock.lean`)
instead stop solo prefixes at the first actual payoff/debt hit. They retain
the exact old word, all-prefix debt nonincrease, the logarithmic date bound
and the same word's independent rational finite/Never laws and full semantic
pair. A nonterminal hit supplies the next actual charged source. Failure of
the positive-column test is not treated as strict preemption.
`rationalPositiveSingletonColumnExitWord_debt_and_delivery`
(`UniformEquilibrium/Quitting/Paths/RationalPositiveSingletonColumnSource.lean`)
computes a fresh finite solo exit from the actual reward table, with total
debt and delivery bounds to its actual singleton-column target. Only the
selected owner's singleton must be nonnegative; outsiders may have signed
rewards. The working-rate variant retains the original requested exit
accuracy separately. These branch owners pass silent named builds.
`executableRationalWeakSubsetStage_spec`
(`UniformEquilibrium/Quitting/Paths/ExecutableRationalWeakSubsetStage.lean`)
combines them on the actual renewed source and proves termination and a
fixed-level date bound. It also passes its silent named check. The dyadic
aggregation now passes its separate silent named check:
`executableRationalWeakSubsetDyadicSelection_length_le_absolute`
(`UniformEquilibrium/Quitting/Paths/ExecutableRationalWeakSubsetDyadicSelection.lean`)
bounds dates by `1000000 * (n + (M / accuracy)^2 * log(16*n*M/accuracy))`.
The same computed word has full terminal debt at most the requested accuracy
and exactly realizing independent finite/Never laws. It runs the initial
M-stage even at equal debt and retains a positive-column exit at the original
accuracy through every later level. Only designated owners need nonnegative
singleton rewards; exclusion is required only for rational finite words.
`exists_uniformEquilibriumPayoff_of_rationalFiniteWordOwnerExclusionOn`
(in the same module) feeds these profiles to the fixed-target consumer.
The fixed real target is not computed. These modules also pass the full silent
default build and exhaustive production axiom audit.

`quittingSelectedOwnerExactWordDebt_reciprocal`,
`executableRationalSelectedOwnerDebt_reciprocal`, and
`executableRationalSelectedOwnerWord_actualDebt_reciprocal`
(`UniformEquilibrium/Quitting/Paths/SelectedOwnerReciprocalEnvelope.lean`)
pass their silent named check. They expose the reciprocal envelope for the
existing real and computed rational renewals at every phase, retaining zero
initial debt and the actual complete-response debt of the same rational word.
The respective constants are `(32*M + 6*initialDebt)/3` and
`(128*M + 24*initialDebt)/3`; no successful phase or replacement source is input.

`quittingGroupExclusionExactWordDebt_half_raw_reciprocal` and
`executableRationalGroupExclusionDebt_half_raw_reciprocal`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarHalfGroupExclusionRates.lean`)
retain the actual exact and executable words from raw group exclusion at cap
one half. Their constants are `32*M + 3*initialDebt` and
`128*M + 15*initialDebt`, respectively, including zero initial debt. They
compose the existing recurrence owners; no favorable word is supplied.

`executableRationalWeakExclusionTwoBranchWord_finiteLaws`
(`UniformEquilibrium/Quitting/Paths/RationalWeakExclusionTwoBranchSelection.lean`)
tests preemption internally, then chooses the actual rational solo exit or
the existing selected-owner renewal. Every positive rational accuracy is
allowed, including zero initial debt and accuracy above the reward bound.
Its all-preempted branch retains the reciprocal phase and logarithmic date
bounds. The exact independent finite/Never laws realize the computed word's
whole payoff/cap pair, not a replacement payoff-only profile.
`executableRationalWeakExclusionTwoBranchWord_finFour_menu_and_latePivot`
(`UniformEquilibrium/Quitting/Paths/FinFourRationalWeakExclusionFiniteMenu.lean`)
controls both menu and late-pivot errors on these same laws when the own
singleton vector is `(1,0,0,0)`. The real-table counterpart is
`exists_finFour_finiteWordMenu_errors_le_of_weakExclusion`
(`UniformEquilibrium/Quitting/Paths/FinFourWeakExclusionFiniteMenu.lean`);
it selects a real word internally with no preemption or rationality premise.
Both retain full terminal Nash and signed finite-horizon delivery and regret
bounds. These modules pass silent named checks, the full default build and
exhaustive production axiom audit.

`UniformEquilibrium/Quitting/Examples/CapThresholdFinFour.lean`,
`UniformEquilibrium/Quitting/Examples/CapThresholdFinThree.lean`, and
`UniformEquilibrium/Quitting/Examples/CapThresholdInitialSkip.lean` pass
silent named checks. They retain the literal reward tables and old source
words. The first two identify the first cap hits at 59 and 30 and the exact
through-hit full-debt ledgers; the signed second example has increasing debt.
The third takes the initial below-singleton skip branch and retains its
zero-debt auxiliary prefix of the original source. None exhibits a positive
semantic minimum or permits affine cap extrapolation beyond the first hit.

`exists_owner_payoffMargin_le_actualSingletonSurplusEnvelope`,
`exists_minimumTerminalSemanticDebt_le_sqrt_actualEnvelope_nonnegativeSingleton`, and
`exists_minimumTerminalSemanticDebt_le_sqrt_actualEnvelope_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticActualPayoffEnvelope.lean`)
pass their silent named check. The envelope is literally the nonnegative part
of the supremum, over actual behavioral profiles, of their minimum singleton
surplus. Its boundedness and each actual owner witness are proved internally.
The minimizing semantic pair is also selected internally. The signed Fin4
facade has no singleton-sign restriction; the general finite-player facade
requires nonnegative singleton rewards. Neither accepts a favorable envelope
or a payoff realizer, nor bounds the debt of an arbitrary carrier point.

`exists_finiteWord_debtSum_le_of_weakExclusion_allPreempted`
(`UniformEquilibrium/Quitting/Paths/FiniteWordWeakExclusionDescent.lean`)
does renew the source when every owner has a strict preemptor and every
actual finite-word profile has some owner's payoff at most its singleton.
It constructs a literal finite word with arbitrarily small total debt,
including for signed singleton rewards. The proof obtains the common
preemption floor internally. The same module proves fixed uniform-payoff
existence under these two hypotheses, without an external reward-bound
parameter. `UniformEquilibrium/Quitting/Paths/FiniteWordWeakExclusionRates.lean`
uses the same selected words for the reciprocal phase bound and the total
date bound, including the logarithmic cost of each phase.
The all-owner interface delegates to
`UniformEquilibrium/Quitting/Paths/FiniteWordSelectedOwnerRates.lean`, whose
single recurrence retains an eligible owner, that same owner's source payoff
inequality, its strict preemptor, and each literal block length.
`exists_finiteWord_selectedOwner_quadraticDebtStep`
(`UniformEquilibrium/Quitting/Paths/FiniteWordSelectedOwnerStep.lean`)
needs only the specified owner's local payoff and preemption inequalities,
not a global weak-exclusion hypothesis. Eligibility can restrict the witnesses to a designated
set without requiring preemption outside that set.
`UniformEquilibrium/Quitting/Paths/FiniteUnpreemptedSoloExit.lean` constructs
arbitrarily accurate finite solo words when an owner is unpreempted and
that owner's singleton reward is nonnegative. The theorem
`exists_finiteWord_debtSum_le_of_nonnegative_unpreemptedDesignatedOwner`
allows signed outsider singleton rewards and retains the geometric-tail
debt estimate. The globally nonnegative specializations delegate to it.
Combining the globally nonnegative alternatives,
`exists_uniformEquilibriumPayoff_of_weakExclusion_nonnegativeSingleton`
(`UniformEquilibrium/Quitting/Paths/FiniteWordWeakExclusionSelection.lean`)
requires only finite-word weak exclusion and nonnegative singleton rewards.
These are real-table existence constructions; rational grid algorithms
are not supplied by these results.
`UniformEquilibrium/Quitting/Paths/WeakExclusionSinglePivotFiniteMenu.lean`
deduces arbitrarily accurate canonical single-pivot menus above any
prescribed deadline, for any finite player set. This existence corollary
does not assert preservation of a particular selected word or its
quantitative length bound.
`exists_finiteDeadlineTimingProfile_literalRootStack_exact`
(`UniformEquilibrium/Quitting/Root/LiteralFiniteWordMenuRealization.lean`)
realizes any literal finite root word over Always Continue on any menu
whose deadline is at least the word's length. It preserves each player's
actual stopping law and the full prescribed-payoff/response-cap pair.
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineHorizonError.lean`
bounds prescribed terminal/finite-average error by `M*N/H` for a menu
with deadline N. With nonnegative singleton rewards it bounds every
unilateral finite-average payoff above by terminal payoff plus `M*N/H`.
A terminal D-Nash menu is therefore horizon Nash with error
`D + 2*M*N/H`, including at deadline zero.
`exists_singlePivot_selectedFiniteWordMenu_errors_and_length_le`
(`UniformEquilibrium/Quitting/Paths/WeakExclusionFiniteWordMenuRate.lean`)
retains one quantitative weak-exclusion word and its actual menu, under
the strict-preemption and canonical-singleton hypotheses. That same
witness satisfies the explicit length bound, full terminal Nash bound,
both canonical menu inequalities, and every positive-horizon Nash bound.
The menu realization does not reselect the word or discard its rate.

`exists_finFour_selectedWord_pivotRepairMinimizer_of_rawPayoffExclusion`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarSelectedWordPivotRepair.lean`)
internally selects one real word from accepted strict, group, or weak-subset
exclusion, then produces the canonical pivot-repair optimizer for that word's
same nonpivot laws. Its optimum is at most the word's full total debt, which
is strictly below the requested error. Every marginal law and the full
payoff/cap pair are retained. The pivot is arbitrary; an unused padded date
handles an empty word without changing its laws. No claim that an arbitrary
pivot replacement preserves outsider debt is made.

`CrossMassDeterminantFixture.exact_word_pair` and
`exactValue_isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Examples/CrossMassDeterminantFixture.lean`)
retain the literal fifteen-row reward-bound-21 table and actual payoff and
complete cap `(53/33,-20/11,2/3,14/11)`. Its strict-deficit and group-exclusion
failures, raw unit-level comparisons and correlated-hull separator failure
are separate checked statements; a correlated lottery is not an independent
strategy law. `CrossMassPayoffThresholdRegression.executable_index_eq`
(`UniformEquilibrium/Quitting/Examples/CrossMassPayoffThresholdRegression.lean`)
proves the first actual payoff/debt crossing is exactly 155 for the original
two-row source tail. Its final 158-date word has zero full debt. This is not
a first-cap-crossing assertion or a reset to a zero continuation.
`TwoPairCrossMassSharpProfiles.actual_determinant_eq`
(`UniformEquilibrium/Quitting/Paths/TwoPairCrossMassSharpProfiles.lean`)
attains the determinant and square-root mass boundaries with actual independent
laws, including both closed parameter endpoints. The all-Never boundary is
handled separately. `SignedTwoPlayerExactNashNonattainment.not_exact_terminal_nash`
(`UniformEquilibrium/Quitting/Examples/SignedTwoPlayerExactNashNonattainment.lean`)
excludes exact terminal Nash for every parameter strictly between zero and one
and every behavioral profile; it does not exclude approximate or uniform
equilibrium. These additions pass silent named checks.

`exists_sparseFiniteStoppingLawMixture_wholePayoff_eq`
(`UniformEquilibrium/Quitting/Paths/SparseWholePayoffFiniteMixture.lean`)
replaces a finite mixture of one player's strategies using at most the
number of players plus one original positive-support generators. It
preserves every observer's prescribed terminal payoff simultaneously.
This is a payoff-only replacement: it does not preserve response caps,
compress all players at once, or produce a common finite calendar.
`exists_sparseFiniteStoppingLaw_wholePayoff_eq`
(`UniformEquilibrium/Quitting/Paths/SparseWholePayoffFiniteStoppingLaw.lean`)
specializes that construction to independent finite clock laws, retaining
the original positive-support dates and every observer's payoff against
the current opponents.
`UniformEquilibrium/Quitting/Paths/CommonStoppingCalendarRetiming.lean`
separately ranks the union of finite support dates using one common map,
preserving the independent first-quitter outcome law, ties, and Never.
If each marginal has at most n+1 support points, the retimed finite dates
are below n(n+1).
`UniformEquilibrium/Quitting/Paths/SparseWholePayoffFiniteStoppingProfile.lean`
performs successive current-opponent replacements and common retiming for
arbitrary finite independent clock laws. The output preserves the entire
payoff vector, has at most n+1 support points per marginal, and uses finite
dates below n(n+1).
`quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffClosure.lean`)
identifies the entire actual behavioral terminal-payoff set with the
fixed n(n+1)-date timing game's payoff image and proves that set compact.
Every payoff in its closure has an exact realization with at most n+1
support actions per player and finite dates below n(n+1). The proof
compactifies in the full finite simplex and recompresses the limit;
no response-cap preservation is asserted.
`forall_finiteRootWordPayoff_iff_forall_actualTerminalPayoff`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarFiniteWordPayoffEquivalence.lean`)
also identifies the predicates satisfied by all finite-root-word payoffs
with zero tail and by all actual behavioral terminal payoffs. The module
constructs a chronological root word from each finite-calendar profile,
proves literal profile equality with that word followed by Always Continue,
and connects the fixed-calendar and finite-word payoff images. Arbitrary
payoff predicates are allowed; response caps are not being compressed.
`EqualPayoffDifferentBehavioralCaps.equal_terminalPayoff_and_different_playerZero_responseCaps`
(`UniformEquilibrium/Diagnostics/Quitting/EqualPayoffDifferentBehavioralCaps.lean`)
gives two actual four-player chronological profiles with the same zero
payoff vector but player-zero response caps one and zero. The caps range
over unrestricted behavioral responses.
`exists_mem_quittingFiniteOpponentAtomGapReplyMenu_payoff_eq_cap`
(`UniformEquilibrium/Quitting/Terminal/FiniteOpponentAtomGapReplyMenu.lean`)
attains the full behavioral cap against opponents supported on an arbitrary
finite calendar. Its concrete menu contains Never, zero, the calendar's
atoms, and their immediate successors. The responder's original law is
unrestricted. This is a complete reply scan for the fixed opponents, not a
claim that compressing their payoff preserves their response caps.
`exists_mem_quittingFiniteOpponentAtomGapReplyMenu_actual_payoff_eq_cap`
in the same file gives the corresponding actual-profile theorem through
canonical stopping-law reconstruction. The menu preserves terminal payoffs,
not arbitrary clock evaluations.
`image_fst_quittingTerminalSemanticCarrier_eq_actualPayoffSet`
(`UniformEquilibrium/Quitting/Paths/TerminalSemanticPayoffProjection.lean`)
identifies the prescribed-payoff projection of the full semantic carrier
with that actual payoff set. Any predicate on payoff vectors can therefore
be tested equivalently on the fixed calendar or on every carrier point's
prescribed coordinate; the predicate needs no regularity assumption.
The realizing profile need not have the carrier point's response caps.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPayoff.lean` identifies
the displayed finite sums and products for first-quitter coalition mass,
Never mass, and prescribed payoff with the actual independent stopping-law
semantics. The masses sum to one.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPolynomial.lean`
represents the coalition masses and fixed-table prescribed payoffs by
multivariate polynomials and identifies their evaluations with those
semantic formulas. Their degree is at most the number of players.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarJointPolynomial.lean`
treats reward entries and calendar probabilities as separate variable
blocks. Joint payoff and singleton-surplus polynomials have degree at
most the number of players plus one; their evaluations agree with the
existing raw payoff formulas. Never mass has its own polynomial.
`isSemialgebraic_quittingActualTerminalPayoffSet`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffSemialgebraic.lean`)
proves that all actual prescribed payoffs form a semialgebraic set for
nonempty `Fin n` and arbitrary real rewards. It identifies the actual set
with the polynomial image of the literal finite-calendar simplex; it does
not represent response caps.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPredicates.lean`
transports arbitrary payoff predicates between the raw fixed-calendar
formulas and all actual behavioral profiles. It instantiates this
equivalence for weak exclusion on a designated nonnegative-singleton
subset, strict singleton deficit with a fixed margin, and nonconcentrated
group exclusion with a fixed weight cap. Compactness also makes strict
pointwise singleton exclusion equivalent to one positive uniform deficit.
`exists_uniformEquilibriumPayoff_of_actualWeakSubsetExclusion` and
`exists_uniformEquilibriumPayoff_of_finiteCalendarRawWeakSubsetExclusion`
(`UniformEquilibrium/Quitting/Paths/FiniteWordWeakSubsetSelection.lean`)
give the uniform-equilibrium-payoff consequence for any finite player type.
Only designated owners need nonnegative singleton rewards; other rewards may
have either sign. The exclusion assumption itself implies that the designated
set is nonempty. The same module constructs literal finite-word approximate
Nash profiles against unrestricted behavioral deviations, already from
exclusion on finite words alone. In the all-designated-preempted branch,
`exists_designatedBlockerCertificate_forall_epsilon_finiteWord_length_le`
chooses one actual preemption certificate before all positive accuracies
and bounds the resulting word lengths. That bound depends on the fixed
table's preemption gap, not only the reward bound and requested accuracy.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarWeakSubsetMaximalOwners.lean`
proves that a successful owner set can be enlarged to all players with
nonnegative own-singleton rewards, and gives the corresponding existence
equivalence. `UniformEquilibrium/Quitting/Paths/FiniteCalendarRawRejectionWitnesses.lean`
states the exact real-calendar rejection alternatives. For group exclusion,
every admissible common weight has a counterprofile; the profile may depend
on the weight. These are existence statements, not witness-extraction algorithms.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawAlgebraicRejectionWitnesses.lean`
strengthens strict and weak-subset rejection for rational reward tables:
the counterprofile can have algebraic coordinates. Weak rejection retains
the alternative that a designated owner's singleton reward is negative.
These theorems do not extract an encoded counterprofile.
`exists_uniformEquilibriumPayoff_of_finFour_signFreeWeakSubsetExclusion`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourSignFreeWeakSubsetUniformPayoff.lean`)
removes the singleton-sign condition for four players. Its assumption is
literal actual-payoff exclusion on the designated set; a raw twenty-date
form is also provided. It uses the four-player strict-minimum plateau and
exact payoff projection, without transferring the plateau's response caps.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarPurePoints.lean` supplies
literal All-Never and pure-coalition simplex points, with exact mass and payoff
evaluations on any finite calendar. These evaluations do not preserve caps
under compression.
`exists_finiteCalendarRawNonconcentratedGroupExclusion_iff_orderedPair`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarOrderedPairGroupExclusion.lean`)
reduces group exclusion to distinct ordered pairs with one positive
parameter at most one half, chosen before the calendar point. The pair
may depend on that point. The same module proves the actual-profile form.
`isSemialgebraic_quittingRewardTables_rawStrictExclusion` and
`isSemialgebraic_quittingRewardTables_rawWeakSubsetExclusion`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarRewardTableSemialgebraic.lean`)
prove semialgebraicity of the accepted real reward-table sets themselves.
The weak-subset test retains its nonnegative-own-singleton requirement.
`isSemialgebraic_quittingRewardTables_rawNonconcentratedGroupExclusion`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarGroupRewardTableSemialgebraic.lean`)
gives the corresponding accepted-table set for group exclusion, preserving
one uniform positive parameter before the universal calendar quantifier.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarReciprocalParameterRecovery.lean`
proves that strict-deficit and ordered-pair parameters can be chosen as
positive rational reciprocals.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarReciprocalParameterDecision.lean`
provides exact Boolean tests at a supplied rational deficit or ordered-pair
weight. The chosen parameter is fixed before all calendar coordinates.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarReciprocalSearch.lean`
uses these tests in terminating searches for rational reward tables. Strict
search returns the first positive denominator; group search starts at two.
Each result supplies the exact raw predicate at its reciprocal, and `none`
is equivalent to failure of the corresponding exclusion property. The proof
gives termination and minimality, not an a priori denominator bound.
Literal accepted-source joins are
in `UniformEquilibrium/Quitting/Paths/FiniteCalendarAcceptedSelectorSources.lean`:
`rationalFiniteWordOwnerExclusion_and_signs_of_rawWeakSubsetDecision` supplies
the designated signs and actual rational-word source from Boolean acceptance;
the strict and group reciprocal joins retain the returned denominator and
its exact raw predicate. These joins pass silent named checks.
`executableRationalFiniteCalendarRawWeakSubsetSelection_finiteLaws_and_bound`
(`UniformEquilibrium/Quitting/Paths/RationalFiniteCalendarWeakSubsetSelection.lean`)
retains the computed word, exact independent finite/Never laws, full payoff/cap
pair and absolute date bound from the literal raw-calendar source.
`exists_finFour_finiteWord_exactLaws_of_rawPayoffExclusion`
(`UniformEquilibrium/Quitting/Paths/FinFourRawPayoffExclusionFiniteLaws.lean`)
selects an actual real word internally from any of the three accepted raw tests
and realizes that same word's laws and full pair with strict debt below error.
Its fixed-target corollary does not compute the target. These modules pass
silent named checks and the full integration gate.
`exists_finiteCalendarRawStrict_sameProfile_quantitativeUniform`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarStrictDeficitSuffixHorizon.lean`)
internally supplies the common positive raw margin and retains both original
diagonal families, all exact-Nash suffixes and their same-profile uniform
targets. This exact-suffix conclusion requires all own singletons nonnegative.
`exists_actualGroupExclusion_of_nonnegativeWeightChamber`
(`UniformEquilibrium/Diagnostics/Quitting/NonnegativeWeightChamberGroupExclusionSource.lean`)
normalizes the same fixed table weight; two positive coordinates make its cap
strictly below one. It needs only the weighted singleton sign, not individual
singleton signs. Both modules pass silent named checks.

`UniformEquilibrium/Quitting/Paths/FiniteCalendarStrictDeficitGroupWeakImplications.lean`
proves strict deficit implies group exclusion, deriving the required distinct
players from the deficit assumption itself. With nonnegative own singletons,
group exclusion implies weak exclusion on all players. Both actual-profile
and raw-calendar forms are provided.
`decideHasQuittingFiniteCalendarRawStrictExclusion_eq_true_iff`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawStrictDecision.lean`)
proves correctness of executable strict-exclusion recognition for rational
tables with a nonempty finite player set. The Boolean procedure universally
quantifies every calendar coordinate and accepts exactly the canonical raw
strict-exclusion predicate. It decides this sufficient condition, not
uniform-equilibrium existence.
`decideHasQuittingFiniteCalendarRawWeakSubsetExclusion_eq_true_iff`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawWeakSubsetDecision.lean`)
provides rational weak-subset recognition, including its designated singleton
sign condition and equality cases.
`decideExistsQuittingFiniteCalendarRawGroupExclusion_eq_true_iff`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawGroupDecision.lean`)
provides rational group-exclusion recognition. One positive pair weight is
chosen before the universal calendar quantifier; the distinct player pair
may vary with the calendar.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawParameterFormula.lean`
retains the reward entries as free coordinates in all three formulas, with
the same quantifier order and exact raw-predicate semantics.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawIsolatedRootDecision.lean`
provides the three corresponding executable tests for certified algebraic
reward entries. Each correctness theorem applies to every real table denoted
by the input. Algebraic coverage is existential; no algorithm encodes an
arbitrary unencoded real table. The reciprocal searches above take rational
reward tables, not general isolated-root inputs.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffFormula.lean` constructs
executable rational expressions for coalition masses, payoffs, and singleton
surpluses from supplied reward and calendar terms. Its simplex guard includes
every Never coordinate. Evaluation agrees with the raw semantic payoff map;
the caller must still bind the calendar variables and invoke elimination.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarFormulaCoordinates.lean` supplies the
deterministic coordinate terms and the two-way simplex encoding: every
guarded coordinate vector decodes to a genuine independent calendar profile.
`StrictDeficitAndZeroBoundaryTables.strictDeficitReward_has_actualStrictSingletonDeficit`
(`UniformEquilibrium/Quitting/Examples/StrictDeficitAndZeroBoundaryTables.lean`)
gives a concrete four-player table with uniform deficit margin one. The same
module proves that the zero table has no positive strict-deficit margin but
does satisfy group exclusion and weak exclusion on every nonempty subset,
with equality. These statements concern all actual behavioral profiles.
`UniformEquilibrium/Quitting/Examples/FiniteCalendarWeakExclusionBeyondGroupBoundary.lean`
gives weak exclusion on player zero's singleton owner set, but no group
exclusion with a cap strictly below one and no positive strict deficit.
The same pure-zero profile witnesses both failures and is exact terminal Nash.
`UniformEquilibrium/Quitting/Examples/FiniteCalendarPredicateFailureExactNashBoundary.lean`
gives a four-player table whose full-quitting profile is exact terminal Nash
against every behavioral deviation, while its payoff exceeds all singleton
rewards. It therefore refutes every positive strict-deficit certificate,
group exclusion for every weight cap, and weak exclusion for every subset.
These tests are sufficient conditions, not an equilibrium-existence decision.
`UniformEquilibrium/Quitting/Examples/FiniteCalendarGroupExclusionBeyondDeficitBoundary.lean`
gives a four-player table satisfying group exclusion with weight cap one
half, while strict singleton deficit and product-low premiums both fail.
The proof applies the actual first-stopping-pair square-root law and keeps
Never mass explicit. No nonzero nonnegative fixed weight bounds every
terminal row by the singleton benchmark, although the table has an exact
terminal Nash profile. The correlated midpoint used to refute fixed weights
is not asserted to come from an actual behavioral profile.
The [real quantifier-elimination library](REAL_QUANTIFIER_ELIMINATION.md)
supplies the shared elimination algorithm using its proved recursive
sign-diagram producer.
`eliminateQuantifiers_holdsAt_iff` and `decideClosedFormula_eq_true_iff`
(`MathUE/RealQuantifierElimination/QuantifierElimination.lean`) establish
truth preservation for arbitrary nested real quantification and correctness
of closed rational-formula decision. The game-specific predicate encodings
and semantic adapters remain necessary before using these endpoints for
raw-table recognition.

`IsSemialgebraic.image_coordinate_projection` and
`IsSemialgebraic.forall_coordinates`
(`MathUE/Semialgebraic/Projection.lean`) give projection and universal
quantification over any finite coordinate block for ordinary semialgebraic
sets with arbitrary real polynomial coefficients. The proof represents
finitely many coefficients as fixed real parameters, applies the concrete
eliminator, and substitutes them back. This is not an algorithm on
unencoded real-valued input tables, nor a finite-formula characterization
of uniform-equilibrium existence.

`StochasticGame.exists_analyticBellmanGerm_of_mem_closure_positiveDiscount`
(`UniformEquilibrium/VanishingDiscount/Bellman/SpecifiedEndpointGerm.lean`)
constructs an analytic Bellman germ through a supplied complete assignment
in the closure of positive-discount solutions, with discount coordinate zero.
Its endpoint equals that assignment literally; no curve-selection hypothesis
or action-nonemptiness assumption is required. The proof uses the existing
unconditional polynomial sign-cell arc theorem.

`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`
defines the discounted displacement and live value from the actual reward
table and product root. It proves the positive denominator, the exact
displacement/endpoint-gap identity, live Bellman consistency, uniform value
bounds from the reward box, and all three clipped-map face conditions.
These statements hold at the supplied root; no favorable fixed point is
selected.
`UniformEquilibrium/Quitting/Bellman/Discounted/PayoffBridge.lean`
owns the quitting-game discounted payoff identities used by both the lift and
the analytic boundary consumer.
`quittingDiscountedBellmanAssignment_of_hazard_fixedPoint`
(`UniformEquilibrium/Quitting/Bellman/Discounted/FixedPointLift.lean`)
lifts every supplied cube fixed point to a complete Bellman assignment for
the same reward table, retaining its live hazards and values.
`exists_analyticBellmanGerm_at_quittingDiscountedFixedPoint_limit`
(`UniformEquilibrium/Quitting/Bellman/Discounted/SpecifiedEndpoint.lean`)
constructs a germ through the full limiting assignment of an actual source.
`exists_analyticBellmanGerm_at_discountedFixedPoint_hazardCluster`
(`UniformEquilibrium/Quitting/Bellman/Discounted/ClusterCompletion.lean`)
needs only the supplied hazard cluster: compactness selects a compatible
value cluster along a nontrivial refinement of the same source.
`auxiliaryDiscounted_fixedPoint_sum_lt_of_no_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/AuxiliaryDiscountedLocalization.lean`)
then proves that, if the original game has no uniform-equilibrium payoff,
every sufficiently small positive discount has only small-total-hazard
fixed points in the cube for the canonical auxiliary reward table. The
threshold precedes both the discount and the fixed point. The proof handles
signed rewards through the existing original-game punishment consumer;
it requires neither normality nor an R0 or degree hypothesis. The degree
comparison below uses this source result.

`isStandardLCPSolution_of_quittingDiscountedFixedPoint`
(`UniformEquilibrium/Quitting/Stationary/DiscountedR0Localization.lean`)
rewrites every actual cube fixed point below the upper faces as a standard
LCP for its own singleton matrix. The right-hand side uses the literal
discounted-displacement remainder, and the slack is minus that displacement.
The same module bounds hazard divided by discount from an R0 matrix
hypothesis, a quadratic bound on that remainder, and a smallness condition.
These source hypotheses are explicit; the algebraic rewrite does not prove
them.
`abs_quittingRootExpectedPayoff_sub_singletonExpansion_le`
(`UniformEquilibrium/Quitting/Root/BernoulliExpectation.lean`)
gives the actual root's quadratic singleton-expansion error, retaining
separate tail and terminal-reward box constants. Its expectation identity
uses the existing reward extension and the supplied root's hazards.

`abs_quittingDiscountedSingletonRemainder_le`
(`UniformEquilibrium/Quitting/Stationary/DiscountedQuadraticRemainder.lean`)
supplies the literal discounted remainder bound from the actual reward box:
`4*M*(discount + totalHazard)²`, at every cube hazard and every nonnegative
discount complement. No fixed-point, small-hazard, or equilibrium hypothesis
is needed for this estimate. Its localization corollaries therefore need no
supplied remainder certificate.
`isR0Matrix_quittingSingletonMatrix_of_normal_of_no_uniformPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/PunishmentNormalR0.lean`)
proves the full original singleton matrix is R0 under all-player punishment
normality and absence of an original uniform payoff.
`quittingSingletonMatrix_sub_payoff`
(`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`)
proves invariance under playerwise terminal shifts. This matrix identity does
not assert strategic equivalence when Never still pays zero.
`finFour_auxiliaryDiscounted_fixedPoint_scaled_sum_lt_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`)
supplies one positive radius and discount threshold controlling total hazard
divided by discount, and every coordinate, for all actual auxiliary cube
fixed points of a four-player table with no original uniform payoff. The same
original-table contrary hypothesis supplies punishment normality and full R0;
matrix shift invariance transfers R0 to the actual auxiliary table. No
normality, remainder certificate, or selected fixed point is an input to this
Fin4 conclusion. The generic quantitative theorem in
`UniformEquilibrium/Quitting/Classification/AuxiliaryDiscountedQuantitativeLocalization.lean`
retains R0 as an explicit premise. Neither theorem supplies signed integer
degree.

`hasFDerivAt_quittingDiscountedDisplacement_zero`
(`UniformEquilibrium/Quitting/Stationary/DiscountedAmbientDerivative.lean`)
identifies the ambient derivative of the actual displacement from the cube
remainder and uniqueness of derivatives on that full-dimensional cube.
`tendstoUniformlyOn_quittingDiscountedDisplacement_scaled`
(`UniformEquilibrium/Quitting/Stationary/DiscountedUniformScaling.lean`)
then proves uniform convergence of minus displacement divided by discount
to the singleton-matrix affine map on every fixed bounded set of signed
scaled hazards. It needs no fixed-point or no-equilibrium premise. This
supplies the ambient comparison, not integer degree or its invariance laws.

`BoxComplementarityProblem.ofAmbientMap`
(`MathUE/Topology/BoxComplementarityAmbientMapAdapter.lean`) pulls an ambient
field through a positive rectangular chart and negates it to obtain the gain.
It requires continuity only on the closed rectangle. Interior complementarity
solutions are exactly ambient zeros. The same module proves isolation of the
pulled-back region from a zero-free frontier inside the open rectangle, and
identifies its selected solution set with the preimage of the ambient zeros.
These are chart-level statements, not chart independence or an identification
with ambient Brouwer degree. The generic problem and continuous-family
definitions reside in `MathUE/Topology/BoxComplementarityProblem.lean`.

`ambientDegree` and `ambientDegree_eq_of_extension`
(`MathUE/Topology/AmbientDegree.lean`) construct degree for an actual field
continuous on the closure of a bounded open region, at any target excluded
from the frontier image. The enclosing positive rectangle and continuous
extension are constructed internally; independence of both choices is proved.
Empty regions, zero dimension and nonisolated fibers are allowed.
`ambientDegree_homotopy`
(`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`) uses one jointly
continuous extension of the time-space field.
`ambientDegree_congr`, `ambientDegree_excision`, `ambientDegree_additive`
and `ambientDegree_id_eq_one` (`MathUE/Topology/AmbientDegreeProperties.lean`)
give closure extensionality, excision, root-cover additivity and identity
normalization on arbitrary admissible regions. These are the standard defining
properties of Brouwer degree; uniqueness against another implementation is
not proved. No finite-fiber or regular-value hypothesis is imposed.
`ambientDegree_lcpMinMap_zero_eq_r0Degree`
(`MathUE/LinearProgramming/R0AmbientDegree.lean`) identifies the canonical R0
integer with this ambient construction on every bounded open neighborhood
of the origin. The bounded-offset total-degree comparison, including the
literal offset minus one, is in `MathUE/LinearProgramming/R0AmbientOffsetDegree.lean`.

`Math.exists_compact_connected_fixedPoint_continuation`
(`MathUE/Topology/ConnectedFixedPointContinuation.lean`) produces an actual
compact connected subset of the fixed-point graph of a jointly continuous
interval-parameterized self-map of a nonempty compact convex set in a
finite-dimensional real normed space. The subset meets both endpoint fibers;
neither a spanning component nor isolated fixed points are supplied. Dimension
zero and compact convex sets with empty interior are allowed. Its component
separation owner is `Math.exists_isClopen_separator_of_no_common_component`
(`MathUE/Topology/CompactComponentSeparation.lean`). This is interval
continuation, not continuation over every connected compact parameter space
or an actual finite-game Nash decoder.

`Math.Probability.FiniteStoppingSimplex.stop_eq_conditional` and
`Math.Probability.FiniteStoppingSimplex.continuousOn_stop`
(`MathUE/Probability/FiniteStoppingSimplexReconstruction.lean`) expose the
canonical finite-simplex stopping law and conditional hazard. Finite and
Never atoms are preserved exactly, including empty calendars and exhausted
prefixes. Hazard continuity and strict upper bounds require positive Never
mass; continuity on the whole simplex is not asserted. The construction
reuses the canonical stopping-law reconstruction, not a second hazard engine.

The construction
`BoxComplementarityProblem.localDegree`
(`MathUE/Topology/BoxComplementarityStabilizedLocalDegree.lean`) gives an
integer for each isolating relatively open region of the unit cube, normalized
to one on the whole cube. It is `(-1)^n` times `BoxComplementarityProblem.rawLocalDegree`,
the literal eventual signed count.
`BoxComplementarityProblem.eventually_localSignedCount_eq`
(`MathUE/Topology/BoxComplementarityFloorRefinementSignedTransport.lean`)
proves that every sufficiently fine positive grid gives the same actual
anchor-selected signed count. The construction derives this equality from
coordinate-floor refinement and an actual solution-free frontier collar;
count invariance is not a premise.
`IsContinuousBoxComplementarityFamily.localDegree_endpoints_eq`
in the stabilized-degree file proves homotopy invariance for jointly
continuous families on a common isolating region.
`BoxComplementarityProblem.localDegree_univ_eq_one`
(`MathUE/Topology/BoxComplementarityMeshOneNormalization.lean`) proves
normalization from the actual unique mesh-one simplex, whose signed weight
is `(-1)^n`. The ambient affine comparison and game-specific consumer are
described below. No general regular-Jacobian or arbitrary-chart theorem is
assumed by that consumer.
`BoxComplementarityProblem.localDegree_union_of_disjoint` and
`BoxComplementarityProblem.exists_isolatingFrontierCollar_localDegree_coherent`
(`MathUE/Topology/BoxComplementarityLocalDegreeConsequences.lean`) give
disjoint-region additivity and excision within an actual frontier collar.
`BoxComplementarityProblem.exists_solution_mem_of_localDegree_ne_zero`
in the same file gives an actual solution in any isolating region of nonzero
degree, without requiring that relatively open region to be compact.
`BoxComplementarityProblem.localDegree_eq_of_gain_eqOn_frontier`
(`MathUE/Topology/BoxComplementarityFrontierReplacement.lean`) preserves
degree when the gain fields agree on the region frontier. The explicit
straight-line family supplies continuity and common isolation from just
one endpoint's isolation.

`BoxComplementarityProblem.localDegree_scaleGain` and
`BoxComplementarityProblem.localDegree_ofAmbientMap_dilation`
(`MathUE/Topology/BoxComplementarityPositiveRescalingDegree.lean`) preserve
normalized degree under positive gain scaling and under a translated positive
dilation with the displayed transformed field, rectangle, and region.
Positive scaling also preserves every actual grid label. The dilation result
uses the field `scalar⁻¹ * field(shift + scalar * point)` and derives equality
of the pulled-back problems up to positive scaling. It does not compare
arbitrary charts for an unchanged ambient field.

`completeSimplex_diagonalOrderedChain` and `signedWeight_diagonalOrderedChain`
(`MathUE/Topology/BoxComplementarityDiagonalChain.lean`) construct one
actual complete central simplex for a centered nonzero diagonal field and
compute its signed weight, including dimension zero. The negative
coordinates are ordered increasingly and the positive ones decreasingly;
the dimension label lies between the two groups.
`localCompleteSimplices_centeredDiagonal_eq_singleton` and
`localDegree_centeredDiagonal_eq_sign_det`
(`MathUE/Topology/BoxComplementarityDiagonalLocalIndex.lean`) prove uniqueness
in the central region and identify the normalized local degree with the
determinant sign.

`Math.LinearAlgebra.exists_path_diagonal_det_eq`
(`MathUE/LinearAlgebra/MatrixDiagonalDeterminantPath.lean`) constructs a
continuous determinant-preserving path from any real square matrix to a
diagonal matrix, including singular matrices and the empty index type.
It reuses finite transvection factorization. This supplies a matrix
deformation.
`localDegree_affineRootProblem_eq_sign_det`
(`MathUE/Topology/BoxComplementarityAffineLocalIndex.lean`) supplies the affine
local-degree comparison. `exists_finset_lcpMinBoxProblem_localDegree_eq_sum_sign_det`
(`MathUE/LinearProgramming/RootDegreeSum.lean`) constructs the complete finite
root set in a supplied isolating interior region and computes its total index
from active determinant signs when its actual roots are strictly complementary
and have nonsingular active matrices. These regularity assumptions serve
finite calculations; they are absent from the following existence criterion.

`r0Degree` (`MathUE/LinearProgramming/R0Degree.lean`) is the canonical integer
of the homogeneous minimum-complementarity map. The same module proves its
independence of positive scalar chart radius, equality with every bounded
offset family's degree on one sufficiently large central region, and
`isStandardQ_of_r0Degree_ne_zero`. These statements allow nonisolated roots.
`BoxComplementarityProblem.exists_solution_not_mem_closure_of_localDegree_ne_one`
(`MathUE/Topology/BoxComplementarityDegreeEscape.lean`) extracts an actual
solution outside the closure of any isolating region whose local degree differs
from the whole cube's degree one. Applying it to a quitting-game response
quotient still requires a source-specific local-degree calculation.
`r0Degree_quittingSingletonMatrix_eq_one_of_discounted_fixedPoint_localization`
(`UniformEquilibrium/Quitting/Stationary/DiscountedClippedDegree.lean`) derives
degree one from full R0 and a uniform scaled bound on every actual discounted
clipped fixed point. It compares shrinking regions in one fixed chart using
the actual source approximation, self-map normalization, and solution excision.
It includes dimension zero and supplies no localization assumption itself.

`singleton_r0Degree_eq_one_of_no_uniformPayoff` and
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one`
(`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`)
give the game-semantic criterion for every player count `Fin n`: full R0 and
degree different from one yield an original uniform payoff. Rewards may have
arbitrary signs. The actual auxiliary-source localization is derived from
original-game nonexistence, never from an assumed auxiliary-game nonexistence.
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`)
additionally derives full R0 itself from nonexistence in four players.
The general four-player conjecture remains open.

`exists_uniformEquilibriumPayoff_of_finite_support_degree_test`
(`UniformEquilibrium/Quitting/Classification/LCP/FiniteSupportDegreeCriterion.lean`)
turns finite tests on the literal singleton matrix into a uniform payoff for
any positive player count. Its inputs are a positive test anchor, one negative
entry in each column, nonsingular principals of size at least two, strict
inactive residuals on admissible inverse-principal candidates, and a support
determinant-sign sum different from one. The complete root inventory and R0
are derived. The anchor is not a strategic payoff target, and no reward
normalization is imposed.

`r0Degree_eq_sign_det_of_nonnegative_inverse`
(`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`) computes the degree
of an R0 matrix with entrywise nonnegative inverse as its determinant sign.
Zero inverse entries are allowed. The separate R0 premise cannot be dropped:
`CycleFourNonnegativeInverse.not_isR0Matrix`
(`MathUE/LinearProgramming/Examples/CycleFourNonnegativeInverse.lean`) gives
an invertible four-cycle matrix with nonnegative inverse and a nonzero
homogeneous LCP solution.
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse`
(`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`)
needs only negative determinant and nonnegative inverse of the raw singleton
matrix, for every player count at least three. It obtains strictly positive
inverses through literal reward-table approximation, applies the degree
criterion there, and uses reward closure to select one fixed original target.
`isR0Matrix_of_strictlyPositiveInverse`
(`MathUE/LinearProgramming/PositiveInverseR0.lean`) supplies R0 for the
approximating matrices; no arbitrary-player inference from nonexistence to
R0 is assumed. The four-player theorem in
`UniformEquilibrium/Diagnostics/Quitting/FinFourNonnegativeInverseCriterion.lean`
is a specialization. That file also retains the separate four-player result
for a singleton matrix that fails R0.

`exists_pos_strictlyPositiveInverse_sub_offDiagonalOnes`
(`MathUE/LinearProgramming/NonnegativeInverseApproximation.lean`) approximates
every invertible matrix with nonnegative inverse in dimension at least three
by subtracting a small positive multiple of the off-diagonal-ones matrix.
One threshold works for all smaller positive parameters: the actual inverse
is strictly positive, the determinant sign is unchanged, and the diagonal
is preserved. No zero-diagonal assumption is needed. The same module proves
that a zero-diagonal two-by-two matrix cannot have a strictly positive inverse.
The four-cycle module above certifies the exact one-twentieth perturbation
and shows why its first-order inverse correction alone is insufficient.

`exists_pos_strictlyPositiveInverse_singletonMatrix_rewardApproximation`
(`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseRewardApproximation.lean`)
realizes this matrix approximation by actual reward tables. It subtracts the
parameter only from off-own singleton coordinates, preserves own-singleton
and nonsingleton rewards, and bounds every reward change by the parameter's
absolute value. The matrix identity and the common positive threshold are
literal conclusions, not supplied compatibility assumptions.

`directedCycleMatrix_inverse`, `columnWeight_balances`, and
`prod_survivalFraction`
(`MathUE/LinearProgramming/ThreeCycleInverseFormulas.lean`) give the
canonical three-cycle inverse, its column-weight identities, and the product
of the three normalized survival fractions. The same module proves that
the fractions lie strictly between zero and one in the strict product-gap
chamber. These are finite algebraic identities, not a theorem about the
blocks of an arbitrary infinite quitting schedule.

`normalizedSingletonPathOfRootSequence`
(`UniformEquilibrium/Quitting/Paths/NormalizedSingletonPath.lean`) derives a
normalized singleton path from actual terminal continuation payoffs on an
arbitrary finite embedded child. Its inputs are absorbing solo play with
hazards below one, positive balancing weights, singleton floors, and exact
active-owner ties. It assumes neither periodicity nor finite owner blocks.
`quittingRootSequenceSingletonSurplus_eq_of_row_span` in the same file
transports signed linear relations among child singleton rows to actual
parent surpluses, without floor or tie hypotheses. The inverse-row
specialization uses the actual nonsingular child matrix.
`NormalizedSingletonPath.exists_first_owner_change`
(`MathUE/LinearProgramming/ThreeCyclePathRigidity.lean`) constructs a finite
owner change whenever every column has a negative coordinate. Its strict
three-cycle specialization forces cyclic changes.
`ThreeCycleInverseFormulas.exists_vertex_after` in the same file constructs
visits to every weighted simplex vertex after any starting date;
`dotProduct_nonneg_on_tail_iff` characterizes a signed row's nonnegativity
along a whole tail by nonnegativity of its coefficients.
`exists_vertex_after_with_survival_ge` in the same file gives these visits
with survival at least the product of the three canonical block fractions.
Finite owner blocks and the preceding zero-hazard gap are derived from the
path, not assumed. The finite merged recurrence and the partial/complete
block survival identities are also explicit there.
`quittingRootSequence_singletonFloor_on_tail_iff_inverseRow_nonneg_of_strictThreeCycle`
(`UniformEquilibrium/Quitting/Paths/StrictThreeCycleSingletonFloor.lean`)
combines these results for actual terminal continuation payoffs. For every
parent player and every starting date, the singleton floor holds along the
whole tail exactly when its actual inverse-row coefficients are nonnegative.
`quittingBehaviorDeviationDebt_ge_of_strictThreeCycle_from_start`
(`UniformEquilibrium/Quitting/Terminal/StrictThreeCycleDeadlineResponseDebt.lean`)
then bounds an outside player's unrestricted behavioral response debt at
every starting date of the same schedule by the canonical survival product
times the positive part of the inverse-row deficit after subtracting twice
the reward bound times the hazard bound.
`exists_pureTimeDeviationGain_ge_of_strictThreeCycle_from_start` in the
same file exposes an actual deterministic deadline realizing the positive
bound, together with its survival lower bound and an absolute date no
earlier than the start. The schedule need not be periodic.

`BalancedSingletonCycleCertificate.rootSequence_terminalValue_eq` and
`rootSequence_liveMassLimit_eq_zero`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonActualPath.lean`)
identify the actual values and absorption of the certificate's subdivided
periodic schedule for every initial mesh phase. Its solo roots, hazard bound,
singleton floors, and exact owner ties are also explicit.
`BalancedSingletonCycleCertificate.deletedRootSequence_terminalValue_eq`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonDeletedPath.lean`)
preserves those child values in the actual parent root sequence with every
deleted player at Never. The same file supplies its absorption, child floors,
and owner ties for arbitrary deletion blocks. It does not assume parent
singleton floors. `BalancedSingletonCycleCertificate.deletedThree_singletonFloor_on_tail_iff_inverseRow_nonneg`
and `deletedThree_behaviorDeviationDebt_ge`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonDeletedStrictThreeCycle.lean`)
compose that actual parent schedule with the strict three-cycle theorems at
every starting date. A three-survivor equivalence supplies the owner labels;
the reward-table strict-cycle equation and bounded rewards remain explicit.
The same module gives a finite pure-deadline witness when the adjusted
inverse-row deficit is positive. This is a sharpness result for a supplied
balanced child certificate, not a new producer of one.

`PassiveSingletonRowFactorization.certificate` and
`PassiveSingletonRowFactorization.isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonPassiveRows.lean`)
lift a balanced certificate on the literal deleted child to the parent and
then to one fixed uniform payoff when each outside singleton-difference row
is a nonnegative combination of child rows. Nonsingleton rewards are
unrestricted. Producing the child certificate from a raw strict
inverse-positive triple is supplied by
`exists_balancedCertificate_of_strictlyPositiveInverse_child`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/StrictInversePassiveRowCycle.lean`).
Together with the literal passive rows,
`exists_uniformEquilibriumPayoff_of_strictInverse_passiveRows` gives a fixed
uniform payoff for the parent game. This is an actual child-cycle producer,
not a theorem conditional on a supplied cycle.
`exists_labeledCycle_uniformPayoff_of_strictInverse_passiveRows` in the same
file retains one actual cyclic labeling and its strict child cycle. Its
produced ambient certificate has the stated uniform payoff at its own
phase-zero target. The raw-table counterpart is
`PassiveRowInverseCriterion.exists_labeledCycle_uniformPayoff_of_raw_strictInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`).
These interfaces keep labeling, certificate and target correlated before
accuracy; they do not select unrelated certificates at successive accuracies.
`exists_uniformEquilibriumPayoff_of_nonnegativeInverse_passiveRows`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/WeakInversePassiveRowCycle.lean`)
extends this to an invertible three-player child matrix with entrywise
nonnegative inverse. Its literal nearby parent reward tables preserve the
same outside row weights, and reward-table closure selects one fixed payoff
for the original game. The theorem still requires the raw outside-row
factorization; it does not assert that every reward table has one.
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`)
supplies that factorization from the packet's literal matrix test: an
invertible three-player child matrix `T` with `T⁻¹ ≥ 0` and, for every
outside receiver, `ΓₖS T⁻¹ ≥ 0`. It then returns a fixed parent uniform
payoff, without a supplied cycle, row factorization, or strategy. This is
the full raw-table sufficient class; it is not a universal existence theorem.
`PassiveRowInverseCriterion.raw_inverse_test_failure_of_no_uniformEquilibriumPayoff`
in the same file gives its contrapositive for every selected three-player
child: if the parent game has no uniform-equilibrium payoff, the child matrix
is singular, some child inverse entry is negative, or some deleted receiver's
inverse weight is negative. No counterexample game is constructed.
`PassiveRowInverseCriterion.exists_quietFiniteTimingUniformWitnesses_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/WeakInversePassiveRowQuietWitnesses.lean`)
retains actual independent finite-date-or-Never laws under the same raw weak
inverse tests. One target in the original reward cube precedes every accuracy;
the selected laws have terminal Nash error and target error at most half that
accuracy, and every deleted player is literally Always Continue at every
history. The same laws work for every valid real reward bound `M`: all horizons
at least `max 1 (ceil (4 * M * (deadline + 1) / accuracy))` have the requested
Nash and delivery errors. The proof selects members of the actual family of
nearby strict-table witnesses, transfers those profiles to the original table,
and uses retained-family payoff selection. It requires neither rational
rewards nor strategy convergence. The finite law masses may be real; no
executable weak-boundary target or uniform boundary calendar complexity is
asserted.
`finiteDeadlineTiming_uniformPayoffWitness_of_terminal_bounds`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineSignedHorizonError.lean`)
is the shared signed-reward consumer for that explicit horizon cutoff. It
accepts any actual finite timing laws with the two half-accuracy terminal
bounds, without a separate nonnegativity assumption on the valid reward bound.
`PassiveRowInverseCriterion.exists_rationalClocks_of_raw_strictInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RationalRawPassiveRowClocks.lean`)
constructs rational coarse hazards from rational singleton rewards and the
strict inverse/outside-row tests. One certificate and target precede all
rational accuracies. Its actual independent finite clocks preserve the same
calendar's full terminal semantic pair, satisfy the terminal regret and
delivery bounds, and put every deleted player at Never. Nonsingleton rewards
may be arbitrary real numbers within a rational reward bound. The rate
arithmetic is executable; labeling is selected existentially. This does not
assert a canonical executable raw-table search or bit complexity.
`PassiveRowInverseCriterion.exists_rationalClocks_log_bound_of_raw_strictInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RationalPassiveRowCalendarBound.lean`)
retains those clock laws and fixes a calendar constant before accuracy.
For each fixed strict input, the date count is at most a constant times
`accuracy⁻¹ * log(accuracy⁻¹)` at every sufficiently small positive rational
accuracy. The exact rational power search remains the executable cutoff;
logarithms are used only in its bound. No constant uniform across weak-inverse
boundary inputs is asserted.
`BalancedSingletonCycleCertificate.variable_rootSequence_terminalValue_eq`
(`UniformEquilibrium/Quitting/Cycles/VariableSingletonCalendar.lean`)
identifies every actual suffix value when each coarse phase is subdivided
into an independently chosen positive integer number of dates. Its micro-hazard
is `q / (n - l * q)`. Joint and opponent survival products retain their coarse
values, and deleted players Continue at every history. Positivity is required
for the semantic and boundary arguments, not for the pure index or value
definitions. The tolerance-selected calendar delegates to this construction
in `UniformEquilibrium/Quitting/Cycles/RationalSingletonCalendar.lean`;
there is one chronological compiler proof, not separate proofs for the
generic and selected-length cases.
`BalancedSingletonCycleCertificate.exists_realFiniteCalendar_log_bound`
(`UniformEquilibrium/Quitting/Cycles/RealSingletonCalendarLogBound.lean`)
supplies the fixed-input date-count bound for real singleton data and real
accuracies. One fixed certificate and positive real reward bound select the
constant and threshold before accuracy. The same positive cutoff satisfies
every opponent's survival bound and gives terminal Nash, target delivery,
the printed operational date count, and the logarithmic date count for the
same finite profile. The target is the certificate's original phase-zero
value. This is a consumer of a produced certificate, not another raw-table
producer or an executable real-logarithm algorithm. Exact rational searches
remain unchanged and delegate only their estimates to
`powerLogCutoff_spec_and_bound` (`MathUE/PowerCutoffLogBound.lean`).
`PassiveRowFourFixture.target_isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/PassiveRowFourFixture.lean`)
checks the packet's rational four-player singleton matrix, its selected
three-player inverse and outside-row weights, and its explicit phase-zero
uniform payoff for every reward completion with that singleton matrix.
The module does not calculate the matrix's R0 degree or prove an open
neighborhood result; those are proved in
`PassiveRowFourDegreeNeighborhood.exists_open_degree_one_uniformPayoff_class`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/PassiveRowFourDegreeNeighborhood.lean`).
It gives a nonempty open set in the full four-player reward-table space on
which the literal singleton matrix has canonical chart R0 degree one and every game has a
uniform-equilibrium payoff. The degree calculation uses a finite support
inventory; the payoff conclusion uses the raw inverse-weight criterion.
Identification of this chart integer with ambient Brouwer degree remains
separate from the strategy proof and is supplied by
`ambientDegree_eq_one` and `exists_open_ambient_degree_one_uniformPayoff_class`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/PassiveRowFourAmbientDegreeNeighborhood.lean`).
These apply on every bounded open neighborhood of the origin. The payoff
conclusion uses the inverse/passive-row criterion, not degree one alone.

`QuittingResponseInvariantOnUnitCube` and
`quittingSingletonMatrix_mulVec_blockLift_eq_quotient`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`)
turn equality of the actual stationary residual within each block of a
partition into the exact singleton-matrix relation `Γ E = E A`. The same
module defines a continuous clipped quotient response map and proves its
coordinatewise fixed-point sign conditions.
`quittingResponseInvariantOnUnitCube_iff_forall_ambient`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientAmbientIdentity.lean`)
extends that literal cube identity to every signed block vector.
`quittingResponseInvariantOnUnitCube_iff_finite_coefficients`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientPolynomial.lean`)
identifies it with finitely many coefficient equalities. Their monomial indices
depend only on the block map and coalition bases; each coefficient is a displayed
linear combination of actual reward entries. Exact polynomial evaluation is
proved for the canonical displacement on the whole ambient space. No root,
degree, regularity or nonempty-block hypothesis is added. This finite encoding
does not assert executable decision for arbitrary real reward tables.
`exists_nonzero_quittingQuotientStationaryClippedMap_fixedPoint`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientDegreeEscape.lean`)
computes the actual quotient map's local degree from the raw R0 quotient
matrix and produces a nonzero fixed point when that degree is not one.
`exists_globalQuotient_entireNonzeroSet_degree_eq_one_sub_r0Degree`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientTotalDegree.lean`)
selects the entire nonzero fixed-point set and computes its total normalized
degree in the explicit global chart. The statement includes closed-ball
origin isolation and does not assume finitely many, regular, or isolated
nonzero roots. It does not identify this integer with ambient Brouwer degree.
`quittingQuotientFixedPointField_ambientDegree_omega_eq_one`,
`exists_quittingQuotientOriginBox_ambientDegree_eq_r0Degree`, and
`exists_quittingQuotientOmegaAnnulus_ambientDegree_eq_one_sub_r0Degree`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientAmbientDegree.lean`)
give the intrinsic total degree on `(-1,2)^k`, a constructed origin coordinate
box with radius below one half, and the literal annulus degree `1 - kappa`.
The annulus zero set is exactly the entire nonzero fixed-point set, including
upper-face and nonisolated roots. The total box uses the larger enclosing
chart; the old chart is used only near the origin. These degree statements
concern the actual selected-representative field and need no response-invariance
premise; decoding to all original players retains that premise.
`exists_quittingQuotientResponse_ambient_quadratic_bound`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientAmbientEstimates.lean`)
projects the signed full-player quadratic bound through the block lift and
recipient projection, using the exact singleton-matrix intertwining identity.
Both modules pass silent named checks, including their dimension-zero scope.
`exists_original_stationaryBellmanRoot_of_quotientDegree_ne_one`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientBellman.lean`)
decodes positive absorption and the original players' Nash–Bellman equations.
`stationaryBellmanCertificate_of_nonzero_quotientFixedPoint` and
`terminalNash_and_sameProfileUniform_of_nonzero_quotientFixedPoint_singletonSign`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientSameProfile.lean`)
decode every actual nonzero quotient fixed point, not just a root selected by
degree. Under nonnegative own-singleton rewards only for singleton-block owners,
the very same stationary profile is exact terminal Nash and uniform at its
actual payoff. The no-singleton-block specialization permits all reward signs.
`boundary_and_sameProfileUniform_of_nonzero_quotientFixedPoint_soloQuitterInfeasibility`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientSoloQuitterInfeasibility.lean`)
replaces those signs by infeasibility of the original opponents-only joining
inequalities for every negative singleton-block owner and every hazard in
`(0,1]`. It derives the Never-aware boundary condition internally; a supplied
cap or selected favorable root is not an input.
`exists_uniformEquilibriumPayoff_of_responseInvariant_singletonSign`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientStrategic.lean`)
consumes this root when singleton-block owners have nonnegative singleton
rewards; the same module has a no-singleton-block corollary. Normal-negative
singleton owners are handled by
`exists_stationaryBellmanRoot_uniformPayoff_of_responseInvariant_singletonNormality`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientNormalCompletion.lean`),
which needs normality only for negative singleton-block owners and retains
the produced root's actual Bellman value as the fixed uniform payoff target.
The all-player-normality theorem is a specialization; only its negative
sole-owner branch uses the existing solo punishment compiler. The same module proves
`exists_uniformEquilibriumPayoff_finFour_of_responseInvariant_degree_ne_one`
for arbitrary signed four-player rewards, deriving normality under a
same-table no-UE assumption and discharging that assumption. No punishment
plan is supplied to the raw-table theorem.

`isStandardLCPSolution_quittingBlockLift_zero` and
`isR0Matrix_quittingResponseQuotientMatrix_of_singleton`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientHomogeneous.lean`)
transport homogeneous complementarity through the actual block lift and
derive quotient R0 from full singleton R0. The vector need not lie in the
hazard cube. `finFour_responseQuotient_r0Degree_eq_one_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`)
derives both quotient R0 and degree one from absence of original-game UE.
The same file's
`finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
therefore needs only response invariance, negative quotient determinant and
entrywise nonnegative inverse. R0, normality, a selected root and a computed
degree are not supplied; zero inverse entries remain allowed. These statements
pass their silent named check. The quotient is not a smaller quitting game.

`responseInvariant_of_reward_subgroup_automorphisms`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientPlayerOrbits.lean`)
constructs canonical orbit blocks and representatives for any subgroup of
literal full-reward-table automorphisms and proves their response invariance.
`finFour_orbitResponseQuotient_isR0_of_no_uniformPayoff` and
`finFour_orbitResponseQuotient_degree_eq_one_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourOrbitResponseQuotientCriterion.lean`)
apply the same-table obstruction to each such subgroup. The source retains
all coalition rewards; singleton-only symmetry is not assumed sufficient.

`IsPairedCenteredCompletion` and
`exists_uniformEquilibriumPayoff_of_pairedCenteredCompletion`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedResponseQuotientClass.lean`)
give a raw paired-row class whose literal centered symmetry produces response
invariance. Its quotient matrix has R0 degree minus one, while the full
singleton matrix has degree plus one
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedResponseQuotientMatrix.lean`).
The class theorem permits signed nonsingleton rewards and supplies no strategy
as an input. `exists_stationaryTerminalNash_sameProfileUniform_of_pairedCenteredCompletion`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedResponseQuotientSameProfile.lean`)
retains one exact stationary profile and its actual fixed payoff at every
accuracy when only singleton owners 2 and 3 have nonnegative own rewards.
`exists_omegaAnnulus_ambientDegree_eq_two_of_pairedSingletonMatrix`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedResponseQuotientAnnulus.lean`)
gives intrinsic degree two on exactly the entire nonzero quotient fixed fiber.
Its separate negative-one LCP statement has the unique root `(1,1,1)`.
Degree two is not a count of stationary roots.
`pairedCompletionReward_injective` and
`isPairedCenteredCompletion_iff_exists_coordinates`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedResponseQuotientCoordinates.lean`)
give the exact class chart: thirty-three independent nonsingleton entries and
four arbitrary signed own-singleton levels, with reconstruction and an actual
uniform-payoff consumer for every chart input.
`pairedAsymmetricCompletionReward_properties`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedResponseQuotientAsymmetry.lean`)
changes one nonsingleton reward entry, preserves the class and singleton rows,
and destroys full-table player-swap covariance.
`PairedCubicStationaryExample.exists_local_stationary_branch`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`)
produces an open neighborhood of the literal cubic table over all sixty reward
coordinates. Each table has one exact stationary equilibrium and its own fixed
uniform payoff target before accuracy. No common target across tables or
numerical neighborhood radius is asserted. The raw, canonical and normalized
tables also have checked reward-class attachments and no deterministic terminal
equilibrium, including Never and arbitrary later quitting dates. These results
pass the full integration gate; the class chart is not an open full-table neighborhood.

`NegativeSoloStationaryBoundary.exploitability_positive` and
`exploitability_boundary`
(`UniformEquilibrium/Quitting/Examples/NegativeSoloStationaryBoundary.lean`)
give the actual full exploitability `3h/2` at positive rates and `1/2` at
the zero-rate endpoint. The literal Bellman/Nash endpoint therefore does not
imply exact terminal Nash. The same example proves punishment value `-1/2`
and feasibility of the canonical solo joining system exactly when `h ≥ 1/4`.
It does not refute approximate or uniform equilibrium.
`PairedAdditiveStationaryBoundary.upperFaceRoot_terminalNash_sameProfileUniform`
and `upperFaceRoot_completeCap_eq_payoff`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedAdditiveStationaryBoundary.lean`)
retain actual strategies and complete caps on both entire upper faces of
the singular quotient, including proper-support endpoints. Its nonzero fixed
fiber is infinite, while the entire-fiber annulus degree is one.
`Math.LinearProgramming.SwapTwoNonnegativeInverse.isStandardLCPSolution_neg_one_iff`
and `not_isR0Matrix`
(`MathUE/LinearProgramming/Examples/SwapTwoNonnegativeInverse.lean`)
give a negative-determinant nonnegative-inverse matrix with a unique
inhomogeneous solution but a nonzero homogeneous solution. No R0 degree is
assigned to that matrix. These three boundary examples pass targeted checks.

`PairedCollisionReward.exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardExistence.lean`)
constructs a uniform-equilibrium payoff for every real collision parameter of
its literal fifteen-row reward table. It combines the signed low-parameter
branch, a produced exact two-phase equilibrium for parameters between one and
two, a produced stationary equilibrium between two and four, and the pure exit
at parameters at least four. Both shared endpoints are retained. No rate,
strategy, or Nash certificate is supplied to this theorem.
`PeriodicRates.profile_completeCap`, `allSuffix_isExactTerminalNash`, and
`profile_uniformPayoffWitness`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardPeriodic.lean`)
retain the actual independent periodic profile, its unrestricted behavioral
cap including Never, every live suffix, and that same profile's uniform
finite-horizon witnesses. The rates and target depend only on the table
parameter, not the accuracy. This solves the displayed family, not arbitrary
collision rewards.
`exists_one_periodicRates_all_finiteCalendar_accuracies`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardFiniteCalendar.lean`)
chooses one rate pair before all accuracies and constructs actual independent
finite-date-or-Never witnesses. `PeriodicRates.finiteProfile_completeCap`
identifies the full behavioral cap exactly with the infinite target; the
same module exposes geometric marginal masses, exact debts and the complete
terminal semantic pair. Its delivery and deviation boundary charges are
`8 * cycles / horizon`, and its regret charge is `16 * cycles / horizon`.
The reconstructed timing laws themselves satisfy the uniform-payoff
inequalities at the fixed target for every horizon at least
`max 1 (ceil (32 * cycles / accuracy))`. Positive Never masses remain in
the witnesses and in the response comparison.

`PeriodicRates.profile_at_one` and `primary_mem_sharpInterval`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardCalibration.lean`)
identify the parameter-one construction with the existing period-two profile,
its exact rates and phase values. The sharper rate brackets are
`373/500 < primary < 747/1000` and `73/100 < secondary < 74/100`.
`PeriodicRates.profile_horizonDeviation_absolute_uniform` and
`allSuffix_horizonDeviation_absolute`
(`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardHorizon.lean`)
bound the absolute terminal-to-average error by `8000 / (271 * horizon)`
for every behavioral deviation, phase and live suffix. The same delivery
constant and the regret constant `16000/271` are uniform over the periodic
parameter interval. These infinite-profile estimates are separate from the
finite-calendar boundary charges.

`QuittingThreePlayerStrategyClass.of_normalizedThreePlayer`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazard.lean`)
constructs, for every three-player table with unit own-singleton rewards and
every positive accuracy, a stationary terminal approximate equilibrium or an
actual root sequence whose every date/player Quit hazard is at most that
accuracy. Deviations are unrestricted behavioral replacements. Weak and
degenerate singleton supports are included. The infeasible-mixture branch
produces an exact stationary terminal equilibrium; the feasible branch reuses
the singleton alternative and explicit cyclic arcs. This source conclusion
does not quantify a fixed payoff target. Positive scaling and player-cardinality
transports are supplied by
`QuittingThreePlayerStrategyClass.of_card_le_three_of_positiveSolo_when_three`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazardTransport.lean`).
This retains the actual selected roots or root sequences for every finite
player type of cardinality at most three, requiring positive own-singleton
rewards only at cardinality three. At cardinalities zero, one and two,
`exists_stationaryTerminalNash_of_card_le_two` retains actual stationary roots
for arbitrary reward signs. Multiplicative coordinate scaling preserves zero
Never payoff; no terminal-only additive translation is used. The generic
terminal-payoff and Nash pullback lemmas reside in
`UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`.
`QuittingThreePlayerStrategyClass.of_card_le_three`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazardAllSigns.lean`)
removes the sign restriction: every reward table on at most three players has,
at each positive accuracy, a stationary terminal approximate equilibrium or
a profile whose every date/player Quit hazard is at most that accuracy.
The terminal Nash inequalities cover unrestricted behavioral deviations.
On the remaining three-player standard-Q branch, the actual normalized
singleton matrix produces a strict directed cycle; the existing cycle
compiler accepts arbitrary own-singleton signs. This strategy-class result
does not select a fixed payoff target before accuracy.
Literature wrappers delegate to these production proofs, not conversely.

The literal Literature `proposition1` delegates to this theorem and passes its
separate standard-axiom check. The paper's distinct printed subdivision rates
are not asserted by this assembly.

`QuittingThreePlayerStrategyClass.of_homogeneousMatrixBranch` and
`of_not_standardQMatrixSide`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazard.lean`)
reuse the actual stationary-root families from the existing LCP producers.
They allow arbitrary finite player types and reward signs under their explicit
matrix hypotheses. `stationaryAlternative_or_standardQMatrixSide` retains the
remaining nonhomogeneous standard-Q side as an alternative; signs alone do not
exclude that side.

`quittingCrossedClippedMap` and `quittingCrossedResponse_derivative_apply`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponse.lean`), with
`quittingCrossedClippedMap_eq_self_iff`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseFaces.lean`),
define the different full-player swapped-response map with its selected-player
ceiling, derivative, and exact fixed-point face signs. The local-degree and
global-escape lemmas
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseDegree.lean`,
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseEscape.lean`)
produce a nonzero crossed root from R0 and degree not equal to one for the
permuted singleton matrix.
`exists_globalCrossed_entireNonzeroSet_degree_eq_one_sub_r0Degree`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseTotalDegree.lean`)
uses one radius to isolate the origin and identifies the exterior's selected
solutions with the entire nonzero fixed-point set, including its exact image
under the global chart. Its normalized integer degree is one minus the crossed
R0 degree; the positive-inverse specialization gives two. No finiteness or
regularity of the nonzero roots is required. These degree statements use the
explicit `[-2,2]` chart; identification with ambient Brouwer degree or arbitrary
chart independence is not asserted by those modules.
`exists_quittingCrossedAmbientAnnulus_degree_eq_one_sub_r0Degree`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseAmbientDegree.lean`)
constructs a bounded open ambient annulus whose actual zero fiber is precisely
the entire nonzero crossed fixed-point set and whose ambient degree is
one minus the crossed R0 degree. Frontier avoidance and strict chart enclosure
are derived from actual confinement and origin isolation.
`exists_quittingCrossedOmegaAnnulus_degree_eq_one_sub_r0Degree`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseOmegaDegree.lean`)
gives the same intrinsic degree on the source's literal box `(-1,2)^n` with
a small closed ball removed. Excision through the intersection with the
radial annulus retains the entire nonzero fiber. Neither finite roots nor
enclosure of the literal box's closure in the old chart is assumed.
Under the strict full-box guards, reciprocal
singleton signs, and the same degree assumptions,
`exists_guardedCrossed_stationaryTerminalNash_uniformPayoff`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseStrategic.lean`)
turns that root into an original-game exact stationary behavioral terminal
Nash profile and a fixed uniform-equilibrium payoff. The full-box guards
are stated in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseGuards.lean`;
`quittingCrossedSourceGuards_iff_fullBoxGuards` in that file identifies them
with the packet's literal two-face guards. The strategic module also states
`exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_sourceGuards`
under those source conditions.
`quittingCrossedSingletonMatrix_degree_eq_one_of_sourceGuards_no_uniformPayoff`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseR0Restriction.lean`)
gives the separate necessary restriction when the original singleton matrix
is R0, selected reciprocal entries are positive, and selected external entries
are strictly negative. The actual row-swapped matrix is then R0 without any
inverse-positivity assumption; source guards and absence of a UE target force
its degree to be one. The generic finite-index row-swap result resides in
`MathUE/LinearProgramming/RowSwapR0Restriction.lean`. The source adapter passes
a silent named check. Degree one does not imply absence of UE.
`exists_isAlgebraic_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_sourceGuards`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseAlgebraicStrategic.lean`)
adds algebraic hazards and algebraic actual payoff for rational rewards and
rational selected-player ceiling. It derives the algebraic witness from the
same R0/nonunit-degree source, without a supplied root or regularity assumption.
The original-game endpoint, full-rate cap, complete behavioral cap and uniform
payoff all refer to that same selected root and value; zero and upper hazard
faces are retained. The finite sign-formula encoding is in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseRationalFormula.lean`.
This is algebraic existence, not executable root isolation or rational search.
`rationalQuittingStationaryRegretAccepts_eq_true_iff`
(`UniformEquilibrium/Quitting/Stationary/RationalPayoffCap.lean`)
identifies the executable rational product/sum/quotient/max test with
deleted-opponent contraction and the actual stationary terminal Nash condition
against every behavioral deviation. Its payoff and cap formulas are jointly
continuous on the contracting part of the closed hazard cube, including zero
and sure hazards
(`UniformEquilibrium/Quitting/Stationary/HazardPayoffCap.lean`).
`rationalQuittingStationaryBoundedSearch_eventually_succeeds_of_sourceGuards`
(`UniformEquilibrium/Quitting/Stationary/RationalGridSearch.lean`)
proves success at every sufficiently large finite search budget from the literal
rational guarded source and R0/nonunit-degree hypotheses. The first successful
budget selector returns an actual contracting stationary profile satisfying
the requested full behavioral regret bound. It requires only accuracy, not a
prescribed payoff or a selected real root; no complexity bound is asserted.
The source ceiling may be real; rationality is required only for the reward
table and requested accuracy, not for this auxiliary source parameter.
These rational-search modules pass silent targeted checks.
`exists_rationalQuittingSearchFiniteCensor_of_sourceGuards`,
`exists_rationalQuittingSearchFiniteCensor_of_strictRawUnit`, and
`exists_rationalQuittingSearchFiniteCensor_of_halfStrictRaw`
(`UniformEquilibrium/Quitting/Stationary/RationalSearchFiniteCensor.lean`)
compose that actual selector with approximate-Nash censoring. The source
conditions supply search success internally. At every positive rational
accuracy, the resulting independent date/Never laws retain exact geometric
atoms, Never mass and the full censored semantic pair, with the requested
terminal regret and payoff error at most one sixth of accuracy relative to
this selected stationary value. The actual deleted-survival rate determines
the logarithmic cutoff and signed finite-horizon bounds. The module passes
a silent named check. Its selected value may change with accuracy; it does
not search for a prescribed target or assert an executable logarithmic cutoff.
`exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_strictRawUnit`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseRawProducer.lean`)
closes the strict unit-ceiling reward-table branch: the literal lower ranking
and joining comparisons for both selected recipients, together with positive
determinant and entrywise positive inverse of the full singleton matrix,
produce the guards, crossed R0 degree minus one, and the exact stationary
Nash/uniform-payoff conclusion. The full unswapped singleton matrix has R0
degree plus one by
`quittingSingletonMatrix_r0_degree_one_of_positiveInverse`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseRawMatrix.lean`).
`exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_halfStrictRaw`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseHalfCeilingProducer.lean`)
closes the four-player strict half-ceiling branch from the same determinant
and inverse conditions, two lower ranking comparisons, and nine strictly
negative tensor Bernstein coefficients for each selected residual. The
coefficient reconstruction applies to the actual reward-table residuals
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseHalfCeilingCoefficients.lean`),
not a supplied polynomial.
`exists_stationary_uniformPayoff_targetApproximation_of_weakHalfRaw` and
`exists_stationary_uniformPayoff_targetApproximation_of_strictRawUnit_nonnegativeInverse`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakBoundaryTarget.lean`)
close both nonnegative-inverse boundary branches: the four-player weak
half-ceiling class and the strict unit-ceiling class in every dimension at
least three. Each conclusion selects one fixed original-game uniform-equilibrium
payoff and, at every positive accuracy, a contracting stationary profile
whose complete terminal regret and payoff distance to that target are bounded
by the accuracy. The residual perturbation, strict coefficients, and raw
matrix/lower-guard approximations are derived from the literal reward table.
`exists_uniformPayoff_stationaryTargetAcceptance_of_terminalApproximations`
(`UniformEquilibrium/Quitting/Stationary/StationaryTerminalPayoffSelection.lean`)
provides the reusable stationary fixed-target selection step. Generic affine
Bernoulli and quadratic tensor Bernstein algebra resides in `MathUE`.
`exists_stationary_uniformPayoff_witnesses_of_weakHalfPolynomialGuards`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialProducer.lean`)
extends the half-ceiling boundary result to the actual weak polynomial face
guards, without finite reward-ranking or Bernstein-coefficient assumptions.
The literal perturbation produces strict lower and upper faces; the original
weak lower face derives the external singleton signs and nonnegative inverse
derives reciprocity. Fresh nearby equilibria transfer to the original signed
game and the existing selector fixes one target before accuracy. The theorem
retains actual contracting stationary witnesses for terminal approximation and
all sufficiently long finite horizons. Its named check is silent; exact boundary
stationary attainment is not asserted.
`exists_uniformPayoff_of_oneSidedWeakUnitRawGuards`
(`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`)
proves a matrix-free Fin4 class from twelve weak owner lower comparisons
and four weak joining comparisons for the passive player. It constructs
the outsiders' joining-game root with one sure owner and one passive player.
An active outsider yields an exact contracting stationary terminal Nash
profile. With no active outsider, all no-join inequalities hold; the checked
Fin4 punishment-normality reduction supplies UE existence for arbitrary
singleton signs. This latter branch does not assert stationary attainment
or prescribe the UE target. The polynomial-face variant is
`exists_uniformPayoff_of_oneSidedWeakUnitGuards` in the same file.
`stationaryTerminalNash_or_sureSolo_everyHorizon_of_oneSidedWeakUnitRawGuards`
(`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitFiniteHorizon.lean`)
strengthens the nonnegative-owner case: the original stationary sure-solo
profile itself is exact behavioral Nash at every horizon, including zero,
and delivers the singleton target within `M / H` at positive horizons.
The raw producer derives all no-join comparisons internally.
`quittingFiniteHorizonDeviationCap_sureSolo_eq`
(`UniformEquilibrium/Quitting/Stationary/SureSoloFiniteHorizon.lean`)
owns the reusable same-profile theorem for every finite player type; the
displayed owner supplies nonemptiness internally. This does not strengthen
the negative sole-owner punishment branch to stationary attainment.
`halfCeilingValue_uniformPayoff` and `unitCeilingValue_uniformPayoff`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseExactRoots.lean`)
check both literal tables' displayed roots, Bellman values, exact unrestricted
caps, and fixed UE targets. The raw class consumers independently produce
UE from the tables' finite comparisons
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseClassConsumers.lean`).
`halfCeiling_exists_behaviorDeviation_gain_one`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponsePureClockSeparation.lean`)
excludes every deterministic stopping-clock profile, including all Never.
`halfCeiling_not_oneSidedWeakRawGuards`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseRawClassSeparation.lean`)
excludes every relabeled ordered pair for the matrix-free raw test; that file
also excludes the unit table's selected-pair weak half-ceiling test, not
every relabeling of that test.
`halfCeiling_block_injective_of_responseInvariant` and
`unitCeiling_block_injective_of_responseInvariant`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponsePartitionSeparation.lean`)
use distinct all-half residuals to exclude every nondiscrete block map.
`halfCeiling_fullRewardBall_stationaryTerminalNash_uniformPayoff` and
`unitCeiling_fullRewardBall_stationaryTerminalNash_uniformPayoff`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseFullRewardNeighborhood.lean`)
produce fresh actual contracting stationary equilibria and fixed UE targets
throughout the full sixty-coordinate reward balls of radii `1 / 100` and
`1 / 1000`, respectively. No singleton coordinate or symmetry is fixed.
The inverse calculation uses the ordinary entrywise reward metric and derives
positive determinant and positive actual inverse for each new table; the half
coefficient-error factors are derived from its actual reward residual.
`unitCeiling_block_injective_of_dist_lt_responseInvariant`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponsePartitionNeighborhood.lean`)
excludes every nondiscrete response quotient throughout the unit ball. Both
modules pass silent named checks. The algebraic-root, accuracy-only rational
search, and child-LP comparisons have the stated producers and checks above
and below; they are not a complete packet seal.
`unitCeiling_not_reindexed_weakHalfRawGuards_of_dist_lt`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseWeakHalfNeighborhoodSeparation.lean`)
excludes the weak half-ceiling raw test under every relabeling throughout the
unit ball, using actual lower-ranking and upper-face witnesses.
`joining_zero_gain_eq_two` and `profile_not_exact_terminalNash`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseUnguardedRootCounterexample.lean`)
give the literal crossed fixed root whose original player's behavioral
Quit-now deviation gains two. These modules pass silent named checks.
The example refutes unguarded fixed-point transfer, not UE existence.
The quotient RI route does not apply to the crossed map.

`quittingCrossedFixedPointField_ambientDegree_omega_eq_one` and
`exists_quittingCrossedFixedPointField_ambientDegree_ball_eq_r0Degree`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseAmbientNormalizations.lean`)
give the literal total-box and origin-ball normalizations. The total box uses
a larger enclosing chart; its closure need not fit inside the old chart.
`exists_quittingCrossedResponse_quadratic_bound` and
`exists_quittingCrossedSingleton_minMap_margin`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseAmbientEstimates.lean`)
produce the second-order displacement bound on a signed ambient ball and
the global homogeneous complementarity margin. The shared bounds are
`exists_ambient_quittingDisplacement_singleton_bound`
(`UniformEquilibrium/Quitting/Stationary/DiscountedAmbientQuadraticRemainder.lean`)
and `exists_pos_mul_norm_le_lcpMinMap_zero`
(`MathUE/LinearProgramming/R0MinMapCoercivity.lean`). They do not restrict
the local estimate to nonnegative hazards or require nonempty coordinates.

`quittingHalfFirstCoefficient_reward_l1_norm` and
`quittingHalfSecondCoefficient_reward_l1_norm`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseHalfCoefficientNorms.lean`)
state the exact reward-coordinate norms of all eighteen Bernstein coefficients;
the same module proves coefficient uniqueness. Recipient-row translations
preserve the actual singleton matrix, zero-discount displacement and crossed
guards (`UniformEquilibrium/Quitting/Stationary/RewardRowTranslation.lean`,
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseRowTranslation.lean`).
Never still has payoff zero, so arbitrary-profile strategic equivalence is
not asserted.

`halfPolyhedralReward_covers_fixedSingletonMatrix`,
`halfPolyhedralReward_strictRawGuards_iff`, and
`nonempty_halfSelectedPolyhedralRegion`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseSelectedPolyhedron.lean`)
describe the selected-recipient slice by exactly forty-two strict affine
constraints. For arbitrary own singleton values the slice is nonempty, open
and convex. The twenty-two outsider-recipient nonsingleton coordinates are
independently free. This relative polyhedral description is distinct from
the full sixty-coordinate reward neighborhoods above.

`halfCeiling_lowerMargin_minimum`, `unitCeiling_joiningMargin_minimum`, and
`halfCeiling_upperCoefficient_maximum`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseLiteralMargins.lean`)
give attained margins and the literal joining arrays. The six displayed
partition witnesses have exact actual residual gaps in
`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponsePartitionWitnesses.lean`.
`crossedSourceSingletonPartition_failed_count`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseSingletonPartitionCount.lean`)
counts eight failures among the fourteen canonical nondiscrete maps. Passing
this necessary derivative test does not imply response invariance.
`halfCeiling_literalToggleGap_one`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseToggleWitnesses.lean`)
supplies all fifteen source-supported membership toggles used by the
deterministic-clock counterresponses.

`halfCeiling_exists_uniformPayoff_strictly_above_singletons`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponsePayoffExclusions.lean`)
retains one actual target with strict coordinate surplus and every nonzero
nonnegative weighted surplus. `not_halfWeakRawGuards_reindex_of_no_uniformPayoff`
and `not_oneSidedWeakUnitRawGuards_reindex_of_no_uniformPayoff`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseNoUERestrictions.lean`)
give all-label contrapositives under the respective source hypotheses.
They do not assert that some passing pair exists for every Fin4 reward table.

`halfCeiling_every_proper_child_raw_test_fails` and
`unitCeiling_three_player_child_no_certificates`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseChildLP.lean`)
evaluate the literal source reward restrictions. The half table excludes
every proper-child universal raw certificate, including the positive-singleton
license for omitting Never. The unit table has four strict three-player-child
dual certificates. These do not exclude extension of a particular child
equilibrium. Sampled rows and quantitative perturbation consumers reuse
the exact finite LP alternative in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockSampledLPDual.lean`
and the game-independent weighted-error estimate in
`MathUE/DirectedTransport/FiniteInequality/Perturbation.lean`.
`unitCeiling_three_player_child_no_certificates_of_dist_lt`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseChildLPRobust.lean`)
extends both unit-table exclusions to every actual reward table at entrywise
distance below `1 / 1000`. The exact weighted-error factors are `36`, `4`,
`254`, and `28`. This is a full reward-coordinate perturbation, not a
fixed-singleton or symmetric subspace. The half table's zero-column duals
do not assert robust exclusion.

The original-coalition source identities for these child rows are owned by
`rawChild_future_delta` and `rawChild_joining_delta`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockOriginalCoalitionRows.lean`).
They apply to every finite original player type and its actual child-plus-one
restriction, rather than a separately supplied restricted table.

`isHorizonNash_stationary_of_terminalNash_and_opponentGap`
(`UniformEquilibrium/Quitting/Stationary/FiniteHorizonRate.lean`)
specializes the existing periodic rate to any finite-player stationary root.
Absolute reward bound `M`, deleted-clock gap `g > 0`, and exact terminal Nash
give full behavioral horizon regret at most `2 * M / (g * H)` for the same
prescribed profile and every positive horizon.
`halfCeilingRoot_isHorizonNash`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseFiniteHorizon.lean`)
instantiates the packet's literal `4776 / (35 * H)` bound.

`exists_stationaryFiniteCensorTimingProfile`
(`UniformEquilibrium/Quitting/Stationary/FiniteCensor.lean`) retains one actual
independent finite-clock family obtained by censoring a stationary terminal
Nash profile after `N` dates. It derives the full behavioral cap internally,
preserves the exact censored marginals and semantic pair, and gives terminal
regret at most `3 * M * rho^N`, delivery error at most `M * rho^N`, and signed
horizon errors with additional `2 * M * (N + 1) / H` and
`M * (N + 1) / H`, respectively. Here `rho` is the maximum deleted-opponent
survival, not a sum of marginal tails. The empty-player case is included.
`exists_stationaryFiniteCensorTimingProfile_of_approximateNash` in the same
file generalizes this construction to a source with terminal Nash error
`error`. Censoring adds `3 * M * rho^N` to that error, with unchanged delivery
and horizon corrections, on the same actual independent finite laws and
semantic pair. The exact-Nash theorem delegates with error zero. The generalized
module and its logarithmic-cutoff consumers pass a silent targeted check.
`exists_halfCeilingFiniteCensorTimingProfile`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseFiniteCensor.lean`)
constructs these laws from the actual half-ceiling root, with
`rho = 7 / 12`, reward bound `199 / 7`, and regret coefficient `597 / 7`.
`exists_stationaryFiniteCensorTimingProfile_logCutoff`
(`UniformEquilibrium/Quitting/Stationary/FiniteCensorCutoff.lean`) retains that
same family with an explicit logarithmic date bound. The survival rate and
logarithmic scale are fixed before accuracy, not uniformly over boundary roots.
`exists_stationaryFiniteCensor_oneDate_exact` in the same file preserves
payoff and full cap exactly when the maximum deleted-opponent survival is zero.
`exists_unitCeiling_oneDateFiniteCensor_exact`
(`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseOneDateCensor.lean`)
applies this to the actual unit-ceiling root, with no supplied root or cap.

`weight_le_inverseRow_of_singletonFutureRows`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockInverseRowObstruction.lean`)
derives the inverse-row obstruction from only the singleton future rows.
It permits any finite embedded child and an entrywise nonnegative inverse.
The comparison permits signed weights; nonnegative weights imply a
nonnegative inverse row. Both exact and Never-relaxed capped-clock
certificates have direct corollaries in the same file.

`ThreeCoreCyclicLabelAdapter.exists_directedCycle_labeling_of_strictlyPositiveInverse`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/PositiveInverseCyclicLabelAdapter.lean`)
supplies the canonical strict-cycle labeling from a zero-diagonal matrix
with three coordinates and strictly positive inverse. It composes the
existing classification and inverse-positive implications.
`fullChild_join_le_of_joinRows`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockFullChildJoinObstruction.lean`)
extracts the full-child joining obstruction from only the joining rows,
even with signed weights. The same file constructs a change to the
outsider's full-parent collision payoff that violates this obstruction
while preserving the singleton matrix and the deleted child reward.

`PositiveInverseFourMatrixComparisons.not_projectiveQBar`
(`UniformEquilibrium/Quitting/Classification/LCP/PositiveInverseFourMatrixComparisons.lean`)
separates the strict-inverse criterion from the projective-Q-bar criterion
on the determinant-minus-three example. The same module proves full standard Q,
absence of a homogeneous solution, full normal core, and failure of the named
signed-four-cycle input under relabeling. The example still has a covering
negative walk with repeated owners; arbitrary longer calendars are not excluded.

`exists_finset_r0Degree_eq_sum_sign_det`
(`MathUE/LinearProgramming/R0DegreeSum.lean`) computes this integer from all
actual roots at one regular test offset. The finite root set is derived, not
supplied; its membership is exactly the standard LCP solution predicate.
`NegativeDegreeFourMatrix.r0Degree_eq_neg_one`
(`MathUE/LinearProgramming/Examples/NegativeDegreeFourMatrix.lean`) applies
the computation to an explicit four-by-four matrix with three roots of
indices minus one, minus one, and plus one. Its determinant is positive and
its inverse has both signs. The same matrix is standard Q and has an infinite
solution set at another offset, so regularity of the test offset is not a
claim about every offset.
`exists_uniformEquilibriumPayoff_of_negativeDegreeFourMatrix`
(`UniformEquilibrium/Quitting/Classification/LCP/NegativeDegreeFourMatrixCriterion.lean`)
gives an original uniform payoff for every reward table with that singleton
matrix, with no restrictions on own-singleton levels or nonsingleton rewards.
`eventually_exists_uniformEquilibriumPayoff_near_negativeDegreeFourMatrix`
in the same file extends this conclusion to every sufficiently nearby
singleton matrix. The generic strict support-test stability theorem
`eventually_r0Degree_eq_of_strict_support_inventory`
(`MathUE/LinearProgramming/SupportTestStability.lean`) preserves the complete
admissible-support inventory and R0; degree is constant among nearby
zero-diagonal matrices. The concrete matrix retains exactly its three
supports and degree minus one, with the roots recomputed from the perturbed
principals.

`AdaptiveChildCenter.target_isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenter.lean`)
gives the payoff `(1,0,0,1)` for a signed four-player table with three fair
Quit-at-zero/Never clocks and one sure-quitting anchor. The actual profile
is exact terminal Nash against all behavioral deviations. The module also
identifies the unique active root probabilities over the closed cube and
reconstructs each three-player deletion with the surviving stopping laws
unchanged. `exists_center_parent_child_exploitability_floor`
(`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterPairedFloor.lean`)
gives a positive lower bound on parent-plus-child exploitability for every
parent profile and every deletion. The neighborhood theorem
`exists_solved_open_neighborhood_sameProfile_horizon_equilibrium_floor`
(`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterNearbyHorizons.lean`)
retains this obstruction while producing, for each nearby reward table, one
profile that is exact Nash at every finite horizon and delivers one fixed
target over sufficiently long horizons. This obstructs unchanged-law child
extension, not uniform-equilibrium existence. Complete-claim review, the full
silent default build and exhaustive production axiom audit pass. The source
packet is retired unchanged to
`math/formalized/ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO.md`.

`positive_minimum_preemptedOwner_quadraticMargins`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`)
proves explicit cap and prescribed-payoff margins at a positive global
minimum of total semantic debt. If that minimum is `d` and rewards have
absolute bound `M > 0`, a preempted owner's cap exceeds its singleton by
at least `d + d²/(8M)`, and its prescribed payoff exceeds its singleton
by at least `d²/(8M)`. The module extends this to each nonnegative-singleton
owner, and to every owner in four-player games without singleton signs.
These are consequences of a hypothetical positive minimum, not a proof
that no such minimum exists.
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPayoffEnvelope.lean`
also bounds the attained minimum by `sqrt(8*M*ρ)` if every actual profile
has some player's prescribed payoff at most its singleton plus `ρ ≥ 0`.
This applies to nonnegative singleton tables with any finite player set,
and to signed four-player tables. The witnessing player may vary with
the actual profile.
The general nonpreempted-owner alternative is stated separately as
`isUniformEquilibriumPayoff_soloReward_of_nonnegative_noPreemptor`
(`UniformEquilibrium/Quitting/Classification/Existence/SoloPreemptionUniformPayoff.lean`):
the fixed target is the owner's singleton reward vector.

`exists_uniformEquilibriumPayoff_of_supportwiseBalance`
(`UniformEquilibrium/Quitting/Classification/Existence/SupportwisePremiumUniformPayoff.lean`)
proves uniform-payoff existence for every finite nonempty player set with
nonnegative singleton rewards and supportwise weighted premium balance.
The input is a reward-table condition: on each nonempty support, one
normalized nonnegative weighting makes the participant-only premium sum
nonpositive for every contained nonempty coalition. Weights may vanish and
depend on the support; passive rewards and own premiums may have either sign.
`exists_periodic_allSuffix_terminalNash_of_supportwiseBalance` in the same
module constructs periodic profiles whose every suffix is terminal approximate
Nash against unrestricted behavioral deviations, before the fixed-payoff
selection. No equilibrium source is supplied as an input.

`IsSupportwiseBalancedQuittingPremiumTable` and its exact product-premium
identity are in `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`.
`IsSupportwiseQuittingPremiumWeightCertificate`
(`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumBalanceAt.lean`)
is the shared one-weight predicate; the global table condition quantifies
its existence over nonempty supports. The aggregate theorem retains the
same certificate and a positive-weight active player with low Quit payoff.
`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumFeasibleSet.lean`
proves the literal one-support feasible set closed, and compact for finite
player types. `MathUE/FinFourSubsetIncidenceCounts.lean` supplies the counts:
15 supports, 32 weight coordinates, 65 coalition inequalities, and 33 after
discarding singleton tautologies. These are counts of the sufficient test,
not an equilibrium-computation complexity bound.
The raw-table identity gives an active player with Quit endpoint at most its
singleton at every absorbing product root, without a Nash premise.
`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumNormalization.lean`
proves preservation under shifted playerwise normalization, with the weights
reweighted by the positive coordinate scales. It includes weak support-peeling
and global strictly positive weighting as sufficient conditions.

`weakQuittingPremiumSupportPeeling_iff_playerRanking`
(`UniformEquilibrium/Quitting/Classification/QuittingPremiumSupportPeelingOrder.lean`)
identifies weak premium support peeling with an injective player ranking:
every coalition giving a member a positive own premium contains an earlier
member. This is a ranking of player labels, not quitting dates. The underlying
finite coalition relation theorem is game-independent and resides in
`MathUE/FiniteCoalitionSupportPeelingOrder.lean`.
`exists_uniformEquilibriumPayoff_of_weakPremiumSupportPeeling` and
`exists_uniformEquilibriumPayoff_of_positivePremiumPlayerRanking`
(`UniformEquilibrium/Quitting/Classification/Existence/QuittingPremiumSupportPeelingUniformPayoff.lean`)
state the original-game fixed-payoff conclusions directly. Their companion
periodic theorems retain unrestricted terminal approximate Nash at every suffix.

`UniformEquilibrium/Quitting/Examples/SupportwisePremiumClassSeparation.lean`
gives exact cyclic, one-positive-premium, and combined Fin4 tables separating
weak peeling from global positive weighting, with supportwise balance holding
even when both special conditions fail. Passive payoffs remain arbitrary.
`UniformEquilibrium/Quitting/Examples/SemipositiveGlobalWeightCounterexample.lean`
shows that a single nonnegative weighting can miss the active support: its
sure-pair root is exact Nash while every active Quit endpoint exceeds its
singleton reward. These are failures of sufficient conditions, not failures
of equilibrium existence.
`UniformEquilibrium/Quitting/Examples/FinTwoHazardWeightedPremiumBoundary.lean`
exhibits an actual two-player reward table, product root, and normalized
weights whose plain average Quit premium is positive while the average
multiplied by the actual Quit hazards is zero.

The shared classical source is
`exists_periodic_quittingPerfectAbsorbingRootSequence_of_lowActiveQuitPayoff`
(`UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRootSequence.lean`).
It assumes unit singletons and a low active Quit endpoint, not capped joint
rewards, and constructs a literal periodic sequence with positive absorption
floor and perfect rows against its actual next-tail payoffs. The unit-only
full-response extraction in
`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`
retains periodicity and every-suffix terminal Nash, but does not assert that
the extracted profile keeps the absorption floor.
`UniformEquilibrium/Quitting/Terminal/TerminalAffineNashTransfer.lean` transfers
terminal Nash under nonnegative coordinate scaling and removes a nonnegative
terminal-only shift bounded by `t` at error cost `t`, keeping Never's zero
payoff and the same literal root sequence.

Rational coefficient approximation is provided by
`exists_evalReal_fderiv_close_on_compact`
(`MathUE/Interval/RationalPolynomialDerivativeApproximation.lean`). It constructs
one native rational polynomial approximating the derivative of a supplied real
multivariate polynomial uniformly on any compact set, retaining both summed
coordinate-direction error and derivative operator-norm error.
`exists_evalReal_eq_eval₂` supplies the exact rational-polynomial syntax bridge.
The cube specialization permits arbitrary real radii and dimension zero.
This is not an approximation theorem for an arbitrary smooth function.

`MathUE/Polynomial/TensorBernstein.lean` supplies actual tensor Bernstein
multivariate polynomials with separate coordinate degrees. Exact evaluation,
nonnegative unit-cube weights, total weight one, and coordinate variance are
proved, including zero degrees and dimension zero where meaningful.
`derivative_bernsteinCoefficientPolynomial` is the univariate consecutive-
coefficient difference identity; `pderiv_tensorBernsteinPolynomial` and
`hasDerivAt_eval_mvPolynomial_update` connect tensor formal derivatives to
actual coordinate-line derivatives. These algebraic identities do not yet
assert simultaneous derivative approximation of a smooth function.

`pderiv_tensorBernsteinCoefficientPolynomial`
(`MathUE/Polynomial/TensorBernsteinDifferences.lean`) lowers the differentiated
coordinate degree by one and replaces coefficients by consecutive differences.
Its evaluated formula is a tensor-weighted average, and
`hasDerivAt_eval_tensorBernsteinCoefficientPolynomial_update` identifies it
with the actual coordinate-line derivative. The natural-index coefficient
adapter is the same multivariate polynomial, not a separate polynomial model.

`MathUE/Polynomial/MvPolynomialFDeriv.lean` separates general polynomial
calculus from the Bernstein construction: smoothness of every order and
`fderiv_eval_mvPolynomial_apply_single` identify formal partials with the
actual derivative. `MathUE/Polynomial/TensorBernsteinGridEstimates.lean`
bounds the canonical-grid second moment and the displacement of finite-
difference sample segments from mixed-degree grid nodes. The two grids are
kept distinct. `MathUE/Analysis/PositiveWeightedApproximation.lean` provides
near/far bounds for finite positive averages, and
`MathUE/Analysis/CoordinateSecantEstimate.lean` controls literal finite
differences from actual derivative bounds. Uniform derivative convergence
is supplied by
`eventually_fderiv_tensorBernsteinApproximation_close_on_unitCube`
(`MathUE/Polynomial/TensorBernsteinDerivativeConvergence.lean`), with one
degree working for all coordinates and cube points. Affine transport in
`MathUE/Polynomial/PolynomialDerivativeApproximation.lean` extends this to
bounded real domains. `exists_evalReal_fderiv_close_of_contDiff_on_box`
(`MathUE/Interval/RationalPolynomialSmoothDerivativeApproximation.lean`)
constructs one native rational polynomial with uniform coordinate-derivative
and derivative-operator error bounds for a supplied global continuously
differentiable function. Boxes need not have rational endpoints or positive
width; empty boxes and dimension zero are included. These are derivative
approximation theorems, not function-value approximation or smoothing of a
Borel capacity function.

Stationary terminal approximate equilibria supply weighted packets through
`hasAbsorptionWeightedFiniteForwardPackets_of_stationary`
(`UniformEquilibrium/Quitting/Projective/StationaryAbsorptionWeightedForwardPacket.lean`).
One positive singleton reward suffices to obtain positive absorption at small
error; normality is not assumed. The payoff box is the reward bound plus two.
`exists_stationaryAbsorbingRoot_generating_weightedPackets` selects one root
before all charge requests and retains its literal root and annotation in
every resulting packet. The annotation is the actual stationary payoff plus
twice the error. In `UniformEquilibrium/Quitting/Stationary/UpwardTranslation.lean`,
`quittingRootCoordinateNashDefect_stationaryUpwardTranslate_le` bounds regret
by twice the error times absorption, and
`quittingStationaryUpwardTranslate_sub_successor_eq` gives equality for the
Bellman residual. The general support-local translation retains its factor
three in `UniformEquilibrium/Quitting/Root/UpwardTranslation.lean`.

Sequentially perfect absorbing sources supply exact finite packets through
`hasExactFiniteForwardPackets_of_normal_of_sequentiallyPerfect`
(`UniformEquilibrium/Quitting/Projective/SequentiallyPerfectAbsorbingForwardPacket.lean`).
All-player normality, a reward bound, and one positive singleton reward are
the game hypotheses. `exists_sequentiallyPerfectSource_generating_floorFreePackets`
retains one source sequence before every charge request, with literal reversed
roots, restarted terminal payoffs, and exact charge equality. The full producer
uses fixed burn-in and retains the reward box, not the original horizon.
Separately, `punishmentFloor_le_quittingRootSequenceTailVector_of_rowPerfect`
(`UniformEquilibrium/Quitting/Classification/Existence/SequentiallyPerfectAbsorbingForwardSource.lean`)
proves the approximate punishment floor at every restarted date under the
explicit row-error bound. The same generic module proves that termination
after every restart forces nonsummable absorption. No reverse AKRS implication
is used in these source adapters.

`quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot`
(`UniformEquilibrium/Quitting/Projective/FixedBoxForwardCharacterization.lean`)
equates uniform-payoff existence, for normal four-player games with a positive
singleton reward, to weighted packets in the fixed box of radius `M+2` or
`HasQuittingPunishmentVectorNashRootWithSureQuitter`. The displayed reward bound
`M` is fixed before accuracy and charge. The forward proof uses the checked
AKRS forward trichotomy; the reverse uses the packet and sure-root payoff
consumers. This does not assert repeatability of the sure root or provide a
polynomial certificate.

`QuittingRenewedActualProfileSequence`
(`UniformEquilibrium/Quitting/Root/RenewedActualProfileDebtRecharge.lean`)
stores actual cap-attaining one-player updates, each literally the next source.
Its exact horizontal debt decomposition separates the owner's gain from
cross-player debt changes. A supplied per-phase total-debt drop `c` gives
cumulative horizontal injection at least `N*c` minus the initial source debt;
cumulative cross-player injection additionally pays the sum of owner gains.
These identities work for arbitrary finite player sets without a payoff-bound,
punishment-floor, exact-prefix, or no-uniform-payoff premise. They do not
construct a renewable source or turn its horizontal updates into charged edges.

`quittingLiteralExactWordBoxPath`
(`UniformEquilibrium/Quitting/Bellman/Finite/LiteralExactPrefixBoxPath.lean`)
decodes a supplied exact literal root word over an actual profile into the
full boxed predecessor relation, retaining endpoint payoff, root decoration,
charge, and length. Empty words retain the supplied source decoration.
`QuittingRenewedLiteralExactWordSequence.toRenewedPathSequence`
(`UniformEquilibrium/Quitting/Root/RenewedLiteralExactWordSequence.lean`)
uses those actual words and literally reuses the all-Continue-decorated
cap child as the next source. `finFour_renewedLiteralExactWord_capacityRecharge`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourRenewedLiteralExactWordCapacity.lean`)
applies the no-uniform-payoff capacity bound to this supplied sequence.
It gives linear horizontal capacity recharge, not a renewable source producer
or a bound on that recharge.

`sum_pathFamily_charge_add_boundary_le_sum_recharge`
(`MathUE/PathFamilyPotentialRecharge.lean`) states the exact-boundary
inequality for arbitrary path families without a positive minimum charge.
Its actual-word adapter in
`UniformEquilibrium/Quitting/Bellman/Finite/LiteralExactWordCapacityRecharge.lean`
allows empty words and arbitrary chosen source decorations. The same next
decorated source occurs on both sides of every horizontal seam.
`sum_crossPlayerDebtInjection_eq_sum_verticalDrop_add_gain_boundary`
(`UniformEquilibrium/Quitting/Root/RenewedActualProfileDebtRecharge.lean`)
retains the exact vertical drops, cap gains, and debt boundary as an equality.

`quittingFloorFreeRobustChargedRelation`
(`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`) is the
full relation of boxed payoff/root/payoff triples satisfying absorption-relative
Bellman residual and ordinary Nash-regret bounds. Bare payoff states and the
full edge space are compact; source, target, and absorption charge are
continuous. No punishment floor, support-local condition, or selected-root
restriction is imposed. A finite capacity bound is not supplied by this
definition or its topological properties.

`isQuittingFullExactRootPotential_add_one_of_robust_add_two`
(`UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`)
restricts the same robust potential to every exact Nash root in the smaller
box, for every nonnegative tolerance. The collision-adjusted actual singleton
roots in `UniformEquilibrium/Quitting/Root/CollisionAdjustedSingletonProbe.lean`
preserve binding upper coordinates and produce exact source Nash and the
literal successor at all sufficiently small positive rates.
`IsQuittingFullExactRootPotential.singletonFace_drift`
(`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`)
gives unit directional drift at every singleton lower face, including upper-face
intersections. `IsQuittingFullExactRootPotential.minimum_above_singleton` and
`IsQuittingFullExactRootPotential.exists_minima_strict_gap`
(`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMinimum.lean`)
put every full-box minimum strictly above every own singleton and produce an
attained strict value gap from the lower boundary. The location theorem needs
only a derivative at that minimum; the attained-gap theorem additionally uses
continuity and regularity on the stated boxes. These results pass the full
integration gate for signed rewards and arbitrary finite player sets, with nonemptiness
required for the boundary gap. They constrain a supplied potential; they do
not construct one or prove uniform-payoff existence.

`lowerBoxBoundary_minimum_partial_signs` and
`lowerBoxBoundary_minimum_derivative_toward_strictLower_pos`
(`MathUE/Analysis/LowerBoxBoundaryMinimum.lean`) retain the lower-face,
interior-coordinate and upper-face derivative signs at a boundary minimum,
and strict positive drift toward every strictly lower boxed target.
`IsQuittingFullExactRootPotential.not_quasiconvex`
(`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialQuasiconvexExclusion.lean`)
excludes quasiconvexity on the upper singleton rectangle without a matrix
assumption. It permits signed rewards and arbitrary finite nonempty players.
The same file's
`exists_positive_quittingRobustEdge_potential_violation_of_quasiconvex`
internally produces a rejecting edge at every nonnegative tolerance, retaining
the same table, potential, exact Nash root and literal successor. Positive
absorption is a conclusion, not additional source data. These declarations
pass the full integration gate; they do not supply a potential producer.

`IsQuittingFullExactRootPotential.radialReversal`
(`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialReflection.lean`)
selects a lower-boundary minimizer for every global minimum on box three,
including upper-face minima. The same point gives radial derivative at most
minus half the minimum singleton gap, a boxed reflected point, and the entire
boxed segment with parameter in `[0,2]`. Rewards are bounded by one and own
singletons are nonnegative.
`not_isQuittingFullExactRootPotential_totalDegree_le_two`
(`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialQuadraticExclusion.lean`)
excludes every real polynomial of total degree at most two after coefficient
cancellation, without convexity or a Hessian-sign condition.
`not_isQuittingFullExactRootPotential_coordinateAffine`
(`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMultiAffineExclusion.lean`)
excludes coordinate-affine potentials with the stated continuity and derivative
regularity; its polynomial consumers allow every square-free interaction order.
Neither exclusion assumes that the global minimum is interior.

`IsQuittingFullExactRootPotential.directionalThirdDerivative`
(`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialThirdDerivative.lean`)
uses C³ regularity on an open neighborhood of the box. One boundary minimizer,
direction and segment point jointly witness radial reversal and an actual
directional third derivative at least three times the singleton gap. This is
not a fixed mixed-partial bound or a uniform gap over all potentials.
`quittingGame_noUniformPayoff_iff_noSureRoot_and_restricted_rationalPotential`
(`UniformEquilibrium/Quitting/Projective/RestrictedPolynomialForwardCharacterization.lean`)
strengthens the existing characterization for bounded nonnegative-singleton
Fin4 tables with a positive own singleton. It internally produces the same
rational tolerance and polynomial with degree at least three, failure of
multi-affinity, and the joint minimum conditions at every global minimum.
The named checks, separate standard-axiom checks and full integration gate pass.
No concrete polynomial or general Fin4 equilibrium is produced.

`not_isQuittingFullExactRootPotential_monotone_polynomial_transform`
(`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMonotoneTransformExclusion.lean`)
excludes a C¹ outer transform of either an arbitrary quadratic or an arbitrary
multi-affine polynomial, under the same bounded-reward and nonnegative-own-singleton
hypotheses. The outer function may be weakly increasing or weakly decreasing
on the polynomial's entire box image, with flat parts allowed. Its derivative
bound is selected internally on that compact image; no uniform slope bound
is supplied. The named dependency check, separate standard-axiom check and
full integration gate pass.

`quittingGame_noUniformPayoff_iff_noSureRoot_and_quantitative_rationalPotential`
(`UniformEquilibrium/Quitting/Projective/QuantitativePolynomialForwardCharacterization.lean`)
retains one polynomial and rational tolerance for all added shape and curvature
conclusions, under the original bounded normal Fin4 and positive-own-singleton
hypotheses. Every singleton-box minimum obeys the signed curvature account;
the mixed-partial and least-Hessian extrema are separately attained internally.
`quittingRobustPotential_not_singletonBox_representations_of_simplex`
(`UniformEquilibrium/Quitting/Projective/SingletonBoxRepresentationExclusions.lean`)
excludes additive and regular scalar-composition representations on the closed
box from a nonnegative simplex with nonnegative matrix image. The outer
function need not be monotone; standard Q is not an extra hypothesis there.
`isQuittingRobustPotentialWithCharge_iff_div` and its curvature consumers
(`UniformEquilibrium/Quitting/Projective/RobustPotentialChargeScale.lean`)
normalize any positive charge coefficient without changing the table, edge,
box or tolerance. Zero-charge constants are admitted separately. These named
checks, separate standard-axiom checks and full integration gate pass.
None constructs a polynomial or solves an additional game class.

`exists_rational_exact_solo_rejection_of_standardQ_quasiconvex`
(`UniformEquilibrium/Quitting/Projective/RationalExactSoloRejection.lean`)
passes its silent named check. For a rational bounded reward table with standard Q
and a quasiconvex rational polynomial, it internally selects one owner,
positive rational quitting rate below one, rational source and literal successor.
The root is exact Nash against that source, absorption equals the selected rate,
and the potential drop is less than three quarters of absorption. The endpoints
lie in the stated box. This is an annotated one-stage rejection witness, not a
behavioral equilibrium, approximate-root search, or general decision algorithm.
Its exhaustive axiom audit and full silent integration check also pass.

`exists_rational_robust_rejection_of_excluded_polynomial`
(`UniformEquilibrium/Quitting/Projective/ExcludedPolynomialRationalRejection.lean`)
produces a rational source/root pair for every positive rational tolerance,
under the unit reward bound and nonnegative own singletons, when the canceled
polynomial is quadratic or multi-affine. The source and exact successor are
boxed, absorption is positive, every source-based regret is strictly below
tolerance times absorption, and the potential drop is strictly below absorption.
`rationalQuittingPotentialRejectionSearch_eventually_succeeds_of_excluded_polynomial`
and `rationalQuittingPotentialRejectionSearch_sound`
(`UniformEquilibrium/Quitting/Projective/RationalPotentialRejectionSearch.lean`)
prove eventual finite-budget success and the literal robust interpretation of
the actual returned pair. The executable test uses exact rational evaluation
and accepts non-strict regret bounds. The checks include a silent named build,
separate returned-pair consumer and standard-axiom audit, and the full build.
Neither theorem gives rational exact Nash, an effective cutoff, or a denominator
bound.

`exists_finFourBoundedSinglePivotPolynomialObstruction_of_no_uniformPayoff` and
`exists_finFour_no_uniformPayoff_iff_exists_boundedSinglePivotPolynomialObstruction`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourBoundedSinglePivotPolynomialObstruction.lean`)
give the decision-preserving normalization from arbitrary real Fin4 rewards.
Bare no-UE data produce an actual single-pivot no-UE table, an integer bounding
that table, and its positive reciprocal scaling to unit-bounded rewards. The
scaled singleton vector is positive only at the produced pivot. A fresh call to
the polynomial characterization produces one tolerance and expression with
robust drift on box three, canceled degree at least three, non-multi-affinity,
and the stated restrictions at every global minimum. Common scaling preserves
the whole-game uniform-payoff semantics through
`quittingGame_exists_uniformPayoff_scale_iff`
(`UniformEquilibrium/Quitting/Transform/PositivePayoffScaling.lean`), delegating
to the existing stochastic-game affine-payoff transport. The final equivalence
is existential over tables; it assumes no rational reward table and transports
no old polynomial certificate between boxes.
The normalization chain passes a silent named build and expanded source-facing
consumer check, the full silent default build, and the exhaustive production
axiom audit.

`pairedFacePotential_boundedCompletion_face_drift` and
`pairedFacePotential_boundedCompletion_not_fullRoot`
(`UniformEquilibrium/Quitting/Examples/PairedFacePotentialBoundedCompletion.lean`)
separate the singleton-face inequalities from the full exact-root relation.
The same coupled polynomial satisfies every singleton-face inequality above
the singleton vector but fails the full-root inequality for every unit-bounded
completion of the prescribed singleton columns. Its generic geometry in
`MathUE/Analysis/Examples/PairedFacePotentialGeometry.lean` identifies the actual
canonical Hessian, proves that its spectrum is exactly `96, 32, -64`, derives
the least eigenvalue `-64`, and produces a non-top minimizing vertex internally.
The repeated `-64` eigenvalue is represented by two independent eigenvectors
in `MathUE/Analysis/Examples/PairedFacePotential.lean`. No spectral certificate,
minimizer, standard-Q assumption, or behavioral equilibrium is supplied or
inferred.

`Math.PairedFacePotential.translatedPotential_not_quasiconvexOn_singletonBox`
(`MathUE/Analysis/Examples/PairedFacePotentialGeometry.lean`) explicitly rejects
quasiconvexity on the singleton box: two endpoints have value `-8`, while their
midpoint has value `56`. The reflection and directional third-derivative
theorems retain a strict interior peak on the same reflected segment; this
same-segment conclusion is also retained by the polynomial characterization.

The arithmetic cases in `MathUE/Analysis/Examples/ReflectionBoundaryArithmetic.lean`
record the adaptive reflection endpoint and failures of unsigned or fixed-cap
extensions. `ConstantSignedNormalTable.punishment_vector` and `all_normal`
(`UniformEquilibrium/Quitting/Examples/ConstantSignedNormalTable.lean`) prove
that normality does not imply nonnegative own singletons, using the constant
reward vector `(1,-1,0,0)`. Positive scaling preserves its negative singleton.

`midpoint_thirdDerivative_integral_identity` and
`midpointThirdDerivativeKernel_weighted_mass`
(`MathUE/Analysis/MidpointThirdDerivativeIntegral.lean`) give the exact weighted
third-derivative midpoint identity and kernel mass `1/6`. The two half-interval
identities use ordinary iterated derivatives, under third-order regularity at
every point of the closed segment, including both endpoints.
The paired example and integral identity pass silent named checks, the full
silent default build, and the exhaustive production axiom audit.
The strengthened same-segment conclusions and the remaining reflection
boundary examples pass the same full integration gate, completing the packet's
mathematical coverage. The surviving higher-degree polynomial alternative
remains open.

The shape examples and boundary cases are integrated and pass silent named,
separate standard-axiom and full build checks. `upper_two_fixture`
(`UniformEquilibrium/Quitting/Examples/CollisionAdjustedProbeBoundary.lean`)
retains the exact collision correction and boxed upper-face freeze for every
positive rate below one half. `not_standardQ`
(`MathUE/Analysis/Examples/NonQLinearFace.lean`) proves that the convex
positive-face-drift example fails the matrix hypothesis. The exact charge
normalization in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialChargeScale.lean`
retains all full-root quantifiers. The one-player and zero-table solo self-loop
producers in
`UniformEquilibrium/Quitting/Examples/ExactRootPotentialPlayerCountBoundary.lean`
reject every potential, without shape or regularity assumptions; the empty-player
case instead has zero absorption for every root. Together with the coupled
cubic example, these complete the shape packet's boundary tests. They do not
exclude every polynomial or solve an additional game class.

The literal conversions in
`UniformEquilibrium/Quitting/Projective/RobustChargedRelationPacketAdapter.lean`
preserve roots, values through the endpoint, horizon, and total charge in
both directions between robust paths and floor-free finite packets.
`UniformEquilibrium/Quitting/Projective/RobustChargedRelationCapacity.lean`
specializes finite-horizon attainment and upper semicontinuity to this full
relation; its all-horizon capacity is Borel measurable under finite budget.
`UniformEquilibrium/Quitting/Projective/RobustChargedRelationTranslation.lean`
translates both endpoints by the same nonnegative vector, keeps the literal
root and charge, and bounds endpoint displacement proportionally to
absorption. The capacity itself need not be smooth.

`quittingRobustChargedEdge_charge_add_smoothedCapacity_target_le_source`
(`UniformEquilibrium/Quitting/Projective/RobustChargedRelationSmoothing.lean`)
constructs a globally smooth potential from finite outer capacity by one-sided
convolution of its Borel zero extension. It retains the full absorption drift
on every inner edge, with box radius reduced by one and tolerance divided by
four. The generic smoothing and compact-domain zero-extension lemmas live in
`MathUE/Analysis/OneSidedCapacitySmoothing.lean` and
`MathUE/Analysis/CompactSubtypeZeroExtension.lean`.
`exists_evalReal_charge_drift_of_contDiff`
(`MathUE/Interval/RationalPolynomialChargedDrift.lean`) constructs one native
rational polynomial preserving every supplied edge's full charge drift on a
compact convex domain. It uses an absorption-proportional displacement bound
and actual derivative approximation, including zero-charge edges. Neither
the smooth potential nor the polynomial is assumed in the capacity-to-potential
construction.

`exists_quittingFloorRobustChargedRelation_rationalPotential_of_finiteBudget`
(`UniformEquilibrium/Quitting/Projective/FloorRobustPolynomialSeparator.lean`)
also proves the construction when both endpoints satisfy tolerance-dependent
coordinate floors. The floor vector is arbitrary, not necessarily rational or
a punishment vector; the theorem concerns the entire floor-bearing relation.
`exists_quittingRobustChargedRelation_rationalPotential_of_finiteBudget`
(`UniformEquilibrium/Quitting/Projective/RobustChargedRelationPolynomialSeparator.lean`)
proves the floor-free construction.
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
(`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`)
characterizes failure of uniform-payoff existence in a normal four-player game
with a positive singleton payoff: no punishment-vector Nash root with a sure
quitter, and one rational polynomial with full charge drift on every robust
edge at a positive rational tolerance at most one quarter, in the fixed reward
box enlarged by two. The forward implication constructs the polynomial from
finite capacity in the box enlarged by three; no smoothness or polynomial
producer is an extra hypothesis. No concrete polynomial counterexample or
complete polynomial-checking algorithm is supplied.

The boundary examples are literal game-semantic statements.
`UniformEquilibrium/Quitting/Root/AllContinueWeightedRoot.lean` records the
zero-charge root and the failure of negative-translation invariance.
`UniformEquilibrium/Quitting/Examples/ZeroRewardEntryFloor.lean` and
`UniformEquilibrium/Quitting/Examples/NonNormalFloorFailure.lean` distinguish
the deleted entry endpoint from the retained floor and expose the role of
normality. `UniformEquilibrium/Quitting/Examples/SureRootNonrepeatability.lean`
computes the semantic punishment vector and an actual exact terminal Nash
profile whose prescribed sure root is not repeatable against its own payoff.
`UniformEquilibrium/Quitting/Examples/ThreeOwnerRobustCycle.lean` rules out
every potential on a literal charged three-cycle; composing it with the
polynomial characterization proves `ThreeOwnerRobustCycle.exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Quitting/Examples/ThreeOwnerRobustCycleUniformPayoff.lean`.
This conclusion concerns that table only and does not select a numerical payoff.

`quitting_pureTimeCap_literalPrefix_transport`
(`UniformEquilibrium/Quitting/Root/ExactCapClockTransport.lean`) transports an
actual pure-time cap through exact Nash roots with positive owner Continue
probability, retaining the literal updated profiles and exact debt multiplier.
`UniformEquilibrium/Quitting/Root/PureTimeCapChild.lean` fixes the single-profile
child constructor and its cap-attaining owner's zero debt and exact gain.
`finFour_summable_actualExactPrefix_hazard_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourActualPrefixHazard.lean`)
derives summable marginal hazards for a supplied nested exact-root sequence
under no uniform payoff. The finite-block adapter uses actual reversed
prefixes, not independent supplied paths. The generic survival consequences
in `UniformEquilibrium/Quitting/Paths/SummableRootSurvival.lean` include
uniform late-window bounds and a positive floor for every finite prefix
when each root has positive survival.
`UniformEquilibrium/Quitting/Paths/InfiniteJointSurvivalDebt.lean` identifies
the limit of the actual finite prefix products, proves its strict positivity
under these hypotheses, and gives the cap owner's debt bound by this limit
times the initial debt floor.
`eventually_resetChild_everyExactRoot_debtDrop_and_absorptionFloor`
(`UniformEquilibrium/Diagnostics/Quitting/LateResetChildCapPinExit.lean`)
pins the actual reset child's cap near the singleton payoff and obtains a
debt drop and absorption floor for every exact root against that child's
payoff. These are conditional source tools; they do not yet construct a
renewable reset sequence or a returned source.

`HasTerminalExploitabilityGap.exists_infiniteSurvival_fixedOutsiderResponse`
(`UniformEquilibrium/Quitting/Root/NestedCapChildInfiniteSurvivalDebtor.lean`)
uses the actual infinite joint-survival product before the starting depth; at each requested depth,
one outsider and one response are then fixed for all later literal children.
It retains the copied behavioral response, exact survival-scaled gain, and
debt bounds using both the actual window and infinite-survival factors.
`HasTerminalExploitabilityGap.exists_late_fixedOutsider_halfGap`
(`UniformEquilibrium/Quitting/Root/LateResetFixedOutsiderHalfGap.lean`)
chooses a starting child beyond any requested depth, then one outsider and
one bounded finite-or-Never attained response. At every later child it
retains the exact copied-response gain and both its gain and debt bounds by
half the game-level gap. This late bound is independent of the initial
infinite-survival product; positive initial survival is still used to
transport the owner's cap along the supplied source.
`exists_coherentOutsiderCapClock_on_pureTimeCapChildren`
(`UniformEquilibrium/Quitting/Root/CoherentPureTimeCapClock.lean`) selects
complete caps coherently, with each next clock either immediate Quit or the
previous clock shifted by one date, including Never. The same module proves
the eventual-shift/cofinal-reset alternative and its exclusivity, including
permanent Never. Summable total marginal hazards also force the
forced-Continue opponent-survival coefficients to one, without distinctness
or early positive survival, in
`UniformEquilibrium/Quitting/Paths/SummableRootSurvival.lean`.
`UniformEquilibrium/Quitting/Root/NestedChildBellmanEndpointDifference.lean`
states the actual child Bellman identities and the expanded outsider endpoint
difference.
`UniformEquilibrium/Quitting/Root/NestedOwnerRootNashSeamSummable.lean`
proves the zero-debt owner's forced-Continue action is root-optimal and
separately proves summability of the first, second, and fourth outsider seam
terms from summable owner hazard. It does not make outsider roots Nash or
bound the third, nonlocal payoff-displacement term by a summable sequence.

`exists_terminalCapChildDisplacement_limit_series`
(`UniformEquilibrium/Quitting/Root/TerminalChildPayoffDisplacementSeries.lean`)
identifies the literal child-minus-source payoff limit from any starting
depth as its displacement times the infinite forced-root product plus the
weighted series of owner-correction charges. Both the absolute charge tail
and the weighted series are explicitly summable. The actual genealogy and
summable marginal hazards are inputs; Nash, positive survival, and a
distinct observer are not needed for this series identity.
`quittingForcedContinueOwnerCorrection_eq_sum_opponentCoalitionMass`
(`UniformEquilibrium/Quitting/Root/ForcedContinueOwnerCorrectionCoalitionSum.lean`)
identifies each correction as the exact owner-deleted coalition average of
the payoff without the owner minus the payoff with the owner inserted.
The empty coalition contributes continuation minus singleton payoff.
`MathUE/DisplacementSeamScalarBoundaries.lean` distinguishes finite variation
from summability of values: harmonic displacement has summable increments
and zero limit but nonsummable values. A nonzero limiting displacement with
survival coefficient tending to one and a summable remainder gives a seam
that neither tends to zero nor is summable. These are scalar results, not
counterexample games.

`exists_offMinimum_collar_on_completeCap_singletonSlab`
(`UniformEquilibrium/Diagnostics/Quitting/CompleteCapSingletonSlabCollar.lean`)
gives a uniform positive debt margin above a positive global lower bound on
the semantic carrier's closed singleton-cap slab. No attaining minimizer is
an input. Its parameter-family corollary requires neither compactness of the
parameter set nor attained responses.
`UniformEquilibrium/Diagnostics/Quitting/CapResponseSegmentCollar.lean`
applies this to the entire closed interval of actual unilateral stopping-law
mixtures. The moved player's complete cap is constant, and an attained
response makes its debt equal to the uninstalled fraction times its old
debt.
`UniformEquilibrium/Diagnostics/Quitting/StationaryQuitNowSegment.lean`
provides a literal first-root installation followed by the unchanged
stationary source. It agrees with the mixture's full payoff/cap pair, retains
the original suffix at cuts one and two, and bounds the installed row's
hazard from below by its parameter. No positive-survival assumption is needed
for these profile equalities, including null continuation histories.
The underlying complete stopping-law identity is in
`MathUE/Probability/DiscreteHazardQuitZeroInstallation.lean`.
`exists_quittingStationaryQuitNowSegmentTwoCut_offMinimum`
(`UniformEquilibrium/Diagnostics/Quitting/StationaryQuitNowSegmentTwoCutReturn.lean`)
places this installation between literal cuts one and two. Positive source
excess determines a hazard scale for which the actual exit satisfies the
quantitative off-minimum alternative. No paid splice or return to a minimum
is asserted. `eventually_capResponseSegment_exactRoot_debtDrop_and_absorption`
(`UniformEquilibrium/Diagnostics/Quitting/CapResponseSegmentExactRootExpenditure.lean`)
gives uniform debt-drop and absorption floors for every sufficiently late
exact root at any fixed proper installation parameter, from a positive
source-debt floor and convergence of the owner's cap to its singleton.
Source attainment and the debt floor need hold only eventually.

`HasTerminalExploitabilityGap.exists_late_childRestart_capPinDichotomy`
(`UniformEquilibrium/Diagnostics/Quitting/LateResetChildRestartAssembly.lean`)
attaches a coherent cap clock to the same selected late outsider and response.
It retains bounded finite-or-Never seed attainment, original gap debt, and
all later copied-response gain identities and half-gap floors. At sufficiently
late resets, the actual child is cap-pinned, and every exact root against its
payoff has the stated debt-drop and absorption floors. The output is a
shift/reset dichotomy; by itself it does not construct the subsequent exact
ray from that reset child.
`finFour_lateResetChild_exists_directShiftedCapRestart`
(`UniformEquilibrium/Diagnostics/Quitting/LateResetDirectSourceRestart.lean`)
constructs that ray from the unchanged reset child. Its all-positive-survival
branch keeps the reset owner's profitable immediate-Quit cap as its initial
choice. Its other branch retains the old zero-debt anchor and starts the
unique sure quitter's shifted cap at the literal last-zero child.
`LateResetChildCapPin.totalDebt_ge_minimum_add_expenditure`
(`UniformEquilibrium/Diagnostics/Quitting/LateResetChildCapPinExit.lean`)
places the reset child's debt above any global carrier lower bound by the
fixed cap-pin expenditure; the proof selects an exact root internally.

`exists_quittingActualExactPrefixRay`
(`UniformEquilibrium/Quitting/Paths/ActualExactPrefixRay.lean`) recursively
constructs an infinite sequence of literal exact-root prefixes from any
actual profile. The same module transports a finite-or-Never attained cap
along an arbitrary supplied ray with summable hazards and positive survival
on its chosen tail, retaining one positive debt floor. A prescribed sure
deadline and zero anchor debt persist under every exact prefix. This generic
construction does not prove that its chosen roots have positive survival.
`QuittingActualExactPrefixRay.initial_or_lastZero_uniqueSure_shiftedCapTail`
(`UniformEquilibrium/Diagnostics/Quitting/ActualExactPrefixRayRestart.lean`)
applies to every actual ray from a zero-debt anchor that quits surely by a
finite deadline. A positive terminal gap supplies summable hazards. Either
one fixed outsider's cap shifts from the initial source, or the last
zero-survival root's unique sure quitter starts a shifted cap at its literal
child. Both alternatives retain bounded finite-or-Never attainment and one
positive debt floor. No stationary tail replacement or forward infinite
chronology is inferred. `quittingLiveMass_update_succ_eq_zero_of_sureOpponentAt`
(`UniformEquilibrium/Quitting/Root/CapChildDeadlineAbsorption.lean`) states
the anchor's deadline absorption after every distinct player's behavioral
deviation.
`not_immediateQuitAttainsTerminalCap_of_sureQuitter_of_positiveDebt`
(`UniformEquilibrium/Quitting/Root/NestedImmediateQuitCapExactPrefixExit.lean`)
proves that the sure quitter's positive-debt literal child cannot have an
immediate-Quit cap. This prevents identifying that branch with a cap-pinned
stationary replacement.

`UniformEquilibrium/Quitting/Root/CopiedCapResidualDebt.lean` computes the
residual debt of copying the prescribed root before a cap response and the
ordinary mixed-root Nash defect at the cap-raised tail. This is not a bound
on every supported action's regret.
`HasTerminalExploitabilityGap.exists_deadline_paidFirstDisagreement`
(`UniformEquilibrium/Diagnostics/Quitting/DeadlinePaidFirstDisagreement.lean`)
selects a distinct paid observer before a zero-debt owner's sure deadline,
with opponent reach at least the gap divided by twice the reward bound.
It jointly retains a prescribed-support source time, a cap-attaining receiving
time that is at most the deadline or Never, their payoff gap, and their exact
identities in the paid row. The same observer's debt and the same receiving
response's gain over the actual prescribed payoff also remain explicit.
`UniformEquilibrium/Diagnostics/Quitting/ActualReversePrefixAtomTransport.lean`
transports terminal payoff-difference atoms through common literal prefixes.
It does not by itself identify a marked row's conditional data.
`UniformEquilibrium/Quitting/Paths/ActualReversePrefixMarkedSuffix.lean`
separately proves literal equality of the complete suffix profile, preservation
of its live roots, and the exact prefix factor for every later live mass.
`UniformEquilibrium/Quitting/Paths/ActualPrefixPayoffLimit.lean` proves payoff
convergence from summable hazards and actual nesting, without a Nash premise.
`allContinue_exactNash_and_fixedPoint_of_tendsto_terminalPayoff`
(`UniformEquilibrium/Quitting/Paths/ActualPrefixAllContinueLimit.lean`) combines
root convergence, payoff convergence, and closedness of exact root Nash.
`finFour_positiveSurvival_capChild_paidRow_source`
(`UniformEquilibrium/Diagnostics/Quitting/PositiveSurvivalCapChildSource.lean`)
assembles the actual exact recursion, positive survival, initial cap, and
positive terminal gap into one infinite-survival floor and all-depth literal
cap children with persistent owner gain, zero owner debt, deadline absorption,
and jointly selected bounded paid responses. The infinite survival and
summability conclusions are derived, not input fields.
`finFour_actualExactPrefix_frontLimit_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/ActualExactPrefixFrontLimit.lean`)
derives one payoff limit and convergence of every fixed reverse-front root
and continuation coordinate, with an exact all-Continue limiting root. It
does not need the positive-survival assumption.

`quittingBehaviorExactFiniteFirstCoalitionMass_eq_terminalOutcomeMass`
(`UniformEquilibrium/Quitting/Paths/BehaviorFirstStoppingPairLaw.lean`)
identifies the independent-clock formula with the existing executed terminal
coalition probability. The same module proves the square-root inequality
for any two distinct two-player coalitions in any finite-player game.
`UniformEquilibrium/Quitting/Paths/StageCoalitionMass.lean` and
`UniformEquilibrium/Quitting/Paths/StageCoalitionStoppingLaw.lean`
supply its time-disintegration and product-factorization dependencies.
`exists_pair_terminalOutcomeMass_eq_one_of_terminalPairMass_eq_one`
(`UniformEquilibrium/Quitting/Paths/PairOnlyTerminalLawRigidity.lean`) proves
that an actual terminal law with total pair mass one is concentrated on one
pair. The same module excludes the uniform one-sixth law on the six Fin4
pairs, although its two-coordinate square-root inequality holds.
This does not characterize general coalition-law realizability.
`exists_actual_finFour_pairProjection_sharpProfile`
(`UniformEquilibrium/Quitting/Paths/FinFourPairSharpness.lean`) constructs
actual profiles attaining the square-root boundary for any two distinct
Fin4 pairs, whether overlapping or disjoint. Generic player relabeling is
proved in `MathUE/Probability/FirstStoppingCoalitionRelabel.lean` and its
behavioral adapter in
`UniformEquilibrium/Quitting/Paths/FirstStoppingCoalitionRelabel.lean`.
`MathUE/AffinePairRootCrossingAttainment.lean` proves attainment of the least
feasible crossing and the exact two-coordinate feasibility criterion.
`MathUE/Probability/OverlappingFirstStoppingEquality.lean` supplies the
zero-continuation one-row equality case.
`MathUE/Probability/OverlappingFirstStoppingPositiveContinueEquality.lean`
proves the complementary positive-continuation one-row necessity, retaining
the all-zero hazard degeneracy.
`MathUE/Probability/OverlappingFirstStoppingInfiniteRecurrence.lean` supplies
the exact infinite first-row recurrence, including zero continuation.
`equalFirstSecondBeforeThirdMass_eq_one_iff_deterministicFiniteAtom`
(`MathUE/Probability/OverlappingFirstStoppingDeterministicAtom.lean`) identifies
a mass-one pair event with a common deterministic finite atom and strict
survival of the third clock, allowing its arbitrary later or Never behavior.
`overlappingMass_sqrt_sum_eq_one_iff_deterministic_or_chronological`
(`MathUE/Probability/OverlappingFirstStoppingChronologicalEquality.lean`)
classifies equality for arbitrary complete stopping laws: either mass-one
endpoint, or an initial silent prefix followed by one of three positive-mass
chronological configurations. The staggered configurations retain a literal
later deterministic residual atom; irrelevant tails remain unrestricted.
`exists_pureTime_gain_half_affinePairRootLeastCrossing`
(`UniformEquilibrium/Quitting/Terminal/PairMassForcingConsumer.lean`) turns
supplied affine lower bounds on two pair masses into a profitable finite-time
or Never deviation for every profile. Its positive gap depends on the
forbidden zero-error corner. The module also proves terminal exploitability
and no-uniform-payoff consequences; it does not construct those affine bounds
from an arbitrary reward table.
`UniformEquilibrium/Quitting/Terminal/FinFourAllPairCrossingConsumer.lean`
takes the maximum of the fifteen pair crossings, proves it is attained, and
gives the corresponding all-profile exploitability bound, pure-time response,
and conditional no-uniform-payoff consumer. With nonnegative slopes it also
characterizes simultaneous feasibility of all fifteen pair projections, not
joint realizability of the six masses.
`UniformEquilibrium/Quitting/Examples/OverlappingFirstStoppingBoundary.lean`
computes complete stationary and rational clock laws and refutes the nested-
coalition extension and the separate-square-root continuation estimate.
`fixedCardProductRow_eq_deterministic`
(`MathUE/PMFProduct/FixedCardinalityRigidity.lean`) proves a local rigidity
result for any fixed coalition size at least two: if every supported nonempty
product-row action has that size and one exists, every marginal is pure.

`exists_twoSupported_simplex_preserving_first_improving_second`
(`MathUE/TwoCoordinateSparseSimplex.lean`) replaces any finite mixture by one
supported on at most two atoms while preserving one real expectation and
weakly increasing another. Its three-marginal version retains independence
and performs the replacement successively for arbitrary finite trilinear
kernels. A continuous objective monotone in the second expectation therefore
has a global maximizer with all three marginals two-supported. No assumption
that every maximizer is sparse is made.
`exists_twoSupported_canonicalOverlap_maximizer_on_dates`
(`MathUE/Probability/FiniteOverlapSparseMaximizer.lean`) applies this to
canonical complete stopping laws on any finite menu of natural-number dates
plus Never. Exact indicator identities, embedding transport, and reconstruction
cover every law supported on that menu, not merely supplied encodings.
`exists_twoSupported_canonicalOverlap_compression_on_dates`
(`MathUE/Probability/FiniteOverlapSparseCompression.lean`) preserves the first
overlap mass exactly and weakly increases the second, on the same finite
menu. The simultaneous lower-threshold feasibility problem therefore has a
solution exactly when it has one with three two-supported marginals. The
underlying PMF expectation and support-cardinality bridges are shared in
`MathUE/Probability/ThreeIndependentFiniteLaws.lean`. Infinite-support
compression and preservation of both masses exactly are not asserted.

| Family | Canonical import | What it exports |
| --- | --- | --- |
| Compact-edge path capacity | `MathUE/ChargedPathCode.lean` and `MathUE/CompactChargedPathCapacity.lean` | `exists_path_eq_compactFiniteHorizonMaxCharge` attains finite-horizon charge from each initial state for compact state and edge spaces, Hausdorff states, and continuous source, target, and charge. Codes decode to literal paths with exact endpoints and charge, including nil at dead ends. `upperSemicontinuous_compactFiniteHorizonMaxCharge` and `measurable_value_of_compact_edges` give finite-horizon upper semicontinuity and Borel measurability of the existing all-horizon value under finite budget. The latter is not asserted upper semicontinuous. The countable-supremum identity needs no topology. |
| Same-root uniform payoff from instant punishment | `UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterPayoff.lean` | `quittingPunishmentSureRootTarget_isUniformEquilibriumPayoff_and_floor` proves that the literal successor payoff of a supplied exact punishment-vector Nash root with a sure quitter is a uniform-equilibrium payoff and lies above every punishment value. The target and root are fixed before every error request. It requires neither normality nor a joint punishment-vector realizer. |
| Unrestricted optimality of the rational repair example | `UniformEquilibrium/Diagnostics/Quitting/PivotRepairRationalOptimality.lean` | `exploitability_ge_1584_div_5243_of_pivotBehavior` bounds every actual behavioral pivot replacement against the fixture opponents. `optimizerPivotBehavior_exploitability_eq` supplies an attaining strategy, and `pivotBehavior_exploitability_infimum_eq` states the exact behavioral infimum. This positive fixed-opponent value is not a gap over all players' strategies. |
| Finite sure-quitter characterization of instant punishment | `UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean` | `quittingInstantPunishmentεEquilibriumExistence_iff_sureQuitterPunishmentVectorNashRoot` identifies the literal instant-punishment branch with existence of an exact product Nash root against the coordinatewise punishment vector having a sure quitter. It holds for arbitrary finite player sets and signed rewards, without normality or a joint profile realizing that vector. |
| Two actual best responses after rational pivot repair | `UniformEquilibrium/Diagnostics/Quitting/PivotRepairRationalSequentialReplacement.lean` | `afterOneProfile_eq_update_optimizer` and `afterTwoProfile_eq_update_afterOne` identify the literal sequential Never replacements. Each replacement attains its player's unrestricted behavioral cap. `afterTwo_payoff` and `afterTwo_cap` both give `(1,7,7,0)`; `afterTwo_isExactTerminalNash` proves zero-error terminal Nash for that actual profile. This closes the explicit example, not a general best-response convergence theorem. |
| Floor-free finite forward producers | `UniformEquilibrium/Quitting/Projective/FloorFreeForwardPacketInputRemoval.lean` | `hasFloorFreeExactFiniteForwardPackets_iff_exact` and `hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted` remove the punishment-floor input under normality and a positive coordinate reward bound, in any fixed coordinate box. The box need not contain the rewards. The packet conversions delete a fixed number of initial construction rows chosen before the charge request; the suffix constructors expose the retained horizon, roots, and values. No actual-tail realization or arbitrary-game producer is assumed or constructed. |
| Finite endpoint-error punishment floors | `UniformEquilibrium/Quitting/Bellman/Finite/FiniteEndpointErrorPunishmentFloor.lean` | `quittingPunishmentFloor_le_of_finite_endpointErrors_after_burnIn` puts every displayed value after a fixed cutoff above punishment minus `τ`, under normality, a coordinate reward bound `M > 0`, an initial coordinate lower bound `-B`, and both pure-endpoint inequalities with error at most `min (τ/2) (τ²/(8*M))`. The cutoff satisfies `M+B < L*τ²/(8*M)`. No initial floor, exact Bellman equation, or actual-tail realization is assumed. This finite theorem does not itself construct all-accuracy, all-charge packets. |
| Exact rational repair example | `UniformEquilibrium/Diagnostics/Quitting/PivotRepairRationalOptimizer.lean` | `optimizerMass_objective_eq` attains the global repair-LP lower bound `1584/5243` for the explicit four-player reward table. `optimizerGeometric_payoff`, `optimizerGeometric_cap`, and `optimizerGeometric_debt` give the actual geometric profile's complete payoff, unrestricted behavioral cap, and debt vectors; `optimizerMass_geometric_exploitability_eq` proves its exploitability equals the optimum. This is one fixed-opponent example, not convergence of an iterative repair algorithm. |
| Quantitative finite menus from pivot repair | `UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteMenuConsumer.lean` and `UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralApproximation.lean` | `exists_finite_menu_of_feasible_mass_signed_of_reward_bound` constructs actual finite menus from any feasible repair point with error bounded by the LP objective, a requested approximation error, and `4 * M` times the censored late-finite mass, for any supplied coordinate reward bound `M`. It retains the exact censor laws and survival identity. `exists_law_boundary_approximation_of_reward_bound` preserves the payoff vector and Never atom with boundary error `2 * M * firstAtom`; zero nonpivot singleton rewards sharpen this to `M * firstAtom`. A positive pivot singleton is needed only for the additional LP-based survival budget, not for signed finite-menu conversion. |
| Small pivot-repair source characterization | `UniformEquilibrium/Quitting/Terminal/PivotRepairUniformPayoffCharacterization.lean` and `UniformEquilibrium/Quitting/Terminal/SinglePivotRepairSourceEquivalence.lean` | `smallPivotRepairValue_iff_exists_uniformEquilibriumPayoff` identifies selection of actual finite nonpivot laws with arbitrarily small inner-LP values with existence of one fixed uniform-equilibrium payoff target. This holds for arbitrary signed rewards and any distinguished pivot. For canonical singleton tables, `singlePivotFiniteMenuScalarSource_iff_smallPivotRepairValue` also identifies the existing same-menu scalar source with this LP source, retaining deadline zero. These equivalences do not select the opponent laws or prove either source for arbitrary games. |
| Absorption-weighted finite forward packets | `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketTranslation.lean` | `hasExactFiniteForwardPackets_rewardBox_iff_exists_absorptionWeightedBox` equates, for four players, exact support-local packets in the reward box and absorption-weighted Bellman/regret packets in a larger box chosen before every accuracy and charge request. `QuittingAbsorptionWeightedForwardPacket.repair` retains the horizon and initial value, changes each root coordinate by at most `ρ` times its original absorption, retains at least half the full original charge, and bounds value error by `17 * B * ρ` and support/floor error by `32 * B * ρ`. The reverse translation has the literal Bellman residual `2 * δ` times row absorption. `quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets` consumes a supplied weighted producer; this module does not supply an arbitrary-game producer. Fixed-box necessity under normality and a positive singleton is provided separately by `quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot`. |
| Reward-box reduction of finite packets | `UniformEquilibrium/Quitting/Projective/FiniteForwardPacketRewardBoxReduction.lean` | `hasExactFiniteForwardPackets_rewardBox_of_box` converts a four-player exact-packet producer in a fixed larger box to one in the reward box, including a zero reward bound. `QuittingFiniteForwardPacket.clipSuffixLogarithmic` selects a cut costing at most `max 0 (log ((B-M)/η)) + 1` in absorption charge, retains its literal suffix roots, clips its initial value, and recomputes exact values within `η` of every retained annotation. Support and floor errors increase by at most `η`. Neither producer is supplied for arbitrary games. |
| Unattained behavioral repair infimum | `UniformEquilibrium/Diagnostics/Quitting/PivotRepairNonattainedAllLaws.lean` | `behavioral_repair_infimum_zero_not_attained` gives a concrete four-player game and fixed opponent laws with behavioral repair infimum zero but strictly positive exploitability for every pivot behavioral strategy. The compact finite LP attains zero at an unrealizable boundary point. This is a fixed-opponent nonattainment example, not a counterexample to uniform-equilibrium existence. |
| Exact one-player behavioral repair value | `UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean` | `exists_objective_minimizer_eq_behavioral_infimum` identifies the attained finite-LP minimum with the infimum of full exploitability over all pivot behavioral strategies against fixed finite opponent laws. The approximation theorem in `UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralApproximation.lean` preserves the prescribed payoff vector, including when a positive late mass and zero first atom require approximants. Behavioral attainment and selection of opponent laws with small optimal value are not asserted. |
| Actual geometric repair objective | `UniformEquilibrium/Quitting/Terminal/PivotRepairExactObjective.lean` | `geometric_exploitability_eq_objective` identifies the finite objective with full behavioral exploitability when the geometric first atom matches the feasible mass coordinate. The zero-tail case is included. `geometric_cap_le_of_endpoints` bounds all responses using the head dates, Never, first late date, and limiting late endpoint. A positive late mass with zero first atom requires the separate behavioral-approximation theorem rather than exact realization. |
| Finite affine pivot-repair objective | `UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean` and `UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLPBoundary.lean` | `QuittingPivotRepairLPInput` fixes actual finite opponent laws and computes the response coefficients from the game. `exists_objective_minimizer` proves attainment on the compact feasible mass polytope; `constraintGain_affine` exposes the affine constraints. `prescribedPayoff_withFirstAtom` and `abs_objective_withFirstAtom_sub_le` preserve the prescribed payoff vector and bound the objective change when perturbing the first late atom. Equality with the infimum over actual pivot strategies is not supplied by these modules. |
| Rational coefficients from actual repair data | `UniformEquilibrium/Quitting/Terminal/PivotRepairRationalCoefficients.lean` | `exists_rationalAffineConstraintFunctional_of_actual_source` constructs an exact rational affine functional for every repair constraint from rational reward entries and rational probabilities in the actual finite nonpivot laws. It assumes neither a rational optimizer nor an opponent-law selection procedure. The game-independent affine basis reconstruction is in `MathUE/LinearAlgebra/RationalAffineCoefficients.lean`. |
| Geometric compression of an actual pivot law | `UniformEquilibrium/Quitting/Terminal/GeometricPivotCapDomination.lean` | `exists_geometric_pivot_payoff_eq_and_caps_le` selects a geometric finite-tail replacement of an arbitrary complete pivot law against fixed finite opponent laws. It preserves the payoff vector and lowers every unrestricted behavioral cap; `exists_geometric_pivot_payoff_eq_and_exploitability_le` also exposes full exploitability control. The Never atom is retained, rewards may have arbitrary signs, and the limiting late-response endpoint need not be attained. This is not an optimizing pivot-law existence theorem. |
| Signed late responses against finite opponents | `UniformEquilibrium/Quitting/Terminal/FiniteOpponentPivotResponseFormula.lean` | `quittingTerminalPayoff_pivot_late_response_eq` computes a late response against any actual pivot stopping law from its finite interval mass, tie atom, late-finite mass, and Never atom. `quittingPivotEarlyContribution` is the payoff of the actual censored pivot with the responder at Never. The identity holds for every payoff observer with arbitrary signed rewards. Geometric cap domination and an optimizing pivot law are not supplied by this identity. |
| Full-cap finite-menu early absorption | `UniformEquilibrium/Quitting/Terminal/TerminalProfileFiniteEarlyAbsorption.lean` | `finiteMenuFullEarlyAbsorption_of_terminalProfiles_liveMassZero` turns arbitrarily accurate actual profiles with zero limiting live mass into finite timing menus with unrestricted exploitability below the requested error and survival below the requested bound before the terminal window. `HasQuittingFiniteMenuFullEarlyAbsorption` retains both conclusions explicitly, at deadlines above any supplied lower bound. No singleton-sign assumption is used. |
| Signed singleton four-cycle producer | `UniformEquilibrium/Quitting/Cycles/SignedFourCycleCertificate.lean` and `UniformEquilibrium/Quitting/Cycles/SignedFourCycleFiniteEarlyAbsorption.lean` | `SignedFourCycleSingletonData.certificate` derives all Bellman equations, owner equalities, singleton lower bounds, and opponent divergence from the actual singleton comparison table and its explicit spectral tests. `targetValue_isUniformEquilibriumPayoff` produces the computed fixed target against unrestricted behavioral deviations. `hasFiniteMenuFullEarlyAbsorption` also produces actual finite timing menus retaining an unrestricted deviation bound and early absorption. Own singleton levels and nonsingleton rewards may be arbitrary signed reals. The coarse four-phase profile itself is not asserted to be Nash. |
| Pivot-law invariance against finite opponents | `UniformEquilibrium/Quitting/Paths/FiniteOpponentPivotLaw.lean` | `quittingIndependentTerminalOutcomeLaw_pivot_eq_of_head_and_never` preserves the full labelled terminal law when an arbitrary pivot law retains its atoms before the finite opponents' deadline and its Never atom. Payoff equality holds for signed rewards and after any nonpivot replacement supported before that deadline or at Never. The pivot's unrestricted response cap is unchanged. No equality of other players' unrestricted caps or geometric-tail domination is asserted here. |
| Positive-singleton early-absorption characterization | `UniformEquilibrium/Quitting/Terminal/FiniteMenuEarlyAbsorptionNecessity.lean` | `exists_uniformEquilibriumPayoff_iff_finiteMenuEarlyAbsorption_of_singleton_pos` identifies uniform-payoff existence with actual finite-menu early absorption when one own singleton is positive. Necessity uses fixed-family late-finite censoring and the actual joint-Never debt bound. The negative one-player regression shows the hypothesis cannot simply be removed. |
| Full-cap finite-menu approximation and fixed targets | `UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean` | `exists_finiteDeadlineTimingProfile_approximation` approximates one arbitrary actual profile by one finite product law with simultaneous payoff-norm and unrestricted-exploitability control, at a deadline above any supplied lower bound. `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation` keeps one specified target fixed before every accuracy. These statements allow arbitrary signed rewards and need neither normality nor a positive singleton; exact menu Nash and early absorption are not asserted. |
| Canonical single-pivot finite menus | `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean` and `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineNashExistence.lean` | `exists_exactFiniteDeadlineTimingNash` supplies a fresh exact menu Nash equilibrium at every deadline, including zero. `singlePivot_fullExploitability_eq_max_menuExploitability_scalar` reduces the full cap discrepancy to one explicit scalar when the own singleton vector is a unit vector. No selection making that scalar small is supplied; exact menu Nash and zero joint-Never mass can coexist with positive unrestricted debt. |
| Finite-date-only punishment and zero-Never normalization | `UniformEquilibrium/Quitting/Punishment/FinitePureReplyPunishment.lean` and `UniformEquilibrium/Quitting/Punishment/SinglePivotPunishment.lean` | `quittingFinitePureReplyPunishmentValue_eq_min` proves that the infimum of the all-finite-date response supremum over complete opponent plans is the minimum of full punishment and the own singleton. `quittingPunishmentValue_singlePivotNormalized` gives exact punishment transport under original coordinate normality and a positive pivot singleton. `quittingTerminalPayoff_singlePivotNormalized` retains the joint-Never correction for an unchanged actual profile. |
| Single-pivot strategy lift and fixed-target payoff sets | `UniformEquilibrium/Quitting/Punishment/SinglePivotTailLift.lean` and `UniformEquilibrium/Quitting/Punishment/SinglePivotUniformPayoff.lean` | `exists_singlePivot_samePrefix_terminal_lift` preserves every history before one cutoff and installs one fixed stationary punishment target, with quantitative payoff and unrestricted-debt bounds. `uniformEquilibriumPayoffSet_singlePivotNormalized` proves affine equality of fixed-target uniform payoff sets under original all-player punishment normality and a positive pivot singleton. Forward target transport needs only the positive pivot; reverse transport uses the actual lifts. Never remains zero. |
| Single-pivot quantitative gap and finite packet transport | `UniformEquilibrium/Quitting/Punishment/SinglePivotTerminalGap.lean` and `UniformEquilibrium/Quitting/Projective/SinglePivotFiniteForwardPacketTransport.lean` | `singlePivot_terminalExploitability_ge_gap_sq_div` gives the normalized global lower bound `γ²/(16M²)`; `hasTerminalExploitabilityGap_singlePivotNormalized` supplies actual deviations with margin `γ²/(32M²)`. `QuittingFiniteForwardPacket.singlePivotNormalized` transports supplied Bellman data, compact carrier, support tolerance, and punishment floors while retaining roots, horizon, and charge. Neither theorem transports a chosen minimizing profile or its provenance. |
| Actual finite timing menus and displayed reply caps | `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean`, `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineReplyCap.lean`, `UniformEquilibrium/Quitting/Root/FiniteDeadlineCapRecursion.lean`, and `UniformEquilibrium/Quitting/Root/FiniteDeadlineWordRealization.lean` | The menu `QuittingFiniteDeadlineTimingAction H` consists of dates strictly below `H` and Never. `quittingFiniteDeadlineReplyCap_eq_finiteRootWordCap` identifies its actual reply cap with the finite root-word fold ending at zero. `exists_finiteDeadlineTimingProfile_menu_payoff_realization` realizes arbitrary finite root sequences as independent menu laws preserving prescribed and every displayed pure-reply payoff; the resulting cap realization holds simultaneously for every player. Original Never mass is preserved. `IsQuittingFiniteDeadlineNash` asks only for menu comparisons, not unrestricted behavioral regret. |
| Finite-menu punishment converges to unrestricted punishment | `UniformEquilibrium/Quitting/Punishment/FiniteMenuPunishmentValue.lean`, `UniformEquilibrium/Quitting/Punishment/FiniteMenuPunishmentConvergence.lean`, and `UniformEquilibrium/Quitting/Punishment/FiniteMenuPunishmentRecursion.lean` | `quittingFiniteMenuPunishmentValue` is the minimum over actual independent finite-menu laws, not a recursively stipulated value. `quittingFiniteMenuPunishmentValue_eq_operator_iterate` proves its Bellman representation using actual root-word minimizers and menu realizations. `tendsto_quittingFiniteMenuPunishmentValue` proves convergence to full behavioral punishment for arbitrary signed rewards. `tendsto_quittingFiniteMenuPunishmentDeficit` gives a nonnegative, uniformly vanishing finite-player deficit. No effective rate or monotone increase from zero is asserted. `HasQuittingFiniteMenuEarlyAbsorption` in `UniformEquilibrium/Quitting/Terminal/FiniteMenuEarlyAbsorption.lean` states the separate actual-menu early-absorption condition; the punishment results do not produce that condition. |
| Early finite-menu absorption and unrestricted completion | `UniformEquilibrium/Quitting/Punishment/FiniteMenuCompletion.lean` and `UniformEquilibrium/Quitting/Terminal/FiniteMenuEarlyAbsorptionCompletion.lean` | `exists_finiteMenu_samePrefix_completion` retains the actual menu profile at every history before the cutoff and installs one preselected stationary punishment target. Its unrestricted exploitability is at most the menu error plus `2Mρ + max(2M√ρ, ω(H) + η)`. The source requires only displayed-menu Nash comparisons and small joint reach; opponent-deleted reach is handled separately in the proof. `exists_uniformEquilibriumPayoff_of_finiteMenuEarlyAbsorption` consumes arbitrarily accurate early-absorption sources to produce one fixed uniform payoff for any finite nonempty quitting game, including signed and zero rewards. These are checked source-to-equilibrium consumers; no general early-absorption producer is supplied. |
| Universal-prefix hull floors and renewable response ledgers | `UniformEquilibrium/Quitting/ControllerTester/RenewableBarrierSaturation.lean` and `UniformEquilibrium/Diagnostics/Quitting/RenewableTwoClockRegression.lean` | `exists_minimizer_rawMaximumDebt_universalPrefixHull_eq_sInf_wordInf_of_box` gives the attained hull minimum as the seedwise infimum of the literal raw-debt word envelope in any invariant reward box, without requiring carrier seeds or nonnegative raw debt. `quittingUniversalPrefixHull_union_never_eq_carrier` identifies the hull after adding Never to carrier seeds. `canonicalRawBarrier_renewableLedger_and_limsup` gives the exact finite ledger and a nonpositive average response-lift limsup from literal finite-prefix ancestry; no cap-seam monotonicity is assumed. The four-player regression proves four exact complete-cap gains and raw debts equal to one, yet raw envelope and hull floor zero. Its actual sentinel profile is terminal Nash and attains global raw-debt minimum zero. These are checked hull computations and a route exclusion, not a positive global barrier producer. |
| Nonnegative-weight minimum chamber and sparse terminal-law boundary | `MathUE/LinearAlgebra/FiniteConicSparseCombination.lean`, `MathUE/LinearAlgebra/FiniteConePositiveAlternative.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightLawCertificate.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalRewardSparseAlternative.lean`, and `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawSparseSourceImprovement.lean` | `minimumTerminalSemantic_nonnegativeWeight_chamber` gives the sharp weighted lower chamber at an ordinary positive global debt minimum; two positive weight coordinates make its debt coefficient positive. If the corresponding weighted outcome upper bound lies below the weighted singleton value, `exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber` forces zero minimum debt and invokes the unrestricted-behavior consumer. A positive-minimum joint law instead yields a finite atom with weighted surplus and the general mass floor `c D / (R T K)`; the Fin4 symmetric-bound corollaries give `D / (16R)` and the weaker packet scale `D / (32R)`. The finite-cone alternative returns either a supported positive costate or a sparse nonnegative terminal law, and the actual joint-law adapter retains the original atom identities while reweighting their masses. These results have `M` and `L`; compact minimum and joint-law selection provide `A`, while `C` is available only in the zero-minimum chamber. The sparse reweighted law is not asserted to be behaviorally realizable. The sharp Fin4 regression has exactly four supported pair atoms and is not realizable by any behavioral profile or one-date product root; the two-player regression shows that sparse positive social reward does not imply Nash play. |
| Common-prefix unrestricted-cap stability | `UniformEquilibrium/Quitting/Root/BoundedEndpoint.lean` and `UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean` | `abs_quittingContinuationBestResponseValue_literalRootStack_sub_max_le` bounds the complete behavioral cap behind any nonempty finite root word by the larger of singleton cash-out and the suffix cap, with error `2 * M` times lost opponent-deleted survival. `abs_quittingContinuationBestResponseValue_literalRootStack_sub_le` gives the corresponding contraction between two arbitrary suffix caps. The two `tendsto_quittingContinuationBestResponseValue_literalRootStack` theorems transport a convergent suffix cap when opponent or joint prefix survival tends to one and the limit strictly dominates singleton cash-out. These source-independent declarations have `M` and `L`; they supply no prefix source `A`, Nash property, minimum, chronology, renewal, downstream `C`, or uniform-equilibrium conclusion. |
| Arbitrary finite-word live tails and semantic splicing | `UniformEquilibrium/Quitting/Root/FiniteWordSemanticSplice.lean`, `UniformEquilibrium/Quitting/Root/FiniteWordSurvivalSeams.lean`, and `UniformEquilibrium/Quitting/Examples/HostClearingBoundary.lean` | `isAsymptoticNash_tail_of_literalRootStack_joint_pos` divides the actual source Nash error by joint survival. `exists_diagonal_tail_limit_of_literalRootStack_nash_ratio` turns vanishing divided error into a fixed uniform payoff from a subsequence of those actual tails. Conversely, `growingWord_referenceSeams_completion` proves actual splice payoff convergence, unrestricted exploitability tending to zero, and a uniform target when the algebraic reference debt and the two transmitted discrepancies vanish. Joint survival multiplies payoff error; opponent-deleted survival multiplies only the positive cap error. Exact reference chains and positive joint floors have separate specializations. The literal two-profile host-clearing regression retains zero host debt and a unit outsider gain, so clearing one host does not control the marked profile's other caps. These are checked conditional consumers with actual-profile adapters, not a producer of the required vanishing discrepancies. |
| Period-one Fin4 vanishing-hazard source and endpoint limits | `UniformEquilibrium/Quitting/Cycles/FourPlayerPeriodOneVanishingHazardSource.lean`, `UniformEquilibrium/Quitting/Cycles/PeriodOneVanishingHazardLimitLaw.lean`, `UniformEquilibrium/Quitting/Cycles/PeriodOneVanishingHazardTerminalCap.lean`, and `UniformEquilibrium/Quitting/Cycles/PeriodOneVanishingHazardEndpointLimits.lean` | `exists_periodOne_tropical_twoNever_escape_of_fourPlayer_noUniformPayoff` constructs one actual stationary source chronology with vanishing total hazard, convergent normalized hazard direction and payoff, a common positive minimum singleton margin, and the corresponding endpoint-regret-density limit. On the same strict subsequence, literal Quit converges to the singleton payoff, literal Never converges to the normalized opponent singleton lottery, and Never eventually attains the complete unrestricted behavioral cap. Complete debt converges to the player's direction share times the minimum margin divided by the complementary share; zero-share outsiders consequently have vanishing debt. Two fixed distinct support players have one positive Never-gain floor on those same actual profiles. The declarations have `M` and `L`, and the no-uniform-payoff constructor supplies source-family `A`. Chronological descendants are handled by the subset interface below; this source theorem alone does not produce the final paid port or a uniform-equilibrium payoff. |
| Literal stationary subsets and sequential Never caps | `UniformEquilibrium/Quitting/Cycles/PeriodOneStationarySubsetLimits.lean`, `UniformEquilibrium/Quitting/Stationary/TerminalCoalitionLaw.lean`, and `UniformEquilibrium/Quitting/Stationary/StrictEndpointSelection.lean` | `subsetProfile_actualTerminalLaw_tendsto` and the subset endpoint limits preserve the original finite hazards of zero-share outsiders. `exists_chronological_twoNever_supportDescent` gives two sequential attained unrestricted Never caps at common-minimum source limits with at least three positive shares; `exists_chronological_Never_singletonDescent` handles support two. The updated player changes on the actual preceding child, not on a sibling. Explicit gain formulas and eventual live-probability half floors are retained. The two-owner matrix sign alternative is checked in `MathUE/LinearProgramming/TwoPointHomogeneousObstruction.lean`, including a derived negative outsider when both cross entries vanish. |
| Tropical source descent to an off-minimum paid row | `UniformEquilibrium/Diagnostics/Quitting/PeriodOneOffMinimumPaidPort.lean` | `exists_periodOne_literalPaidCapChain_of_fourPlayer_noUniformPayoff` constructs the actual vanishing-hazard source and a same-subsequence chain of two to four literal unilateral updates. Every edge attains the mover's unrestricted behavioral cap with one common positive gain floor. The final edge is Quit0; its stationary source has total debt uniformly above the global minimum. `StationaryOffMinimumQuitNowPort.eventually_paid_initialRow` exposes date-zero reach one, positive Continue support, stationary self-continuation, and a positive local endpoint gap; the port retains own, opponent, and joint Continue half floors. This supplies `M/L/A` and the finite-descent consumer, but not minimum-source ancestry, renewal, or a terminal approximate equilibrium. |
| Singleton blockers and separation from minimum debt | `UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean` and `UniformEquilibrium/Diagnostics/Quitting/CompleteCapSingletonLimitCollar.lean` | `exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform` derives full normalized-matrix homogeneous infeasibility, a distinct blocker for every owner, and one uniform positive singleton gap. `exists_eventual_offMinimum_collar_of_completeCap_tendsto_singleton` derives eventual strict separation from minimum total debt for any actual behavioral family with a named complete cap converging to its singleton payoff. It assumes neither stationarity nor minimum ancestry. This separation does not supply an additive charge budget or return. |
| Literal-prefix cap selection and debt transport | `UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean`, `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineCapSelection.lean`, `UniformEquilibrium/Quitting/Root/PureTimeCapPrefixSelection.lean`, and `UniformEquilibrium/Quitting/Root/TerminalGapPrefixDebtorTransport.lean` | `quittingTerminalPayoff_literalRootStackProfile_sub_eq_jointSurvival_mul` transports every supplied suffix payoff difference through a literal finite root word with the exact joint-survival multiplier, and `quittingTerminalPayoff_copyLiteralRootStackThenDeviation_sub_eq` realizes the transported difference by one actual behavioral deviation that copies the displayed prefix. If one named opponent quits surely at a finite deadline, `exists_pureTime_le_deadline_or_never_terminalPayoff_eq_cap` attains another player's complete behavioral cap at `Never` or a pure quit time no later than that deadline. `exists_pureTimeCap_zero_or_map_succ_of_suffixAttainer` installs a supplied pure-time suffix cap behind one product root. Finally, `HasTerminalExploitabilityGap.exists_outsider_pureTimeCap_with_prefix_debt` combines these statements: a sufficiently low-debt sure-exiting owner yields a fixed outsider, an exact pure-time cap attainer, the full terminal-gap debt at the suffix, the exact prefix gain, and the joint-survival-scaled prefix debt floor. These source-independent and supplied-data declarations have `M` and `L`. They do not produce a Fin4 source sequence, preserve one debtor across a sequence, prove summable hazards, supply an outsider root-gap seam, consume the transported debt, or establish Nash play or a uniform-equilibrium payoff; source `A` and downstream `C` are absent. |
| Forced-Continue terminal-child payoff displacement | `UniformEquilibrium/Quitting/Root/CoordinateMarginalMixture.lean`, `UniformEquilibrium/Quitting/Root/ForcedContinuePayoffDisplacement.lean`, `UniformEquilibrium/Quitting/Root/TerminalChildPayoffDisplacementSequence.lean`, `UniformEquilibrium/Quitting/Root/ImmediateQuitCapDisplacement.lean`, and `UniformEquilibrium/Quitting/Root/CofinalImmediateQuitCapDisplacementLimit.lean` | `terminalChildPayoffDisplacement_next_eq` gives the exact affine recurrence between a supplied Bellman source and the child obtained by forcing one fixed owner to Continue. Summable forced-root absorption and owner hazard make the displacement increments absolutely summable and the full displacement sequence converge. At a supplied immediate-Quit complete-cap reset, `debtFloor_sub_ownerHazardError_le_neg_payoffDisplacement_of_quitZeroCap` gives the signed outsider bound with error `4 * M` times the removed owner hazard. Cofinal resets, an eventual positive outsider debt floor, and eventual source-root exactness force one finite displacement limit at most `-debtFloor`. Positive outsider Continue follows from the positive debt floor; it is not an extra premise. These generic finite-player declarations have `M`, `L`, and a conditional limit `C` for a supplied literal source/child genealogy. They do not construct that genealogy or its cap selections, make the forced child roots Nash, prove summability of displacement values, supply the separate weighted-series representation, return to the source, regenerate a source, or establish a uniform-equilibrium payoff; source `A` is absent. |
| Minimum-fibre response chords and Fin4 tangent paid rows | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveDebtSupport.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticMinimumResponseChord.lean`, and `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FullReplacementQuantitativePaidPort.lean` | `QuittingMinimumResponseChordLaw.ofProfiles` constructs the literal one-player stopping-law chord and records its affine complete terminal law and debt upper bounds. When both endpoints have the same globally minimal total debt, `chord_debt_eq_affine`, `chord_debtSum_eq_endpoint`, and `chord_support_eq_union` make coordinate debt, total debt, and positive-debt support exact; the response support is nonempty and has cardinality at most three in Fin4 when a positive endpoint coordinate is killed. For every supplied Fin4 tangent full-replacement cluster, `nonempty_finFourFullReplacementQuantitativePaidPort` selects one fixed nonmover with limiting debt at least `D_*/3`, eventual debt at least `D_*/4`, paid gain `D_*/16`, and literal `4M`, `8M`, and `32M²` reach bounds. `nonempty_finFourFullReplacementQuantitativePaidPort_of_positiveMinimum` supplies the tangent family and cluster from a positive compact-carrier minimum. These declarations have `M` and `L`, and the final wrapper gives branch-local source `A`; they do not make the horizontal replacement chronological, identify it with a full-debt residual branch, consume the paid rows, regenerate a source, provide renewal, or yield downstream `C` or a uniform-equilibrium payoff. |
| Complete stopping-law cap-band redistribution | `MathUE/Probability/StoppingLawCapBandRedistribution.lean` and `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/CapBandRedistribution.lean` | `stoppingLawSourceCapDebt_le_epsilon_add_two_mul_badMass` bounds source cap debt by the band width plus `2 * M` times the complete stopping-law mass outside the band, including Never and infinitely many finite clocks. The pushforward preserves every survival prefix through a supplied cut. For a supplied actual behavioral profile whose mover debt exceeds the positive band width, `exists_quittingCapBandFiniteCut` selects a source-supported finite cut and near-cap receiver. Its target is a literal unilateral behavioral update with unchanged own unrestricted cap, target debt at most the band width, payoff gain at least source debt minus that width, exact debt subtraction, and a `2 * M` joint-reach bound. The generic compiler and quitting adapter have `M` and `L`; the quitting theorem gives local actual-profile `A` only after the profile and positive-debt inequality are supplied. There is no source producer or downstream `C`, compactness, renewal, Nash, or uniform-equilibrium conclusion. |
| Full-debt cap-band target split and support-contracted renewal (Research-only) | `Research/Quitting/FinFourProducerAtlas/FinFourFullDebtCapBandTargetDispatch.lean`, `Research/Quitting/FinFourProducerAtlas/FinFourFullDebtCommonPrefixResponse.lean`, `Research/Quitting/FinFourProducerAtlas/FinFourFullDebtPairedSourceRegeneration.lean`, and `Research/Quitting/FinFourProducerAtlas/FinFourFullDebtSupportContractedRenewal.lean` | From a supplied positive global-minimum `FinFourMinimumAtomProducer` with positive debt in every coordinate, `nonempty_finFourFullDebtCapBandTargetDispatch` returns either a literal strict-target actual-reach paid port or a fixed-weight minimum-response chord whose target support is nonempty of cardinality at most three. `nonempty_finFourFullDebtCommonPrefixResponse` selects common exact cap--Nash root words, and `nonempty_finFourFullDebtPairedSourceChronologyRegeneration` retains the chord-to-target update edge while regenerating a same-residual source at the target law point. `nonempty_finFourFullDebtSupportContractedRenewal` keeps that one-use origin edge separate and starts the neutral renewable trace at the regenerated target, with at most two further strict-support descents. `finFour_noUniformPayoff_exists_fullDebtTargetDispatch_or_resetRigid` supplies a same-point producer only in the full-debt arm of the existing conditional no-uniform-payoff classifier; the reset-rigid arm is unchanged. The chain has `M` and `L`, conditional source `A` at that classifier entrance, and branch-local `C` through the strict paid-cap attachment or support-contracted renewal. It does not identify independently selected residuals, identify the public paired chronology with the regenerated producer's internal chronology, consume the resulting structural terminal exit, or prove Nash play, terminal approximation, or a uniform-equilibrium payoff. |
| Actual reached-pair premark residual | `UniformEquilibrium/Diagnostics/Quitting/LiteralOneDateProfile.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachedPairPremarkResidual.lean`, and `UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourPremarkDeletedReach.lean` | A supplied screened actual mark gives a literal one-date behavioral update. Its complete mover debt splits into the reached endpoint gain and `premarkResidual`; positive residual selects a source-supported paid first-disagreement row strictly before the mark, with the exact own-survival, opponent-reach, and joint-reach floors. A separately supplied attained positive minimum attaches that row to the paid-cap trichotomy. The pure nonempty-host specialization gives the exact signed complete terminal law, including `Never`, and the restricted premark response envelope. The Fin4 regression proves that arbitrarily small marked joint reach can coexist with unit nonmover cap change through deleted reach. These declarations have `M` and `L`, but no source `A`; only the separately supplied positive-minimum attachment has branch-local `C`. They do not produce the marked profile or minimum, identify a chronology, regenerate a source, prove Nash play, or yield a uniform-equilibrium payoff. |
| Moving marked-pair minimum chord and support descent (Research-only) | `Research/Quitting/FinFourProducerAtlas/MovingMarkedPairSource.lean`, `Research/Quitting/FinFourProducerAtlas/MovingMarkedPairResidualAlternative.lean`, `Research/Quitting/FinFourProducerAtlas/MovingMarkedPairMinimumChordCompactification.lean`, `Research/Quitting/FinFourProducerAtlas/MovingMarkedPairCommonPrefixResponse.lean`, and `Research/Quitting/FinFourProducerAtlas/MovingMarkedPairSupportDescentAlternative.lean` | From a supplied moving family with a nonempty pure host, fixed mover, fixed distinct source and target terminal outcomes, positive marked-reach and reward-gap floors, source profiles approaching a positive global minimum, and exact marked-toggle identities, `nonempty_finFourMovingMarkedPairPrecompactAlternative` returns either an off-minimum actual-reach paid port or a minimum-fibre fixed-weight response chord. The minimum branch has a nonempty target support of cardinality at most three; common exact cap--Nash prefixes preserve the literal response edge and complete semantic convergence, after which the same-residual consumer returns support-contracted renewal. The host need not have cardinality two: its nonemptiness follows from the distinct sure-quitting screening player. This supplied-data compiler has `M` and `L`, no source `A`, and branch-local `C` through the paid port or renewable support descent. It does not construct the moving family, turn the public paired chronology into the regenerated producer's internal chronology, consume the terminal exit, or prove Nash play, terminal approximation, or a uniform-equilibrium payoff. |
| Reset-rigid positive-Never restart and support contraction (Research-only) | `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveNeverTwoRelease.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockFreshRelease.lean`, `Research/Quitting/FinFourProducerAtlas/EscapeProductRestart.lean`, `Research/Quitting/FinFourProducerAtlas/ResetRigidEscapeSupportContraction.lean`, and `Research/Quitting/FinFourProducerAtlas/ResetRigidProducerRank.lean` | For a supplied positive-Never product descendant of a positive Fin4 minimum source, `FinFourEscapeProductRestart.offMinimumPaidPort_or_minimumRestart` returns an actual-reach off-minimum paid port or accepts the exact product point. In the equality arm, `FinFourEscapeProductRestart.MinimumRestart.sourceAtProduct` uses the literal constant product suffix behind words of `n + 1` all-Continue exact cap--Nash roots, with unchanged semantic pair and complete law and a shifted positive atom. The two fresh releases retain quarter-Never reach and gain floors. `finFourResetRigidEscape_productExit_or_singletonExit_or_supportContraction` then returns a product paid exit, singleton paid exit, or the existing moving support-contraction result, while `FinFourResetRigidProducerTransition.rank_lt` proves the displayed one-way phase/support rank. This chain has `M` and `L`, no reset-rigid escape-origin source `A`, and branch-local `C` only through the attached paid and moving consumers. It does not construct the supplied product or ancestry, consume a terminal atlas exit, rank arbitrary atlas edges, or prove Nash play, terminal approximation, or a uniform-equilibrium payoff. |
| Signed source retraction and selected near-minimum cycle contraction (Research-only) | `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FinFourSignedRetraction.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticNearMinimumExactResponseChordCompactification.lean`, and `Research/Quitting/FinFourProducerAtlas/FinFourSignedCycleContraction.lean` | `nonempty_quittingFinFourSignedRetraction` gives the exact signed debt ledger for one supplied Fin4 replacement chain. From explicitly supplied cofinal response cycles and a selected asymptotic arm, `nonempty_finFourSelectedCycleContractionResult` returns either a fixed paid arm on one strict cofinal subsequence or a near-minimum fixed-weight chord with same-residual strict-support regeneration. `FinFourUniformCycleFixedPaidRetraction.moverPaidRow_of_fixedLabel_eq` exposes the fixed mover with `epsilon / 16` gain and `epsilon / 64` paid-row thresholds; `nonmoverPaidRow_of_fixedLabel_eq` exposes the fixed observer with `epsilon / 48` debt and `epsilon / 192` paid-row thresholds, together with the literal reach bounds. The source-independent layers and supplied-data compiler have `M` and `L`; the Research capstone has conditional `A` only from the supplied producer, chronology, cofinal cycles, and selected branch. There is no terminal or renewal `C`, no construction of the cofinal-cycle input, and no Nash-play, terminal-approximation, or uniform-equilibrium conclusion. |
| Exact Fin4 scale resolution and counterexample semidecision (Research-only) | `MathUE/Interval/RationalLowerBoxSearch.lean`, `Research/Quitting/FinFourRationalSingleShellLower.lean`, `Research/Quitting/FinFourExactScaleResolution.lean`, `Research/Quitting/FinFourCounterexampleSemidecision.lean`, `Research/Quitting/FinFourIndependentCertificateSoundness.lean`, and `Research/Quitting/FinFourFixedTableCounterexampleSearch.lean` | `finFourExactScaleStep` is a total proof-free upper-first stage function. `exists_finFourExactScaleStep` proves finite termination for every normalized rational Fin4 table and positive rational scale. Upper output decodes to an actual finite-clock product profile with unrestricted exploitability below `3 * epsilon / 4`; lower output proves `epsilon / 4` below the global infimum and supplies a literal `epsilon / 8` terminal gap and no-uniform-payoff consumer. `FinFourExactScaleCertificate.lower_verifies_infimum_sound` proves that an independently accepted lower tree has this global unrestricted-behavior meaning without replaying its generator. For any supplied normalized rational Fin4 table with positive unrestricted terminal-exploitability infimum, `exists_finFourFixedTableCounterexampleStep_of_infimum_pos` proves that the fixed-table dovetail emits a checked lower certificate at some finite stage. `exists_finFourCounterexampleStep_iff_exists_real_infimum_pos` remains the global existential r.e. equivalence, using reward robustness, positive scaling, normalized rational approximation, and fair enumeration. This Research route has `M/L/A/C` at its stated inputs. It produces no positive-gap table, does not decide a supplied real table, and nontermination has no conclusion. |
| Constrained-root normal-work ledger and zero-minimum boundary (Research-only) | `MathUE/ConstrainedAffineNormalWork.lean`, `Research/Quitting/ConstrainedRootNormalWork.lean`, `Research/Quitting/ConstrainedRootExistence.lean`, and `Research/Quitting/FinFourConstrainedRootNormalWorkRegression.lean` | `constrainedRoot_terminalDebt_eq_normalWork_add_inherited_sub_shield` and `constrainedRoot_totalNormalWork_eq_excessChange_add_killed_add_shield` give the exact coordinate and total semantic-debt ledgers. `nearMinimum_totalNormalWork_ge_kappa_mul_minimum_sub_excess` gives the finite min--max floor bound, while `lowerFaceRemoval_otherDebtChange_sum_eq` and `lowerFaceRemoval_exists_supportEntry_of_uniqueDebtor` give exact signed repayment and the correctly hypothesized unique-debtor support-entry conclusion. `constrainedRoot_finiteBackwardBlock_telescope` and `actualOwnStrategyRemoval_finiteDebtCutBalance` are the finite row and label-cut telescopes. `exists_quittingLowerBoundConstrainedRoot` constructs a constrained root against any prescribed payoff, and `exists_actual_quittingLowerBoundConstrainedPrefix` prefixes one to a supplied actual behavioral tail. `FinFourConstrainedRootNormalWorkRegression.finite_boundaryRegression` is an actual full-behavior zero-minimum table whose unit debt circulates around four unilateral updates. The ledger has `M` and `L`, and the prefix theorem has `A` relative to its supplied actual tail; there is no positive-minimum atlas source `A` or downstream `C`. In particular, the results provide no sign orientation or cancellation for cross-coordinate repayment, renewable source rank, terminal approximation, or uniform-equilibrium conclusion. |
| Finite-product total variation, censoring, and projective timing-Nash compatibility | `MathUE/PMFProduct/TotalVariation.lean`, `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineAdjacentTotalVariation.lean`, `UniformEquilibrium/Diagnostics/Quitting/CensoredFiniteClockOperationalEffect.lean`, `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineProjectiveCompatibility.lean`, `UniformEquilibrium/Diagnostics/Quitting/ProjectiveTimingInverseLimit.lean`, `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineVanishingAdjacentDistance.lean`, `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingRealization.lean`, and `Research/Quitting/FiniteDeadlineCompatibleNashChains.lean` | `Math.PMFProduct.pmfTV_pmfPi_le_sum` and `abs_expect_pmfPi_sub_le_two_mul_sum_pmfTV` give finite-product TV and bounded-observable estimates. For consecutive exact timing Nash laws, `quittingFiniteDeadlineTimingProfile_semanticDebt_le_adjacentTV` gives `d_i <= 4 R * sum_j TV`, with the supplied-coordinate converse `quittingFiniteDeadlineAdjacentTV_ge_div_of_semanticDebt_ge`. Censoring is a literal nonexpansive retraction; `pmfTV_quittingFiniteDeadline_include_censor_eq_boundary` identifies exactly the erased boundary atom, and `quittingFiniteDeadlineAdjacentTV_le_censorBudget` splits boundary participation from old-clock reshuffling. `quittingFiniteRootWordOperationalObservables_mixedTiming_eq` and `quittingFiniteRootWordOperationalEffectDistance_mixedTiming_eq` identify the mixed-law gauge with its literal reconstructed root word; `quittingFiniteDeadlineOperationalEffectDistance_zero_retainedTailSemantic_eq` then preserves the complete terminal semantic pair behind every common behavioral tail at zero distance. A `QuittingFiniteDeadlineCompatibleNashFamily` has an exact Never-mass telescope and vanishing adjacent TV. `exists_uniformEquilibriumPayoff_of_arbitrarilySmallAdjacentNashTV` and the family method `exists_uniformEquilibriumPayoff` compile arbitrarily close consecutive Nash pairs, hence any supplied compatible family, to a uniform-equilibrium payoff. `QuittingFiniteDeadlineCompatibleNashFamily.isZeroAsymptoticNash_limitProfile` strengthens that from existence of some payoff to an identified profile: the family determines one stopping law on the compactified times per player whose deadline truncations are exactly the supplied marginals, and their independent product is an exact terminal Nash profile against every unilateral behavioral deviation at error `0`, with `isUniformEquilibriumPayoff_limitProfile` reading off its prescribed payoff. `quittingGame_isUniformEquilibriumPayoff_of_adjacentTV_tendsto` is the matching consumer over an arbitrary index filter, identifying the target as the limit of the realized prescribed payoffs; the selected deadlines need not be cofinal, since the estimate consumes vanishing terminal debt and not deadline growth. `QuittingFiniteDeadlineCompatibleNashChain` records finite compatible chains and implies deadlinewise timing-Nash existence, but `FiniteCompatibleChainsProduceProjectiveNashFamily` is only the explicit remaining Research proposition; no theorem inhabits it. This compatible-family route has `M/L/C` but no `A`: no compatible-family or semialgebraic-minimizer producer is checked. The independent adjacent-gap dispatch and concrete null-direction regression below do not supply such a family or a source-level uniform-equilibrium conclusion. |
| Adjacent finite-deadline gap dispatch and censored null direction | `UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineGapSource.lean`, `UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineOperationalEffectPaidPort.lean`, `UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineRetainedTailReprojection.lean`, `UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineSelectedBoundaryEffectDispatch.lean`, `UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineSingletonSeparatedTailDispatch.lean`, `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingStageCoalitionMass.lean`, `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineBoundaryResponseCollision.lean`, `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingHybridDispatch.lean`, `UniformEquilibrium/Diagnostics/Quitting/FinFourCensoredClockNullDirection.lean`, and `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticActualNearCarrierTail.lean` | `QuittingAdjacentDeadlineGapSource.of_terminalExploitabilityGap` attaches the terminal gap to any supplied pair of consecutive exact timing Nash laws, and `censoredError_or_boundaryParticipation` gives the literal `gamma / (8 * R)` old-clock-error or new-boundary-participation split. For a supplied actual tail uniformly separated from every own singleton reward, `quittingAdjacentDeadline_singletonSeparatedTail_dispatch` returns a lossless zero-`Never` boundary response, a paid pass response, a paid reverse-participant update, or the raw censor-error arm. The first three arms expose literal behavioral updates; the reverse arm preserves the mover's unrestricted cap and subtracts its payoff gain exactly from its debt. `quittingAdjacentDeadline_singletonSeparatedTail_dispatch_finFour` displays the reverse payment as `147 * delta * (gamma / R)^2 / 16384`. The separate selected-effect gauge records all `Never` discrepancies and one normalized observer boundary-gain discrepancy; it is bounded by, but is not the full operational-effect distance. `quittingAdjacentDeadline_operationalEffectDistance_ge_or_paidReverseParticipant_finFour` gives either full operational effect at least `gamma / (8 * R)` or a paid reverse participant with floor `27 * delta * (gamma / R)^4 / 4096`. Exact equality of the selected coordinates strengthens the payment to `7 * delta * (gamma / R)^3 / 256`. `finFourAdjacentSpectator_exists_sameTailPaidUpdate` now consumes both selected-effect branches at the common positive floor `min (27 * delta * (gamma / R)^4 / 4096) (min (delta * gamma / (32 * R)) (gamma / 8))`, preserving the mover's unrestricted cap and subtracting the exact payoff gain from its debt. Its actual-support passport supplies explicit self/opponent/joint reach floors, and `finFourAdjacentSpectatorTailMinimum_nonempty_capLiftedSummablePort` adds finite all-Continue-prefix ancestry plus the cap-lifted summable port with `D_* / (8 * R)` suffix reach and `D_* * W / (32 * R)` shifted paid gain. Independently, `quittingAdjacentDeadline_paidOwnEdge_or_paidResponseSquare` gives a hard own-edge/response-square split, and `QuittingFiniteDeadlineBoundaryResponseCollision.of_boundaryParticipation` supplies a counterfactual collision cylinder. `FinFourCensoredClockNullDirection.regressionCertificate` proves that raw censored TV can be arbitrarily large while the censored endpoints have equal terminal law and equal retained-tail semantics behind every common tail. Finally, `exists_actualNearCarrierTail_of_uniformSingletonGap` selects an actual profile near any supplied carrier point with a uniform singleton gap. These adjacent dispatches have `M/L/C` only conditionally on their supplied adjacent source and tail; no theorem jointly selects those inputs, so `A` remains incomplete. The raw censor-error arm still has no downstream `C`. No result here puts the tail on a minimum fibre, makes it Nash, or supplies chronology, return, renewal, rank, terminal approximation, or uniform equilibrium. |
| Minimum response-chord law, regeneration, and actual normalized-return decoder (Research-only) | `Research/Quitting/MinimumResponseChordLaw.lean`, `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean`, and `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordActualDecoder.lean` | `responseAtom_pos_imp_pureTime_ge_mark` turns a supplied positive complete-law rectangle atom into the exact late-or-Never response order. `quittingStageCoalitionMass_le_update_pureTime_routed` proves no-loss routing at the marked row. From a supplied `FinFourMinimumResponseRectanglePacket`, `FinFourMinimumResponseRectanglePacket.nonempty_minimumResponseRectangle` freezes the Boolean response mode on a strict refinement, while `FinFourMinimumResponseRectangle.routedStageMass_floor` derives the routed mass floor rather than accepting it. `FinFourMinimumResponseRectangle.nonempty_minimumResponseChord` constructs every proper joint chord; `debt_eq_affine`, `terminalLaw_eq_affine`, `theta_mul_lambda_le_terminalMass`, and `regeneratedSources_same_source` retain exact debts, law, atom floor, and same-law response/chord sources. The supplied-packet compiler has `M` and `L`. Separately, `FinFourNormalizedReturnSourceCapstone.nonempty_minimumResponseActualSourceOutcome` gives an actual exhaustive decoder from the normalized-return source capstone: strict inert, endpoint ascent, routed singleton, prescribed atom, response ascent, or compiled rectangle. `ConcentratedCollisionThreeRoleEndpointLaw.nonempty_canonicalMinimumResponseEndpointRiseOrigin` retains the actual profiles and endpoint law with mover gain `rho^2 * D_* / 8`, endpoint observer debt at least `rho^2 * D_* / 64`, and decoder charge `rho^2 * D_* / 128`; `FinFourMinimumResponseCanonicalEndpointRiseOrigin.compiled_crossFloor_eq` gives `7 * rho^2 * D_* / 1024`. In the compiled arm, `FinFourMinimumResponseCompiledRectangle.nonempty_chord_with_responseSupportDrop` constructs each proper chord and proves a strict response-to-chord positive-debt-support inclusion. This actual route has `M`, `L`, and `A`, but no `C`. It begins at the normalized-return equality endpoint, not a paid spectator cycle; it does not retain the old edge in a regenerated chronology, make support drop renewable, orient a return, consume ascent or the compiled chord, or imply terminal approximation or uniform equilibrium. |
| Directed transport theory | pinned `multitubes` modules under `Maths/Graph/` and `Maths/Multitubes/` | Exact and lax path transport; path-category, SCC, condensation, and categorical-retract normal forms; complete-lattice closure; additive cycle and signed-circulation duality; sparse rational and integral finite-inequality certificates; and max-affine path, slack, gauge, and holonomy theory. |
| Uniform-payoff consequences | `UniformEquilibrium/Diagnostics/Uniform/Consequences.lean` | Semantic waist dependencies, target equivalence under vanishing payoff gaps, potential shaping, tail-width and bounded-work characterizations, and transition discontinuity. |
| Adaptive-potential systems | `UniformEquilibrium/Certificates/Adaptive/PotentialSystemTools.lean` | The single `AdaptivePotentialSystemAt` structure together with retargeting, profile transport, ledger conversion, finite-time bounds, and owner-separated assembly. |
| Quitting terminal selection | `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean` | The equivalence between terminal approximate Nash existence at every accuracy and uniform-payoff existence for finite quitting games. |
| Passive-player padding | `UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding.lean`, `UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingCanonical.lean`, `UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingCorollaries.lean`, `UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingRetraction.lean`, `UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingExploitabilityRetraction.lean`, `UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingPeriodRetraction.lean`, and `UniformEquilibrium/Quitting/Terminal/TargetTail/PassivePlayerPaddingUniformTargetRetraction.lean` | Projects actual padded behavioral profiles, lifts arbitrary old-player behavioral deviations, and prices new-only preemption by aggregate new-player Never gains. `HasTerminalExploitabilityGap.passivePlayerPadding_canonical` preserves the exact fraction `penalty / (penalty + card J * canonicalWidth)` of every supplied terminal gap. Projection and quiet lift preserve every literal live-root period, and `quittingTerminalExploitability_project_onePassivePlayer_le` gives the pointwise multiplier `1 + canonicalWidth / penalty`, including zero width. For the canonical positive-penalty padding only, `isUniformEquilibriumPayoff_passivePadding_iff` identifies the padded target set exactly with zero-extensions of old targets. This converse does not reduce an arbitrary larger-player reward table and is not a general cardinality-descent theorem. |
| Passive-padding exact-period obstruction | `UniformEquilibrium/Quitting/Boundary/Analytic/PassivePaddingBlockCertificateRetraction.lean` and `UniformEquilibrium/Quitting/Boundary/Analytic/SolanPassivePaddingBlockNoGo.lean` | `exists_boundedCompletelyAbsorbingInverseIterate_of_onePassivePlayerBlockCertificate` deletes one passive player from any positive-penalty exact bounded absorbing admissible block certificate and returns a bounded completely absorbing inverse iterate of the old table, for every supplied coordinatewise upper bound. `no_isQuittingBlockCertificate_solanPassivePaddedReward_one` gives a literal rational Fin4 table, with dummy-only row `(3,3,3,-1)`, having no such certificate at any finite period. The stronger parametric theorem covers every real `0 < epsilon <= 2`; the rationality statement is literal at `epsilon = 1`. This rules out universal exact finite-period certificate production, not approximate cycles, nonperiodic profiles, or uniform equilibrium. |
| Diagonal target tails | `UniformEquilibrium/Quitting/Terminal/TargetTail/DiagonalTargetTail.lean` | Exact-prefix plus player-indexed closed-tail compilation and its counterexample restriction. |
| Support-retaining paths | `UniformEquilibrium/Quitting/Paths/SupportWitnessUniform.lean` | Infinite support-rational paths, finite periodic witnesses, and signed, absolute-weighted, and single-seam projective-lasso compilation. |
| Cyclic `K/N` finite words | `UniformEquilibrium/Quitting/Cycles/CyclicKofNPlayerPhaseHazards.lean` | Translated-block support clocks, positive player-and-phase hazards, canonical terminal evaluation, and a finite exact-Nash compiler. |
| Cyclic Green debt and exact obstruction classifiers | `UniformEquilibrium/Quitting/Cycles/CyclicGreenDebt.lean`, `MathUE/FiniteSetCoverClassification.lean`, `MathUE/FiniteAffineIntervalClassification.lean` | `quittingCyclic_norm_attachment_and_terminalDebt_le` turns a supplied approximate Nash--Bellman product-root word with playerwise positive opponent-only coalition atoms into the sharp `K * delta / rhoMax` attachment estimate and `(K / rho_i) * (epsilon + K * delta / rhoMax)` unrestricted behavioral-debt bound. The generic classifiers identify atom-cover failure with a common intersection and exact affine phase/seam infeasibility with one impossible phase, two crossed phases, or a phase--seam crossing; propagated canonical payoff-box rows add no obstruction type under the exact bounded recurrence hypotheses. No game-facing producer supplies the covered aligned word. |
| Endogenous interior cyclic Nash--Bellman blocks | `UniformEquilibrium/Quitting/Cycles/EndogenousInteriorCyclicBlock.lean`, `UniformEquilibrium/Quitting/Cycles/PeriodicApproximateNashDeviationCap.lean`, `UniformEquilibrium/Quitting/Cycles/InteriorApproximateNashCyclicProfile.lean`, `UniformEquilibrium/Quitting/Cycles/InteriorCyclicAbsorptionAlternatives.lean`, `UniformEquilibrium/Quitting/Cycles/OwnerSingletonCyclicConcentration.lean`, `UniformEquilibrium/Quitting/Cycles/InteriorCyclicDebtEscape.lean`, `UniformEquilibrium/Quitting/Cycles/InteriorCyclicTerminalDebtRatio.lean`, `UniformEquilibrium/Quitting/Cycles/FixedPeriodInteriorCyclicLimit.lean`, and `UniformEquilibrium/Quitting/Cycles/FixedPeriodInteriorCyclicTerminalGap.lean` | `nonempty_interiorApproximateNashCyclicBlock` constructs a strictly interior logistic-response word for every positive local error and finite period, with exact Bellman return and root Nash defect at most the error. `InteriorApproximateNashCyclicBlock.quitProbability_eq_response`, `quitProbability_odds_eq_exp`, and `tendsto_cyclicBlock_quitProbability_ratio_zero_of_separated_continueAdvantages` retain the exact response equation and its separated-Continue-advantage hazard selection. `value_eq_cyclicTerminalValue` identifies the displayed values with the actual almost-surely absorbing periodic profile, while `quittingTerminalDeviationDebt_cyclicBehaviorProfile_le_card_mul_error_div_opponentAbsorption` bounds unrestricted behavioral debt, including Never, by period times error over player-deleted absorption. `quittingGame_isUniformEquilibriumPayoff_of_interiorCyclicBlocks` consumes vanishing maximum ratios. Under a supplied positive terminal gap, `exists_interiorCyclicFixedDebtor_and_ownerEscape_of_terminalGap` instead returns singleton terminal-law/payoff concentration with vanishing outsider debts or vanishing total hazard, retaining the owner debt floor and opponent-absorption limit in either branch. `exists_fixedPeriodExactNashCyclicLimit_of_terminalGap` gives the fixed-period exact limit supported on at most one Quitter. The construction has `M`, `L`, and actual-profile `A`; `C` applies only to the vanishing-ratio branch. Neither positive-gap residual is terminal Nash, minimum-anchored, or otherwise consumed to a uniform payoff. |
| Fin5 full-face phase--seam regression | `UniformEquilibrium/Diagnostics/Quitting/Regression/FinFivePhaseSeamAtomFloor.lean`, `UniformEquilibrium/Diagnostics/Quitting/Regression/FinFiveFullFaceSourcePhaseSeam.lean` | One rational table has five actual two-date deleted-game exact terminal Nash sources, literal quiet lifts, positive omitted-player gaps, and mass-`1/2` opponent-only atoms, while its scalar phase rows and closing seam are incompatible below the sharp `31/32` threshold. Its ambient all-Quit equilibrium gives `D_* = 0`, so the regression isolates rather than resolves the positive-minimum alignment question. |
| Balanced singleton cycles | `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean` | A one-owner-at-a-time cyclic Bellman certificate with owner indifference, passive-player solo floors, and one positive opponent hazard per player compiles to exact terminal values, explicit square-root finite-horizon Nash/delivery bounds, and a uniform-equilibrium payoff. Finite mesh and collision caps are inferred automatically, so nonsingleton coalition rewards remain arbitrary. |
| Fin4 integral-tournament singleton fibres | `MathUE/LinearProgramming/FinFourIntegralTournament.lean` and `UniformEquilibrium/Quitting/Classification/LCP/FinFourIntegralTournamentBalancedSingleton.lean` | `exists_finFourIntegralTournamentCycleOutsider` selects a directed owner triangle and an outsider beating two consecutive owners in every no-sink four-vertex integral tournament. `target_isUniformEquilibriumPayoff` compiles the literal period-three tails to a fixed unrestricted-behavior uniform payoff. `singletonLCPFeasible_or_exists_uniformEquilibriumPayoff` gives the exhaustive sink-witness/no-sink-payoff split, and `normalizedSoloMatrix_eq_tournamentSkewMatrix_iff` exposes the exact singleton-row fibre. All nonsingleton coalition rewards remain arbitrary. The theorem covers integral tournament matrices only; it does not classify general standard-Q matrices or all Fin4 tables. |
| Exact controller--tester value and barriers | `UniformEquilibrium/Quitting/ControllerTester/All.lean`, `UniformEquilibrium/Quitting/Root/NeverGeneratedSemanticCarrier.lean` | A `4|I|+1` forward ledger and an exact occupation-flow/Bellman dual cover every calendar-dependent unilateral behavioral stopping hazard, including Never. Compact semantic optimization gives the fixed-target value `W_r(v)` and the literal raw maximum-debt minimum `eta(r)`; finite-word minima converge to them, and the original offline `inf_profile inf_N sup_{H>=N}` value equals `W_r(v)` without interchanging profile and horizon infima. The target-free value has full-reward-box greatest upper-semicontinuous Bellman and closed invariant-set duals. The package proves `eta(r)=0` iff a uniform-equilibrium payoff exists; it does not prove the sign for arbitrary Fin4 tables or make the barriers effective. |
| Fin4 two-block singleton fibre | `UniformEquilibrium/Quitting/Cycles/CyclicSupersolution.lean` and `UniformEquilibrium/Quitting/Examples/Cyclic/FinFourTwoBlockSingletonFiber.lean` | `TwoBlockTargetSingletonConditions.target_isUniformEquilibriumPayoff` gives the fixed target `(1, -1/2, 0, -1/4)` when singleton rows 0 and 1 are fixed, `r_2({2}) <= 0`, and `r_3({3}) <= -1/4`; `target_isUniformEquilibriumPayoff_of_exactFourSingletonRows` is the literal four-row corollary. Every nonsingleton reward remains arbitrary. The periodic witnesses are terminal approximate Nash against unrestricted behavioral deviations. Their owner-1 block uses the generalized cyclic supersolution compiler's Continue upper bound rather than owner indifference. This is a solved Fin4 table class, not a result for arbitrary Fin4 rewards. |
| Cyclic singleton escort and open-sign producer | `UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`, `UniformEquilibrium/Quitting/Cycles/CyclicSingletonTailProducer.lean`, `UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean` | `BalancedSingletonCycleCertificate.exists_escortCycle` forces a closed escort walk with period at least two from any balanced singleton certificate. `hasQuittingCanonicalEqualHazardTailData_iff` gives the exact criterion for the canonical equal-hazard tail data, and `QuittingCyclicSingletonOpenSignData.isUniformEquilibriumPayoff` produces a direct unrestricted-behavior uniform payoff for every finite cyclic size in the open-sign class. The escort conclusion is “at least two,” not “exactly two”; this is not a necessity theorem for arbitrary cyclic certificates, and no arbitrary cyclic matrix is covered. |
| Essential APS | `UniformEquilibrium/Quitting/EssentialAPS/All.lean` | The complete singleton-flow APS layer, including the adaptive-mesh capstone. |
| Projective packets and lassos | `UniformEquilibrium/Quitting/Projective/LassoAll.lean` | Matching-order analytic packets, packet-target mismatch, resolved-chart/Farkas contracts, exact signed monodromy, finite charged return, forward-block single-seam closing, and lasso compilation. |
| Actual-profile paid cap ports and cumulative near-returns | `MathUE/ProbabilityMassFunction/BoundedSupportAverage.lean`, `UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortSequenceNearReturn.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapMinimumFiberContraction.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfilePaidCapMinimumApproximation.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfilePaidCapUniformStepObstruction.lean` | `exists_support_pair_expect_sub_le_sub` brackets two bounded stopping-law averages by actual support atoms, so `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` retains the full gap at every literal profile. `nonempty_actualProfilePaidCapPort` constructs the source and port. Its exact trichotomy closes positive charge with zero displacement; a terminal gap leaves quantitative descent or inertness. The contraction estimates give `D_* A <= D_source - D_*` and `D_* rho <= 2 R (D_source - D_*)`, hence every exact-fiber source is inert. `exists_profileSequence_eventually_all_paidCapPorts_small` retains one realizing sequence and eventually makes every compatible source/port simultaneously small; `not_uniformPositivePaidCapDebtDropSelection` excludes any fixed positive real debt-drop step over all profiles. Conversely, a supplied source/port sequence with eventual total absorption bounded below and cap displacement tending to zero produces source-matched cumulative near-returns at every retained positive charge below that floor, and a uniform-equilibrium payoff. No producer supplies the floor. Remaining regeneration must be profile-dependent and nonuniform or genuinely well founded, or consume inertness. No attained minimum profile or such consumer is supplied. |
| Fixed cap-pin exact-root debt drop | `UniformEquilibrium/Diagnostics/Quitting/FixedCapPinCoordinateDebtDrop.lean` | `fixedCapPinDebtDropBound_pos` makes the bound `min (gamma / 2) (gamma ^ 2 / (16 * M))` literally positive. `fixedCapPin_coordinateDebtDrop` forces every exact product root to spend at least that amount of one named player's debt from only bounded rewards, that coordinate's bounded prescribed value, debt at least `gamma`, and cap distance at most `gamma / 4` from the singleton reward. `fixedCapPin_totalDebtDrop` gives the same total-debt loss when all source debts are nonnegative. `eventually_fixedCapLimit_coordinateDebtDrop` and `eventually_fixedCapLimit_totalDebtDrop` put every exact root inside one eventual quantifier when the fixed cap converges to the singleton reward. This has `M`, `L`, and a conditional one-step `C` for supplied semantic-pair sequences with those fields, but no integrated source `A`. Prefixing need not preserve the cap pin, so the theorem supplies no renewal or regeneration. |
| Same-root singleton-gap debt descent | `UniformEquilibrium/Quitting/Root/TerminalSemanticDebt.lean` and `UniformEquilibrium/Quitting/Root/SingletonGapSemanticDebtDescent.lean` | `quittingRootEndpointDifference_ge_singletonGap_sub_four_mul_of_tail_bound` compares an arbitrary bounded payoff tail to one singleton reward. For a supplied carrier pair with one debt coordinate above `debtFloor`, one strict singleton gap, and an exact Nash root against the pair's displayed payoff, `quittingTerminalSemanticPrefix_debtDrop_and_minAbsorption_of_carrier` preserves carrier membership, spends total semantic debt by at least `min debtFloor (min (gap / 2) (gap * debtFloor / (8 * M)))`, and forces joint absorption at least `min 1 (gap / (8 * M))` at that same literal root. This source-independent result has `M`, `L`, and a conditional one-step `C`; it has no `A` selecting the pair or exact root and does not regenerate a source, prove a reset wall, or construct a renewable sequence. |
| Recurring immediate-Quit cap reset exit | `UniformEquilibrium/Quitting/Root/NestedImmediateQuitCapExactPrefixExit.lean` | For a supplied nested actual-profile sequence with vanishing opponent absorption for the fixed observer and one fixed positive player-debt floor, `eventually_terminalPayoff_le_singleton_sub_half_at_immediateQuitCapReset` puts the parent payoff below the singleton reward by half the floor at every sufficiently late immediate-Quit cap reset. `eventually_every_exactRoot_has_debtDrop_and_absorption_at_immediateQuitCapReset` gives every exact product root at that literal payoff the common total-debt drop `min debtFloor (min (debtFloor / 4) (debtFloor ^ 2 / (16 * M)))` and absorption floor `min 1 (debtFloor / (16 * M))`; cofinal and carrier-minimum consequences are literal theorems. `exists_nestedPayoffLimit_le_singleton_sub_debtFloor_of_cofinal_quitCap` uses the stronger summable-marginal-hazard hypothesis to prove simultaneous coordinatewise payoff convergence and separation of the limit from the singleton reward by the full debt floor. These results have `M`, `L`, and conditional reset-exit `C`, but no `A` producing the nested profiles or cap resets, and no regeneration theorem. |
| Fixed cap-pin approximate-root expenditure and visit bounds | `UniformEquilibrium/Diagnostics/Quitting/FixedCapPinApproximateRootDebtExpenditure.lean` and `UniformEquilibrium/Diagnostics/Quitting/FixedCapPinDebtVisitBudget.lean` | `fixedCapPin_approximateRoot_coordinateDebtDrop` retains the exact-root drop up to the root-Nash error. The finite visit ledgers charge errors and positive replenishment of the named debt coordinate. `fixedCapPin_prefixChain_visitSet_finite_and_ncard_le` proves finiteness of all visits and the floor-cardinality bound under summable nonnegative errors. `fixedCapPin_carrierPrefixChain_visitSet_finite_and_ncard_le` supplies the initial `2 * M` bound from carrier membership. The re-entry versions allow summable replenishment, and `fixedCapPin_reentry_visitSet_finite_and_ncard_le_coordinateSeams` pays for it through summable prescribed-payoff and cap seams. These are conditional consumers for supplied chains; they do not construct the source chain, prove summability for a renewed source, or supply a uniform equilibrium. |
| Fixed cap-pin first-root limits and responses | `UniformEquilibrium/Diagnostics/Quitting/FirstExactRootDebtDescent.lean`, `UniformEquilibrium/Diagnostics/Quitting/FirstExactRootCompactification.lean`, `UniformEquilibrium/Diagnostics/Quitting/FirstExactRootSurvivalResponses.lean`, and `UniformEquilibrium/Diagnostics/Quitting/FirstExactRootStationaryDichotomy.lean` | `StationaryQuitNowCapPinSource.firstExactRoot_dichotomy` consumes actual stationary cap-pinned profiles and absence of a uniform-equilibrium payoff. Every exact root spends a uniform amount of the named debt and has absorption at least `min 1 (gamma / (16 * M))`. One source/root subsequence has positive survival and an executable copied-root paid response, or vanishing survival, one sure limiting owner, vanishing outsider debt, and an attained shifted Quit0-or-Never cap with positive opponent reach. The latter branch retains the same limiting stationary root, its zero outsider debts, and its complete Never cap with a terminal-gap gain. Stationary endpoint attainment includes opponents who always Continue. The explicit `UniqueSureNeverReactivationRegression` shows that the Never child can reactivate an outsider. Neither branch supplies a renewed cap pin or a returned minimum source. |
| Sure-root singleton handoff at the supplied profile | `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SureRootSingletonHandoff.lean` | `quittingRootFreeMixedPoint_mem_singletonBaseNashSet_of_sure_exactNash` restricts any exact root with a sure owner to its own singleton-base induced Nash point. The root, stationary profile, and owner Always Continue repair are identified by explicit equalities. Under a terminal exploitability witness, `QuittingTerminalExploitabilityWitness.exists_sureRootHandoff_with_paidAtom_and_floorDispatch` produces the handoff and paid endpoint atom at that repaired profile, then gives a free player's punishment-floor failure or its exact orbit with vanishing absorption and no positive-threshold charged recurrence. The player type is arbitrary finite, and the owner need not be the only sure quitter. This does not produce the supplied root from finite source descendants or consume the vanishing-absorption orbit. |
| Opponent-tight terminal-semantic realization | `MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`, `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean` | `nonempty_terminalSemanticSelectedLawLimit_of_mem_carrier` retains, for every carrier point, actual realizing profiles, one strict subsequence, semantic convergence along it, and coordinatewise compact-law convergence. `quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit` reconstructs one actual profile realizing a selected semantic limit whenever every player's opponents are uniformly tight; caps retain the unrestricted behavioral strategy class through exact pure-time extremality. Two proper limiting clocks suffice. At a nonattained global minimum there is at most one proper clock; the unique-proper arm has an exact Never cap, negative singleton reward, and strict jump bounded by the opponent Never product. With nonnegative singleton rewards, one selected law-limit package has every limiting clock nonproper. The all-nonproper arm and the mixed-sign unique-proper arm have no paid, admissible-path, or uniform-payoff consumer. Never-atom convergence of the approximants and one exceptional owner uniform across subsequences are not asserted. |
| Terminal-law escape, cap, minimum, and social-sign attainment | `UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeAccount.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeDebtJump.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeMinimumConsequences.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeSocialSignAttainment.lean` | The common source/account adapter retains semantic, marginal-law, and full outcome-law convergence and exposes the exact escape, cap-drop, and debt-jump identities. At a supplied global carrier minimum, nonnegative singleton rewards make the cap-drop sum nonnegative; minimum-value nonattainment then selects a positive-social-reward escape coalition at the exact finite-player scales. Under nonpositive aggregate coalition rewards, `exists_actual_minimum_of_singleton_nonneg_social_nonpos` instead returns an actual globally minimal profile with the same minimum debt value. Its account has zero debt jump, cap drops, and escaped social reward, with positive escape supported only on zero-social-reward coalitions. Strict aggregate negativity strengthens this to exact realization of the supplied minimizing semantic pair by `minimum_point_attained_of_singleton_nonneg_social_neg`. The full generic finite-player packet has `M`, `L`, carrier-facing `A`, and branch-local `C` for weak-sign value attainment and strict-sign point attainment; the positive-social arm has no `C`. Weak signs do not realize an arbitrary minimizer, and no Fin4 specialization, terminal Nash profile, or uniform-equilibrium payoff is supplied. |
| Literal terminal-debt infimum and joint-law minimum | `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumLawFiniteAtom.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCapNashNearMinimum.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauNashMoat.lean`, `Research/Quitting/UniqueAllContinueCapStackNoGo.lean`, `Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`, `Research/Quitting/MinimumLawCausalSuffixInertStack.lean`, `Research/Quitting/MinimumLawCausalSuffixPureNeverLimit.lean` | `quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum` identifies the literal-profile infimum with every compact-carrier minimum, and `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff` identifies positivity with the finite-quitting obstruction. `exists_positive_finiteLawAtom_of_punishmentNormal_minimum_of_not_uniformPayoff` and `nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff` remove the pure-Never obstruction for every nonempty finite punishment-normal game without a uniform-equilibrium payoff; the Fin4 hard-residual declarations remain checked corollaries. They retain the same minimum joint point, one positive finite atom, and arbitrarily deep source-matched cap-Nash chronologies. The Research maximal-cap dispatch turns that exact atom into either one positive exact punishment-prefix charge retaining it or arbitrarily deep literal all-Continue, zero-charge stacks. The latter have pure-Never marginal limits, fixed-horizon joint and opponent tail products tending to one, checked failure of joint and opponent tightness, and vanishing absorption for nearby approximate roots through the quantitative near-minimum cap freeze and robust moat. The joint point is a carrier limit rather than an attained actual profile; the positive-charge arm has no paid/reset/return-cycle consumer, and the inert arm may still carry tangent or paid structure. Coordinate marginal limits do not recover the retained positive joint atom, so neither branch currently yields a contradiction or a uniform-equilibrium payoff. |
| Positive-minimum two-cut coercivity and paid splice | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumTwoCutPaidSplice.lean` | `quittingTerminalSemanticDebtSum_twoCut_eq` is the exact survival-weighted two-cut debt telescope. `QuittingPositiveMinimumTwoCutBlock.totalCharge_add_theta_mul_exitExcess_ge` gives the corresponding coercive inequality for every supplied survival factor. For a supplied uniformly reached post-mark block, `offMinimum_or_exists_paidSplice` returns either a strict exit from the minimum level or one fixed coordinate payer and, at every positive tolerance, an executable suffix deviation obtained by a literal `Function.update`; the latter has the exact reach-weighted payoff gain and same-coordinate debt drop. `finFour_offMinimum_or_exists_paidSplice` exposes the Fin4 constants `block.coerciveConstant / 16` and `block.reachFloor * block.coerciveConstant / 16`. The pre-entry behavior, live roots and masses, stage coalition masses, and finite stopping atoms remain unchanged. This conditional interface has `M` and `L`, and a conditional `C` for supplied two-cut blocks, but no source `A`: it constructs no cuts, hazard or reach floor, renewable child, ancestry, terminal equilibrium, or uniform-equilibrium payoff. The paid-splice module itself does not consume a signed semantic seam. |
| Minimum-tail silent-padding two-cut source | `UniformEquilibrium/Quitting/Paths/RootSequenceSilentPrefix.lean`, `UniformEquilibrium/Diagnostics/Quitting/SilentPrefixTerminalSemantics.lean`, `UniformEquilibrium/Diagnostics/Quitting/SilentPaddingTwoCutSource.lean`, `UniformEquilibrium/Diagnostics/Quitting/MinimumTailProfileSource.lean`, `UniformEquilibrium/Diagnostics/Quitting/MinimumTailSilentPaddingConsumer.lean`, and `Research/Quitting/FinFourProducerAtlas/MinimumReturnPacketSilentPaddingAdapter.lean` | A leading all-Continue row is inserted before a literal root-sequence tail without changing the complete terminal outcome law, including Never. A positive finite-law atom gives a finite post-mark hazard window, exact entry reach one, and a supplied positive-minimum two-cut block. `FinFourMinimumTailFiniteAtomCompactification.eventually_nonempty_silentPaddingTwoCutRealization` retains one common subsequence and fixed atom and applies the checked off-minimum-or-paid-splice consumer at every sufficiently late rank. `FinFourMinimumReturnPacket.exists_finiteAtomCompactification_eventually_silentPaddingTwoCutRealization` is the Research source adapter from the actual minimum-return packet. The generic construction and conditional consumer have `M` and `L`; the Research adapter supplies branch-local `A`, and the paid-splice alternative is a branch-local `C`. The artificial first row is only an order witness: there is no renewable return, meaningful source chronology, Nash claim, nonpayer cap control, terminal approximation, or uniform-equilibrium payoff. |
| Signed terminal-semantic seam telescope | `UniformEquilibrium/Quitting/Debt/Dynamic/TerminalSemanticSignedSeamTelescope.lean` | `QuittingTerminalSemanticSeamChain.debtSum_eq_totalCharge_add_endpoint_add_weightedSignedSeamError` is the exact finite signed-error telescope for supplied semantic prefix equations. Prescribed-payoff and unrestricted-cap errors jointly control its absolute seam cost; a common coordinate bound costs `2 * card ι`, and `finFour_weightedAbsoluteDebtSeamError_le_of_commonCoordinateBound` exposes factor `8`. `totalCharge_add_coordinateSeamBound_add_theta_endpointExcess_ge` gives the seam-stable coercive bound from only scalar endpoint debt floors and a survival ceiling. This conditional semantic compiler has `M` and `L`, but no source `A` and no consumer `C`: it supplies no executable profile, behavior, chronology attachment, renewable child, terminal equilibrium, or uniform-equilibrium payoff, and payoff-only seam control is insufficient. |
| Positive-minimum carrier-cycle seam toll | `UniformEquilibrium/Quitting/Debt/Dynamic/TerminalSemanticCarrierCycleSeamToll.lean` | `QuittingTerminalSemanticCarrierCycle.sum_signedDebtRebase_eq_sum_netAbsorptionCharge` is the exact cyclic debt ledger for supplied carrier points, literal product roots, and an arbitrary finite successor permutation. Exact roots turn positive carrier debt into an `L¹` seam toll; `finFour_debtFloor_div_eight_mul_sum_absorptionMass_le_sum_semanticSupRebase` gives the sharp Fin4 factor `1/8`. The approximate form subtracts `card ι` times total root error, stationary equal-marginal couplings obey the same weighted toll, and `QuittingTerminalSemanticCarrierOpenChain.debtFloor_mul_sum_absorptionMass_sub_initialExcess_le_sum_signedDebtRebase` records the one-use open-chain initial-excess battery. These supplied-family identities have `M` and `L`, but no source `A` or downstream `C`: they construct no cycle, behavioral chronology, renewal, terminal consumer, Nash profile, or uniform-equilibrium payoff. |
| Law-tight cap--Nash saturation hull and minimum level set | `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashSaturationHull.lean`, `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashMinimumFace.lean`, and `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashGlobalMinimumMoat.lean` | `quittingLawTightCapNashSaturationHull` closes one supplied joint-law origin under exact cap--Nash prefixes and debt-nonincreasing replacements within the same terminal-law fibre. If the origin lies in the joint carrier, the hull is compact. A supplied positive global carrier debt floor and positive finite origin atom give a debt minimizer retaining that atom. `quittingLawTightCapNashSaturationMinimumFace` is only the minimum equality level set, not a convexity claim. Every point on it minimizes debt on its whole terminal-law fibre; at positive minimum debt, all Continue is the unique exact root against the displayed cap and its semantic/law prefix is the identity. `lawTightCapNashMinimum_globalMinimumOriginDebtMoat` additionally shows that a hull minimum over a globally minimizing origin inherits the same global debt and the literal all-owner singleton moat measured by the origin debt. `quittingLawTightCapNashSaturationHull_rootAbsorptionMass_le_debtExcess_div` and the two finite-chain sum bounds charge exact-root absorption to debt above the hull minimum. This conditional layer has `M` and `L`, but no `A` selecting its origin, floor, or atom and no standalone downstream `C`; it recovers no ancestry, timing, behavioral realization, strict chamber, Fin4 source, or uniform-equilibrium payoff. |
| Law-tight strict-minimum carrier chambers | `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean` and `UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean` | `lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle` classifies a supplied positive minimum-face point with a positive finite atom as full debt support, a same-law reset-rigid return fixed by the all-Continue prefix, or singleton/Never support with exact cap binding and a binding-collision cycle of period at least two. `finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber` supplies the origin, positive law-tight minimum, retained finite atom, both global-minimum statements, origin/minimum debt equality, and literal origin-debt moat from a Fin4 no-uniform-payoff hypothesis; the moat and cap binding exclude singleton/Never, leaving full debt or reset-rigid return. The generic layer has `M` and `L`; the Fin4 capstone adds source `A` and branch-local `C` only for that exclusion. The two surviving arms have no behavioral realization, chronology, consumer, contradiction, or uniform-equilibrium conclusion. |
| Singleton-cap collision sign and singleton/Never cap tightness | `UniformEquilibrium/Quitting/Punishment/SingletonCapBindingCollision.lean` and `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonNeverCapTightness.lean` | `exists_quittingSingletonCollisionGain_pos_of_unique_allContinue` proves that every binding coordinate at a cap with unique all-Continue exact root has a distinct binding collision successor with positive gain. `one_sub_neverMass_mul_opponentNeverProduct_le_singletonOutcomeMass` is the one-sided behavioral singleton cylinder; `terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward` uses one common carrier-realizing sequence and quantitative immediate-Quit/Never bounds to make a positive singleton/Never owner's zero-debt cap equal its singleton reward. These declarations have `M` and `L`. They do not construct the cap, carrier point, law support, unique-root hypothesis, behavioral limit realization, downstream `C`, or uniform-equilibrium payoff. |
| Nonsingleton anti-diffusion and live-weighted transfer | `MathUE/Probability/NonsingletonConcentration.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonsingletonAntiDiffusion.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`, and `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean` | `finite_exists_rpow_ratio_le_of_sum_root_le_one` supplies the sharp finite concentration exponent, while `exists_maximal_quittingStageCoalitionMass_of_positive_total` and `exists_quittingStageCoalitionMass_ge_tsum_rpow` attach it to actual behavioral stopping laws and a literal finite stage. `QuittingReprojectionDiffuseWindowPacket.terminal_card_eq_one` consumes this concentration to prove that every diffuse packet is singleton-labelled. The production live-weighted split `quittingLiveWeightedCollisionTransfer_tailEscape_or_routedTransfer` retains the actual source row, unrestricted behavioral debt, exact endpoint gain, selected distinct recipient, and a nonempty routed atom with no stage-mass loss; its Fin4 specialization has the exact `1/8` and `1/48` local constants. In Research, `QuittingMinimumLawCausalSuffixAtom.nonempty_tailEscape_or_routedTransferSubsequence` composes the actual minimum-law chronology into an inclusive strict-subsequence disjunction with general gain `mu^2 D_*/(16 card(I))` and recipient `mu^2 D_*/(32 card(I)(card(I)-1))` floors; `nonempty_finFourTailEscape_or_routedTransfer` exposes `mu^2 D_*/64` and `mu^2 D_*/384`. The alternatives may coexist. Neither surviving branch has a checked return, paid/reset, well-founded descent, or uniform-payoff consumer, so this does not contract the conjecture frontier. |
| Fin4 source-preserving producer atlas and common strong-packet contraction (Research-only) | `Research/Quitting/FinFourExhaustiveProducerAtlas.lean`, `Research/Quitting/FinFourProducerAtlas/ActualLowTail.lean`, and `Research/Quitting/FinFourProducerAtlas/SelfTailContraction.lean` | `uniformPayoff_or_nonempty_finFourProducerResidual` first gives the six source-tagged atlas. `sameStageEndpointTrace_false_of_visitedSupport_card_le_four` and `FinFourProducerResidual.withoutMonodromy` delete both Fin4 monodromy tags. The stronger `FinFourMinimumAtomProducer.nonempty_contractedConsumer` then treats the retained minimum atom directly: singleton atoms use one fixed owner-clock chronology, while every nonsingleton atom uses an actual selected row and its literal self-tail closure, so quantitative tail escape is no longer a terminal atlas leaf. `FinFourSelfTailLowRow.stageMass_eq_selectedStageMass`, `FinFourSelfTailLowRow.lambda_lt_stageMass`, and `FinFourSelfTailSingletonEndpoint.postDateSpine_eq_selectedProfile` retain the exact marked mass and the complete post-date `BehaviorProfile`. The raw `FinFourActualLowTailSingletonOrigin` tag records whether dispatch stopped at a partial singleton or at a terminal orbit, with route-source, routed-coalition, mass, path, mover, and action accessors. `FinFourMinimumAtomProducer.exists_residual_eq_of_hardResidual`, `exists_finFourMinimumAtomContractedConsumer_of_hardResidual`, and `uniformPayoff_or_exists_finFourMinimumAtomContractedConsumer_withResidualProvenance` retain literal equality to the supplied or selected hard residual. The route-tagged consumer retains the construction origin; its forgetful projection `FinFourMinimumAtomProducer.contractedConsumerResult` retains an actual strong packet. `QuittingTerminalExploitabilityWitness.hasStaticAtomicToggleHandoff` is the table-level, packet-independent handoff, and `not_hasQuittingExactPlayerDeletionAtGap_finFour` independently eliminates exact positive-gap deletion. `FinFourSingletonStageStrongConcentratedPacket.strategicArm_iff_action_eq_false` identifies the full named strategic arm with Continue mode, and `FinFourSingletonStageStrongConcentratedPacket.collisionMinimumResidual_of_action_eq_true` forces the unchanged source-attached collision-minimum residual in Quit mode. The action-indexed selector does not assert that such a residual is absent in Continue mode. This contraction has `M`, `L`, `A`, and `C`, but the collision-minimum arm remains open: there is no target full-root Nash, whole-profile near-minimality, return, regeneration, recursive descent, completion closure, or new uniform-payoff conclusion. |
| Fin4 weak-singleton forced-pair and cofinal minimum-tail contraction (Research-only) | `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean`, `Research/Quitting/FinFourProducerAtlas/ForcedPairMinimumTailConsumer.lean`, `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`, and `Research/Quitting/FinFourExhaustiveProducerAtlas.lean` | `FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairResidualCapstone` retains an arbitrary supplied weak core, its selected literal pair packet, the exact collision residual, and its cluster equality to the core's actual post-date tail. Its typed outcome is strict tail escape or minimum-tail with payer defect `lambda * D_* / 6` and gain `lambda^2 * D_* / 6`; the granular one-row declarations retain the stronger `D_* / 3`, `lambda * D_* / 3`, `lambda * gamma`, and canonical `mu^2 * D_* / 24` bounds. For a singleton minimum atom, `FinFourMinimumAtomProducer.nonempty_minimumReturnForcedPairFamilyCapstone` fixes one source chronology and table outsider before every `0 < lambda < mu`; each `ResolutionCapstone` retains one moving packet, a collision residual with cluster debt exactly `D_*`, and one fixed payer carrying the stronger `D_* / 3` defect and `lambda * D_* / 3` gain bounds at every index. The cross-tail declarations retain exact prefix live roots and marked mass, literal full post-date spine, and exact spine-debt excess. This has `M`, `L`, `A`, and `C` for the forced-pair collision/minimum-tail contraction only. The arbitrary weak core can still take the tail-escape arm, and the cofinal minimum-tail collision residual remains unconsumed: no whole pair target is near-minimal or cap--Nash, and there is no cross-coordinate cap control, return, regeneration, recursive descent, completion, or uniform-payoff conclusion. |
| Fin4 source-preserving completion atlas (Research-only) | `Research/Quitting/FinFourProducerAtlas/SourcePreservingSingletonFrames.lean`, `Research/Quitting/FinFourProducerAtlas/SourcePreservingForcedPair.lean`, `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`, `Research/Quitting/FixedPairMinimumTailNormalizedReturn.lean`, `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinitePureTimeResetArrival.lean`, `Research/Quitting/FinFourProducerAtlas/ThreeRoleAscentResetHandoff.lean`, and `Research/Quitting/FinFourExhaustiveProducerAtlas.lean` | `FinFourProducerResidualWithoutMonodromy.exists_cofinalSingletonPacket` retains literal equality to the input four-tag residual and constructs one entrance-indexed cofinal singleton stream: one owner-clock chronology in the minimum-singleton case and exactly the stored selected rows in the other three cases. The forced-pair compiler retains the exact collision tail, post-date behavioral spine and outcome law, and the canonical `mu^2 * D_* / 24` payer-gain floor. The priority atlas fixes all four finite labels and gives uniform positive tail excess or tail debt converging to `D_*`, with exact self-shifts and the stated two-terminal-component structural graph. `FinFourUniformEscapePacket.exists_maximalCapNash_halfFloorDispatch` now consumes every literal escape row into a positive-survival maximal exact root and same-tail return-selection-or-universal-undercharge dispatch; the named continuation and returned-profile accessors retain the actual tail law and half-floor near-minimum debt, but no reset coordinate. The generic `QuittingMarkedPairMinimumTailSource.nonempty_normalizedThreeRole_or_strictInert` derives its compact selection, passport, minimizer, and actualizer from fixed-pair rows with uniform positive mass/gain floors. `FinFourMinimumReturnPacket.nonempty_normalizedThreeRole_or_strictInert` uses the exact termwise tail identity and returns actual three-role regeneration/ascent or strict normalized inert. In its strict-ascent branch, `FinFourThreeRoleAscentResetHandoff.nonempty_of_strict_ascent` selects one literal endpoint rank and enters a fixed-law reset dispatch along a recipient-first profitable path of length at most seven, while preserving the fixed minimum dispatch source and the historical endpoint law, roles, and routed mass. `uniformPayoff_or_sourcePreservingConsumedOutcome` composes the earlier consumers while preserving the exact outer residual index. This has `M`, `L`, `A`, and branch-local `C`, but no terminal `C`: the open escape/return capstones, consumption of the reset-dispatch branches, cross-coordinate cap bound, descent, outer-entrance regeneration, terminal approximation, and uniform-equilibrium completion remain unproved. Equality regeneration retains only the underlying hard residual and exact new endpoint law; the target law need not equal the original source law. |
| Paid nonsingleton maximum-toggle cycle and atom dispatch (Research-only) | `Research/Quitting/PaidNonsingletonToggleCycle.lean`, `Research/Quitting/FinFourProducerAtlas/PaidNonsingletonCycle.lean`, and `Research/Quitting/FinFourExhaustiveProducerAtlas.lean` | `exists_finFourMaximumToggle_terminalOrbit_or_closedSegment` makes the deterministic table-level maximum-toggle dispatch literal. A closed nonsingleton orbit has period `4`, `6`, or `8`; every realized edge over a supplied actual marked row gains at least `lambda * D_* / 4` and subtracts exactly that gain from the mover's unrestricted debt. `FinFourLiteralSiblingCycle.exists_spectator_debtRise` is the generic complete-profile ledger giving the sharp Fin4 divisor `3`. From the actual cofinal forced-pair family, `nonempty_forcedPairPaidNonsingletonCycle` fixes one edge and one distinct observer on a strict source subsequence, with observer rise at least `lambda * D_* / 12`. `FinFourForcedPairPaidNonsingletonCycle.atomAlternative` supplies the checked fixed charge `7 * lambda * D_* / 96` and vanishing error. `nonempty_paidNonsingletonCycleOutcome` is exhaustive: a paid singleton, a strict off-minimum actual endpoint, or a fresh minimum-atom producer at the endpoint's same joint semantic/law point with the unchanged hard residual and routed-law mass at least `lambda`. This has `M`, `L`, and `A`; `C` is branch-local through the atom decoder and equality-arm source regeneration. Cycle edges are same-date sibling comparisons, not successive play dates. There is no chronological sibling edge, return, renewable rank descent, terminal approximation, atlas completion, or uniform-equilibrium conclusion. |
| Normalized-passport minimization, actual Fin4 minimum return, and endpoint-law regeneration (Research-only) | `Research/Quitting/NormalizedPassportPrefixOrbit.lean`, `Research/Quitting/NormalizedPassportMinimizer.lean`, `Research/Quitting/NormalizedPassportMinimumReturn.lean`, `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`, `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`, and `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean` | The generic declarations `QuittingMarkedPairDecoratedFamily.rawDecoration_markedMass_eq`, `QuittingMarkedPairDecoratedFamily.rawDecoration_actualGain_eq`, and `QuittingMarkedPairDecoratedFamily.descendant_postMarkSpine_eq` expose exact arbitrary-prefix scaling and the full post-mark spine. `QuittingMarkedPairDecoratedFamily.exists_minimum_normalizedPassportSlice_eq_or_strict_inert` then gives global-minimum return or strictly larger debt with all Continue as the unique exact cap--Nash root for a supplied convergent passport. The Fin4 adapter `FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_normalizedReturnSelection` derives the compact subsequence and passport from actual forced-pair profiles. `FinFourMinimumAtomProducer.exists_normalizedReturnSource_for_all_resolutions` fixes one source chronology and outsider before every `0 < lambda < mu`; the packet, subsequence, roles, minimizer, and outcome may depend on `lambda`. In the equality arm, `QuittingMarkedPairMinimumReturnActualizer.nonempty_threeRoleEndpointLaw_of_minimumReturn` derives fixed roles and an actual endpoint joint law without accepting a chord or roles. `ConcentratedCollisionThreeRoleEndpointLaw.perRank_mass_chain` retains `rho` below the source marked mass, routed target stage mass, and target terminal-law mass. The literal Fin4 bounds are `rho^2 * D_* / 8` in `finFour_mover_drop` and `rho^2 * D_* / 64` in `finFour_recipient_rise`. `ConcentratedCollisionThreeRoleEndpointLaw.nonempty_finFourRegenerationOrAscent` gives strict target-debt ascent or exact endpoint-law source regeneration; `FinFourThreeRoleMinimumTargetRegeneration.next_terminalMass_eq_endpoint`, `next_residual_eq`, `next_point_eq`, `next_terminal_eq`, and `resolution_le_terminalMass` retain the hard residual, joint point, routed atom, and law-mass floor. Thus normalized return has `M`, `L`, and `A`; its equality branch has `C` through the endpoint-law classifier and, on the minimum-target subbranch, a fresh `FinFourMinimumAtomProducer`. The strict normalized inert arm has no `C`. The minimizer may lie only in the enlarged arbitrary-prefix slice and need not be attained; actualizer origin ranks need not be cofinal; the root word is not canonical. A public chord alone does not determine the endpoint law. There is no canonical ray, chronology return, rank decrease, recursive closure, strict-inert consumer, or uniform-equilibrium conclusion. |
| Source-faithful minimum-law causalization and Fin4 endpoint regeneration (Research-only) | `Research/Quitting/SourceFaithfulMinimumLawCausalization.lean` and `Research/Quitting/FinFourProducerAtlas/SourceFaithfulThreeRoleRegeneration.lean` | `nonempty_sourceFaithfulMinimumCausalization` retains one supplied convergent profile family and its literal marked dates, chooses only finite exact cap--Nash words and cutoffs, proves exact shifted atom mass with an eventual `lambda / 2` floor, and makes prefix debt converge to the positive minimum while joint survival tends to one. `quittingTerminalPayoff_shiftedBehavioralResponse_sub_eq`, `QuittingSourceFaithfulMinimumCausalization.responseMenu_transport`, and the Fin4 `responseMenu_lowerBound_transport` transport arbitrary complete behavioral two-response contrasts and their supplied lower bounds exactly by the player-deleted survival factor; `opponentSurvival_tendsto_one` and `responseMenuMultiplier_bounds` show that factor lies between joint survival and one and tends to one. For a same-minimum three-role endpoint with a nonsingleton incoming marked coalition, `ConcentratedCollisionThreeRoleEndpointLaw.nonempty_sourceFaithful_finFourMinimumTargetRegeneration` keeps the exact endpoint target profiles and incoming marks, exposes a public chronology and the original residual/endpoint point/routed terminal, and forgets through `toMinimumTargetRegeneration` to the older regeneration. Without nonsingletonity, `nonempty_sourceFaithful_reselectedMarkRegeneration` keeps the exact profiles, source, point, terminal, and residual but selects new positive finite-window marks; it claims neither equality with incoming marks nor a uniform per-stage floor. These declarations have `M`, `L`, and `A`, but no `C`: they do not select a common observer, orient a paid cycle, consume spectator leakage, or produce a renewable return or uniform equilibrium. |
| Single-density normalized boundary and scalar Zeno obstruction (Research-only) | `Research/Quitting/NormalizedPassportSingleDensityToll.lean`, `Research/Quitting/FinFourProducerAtlas/NormalizedInertSingleDensityToll.lean`, `Research/Quitting/NormalizedPassportVanishingDensityBoundary.lean`, `Research/Quitting/FinFourProducerAtlas/NormalizedInertVanishingDensityBoundary.lean`, and `Research/Quitting/NormalizedPassportZenoBoundary.lean` | `FinFourNormalizedReturnSelection.carrier_actualGain_eq_gap_mul_markedMass` identifies actual gain with the fixed positive forced-pair gap times marked mass on the complete closed prefix carrier. `QuittingSingleDensityPassportMinimizer.prefixMap_mem_slice_iff`, `rootDefect_ge_min_tent`, and `saturation_ratio` give the exact one-density feasibility criterion, arbitrary-root tent bound, and saturated mass/gain/debt ratios. `FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_normalizedInertVanishingDensityBoundary` internally selects all slice minimizers, one compact subsequence, and one limit. `FinFourNormalizedInertVanishingDensityBoundary.outcome` returns minimum debt with an internally constructed actualizer, zero limiting mass and gain, or the literal fixed-cap barrier `D(limit) * Abs(root) <= rootDefect` for every product root; deterministic Continue trembles cover full-absorption roots without exchanging quantifiers. This has `M`, `L`, and `A`. Only the positive minimum-return arm has `C`, through the existing actualizer and endpoint-law consumer; the zero-passport and barrier arms have no `C`. The scalar `NormalizedPassportZeno` chain realizes the ledgers and saturated half-density transition at every finite rank, while `RenewableNormalizedPassportDensity.rank_lt_of_density_le_half` proves strict natural-rank descent only under a supplied renewable absolute density floor. The scalar system is not a quitting game, and no Fin4 source supplies that floor or a regenerated source. There is no base-cluster return, chronology return, barrier consumer, terminal approximation, recursive closure, or uniform-equilibrium conclusion. |
| Off-minimum carrier actualization (Research) | `Research/Quitting/NormalizedPassportCarrierActualizer.lean` | `nonempty_quittingMarkedPairCarrierActualizer` selects literal raw descendants of any positive normalized carrier point above the positive reference debt, with fixed reference-based mass and gain floors. `QuittingMarkedPairCarrierActualizer.toDecoratedFamily` reassembles them as an executable family and `toDecoratedFamily_baseDecoration_tendsto` retains the complete decoration limit. This actualizer has `M`, `L`, and `A` relative to its supplied decorated family and carrier point, but no `C`; origin ranks need not be fixed or cofinal and the incoming absolute floor is not preserved. |
| Finite-word complete-cap defect ledger | `UniformEquilibrium/Quitting/Root/FiniteWordWeightedCapDefectLedger.lean`, `UniformEquilibrium/Quitting/Root/ZeroJointCapLedgerBoundary.lean`, and `UniformEquilibrium/Quitting/Examples/HostClearingCapLedgerBoundary.lean` | `quittingTerminalDeviationDebt_literalRootStack_eq_playerLedger_add` and `quittingFiniteWordPlayerCapDefectLedger_append` are exact playerwise identities against actual complete suffix caps. Under vanishing joint survival, `terminalExploitability_tendsto_zero_iff_playerLedger_tendsto_zero` characterizes vanishing unrestricted exploitability. `exists_uniformPayoff_of_zeroJoint_playerLedgers` is its conditional uniform-payoff consumer. In a hypothetical Fin4 counterexample, `exists_positive_minimum_and_fixed_capLedger_payer_of_no_uniformPayoff` instead derives a positive global minimum and one fixed payer on a strict subsequence whose ledger is at least one eighth of that minimum. Distinct serial hosts can screen the deepest tail without cancelling a persistent outer ledger; this obstruction and fixed-host subsequence selection are literal theorems. The marked-profile regression has outsider cap defect and ledger exactly one despite zero host debt. These results do not select a uniformly defective row, paid chronological edge, or renewed source, and the positive-ledger source does not meet the vanishing-ledger consumer. |
| Actual Zeno host compression, sibling coalescence, and finite clock clearing (Research-only) | `Research/Quitting/CombinedDeletedSurvivalWord.lean`, `Research/Quitting/FinFourProducerAtlas/ActualZenoDeletedSurvivalSource.lean`, `Research/Quitting/FinitePrefixClockClearing.lean`, `Research/Quitting/FinFourProducerAtlas/FullyScreenedFiniteClockClearing.lean`, `Research/Quitting/FinFourProducerAtlas/ActualZenoHostCompression.lean`, and `Research/Quitting/FinFourProducerAtlas/ActualZenoFullyScreenedSiblingCoalescence.lean` | `quittingCombinedPremarkWord_opponentSurvival_eq` factors each combined deleted clock into the arbitrary new word and immutable base chronology. `FinFourNormalizedInertVanishingDensityBoundary.nonempty_actualZeno_fixedEndpoint_or_coalescingClearingFamily` constructs the literal Zeno source at a zero-mass boundary and exhaustively returns either the fixed positive-host endpoint or one same-source package containing both the full-screening proof and clearing family. In the host arm, `FinFourActualZenoPositiveHost.other_tendsto_zero` screens every nonhost clock on the retained strict subsequence, while `FinFourActualZenoPositiveHost.FixedEndpoint.eta_le_markedMass`, `markedHostDefect_eq_zero`, `profile_opponent_eq`, `postMarkSpine_eq_reference`, and `terminal_erase_or_insert` retain the positive floor, zero local host defect, unchanged nonhost behaviors, complete tail, and exact routed terminal. In the screened arm, `abs_sibling_terminalPayoff_sub_le`, `abs_sibling_bestResponseValue_sub_le`, and `abs_sibling_terminalOutcomeMass_sub_le` give exact common-prefix bounds; `FinFourActualZenoDeletedSurvivalSource.FullyScreenedCoalescingClearingFamily.semanticLaw_coalescence` packages coordinatewise convergence of prescribed payoffs, unrestricted behavioral caps, and every complete terminal-law coordinate. The same branch's clearing family produces source-attached concentrated packets after at most four genuinely paid clears. The common resolution is `rho * gamma / (128 * R)`; premark atoms have mass above `gamma / (64 * R)`, and `eta <= 1/8`. `FullyScreenedClearingPacketResult.consumerResult` applies the existing strategic-singleton-or-collision-minimum compiler. The exhaustive contraction has `M`, `L`, and `A` in both arms; only the screened clearing arm has `C`, and both consumer outputs remain open. The host endpoint is not asserted whole-profile near-minimal, cross-cap coherent, or cap controlled in the other coordinates. The explicit `H_i = n^-3` zero-minimum regression is not checked. There is no return, regeneration, renewable compression, recursive descent, terminal approximation, or uniform-equilibrium conclusion. |
| Canonical maximal-prefix ray return or strict stall (Research-only) | `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`, `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`, and `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean` | The cap-indexed `quittingMaximalAbsorptionCapRoot` generates one tail-independent semantic orbit for every pure coalition of cardinality at least two. `quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card` gives its exact static semantic pair, while `FinFourOwnerCompressedMinimumReturnForcedPairPacket.rayBaseOutcomeLaw_eq_pure` gives the complete pure terminal law. Debt coordinates, normalized positive-debt support, shifted marked mass, and copied-prefix payer gain have one common survival factor. `QuittingMaximalCapSemanticPrefixRayStall.weightedAbsorption_hasSum`, `QuittingMaximalCapSemanticPrefixRayStall.absorption_tsum_le_exact_debtDrop`, `QuittingMaximalCapSemanticPrefixRayStall.absorptionTailSum_tendsto_zero`, and `QuittingMaximalCapSemanticPrefixRayStall.absorptionTailSup_tendsto_zero` give the exact weighted telescope, unweighted budget, and vanishing future canonical charge. For every strictly increasing convergent joint-law subsequence, `quittingMaximalCapSemanticPrefixLawPoint_cluster_facts` gives the same cluster debt `L`, sharp retained pair mass `L / D_0`, exact all-Continue Nash, and the unique-all-Continue-or-positive-absorption support-entry alternative. `FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_maximalPrefixRayMinimumReturn_or_stall` constructs the actual source-facing dichotomy: `L = D_*` builds the reprojection packet and reaches the existing transfer/limit-chord consumer; `L > D_*` stores that exact sharp retained-law object. Both arms have `M`, `L`, and `A`; only the equality arm has `C`. The strict stall is confined to the unchanged canonical ray: it gives no support descent, changed-endpoint recomputation, source regeneration, recursive return, uniform-equilibrium payoff, or completion. |
| Positive-minimum exact-prefix clock escape (Research-only) | `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashFixedTailPrefixRay.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FixedTailCapNashPrefixClockEscape.lean`, `MathUE/ProbabilityMassFunction/OptionNatEscape.lean`, `UniformEquilibrium/Quitting/Paths/ReversePrefixStoppingLaw.lean`, and `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayClockEscape.lean` | The generic fixed-tail layer constructs coherent exact cap--Nash reverse prefixes and proves debt-product identities, while the reverse-prefix stopping-law layer proves finite-head escape, late finite mass, and general-total-variation separation. `FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_finFourMaximalPrefixRayClockEscape` applies those results to a supplied strict maximal-prefix ray: every fixed marginal head vanishes, both retained pair members have zero `Never` mass and late finite mass tending to one, their stopping laws stay asymptotically at general total variation one from every fixed law, and no cofinal subsequence converges in that metric. The shifted pair atom has limiting mass `L / D_0`, is positive and at most one, and is at least `D_* / D_0`. The generic layers have `M` and `L`; the Fin4 adapter is conditional Research and assumes a supplied minimum producer, forced-pair packet, and strict-stall arm. It supplies no unconditional Fin4 source `A`, no downstream `C`, no target-law convergence, no compactness obstruction in weaker topology, no terminal approximation, and no uniform-equilibrium conclusion. |
| Strict canonical-ray forward tail flow and eventual-stall normal form (Research-only) | `MathUE/Analysis/SummableTailAverage.lean`, `UniformEquilibrium/Quitting/Root/FirstOrderProductFlow.lean`, `Research/Quitting/ForwardExactCapTailFlow.lean`, `Research/Quitting/ForwardExactCapTailFirstOrder.lean`, `Research/Quitting/FinFourProducerAtlas/StrictRayTailNormalizedCapFlow.lean`, `Research/Quitting/FinFourProducerAtlas/StrictRayPositiveRootReturn.lean`, `Research/Quitting/FinFourProducerAtlas/EventualAllContinueStallNormalForm.lean`, and `Research/Quitting/FinFourEventualAllContinueLocalRegression.lean` | `FinFourOwnerCompressedMinimumReturnForcedPairPacket.eventualAllContinue_or_nonempty_strictRayForwardExactCapTail` refines the actual strict-ray stall. A zero selected maximal root gives a literally fixed semantic orbit and the unique exact all-Continue root at that cap; otherwise it produces an actual positive-hazard `QuittingForwardExactCapTail` with the same packet source, selected pairs, and selected roots. In the zero-root arm, `FinFourMaximalRayEventualAllContinue.fixedProfile_semantic_eq` retains one actual finite-clock profile at the fixed semantic state, `exists_fixedProfile_capAttainer` attains every unrestricted behavioral cap at Never or one finite pure quitting date, and `fixedProfile_debt_eq_rayLimit` identifies its debt with `L`. `fixedProfile_endpoint_debt_eq_sub_add_spectatorLeakage` is the exact endpoint ledger; `rayPaidGain_sub_fixedExcess_le_spectatorLeakage` and `not_spectatorLeakage_lt_rayPaidGain_sub_fixedExcess` show that global minimality gives only the lower bound opposite to strict descent. `endpoint_debt_eq_minimum_of_spectatorLeakage_le` returns the endpoint to the minimum fibre only under the supplied missing upper threshold. In the positive-hazard arm, `QuittingForwardExactCapTail.tailAverage_renewal` and `eventually_currentHazard_supported_binding` give the exact renewal and eventual binding-support laws. The exact first-order product estimates feed `QuittingForwardExactCapTail.tailNormalizedCapFlow`, while `FinFourStrictRayForwardExactCapTail.analysis` supplies the nested analysis without an extra error hypothesis. These source-matched declarations have `M`, `L`, and `A` relative to the already selected actual branch. A supplied positive exact root at the limiting cap now has branch-local `C`: `FinFourStrictRayCapLimitJointLaw.nonempty` selects the same-ray law cluster, and `nonempty_minimumLawHandoff_or_offMinimumDescent` regenerates a same-residual minimum source or retains debt strictly between `D_*` and `L`. The strict descent has no renewable consumer, and no theorem forces the positive-root branch. Separately, `FinFourEventualAllContinueLocalRegression.pair_semantic_eq`, `exactRoot_eq_allContinue`, and `maximalPrefixOrbit_pairSemantic_eq` implement the packet's exact rational local table and immediate semantic stall. `residualHardClass`, `normal`, and `singletonPacket_support_eq_univ` prove its witness-independent hard fields; `neverPair_globalMinimum` and `neverUniformEquilibriumPayoff` prove global debt minimum zero and an all-Never uniform payoff. This explicit regression has `M`, `L`, `A`, and `C` for its own zero-minimum table, but it is not a positive-minimum strict-ray source. No theorem supplies the spectator upper bound, renewable rank decrease, strict-ray contradiction, or general uniform-equilibrium completion. |
| Full-binding compact and pointwise-support ballistic reduction (Research-only) | `Research/Quitting/FinFourProducerAtlas/StrictRayFullBindingDiffuseReduction.lean` and `Research/Quitting/FinFourProducerAtlas/FullBindingPointwiseSupportBallistic.lean` | `QuittingForwardExactCapTail.nonempty_compactHazardCluster` jointly extracts, on one strict subsequence of the same actual forward ray, the current hazard direction, remaining-tail hazard barycenter, and renewal ratio. `FinFourMinimumAtomProducer.not_hasHomogeneous_fullNormalizedSoloMatrix` transports the hard residual through the literal full-core reindexing. Given `flow.forward.bindingFinset = Finset.univ`, `nonempty_compactCluster_ratioLimit_pos_or_currentSupport_card_le_three` returns one same-flow positive-ratio or at-most-three-support cluster. More sharply, `compactCluster_ratioLimit_pos_of_eventually_all_currentHazard_pos` applies exact finite complementarity before taking limits: eventual positivity of every finite current coordinate along any compact cluster forces its ratio limit positive even if its limiting current direction lies on the simplex boundary. `eventually_renewalRatio_ge_pos_of_fullBinding_of_eventually_all_currentHazard_pos` upgrades eventual finite full support to one eventual positive renewal-ratio floor on the same ray, and `eventually_renewalRatio_ge_pos_or_exists_frequently_currentHazard_eq_zero` gives the literal source-level dispatch to uniformly ballistic renewal or one fixed player absent infinitely often. This conditional full-binding reduction has `M`, `L`, and `A` relative to the actual source-retaining flow, but no `C`. It does not produce full binding or eventual full support, consume the ballistic or omitted-player branches, give a return or rank drop, contradict the strict ray, or imply a uniform-equilibrium payoff. |
| Ballistic normalized omega chain, balanced occupation, and selected-chain no-go (Research-only) | `MathUE/Topology/SourceOmegaChain.lean`, `MathUE/Topology/CompactOrbitOccupation.lean`, `Research/Quitting/FinFourProducerAtlas/BallisticNormalizedOmegaChain.lean`, `Research/Quitting/FinFourProducerAtlas/BallisticNormalizedOccupation.lean`, and `Research/Quitting/BallisticNormalizedSelectedChainRegression.lean` | `Math.Topology.nonempty_sourceOmegaChain` extracts one bi-infinite path from a one-sided compact source with a common strict center subsequence; `SourceOmegaChain.sourceFiniteWindow_tendsto` retains literal consecutive finite source windows. From a source-attached strict Fin4 flow with full limiting binding and eventual positive current hazards, `nonempty_ballisticNormalizedOmegaChain_of_fullBinding_of_eventually_all_currentHazard_pos` constructs this chain on the same actual ray. `source_current_tendsto`, `source_tail_tendsto`, `source_ratio_tendsto`, `renewal`, `work_nonpos`, and `current_work_eq_zero` expose exact source dates, renewal, collision feasibility, and complementarity. `FinFourBallisticNormalizedOmegaChain.nonempty_normalizedOccupation` produces an empirical edge limit whose `marginals_eq` and `support_subset_ballisticEdgeGraph` give a balanced probability flow on the closed normalized relation. The actual chain has `M`, `L`, and `A` under its explicit full-binding/eventual-support hypotheses, but no `C`. Separately, `BallisticNormalizedSelectedChainRegression.stateAt_edge`, `stateAt_current_ge_one_eighth`, and `stateAt_not_periodic` give an exact full-support aperiodic orbit with ratio `1/2`; `fixedState_edge` exhibits a fixed point in the same relation, and the `soloMatrix_...` declarations retain the full paired-singleton hard class. That regression has `M` and `L` only: it is not an actual quitting ray, positive-minimum source, absolute product-root/payoff/Bellman realization, or terminal consumer. |
| Zero-minimum maximal-ray regressions and exact equilibrium consumers (Research-only) | `Research/Quitting/MaximalRayZeroMinimumActiveRegression.lean` and `Research/Quitting/FinFourMaximalRayZeroMinimumRegressions.lean` | The rational and fixed-real Fin4 tables construct actual canonical maximum-absorption prefix rays from a literal forced-pair profile. `LocalForcedPairFragment.pairStageMass_eq_one`, `postDateSpines_eq`, and `distinctPayer_pairDebt_pos` retain full marked mass, the complete common behavioral tail, zero marked debt, and a distinct positive payer debt. `Regression.pair_zero_eq_fragment` and `root_zero_eq_fragment` attach that exact fragment to the first semantic pair and selected maximal root. `rationalCardThree` has binding cardinality three; `fullBindingBallistic` has full limiting binding, three-player current support, and renewal ratio tending to `1 / 2`. The selected roots tend to all Continue, while `Regression.limitRoot` is a separate positive exact root at the limiting cap. These are actual zero-minimum regressions (`M/L/A`) with checked no-go and equilibrium consumers (`C`): `Regression.neverPair_globalMinimum` and `not_nonempty_minimumAtomProducer` expose the zero global debt floor, `Regression.neverUniformEquilibriumPayoff` gives the all-Never zero payoff, and the two `...PureSingleton_uniformEquilibriumPayoff` declarations give concrete all-behavior singleton equilibria. They do not attach to a positive-minimum source or contradict the strict ray in the conjecture regime. |
| Certificate-free strict-ray binding-cardinality reduction (Research-only) | `MathUE/PMFProduct/Reindex.lean`, `MathUE/PMFProduct/Bool.lean`, `UniformEquilibrium/Quitting/Root/PlayerReindex.lean`, `UniformEquilibrium/Quitting/Punishment/SingletonCapBindingCollision.lean`, `Research/Quitting/Root/EndpointNashBoxComplementarity.lean`, `Research/Quitting/BindingCollisionGainPositivity.lean`, `Research/Topology/BoxComplementarityFaceLocalCountTwo.lean`, `Research/Topology/BoxComplementarityFaceLocalCountZero.lean`, `Research/Topology/BoxComplementaritySpernerEventualLocalParity.lean`, `Research/Quitting/FinFourProducerAtlas/StrictRayBindingCardinalityExplicit.lean`, and `Research/Quitting/FinFourProducerAtlas/StrictRayPositiveRootReturn.lean` | `quittingEndpointNashBoxBridge` constructs the canonical Boolean-PMF box bridge at every finite cap, and `QuittingEndpointNashBoxBridge.isSolution_iff_isZeroQuittingRootNash` identifies its solutions with exact product-root Nash. Under limiting all-Continue uniqueness on one actual `FinFourStrictRayForwardExactCapTail`, `bindingFinset_card_ne_two` internally selects the late cap and common resolution, normalizes the binding pair, uses selected-root maximality and cap convergence to localize every exact root, derives the outsider and collision signs, and combines the both-active count-two and solo count-zero formulas with eventual same-grid parity one. No `ModTwoBoxComplementarityParitySpec`, finite-cap certificate, or GameTheory Sperner substitute is supplied. `positiveAbsorptionExactRoot_at_capLimit_or_bindingFinset_eq_univ_or_card_eq_three` first returns a positive limiting root when uniqueness fails and otherwise applies that exclusion, giving the unconditional actual-flow trichotomy. `minimumLawHandoff_or_offMinimumDescent_or_ballistic_or_omitted_or_cardThree` consumes the positive-root arm into minimum regeneration or strict off-minimum descent and the full-binding arm into ballistic renewal or a frequently omitted player. This has `M`, `L`, `A`, and branch-local `C`. The returned minimum/descent, ballistic, omitted-player, and cardinal-three endpoints remain open; no strict-ray contradiction or uniform-equilibrium payoff follows. The older abstract parity declarations remain checked conditional interfaces but are no longer inputs to this consumer. |
| Cubical-Sperner box-complementarity approximation, local counts, and discrete prism seam (Research-only) | `MathUE/Topology/BoxComplementarityCubicalSperner.lean`, `MathUE/Topology/BoxComplementaritySpernerApproximation.lean`, `MathUE/Topology/BoxComplementaritySpernerLocalCount.lean`, and `MathUE/Topology/BoxComplementaritySpernerSubdivisionPrism.lean` | `boxComplementarity_completeSimplex_card_odd` specializes the pinned strong cubical Sperner theorem to the reduced complementarity labeling. `BoxComplementarityProblem.isSolution_of_completeSimplexAnchorPoint_tendsto` turns every convergent sequence of complete-simplex anchors on a vanishing mesh into a box-complementarity solution, including dimension zero. The local-count layer proves global parity one, exact finite-mesh excision, and eventual clearing of compact isolating frontier collars. `KuhnPrismSpatialBoundaryLabeling.leftEndParity_eq_rightEndParity` constructs the same-resolution cell/face incidence and lateral cancellation; `boxComplementarityDiscretePrism_endpointParity_eq` identifies its ends with the actual pinned endpoint simplex counts. `kuhnStarSubdivision_completeFacetParity_eq` proves mod-two preservation for one elementary stellar subdivision directly from deletion-face pairing. This seam has `M` and `L`, but no geometric finite stellar chain connecting two pinned Kuhn resolutions, local-anchor/collar transport through such a chain, eventual local-parity stability, regularity bridge, `ModTwoBoxComplementarityParitySpec`, finite-cap Fin4 certificate, `A`, or `C`. |
| Canonical pair renewable minimum-endpoint support descent (Research-only) | `Research/Quitting/StoppingLawMinimumEndpointSupportRankHandoff.lean`, `Research/Quitting/MinimumFiberDebtTransfer.lean`, `Research/Quitting/FinFourProducerAtlas/CanonicalPairMinimumEndpointSupportRankHandoff.lean`, `Research/Quitting/FinFourProducerAtlas/CanonicalPairEndpointSourceRegeneration.lean`, `Research/Quitting/FinFourProducerAtlas/CanonicalPairFullReplacementSourceRegeneration.lean`, `Research/Quitting/FinFourProducerAtlas/RenewableSourceTrace.lean`, `Research/Quitting/FinFourProducerAtlas/CanonicalPairRenewableSourceRank.lean`, and `Research/Quitting/FinFourProducerAtlas/CanonicalPairMinimumEndpointRenewal.lean` | The actual canonical minimum-endpoint handoff is no longer only a one-use support comparison. `nonempty_endpointSourceRegeneration` rebuilds a complete source from the literal endpoint profiles and dates. Every minimum-fibre full-replacement child is rebuilt from its own literal profile sequence with the same hard residual, and `terminalExit_or_nonempty_supportDescent` recursively returns positive total slope, flat support entry, or an off-minimum paid first-disagreement endpoint. `canonicalPairRenewableRank` is exactly zero on the residual state, one plus positive-debt-support cardinality on tangent nodes, and six on the nonrecurring incoming state; `canonicalPairRenewableTransitionRel_wellFounded`, `descentCount_le_three`, and `exists_renewalTerminalExit_sameResidual` make well-foundedness, the Fin4 three-descent bound, and residual preservation literal. The initial handoff and every recursive edge expose a positive one-third nonmover debt increase. `not_hasVanishingHorizontalDeviationLeak_of_minimumFiber` proves that no one vanishing error can compare every nonmover behavioral deviation gain across the literal replacement seam. This source-attached structural reduction has `M`, `L`, `A`, and branch-local `C`; the three residual exits remain open. It supplies no backward response compiler, terminal approximation, unconditional uniform-equilibrium payoff, or branch-global completion, and the debt no-go alone says nothing about separate closeness of prescribed payoffs or raw cap vectors. |
| Strict canonical endpoint normalization (Research-only) | `Research/Quitting/FinFourProducerAtlas/StrictEndpointNormalizedReturn.lean` | `FinFourCanonicalPaidEndpointRows.exists_origin_refining` compactifies direct fixed-action endpoint rows on a further strict subsequence. For an actual canonical debt-ascent branch, `CanonicalPairMinimumEndpointDebtAscent.nonempty_strictEndpointOrigin` starts with the already aligned endpoint packet, records the literal composed depth map, and uses uniqueness of semantic limits to identify the decorated whole limit with that exact generic endpoint cluster. `CanonicalPairMinimumEndpointDebtAscent.nonempty_strictNormalizedReturnOrInert` applies normalized-passport minimization to this coherent origin. Its equality arm produces the existing source-attached strategic-singleton or collision-minimum residual; its strict arm retains the unique-all-Continue inert point. `FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_canonicalPairSupportHandoff_or_strictNormalized_or_rayStall` is the coherent source-facing handoff/normalized-endpoint/stall trichotomy. The reduction has `M`, `L`, and `A`; `C` applies to the normalized equality arm's maintained residual, while the support-handoff arm now feeds the renewable finite-rank reduction recorded above. The normalized inert point and ray stall have no `C`, and no arm supplies global completion, terminal approximation, or an unconditional uniform-equilibrium payoff. |
| Normalized Fin4 minimum-pair response chord | `UniformEquilibrium/Diagnostics/Quitting/PureCoalitionOneDateNeverAdapters.lean` and `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FinFourOrientedMinimumPairChord.lean` | The thin one-date layer delegates complete unrestricted behavioral caps and debts to the canonical pure sure-exit-set theory while exposing literal Never deletion and immediate-Quit insertion updates. From supplied normalized data consisting of a positive global-minimum pure pair, its two distinct outsiders, and a strict incoming triple-to-pair dropout gain, `terminalDispatch_nonempty` returns a profitable pair-member singleton response, a strictly off-minimum unique-outsider join, or a same-minimum unique-outsider join. In the equality arm, `pairToJoinedTripleChord_debt_eq` and `pairToJoinedTripleChord_debtSum_eq` give the coordinatewise affine debt formula and constant total debt for every legal stopping-law weight. `quitNowResponse_from_pairToJoinedTripleChord_gain_eq` states the literal updated-profile gain `(1 - lambda) * D_*`; the midpoint corollary gives `D_*/2`. This supplied-data compiler has `M` and `L`, but no actual-source `A` and no downstream or renewable `C`. It constructs no positive-time source, marked row, tail screen, ancestry, chronology, renewal, Nash path, terminal equilibrium, or uniform-equilibrium payoff. |
| Pure nonsingleton common-prefix tail screening | `UniformEquilibrium/Quitting/Paths/PureNonsingletonCommonPrefixScreening.lean` and `Research/Quitting/FinFourProducerAtlas/PureNonsingletonCommonPrefixScreening.lean` | `quittingTerminalSemanticPair_literalRootStack_pureSet_screen` proves that arbitrary behavioral tails behind one unchanged pure coalition of cardinality at least two and one unchanged literal root word have exactly the same prescribed payoff and unrestricted behavioral cap. Its named projection and debt corollaries give coordinate and total-debt equality and literal zero differences. For the actual Fin4 maximal-prefix packet, `rayTailReplacementProfile_semantic_eq_orbit`, `rayTailReplacementProfile_wholeDebt_tendsto_rayLimit`, `rayTailReplacementBaseProfile_outcomeMass_eq_pointMass`, and `rayTailReplacementProfile_outcomeMass_eq_actual` retain the fixed source, word, index, pair, debt limit, Dirac base law, and full outer outcome law. The three `not_exists_positive...rayTailReplacement` declarations consume this data only as a no-go for changing the tail strictly behind that same word and pure pair. This has `M` and `L` generically, `A` for the Fin4 packet, and `C` only for that negative architecture screen. It does not eliminate the strict ray, compare different words, change or screen a marked root, cover non-pure rows, cross a seam, produce a return or regeneration, or imply a uniform-equilibrium payoff. |
| Fin4 pure nonsingleton collision screening (Research-only) | `Research/Quitting/PureNonsingletonCollisionScreening.lean`, `Research/Quitting/FinFourPureNonsingletonCollisionScreening.lean`, `Research/Quitting/FinFourProducerAtlas/PureNonsingletonCollisionScreening.lean`, and `Research/Quitting/SameStageEndpointMonodromyImpossible.lean` | `quittingTerminalSemanticDebtSum_pureNonsingletonRow_eq_totalDefect` identifies unrestricted behavioral debt at every pure nonsingleton row with the sum of its literal root-coordinate defects, with no continuation or low-tail hypothesis. `quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint` follows at most three strict best-endpoint edges to an actual pair and then one mass-preserving Continue route to a literal singleton. `FinFourPureNonsingletonScreenedEndpoint.edge_gain_floor_live`, `edge_mover_debt`, `targetStageMass_eq_liveMass`, and `targetProfile_eq_of_time_ne` expose the exact `L * D_* / 4` paid floor, exact mover-debt subtraction, exact final mass, and complete off-date behavioral-profile preservation. For an actual nonsingleton minimum atom, `FinFourPureNonsingletonStrongConcentratedPacket.canonical_edge_gain_floor` states the literal `mu^2 * D_* / 32` floor and `FinFourMinimumAtomProducer.nonempty_strongConcentratedPacketConsumption_of_nonsingleton` reaches the existing source-attached strong-packet consumer without a tail split, near-minimum selected row, or self-tail closure. The older self-tail route remains available for its stronger restarted-continuation provenance. The initial pure overwrite and final pair-to-singleton route are not claimed profitable or cap--Nash, and the consumer's collision-minimum arm remains open. This contraction has `M`, `L`, `A`, and `C` only through that unchanged consumer. |
| Fin4 deletion near-cap collision producer (Research-only) | `MathUE/FinitePaidCollision.lean`, `Research/Quitting/FinFourDeletionNearCap.lean`, and `Research/Quitting/FinFourDeletionCollisionExpansion.lean` | `exists_finFour_deletionNearCapData` and `exists_finFour_deletionNearCapPaidCollision` construct a literal quiet deletion lift, finite near-cap update, and paid nonsingleton atom from a terminal gap and `Pi_j < gamma`; `finFourDeletionNearCap_collisionDispatch_distinct_with_bounds` adds the live-weighted tail/endpoint disjunction, exact `1/14` tail and `1/56` endpoint scales, `q != j`, exact mover-debt subtraction, and retained routed mass. `finFourDeletionNearCap_tailFormula_six` exposes the tail bound explicitly, while `Math.FinitePaidCollision` supplies the game-independent seven-term and scale algebra. No recipient-debt increase, chronology, return, regeneration, or uniform-payoff consumer is claimed; these game-semantic modules remain Research-only. |
| Tight-face restriction on paid near-returns | `UniformEquilibrium/Quitting/Chronology/TightFaceCollisionEscape.lean`, `UniformEquilibrium/Diagnostics/Quitting/TightFaceCollisionSemanticDebt.lean`, `UniformEquilibrium/Diagnostics/Quitting/Chronology/TightFacePaidNearReturnRestriction.lean` | A positive-charge payoff near-return must leave the separated local payoff face, activate a Quit owner outside it, or contain a nonperturbative collision row. One terminal-semantic source lift makes aggregate collision pay a monotone total-debt drop and excludes positive collision on the minimum-debt fiber. These are necessary restrictions on the missing paid-row producer, not a construction of a near-return family. |
| Fin4 strict minimum fibre and exact-basin restart moats | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`, `UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRigidity.lean`, `UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRestartMoat.lean`, and `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberRestartMoat.lean` | `exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff` gives one open unique-all-Continue tube over the compact global-minimum carrier fibre. `exists_finFour_minimumFiber_uniformRestartMoat_of_no_uniformPayoff` turns it into one terminal-seam floor for every positively absorbing exact block starting at an actual minimum-fibre value. Generically, `summable_hazardCharge_of_summable_restartSeams` makes aggregate block hazard summable from summable restart seams; `moat_div_two_mul_bound_le_hazardCharge` is the literal `rho / (2 * M)` floor. For a supplied canonical exact spine, `finFour_noUniformPayoff_constantAllContinue_or_limit_uniformlySeparated` derives marginal-hazard summability from no uniform payoff and returns the constant all-Continue spine or a convergent limit uniformly separated from the whole minimum fibre. The minimum-fibre selector and consumers are checked, but no theorem constructs the exact spine, rules out either limit arm, or proves a uniform-equilibrium payoff. |
| Fin4 prescribed-owner and pair-base reset boundary | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourPrescribedOwnerResetAlignment.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PrescribedOwnerStationaryHandoff.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseStationaryDebtLocalization.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetAlignment.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetPayoffAlignment.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalLawErasureDeviation.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFixedLawCapRigidity.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetCapRigidity.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointEdge.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseFloorViolationRepair.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointSeam.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointOrbitEscape.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFixedLawMinimumTargetStall.lean` | The pair-base construction co-realizes on one actual profile and law zero debt for a prescribed outside owner, unit incidence from the sure-Quit base, and a terminal-gap paid row whose debtor lies in that base. The general erasure estimate proves that a sure-quitting base of size at least two minimizes unrestricted behavioral caps on its complete-law fibre; when the complement is solved, it is the unique total-debt minimizer there. Consequently `returned_eq_of_fixedLawResetDispatch` identifies the complete returned reset pair, including every cap coordinate, with the literal stationary target. The strict dynamic arm is now literally a positive-absorption prefix at that target with smaller debt and a changed complete law; the other arm is the all-Continue fixed face. At the aligned payoff there is also an exhaustive base-floor-violation or exact endpoint-edge boundary. A base-floor violation gives a later-receiving paid row and zero-debt repair of that coordinate, without preserving other Nash data. A floor-safe endpoint is positive unless singleton domination gives the literal all-Continue self-loop; in a counterexample every positive edge is uniformly payoff-separated from all later reachable states. The reset cap root is literal Nash exactly under the checked surcharge-equals-live-debt identity; positive survival rules out the simpler killed-debt condition. The changed-law child is not renewable or returned, the all-Continue arm remains open, and `QuittingFixedLawResetAdmissibleClosureSeam` remains only a conditional uniform-payoff consumer whose return field cannot hold for a positive edge under the witness. |
| Fin4 prescribed-pair paid-cap semantic dispatch | `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidCapSemanticDispatch.lean` | `nonempty_finFourPairBasePaidCapSemanticDispatch` sends a terminal-exploitability witness and any prescribed two-player base to a stationary paid source on that same base, a positive global semantic minimum, and the summable cap port lifted from the same literal paid row. `FinFourQuantitativeFullSupportHardResidual.nonempty_pairBasePaidCapSemanticDispatch` exposes the same-table hard-residual adapter, while `uniformPayoff_or_exists_pairBasePaidCapSemanticDispatch` needs no hard-residual or reward-bound input. Only the reward table and pair label are prescribed: the minimum, stationary profile, paid row, and cap chronology are freshly selected. This is not an atlas source/trace adapter or a consumer of atlas monodromy, and it supplies no restart, cumulative-charge near-return, or uniform-payoff consumer for the port. |
| Fin4 singleton-base same-law reset and double cap port | `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SingletonBaseSameLawResetProducer.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SingletonBaseResetRepairPaidChain.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SingletonBaseResetRepairPaidCapDoublePort.lean` | `nonempty_singletonBaseSameLawResetProducer` works for every prescribed singleton owner in the quantitative hard residual. One actual stationary pair and law carry all three solved free coordinates, the unique full-gap paid debtor, a strict-superset atom of mass at least `Gamma/[7(Gamma+2M)]`, and a same-law fixed reset dispatch. The literal owner repair supplies a second paid row at a distinct observer. `nonempty_paidCapDoublePort` cap-lifts both profiles from the same positive minimum, and `sourceDescent_or_repairedDescent_or_doubleInert` leaves quantitative descent on one port or two lossless inert stalls. The descent alternatives may coexist; no descent regeneration or equality of the inert laws is proved. |
| Punishment-completed cycles | `UniformEquilibrium/Quitting/Punishment/CompletedCycle.lean` | Coupled phase-switch caps, exact instant-punishment characterization, and exact absorbing cycles completed coordinatewise by contraction or credible punishment. |
| Truncated-ledger boundary | `UniformEquilibrium/Quitting/Debt/Ledger/TruncatedLedgerCapBoundary.lean` | The sound package compiler interface together with one- and two-player counterexamples to treating it as a universal normal form. |
| Generated-secant chronological debt | `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`, `UniformEquilibrium/Quitting/Debt/Dynamic/ExactChronologicalData.lean` | The game-independent two-discount identity gives the sharp `C + 2A` shadowing bound, and its quitting adapter compiles bounded executable data with controlled prescribed and direct-debt forcing, vanishing joint and deleted-player survival, and small initial debt into a terminal `4 * eta` equilibrium. `QuittingChronologicalDebtShadowingCertificate.terminalExploitabilityGap_le` bounds every terminal gap by `4 * eta`, and `quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors` turns certificates at every positive accuracy into one uniform-equilibrium payoff. `exactOfRoots` supplies exact zero-forcing bookkeeping for any root schedule, but it copies the schedule's actual exploitability into the candidate debt and is not a small-debt producer. |
| Summable artificial seams, budget-stable iteration, and the bare-interface drain diagnostic | `MathUE/SublinearCostSchedule.lean`, `MathUE/SequenceVariation.lean`, `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalSeamReduction.lean`, `UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean`, `UniformEquilibrium/Quitting/Debt/Dynamic/MarkedInternalDebtDrain.lean`, `UniformEquilibrium/Diagnostics/Quitting/BudgetStablePacketInterfaceVacuity.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticImplementationBarrier.lean`, and `UniformEquilibrium/Diagnostics/Quitting/PositiveMinimumSeedSeamBarrier.lean` | Exact variable-length artificial Bellman blocks with summable prescribed/cap seams flatten canonically to chronological debt-shadowing data on unchanged literal roots. `exists_summableSeamSource_of_seed` selects the infinite compatible chain when seam plus availability loss is operationally sublinear, two fixed actual labels gain a positive fraction of every scale, and one globally bounded small-debt seed is supplied. The bare structure is not a source producer: `nonempty_quittingBudgetStablePacketSystem_iff_two_le_card` proves that it is inhabited for every reward table exactly when the player type has at least two elements. `quittingTerminalDebtSumInf_le_of_seedImplementation` gives the all-behavior payoff/cap implementation barrier. For a separately supplied source-attached marked chain, `tendsto_sum_positiveInternalDebtDrain_atTop`, `frequently_positiveInternalDebtDrain_ge`, and `tendsto_sum_positiveRowCoordinateDebtDrop_atTop` force divergent cumulative internal exact-Bellman debt drain under divergent exposure and summable seams. This is a checked tool and vacuity diagnostic, not Fin4 or uniform-equilibrium progress: no actual positive-minimum source adapter constructs the required ports/marks, and no consumer turns internal debt drain into prescribed-payoff charge, admissible near-return, terminal approximants, or a uniform payoff. |
| Stopping-law conditioning and exposure | `MathUE/Probability/DiscreteHazardMixture.lean`, `MathUE/ProbabilityMassFunction/GeneralTotalVariation.lean`, `UniformEquilibrium/Quitting/Paths/StoppingLawExposure.lean` | Finite-cutoff conditioning of a two-component hazard mixture is the exact posterior convex mixture, with posterior difference, odds, and denominator-lower-bound estimates. The explicit source-survival `lambda²`, target-survival `1` example has posterior tending to one and rules out any source-independent linear bound in the prior weight. Arbitrary-PMF total variation controls bounded expectations; for quitting stopping laws it is bounded by the two ever-quit masses, so a profitable radial or nested-radial reset carries quantitative finite stopping mass. These are fresh-law estimates, not residual-port stability after conditioning. |
| Reverse-prefix stopping-clock escape | `MathUE/ProbabilityMassFunction/OptionNatEscape.lean`, `UniformEquilibrium/Quitting/Paths/StoppingLawFiniteTail.lean`, `UniformEquilibrium/Quitting/Root/LiteralRootStackSurvival.lean`, `UniformEquilibrium/Quitting/Paths/ReversePrefixStoppingLaw.lean` | `pmfGeneralTV_tendsto_one_sub_min_of_finiteCoordinates_tendsto_zero` identifies the exact total-variation limit of any `Option Nat` law family whose fixed finite atoms vanish and whose `Never` atom converges. For supplied product roots with absorption mass tending to zero and supplied behavioral tails whose selected player has zero `Never` mass, `quittingReversePrefix_finiteHead_tendsto_zero`, `quittingReversePrefix_lateFiniteMass_tendsto_one`, and `quittingReversePrefix_pmfGeneralTV_tendsto_one` prove that every fixed finite head vanishes, all mass escapes to later finite dates, and the marginal law tends to total-variation distance one from every fixed law. Literal root-stack prefixing is executable, and `quittingBehaviorStoppingLaw_none_literalRootStackProfile_eq` gives exact player-own survival transport. These M/L statements are adapters for supplied roots and tails only: no exact-prefix source, positive-debt ray, Fin4 pair, Nash property, source `A`, or downstream `C` is produced. |
| Fixed-tail cap-Nash prefix clock escape | `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashFixedTailPrefixRay.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FixedTailCapNashPrefixClockEscape.lean` | `exists_quittingFixedTailCapNashPrefixRay` constructs one coherent reverse-prefix sequence over every fixed executable tail, with each new root exact Nash against the unrestricted behavioral cap of the preceding prefix. Playerwise and total terminal debt scale by the exact joint Continue product. Under a separately supplied positive debt floor, that product has a positive limit and the new-root absorption masses vanish. A separately supplied positive finite tail atom then gives exact marginal `Never` transport, the exact total-variation limit in `pmfGeneralTV_tendsto_one_sub_min`, the quantitative late-finite floor in `RetainedStageAtom.eventually_debtRatio_mul_mass_le_lateFiniteMass`, and `RetainedStageAtom.no_cofinal_pmfGeneralTV_convergent_subsequence`. These are conditional M/L statements. They do not produce the debt floor or retained atom, make the fixed tail or prefixed profiles Nash, attach a conjecture-facing source `A`, supply a downstream `C`, specialize to Fin4, obstruct weak convergence, or prove a uniform-equilibrium result. |
| Finite-clock minimum purification and pure-time paid port | `UniformEquilibrium/Quitting/Paths/PureTimeDeadlineProfile.lean`, `UniformEquilibrium/Quitting/Paths/PureTimeDeadlineRank.lean`, `UniformEquilibrium/Diagnostics/Quitting/PureTimeMinimumPaidPort.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockCanonicalization.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockMinimumPurification.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockMinimumPaidPort.lean`, and `UniformEquilibrium/Diagnostics/Quitting/FinFourFiniteClockMinimumPaidPort.lean` | `finiteClock_canonicalized_deadlineBounded_and_semantic_eq` reconstructs a supplied finite-clock profile from its stopping laws, preserves the complete prescribed-payoff/unrestricted-cap semantic pair, and makes the common deadline literal. `finiteClockMinimum_exactCapPurification_or_pureTimeDescentPaidPort` then takes a supplied positive global minimum through at most `card ι` exact-cap pure-time replacements while recording every pre-exit point on the original debt fibre. A strict exit returns a deadline-bounded paid response row; otherwise the pure-time endpoint retains the literal replacement ancestry constructed by deadline descent and its paid response. `finFourFiniteClockMinimum_exactCapPurification_or_pureTimeDescentPaidPort` makes the four-step bound literal. These results have `M`, `L`, and branch-local `A` only for the supplied finite-clock minimum profile. They do not produce that profile or minimum, assert arbitrary-profile replacement ancestry, supply chronology or renewal, consume either paid port, or prove a uniform-equilibrium payoff; downstream `C` is absent. |
| Arbitrary-clock minimum purification and actual-reach paid port | `UniformEquilibrium/Quitting/Paths/StoppingLawBadMassSelection.lean`, `UniformEquilibrium/Quitting/Paths/BehaviorSupportedPureTimeReplacement.lean`, `UniformEquilibrium/Diagnostics/Quitting/PureTimeSemanticFiniteRange.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/ArbitraryClockMinimumPurification.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachPaidFirstDisagreement.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ArbitraryClockMinimumActualReachPaidPort.lean`, and `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourArbitraryClockMinimumActualReachPaidPort.lean` | `minimumRealizingSequence_purify_or_offMinimum` starts with an arbitrary behavioral realizing sequence for a compact global debt minimum. Supported non-worse pure-clock replacements and a finite terminal-outcome semantic code return either one canonical pure-clock minimum or a literal finite-replacement descendant strictly above the minimum. `minimumRealizingSequence_exists_offMinimumActualReachPaidPort` composes the canonical branch with pure-time minimum descent; at the resulting off-minimum target, `positiveDebt_exists_actualJointReach_paidRow_mem_support` selects a source-supported paid first-disagreement row with the literal `4M`, `8M`, and `32M²` survival floors. `exists_minimumRealizingSequence_offMinimumActualReachPaidPort_of_debtSumInf_pos` constructs the compact minimum and realizing sequence directly from positive terminal-debt infimum, and the Fin4 wrapper makes the debt `D*/4` and paid-gain `D*/16` floors literal. These declarations have `M`, `L`, and source `A` under the positive-infimum branch. They preserve finite unilateral-replacement ancestry but not nonmover caps, individual debts, the original paid row under later replacements, chronology, renewal, or a Nash--Bellman path. No paid-port consumer, uniform-equilibrium payoff, or downstream `C` is supplied. |
| Finite horizontal pure-time exact-response alternative | `MathUE/FiniteResponseCycleLedger.lean`, `UniformEquilibrium/Quitting/Paths/BoundedSupportedPureTimePurification.lean`, `UniformEquilibrium/Diagnostics/Quitting/PureTimeInheritedResponseAlphabet.lean`, `UniformEquilibrium/Diagnostics/Quitting/PureTimeSelectedExactResponseOrbit.lean`, `UniformEquilibrium/Diagnostics/Quitting/PureTimeExactResponseMinimumAlternative.lean`, `UniformEquilibrium/Diagnostics/Quitting/FinFourPureTimeExactResponseCycleExternality.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualSourcePureTimeResponseAlternative.lean`, and `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourActualSourcePureTimeResponseAlternative.lean` | Every pure-clock profile inherits an exact-response alphabet of size at most `card ι + 2`: its displayed clocks, `Never`, and date zero. An opaque deterministic selector iterates a maximal-debt exact response inside the resulting finite state space; the conclusions do not depend on how ties are resolved. Starting strictly above a positive global debt floor, `exists_minimumDebtEntrance_xor_offMinimumExactResponseCycle` returns exactly one of the first visit to that floor or a nontrivial closed segment whose whole pre-repeat prefix stays strictly above it; every edge gains at least `D*/card ι` and has a fresh paid first-disagreement row. Fin4 recurrence, the selected entrance time, the cycle endpoint, and the cycle period are bounded by `1296`, while `exists_nonmover_payoffFall_and_debtRise_ge_twelfth_finFour` extracts exact `D*/12` nonmover payoff-fall and debt-rise witnesses, which may be different. `exists_finFourActualSourcePureTimeResponseAlternative_of_debtSumInf_pos` attaches this exclusive bounded alternative to the actual positive-infimum paid port after at most four support-selected non-worsening pure-time replacements, retaining actual-source ancestry to every displayed orbit profile. This has `M` and `L`, source `A` from the direct positive-infimum wrapper, and branch-local `C` from the paid-port attachment. The response orbit is horizontal, not temporal; it preserves neither nonmover caps nor debts and supplies no chronology, renewal, Nash--Bellman path, consumer of the entrance/cycle alternative, or uniform-equilibrium payoff. |
| Zero-Never, zero-singleton behavioral-law product base | `MathUE/PMFProduct/SingletonRatioPairConcentration.lean`, `MathUE/PMFProduct/ProductCoalitionSupportCard.lean`, `UniformEquilibrium/Quitting/Root/ProductRootProbabilityBridge.lean`, and `UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean` | `exists_twoSureProductRoot_realizing_law_of_mem_terminalSemanticLawCarrier` turns a supplied joint semantic/law carrier point with zero Never and singleton coordinates into one exact product-root law with two fixed sure quitters and literal common-pair support. Under strict singleton margins, `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin` realizes the complete prescribed-payoff/unrestricted-cap pair and law both by root-then-Never and stationary repetition; under weak margins, `exists_twoSurePaddedProductRoot_realizing_jointCarrierPoint_of_margin` gives the one-row padded realization. The Fin4 support cardinality is literally `1`, `2`, or `4`. This has `M`, `L`, and branch-local `A` from the supplied joint carrier point. It does not produce a carrier minimum, compose with finite-clock purification, assert Nash or replacement ancestry, preserve fixed-calendar intervention laws, implement the superseded sure-core descent, consume the resulting finite profile, or prove a uniform-equilibrium payoff; `C` is absent. |
| Counterfactual stopping-law hierarchy | `UniformEquilibrium/Quitting/Root/TerminalOutcome.lean`, `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean` | `quittingCounterfactualReplacementDetermining_iff` gives the sharp unrestricted threshold: labelled pure-intervention states of order `k` are closed under every one-coordinate stopping-law replacement exactly when `card ι - 1 <= k`. `quittingBehaviorStoppingLaws_update` attaches the independent marginal tuple to an actual behavioral profile and identifies behavioral replacement with coordinate overwrite. Order-one state equality literally determines every current terminal observable and pure-time cap; `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws` and `quittingBehaviorDeviationPayoffCap_eq_pureTime` expose the actual one-player payoff mixture and exact pure-time deviation cap. The module does not identify its abstract joint outcome law with `quittingTerminalOutcomeMass`, construct a literal suffix, preserve equilibrium under replacement, or prove compactness. |
| Cap-switch full-chord and all-proper boundary | `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticCapSwitchFriction.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticCapSwitchFullChord.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticCapSwitchSourceTransfer.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticCapSwitchCompactLimit.lean`, `UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourCapSwitchAllProper.lean` | Normalized first-disagreement gaps have the sharp deleted-survival friction bound. `exists_quittingCapSwitchFullChordPaidRow_of_firstOrderRectangle` turns a supplied two-edge first-order rectangle with scale at most `C * lambda` into one literal source/full endpoint with paid gain `gamma / (4 * C)` and pair-deleted floor `gamma / (8 * M * C)`. Source reset-cube transfer and one common strict subsequence retain the corresponding pair-deleted `Never` product in a compact-law limit. In the fixed Fin4 regression, `tendsto_quittingCounterfactualPureTimeCapSquare_div_lambda_neg_one` gives the normalized cap-square limit `-1`, while `tendsto_uniformFixedResponseSquareBound_div_lambda_zero` gives uniform fixed-response little-o. The response mark tends to infinity, and every displayed opponent survives to that mark with exact probability one; the reconstructed-hazard finite-splice error tends to zero. These are `M`/`L` statements for supplied profiles, rectangles, cubes, or the fixed regression. They provide no positive-minimum source `A`, chronological edge, minimum-fibre return, ancestry-preserving paid-row consumer `C`, or uniform-equilibrium result. |
| Counterfactual suffix compactness no-go | `MathUE/Topology/UniformProbeCompactness.lean`, `UniformEquilibrium/Diagnostics/Quitting/CounterfactualSuffixCompactnessNoGo.lean` | `currentPayoffResponseLaw_zero_eq_one` gives a rational Fin4 pair of independent stopping families with identical payoff-vector response laws after every current one-player marginal replacement; the first-stopping pushforward forgets dates and the reward pushforward forgets coalition labels. `no_currentResponseQuotient_suffixTransition_payoffObservable` rules out simultaneously realizing the stated suffix transition and successor-payoff observation on a state encoded only by that response signature. The actual one-stage roots satisfy `spikeProbe_eq`, and `not_isSeqCompact_of_commonAllDepthSpikeState` plus `exists_no_finite_net_of_commonAllDepthSpikeState` rule out sequential compactness and one finite global net when every depth probe factors through one common metric modulus. Fixed-depth continuity, depth-dependent moduli, finite-program approximations, equilibrium preservation, and a quitting-game counterexample are not ruled out. |
| Literal opponent-Green debt account | `UniformEquilibrium/Quitting/Root/TerminalDebtGreenAccount.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPointwiseDefectGreenRegression.lean` | Actual terminal debt along a literal root sequence satisfies an exact one-step deleted-player-survival account and finite Green telescopes, including bounded-tail and paid-hazard forms. A four-player harmonic regression has vanishing joint survival, vanishing survival after deletion of any one player, and active coordinate defects tending to zero, while every active suffix retains terminal deviation debt at least `1/2`; deleting both active players leaves survival exactly one. Thus pointwise defect decay and the individual deleted-clock limits do not by themselves bound the Green sum or terminal debt. |
| Source-matched chronological boundary | `UniformEquilibrium/Quitting/Debt/Dynamic/NashBellmanChronologicalForcing.lean`, `UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`, `UniformEquilibrium/Quitting/Paths/PersistentTwoLabelCounterexample.lean`, `UniformEquilibrium/Diagnostics/Quitting/Chronology/SourceMatchedChronologicalData.lean`, and `UniformEquilibrium/Diagnostics/Quitting/Frozen/RadialPacketExposure.lean` | Exact Nash--Bellman spines make every prescribed-discrepancy, adverse-forcing, generated-secant, and initial-debt field identically zero. Persistent joint and every one-player-deleted survival are exactly reduced to two fixed labels with divergent marginal hazard; summable reprojection loss or fixed-fraction retention preserves the conclusion. `not_exists_persistentTwoLabelExactNashBellmanSpine` proves that no universal exact-spine two-label selector exists, even for two players. The surviving producer must therefore use the positive-minimum/source-matched hypotheses or return a solved-game certificate disjunctively. A fresh frozen packet with two positive marginals does not by itself provide persistence or source compatibility. |
| Summable exact Nash--Bellman punishment floor | `UniformEquilibrium/Quitting/Debt/Dynamic/PunishmentFloorViolation.lean` and `UniformEquilibrium/Quitting/Bellman/Finite/SummableExactNashBellmanPunishmentFloor.lean` | `successorValue_le_current_of_punishmentValue_violation` makes a violating coordinate nonincreasing across every supplied exact Nash--Bellman edge. `punishmentValue_le_of_normal_of_summable_exactNashBellmanTail` combines that propagation with the all-Continue boundary of an exact tail with any finite common reward/value bound and summable joint absorption: every normal player's value at every date is at least its behavioral punishment value. The canonical-spine theorem is a specialization, and the all-normal corollary applies coordinatewise. These declarations have `M` and `L`, with a conditional `C` for the supplied tail. They do not construct the tail, prove summability, attach dynamic-debt data, select a compact orbit, or provide a source `A` or a uniform-equilibrium payoff. |
| Normal unique-persistent exact-spine compiler | `UniformEquilibrium/Quitting/Classification/Existence/NormalUniquePersistentNashBellmanSpine.lean` and `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardNashBellmanSpine.lean` | `abs_value_sub_soloReward_le_of_bounded_bellman` gives the coordinatewise bound by twice the reward bound times the remaining owner-deleted clock charge; it needs bounded Bellman recursion but not stagewise Nash. `IsCanonicalExactQuittingNashBellmanSpine.isUniformEquilibriumPayoff_soloReward_of_persistent` adds exact root Nash and owner normality and consumes a persistent owner with summable opponent clock into the owner's singleton uniform payoff. `IsCanonicalExactQuittingNashBellmanSpine.isUniformEquilibriumPayoff_soloReward_of_uniquePersistent` replaces the opponent-clock hypothesis by summability of all other marginals. On the Fin4 quantitative full-support hard residual, `FinFourQuantitativeFullSupportHardResidual.all_marginalQuitHazards_summable` proves that every marginal of every supplied exact spine is summable; `all_marginalQuitHazards_summable_of_no_uniformPayoff` composes this directly with the hard-residual constructor. These declarations have `M` and `L` and a conditional consumer for the supplied spine; they do not provide an `A` selecting a unique-persistent branch, construct a canonical spine with prescribed clocks, or resolve the hard residual. |
| Unbounded finite exact-block hazard and summable-residual spine compiler | `MathUE/CompactFiniteChargedReturn.lean`, `UniformEquilibrium/Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`, `UniformEquilibrium/Quitting/Debt/Dynamic/SummableResidualNashBellmanSpine.lean`, `UniformEquilibrium/Quitting/Debt/Dynamic/SummableResidualPersistentClosure.lean`, `UniformEquilibrium/Quitting/Classification/Existence/AllNormalUnboundedExactBlockHazardCapacity.lean`, and `UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean` | `HasUnboundedFiniteExactNashBellmanHazardCapacity` is literal failure of a `BddAbove` uniform bound over positive-length exact Nash--Bellman blocks in a supplied carrier. Compact near-returns concatenate into `QuittingSummableResidualNashBellmanSpine` with arbitrarily small total Bellman-plus-Nash residual and at least one persistent marginal label. `QuittingSummableResidualNashBellmanSpine.exists_uniformEquilibriumPayoff_of_twoPersistent` consumes a single supplied spine with two persistent labels; if there is only one persistent label, `exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity_of_allNormal` uses all-player punishment normality to consume its summable opponent clock. In Fin4, `finFour_exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity` removes the normality hypothesis through the quantitative hard-residual alternative, and `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff` states the literal counterexample-side contrapositive. These are `M`, `L`, and a capacity-conditional `C`; there is no `A` producing unbounded capacity from AKRS or a source trace, no numerical bound in the bounded branch, and no conclusion that bounded exact-block capacity is source-trace capacity. |
| Full-box exact-predecessor capacity and renewal recharge | `MathUE/RenewedChargedPathPotentialRecharge.lean`, `UniformEquilibrium/Quitting/Bellman/Finite/FullBoxExactPredecessorAbsorptionBudget.lean`, and `UniformEquilibrium/Diagnostics/Quitting/FinFourFullBoxExactPredecessorCapacity.lean` | `QuittingFullBoxExactPredecessorPath.toFiniteExactNashBellmanBlock` reverses every supplied full-box charged path into chronological finite-block order while preserving its exact endpoints and edges. `quittingFullBoxExactPredecessor_hasFiniteBudget_of_boundedHazardCapacity` bounds its joint-absorption charge by the marginal-Quit hazard capacity of the same reversed roots, and the canonical budget-to-go is a bounded potential. A supplied `ChargedRelation.RenewedPathSequence` records literal horizontal renewal into the next vertical source; `card_mul_minimumCharge_sub_budget_le_sum_valueRecharge` gives the sharp finite-horizon linear recharge inequality. Under no Fin4 uniform payoff, the existing bounded exact-block capacity supplies the full-box budget and the specialized recharge bound. These declarations have `M` and `L`, and a conditional `C` for supplied renewal data. They do not produce a renewed sequence, cap response, horizontal admissible edge, literal source profile, or uniform-equilibrium payoff; the renewal source `A` is absent. |
| Cap-pump second-label reduction | `UniformEquilibrium/Quitting/Paths/CapPumpSecondPersistentLabel.lean`, `UniformEquilibrium/Quitting/Paths/CapPumpChronologicalAdapter.lean` | On one literal root chronology, divergent favorable drops of a bounded exact scalar cap recursion and summable reverse rises force a persistent opponent label. If the cap owner is persistent this gives the required pair; with a known persistent mover, unbounded excess after subtracting its hazard account forces a second label outside the mover/owner pair. The adapters fill the same-root survival fields and combine with an exact spine, but no theorem orients or produces the required cap pump from arbitrary atom/reset data. |
| Exact charged-packet amplification | `MathUE/ChargedPacketAmplification.lean`, `UniformEquilibrium/Quitting/Bellman/Finite/TerminalExploitabilityPacketAmplification.lean` | `exists_path_charge_gt_of_uniform_tube_packet` concatenates genuine source-matched finite relation paths available at every reachable tube state into paths of arbitrarily large charge. `QuittingTerminalExploitabilityWitness.false_of_uniform_reachable_packet_producer` then contradicts the canonical finite prefix-charge capacity. This is the final consumer of an exact packet producer: it does not lift a stopping-law tangent to a predecessor path, identify residual gain with relation charge, or prove persistent packet availability after the source changes. |
| Singleton-deficit visit budget | `Maths.Graph.ChargedRelation`, `UniformEquilibrium/Diagnostics/Quitting/Capacity/InfiniteOrbitConsequences.lean` | `ChargedRelation.Path.sourceVisitCount_mul_le_chargeSum` counts arbitrary re-entry into any charged source region. Its quitting adapter `QuittingTerminalExploitabilityWitness.admissiblePath_singletonDeficitVisitCount_le` gives one path-independent bound on visits to every fixed positive singleton-deficit region along every exact floor-admissible path, even when the deficit owner changes. `infiniteOrbit_singletonDeficits_tendsto_zero` forces every coherent exact orbit toward the singleton-dominating region coordinatewise. This is a counterexample-side restriction, not a source-matching producer for isolated reset edges. |
| Full admissible-cycle amplification | `UniformEquilibrium/Quitting/Bellman/Finite/PositiveAdmissibleCycle.lean`, `UniformEquilibrium/Quitting/Bellman/Finite/TerminalExploitabilityCycleExclusion.lean` | `quittingGame_exists_uniformPayoff_of_positive_admissible_cycle` iterates any positive closed path in the full punishment-floor admissible exact Nash--Bellman relation, decodes arbitrarily charged literal finite prefixes, and obtains a uniform-equilibrium payoff. `quittingGame_exists_uniformPayoff_of_positive_admissible_return` reduces this to one positive exact edge plus an exact admissible return. The terminal-exploitability adapter proves that every such cycle has zero charge under a positive terminal gap. These are exact return consumers; they do not construct an edge or return from stopping-law geometry. |
| Exact-prefix stack charge obstruction | `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Atom/ExactPrefixStackCharge.lean` | `QuittingStoppingLawAtomExactPrefixStackAccess.absorptionSum_tendsto_zero_of_twoActive` proves that the total literal one-row absorption charge of the increasingly long exact-prefix access stacks tends to zero whenever two distinct positive-debt owners are active. The stacks therefore cannot themselves produce unbounded prefix charge. This does not rule out appending a separate positive exact edge with an admissible return. |
| Finite linear charged capacity | `MathUE/FiniteLinearChargedCapacity.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/LinearChargedCapacity.lean` | `normalizedPositiveChargedCirculation_iff_unboundedFeasibleCharge` is the exact recession theorem for flat finite charged columns. `stoppingLawFlatTangent_chargedCirculation_xor_strictLyapunovWeight` adapts it to a regime-free flat stopping-law tangent family; in the no-circulation arm, `exists_stoppingLawFlatStrictWeight_capacityBound_of_noCirculation` supplies one positive weight and a universal orthant-feasible charge bound. These are numerical tangent-space statements, not semantic realization or executable chronology. |
| Minimal-floor charge-tangent dispatch | `UniformEquilibrium/Diagnostics/Quitting/Debt/ChargeTangentPacket.lean` | `QuittingChargeTangentData.uniformPayoff_or_minimalFloor_underfunded_or_active_funded` gives a witness-free three-way dispatch: a complementary singleton mixture already yields a uniform payoff, one coordinate crosses the negative of the smaller solo/punishment boundary gap, or a positive-mass owner has positive tangent. Under a terminal-exploitability witness, the first arm is removed by `chargeTangentData_minimalFloor_underfunded_or_active_funded` and its packaged-packet analogue. This sharpens the sign alternative but does not construct either residual consumer, an admissible return, or chronology. |
| Terminal-semantic splice noncompositionality | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCommonWitnessNoncompositionality.lean` | Two explicit profiles have the same complete terminal semantic pair and the same first-stage joint survival, but different player-zero-deleted survival. Prefixing the same collision continuation changes player zero's best-response envelope from `2` to `1 + s`. The semantic pair plus joint survival is therefore not a splice-compositional state descriptor; a labelled deleted clock is genuinely additional data. This is an explicit regression, not a classification of all sufficient state enlargements. |
| Positive-debt attained-image nonclosedness | `UniformEquilibrium/Diagnostics/Quitting/PositiveDebtTerminalSemanticNonattainment.lean` | `PositiveDebtTerminalSemanticNonattainment.attainable_inter_debt_ge_one_not_closed` gives a rational two-player table with executable semantic pairs of debt `1 + 1 / (n + 1)` converging to an unattained carrier point of debt one. `attainable_inter_clock_payoff_face` identifies the exact open face, and `OnePlayerTerminalSemanticMinimality.attainable_isClosed` proves two players are minimal for this phenomenon. The candidate-profile quantifier is unrestricted behavioral, but the table's global minimum debt is zero. This forbids carrier-to-profile attainment from pointwise positive debt alone; it does not touch the globally minimal `D = D_* > 0` frontier. |
| Random quitting payoff processes | `UniformEquilibrium/Quitting/PayoffProcess/All.lean` | Measurable approximate-Nash selection, conditional-expectation backward induction, dominated tail approximation, and exact finite-prefix/tail payoff accounting compile every integrably dominated almost-surely convergent quitting payoff process with unit solo exit and capped joint exit in the limit into an adapted `epsilon`-equilibrium for each positive `epsilon`. |
| Face circulations | `UniformEquilibrium/Quitting/Circulation/FaceCirculationAll.lean` | Certificate/orbit production, finite charged closing, compatible compact paths, and cumulative-budget marked-atom consumers. Use `UniformEquilibrium/Quitting/Circulation/MultiOwnerFaceCirculationFiniteClosing.lean` for finite closing and `UniformEquilibrium/Quitting/Circulation/KActiveMarkedAtomBudgetPathConsumer.lean` for the diffuse-clock compiler. |
| Boundary holonomy | `UniformEquilibrium/Quitting/Boundary/Holonomy/All.lean` | Source-retaining fixed-cutoff compactness together with residual, self-similar, tangent, and realized-coordinate analysis. |
| Simon Question 1 boundary | `MathUE/Topology/ExtendedOrbit.lean`, `MathUE/Topology/CompactEdgeBudgetedPrefixRelation.lean`, `MathUE/Topology/SimonViabilityQuestion.lean`, `MathUE/Topology/SimonViabilityBudgetCompiler.lean`, `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean` | The generic strict bounded-potential theorem `not_hasArbitrarilyLargeFiniteOrbitVariationWith_of_potential_bounds` rules out arbitrarily large finite-orbit variation, but the seven generic hypotheses alone supply neither a Simon `F_epsilon` certificate nor the restartability needed by `QuestionOneConclusion`. Independently, a positive restartable extension yields one compatible path satisfying a linearly diverging prefix budget; the adapter `QuestionOneHypotheses.conclusion_of_restartableEscape` is conditional on that extra input. This row scopes the missing-certificate claim to those seven hypotheses only. The direct quitting adapters from approximate equilibria to a uniform payoff and from the stationarily generated residual are recorded below. |
| Simon finite-cell Lyapunov soundness | `MathUE/Topology/CompactEdgeBudgetedPrefixRelation.lean` | `HasFiniteCellLyapunovCertificate.exists_globalPotential` turns exact finite-cell coverage, bounded local potentials, and all cell-pair edge inequalities into one global strict potential. `not_hasArbitrarilyLargeFiniteOrbitVariationWith_of_finiteCellCertificate` and `not_hasArbitrarilyLargeFiniteOrbitVariationWith_of_rationalPolyhedralCertificate` then rule out arbitrarily large finite variation. Rational affine functionals and rational weak halfspaces are represented exactly; coverage, bounds, descent, and certificate search remain supplied proof obligations. |
| Simon harmonic-variation account | `MathUE/MeanErgodic.lean`, `MathUE/Probability/HarmonicStateAccount.lean`, `MathUE/Probability/HarmonicVisitEpoch.lean`, `MathUE/Probability/FinitePathLawAdapter.lean` | `markovReturnPotential` constructs the canonical target-stopped return potential. `HarmonicReturnBoundCounterexample.not_supportwise_returnBound` refutes the pointwise support estimate on three states, `ConditionalReturnBoundCounterexample.not_homogeneousBackwardHarmonicRenewalPrinciple` refutes the one-visit averaged renewal bound on four states, and `SevenStateVisitEpochCounterexample.not_homogeneousBackwardHarmonicVisitEpochPrinciple` refutes the aggregate per-owner visit-epoch principle on seven states. The source-state decomposition and `finiteExpectedMarkovReturnVisitCharge_le_one` remain exact; `HasMarkovVisitEpochBound` is only a sufficient supplied interface. These counterexamples do not refute Simon's global finite-state cardinality bound, which now requires a coupled cross-state proof. `hasAdaptiveFiniteMarginals_of_cylinder` and `finiteExpectedENNVariation_spaceTime_eq_ofReal` check the cylinder-to-finite-history path-law bridge, while `infiniteExpectedENNVariation_le_of_finite` supplies generic finite-to-infinite monotone convergence. Raw absorption charge in the quitting packet/cycle route is a different quantity from Euclidean orbit variation. |
| Supplied Simon quitting correspondence | `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SuppliedCorrespondence.lean` | `QuittingSimonFiniteNearOrbitConditionAt` is equivalent to arbitrarily large finite variation on the production-semantic individually rational, near-feasible carrier. `HasQuittingSimonFiniteCellLyapunovCertificate` and `not_quittingSimonFiniteNearOrbitConditionAt_of_finiteCellCertificate` directly adapt exact finite-cell certificates; the combined `exists_terminalExploitabilityGap_of_suppliedSimonNecessity_of_finiteCellCertificate` capstone consumes that adapter. The necessity implication, a certificate, source extraction, and a chronological strategy are not proved. |
| Repaired-stress Simon obstruction | `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/RepairedStressCycleObstruction.lean` | `not_exists_stressSimonStrictPotential` embeds the repaired four-player stress circulation as a positive-cost cycle in the full production correspondence at every positive tolerance, excluding every global strict potential. `not_hasQuittingSimonFiniteCellLyapunovCertificate_stressWeight` excludes every positive-coefficient finite-cell certificate for this table, while `stressSimonHalfSubdivision_microCost` checks the rational four-edge tolerance-`1/2` regression. This rules out one candidate certificate source; it neither supplies a certificate for another table nor implies equilibrium nonexistence. |
| Simon survival crossing and reached-prefix compactification | `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SurvivalCrossingRepair.lean`, `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/FinitePrefixCompatibility.lean`, `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/ReachedPrefixCompactification.lean`, `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/LowSurvivalSourceAdapter.lean`, `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/ArbitraryNeverExtraction.lean` | Actual approximate equilibria yield support-purified rows with an explicit product-law modulus; any uniformly reached finite window can be recomputed into an exact Bellman prefix with a linear seam bound. Compactification yields a bounded support-Bellman spine or a literal low-survival source prefix. `QuittingPayoffTable.approximateEquilibriumExistence_iff_zeroNever` is the exact arbitrary-Never behavioral normalization used by AKRS. Under all-restart joint-survival decay, the compact spine becomes an actual pointwise well-supported absorbing sequence. On a low-survival source, the checked adapter performs first crossing, reached-Nash transfer, source-tail purification, shifted floor clipping, and repaired window landing. Low cumulative survival still supplies neither the uniform-rho positive-window hypotheses nor cofinal near-total rows, and compactification does not supply the spine's all-restart survival boundary. No global perfect sequence or finite orbit is claimed. |
| Approximate-equilibrium zero-solo/vanishing-Never fork | `UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumVanishingNeverAlternative.lean`, `UniformEquilibrium/Quitting/Paths/VanishingNashRootSequenceFamily.lean` | `singletonReward_le_nashError_div_never` gives the dimension-free positive-Never conditioning estimate. `isQuittingZeroSolo_or_nonempty_vanishingNashFamily` turns the existing infinite-horizon approximate-equilibrium interface into exact zero-solo or actual root sequences with Nash error and Never mass both tending to zero. `QuittingPayoffTable.stationary_or_vanishingNeverNashFamily` reads the first arm as literal S.1 after arbitrary-Never normalization. The second arm retains weighted reached-stage and positive-reach shifted-tail Nash bounds; it does not assert unweighted tail Nash, complete absorption, stagewise perfection, or path compactness. Approximate-equilibrium existence remains a hypothesis, not a finite-horizon Nash theorem. |
| Chronological marked-law absorption path | `MathUE/Probability/ClockGap.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/ChronologicalRootSequenceTail.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/ChronologicalMarkedRootSequenceLaw.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/ChronologicalMarkedRootSequenceJump.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/ChronologicalMarkedRootSequenceJumpLimit.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/ChronologicalMarkedRootSequenceCollision.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/ChronologicalMarkedRootSequenceSingletonDerivativeSupport.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/ClockGapConstantTotalComponents.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/FiniteRootSequenceCDFCut.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalLimit.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalJumpRootRealization.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalSingletonDerivativeSupport.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalJumpPerfection.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalSingletonLowerBound.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalPositiveSingletonRate.lean` | `QuittingFiniteRootSequenceAbsorption.chronologicalLaw_clockCoalitionEvent_real_eq_value` identifies the globally normalized stage--coalition law with the finite post-jump path, including literal clock, root, bounded post-stage tail, and discrete coalition marks. The decoded clock is bounded above by path total, clock gaps have constant total mass, every jump is realized by a product root, and every nonzero continuous right derivative is supported on a singleton. `ChronologicalLimit.isAbsorptionPath` therefore proves that exact conjunction for the same decoded path. The finite prefix/tail payoff identity and reached-stage Nash closure prove `ChronologicalLimit.jumpPerfect`, the exact jump-row component of sequential perfection. `ChronologicalLimit.nonempty_chronologicalPathTimeAdjacentCutLimit` constructs actual adjacent source cuts at every nonterminal path time, and `ChronologicalLimit.singletonReward_le_absorptionPathPayoff` proves the literal singleton lower bound there. At every actual nonterminal path time with positive singleton right derivative, `ChronologicalLimit.absorptionPathPayoff_le_singletonReward_of_pathRightDerivative_pos` proves the matching upper bound and `ChronologicalLimit.absorptionPathPayoff_eq_singletonReward_of_pathRightDerivative_pos` states the equality literally. `ChronologicalLimit.isSequentiallyPerfectAbsorptionPath` bundles these continuous-clock clauses with the checked jump rows for the same actual chronological path. The terminal and no-terminal branches feed the separate checked S.2 and S.3 consumers below, and their exhaustive dispatch is checked in `UniformEquilibrium/Quitting/Classification/Existence/ChronologicalAbsorptionPathTerminalDispatch.lean`. This path construction itself does not assert approximate-equilibrium existence or a uniform-equilibrium conclusion. |
| Chronological terminal-total-jump S.2 consumer | `UniformEquilibrium/Quitting/Classification/Existence/ChronologicalTerminalJumpInstantPunishment.lean` | `ChronologicalJumpStageLimit.stageContinueMass_tendsto_zero_of_pathTotal_eq_one` proves that the actual selected dominant rows have all-Continue mass tending to zero when a chronological path jump reaches total mass one. Reached-source Nash transfer, near-sure-to-sure perturbation, and the punishment adapter then give the literal branch S.2 in `ChronologicalLimit.instantPunishmentEquilibriumExistence_of_terminalPathJump`. This has `M`, `L`, and actual-source `A`/`C`, conditional on an explicitly supplied jump with `pathTotal = 1`. It does not prove that such a jump exists, perform the terminal/no-terminal case split, consume the S.3 branch, prove the table-level AKRS trichotomy, or imply a uniform-equilibrium payoff. |
| AKRS small-cell productization and no-terminal-jump S.3 decoder | `MathUE/PMFProduct/SmallCellProductization.lean`, `MathUE/Topology/OneSidedDiniFencing.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/AKRSPartition.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/AKRSPartitionSmallCell.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/AKRSPartitionDecoder.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/AKRSSequentialPerfectionDecoder.lean`, `UniformEquilibrium/Quitting/Classification/Existence/SequentiallyPerfectAbsorptionPathWellSupportedSequence.lean` | `exists_akrsSmallCellProductization` proves the corrected non-strict closed form of the AKRS small-cell productization with `M` and `L`. The journal prints a strict coordinate bound, which fails when the cell has zero absorption mass; the production theorem uses `≤`, while the Literature file states and refutes the strict form explicitly. The path modules partition a supplied absorption path, copy its large jumps, productize its small cells, and preserve singleton support. They use the exact cell parameter `1 / (resolution - 1)` and the published dimension-factor coordinate bound `2 ^ Fintype.card ι * parameter * pathCellAbsorption`; they do not assert the full weak-convergence conclusion of published Proposition 4.8. `exists_wellSupportedAbsorbingSequence_of_sequentiallyPerfectAbsorptionPath` consumes path-total boundedness, sequential perfection at zero, and no terminal total jump to produce the literal well-supported completely absorbing S.3 sequence. It has `M`, `L`, and the supplied-path `C`. `ChronologicalLimit.wellSupportedAbsorbingSequenceExistence_of_noTerminalTotalJump` is the `M`/`L`/`A`/`C` adapter for the actual chronological source, still conditional on its explicit no-terminal-jump hypothesis. Nothing here decides the terminal-jump alternative, supplies S.2, proves the full AKRS trichotomy, or implies a uniform-equilibrium payoff. |
| AKRS checked correction witnesses | `MathUE/LinearAlgebra/PrincipalMinorDiagonalPerturbation.lean`, `MathUE/PMFProduct/SmallCellProductization.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/PrincipalQViabilityCorrespondence.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/TerminalTotalJumpVacuity.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/WeakPathConvergence.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/EndpointUnboundedWeakLimitCounterexample.lean`, `UniformEquilibrium/Quitting/Classification/Existence/RowPerfectionClosed.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/SequentialPerfectionWeakLimit.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/ClockBoundarySourceApproximation.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/ContinuousClockLowerBoundWeakLimit.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/UnitBoundedBoundaryPayoffTransport.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/PositiveSingletonBoundaryCellEstimate.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/ContinuousClockActiveWeakLimit.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/JumpSubsequenceWeakLimit.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/PreviousBoundaryJumpLocalization.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/LimitJumpSourceLocalization.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/LimitJumpRootLocalization.lean`, `UniformEquilibrium/Quitting/Root/IncidentCoalitionOdds.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/BoundaryCellProductRootOdds.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/RationalCoordinateCompactness.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/SingletonDerivativeWeakLimit.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/CommonLimitJumpSubsequence.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/UnitBoundedSequentialCompactness.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/AKRSFiniteProfileDensity.lean`, and `UniformEquilibrium/Quitting/Classification/ErrorExponentRefutation.lean` | `det_add_smul_one_eq_sum_principalMinors` states the exact principal-minor expansion for a scalar diagonal perturbation, and `det_add_smul_one_pos_of_principalMinors_nonneg` gives its positive-determinant consequence. `akrsPrintedCollisionFactor_five_counterexample` checks the printed `1 / k` collision-factor failure at `k = 5`. `principalQViabilityControls_not_upperHemicontinuous` states the direct upper-hemicontinuity failure. `exists_sequentiallyZeroPerfectAbsorptionPath_with_terminalTotalJumpAtZero` gives, for every nonempty finite quitting game, a path with an immediate terminal total jump which is vacuously zero-perfect under the printed test. `localGlobalCounterexample_rowwiseZeroPerfect_but_terminalRegretOne` bundles exact rowwise perfection with unit unrestricted terminal regret. `HasUnitBoundedTotalMass` records the missing upper probability-mass invariant; its endpoint theorems give total and left-total mass one, coordinatewise left-continuity, and no jump at clock one. `exists_reward_not_closedUnderWeakLimits_without_totalMassUpperBound` gives a two-player endpoint-total-two witness refuting only the unrestricted current Lean closure predicate. The generic row-closedness declarations end in `quittingPlayerRowεPerfect_of_tendsto` and `quittingRowεPerfect_of_tendsto`. Supplied source realizations feed `playerJumpRowsPerfect_of_sourceApproximatedWeakLimit`; plain unit-bounded weak convergence supplies both continuous-clock clauses. The source-localization modules construct literal source jump boundaries and pass the normalized jump identity along a jump-dependent strict subsequence. This is sufficient for `unitBoundedPlayerSequentialPerfectionClosedUnderWeakLimits`, so the corrected full closure has `M`/`L` and source `A`/consumer `C`. `unitBoundedAbsorptionPathSequentialCompactness` separately constructs one common strict subsequence, a unit-bounded absorption-path limit, weak convergence at every continuity point, and convergent literal source realizations of every limit jump. `unitBoundedAbsorptionPaths_are_weakLimits_of_completelyAbsorbingRootSequences` proves the corrected unit-bounded density statement of AKRS Proposition 4.8 with `M`/`L`. `unitBoundedAbsorptionPathSequentialCompactness` proves the corrected unit-bounded compactness statement of Proposition 4.11 with `M`/`L`. These checked corrections do not repair the reverse S.3 implication in AKRS Theorem 3.4. |
| Chronological S.2/S.3 dispatch and AKRS Theorem 3.4 | `UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumVanishingNeverAlternative.lean`, `UniformEquilibrium/Quitting/Classification/Existence/ChronologicalAbsorptionPathTerminalDispatch.lean`, `UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumForwardTrichotomy.lean` | `ChronologicalLimit.instantPunishment_or_wellSupportedAbsorbingSequenceExistence` exhaustively sends every actual completed chronological source to literal S.2 or well-supported S.3. `QuittingPayoffTable.stationary_or_instantPunishment_or_sequentiallyPerfectAbsorbing` then proves the table-level forward implication in AKRS Theorem 3.4, including the empty-player stationary case. Its premise `ApproximateEquilibriumExistence` says that for every positive error there is an arbitrary behavior profile that is terminal-payoff approximate Nash against every unilateral behavioral replacement; the profile may vary with the error, and no fixed payoff target is quantified. The conclusion is one fixed disjunction S.1, S.2, or S.3. This has `M`, `L`, `A`, and `C`. It does not prove the approximate-equilibrium premise for every quitting game, require or imply one fixed uniform payoff target, control all sufficiently long finite horizons, or prove a uniform equilibrium. |
| AKRS reverse-S.3 null-tail boundary and restricted hardness | `UniformEquilibrium/Quitting/Classification/Existence/SequentiallyPerfectAbsorbingNullTailAlternative.lean`, `UniformEquilibrium/Quitting/Classification/Existence/ReverseSequentiallyPerfectAbsorbingHardness.lean` | `QuittingPayoffTable.solo_sub_never_le_of_completelyAbsorbing_not_everyRestart` proves that any nonterminating restarted tail of an initially absorbing row-perfect source forces each singleton payoff below Never plus the row error. `QuittingPayoffTable.allContinueExactNash_or_everyRestartWitnesses` gives the inclusive consequence: all Continue is exact terminal Nash, or every sufficiently accurate such witness terminates after every restart. The restricted predicate `HasStationaryExactEveryRestartRowPerfectSource` retains one fixed stationary exact source and its literal all-restart termination. `universalStationaryExactEveryRestartSource_iff_approximateExistence` proves that the universal implication from this restricted source to terminal approximate-equilibrium existence is equivalent to general finite-quitting terminal approximate-equilibrium existence. Its hard direction adds exactly one player, so it is not a same-cardinality equivalence. These results eliminate the null-tail subcase and show that even this restricted stationary-exact slice is universally hard; they neither prove nor refute the reverse implication of journal Theorem 3.4 for an unresolved table. |
| Compact continuation motion | `UniformEquilibrium/Quitting/Classification/CompactContinuationMotion.lean`, `UniformEquilibrium/Quitting/Classification/CompactFeasibleNeighborhood.lean`, and `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/NormalizedMotionStationaryPrefixProducer.lean` | `exists_compactContinuationMotion_of_not_branches` supplies one positive motion and Continue-mass lower bound for every support-rational row on a fixed compact continuation set, assuming failure of the instant-punishment and stationarily generated branches. `isCompact_quittingFeasibleClosedNeighborhood` supplies compact neighborhoods of the finite feasible payoff polytope. The compact-motion result transfers to literal `lemma2_1_part2_compact` in `Literature/Simon2012.lean` without unfinished imported proofs. These bounds do not construct feasible rows or establish the full finite-orbit theorem. |
| Simon positive-absorption splice | `UniformEquilibrium/Quitting/Classification/Existence/PositiveAbsorptionStationarySplice.lean`, `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedBranch.lean` | `quittingStationarilyGeneratedApproximateEquilibria_of_positiveAbsorptionStationary` and its every-error adapter turn a cofinal family of stationary approximate equilibria with positive one-stage absorption into the stationarily generated branch, while the resulting Nash inequalities quantify over arbitrary behavioral hazard sequences. The direct residual corollary `quittingApproximateEquilibriumExistence_of_stationarilyGenerated` and the direct adapter `quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence` consume these approximate profiles without a cycle classification. This is a checked producer under the stated cofinal hypothesis, not a proof that every stationary family has positive absorption. |
| Uniform payoff and diagonal terminal semantics | `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean` | `isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier` characterizes each fixed uniform-payoff target exactly as a diagonal point in the closure of executable terminal payoff/unrestricted-best-response pairs. `quittingApproximateEquilibriumExistence_iff_exists_diagonal_mem_terminalSemanticCarrier` gives the target-free existential form, and `QuittingPayoffTable.approximateEquilibriumExistence_iff_exists_diagonalCarrierPoint` gives the normalized arbitrary-Never AKRS premise. The carrier point need not be attained by one profile. These are semantic equivalences, not branch classifications or an existence proof for every game. |
| Simon equilibrium-to-positive-cycle assembly | `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/EquilibriumToPositiveCycle.lean` | Supplied exact charged forward packets in one compact carrier close through a single-seam projective lasso to positive cyclic `F_epsilon` orbits, and the periodic support-witness consumer yields a uniform-equilibrium payoff. Here `IsQuittingZeroSolo reward` means that every own singleton reward is nonpositive. The primary supplied hard-branch interface is the disjunction `IsQuittingZeroSolo reward ∨ QuittingSimonArbitrarilyChargedForwardPacketCondition reward`; the positive-cycle corollary assumes the zero-solo branch is absent. The equilibrium-to-packet necessity and seam exactification are substantive supplied obligations: audited approximate paths have not been turned into exact packets in one common carrier, and no arbitrary-game producer is claimed. Raw packet absorption charge is not Euclidean finite-orbit variation and does not automatically feed the Simon variation obstruction. |
| Simon zero-solo/generated/standard-Q trichotomy | `UniformEquilibrium/Quitting/Classification/LCP/ZeroSoloGeneratedStandardQ.lean` | `zeroSolo_or_stationarilyGenerated_or_standardQMatrixSide` proves the elementary three-way split from the production stationary gate: either every own singleton reward is nonpositive, or the stationarily generated residual, or standard-Q. Off zero solo, `hasArbitrarilyAccuratePositiveAbsorptionStationaryEquilibria_of_not_zeroSolo` supplies the positive-absorption cofinal family consumed by the splice theorem. `quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence` is the direct approximate-existence consumer. No normal-player, sign-pattern, or Literature lemma is used; the standard-Q side remains unresolved. |
| Projective Q-bar principal decoder | `UniformEquilibrium/Quitting/Classification/LCP/ProjectiveQBarBehavioralDecoder.lean` and `UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean` | `exists_punishmentNormal_singletonPath_of_projectiveQBar` supplies the continuous path on the punishment-normal principal matrix, and `ContinuousZeroPerfectSingletonPath.ambientLift` checks the omitted-player lift. The logarithmic Snell modules prove the rate calculus, deleted-clock fork, product-law discretization, finite-Quit/Never comparison, and fixed-target behavioral compiler. `quittingPunishmentNormalPathDecoder_of_snell` constructs the former decoder hypothesis, and `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` proves the ambient projective-Q-bar class has a uniform-equilibrium payoff. The result does not solve `ResidualHardClass`. |
| Corrected quitting classification boundary | `UniformEquilibrium/Quitting/Classification/Existence/PrioritizedRefinedSourceBoundary.lean`, `UniformEquilibrium/Quitting/Classification/Existence/PrioritizedAttachmentSingletonDefect.lean`, `UniformEquilibrium/Quitting/Classification/Existence/PrioritizedPreemptionSeedBoundary.lean`, `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedPriorityRegimes.lean`, `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedNegativeOwnerBoundary.lean`, `UniformEquilibrium/Quitting/Classification/Existence/DivergentExceptionalOwnerInstantPunishmentOrWellSupported.lean`, `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointEndpointSequentialReduction.lean`, `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointEndpointUniformPayoff.lean`, `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointExactPrefixOrbitDiagonal.lean`, `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointSummablePortPhantomReduction.lean`, `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointSourceMatchedSummablePortPhantom.lean`, `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointSummablePortBallisticDispatch.lean` | Arbitrary-Never approximate existence gives a fixed corrected branch or cofinally many prioritized residual scales. The attachment arm is consumed into explicit all-Continue-source or positive-singleton-defect packages retaining all four priority negations; every surviving scale forces a positive-period augmented solo-preemption cycle. Cofinal residuals retain scales tending to zero, one fixed positive owner/preemptor edge, and the actual source or defect at every scale. `QuittingCofinalPrioritizedSignedLassoBridge` states the exact still-missing semantic phase data; it compiles to S.3 and contradicts priority, but no producer constructs it from the static edge. Bounded exceptional horizons give S.2, while every divergent unique exceptional-owner source gives S.2 or well-supported S.3. The positive-joint summable arm retains a strict original-source subsequence, literal punishment suffixes, fixed punished label, semantic endpoint limit, no-sure-exit proof, exact-prefix port, phantom/value equality, and uniform-payoff certificate. These payoff identifications do not imply S.1, S.2, or S.3. Nonsummable absorption gives S.3; the ballistic dispatch closes positive charge plus endpoint return, while zero-charge rigidity or a displaced signed port remains. This older residual route is still locally incomplete, but the direct chronological theorem above proves Theorem 3.4 independently. |
| Normal sequentially perfect absorbing source compiler | `UniformEquilibrium/Quitting/Paths/SupportWitnessReduction.lean`, `UniformEquilibrium/Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`, and `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean` | `exists_normalSupportDelayedSwitch` selects a finite boundary after the first support-survival crossing. `exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing` and its well-supported equivalent then construct terminal approximate Nash profiles at every positive error, and `exists_uniformEquilibriumPayoff_of_all_normal_of_sequentiallyPerfectAbsorbing` selects one fixed uniform payoff. The Fin4 hard-residual wrappers obtain all-player punishment normality from the supplied residual. These results have `M` and `L`, source-conditional `A` from the supplied sequentially perfect or well-supported completely absorbing sequence, and conditional terminal/uniform-payoff `C`. The hard residual does not produce that sequence; no unconditional S.3, no no-uniform-payoff contradiction without a supplied source, no stationary equilibrium, and no general stochastic-game theorem are claimed. |
| Blocker-switch stationary class | `UniformEquilibrium/Quitting/Classification/Existence/BlockerSwitch.lean` | For an arbitrary baseline payoff, a weak blocker-switch upper condition yields a positive-hazard stationary certificate with value exactly at baseline; the strict refinement yields a fully mixed certificate. `isUniformEquilibriumPayoff_of_blockerSwitch` upgrades the certificate to an exact behavioral terminal Nash and uniform-equilibrium payoff. This is a special structured class, not a universal producer for finite quitting games. |
| Cycle-balanced signed influences | `UniformEquilibrium/Quitting/Stationary/SignedInfluenceBlock.lean`, `UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean` | A block-triangular signed-influence certificate produces a literal sure-exit coalition. More concretely, fixed positive, negative, or absent pair influences with positive sign product on every directed simple influence cycle yield such a certificate and hence an unrestricted-behavior uniform-equilibrium payoff. `exists_negativeSimpleInfluenceCycle_of_no_sureExitSet` gives the sharp remaining fixed-sign boundary. The theorem permits different polarity switches in different strongly connected components; it does not cover background-dependent influence signs. |
| Componentwise weighted-potential quitting tables | `MathUE/FiniteBinaryWeightedPotential.lean`, `UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean` | `BinaryAffineBlockWeightedCertificate.exists_isBinaryGainStable` solves finite affine binary games with triangular levels and positive within-block symmetrizing weights. The quitting adapter extracts SCC levels from the actual coefficient graph and constructs a literal sure-exit coalition. `exists_pureStationary_exactTerminalNash_of_componentwiseWeightedPotential` and `quittingGame_exists_uniformPayoff_of_componentwiseWeightedPotential` give exact terminal Nash against unrestricted behavioral deviations and a uniform-equilibrium payoff. The quadratic adapter covers SCC-wise symmetrizable active pair coefficients, including equal active coefficients and sign-frustrated reciprocal negative cycles; passive coefficients and cross-SCC influences are unrestricted. This is a sufficient chamber, not a universal producer or characterization. |
| Acyclic augmented solo preemption | `UniformEquilibrium/Quitting/Classification/Existence/AcyclicSoloPreemption.lean`, `UniformEquilibrium/Quitting/Classification/Existence/AcyclicSoloPreemptionRegression.lean` | `exactTerminalNash_or_soloEscape_of_acyclic_augmentedSoloPreemption` dispatches every acyclic augmented graph to exact all-Continue play or an explicit solo-owner family with maximum all-behavior terminal exploitability at most `q * quittingSoloPairPremium`, fixed singleton payoff, and zero pair-coalition mass. `exists_uniformEquilibriumPayoff_of_acyclic_augmentedSoloPreemption` gives the uniform-payoff consequence. The graph uses only singleton rows, own-singleton signs, and pair rows for the quantitative premium; rewards of coalitions with at least three quitters are unrestricted. Directed augmented cyclicity is necessary, not sufficient, for the independent-clock gadget route. |
| Participant-only stationary equilibrium and passive perturbation | `UniformEquilibrium/Quitting/Classification/Existence/ParticipantOnlyStationary.lean`, `UniformEquilibrium/Quitting/Classification/Existence/ParticipantOnlyPerturbation.lean` | `exists_stationary_uniformEquilibriumPayoff_of_participantOnly` constructs an exact stationary terminal Nash profile and uniform-equilibrium payoff for every finite quitting table whose absent-player reward coordinates vanish. `exists_stationary_isTwoPassiveMagnitudeAsymptoticNash` projects an arbitrary table to that class and gives terminal exploitability at most twice `quittingPassiveMagnitude`; `half_terminalExploitabilityGap_le_quittingPassiveMagnitude` forces passive magnitude at least half any universal terminal gap. These are arbitrary-table checked adapters and unrestricted-behavior consumers, but the projected profile need not be exact for the original table. |
| Six-player one-pair ledger, actual-profile clock, and target lock | `MathUE/Probability/CoalitionTargetMassLedger.lean`, `UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean`, `UniformEquilibrium/Diagnostics/Quitting/SixPlayerArbitraryProfileClockAdapter.lean` | `exactCoalitionMass_ge_of_targetCrossPenaltyCompletion` turns an explicit terminal `epsilon`-Nash premise and the literal target/cross-penalty completion predicate into a generic target-mass bound. The complete `Fin 6` integer table satisfies `integerReward_exploitability_ge`, forcing the exact `31/66` first-pair and leftover ledger, while bounded outsider completions retain the `17/8` estimate. `sqrt_firstPairMass_add_sqrt_secondPairMass_le_one` constructs the literal live-root clock and proves the sharp terminal square-root inequality for every behavioral profile; `integerReward_secondPairMass_le` is therefore unconditional. `robustCompletion_targetA_terminalNash_and_uniformPayoff` shows that every direct completion has a pure exact target equilibrium, so no positive second-pair mass is forced. |
| Single-anchor and persistent-base arbitrary-completion escapes | `UniformEquilibrium/Quitting/Stationary/SingleAnchorArbitraryCompletion.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingleAnchorArbitraryCompletionSixPlayer.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean` | One sure-Quit anchor plus an internally selected mixed Nash completion gives exact stationary terminal Nash against unrestricted behavioral deviations when its unconditional Quit value is nonnegative and dominates every anchor-excluding row. Literal anchor-membership reward makes the screen automatic while every other reward coordinate is unrestricted. For `Fin 6`, retaining either one first-target coordinate while altering the other five still yields a uniform payoff with exact second-target atom mass zero. The persistent-base theorem separately covers pointwise leave-safe bases of cardinality at least two. These eliminate the protected-coordinate completion architectures, but not tables altering both first-target coordinates. |
| Robust-join predecessor bases and strict background reversals | `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/RobustJoinPredecessorBase.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/RobustJoinStrictBackgroundReversal.lean` | `QuittingRobustPredecessorBase.complementLeaveSafe` turns a finite base with an incoming background-uniform robust join at every vertex into the checked persistent-base condition; the resulting stationary profile is exact terminal Nash against unrestricted behavioral deviations and supplies a uniform-equilibrium payoff. A supplied robust `PeriodicCycle` is a literal such base. On the counterexample side, the robust graph is a standard finite DAG, has a checked topological order, and every nonempty induced subgraph has a predecessor-free vertex. For any finite player type, `selectedCycle_has_strictBackgroundReversal_of_no_uniformPayoff` forces a selected positive cycle edge to reverse strictly on a nonempty disjoint background. On `Fin 4`, `finFour_exists_uniformPayoff_of_noStrictBackgroundReversal` internalizes the reward bound, hard residual, collision map, and cycle to solve the exact no-strict-reversal table class. This is a static table restriction outside the maintained positive-minimum chronology frontier, not a new frontier leaf or a proof of the full residual. |
| Strategically precompact watchdog boundary | `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdog.lean`, `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogEscape.lean`, `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogException.lean`, `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogBoundary.lean`, `MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`, `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean` | Strategically totally bounded reply families cannot force a fixed profile-dependent deviation gap; complete such families yield a uniform payoff. One arbitrary nonprecompact player range is still harmless, so a surviving selector needs two distinct identities with fixed late-finite mass beyond every horizon. Failure of proper strategic approximation additionally forces fixed late-or-Never mass, and in a strategically totally bounded family yields a nonproper essential Never witness separated from every proper behavior. The compact stopping-law and barycenter infrastructure is checked, but the proper-sentinel compact-game theorem still lacks joint weak continuity of terminal payoff; hence no theorem yet forces failure of proper approximation for every selector identity. |
| Literal strict finite odd interval-blocker cores | `UniformEquilibrium/Quitting/Stationary/HeterogeneousConstrainedFaceNash.lean`, `UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCore.lean`, `UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCoreRowAdapter.lean` | `isUniformEquilibriumPayoff_of_literalStrictFiniteOddIntervalBlockerCore` turns the exact literal row-extrema sandwich `L_i^+ < C_i^- <= C_i^+ < H_i^-` on an embedded odd cyclic core of any finite size at least three into an exact stationary all-behavior uniform-equilibrium payoff. Core continuation rows may vary within their separated band; the outside-player set and every outside-player reward coordinate are arbitrary. The constant-passive declarations in `UniformEquilibrium/Quitting/Classification/Existence/FiniteOddBlockerCoreRowAdapter.lean` remain a checked special case. Overlapping or weak bands and same-background signs without the global extrema sandwich are not covered. |
| Conditional face-gap stationary class | `UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean`, `UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGap.lean`, `UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`, `UniformEquilibrium/Diagnostics/Quitting/Regression/ConditionalFaceGapFivePlayer.lean` | The division-free face numerator is continuous on the full hazard cube and equals the opponent-absorption factor times the conditional face gap away from the zero denominator. On an arbitrary coordinatewise box, strict lower-face and weak upper-face signs (with no derangement assumption) yield a common zero; the exact behavioral terminal Nash and uniform-equilibrium capstone then follow. `exists_uniformEquilibriumPayoff_of_conditionalFaceGapRange` supplies a checked finite reward-range adapter with strict lower and weak upper comparisons. The five-player regression has an exact stationary uniform-equilibrium certificate but deliberately falsifies applicability of that coarse range adapter; its direct face signs are checked. This is a special source-data class, not a universal producer. |
| Integrated safe chambers, stationary face boxes, and owner-risky stationary closure | `UniformEquilibrium/Quitting/Classification/Existence/SureExitChambers.lean`, `UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`, `UniformEquilibrium/Quitting/Classification/Existence/RationalStationaryFaceBox.lean`, `MathUE/Interval/RationalPolynomialL1.lean`, `MathUE/Interval/PolynomialLipschitz.lean`, `UniformEquilibrium/Quitting/Classification/Existence/CenteredStationaryFaceCertificate.lean`, `UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyStationaryClosure.lean`, `UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskySureExitExclusion.lean`, `UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyPairDefect.lean`, `UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyCapLimitRootUniqueness.lean`, `UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourOwnerRiskyInducedOwnerMargin.lean`, `UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourOwnerRiskyStationaryDebt.lean`, and `UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourOwnerRiskyCheckedScreens.lean` | The chamber and face-box declarations compile supplied signs or certified box bounds to exact behavioral Nash and uniform-payoff results. `exists_fullSupport_sharpStationaryCertificate` gives a literal full-support stationary certificate for every `0 <= R <= 1/37`; `sharpReward_quittingTerminalDebtSumInf_eq_zero` projects it to zero global terminal-debt infimum. `isQuittingSureExitSet_sharpReward_iff`, `sharpPurePairDebt_eq`, `quittingInducedOwnerNeverExcess_sharpReward_eq`, and `existsUnique_isQuittingRootNash` expose the four direct screens. `checkedScreens` conjoins those facts. These results have `M/L`, with the stationary consumer supplying `C` for this family and no actual `A`. They do not identify a maximal cap ray or prove an open reward-table neighborhood. The Research aliases `rationalSingletonTwoChamber` and `fullBindingSingletonTwoChamber` refer to different zero-minimum tables. |
| Reward closure | `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean` | Fixed-skeleton quitting-game existence under uniform reward limits and dense solved approximants. |
| General nonexistence certificates | `UniformEquilibrium/Diagnostics/Uniform/NonexistenceCertificate.lean` | A uniform positive exploitability gap at arbitrarily late finite horizons rules out every uniform-equilibrium payoff. |
| Quitting terminal exploitability and minimum semantic debt | `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`, `UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean` | Terminal gaps and the equivalence between finite-quitting nonexistence and some fixed positive terminal gap. For inhabited finite player types, `exists_uniformEquilibriumPayoff_iff_hasZeroMinimumTerminalSemanticDebt` identifies existence exactly with zero attained minimum total semantic debt, while `not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt` identifies nonexistence with a positive attained minimum. |
| Full-core deadlock contraction | `UniformEquilibrium/Quitting/Classification/LCP/FullCore/All.lean` | For every completion of the displayed normalized singleton matrix, exact carrier dynamics give the upper bound `1227/96755` on every global debt floor and terminal exploitability gap. This arbitrary-completion result does not prove zero minimum debt or uniform-payoff existence. |
| Literal full-core deadlock joint block | `UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockJointBlockEquilibrium.lean` | For the specific completion `FullCoreDeadlock.reward` (all nonsingleton coalition rewards are zero), `reward_isUniformEquilibriumPayoff_jointBlock` proves an exact uniform-equilibrium payoff against arbitrary behavioral deviations. The certificate is a three-phase product block with singleton supports `{0}`, `{2}`, and a genuine double-quit support `{1, 3}`. This does not extend the equilibrium conclusion to arbitrary full-core completions; those retain only the `1227/96755` bound. |
| Rational polyhedral full-core deadlock slice | `UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockRationalPolyhedralBlock.lean`, `UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean` | `IsDeadlockRationalJointBlockCompletion reward s` describes an unbounded, nonlocal polyhedral slice with arbitrary baseline payoff `s` (including negative coordinates), the full-core singleton matrix, `reward({1,3}) = s`, and eight explicit collision-cap inequalities. Every member has the fixed target `deadlockRationalBlockValue s` via the same three-phase product block with supports `{0}`, `{2}`, and `{1,3}`. This is a sufficient slice, not a theorem for all full-core completions. |
| Integer-table full-core deadlock period-three block | `UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockIntegerTablePeriodThree.lean` | `integerTableTarget_isUniformEquilibriumPayoff` proves that the literal fifteen-row integer reward table has the fixed target `integerTableTarget` against arbitrary unilateral behavioral deviations. The exact three-phase block is certified through a rational Krawczyk contraction; its algebraic parameter is unique inside the displayed affine parallelotope. The theorem makes no global root-uniqueness or stationary-exclusion claim. |
| Overlapping-support period-three affine cylinder | `UniformEquilibrium/Quitting/Cycles/PeriodThreeClearedGap.lean`, `UniformEquilibrium/Quitting/Cycles/PeriodicRectangularFaceSign.lean`, and `UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreePositiveAffineCylinder.lean` | `overlappingPeriodThreeReward_has_block_and_uniformPayoff` proves an unrestricted-behavior uniform payoff for the displayed rational Fin4 table. `exists_overlappingPeriodThreeBlock_and_uniformPayoff_of_reward_distance` covers the full sixty-coordinate closed reward box of radius `1/50000000`. `exists_periodThreeClearedGapData_and_uniformPayoff_of_visible_affine_reward` permits four exact invisible coordinates to be arbitrary and applies independent positive scales and arbitrary shifts to every player's remaining reward column. The generic face-sign compiler and supplied rational-affine partition-sign lemmas expose the reusable open-chamber interface; they do not construct Bernstein coefficients or a periodic block for an arbitrary reward table. |
| Full-core deadlock reduced lassos | `UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockReducedSingletonLassoBarrier.lean` | Every finite reduced cyclic word of active ideal-singleton blocks for the displayed deadlock matrix has strictly positive debt at every phase. The proof includes the exact homogeneous complementarity obstruction. It gives no word-length-uniform positive floor and does not cover non-singleton chronology. |
| Singleton-tight minimum-face iteration | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonTightMinimumFaceIteration.lean` | Exact owner-prefix iteration on a singleton-tight minimum face, convergence to a carrier washout point, identification of the owner cap with the punishment value and of debt with the punishment gap, stationary-solo consequences, and the resulting atomic-handoff-or-deletion alternative. |
| Strict all-Continue linear absorption basin and carrier-source gate | `UniformEquilibrium/Quitting/Root/StrictAllContinueBasinLinearAbsorptionDefect.lean`, `UniformEquilibrium/Quitting/Paths/StrictAllContinueBasinSuccessorPath.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourCarrierSourceChargeDebtErrorGate.lean` | `exists_open_linearAbsorptionDefect_of_compact_strictAllContinue` gives one open neighborhood and positive modulus `c * absorption <= total root Nash defect` at every root scale around a compact, uniformly singleton-separated, unique-all-Continue source set. `exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff` supplies that source from the complete prescribed minimum-fiber projection of every hypothetical no-uniform `Fin 4` table. `successorPath_mem_and_absorptionSum_le_of_linearDefect` bounds total absorption and path diameter under a small aggregate row-error budget. `FinFourCarrierSourceChargeDebtErrorGate.debt_or_error` turns this into a fixed source alternative for paths beginning at an actual carrier payoff; its exact charged-relation consumer excludes minimum-fiber starts. These are path obstructions, not path producers or uniform-payoff consumers, and no theorem yet source-matches the off-minimum paid profiles to a near-return path. |
| Fin4 charged blocker gate and closure boundary | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourOffMinimumChargedBlockerGate.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ChargedSoloBlockerGateRepayment.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ChargedSoloBlockerClosureDispatch.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointEdge.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointOrbitEscape.lean` | `exists_macroscopicDebtDrop_or_chargedSoloBlockerGate` sends every fixed-charge exact carrier-root family to positive-liminf semantic debt descent or a source-retaining mixed solo debtor and maximizing punishment-normal blocker. The literal gate root has zero semantic-debt drop. A fixed pair premium enters an actual pair-base or leave--join stationary paid source; otherwise every anchored exact floor orbit repays a fixed amount in the blocker coordinate. The independent pair-base reset reaches the exact floor-violation/all-Continue/positive-edge boundary at the paid target payoff. The positive-edge arm cannot return even approximately in payoff under a terminal witness, and no all-coordinate payoff return is produced. |
| Fin4 solo-wall dispatch and pair-base handoff | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourSoloWallDispatch.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseStationaryTwoDebtorHandoff.lean` | `exists_strictCarrierDebtDescent_of_opponentAbsorptionFloor` and `exists_first_soloPrefix_outsiderWall` send a unique-debtor solo gate to strict carrier-debt descent or a first outsider wall. Finite-window compactification and punishment normality exclude indefinite uniformly interior solo continuation. The wall's pair premium gives a singleton-base handoff or full-gap outsider join, and `nonempty_finFourPairBaseStationaryTwoDebtorHandoff` consumes that join into an actual stationary source with quantitative off-base absorption, a heavy strict-superset atom, both free coordinates solved against unrestricted deviations, base-localized debt, and a literal paid row. The source is freshly selected rather than chronologically reached, and no payoff return follows. |
| Sorin uniform-payoff segment | `UniformEquilibrium/Examples/Sorin/UniformPayoffSegment.lean` | A weighted Blackwell--Ferguson account strategy, exact finite-law Bellman and energy identities, almost-sure absorption, all-horizon behavioral deviation bounds, and the unconditional inclusion `(a, 2(1-a))` for every `1/2 <= a <= 2/3`. |
| Frozen stopping-law reset cubes | `UniformEquilibrium/Diagnostics/Quitting/Frozen/ResetCube.lean`, `UniformEquilibrium/Diagnostics/Quitting/Frozen/RadialResetCube.lean`, `UniformEquilibrium/Diagnostics/Quitting/Frozen/RadialScaling.lean`, `UniformEquilibrium/Diagnostics/Quitting/Frozen/RadialPacketExposure.lean`, `UniformEquilibrium/Diagnostics/Quitting/Frozen/RadialCurvatureStrategicDispatch.lean`, `UniformEquilibrium/Diagnostics/Quitting/Frozen/BalancedResetPacket.lean` | A flat charged circulation yields legal radial weights and one variable-scale literal reset cube whose normalized frozen active star tends coordinatewise to zero while its normalized diagonal charge tends to a positive limit. Integer rounding gives uniform `O(1/N)` frozen-prefix control. Exact nested bilinearity gives a uniform `O(lambda²)` fixed-pure-time affine remainder, and the curvature dispatch localizes a negative cap square to an oriented strategic label. These are static frozen-source certificates and supply no chronological carrier path. |
| Frozen radial actual-profile packet | `UniformEquilibrium/Diagnostics/Quitting/Frozen/ActualProfilePacket.lean`, `UniformEquilibrium/Diagnostics/Quitting/Frozen/ConditionedActualProfilePacket.lean`, `UniformEquilibrium/Diagnostics/Quitting/Frozen/ConditionedRestartBarrier.lean`, `UniformEquilibrium/Diagnostics/Quitting/Frozen/KilledSourceStrategicBarrier.lean` | `exists_frozenRadialLiteralFiniteProfilePackets` constructs, on the flat charged-circulation branch, literal finite root words from the actual frozen radial profile. Two fixed active movers contribute at least a common positive multiple of the frontier scale; all internal candidates are actual reached terminal-semantic pairs with exact prefix provenance and one global payoff/debt bound. Exact posterior conditioning and sharp loss are checked. `exists_frozenRadialStrictPackets_available_or_exploitablySourceKilled` gives the exact late-rank dichotomy: a positive-radius two-label conditioned kernel, or an original source marginal with a sure-Quit row before the cutoff and a fixed positive deviation debt. This is not restartability. The killed-source branch needs a strategic dispatch or another source; the available branch still needs a later-rank source/replacement identification, and label alignment and the external small-debt anchor remain open. |
| Four-player quantitative full-support hard residual | `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardPrincipalSize.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardPrincipalDispatch.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictToggleLargeBasePaidChain.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBasePaidEndpointExactStack.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/LeaveJoinStationaryTwoDebtorHandoff.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/TwoCycleLassoHardPairAlignment.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/ThreeCycleLassoHardPrincipalIncidence.lean`, `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FourCycleHardPrincipalAlignment.lean` | `uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual` proves that every bounded `Fin 4` reward table either has a uniform-equilibrium payoff or retains, on the same table, the quantitative full-support packet, full normal core, all-player punishment normality, terminal witness, and `ResidualHardClass`; projective Q-bar is therefore retired. The failing proper principal has size two or three and `hardPrincipalDispatch` gives the exact pair/helper or three-principal alternatives. Every singleton now has a distinct full-terminal-gap collider. In the rooted-two owner-leave arm, the collision either retains a full-gap enlarged-pair outsider join or yields a third-label leave--join chain; the latter has an actual stationary source with a quantitative pair/triple atom, two solved floor-safe coordinates, debt on at most two labels, and a literal paid row. The strict-toggle large-base arm enters a two-plus-two paid chain and a unique-debtor stationary source. `endpointAtom_floorFailure_or_exactOrbit` now gives localized floor failure or a literal exact infinite floor orbit; its finite prefixes enter the collision budget, and charged payoff recurrence has a uniform-payoff consumer. Under a terminal witness every fixed charge is eventually absent, so no payoff near-return follows. The two-, three-, and four-cycle incidence theorems cover all seventeen marked constructors, while the selected toggle and preemption cycles remain unrelated. |
| Fused four-player residual | `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/Preemption.lean`, `UniformEquilibrium/Diagnostics/Quitting/FourPlayerReturnedBlockGap.lean`, `UniformEquilibrium/Diagnostics/Quitting/Chronology/StrictCovectorDynamicTail.lean`, `Research/Quitting/FourPlayerCounterexampleFusion.lean` | Positive packet atoms are punishment-normal; `exists_normal_packetPair_not_mutuallyPreempting` selects a reciprocal-positive pair that cannot mutually preempt at the terminal gap. Full four-player normal core gives `hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample` for every bounded ambient returned block. `exists_strictCovectorPositiveSurvivalTail` supplies a canonical positive-debt tail with summable absorption and eventual positive suffix survival. The Research synthesis records these with the collision/preemption/LCP restrictions. No theorem identifies the packet, minimum semantic pair, and tail, or constructs low-error returned blocks from them. |
| Positive-debt tangent cycles | `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/OffDiagonal/PositiveDebtTangentCycle.lean` | A flat stopping-law tangent with no zero-debt support entry contains a periodic cycle of positive transfers among active debt owners, and every edge is realized as a positive frozen common-source cube edge. This is profile-derived tangent data, not an executable chronological cycle. |
| Observer-absent stopping-law dispatch | `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/ObserverAbsent/ForcedOwnerDispatch.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/ObserverAbsent/FiniteClockDispatch.lean` | A fixed observer-absent rectangle label supplies a finite forced-owner wall; finite-clock polarity and face-loss alternatives retain the literal carrier and terminal data. |
| Positive-total-slope full-replacement cluster | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeAtom.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PositiveTotalSlopeFullReplacement.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PositiveTotalSlopeAtomAccess.lean` | A supplied positive-total-slope mover has a literal source-relative full-replacement debt excursion, a legal mover gain converging to its entire base debt, and a compact full-replacement cluster whose mover debt is zero. `exists_offDiagonal_tangent_ge_average` selects an observer with tangent entry at least the average of total slope plus the entire mover debt over the other players. Its common pure-time response has vanishing endpoint debt, and its existing atom-interface charge is `7/16` of that entry. The same mover, observer, charge, and source rank are retained through arbitrarily long exact-prefix stacks. The full-replacement cluster is counterfactual, not a reached continuation; no anchored return, Bellman rebase, or contradiction follows. |
| Exact-diagonal stopping-law endpoint clusters | `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawVanishingRegretTangentExtraction.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/MinimumFiberSupportDrop.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvatureStrategicDispatch.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean` | Vanishing-regret replacement selection upgrades every maintained tangent family to exact tangent diagonal and zero limiting full-replacement mover debt. `QuittingPositiveMinimumDebtTangentFamily.reducedSupportRankAlternative` re-extracts at same-minimum endpoint clusters and proves finite termination in positive slope, support entry, or an off-minimum paid row. Flat charged circulation is not a fourth terminal exit: in either flat no-entry branch, an arbitrary active mover's literal endpoint retains a strict subset of the old positive-debt support (hence lowers rank) or enters the paid-row arm. The curvature adapter retains both approximate pure-time witnesses and dispatches every sufficiently late row to its legal owner/outsider temporal orientation under the terminal-gap error budget. It does not re-enter that local deviation into a reset family, exact return, or executable chronology. |
| Finite-quitting uniform-existence boundary | `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`, `UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean` | `reducedSupportRankAlternative_of_positiveMinimumDebt` connects the compact positive-minimum obstruction to the reduced three-exit alternative. `exists_uniformEquilibriumPayoff_of_reducedSupportRankExitConsumers` needs chronological consumers only for positive slope and support entry, plus one all-behavior paid-row consumer; no circulation consumer remains. `QuittingPositiveMinimumDebtTangentFamily.nonempty_vanishingDebtAtomAccess` proves that every extracted tangent family already has a fixed vanishing-debt atom alternative, independently of its exit tag; `QuittingPositiveMinimumDebtTangentFamily.exists_vanishingDebtAtomAccess_of_supportEntry` retains the actual zero-debt support-entry recipient. `vanishingDebtAtomChronologicalConsumer_iff_exists_uniformEquilibriumPayoff` proves that the all-frontier chronological consumer is exactly a conjecture-level reformulation, not an independently weaker producer. Budget-stable compatible iteration is checked after concrete local packets, a sublinear seam/radius modulus, fixed labels, and an explicit small-debt seed. The positive-minimum source cannot itself be that seed; a separate external source/payoff-to-candidate adapter or solved-game disjunct remains open. The paid route now asks only for a fixed lower bound on total path charge with varying endpoint payoff near-returns, or a source-matched restart/debt descent at the labelled summable all-Continue port; a fixed charged edge and exact admissible return are stronger specializations. |
| Equivariant security--welfare assembly | `UniformEquilibrium/Quitting/Classification/EquivariantSecurityWelfareAssembly.lean` | Phase-equivariant security at one representative transports to every player at every phase, pins each phase target below that player's punishment value, and combines with a positive weighted phase-welfare cap to produce a uniform-equilibrium payoff. A terminal row above the punishment-priced target total refutes the corresponding welfare cap. |
| Collision-anchored preemption geometry | `UniformEquilibrium/Diagnostics/Quitting/Collision/PreemptionGeometry.lean` | On at most four players, one collision owner roots one of six simple strict-preemption lassos and the collider occupies one of seventeen canonical positions. Every marked position is realizable with an explicit normalized gate matrix; every cycle vertex lies in the normal core. See [`PREEMPTION_GEOMETRY.md`](PREEMPTION_GEOMETRY.md). |
| Aligned collision and preemption | `UniformEquilibrium/Quitting/Boundary/Repair/AlignedPreemptionCollision.lean` | In the sequential two-solo screen, the follower's exact immediate-Quit gain is the owner's rate times the collision gain; the preemption inequality does not enter. Every repair mechanism fails under a terminal exploitability witness. When the collider's punishment value is at most its solo payoff, blocker balance is automatic, leaving owner endpoint failure or a profitable spectator join. The universal aligned two-cycle realization has a uniform-equilibrium payoff. |
| Coupled Bellman--collision reduction | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCoupledBellmanCollisionReduction.lean` | Persistent mass on one fixed pair, vanishing defects of both pair members, and return to the minimum-debt fiber force one fixed third player to have a uniformly positive legal reached-row gain along a strict subsequence. Without the return hypothesis, the exact alternative is nonvanishing shifted-tail excess or that third-player gain. |
| Terminal semantic joint-reset lift | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticJointResetLift.lean` | A finite left-regular band of coupled reset modes, its exact `FinDist` semiconjugacy with semantic prefixing, and debt, payoff-spine, and cap-retention observables. The invariant reset hull need not have positive debt. |
| Quitting terminal exploitability localization | `UniformEquilibrium/Diagnostics/Quitting/Collision/BoundedSelfResetLocalization.lean` | For every starting-profile sequence in a terminal exploitability witness, a pure-time self-reset chain of length at most `card(I)+1` yields either an observer-absent forced-owner wall or an observer-containing reached-row gain. The certificate records a fixed terminal and explicit positive mass/gain floors. No converse is claimed from the branch data. |
| Positive-target reached rows and literal no-go | `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/OffDiagonal/PureTimeReachedRowLocalization.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiteralSourceReturnNoGo.lean` | Every positive observer-containing target yields a strict subsequence and an explicit uniform positive lower bound for one fixed non-observer's legal reached-row gain. `positiveTargetReachedRowLocalization_no_exactNashBellmanEmbedding` packages the resulting actual rows with their literal Nash--Bellman embedding obstruction; it does not produce a packet-preserving return or a uniform-payoff compiler. |
| Fixed-law rectangle reset-face minimization | `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleResetFaceMinimizer.lean` | The rectangle endpoint adapter retains a complete comparison law, a fixed-law reset-face dispatch, its minimizer bridge, and the literal law-premium consumer. `exists_fixedLawResetDispatch` is a checked conditional interface: the returned point preserves the fixed law and endpoint atom data, while the all-Continue alternative remains a static cap face rather than an executable chronology. |
| Maximal-root response-rectangle reduction | `UniformEquilibrium/Quitting/Root/MaximalAbsorptionNash.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleMaximalRootLedger.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleMaximalRootReduction.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumOpponentIncidence.lean`, and `UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourMaximalRootNegativeOrientation.lean` | `exists_maximalAbsorption_isZeroQuittingRootNash` selects an absorption-maximal exact root on every nonempty compact exact-root fibre.  On a supplied hard-residual response rectangle, `quittingRectangleMaximalRootPrefixedEndpoint_debt_coordinate_eq`, `quittingRectangleMaximalRoot_survival_floor`, and `quittingRectangleMaximalRootPrefixed_atom_lower` retain playerwise debt scaling, the literal `D_* / (8 * M) <= 1 - a_n` survival floor, and the `c * D_* / (32 * M) <= 16 * atom` lower bound.  Under vanishing absorption, `quittingRectangleMaximalRootPrefixedEndpoint_tendsto_cluster` retains the common joint semantic/law limit.  `QuittingStoppingLawRectangleJointAtomLimit.maximalRoot_exactlyOne` packages the pairwise-exclusive alternatives: a uniformly charged strict subsequence, a minimum-fibre reset-rigid chamber, or an off-minimum vanishing-root branch; `maximalRoot_threeWay` remains the inclusive eliminator.  This has `M`, `L`, and branch-local `A`, but no downstream `C`: it neither produces the hard-residual rectangle nor renews or consumes any returned branch.  The negative-orientation regression checks a positive signed atom with zero opponent incidence and an exact all-Continue root; it does not prove that root unique. |
| Four-profile descendant-slice neutralization | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFourProfileDescendantSlice.lean` and `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourProfileDescendantSliceLanding.lean` | `QuittingFourProfileResponseFamily.exists_minimum_normalizedDescendantSlice_eq_or_strict_inert` minimizes response debt on a closed common-prefix orbit while retaining separate response/sibling signed-atom and source/replacement actual-gain densities. Exact cap--Nash prefix closure makes all Continue the unique exact root at the positive-debt minimizer. For a supplied Fin4 rectangle joint-law limit and hard residual, `QuittingStoppingLawRectangleJointAtomLimit.exists_fourProfileDescendantSliceLanding` selects one common four-profile subsequence and positive densities, then returns a minimum-debt point with positive opponent incidence and a reset-rigid chamber, or a strictly off-minimum point; both passports and zero observer debt remain literal fields. The generic layer has `M` and `L`, and the Fin4 attachment adds branch-local `A` from the supplied rectangle. There is no `C`: closed-descendant provenance supplies no finite ancestry, marked date, stopping law, chronology, renewal, arm consumer, or uniform-equilibrium result. |
| Exact repair certificates | `UniformEquilibrium/Diagnostics/Quitting/ExactRepairCertificate.lean` | Proof-carrying cutoff-one, stationary, and cyclic certificate checkers. `UniformEquilibrium/Diagnostics/Quitting/CutoffOneMixedActual.lean` instantiates the cutoff-one checker for an exact rational table and names its zero payoff. |
| Solan--Vieille boundary table | `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryEquilibrium.lean`, `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryNonstationarity.lean` | An exact period-two equilibrium and its uniform payoff coexist with quantitative exclusion of all sufficiently accurate stationary or uniformly near-all-Continue terminal approximate equilibria. |
| Small-hazard sequential serialization | `UniformEquilibrium/Quitting/Root/SequentialSerializationEquilibrium.lean` | `isAsymptoticNash_quittingSerializedRoots` splits each stage into four actual one-owner substages. For any bounded Fin4 table with unit own singleton rewards, it transfers an actual terminal approximate equilibrium with error `error` and hazard bound `h` to error `error + 32 * M * h`, against unrestricted behavioral deviations, including Never. It does not require certain absorption or construct a small-hazard source. |
| Solan--Vieille solo-hazard obstruction | `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardLedger.lean`, `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardFloor.lean`, and `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardSemantic.lean` | `Schedule.one_over_sixtyEight_lt_literal_exploitability` checks the literal all-behavior bound `1 / 68 < E` for every arbitrary finite or infinite at-most-one-owner calendar, via the stronger inequality `1 <= 14 * E^2 + 67 * E`. No periodicity or positive-hazard assumption is used. This rules out universal single-owner derandomization on the boundary table; it does not concern multi-owner rows. The packet's rational upper schedule and the exact optimal floor remain unformalized. |
| Returned-block homogeneous tangent obstruction | `UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`, `UniformEquilibrium/Quitting/Stationary/ReturnedBlockPrincipalRestriction.lean`, and `UniformEquilibrium/Quitting/Classification/LCP/ReturnedBlockTangentGap.lean` | `hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks` consumes arbitrary-varying-horizon returned product blocks whose total hazard vanishes and whose aggregate Bellman and probability-weighted endpoint regrets are little-o of that hazard. `relativeError_gap_of_noHomogeneous` strengthens the converse to an explicit `R0`-margin scale and relative-error gap. `ResidualHardClass.exists_pos_ambientNormalCoreReturnedBlock_relativeError_gap` uses the exact pure-Continue coordinate-deletion law to transfer the gap to ambient blocks supported on the recursive normal core. No block, chronology, or unrestricted-behavior strategy is produced. |
| Strict-covector positive-survival terminal cost | `UniformEquilibrium/Quitting/Chronology/ConvergentDiffuseExactFloorTail.lean`, `UniformEquilibrium/Quitting/Chronology/SummableExactTailTerminalGap.lean`, and `UniformEquilibrium/Diagnostics/Quitting/Chronology/StrictCovectorDynamicTail.lean` | Every supplied convergent diffuse exact floor tail either enters a checked uniform-payoff dispatch or admits one common normalized strict covector controlling all sufficiently late finite and infinite horizons. Finite absorption charge, survival tending to one, and eventual positive Never mass are conclusions. For any summable exact tail, the unrestricted behavioral suffix gain converges coordinatewise to the positive part of the solo payoff; the canonical dynamic-tail adapter and positive-solo no-uniform-payoff corollary are checked. This prices the surviving atom but does not attach a punishment or paid return. |
| Exact cyclic singleton example | `UniformEquilibrium/Quitting/Examples/CyclicSingletonFourPlayer.lean` | `CyclicSingletonFourPlayer.isUniformEquilibriumPayoff` checks the explicit four-player cyclic reward table and its unrestricted-behavior uniform payoff by the general balanced singleton compiler. This is an exact example, not a universal cyclic construction. |

Import an internal file directly when its narrower interface is the point of
the proof. The umbrellas are navigation and project-integration boundaries,
not external compatibility promises or a ban on precise dependencies.

## Semantic waist and terminal bridge

`GameTheory/GameTheory/Stochastic/Uniform.lean` owns the canonical
`Stochastic.Game.IsUniformEquilibriumPayoff` and its deviation-cap constructor.
`UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform.lean`
owns the project proof view, and
`UniformEquilibrium/ProofView/Native/Equilibrium.lean` proves their exact
finite-horizon Nash and uniform-payoff equivalence for finite states and
actions. A candidate mechanism is complete only after it supplies the uniform
finite-horizon delivery and unilateral-deviation bounds encoded by that
semantic waist.

The native bridge also retains source data below payoff equivalence.
`IsRealizablePublicHistory` and
`isRealizablePublicHistory_publicHistoryOfTrace`
(`UniformEquilibrium/ProofView/Native/History.lean`) record that every
canonical public stage is source-coherent and belongs to the support of the
actual proof-view transition.  For bounded comparison,
`native_runBehavioral_eq_of_support_agreement` and
`exists_nativeMixed_publicHistoryLaw_eq_compiled`
(`UniformEquilibrium/ProofView/Native/Semantics.lean`) respectively require
profile agreement only on histories exposed by the run and realize the exact
compiled public-history law by a mixed contingent policy.  The mixed witness
depends on the profile and horizon; it is not one mixed profile valid at all
large horizons and therefore is not by itself a uniform-equilibrium compiler.

For finite quitting games, a producer that already names its payoff target
should retain that target through the terminal-to-uniform bridge.
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`
owns the exact and per-accuracy approximate-target interfaces, while
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
also compiles a sequence whose errors tend to zero and whose terminal payoffs
tend to a specified target, provided terminal Nash profiles occur arbitrarily
far along that sequence.  Limits of terminal-payoff vectors remain in the
canonical reward cube, as does every uniform-equilibrium target; the
target-free fallback selects a payoff in that cube from terminal approximate
equilibria available at every positive accuracy.  Compact target selection is
not a substitute for an exact or convergent target already supplied by the
producer.  Terminal verification, target selection, and uniformization remain
separate steps in lower-level proofs.

`quittingGame_exists_terminalTargetAcceptance_of_terminalNash_family` and
`quittingGame_exists_uniformPayoffWitnesses_of_terminalNash_family`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
select one target from a supplied vanishing-error family and retain actual
family indices at every accuracy. The first exposes the same member's
terminal Nash and delivery bounds; the second supplies all sufficiently long
horizons. There is one compact payoff selection proof. Quiet coordinates or
finite support of every family member therefore remain available without
assuming convergence of strategies.

`UniformEquilibrium/Certificates/Adaptive/PotentialSystemTools.lean` is the transformation facade for the
proof-facing adaptive-potential waist. It deliberately reuses the one
`AdaptivePotentialSystemAt` definition: consolidation here means a canonical
API surface, not a second structure. Public stopping and response compilers
remain separate because they add causal-law realization and credibility
obligations.

## Positive construction families

| Family | Required input | Production output | Remaining nonclaim |
| --- | --- | --- | --- |
| Exact product-root closure | One supplied uniform-equilibrium payoff and an exact product Nash root against that continuation payoff | `isUniformEquilibriumPayoff_rootSuccessor_of_isZeroRootNash` in `UniformEquilibrium/Quitting/Root/ExactSuccessorClosure.lean` proves that the Bellman successor is a uniform-equilibrium payoff, including roots with zero survival | Does not supply the continuation payoff. |
| Proper singleton-flow closure | One supplied uniform-equilibrium payoff, a singleton segment of mass strictly between zero and one, viable endpoints, and active-owner equality | `isUniformEquilibriumPayoff_singletonArc_of_viable_proper` in `UniformEquilibrium/Quitting/EssentialAPS/ProperSingletonFlowClosure.lean` proves the source is a uniform payoff. `IsProperViableSingletonFlowChain.isUniformEquilibriumPayoff` handles any finite chain, and `isUniformEquilibriumPayoff_singletonArc_before_rootSuccessor` in `UniformEquilibrium/Quitting/EssentialAPS/JumpFlowClosure.lean` composes it with an exact root | Does not produce the terminal continuation or justify an infinite alternation of jumps and flows. |
| Arbitrary finite jump–flow ordering | A data-bearing finite word retaining each exact root or proper viable singleton segment, with a separate positive mesh count for each occurrence | `CompatibleFiniteJumpFlowWord.execute` in `UniformEquilibrium/Quitting/EssentialAPS/FiniteJumpFlowCompiler.lean` constructs an ordinary behavioral profile. `CompatibleFiniteJumpFlowWord.execute_common_error_bound` and `CompatibleFiniteJumpFlowWord.execute_exploitability_le` bound its target error and unrestricted behavioral debt by the terminal error and accumulated singleton mesh hazards. `CompatibleFiniteJumpFlowWord.isUniformEquilibriumPayoff` transports a supplied fixed uniform-payoff tail through every finite ordering | This is a finite compiler, not an infinite-word completion theorem. The exact all-Continue self-loop in `UniformEquilibrium/Quitting/Examples/AllMinusOneLiveBoundary.lean` satisfies root Nash at the constant payoff one although every actual terminal payoff is nonpositive. |
| Diagonal target tail | Accuracy-indexed exact Nash--Bellman prefixes with small joint survival and player-indexed target-closed tails | Terminal approximate equilibria and hence a uniform payoff | Does not construct the prefixes or prove their survival certificate. |
| Support witness | At every tolerance, a support-wise approximately optimal root path, divergent absorption, and continuation-by-continuation individual rationality; alternatively a finite periodic witness with one absorbing phase | A terminal `3ε` profile and target-free uniform-payoff existence | Does not produce the paths or cycles for arbitrary games. |
| Cyclic `K/N` finite word | A translated finite block word with positive hazards on every scheduled player-phase pair and exact root Nash at every canonical successor value | Every cyclic entry value is a uniform-equilibrium payoff | Does not produce the finite Nash certificate for an arbitrary reward table; prescribed proper positive-hazard words fail for the self-membership reward. |
| Signed projective lasso | An accepted target and, at every tolerance, a finite root word whose signed survival-weighted monodromy is small relative to absorption for every cyclic entry phase, with support optimality and punishment rationality | Exact periodic correction, a divergent support-rational path, and a uniform payoff | Matching analytic packet extraction neither accepts its endpoint nor constructs the required physical candidate; absolute-weighted variation is only a stronger compatibility interface. |
| Finite charged forward packets | At every charge target, one exact finite forward Bellman packet in a fixed compact carrier, with support optimality and punishment rationality | Compact charged return, a single-seam lasso, and a uniform payoff | Does not produce the packets or consume the complementary bounded-charge branch. |
| Essential APS | A compact convex functional unique-live component with finite-window face avoidance, terminal-freeness, and bounds | A coherent executable path, qualitative deleted-player survival, adaptive finite meshes, and a uniform payoff for every initial component value | Does not prove that an arbitrary game has a nonempty component; pointwise full jumps remain outside the adaptive logarithmic mesh. |
| Multi-owner face circulation | A bounded balanced circulation with positive phase ratios, one common ratio ceiling below `1`, and a payoff floor above the quitting punishment value | Arbitrarily charged finite packets and a uniform payoff by finite closing; independently, a chronological compact path | Does not construct such a circulation for every game or identify the selected target with a named certificate vertex. |
| Cumulative-budget marked paths | At every accuracy, compatible compact finite prefixes with a fixed activity cap and a cumulative total-absorption budget tending to infinity; alternatively one fixed singleton mark with divergent cumulative mass in the one-active stratum | One infinite support-rational path with nonsummable absorption and hence a uniform-equilibrium payoff | Does not produce the finite prefixes or prove that one singleton label survives across them. Pointwise positive marked mass is unnecessary, but cumulative divergence is essential. |
| Punishment-completed finite cycle | An exact absorbing Nash--Bellman cycle where each coordinate either contracts in deleted survival or has punishment value at most its selected solo value | The selected phase value is a uniform-equilibrium payoff; the nonnegative-solo admissible-cycle compiler is a corollary | Does not produce an exact cycle, and does not cover an isolated coordinate whose punishment value exceeds its negative solo value. |
| Two-player closure | An arbitrary finite two-player quitting game | Unconditional uniform-payoff existence, with an explicit zero, owner-solo, blocker-solo, or joint-exit target in each branch | Does not extend the pair-repair classification to three or more players. |
| Three-player closure | An arbitrary finite quitting game on `Fin 3` | Unconditional uniform-payoff existence | Does not settle four or more players or the general stochastic-game proposition. |

The essential-APS and circulation families contain genuine producers relative
to their stated structured inputs.  They are conditional positive strata, not
generic quitting-game existence theorems.

## Reusable infrastructure

| Tool | Module | Use |
| --- | --- | --- |
| Discrete hazard stopping | `MathUE/Probability/DiscreteHazardStopping.lean` | Survival products, first-hit weights, total stopping mass, and bounded stopped-payoff accounting independent of quitting games. |
| Independent first-stopping coalition square-root laws | `MathUE/Probability/OverlappingFirstStopping.lean` and `MathUE/Probability/IndependentFirstStoppingPair.lean` | `twoOverlappingFirstStoppingMasses_sqrt_sum_le_one` proves the sharp square-root bound for two overlapping tie-before-third events of three arbitrary complete stopping laws, including positive Never mass. `sqrt_exactFiniteFirstStoppingCoalitionMass_add_sqrt_le_one_of_incomparable` gives the corresponding exact-coalition theorem for any two incomparable intersecting coalitions. Combining it with the disjoint-pair clock yields `sqrt_exactFiniteFirstStoppingPairMass_add_sqrt_le_one`: over any finite player type, every two distinct two-player exact first-stopping coalitions have square-root masses summing to at most one, and hence all fifteen pair projections for four players are covered without a Fin4 case split. Independence is encoded by products of the separately supplied marginal laws. The complete overlapping-event equality classification is in `MathUE/Probability/OverlappingFirstStoppingChronologicalEquality.lean`. Actual-profile adapters and conditional pair-mass consumers are described above. An affine mass-bound producer for an arbitrary reward table is not supplied. |
| Survival products | `MathUE/SurvivalProduct.lean` | Generic finite-product and cumulative-hazard estimates shared by stopping arguments. |
| Survival coboundaries | `MathUE/Probability/SurvivalCoboundary.lean` | Exact varying-hazard survival-weighted telescopes and finite-difference remainder identities. |
| Discounted backward recursion | `MathUE/Probability/DiscountedBackwardRecursion.lean` | Prefix-discrepancy Abel bounds, exact terminal shadow contraction, and summable block-tail accounting; it does not construct an infinite recursion. |
| Finite smooth maxima | `MathUE/Analysis/FiniteLogSumExp.lean` | `smoothMax_eq_weightedMean_add_entropy` gives the exact Gibbs identity and finite-cardinality approximation bounds. `deriv_smoothMax` and `deriv2_smoothMax` identify actual local derivatives, the latter as weighted component curvature plus variance divided by positive temperature. The weights reuse canonical arbitrary-score exponential probabilities. No game-specific tester family or calendar is produced. |
| Compact minimum-envelope right derivatives | `MathUE/Analysis/CompactMinimumEnvelope.lean` | `exists_right_derivative_minimizer` internally selects one old minimum attaining the least actual derivative over all old minima, and proves that value is the envelope's right derivative. Joint continuity of the family and actual parameter derivative on an open real domain supplies uniform first-order error internally. The index is any nonempty compact topological space; uniqueness, a selected favorable minimum and a supplied uniform error certificate are not required. No tilted-calendar selection is produced. |
| Actual common-calendar tester source | `UniformEquilibrium/Quitting/Paths/CommonCalendarSmoothMinimum.lean` | `exists_quittingCommonWindowSmoothMinimum_with_weights` internally selects one independent finite-calendar profile and its own positive, normalized tester weights. The common pool contains zero, every owner's dates through `2*clock+1`, and separate Never replies. Its maximum equals unrestricted behavioral exploitability, and the same weights satisfy the entropy inactivity bound. Late finite payoff retains the signed singleton correction. No outer singleton maximizer, silent transport or enlarged-calendar directional estimate is produced. |
| Actual discounted continuation replacement | `UniformEquilibrium/ProofView/Concepts/Stochastic/Transform/Payoff/DiscountedContinuation.lean` | `discountedPayoff_prefix_decomposition` disintegrates every behavioral profile over its actual finite-prefix law in a finite stochastic game. `discountedPayoff_terminalChildDispatcher` preserves that prefix while dispatching arbitrary complete child profiles. `discountedPayoff_replaceContinuation` gives the exact root payoff change from replacing one public branch: its actual probability times the remaining geometric weight times the child payoff change. Zero depth, zero discount and unreachable branches are included. `continuationCoefficient_mem_Ioo` gives strict coefficient bounds at a reached positive-depth branch with positive discount. This is payoff accounting, not an equilibrium or renewal producer. |
| Actual discounted Nash continuations | `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/DiscountedContinuation.lean` | `realizedAction_discountedPayoff_update_deviationAfterHistory` identifies the root gain of an actual unilateral branch splice with its discounted reach times the full child gain. `realizedAction_afterHistoryProfile_isDiscountedNash_of_mem_support` derives Nash of every reached child from root Nash. Positive depth needs positive remaining discount; zero discount is allowed at depth zero. No perfection at unreachable histories is asserted. |
| Actual initial-mixture and branch-reply deviations | `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/DiscountedInitialBranch.lean` | `realizedActionInitialBranchDeviation` constructs one full unilateral strategy changing its initial mixture and its complete reply at every first-stage public history. `realizedAction_discountedPayoff_initialBranchDeviation` gives exact current-plus-continuation accounting, and `realizedAction_discountedNash_initialBranchDeviation_bound` derives its deviation bound from actual root Nash. Off-path replies remain available when the changed mixture reaches those branches; no jointly feasible continuation-value matrix is assumed. |
| Actual discounted Nash child gluing | `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/DiscountedInitialBranch.lean` | `realizedAction_initialChildDispatcher_isDiscountedNash` combines actual Nash children at every first public history with Nash of the internally defined current-plus-child game. The same dispatcher has the exact mixed payoff by `realizedAction_discountedPayoff_initialChildDispatcher`. Arbitrary full behavioral root deviations, initially unreachable children and zero discount are retained. |
| Support-local discounted Bellman bounds | `UniformEquilibrium/ProofView/Concepts/Stochastic/Strategy/Potential/Adaptive.lean` | `discountedPayoff_le_of_history_bellman_ge_on_support` needs the bounded history potential and one-step bound only on the queried actual profile's history support. Applied to a full deviation, that support is the deviation's own support, not the prescribed profile's support. Zero discount is allowed. The state-only bound delegates to the common expected-value telescope in `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Discounted.lean`. |
| Compact discounted best responses | `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/CompactDiscountedBestResponse.lean` | `exists_discountedBestResponse_of_compact_transfer` internally selects an actual full behavioral reply from a compact continuous unilateral presentation and exact encode/decode payoff transfers. It is conditional on those presentation data. `FiniteStageGame.exists_discountedBestResponse` (`Literature/Sorin1986.lean`) constructs them for every finite repeated game and every paper discount rate, including the current-stage endpoint. The separate standard-axiom check excludes dependence on unfinished Literature proofs. |
| Differently labelled points in one compact fiber | `MathUE/Topology/CompactDiscreteFiber.lean` | `exists_same_fiber_different_labels` proves that a continuous surjection from a compact space onto a Hausdorff preconnected space cannot separate all fibers by a nonconstant continuous discrete label: two differently labelled source points force a fiber containing two differently labelled points. This supplies no payoff-path lifting or selection theorem. |
| Small representations of preconnected convex hulls | `MathUE/Topology/ConnectedConvexHullRepresentation.lean` | `exists_small_finset_of_mem_convexHull_isPreconnected` selects a nonempty finite subset of the actual source representing the supplied convex-hull point, with cardinality at most the ambient dimension or one in dimension zero. No compactness, path connectedness, or supplied representation is required. Its silent named check, exhaustive axiom audit and full integration check pass. This supplies a geometric prerequisite, not Sorin's discounted schedule or an equilibrium. |
| Affine peeling and geometric schedules | `MathUE/Topology/ConnectedConvexHullAffineStep.lean`, `MathUE/RealSeries/GeometricAffineSchedule.lean` | `exists_affine_step_of_mem_convexHull_isPreconnected` internally selects a source point and convex-hull residual under the prescribed dimension-weight budget. `exists_geometric_schedule_of_bounded_affine_steps` constructs the complete schedule from actual affine steps in a bounded region and proves its exact coordinatewise discounted payoff. Neither result asserts equilibrium or closes Sorin's paper statement without its game-specific adapter. |
| Sorin's discounted feasible-set identity | `Literature/Sorin1986.lean` | `proposition_4` proves the paper's exact identity between discounted and correlated feasible payoffs for positive rates below the reciprocal player count. The source geometry, stages and behavioral realization are constructed internally. Its silent paper check, separate actual-profile consumer and standard-axiom checks, and full build pass. `proposition_6` reuses the generic schedule; `proposition_15` retains its actual behavioral equilibrium statement and passes the separate axiom check. Other unfinished paper results remain separate obligations. |
| Sorin's flat-face source and strict-active consumer | `Literature/Sorin1986.lean` | `FiniteStageGame.exists_flatFace_calendar` selects an actual nonempty finite pure calendar approximating a supplied feasible target on a globally capped security face, preserving the flat coordinate at every date. `exists_discountedNash_close_allSmallRates_of_flatFace_strictActive` internally consumes that source when the two listed coordinates exhaust the players and the target has strict active security slack. One profile precedes all sufficiently small rates, with exact flat delivery at every valid rate, full behavioral exact Nash at small rates, and metric target approximation. The silent paper check and separate standard-axiom checks pass. Weak-active targets without strict slack and the whole paper claim are not supplied by this facade. |
| Sorin's original discounted convergence clause | `Literature/Sorin1986.lean` | `property_4_discounted` and its delegating `lemma_2` prove the literal Hausdorff convergence of discounted equilibrium payoff sets to the weakly IR feasible set, under the corrected alternative that this set is full dimensional or there are exactly two players. Actual pointwise profiles precede all small rates; flat-preserving mixing includes weak-active targets, and a compact finite cover makes the threshold uniform over all targets. `exists_discountedNash_flatDelivery_allRates_of_mem_IR_of_flatFace` additionally retains exact flat delivery at every valid rate for the same weak-target profile. The named paper check and separate standard-axiom checks pass. Other unfinished paper claims remain separate obligations. |
| All-sign rationalized quadratic bracket selector | `MathUE/RationalizedQuadraticBracketRoot.lean` | `rationalizedQuadraticRoot_spec` selects the unique root in a positive bracket with negative constant and positive upper-endpoint value, with explicit positive denominator and discriminant and positive derivative at that root. No sign condition is imposed on either higher coefficient. The formula and its closed-interval continuity companion retain the linear case and zero endpoints; endpoint continuity uses positive endpoint linear coefficients. This scalar source does not supply a game-facing pivot or the general two-buffer rational selector. |
| Actual cyclic-child scalar balance and pivot | `MathUE/CyclicChildJointPhaseAlgebra.lean`, `MathUE/CyclicChildJointPhasePivot.lean` | `selectedBalanceRoot_spec` constructs the literal collision-adjusted nonlinear root and proper solo rates from positive cycle/harm parameters, nonpositive collision rewards, nonnegative eta and positive cycle gap. The actual inverse produces positive balance weights; quadratic signs and denominator bounds are discharged internally. `JointPhaseData.exists_pivot` selects an interior hazard from the literal pivot interval using continuous canceled endpoint ratios and both exact endpoint payoffs. Positive crossing and admissible-root uniqueness remain separate checked companions. |
| Raw cyclic-child joint-phase UE source | `UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean` | `CyclicChildJointPhase.exists_uniformPayoff` internally selects a proper three-row cycle and its exact initial payoff from the five specified reward vectors and six retained outsider joining caps. The full coarse `SourceCertificate` is derived, including every player's policy and Continue equations, singleton floors, retained Quit caps and genuine opponent contraction. The same target precedes refinement accuracy. Eta may be zero; xi is positive, v is below one and u is at most one plus xi. All unspecified coalition entries remain arbitrary. The theorem covers the literal open pivot interval; outer parameter exits and packet-specific quantitative refinements remain separate. |
| Protected-set signed exact-root return and analytic exclusion | `UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`, `UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeaversSmoothDrift.lean` | `exactRootSuccessor_mem_protectedSetBox` gives protected participant floors at every boxed source. `exactRootSuccessor_mem_protectedSetSublevelDomain` additionally returns absorbing exact roots to some singleton sublevel when the source has protected floors and each actual premium trap supplies a protected strict leaver. All nonempty opponent coalitions remain in the comparison. `not_isQuittingFullExactRootPotential_of_supportSpecific_strictLeave` proves the signed analytic exclusion for any finite nonempty player type, allowing an empty protected set and signed singleton rewards. Its regularity is continuity on the protected sublevel domain and ambient differentiability on the singleton lower boundary. |
| General convex return-domain exclusion | `UniformEquilibrium/Quitting/Projective/ConvexReturnDomainSmoothDrift.lean` | `not_isQuittingFullExactRootPotential_of_convexReturnDomain` excludes full exact-root potentials from actual boxed return to a compact convex region containing the singleton upper box and absorbing return from that region to some singleton sublevel. Continuity is required only on the sublevel region and ambient differentiation only on the singleton lower boundary. No participant sign or individual successor floor is assumed. Shared compact-minimum and downward-charge owners also preserve the older nonconvex return-domain interface. |
| Actual protected-set strict and weak UE | `UniformEquilibrium/Quitting/Classification/Existence/SupportSpecificQuittingPremiumLeaversUniformPayoff.lean`, `UniformEquilibrium/Quitting/Classification/Existence/SupportSpecificQuittingPremiumLeaversRewardClosure.lean`, `UniformEquilibrium/Quitting/Classification/PassiveQuittingRewardPerturbation.lean` | `exists_uniformEquilibriumPayoff_of_supportSpecific_strictLeave` supplies an actual Fin4 fixed target from nonnegative own singletons, protected participant premiums and actual support-specific strict leavers. Its weak companion uses all-passive reward perturbation and canonical actual-game reward closure, not a weak analytic exclusion. Participant entries, traps, core and maximal protected set are invariant for every real perturbation; positive perturbations strictify weak leave. Maximal-protected-set wrappers derive the participant test internally. |
| Actual weighted trap-leave UE | `UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapReturn.lean`, `UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversRewardClosure.lean` | `exists_successor_le_singleton_of_weighted_strictLeave` constructs absorbing singleton-sublevel return from reward-only per-trap weights satisfying global all-coalition inserted-premium and proper-subset leave tests, including the all-sure support case. The canonical return region is a closed convex intersection of valid weighted halfspaces. `exists_uniformEquilibriumPayoff_of_weightedTrap_weakLeave` supplies one actual Fin4 original target when own singleton rewards are nonnegative; strict nearby tables use the shared convex analytic consumer. All-passive perturbation preserves the valid-weight family and domain at a fixed box bound for every real increment; positive increments strictify the same leave weights. No weak analytic exclusion or finite-polytope representation is asserted. |
| Cyclic-child arbitrary-row root inventory and resonance exit | `MathUE/CyclicChildComplementarity.lean`, `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildSingletonAdapter.lean`, `UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSingletonExits.lean` | `exterior_positiveOffset_solution_iff` classifies all roots at the displayed regular offset, and `exteriorMatrix_det` proves the exact child-gap times exterior-balance determinant. The exterior row is arbitrary; positive-offset activation and homogeneous propagation impose no cycle-coefficient signs. The actual singleton adapter computes its inverse balance from raw rows, proves R0 away from resonance and supplies an actual uniform payoff at resonance. The one-joint facade derives those rows internally. |
| Actual cyclic-child passive-inverse exit | `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildPassiveInverseExit.lean`, `UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSingletonExits.lean` | `exists_uniformPayoff_of_passiveThreshold` supplies an actual original-game fixed target from literal singleton rows and the three computed nonnegative outside-inverse numerators. Child inverse, deleted-player transport and strategic child requirements are discharged internally. Harm coordinates are unrestricted. The two-threshold specialization retains equality and requires v below one; `exists_uniformPayoff_of_passiveExit` supplies the literal one-joint packet threshold. |
| Actual cyclic-child low-degree and all-pivot exits | `MathUE/CyclicChildExteriorDegree.lean`, `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildLowDegreeExit.lean`, `UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSingletonExits.lean` | `exterior_r0Degree_eq_zero` computes degree zero from exactly all roots at the displayed regular offset, with strict inactive residual and opposite active-determinant signs. `exists_uniformPayoff_of_below_resonance` supplies the actual raw-singleton low exit. `exists_uniformPayoff_all_pivots` composes it with resonance, passive and actual interior producers for the original one-joint class, for every real pivot payoff. Xi is positive, v is below one and u is at most one plus xi; eta may be zero. The other packets' different joint selectors, explicit calendar/law constants and fixtures remain separate. |
| Full polynomial endpoint field and clipping | `UniformEquilibrium/Quitting/Root/FullClippedEndpointMap.lean` | `quittingRealHazardEndpointGap` extends every actual endpoint gap to a smooth polynomial on arbitrary real hazards. The literal full clipped map sends all ambient vectors to the closed cube. Its fixed points are precisely exact product-root Nash points, including zero and sure hazards; the continuous full cube-complementarity problem has the same solutions. This does not compute a source Jacobian or a local degree. |
| Nonlinear derivative-sign local index | `MathUE/Topology/AmbientDegreeNonlinearLocalIndex.lean` | `exists_ambientDegree_eq_sign_det_of_hasFDerivAt_on_nhds` derives an isolating root-centered region and determinant-sign degree from local continuity, differentiability at the actual zero and a nonsingular derivative matrix. The coercivity estimate, frontier separation and unique zero on the closure are produced internally. Dimension zero is included; no continuous derivative or isolation oracle is assumed. |
| Generic next-to-top symmetric mean bound | `MathUE/FiniteNextToTopSymmetricMean.lean` | `Math.NextToTopSymmetric.value_le_sum_pow_div_card_pow` bounds the sum of all products omitting one coordinate by the total to power n minus one divided by n to power n minus two, for every finite inventory of at least three nonnegative coordinates, including boundary and zero vectors. The compact-maximum averaging proof is generic, not a Fin4-only substitute. Finite-carrier transport and cardinal-layer grouping supply the actual boxed charge source. |
| Actual boxed Nash-charge payoff producer | `UniformEquilibrium/Quitting/Classification/Existence/BoxedQuittingNashChargesUniformPayoff.lean`, `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeOdds.lean` | `exists_uniformEquilibriumPayoff_of_boxedQuittingNashCharges` produces an actual Fin4 fixed target from nonnegative own singletons, any coordinate reward bound and literal trap coefficient tests with strict charge margins. It internally dispatches sure hazards, derives the odds threshold, selects a common box and supplies exact returning roots. No strategic certificate is an input. `QuittingTrapChargeCoefficients.threshold_of_cardinality_three` and `QuittingTrapChargeCoefficients.threshold_of_cardinality_four` give the literal rational and square-root specializations. Packet neighborhood, child-debt and separation claims remain separate obligations. |
| Literal boxed-charge tables and payoff consumers | `UniformEquilibrium/Quitting/Examples/BoxedNashChargeTripleFixture.lean`, `UniformEquilibrium/Quitting/Examples/BoxedNashChargeFullCoreFixture.lean` | The complete proper-triple and full-core reward tables supply exact participant/trap/core censuses, coefficient layers and actual uniform-payoff consumers. The displayed thresholds are 90 and 348 times the square root of 45. These bounded units do not claim the packet's neighborhood, unbounded-source counterroot, proper-child debt or matrix/response exclusions. The generic binary coalition encoder lives in `MathUE/Finset/CoalitionBinaryCode.lean`; fixtures do not import an unrelated example for coding. |
| Pair inactive-gap annotation avoidance | `MathUE/Topology/CoordinateAffineAvoidance.lean`, `UniformEquilibrium/Quitting/Root/PairInactiveGapNumerator.lean` | `quittingPairInactiveGapNumerator_update` derives the cleared four-atom inactive endpoint numerator's own-annotation slope as the negative product of two joining gaps. When those products are nonzero, finite simultaneous nonzero loci meet every nonempty open annotation region, retaining every outside-pair recipient. This does not classify Nash roots or compute a Jacobian or degree sum. |
| Arbitrary selected complement-component fills | `MathUE/Topology/SelectedComponentFill.lean`, `MathUE/Topology/SelectedComponentFillLocallyPathConnected.lean` | `isPathConnected_selectedComponentFill` constructs actual paths when the ambient space is path connected and the source is closed and path connected. Closedness needs ambient local path-connectedness; local path-connectedness of the fill additionally needs that of the source subtype. No finite selected family, metric or separation premise is imposed. The computed compact-carrier instantiation is recorded below; the general planar disk model remains separate. |
| Actual circle obstruction and first closed-set hit | `MathUE/Topology/ComplexCircleLogarithmObstruction.lean`, `MathUE/Topology/PathFirstClosedSetHit.lean` | Every logarithm of an actual scaled one-turn circle has the explicit nonzero endpoint displacement; hence it cannot close. An actual path to a closed set can be clipped at its first hit, with range in the original range intersected with the union of the closed set and its starting complement path component, for arbitrary topological targets. These are source ingredients, not the planar nullhomotopy bridge for Sorin Proposition 11. |
| Conditional chosen-return payoff compiler | `UniformEquilibrium/Quitting/Projective/SelectedSingletonSublevelReturnSmoothDrift.lean`, `UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean` | `exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_of_reward_bound` consumes existential exact-root return at every strictly-below-singleton source in the same boxed sublevel domain. Own singletons are nonnegative; the box lies strictly above any supplied coordinate reward bound and at most two above the canonical sum bound. The old canonical-bound consumer is a thin instance. Analytic regularity is continuity on that domain and differentiation on the singleton lower boundary. Selected localization does not assert zero absorption for all roots. The actual signed-pair composition is recorded below; mixed-trap composition remains separate. |
| Actual signed pair-core same-sign payoff criterion | `UniformEquilibrium/Quitting/Classification/SignedPairCoreSelectedReturn.lean`, `UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreRewardClosure.lean` | `exists_uniformEquilibriumPayoff_of_empty_or_signed_pair_core_weakSameSign` supplies one original Fin4 fixed target from nonnegative own singletons and either an empty premium core or an exact pair core whose two joining gaps have nonnegative product. The strict producer splits the actual pure-pair Nash alternative from selected return, supplying the second clipped fixed point and bad-root uniqueness internally. The weak boundary changes only two passive singleton entries, preserving every participant entry, own singleton, trap and core. This is not a criterion for every core of size at most two or a weak analytic return theorem. |
| Generic pure-set Nash sure exit | `UniformEquilibrium/Quitting/Root/PureSetNashSureExit.lean` | `isUniformEquilibriumPayoff_setReward_of_pureSetNash` turns an actual exact pure-coalition root Nash point into the coalition reward's uniform payoff, for any finite coalition with at least two members. The canonical sure-exit tests are derived internally, independently of the tail and without reward sign or premium-core assumptions. The pair consumer is a thin specialization. |
| Actual ambient pair Jacobian and signed bad-root classification | `UniformEquilibrium/Quitting/Root/PairFullClippedJacobian.lean`, `UniformEquilibrium/Quitting/Classification/SignedPairCoreBadRoot.lean` | `pairNash_hasFDerivAt_and_negative_det_fullClippedDisplacement` computes the full ambient derivative and negative determinant from a proper pair Nash root, same-sign joining gaps and strict gaps for every inactive player. `signed_pair_core_badRoot_hasFDerivAt_and_negative_det` internally supplies those fields for actual bad roots of a signed pair core; support, properness and uniqueness are proved from reward data and the stated no-pure-pair alternative. These are source classification/index prerequisites, not a raw selected-return or UE theorem. |
| Computed compact-carrier path-image fill | `MathUE/Topology/CompactCarrierPathImageFill.lean`, `Literature/Sorin1986.lean` | `carrierPathImageFill_spec` computes a compact, path-connected, locally path-connected fill containing the actual interval path image and contained in its compact carrier, under the stated ambient separation/connectivity hypotheses. `CompactContinuousGame.feasiblePathImageFill_spec` supplies that carrier from the actual game's feasible payoffs and preserves the real path's image of Icc 0 1. The paper check and separate permitted-axiom query pass. The general planar model and original Proposition 11 remain separate. |
| Accumulating null-family continuity | `MathUE/Topology/NullFamilyPasting.lean` | `continuous_of_null_closed_patches` pastes parameterized maps on arbitrary null families of closed patches in a pseudometric space, assuming patch invariance, continuity on each patch and identity off patch interiors. No local finiteness, disjointness or compactness is assumed. This is not the planar disk model. |
| Unique cube fixed-point index | `MathUE/Topology/AmbientDegreeUniqueFixedPointIndex.lean` | `exists_fixedPoint_ne_of_negative_det_finite` derives another actual fixed point of a continuous cube-valued map from an actual fixed point with a differentiable, negative-determinant displacement. Expanded ambient charts include zero and sure coordinates; the existing nonlinear local index and excision supply the contradiction. The signed-pair producer consumes this actual second point; finite all-negative-index censuses for mixed/triple sources remain separate. |
| Actual normalized disk embeddings and improvement | `MathUE/Complex/UnitDiscShift.lean`, `MathUE/Complex/NormalizedDiskEmbedding.lean`, `MathUE/Complex/DiskEmbeddingDerivativeImprovement.lean` | `exists_normalized_disk_embedding` constructs an injective disk-valued map on an open simply connected proper complex domain, normalized at a supplied domain point, with nonzero derivative throughout the domain. `exists_disk_embedding_norm_deriv_gt` improves a normalized embedding that omits a disk point. The pinned private source is reused through supported import-all; Apache attribution and immutable source provenance are retained. No maximizing map, disk surjectivity or boundary extension is supplied. |
| Analytic zero factorization, circle multiplicities and limits | `MathUE/Analysis/AnalyticCompactZeroFactorization.lean`, `MathUE/Complex/CircleArgumentPrinciple.lean`, `MathUE/Complex/HurwitzLimit.lean` | `Math.Analysis.exists_finset_eq_prod_smul_nonzero` derives a finite zero set and actual-order product factorization on a compact preconnected set for a nonzero analytic function, including vector-valued functions. `circleIntegral_logDeriv_eq_finsum_analyticOrderNatAt` counts the actual zero orders inside a circle from analyticity near the closed disk and a nonzero boundary. The Hurwitz companions prove zero-or-zero-free and constant-or-injective locally uniform limits on open preconnected complex domains, for a nontrivial countably generated filter. No finite-zero oracle, normal-family compactness, maximizing embedding, full Riemann mapping theorem or Sorin Proposition 11 closure is supplied. Apache attribution is retained. |
| Actual covering endpoints and affine image loop families | `MathUE/Topology/CoveringLoopFamilyEndpoint.lean`, `MathUE/Topology/QuotientFiberCollision.lean`, `MathUE/Topology/CoveringImageIncidence.lean`, `MathUE/Topology/SeparatelyAffineImageLoopFamily.lean`, `MathUE/Topology/SeparatelyAffineCoveringEndpoint.lean`, `MathUE/Topology/SeparatelyAffineComplexLoopLift.lean` | Actual continuous prefix-plus-return image loops and their same-fiber homotopies compose with the compact-incidence covering endpoint law. `exists_closed_logarithmic_lift` supplies a continuous logarithmic lift with equal endpoints for every image loop translated away from an omitted complex point. No family or integer-index oracle is assumed. This is not a nullhomotopy in the original image; the planar bridge for Sorin Proposition 11 remains separate. |
| Sorin's actual payoff-image fiber connectors | `MathUE/Topology/SeparatelyAffineFiberConnectors.lean`, `Literature/Sorin1986.lean` | `returnConnector_homotopic_of_same_value` proves the supplied six-edge cancellation in the payoff-image subtype. `CompactContinuousGame.pair_returnConnector_homotopic` instantiates it in actual compact game strategies; `exists_pairPayoffField_range_eq` identifies the whole image when there are exactly two players. Named checks and separate standard-axiom queries pass. The original Proposition 11 remains unproved; no planar winding or whole-image simple-connectivity theorem is asserted. |
| Compact exact-fiber vanishing statistic | `UniformEquilibrium/Quitting/Root/CompactExactNashFiberMoat.lean` | `exists_eventually_totalNashDefect_moat_of_measure_zero_on_exact_fiber` gives a uniform nearby positive defect moat above any positive threshold of a continuous statistic vanishing on the limiting exact Nash fiber. Its absorption companions control every nearby exact root and arbitrary selected roots over convergent sources, without selector convergence or uniqueness. |
| Separately affine based image loops | `MathUE/Topology/SeparatelyAffineFiberLoops.lean` | `SeparatelyAffinePair.sixVertexLoop_nullhomotopic` contracts the literal six-edge strategy loop inside the payoff image subtype. The fiber bridge is a segment and its reverse by separate affinity. These are supplied-loop homotopies, not a proof that the whole image is simply connected or a closure of Sorin's Proposition 11. |
| Mixed-cycle solo refinement at one fixed target | `UniformEquilibrium/Quitting/Cycles/MixedCycleUniformPayoff.lean` | `MixedCycleSoloMesh.isUniformEquilibriumPayoff` constructs refined independent profiles from a literal coarse `SourceCertificate`: policy and exact Continue, singleton floors, retained Quit caps and playerwise opponent contraction. Arbitrary finite phase inventories, repeated solo owners, nonzero singleton rewards and empty solo phases are allowed; retained product rows may contain sure hazards. The selected coarse initial target stays exact while accuracy changes only the solo subdivision. Full behavioral terminal error is not multiplied by period length. Quiet padding makes the actual period the coarse phase count times the subdivision scale. This conditional compiler does not supply packet-specific coarse sources. |
| Sorin's asymmetric critical-rate equilibria | `Literature/Sorin1986.lean` | `asymmetricStationaryProfile_isDiscountedNash` constructs the stationary cooperation equilibrium for loss parameters satisfying `y ≤ x`, including equality. `asymmetricAlternatingProfile_isDiscountedNash` constructs the DC-first alternating equilibrium when `x < y`. Both use the printed critical rate, retain the printed payoff hypotheses without sign restrictions, and cap arbitrary full behavioral deviations. Actual delivery, membership and boundary consumers pass separate standard-axiom checks, the silent paper build and the full build. The above-critical uniqueness conclusion of `concluding_remark_4` remains unfinished. |
| Coupled cubic shape example | `MathUE/Analysis/Examples/CoupledCubicShape.lean` | `Math.CoupledCubicShape.quasiconvexOn` proves quasiconvexity on every convex domain. `not_convexOn` and `not_exists_additive_eqOn` prove nonconvexity and failure of an additive representation on boxes of dimension at least two and coordinate widths at least one. The actual first and mixed derivatives and a literal rational-polynomial representation are also proved. This is an analytical example, not a quitting potential or equilibrium construction. |
| Compact finite-prefix relations | `MathUE/Topology/CompactFinitePrefixRelation.lean`, `MathUE/Topology/CompactDependentFinitePrefixRelation.lean` | Inverse-limit selection from compatible compact finite prefixes. `exists_dependentInfiniteChain_of_finitePrefixes` also permits the state carrier to depend on the depth, but remains conditional on a coherent family of nonempty compact finite-prefix solution sets; it supplies no compatible-prefix producer. |
| Rational max-expression lower search | `MathUE/Interval/RationalMaxExpression.lean`, `MathUE/Interval/RationalLowerBoxTree.lean`, `MathUE/Interval/RationalLowerBoxSearch.lean` | Exact rational interval evaluation for expressions generated by constants, variables, negation, addition, multiplication, and binary maximum; independently checkable lower-box trees; sound breadth-first search; and strict-margin finite completeness on a rational root box. This is generic executable infrastructure, not CAD/QE for arbitrary semialgebraic formulas. |
| Budgeted compact-prefix relations | `MathUE/Topology/CompactBudgetedPrefixRelation.lean` | Inverse-limit selection while preserving every elapsed cumulative continuous-weight budget, plus the resulting nonsummability criterion. |
| Logarithmic block discretization | `UniformEquilibrium/Quitting/AbsorptionPath/LogarithmicBlockDiscretization.lean` | Exact unique-quitter, continuation-product, and quadratic collision estimates for logarithmic hazard blocks. The continuous derivative/Bellman adapter is not supplied. |
| Supremum witness switching | `MathUE/Optimization/SupremumTwoResetWitnessSwitch.lean` | `orientedSupremumWitnessSwitch_of_abs_mixedDifference` retains source and receiving approximate witnesses, receiving regret and gain, the reverse source-edge budget, and the oriented rectangle, without assuming attainment. `finiteCubeAffineRemainder_eq_squareCurvatureSum` identifies every fixed-witness affine remainder with the exact triangular square sum, and `finiteCubeCapNonadditivity_le_or_hasNegativeSquare` localizes excessive cap nonadditivity. `finiteCube_commonPassport_or_edgeWitnessSwitch` is the finite-scale priority split: either one selected face witness has a literal quantitative edge regret drop, or the full-face witness obeys an explicit all-face passport bound. |
| Pure-time witness-switch decoding | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawResetCubeOrientation.lean` | `exists_pureTimeWitnessSwitchCertificate_of_abs_debtCurvature` pays the prescribed-payoff, fixed-witness, and `3 * eta` budgets and returns both the signed cross-distribution rectangle atom and a separate profitable receiving-edge terminal-difference atom of charge `charge + eta`. `exists_resetCubePureTimeSquareEdgeWitnessSwitch_of_abs_debtCurvature` localizes its diagonal regret change to an actual off-diagonal reset edge with raw charge `(charge + eta) / 2`, while retaining the enclosing square, changed-coordinate identity, and endpoint containment. These are static terminal-law and cube certificates; they do not construct a common source, chronology, or renewal blocks. |
| Survival-weighted suffix regret | `UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean` | `quittingRelativePureTimeTerminalValue_sub_prefixTransport` proves exact source-to-suffix transport for relative quit delays explicitly rebased to absolute dates, and `quittingPureTimeSuffixRegret_le` gives the resulting unconditional `sSup` regret bound without attainment or boundedness hypotheses. `quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul` exactly decodes the difference between quit-now and any later finite-or-`Never` pure-time plan at their first disagreement; `quittingPureTimeEarlierValue_sub_later_eq_opponentSurvival_mul` is its finite absolute-time specialization. No reset-cube chronology or renewal producer is supplied. |
| Finite charged return | `MathUE/FiniteChargedReturn.lean`, `MathUE/CompactFiniteChargedReturn.lean` | Converts sufficiently charged finite prefixes in one compact carrier into a close ordered block with fixed charge, without one orbit uniform in the target. |
| Finite phase occupation duality | `MathUE/Probability/PhaseOccupationDuality.lean` | Semantic/LP primal equivalence, bounded attainment, phase-bias decoding, and strong duality conditional on occupation feasibility. |
| Cyclic exposure | `MathUE/CyclicExposure.lean` | Sharp exposure bounds for finite permutation systems; the shared-punishment calculation is an application. |
| Cyclic `K/N` collapse | `MathUE/GroupAction/CyclicKofNCollapseClassification.lean` | Exact `N / gcd(K,N)` minimum translated-block period, classification of attainable stabilizer factors, and explicit primitive-block fiber lifts. |
| Nonperiodic Snell supersolution | `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean` | Turns exact Continue transport, vanishing local Quit error, and survival decay into history-dependent unilateral caps. |
| Target-anchored stopping tail | `UniformEquilibrium/Quitting/Terminal/TargetTail/TargetAnchoredTail.lean` | Constructs one player's stationary-opponent closed tail at a prescribed target. |
| Joint-survival selection | `UniformEquilibrium/Quitting/Paths/JointSurvivalSelection.lean` | Identifies compactly selected continuation values with actual infinite-path terminal values under joint-survival decay. |
| Projective first-event algebra | `MathUE/ProjectiveBellmanPacket.lean` | Exact cemetery/absorption normalization and Bellman balance before any chart or recurrence argument. |
| Affine equality/Farkas alternative | `MathUE/AffineEqualityFarkas.lean` | A finite feasible-tangent-or-dual-row alternative; strategic decoding and arc lifting are separate inputs. |

Phase-occupation duality is optimization infrastructure.  Until a concrete
strategic construction supplies a feasible phase occupation, it is not itself
a game or strategy producer.

## Closure and transfer

- `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform/AsymptoticPayoffEquivalence.lean` transfers an exact target across
  profile-uniform finite-average payoff gaps tending to zero.
- `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform/ExpectedPotentialShaping.lean` applies that transfer to bounded
  expected-potential coboundaries with an `O(1/T)` endpoint telescope.
- `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform/PayoffExistenceClosure.lean` proves target-free existence closure
  under uniform stage-payoff limits on a fixed finite skeleton.
- `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean` specializes the closure theorem
  to uniformly convergent quitting reward tables.
- `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootPerturbation.lean` gives local one-coordinate payoff and regret
  bounds; it should not be confused with target-free closure.

These tools transport a supplied mechanism or existence result.  They do not
supply density of solved games or construct a missing certificate.

`exists_uniformEquilibriumPayoff_eq_on_image_of_terminalNash_lift`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalNashLift.lean`)
transports every specified child payoff through an exact coordinate-payoff
preserving profile lift whose terminal Nash errors have a fixed multiplier.
One compact selection produces a parent target agreeing at every mapped
child coordinate. Block deletion and capped-clock quiet extension use this
same compactness theorem under their respective hypotheses.
`exists_uniformPayoffWitnesses_eq_on_image_of_terminalNash_lift`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalNashLift.lean`)
strengthens that conclusion: after selecting one parent target, every positive
accuracy has an actual child profile whose literal lift satisfies the Nash and
delivery bounds at every sufficiently long horizon. The indexed-family
acceptance and convergence compilers in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
retain the selected family member; the payoff-existence theorems project these
witnesses rather than making a second selection.

`CappedClockParentRewardCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`)
contains nonnegative weights and finite Never, future, and joining reward
inequalities for one outsider and a finite child set. It allows signed rewards.
`DeadlineWithdrawalRewardCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRaw.lean`)
records the distinct finite deadline-withdrawal N/F/J rows, the zero/passive
withdrawal floor, and separate advance and withdrawal weights. Its
zero-withdrawal subcone reuses the capped-clock consumer.
`deadlineMixedPrivateClockLaw_gain_identity` and
`deadlineMixedPrivateClockLaw_evaluatedGain_identity`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalMixedLaw.lean`)
construct the legal private-clock coin and prove that its conditional gain,
multiplied by `max(a,b)`, equals the advance gain weighted by `a` plus the
exact deadline-atom withdrawal gain weighted by `b`. Advancing and withdrawal
are selected on disjoint clock events. The independent-product expectation
and full behavioral-debt comparison are proved in the modules below.
`deadlineWithdrawalActualEvaluatedChildGain_tie_ge_floor` and
`deadlineWithdrawal_futureRows_evaluated`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalPointwise.lean`)
give the actual evaluated withdrawal floor on a tied deadline, including
singleton and nonsingleton first coalitions, and the weighted future-row
inequality. The deterministic combination of all N/F/J rows, product-law
expectation, and full behavioral comparison are proved in the modules below.
`deadlineWithdrawalActualEvaluatedOutsideGain_le_weighted_childGains`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalDomination.lean`)
combines all deterministic N/F/J cases. The exact private mixed parent law
and gain identity are in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalMixedMarginal.lean`
and `UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalMixedGain.lean`.
`deadlineWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalFullBehavioralDebt.lean`)
bounds every outsider behavioral deviation for the actual quiet lift at every
nonnegative antitone evaluation by the weighted child debts. Its total-debt
corollary has coefficients `1 + max(a_i,b_i)`. Multiple-outsider certificate
families and a fixed-target uniform-payoff extension are proved by
`quittingLiftDeletedProfile_evaluatedDebt_of_deadlineWithdrawalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalMultipleOutsiderFamily.lean`)
and `exists_uniformEquilibriumPayoff_eq_on_child_of_deadlineWithdrawalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalFixedTarget.lean`).
The latter takes raw certificates for every outsider and an actual child
uniform-equilibrium target; it adds no favorable child profile or root.
`quittingBehaviorEvaluatedMaxDebt_liftDeletedProfile_le_of_deadlineWithdrawal`
and `quittingBehaviorEvaluatedTotalDebt_liftDeletedProfile_le_of_deadlineWithdrawal`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalFamilyDebtBounds.lean`)
give all-evaluation family max and accumulated-sum bounds with explicit
coefficients. `deadlineWithdrawal_terminalPointwise_iff_certificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalPointwiseNecessity.lean`)
identifies the D-N/F/J rows with universal deterministic terminal pointwise
domination for the same fixed nonnegative weight arrays. This is not a
necessity theorem for an arbitrary behavioral-debt bound.
`exists_deadlineWithdrawalSecurity_optimizer` and
`exists_deadlineWithdrawalSecurity_positive_approximation`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`)
construct the finite reward-table LP value and approximate it with a positive
hazard, including when the optimizer is zero. The same module selects a
positive-hazard or Never witness for the nonpositive security floor.
`exists_rational_deadlineWithdrawalSecurity_optimizer` and
`isRationalReal_deadlineWithdrawalSecurityValue`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/RationalWithdrawalSecurityLP.lean`)
give an exact rational hazard/value optimizer and rationality of the canonical
security value for rational reward tables. The optimizer may have hazard zero;
this is not attainment of positive terminal security by a zero-hazard law.
`exists_deadlineWithdrawalSecurity_positive_rational_approximation` and
`exists_rational_deadlineWithdrawalSecurityRestartLaw_terminal_floor`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/RationalSecurityHazard.lean`)
produce a positive rational hazard for arbitrary real rewards and positive
real error. The same actual post-deadline geometric law has rational atoms,
no Never mass, and terminal payoff at least the canonical LP value minus
error against every future opponent tuple. The law is chosen before those
tuples. This approximation does not require rational rewards or a positive
optimizer; it does not assert exact positive-value attainment or finite support.
`DeadlineSecurityPairExamples.zeroSecurity_half_evaluated_guarantee` and
`DeadlineSecurityPairExamples.positiveSecurity_first_restart_date_payoff`
(`UniformEquilibrium/Quitting/Examples/DeadlineSecurityPairExamples.lean`)
instantiate complete two-player child reward tables with a quiet extra
outsider. Own/passive/joint rewards `(0,-1,1)` improve the zero-based floor
from minus one to zero, secured by the same literal half-hazard law for every
nonnegative antitone evaluation. Rewards `(1,1,0)` have LP value one only
at hazard zero. Each positive geometric law secures `1-h`, attained by the
actual first possible opponent date; that same law pays one against opponent
Never, whereas the actual all-Never tuple pays zero. No nonattainment claim
for all private plans or positive all-evaluation security is made.
The generic `exists_nonnegative_rational_solution`
(`MathUE/LinearProgramming/RationalFeasibility.lean`) rationalizes every real
feasible finite weak rational row system, including empty indices and equality
endpoints. `exists_rational_minPrimalOptimal`
(`MathUE/LinearProgramming/RationalOptimization.lean`) supplies rational primal
and dual optimizers with exact zero gap when such an LP is feasible and bounded.
These are existence theorems, not executable optimizer or complexity claims.
`deadlineWithdrawalSecurityRestartLaw_terminal_floor`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityPayoff.lean`)
proves the actual post-deadline geometric private law's terminal payoff floor
against every deterministic future opponent clock tuple; the law and legal
independent replacement are in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityRestart.lean`.
`exists_deadlineWithdrawalSecurityEvaluatedPlan`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityEvaluatedPlan.lean`)
selects one actual post-deadline law, independent of the evaluation and
opponent clocks, securing the nonpositive floor `min(gamma,0)` for every
nonnegative antitone evaluation. `DeadlineSecurityRewardCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityMixedRaw.lean`)
states the improved literal N/F/J reward rows. The mixed restart's exact
gain identity, product marginal, and expected gain comparison are proved in
the intervening `DeadlineWithdrawalSecurityMixed*` modules.
`deadlineSecurity_quietLift_outsideBehaviorDebt_le_weighted_childDebt` and
`deadlineSecurity_quietLift_totalBehaviorDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityMixedFullBehavioralDebt.lean`)
then bound full behavioral debt of the actual Never lift, for every
nonnegative antitone evaluation, by child debt with coefficients
`max(a_i,b_i)` and `1 + max(a_i,b_i)`. This all-evaluation result uses the
truncated floor `min(gamma,0)`.
`exists_uniformEquilibriumPayoff_eq_on_child_of_deadlineSecurityFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityFixedTarget.lean`)
extends every specified child uniform-equilibrium target under these raw rows.
`quittingGame_exists_uniformEquilibriumPayoff_of_finFour_deadlineWithdrawalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalFinFourExistence.lean`)
and `quittingGame_exists_uniformEquilibriumPayoff_of_finFour_deadlineSecurityFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityFinFourExistence.lean`)
give four-player existence from ordinary or security-enhanced finite-table
certificates for all quiet outsiders and any nonempty proper child. Both
produce the child target using the existing one-, two-, and three-player
existence results; neither assumes a favorable child strategy, target, or cap.
The raw certificates remain hypotheses, not certificates supplied for every
four-player game.
`deadlineSecurityTerminal_outsideBehaviorDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityTerminalDebt.lean`)
proves the full terminal debt comparison from literal untruncated `gamma`
rows. It constructs an actual private restart for every positive error,
compares each response with the unrestricted behavioral cap, and then removes
the error. The security value need not be attained by one restart law.
`quittingLiftDeletedProfile_debt_of_deadlineSecurityTerminalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityTerminalFamily.lean`)
transfers the comparison through exact deletion and reindexing for every
outsider simultaneously, with unchanged child debts.
`exists_uniformEquilibriumPayoff_eq_on_child_of_deadlineSecurityTerminalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityTerminalFixedTarget.lean`)
extends every specified child target to one fixed parent UE payoff agreeing
at all child coordinates. Its finite amplification is the maximum of one
and the outsiders' total debt weights.
`quittingGame_exists_uniformEquilibriumPayoff_of_finFour_deadlineSecurityTerminalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityTerminalFinFourExistence.lean`)
supplies the actual child target from low-cardinality existence. Thus literal
untruncated security rows suffice for Fin4 existence, without a selected
strategy or target as input. These terminal results do not assert the
positive-security bound for arbitrary horizon evaluations or that every
table has such rows.
`isεAsymptoticNash_quietLift_of_outsideTerminalDebtBounds`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/TerminalWeightedDebtLift.lean`)
is the shared approximate-Nash assembly for ordinary, truncated-security,
untruncated-security, and patient extensions. It also permits empty child or outsider
sets; the raw security producers impose their own child requirements.
`PatientWithdrawalRewardCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalRaw.lean`)
records the separate patient-withdrawal rows with the favorable late-own-quit
alternative on all-Never opponents. Its response coefficients add, rather
than taking their maximum.
`patientWithdrawalPrivateReplacement_childProduct`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalLaw.lean`)
constructs the actual independent private replacement: it retains earlier
own clocks, otherwise uses a finite late date for a nonnegative singleton
and Never for a negative singleton. The actual patient payoff-limit and
full-debt comparison use separate steps.
`patientWithdrawal_expectedTerminalPayoff_tendsto`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalExpectedLimit.lean`)
proves convergence on the fixed original-clock and outsider-replica sample.
The limit retains the favorable own singleton payoff on opponent Never;
weak convergence of the late-date laws to Never is not their payoff limit.
`patientWithdrawal_expectedTerminalPayoffLimit_le_behaviorDeviationCap`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalFullCap.lean`)
bounds every actual finite-delay payoff by the unrestricted behavioral cap
before passing to the limit.
`patientWithdrawal_outsideBehaviorDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalFullBehavioralDebt.lean`)
integrates the actual pointwise comparison and bounds unrestricted outsider
debt with the sum of the two response weights. No attained response or
favorable cap is assumed.
`quittingLiftDeletedProfile_debt_of_patientWithdrawalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalFamily.lean`)
controls every quiet outsider simultaneously and preserves every child debt.
`exists_uniformEquilibriumPayoff_eq_on_child_of_patientWithdrawalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalFixedTarget.lean`)
extends each specified child target to one fixed parent payoff.
`quittingGame_exists_uniformEquilibriumPayoff_of_finFour_patientWithdrawalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalFinFourExistence.lean`)
constructs the child target from low-cardinality existence. These are raw
reward-certificate classes, not a theorem that every Fin4 table passes.
They make no finite-evaluation claim for the favorable patient Never floor.

`cancellationStoppingClock` and
`cancellationPrivateReplacement_childProduct`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CancellationWithdrawal.lean`)
retain earlier own clocks and cancel clocks at or after a finite private
replica deadline to Never; a Never deadline is the identity. The resulting
replacement law is an actual independent product with unchanged opponents.
`cancellationWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CancellationWithdrawalFullBehavioralDebt.lean`)
bounds every complete outsider deviation at every nonnegative antitone
evaluation, for any actual child profile under its raw cancellation N/F/J
certificate. The coefficients are the SUM of advancing and cancellation
weights. Its floor is zero-based, not the patient late-own-quit alternative.
`exists_uniformPayoffWitnesses_eq_on_child_of_cancellationWithdrawalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CancellationWithdrawalFixedTarget.lean`)
retains actual quiet lifts at one fixed parent target agreeing with the
specified child target. The corresponding Fin4 source consumer
`quittingGame_exists_uniformPayoffWitnesses_of_finFour_cancellationWithdrawalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CancellationWithdrawalFinFourExistence.lean`)
produces that child target internally for a nonempty proper child and raw
certificates for every outsider; it does not assume a favorable profile.

`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`)
covers the patient, ordinary deadline, evaluated-security, terminal-security
and cancellation F/J-only systems. It retains the explicit positive-part
Never-row residual times the ACTUAL child joint-Never mass. Patient and
cancellation use summed response weights; the other three use their maximum.
The patient residual also retains its late-own-quit Never bonus.
`withdrawalFutureJoin_quietLift_outsideDebt_le_of_positiveSingleton` in the
same file charges residual divided by one actual positive child singleton
to that pivot's terminal debt. Zero joint-Never mass removes the residual
without a singleton-sign assumption. All these relaxations are TERMINAL-only.
`exists_uniformPayoffWitnesses_eq_on_child_of_withdrawalFutureJoinFamily` and
`quittingGame_exists_uniformPayoffWitnesses_of_finFour_withdrawalFutureJoinFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`)
preserve actual quiet lifts and the fixed target, allowing different kinds
for different outsiders and requiring a positive actual child singleton.
The Fin4 wrapper constructs the child target internally. An outsider-only
terminal reward shift keeps Never zero and carries an explicit joint-Never
correction; it is not arbitrary-profile strategic equivalence.

`exists_terminalProfile_smallExploitability_smallNever_of_nonnegativeSingleton`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/NonnegativeSingletonEarlyAbsorption.lean`)
selects an actual original-game child profile from cardinality at most three,
one nonnegative own singleton, and any positive delta. The same laws have full
terminal exploitability at most `delta + delta²` and joint Never at most `delta`.
It increases only that singleton coordinate, applies the existing low-player
producer, and returns the same profile through the sharp one-sided reward
transport in `UniformEquilibrium/Quitting/Terminal/TerminalPayoffRewardOrder.lean`.
No child target, favorable law, or perturbed outsider certificate is assumed.
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`
and `exists_quietProfiles_smallExploitability_smallNever_of_withdrawalFutureJoinFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`)
retain the original certificate residual for every actual child profile, then
select fixed finite maximum weight and residual bounds before the positive scale.
The selected quiet parent has full terminal exploitability at most
`factor * (delta + delta²) + residual * delta`, with the same child joint Never
at most `delta`. Outsiders may independently use any of the five certificate kinds.
`exists_finiteQuietProfiles_of_withdrawalFutureJoinFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFiniteQuietSource.lean`)
selects actual finite independent child menus with positive deadlines, parent regret
at most `(factor + residual) * delta + (factor + 4 * bound) * delta²`, and child
joint Never at most `delta + delta²`. The parent reward bound may be supplied.
The censor is applied only to finite child tails; quiet outsiders remain Never.
Its law-level commutation and exact discarded-mass identity are in
`UniformEquilibrium/Quitting/Classification/QuietExtension/QuietLiftFiniteCensor.lean`.
`exists_uniformFiniteQuietFamily_of_withdrawalFutureJoinFamily` in the same source
owner selects one payoff target from one indexed family of those finite quiet lifts.
Both full regret and child joint Never converge to zero; every requested uniform
accuracy retains a member of that same family. The generic existence facade and
`quittingGame_exists_uniformEquilibriumPayoff_of_finFour_nonnegativeWithdrawalFamily`
cover the nonnegative singleton boundary, including zero. They do not strengthen
the specified-child-target theorem or supply certificates for arbitrary Fin4 games.

`smallPivotRepairValue_of_deleted_nonnegativeSingleton_withdrawalFamily`, its
single-deleted-pivot specialization, and its Fin4 corollaries
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalSmallPivotRepairSource.lean`)
retain the finite nonpivot marginals and feed their actual quiet full profile into
the existing pivot-repair LP. The source supplies arbitrarily small objective values;
no optimal-pivot compatibility hypothesis is assumed. The repair pivot is any
parent player and need not be deleted or equal the child's nonnegative-singleton
owner. The Fin4 existential facade requires only one nonnegative surviving
singleton. Fin4 normalization with one own singleton equal to one and the others
zero satisfies that sign premise.

The omitted-Never supplied-profile obstruction is already proved by
`neverResidual_outsideDebt_gt_weighted_childDebt`
(`UniformEquilibrium/Quitting/Examples/WithdrawalNeverBoundary.lean`).
`NegativeSingletonQuietBoundary.debts_eq_childClockMasses`,
`NegativeSingletonQuietBoundary.quietLift_exploitability_ge_half`, and
`NegativeSingletonQuietBoundary.outsiderQuitProfile_exactNash`
(`UniformEquilibrium/Quitting/Examples/NegativeSingletonQuietBoundary.lean`)
separately prove the negative-sign obstruction: zero-weight original certificates
exist for every withdrawal kind, but each actual quiet lift has regret at least
one half. Its child debt is the finite-quit probability and outsider debt the Never
probability. The same finite parent has an exact terminal Nash profile with an
outsider quitting at date zero. A literal Fin4 instance is included. This is not
a counterexample to uniform-equilibrium existence.

The literal Fin4 prescribed-child-target boundary is proved by
`PrescribedChildTargetQuietBoundary.one_le_three_exploitability_add_childPayoffs`
and `PrescribedChildTargetQuietBoundary.no_quiet_uniformWitnesses_extending_zeroChild`
(`UniformEquilibrium/Quitting/Examples/PrescribedChildTargetQuietBoundary.lean`).
Every actual quiet profile satisfies one less than or equal to three times its
full exploitability plus its two child payoffs. Therefore vanishing-regret quiet
profiles cannot deliver the prescribed child target zero. The uniform-witness
obstruction retains the same quiet profiles through the finite-horizon limits.
The restricted child's all-Never profile is an exact zero-payoff equilibrium,
whereas the two alternative child targets `(0, 1)` and `(1, 0)` have exact quiet
parent equilibria. Both literal outsiders admit all five original zero-weight
certificates. This obstructs preservation of an arbitrary child target, not
selection of some quiet target or parent uniform-equilibrium existence.
The arbitrary-law payoff identity `quittingTerminalPayoff_soloStoppingLaw_eq`
(`UniformEquilibrium/Quitting/Paths/SoloStoppingLawPayoff.lean`) supplies the
actual child Never-deviation payoffs without finite-support restrictions.

`quietLift_fixedTarget_of_withdrawalFutureJoin_absorbingStationary`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalAbsorbingStationaryChild.lean`)
uses an actual absorbing stationary child equilibrium instead of a positive
singleton pivot. Actual absorption derives zero joint-Never mass; every
outsider may use a different one of the five F/J certificate kinds. The same
quiet parent profile is exact full-behavioral terminal Nash, its actual payoff
is one fixed uniform-equilibrium target, and retained coordinates equal the
child payoff. Signed rewards and empty outsider sets are allowed. The endpoint
facade `quietLift_fixedTarget_of_withdrawalFutureJoin_stationaryEndpoint` in
the same file retains the actual Bellman, endpoint and Never-boundary premises.
These terminal-only adapters do not produce a child equilibrium or assert
all-evaluation domination. The named module and full integration closure pass
their silent builds.

`exists_rational_patientWithdrawalRewardCertificate`,
`exists_rational_deadlineWithdrawalRewardCertificate`,
`exists_rational_deadlineSecurityRewardCertificate`,
`exists_rational_deadlineSecurityTerminalRewardCertificate`,
`exists_rational_cappedClockParentRewardCertificate`, and
`exists_rational_cappedClockParentFutureJoinCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/RationalWithdrawalWeights.lean`)
replace real feasible weights by exact rational nonnegative weights for their
respective literal reward-row systems when all reward entries are rational.
Zero weights, boundary floors and equality rows are retained. Feasible weights
remain an input; these adapters do not certify every game or perform a search.
`exists_rational_cancellationWithdrawalRewardCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/RationalCancellationWithdrawalWeights.lean`)
and `exists_rational_withdrawalFutureJoinRewardCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/RationalWithdrawalFutureJoinWeights.lean`)
supply the cancellation and all-five-kind F/J-only rational counterparts.
They retain weak equality rows, zero weights and empty indices, rationalizing
actual table-derived floors and gains rather than assuming a rational optimum
for an arbitrary real table.

`selectNonnegativeRationalFeasible` and `selectRationalPrimalDual`
(`MathUE/LinearProgramming/ExecutableRationalSelection.lean`)
are executable exact rational selectors. The weak-row selector first tests
zero; the primal/dual selector first tests zero-primal/zero-or-unit-dual
candidates. Accepted candidates satisfy the same exact tests; other cases
retain the canonical encodable exhaustive fallback.
Their real feasibility and boundedness proofs are erased, not runtime witnesses;
the latter selector tests actual primal/dual feasibility and exact zero gap.
`ExecutableWithdrawal.securityValue_cast`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/ExecutableWithdrawalSecurity.lean`)
identifies the computed rational security LP value with the actual real value,
including zero-hazard optima. `ExecutableWithdrawal.advancingWeights`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/ExecutableAdvancingWeights.lean`)
computes advancing-only source weights without withdrawal columns.
`ExecutableWithdrawal.fullWeights` and `ExecutableWithdrawal.futureJoinWeights`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/ExecutableWithdrawalWeights.lean`)
compute weights from the actual rational reward coefficients for all five
kinds; a real raw feasibility proof supplies no selected weights or cap.
`ExecutableWithdrawal.fullAmplification_cast` and
`ExecutableWithdrawal.futureJoinAmplification_cast`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/ExecutableWithdrawalSourceAmplification.lean`)
retain the exact sum-versus-max debt rule, patient Never bonus, residual and
positive-singleton correction in a computed rational source multiplier K.
K is fixed before the requested accuracy.

`rationalQuittingFiniteWordBoundedSearch_eventually_succeeds_of_terminalApproximation`
(`UniformEquilibrium/Quitting/Root/RationalFiniteWordSearch.lean`)
derives termination from actual approximate terminal-equilibrium existence,
using full-cap finite-calendar approximation and rational density. The
low-player producer `rationalQuittingFiniteWordSearchOfCardLeThree_finiteLaws`
(`UniformEquilibrium/Quitting/Root/RationalLowPlayerFiniteWordSearch.lean`)
obtains that existence internally, including zero players and zero-length
words. The exact evaluator keeps gap-date and late replies and Never;
it is not a stationary-only test or a prescribed-target oracle.
`ExecutableWithdrawal.fullWord_finiteLaws` and
`ExecutableWithdrawal.futureJoinWord_finiteLaws`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/ExecutableWithdrawalQuietFiniteWords.lean`)
start with an actual rational parent table, decidable deletion, a nonempty
child labeled by at most three players, nonempty outsiders and raw feasible
certificates. They compute K before accuracy and select the CHILD word at
the exact rational accuracy/K. The parent laws keep the same child dates
and every exact rational child atom, and every outsider law is literally
Never. Parent terminal debt is strictly below the requested accuracy for
every complete behavioral deviation. The F/J-only version requires an actual
positive child singleton for its pivot correction. These accuracy-only word
selectors compute neither a fixed real UE target nor a complexity bound;
they do not decide infeasibility or certify every reward table.
`exists_rationalWithdrawalFutureJoin_quietFiniteWordLaws`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/RationalWithdrawalFutureJoinQuietFiniteWords.lean`)
also retains all five kinds' exact rational weights and one rational K before
every accuracy, then the same child word and parent laws. This existential
rational wrapper is distinct from the computed source weights/K frontend.

`WithdrawalBoundaryExamples.patientOnly_no_deadlineCertificate` and
`WithdrawalBoundaryExamples.deadlineOnly_no_patientCertificate`
(`UniformEquilibrium/Quitting/Examples/WithdrawalRawIncomparability.lean`)
separate the two raw cones using complete literal reward tables and actual
passing certificates. The patient-only table also excludes both security
deadline variants. These raw compiler obstructions are not no-UE claims.
`WithdrawalBoundaryExamples.patient_deadline_incomparable_on_fixed_twoPlayerChild`
in the same file puts both separations on the same two-player child subset
inside the same three-player label type. It also excludes both security
variants on the padded patient-only table. The two restricted child reward
tables need not coincide; no strategic padding equivalence is asserted.
`patient_horizon_three_bound_fails`
(`UniformEquilibrium/Quitting/Examples/PatientWithdrawalFiniteHorizonBoundary.lean`)
exhibits a passing terminal patient certificate whose actual horizon-three
outsider debt is `2 / 3`, exceeding the weighted child debt `1 / 3`.
`patient_discounted_bound_fails`
(`UniformEquilibrium/Quitting/Examples/PatientWithdrawalDiscountedBoundary.lean`)
uses the same actual child profile and Never lift. For every `0 < d < 1`,
the outsider's evaluated debt `d` exceeds the weighted child debt
`max (d - d^2) (d^2)`. The evaluation is the packet's clock weight `d^(t+1)`;
the semantic discounted stage bridge below identifies that weight with
the standard normalized stage-series evaluation. Both comparisons use
unrestricted behavioral caps, not a retained finite response menu.
`quittingDiscountedPayoff_eq_stoppingLawEvaluatedPayoff` and
`quittingDiscountedPayoff_update_eq_behaviorEvaluatedPayoff`
(`UniformEquilibrium/Quitting/Paths/DiscountedStoppingLawPayoff.lean`)
identify the ACTUAL normalized discounted expected stage series with
first-absorption evaluation `d^(t+1)` for every profile and complete unilateral
update when `0 ≤ d < 1`, on a finite nonempty player set. Signed rewards and
joint Never remain literal. `quittingDiscountedDeviationDebt_eq_behaviorEvaluatedDebt`
(`UniformEquilibrium/Quitting/Paths/DiscountedBehavioralCap.lean`)
retains the supremum over ALL behavioral replacements.
`patient_discounted_stage_bound_fails`
(`UniformEquilibrium/Quitting/Examples/PatientWithdrawalDiscountedStageBoundary.lean`)
therefore states the same strict failure for actual normalized discounted
stage payoffs and complete discounted debt for every `0 < d < 1`.
`WithdrawalBoundaryExamples.neverResidual_outsideDebt_eq_residual_times_childJointNever`
(`UniformEquilibrium/Quitting/Examples/WithdrawalNeverBoundary.lean`)
uses the canonical actual one-child profile with zero child rewards: all five F/J kinds
pass with zero weights, child debt is zero, child joint-Never is one, and
both the exact outside debt and residual equal one. No positive child
singleton exists. Dropping the residual is false; this is not a no-UE claim.
`exists_uniformPayoffWitnesses_eq_on_child_of_patientWithdrawalFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalFixedTarget.lean`)
and the corresponding ordinary, truncated-security, and terminal-security
wrappers retain the literal quiet lifts as uniform witnesses. Their Fin4
consumers also retain this constraint while obtaining the child target from
low-cardinality existence. Outsiders therefore prescribe Never in each selected
uniform profile, not merely in a sequence of terminal approximants.
`StrictPatientWithdrawal.outsideDebt_le_of_dist_lt`
(`UniformEquilibrium/Quitting/Examples/StrictPatientWithdrawalNeighborhood.lean`)
proves, for every actual child profile throughout the full sixty-coordinate
radius-`1 / 100` reward ball, outsider debt at most half player zero's child
debt plus three times player two's. The same displayed weights use freshly
computed floors, and full exploitability amplifies by at most `7 / 2`.
`StrictPatientWithdrawal.every_proper_child_no_certificates_of_dist_lt`
(`UniformEquilibrium/Quitting/Examples/StrictPatientWithdrawalAdvancingExclusions.lean`)
excludes both full and Never-omitting advancing-only certificates for all
fourteen proper nonempty children, using actual joining-row witnesses.
This is certificate separation, not equilibrium nonexistence.
`StrictPatientWithdrawal.degree_response_and_uniformPayoff_of_dist_lt`
(`UniformEquilibrium/Quitting/Examples/StrictPatientWithdrawalFullScope.lean`)
derives degree one, injectivity of every response-invariant block map, and a
uniform-equilibrium payoff for the same changed table at the same radius.
The UE producer consumes the patient rows, not the degree conclusion.
`StrictPatientWithdrawal.ambientDegree_one_of_dist_lt` in that file also
states intrinsic singleton-min-map degree one on every bounded open
neighborhood of the origin. The underlying inverse and residual witnesses
are literal source calculations, not supplied matrix or partition certificates.
`StrictPatientWithdrawal.actualValue_uniformPayoff`
(`UniformEquilibrium/Quitting/Examples/StrictPatientWithdrawalOneDateProfile.lean`)
retains the center's actual one-date hazards `(1 / 2, 2 / 5, 1, 0)` and Never
tail at payoff `(0, -1, -2 / 5, 7 / 10)`. The same profile works for all
accuracies; its full cap and every positive finite and Never reply are checked.
`StrictDeadlineWithdrawal.outsideEvaluatedDebt_le_of_dist_lt`
(`UniformEquilibrium/Quitting/Examples/StrictDeadlineWithdrawalNeighborhood.lean`)
gives outsider debt at most player zero's child debt plus twice player two's
for every actual child profile and every nonnegative antitone clock evaluation
throughout the full sixty-coordinate radius-`1 / 512` reward ball. Fresh
zero-or-passive floors retain the displayed weights; maximum debt amplifies
by at most three. Its fixed-target consumer obtains the child equilibrium
internally and retains the actual quiet lift.
`StrictDeadlineWithdrawal.degree_response_and_uniformPayoff_of_dist_lt`
(`UniformEquilibrium/Quitting/Examples/StrictDeadlineWithdrawalFullScope.lean`)
combines independent degree-one, response-partition exclusion and UE
conclusions for that same changed table. UE follows from the deadline
certificate, not from degree one. Its ambient singleton-min-map degree
statement covers every bounded open neighborhood containing the origin.
`StrictDeadlineWithdrawal.actualValue_uniformPayoff`
(`UniformEquilibrium/Quitting/Examples/StrictDeadlineWithdrawalOneDateProfile.lean`)
retains the literal hazards `(1 / 2, 1 / 3, 1, 0)` followed by Never, at
actual payoff `(2 / 3, -9 / 16, -11 / 48, 23 / 16)`. The complete behavioral
cap equals that payoff, and the same profile uniformizes at every accuracy.
The sure player's Never payoff `-17 / 24` differs from every positive finite
deadline payoff `-35 / 48`; the negative singleton correction is retained.
`StrictDeadlineWithdrawal.every_proper_child_split_exclusions_of_dist_lt`
(`UniformEquilibrium/Quitting/Examples/StrictDeadlineWithdrawalAdvancingExclusions.lean`)
excludes every proper child's full advancing-only certificate throughout the
same reward ball. Children containing player zero also fail F/J-only; the
others fail the genuine Never row and have strictly negative child singletons.
The latter statement blocks the positive-singleton relaxation without claiming
F/J infeasibility. One obstructing outsider is produced per child. These
are certificate obstructions, not failures of equilibrium existence.
`StrictDeadlineWithdrawal.exists_actualCompletion_uniformPayoff`
(`UniformEquilibrium/Quitting/Examples/StrictDeadlineWithdrawalCompletionRegion.lean`)
allows arbitrary signed values in all thirty-three child-recipient
nonsingleton coordinates while fixing all sixteen singleton entries.
It produces eleven actual outsider-recipient coordinates and a fixed UE
target, using internally computed child floors and the existing quiet-lift
producer. `StrictDeadlineWithdrawal.completionRegion_open_convex_nonempty`
in that file gives a nonempty open convex passing region in those eleven
coordinates for each fixed child vector; membership is exactly strict
N/F/J feasibility for the displayed weights. The coordinate chart is
injective and covers the entire fixed-singleton reward fiber. The region
is not asserted convex in all forty-four coordinates, contained in the
small reward ball, or equal to every possible outsider completion.
Finite pure-time replies against perpetual continuation pay the actual
singleton reward; Never pays zero. Their shared owner is
`quittingTerminalPayoff_alwaysContinueProfile_update_pureTime_some`
and `quittingTerminalPayoff_alwaysContinueProfile_update_pureTime_none`
(`UniformEquilibrium/Quitting/Root/AlwaysContinuePureTimeReplies.lean`), reused
by these examples and the diagnostic cap computations.
`quittingLiftDeletedProfile_outsideTerminalDebt_le_of_oneOutsiderBound`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/TerminalOneOutsiderTransport.lean`)
owns the common exact deletion/reindex transport. This internal consumer
assumes its one-outsider debt bound; the untruncated-security and patient
producers supply that bound from their literal reward rows.
`exists_cappedClockParentRewardCertificate_zero_weight_iff_blockDispensable`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockBlockDeletion.lean`)
identifies the zero-weight case with the exact singleton deletion gate.
This algebraic equivalence also permits an empty child; the equilibrium
extension consumer uses the child nonemptiness assumption.
`cappedClockActualGain_le_iff_rewardRows`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseNecessity.lean`)
characterizes these rows by universal deterministic terminal-gain domination
with the same fixed nonnegative weights. Necessity uses explicit all-Never,
future-coalition, and tied-coalition clock tuples. This is not a necessity
claim for arbitrary behavioral debt bounds.
`cappedClockExpectedActualGain_le_iff_rewardRows`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockExpectationNecessity.lean`)
gives the same characterization for terminal expectation domination over
every coupled child/deadline clock law. Dirac laws recover the deterministic
necessity tests. Arbitrary coupling here is a proof-level comparison of
clock experiments, not permission to correlate players' strategies.

`CappedClockParentRewardRowErrorCertificate` and
`cappedClockActualEvaluatedOutsideGain_le_weighted_actualChildGain_add_rowErrors`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`)
allow separate nonnegative errors in the Never, future, and joining rows.
The deterministic correction retains the actual clock regime: an early
deadline uses the decrease in evaluation weight for the Never error and the
later evaluation weight for the future error. A tied deadline uses only the
joining error. The existing Never-only slack theorem is an exact specialization.
`CappedClockParentRewardAdditiveCertificate` and
`expect_cappedClockActualEvaluatedOutsideGain_le_sum_childExpectations_add_error`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockAdditiveDomination.lean`)
bound a common row error by that error times the evaluation at time zero,
both pointwise and in expectation. The two early-deadline coefficients add
to one evaluation weight; no factor of two is charged.
`outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_error`
in the same file transports this allowance to unrestricted behavioral caps.

`quittingStoppingLawEvaluatedCap_behaviorStoppingLaws_eq_behaviorCap`
(`UniformEquilibrium/Quitting/Paths/StoppingLawEvaluatedPayoff.lean`) identifies
complete-law replacement caps with unrestricted behavioral replacement caps
for clock-evaluated payoffs. Reconstruction preserves these payoffs, and
nonnegative nonincreasing evaluations give finite bounds from the reward table.
The terminal specializations are proved equal to the existing terminal payoff
and deviation cap. This interface does not by itself identify an evaluation
with the existing finite-horizon stage-payoff semantics.

`quittingBehaviorEvaluatedDeviationPayoffCap_eq_pureTime`
(`UniformEquilibrium/Quitting/Paths/EvaluatedPureTimeCap.lean`) gives the exact
unrestricted behavioral envelope over all dates and Never for every actual
clock evaluation between zero and one. Monotonicity is not required. Its
replacement-payoff identity disintegrates the deviator's actual private law;
the reward table supplies the bound used to take the supremum.
`quittingFiniteAveragePayoff_eq_stoppingLawEvaluatedPayoff`
(`UniformEquilibrium/Quitting/Paths/FiniteHorizonStoppingLawPayoff.lean`)
identifies actual finite-stage averages with the first-Quit evaluation
`(H - t - 1) / H`, with truncated natural subtraction and Never equal to zero.
`quittingFiniteHorizonDeviationCap_eq_pureTime`
(`UniformEquilibrium/Quitting/Paths/FiniteHorizonPureTimeCap.lean`) consequently
exhausts the actual finite-horizon behavioral cap with every pure date and
Never, including horizon zero. This is a stage-payoff identity, not only
a comparison of clock experiments.

`outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockEvaluatedFullBehavioralCap.lean`)
bounds the outsider's unrestricted evaluated debt by weighted survivor debts
at the reconstructed quiet parent profile, for every nonnegative nonincreasing
evaluation and every complete tuple of child stopping laws. The proof realizes
each capped-child law as an actual deviation before taking the outsider's
supremum. Its right side uses survivor debts in the parent game.
`quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockEvaluatedChildDeletionAdapter.lean`)
transports this bound to the actual Never lift of every child behavioral
profile, with literal deleted-child debts on the right. Equality of complete
profile stopping laws preserves both evaluated payoff and unrestricted cap;
no equality of off-path behavioral profiles is claimed.
`quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_error`
in the same file gives the corresponding actual-child bound for a common
additive reward-row error. The allowance is the row error times the evaluation
at time zero. Its `quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_rowError`
corollary charges just the row error when that evaluation is at most one.
`quittingBehaviorEvaluatedPayoff_profilePullback` and
`quittingBehaviorEvaluatedDeviationPayoffCap_profilePullback`
(`UniformEquilibrium/Quitting/Classification/PlayerReindexEvaluatedPayoff.lean`)
transport evaluated payoffs and unrestricted caps through player relabeling.
`quittingLiftDeletedProfile_evaluatedDebt_of_cappedClockCertificateFamily`,
`quittingBehaviorEvaluatedMaxDebt_liftDeletedProfile_le`, and
`quittingBehaviorEvaluatedTotalDebt_liftDeletedProfile_le`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockEvaluatedMultipleOutsiderFamily.lean`)
apply every outsider's certificate to the same actual Never lift, preserving
child debts and giving the maximum and sum bounds for every nonnegative
nonincreasing clock evaluation. These are stronger evaluation-wise bounds;
the terminal fixed-target existence consumer below was already complete.
These approximate bounds impose no reward-sign restriction or normalization
of the nonnegative weights. They do not by themselves eliminate a fixed
positive row error to obtain an exact uniform-equilibrium payoff.

`quittingBehaviorEvaluatedPayoff_liftDeletedProfile` and
`quittingBehaviorEvaluatedDeviationPayoffCap_liftDeletedProfile`
(`UniformEquilibrium/Quitting/Classification/PlayerDeletionEvaluatedPayoff.lean`)
prove payoff and full-cap preservation for every survivor under the existing
Never lift. They allow an arbitrary deleted-player predicate and arbitrary
clock evaluation; neither monotonicity nor boundedness is needed for these
equalities. The parent and survivor player types are nonempty. The proof
preserves the actual first clock and quitting coalition and identifies the
entire replacement-law payoff ranges.

`quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockChildDeletionAdapter.lean`)
bounds the outsider's unrestricted terminal debt at the actual Never lift of
every child profile. Survivor debts are preserved.
`exists_uniformEquilibriumPayoff_eq_some_of_cappedClockCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockFixedTargetQuietExtension.lean`)
therefore extends each fixed child uniform-equilibrium payoff without
changing its coordinates.
`quittingGame_exists_uniformEquilibriumPayoff_of_finFour_cappedClockCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockFinFourExistence.lean`)
supplies a four-player uniform payoff from the reward certificate alone,
using the three-player existence theorem for the child. It does not assume
a child profile, a strategic source, or a dispensability gate.

The rational search-to-parent construction is checked separately in Research:
`FinFourRationalCappedClockProducer.exists_rationalAmplification_checkedChildCandidateAt_and_rawParentTerminalNash`
(`Research/Quitting/FinFourRationalCappedClockProducer.lean`). Given any
rational Fin4 table, its owner-reindexed capped-clock certificate, and a
positive rational error, it supplies a rational amplification bound and a
finite child-only checker acceptance at the error divided by that bound.
The accepted code has positive clock and a pure-Never owner. Its canonical
parent profile is terminal approximate Nash for the original table against
every behavioral deviation, with the owner's complete stopping law exactly
Never. Three-player existence supplies the child source; no reward
normalization or finite-calendar bound is assumed. This Research result is
not imported by production.

`CappedClockPairedFamily.exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedFamily.lean`)
applies this criterion to tables with the paired singleton columns and explicit
future and joining inequalities. The certificate uses weight two on one
surviving player. `exampleReward_exists_uniformEquilibriumPayoff` supplies a
concrete rational table, and `not_blockDispensable` proves that every member
fails exact singleton block deletion for every player. The
family theorem assumes only reward-table conditions, not an equilibrium source.
Together with the zero-weight equivalence, its example shows that weighted
certificates admit tables beyond exact singleton deletion.

`CappedClockPairedCompletion.completedReward`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedCompletion.lean`)
constructs a member of this family from an arbitrary four-player reward table.
It preserves all nonsingleton coordinates of the three surviving players,
fixes the paired singleton rows, and fills the remaining quiet-player entries.
The same file proves those preservation statements, the raw family conditions,
and uniform-equilibrium payoff existence for every completed table. Thus these
free coordinates are inputs to a proved constructor, not feasibility hypotheses.

`not_nonempty_balancedSingletonCycleCertificate` and
`not_nonempty_balancedSingletonCycleCertificate_deleteThree`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedCycleExclusion.lean`)
exclude balanced singleton cycles of every period in every member of the
paired family and its deletion-3 child. The fixed singleton columns exclude
every escort edge, so the proof uses the existing escort necessity theorem;
it is not restricted to the displayed rational example.

`HasQuittingPureTimeMembershipToggleGap.exists_behaviorDeviation`
(`UniformEquilibrium/Quitting/Paths/PureTimeMembershipToggleObstruction.lean`)
turns a solo escape from Never and a joining or nonterminal leaving gain at
each nonempty coalition into a uniform gain against every complete pure-clock
profile. The constructed deviation is behavioral, and the pure clocks may
use arbitrary dates and Never. This does not exclude mixed equilibria.
`CappedClockPairedFixtureNoPureTerminal.membershipToggleGap_one`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedFixtureNoPureTerminal.lean`)
supplies a gain of one for the paired rational example. Its mixed one-date
profile nevertheless is exact terminal Nash, as proved by
`CappedClockPairedFixtureTerminal.profile_exactTerminalNash`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedFixtureTerminal.lean`).

`certificate_of_reward_close` and `exists_uniformEquilibriumPayoff_of_reward_close`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedFixtureRobustness.lean`)
preserve the weight-two certificate, and hence uniform-payoff existence,
throughout the fixture's entrywise reward neighborhood of radius below one
sixth. The same module excludes complete pure-clock exact equilibria and
balanced singleton cycles on every principal restriction below radius one
half. Exact singleton deletion and capped joint exit are excluded below
radius one. Its fixed-profile robustness theorem gives only a terminal
Nash error of twice the radius; the nearby uniform-payoff theorem uses the
certificate and does not identify its payoff or profile with the fixture's.

`AdaptiveChildCenterCappedClockObstruction.not_nonempty_cappedClockParentFutureJoinCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/AdaptiveChildCenterCappedClockObstruction.lean`)
proves that every deletion of the existing adaptive-child center fails even
the future/join system without the Never row. That table already has a proved
uniform payoff. Thus failure of all these certificates is compatible with
uniform equilibrium.

`CappedClockParentFutureJoinCertificate` and
`exists_uniformEquilibriumPayoff_eq_some_of_cappedClockPositiveSingleton`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPositiveSingletonQuietExtension.lean`)
drop the separate Never-row inequality when some child own singleton is
strictly positive. The positive part of the Never-row residual, multiplied
by actual child joint-Never mass, is charged to that child's unrestricted
debt. This gives the fixed error multiplier `max(1, sum(weight) + excess/singleton)`
and preserves every coordinate of the specified child target.
`quittingGame_exists_uniformEquilibriumPayoff_of_finFour_cappedClockPositiveSingleton`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPositiveSingletonFinFourExistence.lean`)
supplies four-player existence under this relaxed raw-table criterion.
The shared pointwise and expectation theorems allow an explicit nonnegative
Never-row slack; the exact certificate specializes it to zero. For general
nonincreasing evaluations the correction includes the evaluation drop, so
the terminal relaxation does not assert the same bound for all evaluations.
A decision procedure for these raw classes remains to be supplied.

`CappedClockMissingNeverFixture.liftedProfile_outsiderDebt_eq_one`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockMissingNeverFixture.lean`)
shows why some Never protection is needed: a zero-reward child has an exact
all-Never equilibrium and a zero-weight future/join certificate, but its
actual quiet lift gives the outsider unrestricted terminal debt one.

`not_nonempty_cappedClockParentRewardCertificate_iff_exactLPDual`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockExactLPAlternative.lean`)
characterizes failure of the exact reward criterion by a nonnegative
combination of its actual Never, future, and joining rows, with nonpositive
weighted columns and strictly positive weighted lower bound. The same file
gives rational weights or a rational dual for rational tables.
`exists_rationalNonnegativePotential_iff_exists_realNonnegativePotential`
(`MathUE/DirectedTransport/FiniteInequality/Nonnegative.lean`) proves that
rational finite systems have nonnegative rational solutions whenever they
have nonnegative real solutions. These are certificate-existence theorems,
not an implemented executable LP solver or finite-law equilibrium search.

`quittingBehaviorStoppingLaws_childWithOutsiderFullProfile`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockMultipleOutsiderRestriction.lean`)
proves that retaining the child and one chosen outsider, applying its quiet
lift, and lifting back gives the same complete stopping laws as the direct
child lift. This uses an arbitrary deletion predicate and literal restricted
reward tables. The shared player-reindexing module
`UniformEquilibrium/Quitting/Classification/PlayerReindexNaturality.lean`
proves exact terminal-payoff and unrestricted behavioral-cap transport in
both directions.
`quittingLiftDeletedProfile_debt_of_cappedClockCertificateFamily` and
`quittingLiftDeletedProfile_debt_of_cappedClockPositiveSingletonFamily`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockMultipleOutsiderFamily.lean`)
give survivor debt equalities and every outsider's weighted debt bound at the
same actual lifted profile. The relaxed family permits a separate positive
child singleton for each outsider. Its terminal-Nash error multiplier is
the maximum of one and the corrected outsider weight totals, not their sum.
`exists_uniformEquilibriumPayoff_eq_on_child_of_cappedClockCertificateFamily`
and `exists_uniformEquilibriumPayoff_eq_on_child_of_cappedClockPositiveSingletonFamily`
in that file extend each specified child target while preserving all child
coordinates. The maximum-factor and fixed-target interfaces assume a
nonempty outsider family; the exact criterion also assumes a nonempty child.
No outsider weight is asserted optimal among possible certificates.
`quittingLiftDeletedProfile_debt_of_cappedClockFutureJoinFamily` in the same
file also states the terminal slack bound without a positive pivot: each
outsider's correction is its Never-row excess times the literal product of
the original child profile's Never probabilities. The positive-singleton
bound is derived from this common statement by charging that product to the
chosen child's debt. This slack statement permits an empty outsider family
but still assumes a nonempty child.

## Boundary analysis and diagnostics

`minimumTerminalSemantic_maximumDebt_allPlayersTie` and
`minimumTerminalSemantic_maximumDebt_lt_half`
(`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`)
show that, for unit-bounded rewards and any finite nonempty player type,
every debt coordinate equals the positive global minimum of maximum debt,
and that minimum is strictly below one half. These statements concern
minimum points in the full prescribed-payoff/response-cap carrier. The
module also extends attained actual-profile minima to the carrier and gives
the corresponding actual-profile corollaries. Signed singletons are allowed.
The results do not establish existence of a positive minimum or an attaining
best response. The objective is maximum debt, not total debt.

`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
proves that uniform reward perturbations of size `delta` change each actual
profile's unrestricted response cap by at most `delta`, and its maximum
terminal debt and the global infimum by at most `2 * delta`. The same
behavioral strategies are used at both tables; no response supremum must be
attained. Exact nonnegative scaling laws are also provided.
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in that
module delegates reward-closedness of uniform-payoff existence to
`quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarily_close_rewards`
(`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean`).
The nearby tables' targets may vary; fixed-skeleton payoff closure selects
one fixed target for the limit table.

`quittingTerminalDeviationDebt_oneDateThenNever_eq_expect_of_supported_coherent`
(`UniformEquilibrium/Diagnostics/Quitting/ScreenedMembershipDebt.lean`)
expresses the full behavioral debt as the expected losing-action reward gap
on the original product draws. One sure opponent suffices, and the preferred
action must have a nonnegative directed gap on those draws. The same module
gives the losing-probability times expected-gap identity under the weaker
averaged optimality premise. Neither form assumes root Nash, a global
minimum, reward bounds, or an earlier padding date.

`UniformEquilibrium/Diagnostics/Quitting/MembershipStretch.lean` defines the
literal paired reward stretch, preserving own singleton entries. It proves
the reward bounds and displacement estimate for the constructed table.
A final table may reselect its own singleton entries; with one sure opponent,
supported directed gaps still follow the same original-table stretch.
The displacement estimate is not asserted for that arbitrarily reselected
final table. This module does not construct a worst table or a minimum source.
`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchDebtComparison.lean`
compares full behavioral debts at the same unpadded product root. Under
supported coherent preferences, undoing the stretch cannot increase debt.
For a positive stretch, equal positive debts force every supported directed
gap to be zero or two.
The comparison does not assume a global minimum; applying it to an actual
minimum source still requires the original and final tables and their ordering.
`membershipStretch_sameRoot_minimumEquality_and_supportedSaturation`
(`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchMinimumEquality.lean`)
supplies the global comparison when the final root attains a positive global
minimum, both tables are unit-bounded, and the final infimum is at most the
original one. Two sure quitters and supported coherent preferences are
required. It first proves that the same root attains the original minimum,
then obtains equal player debts and zero-or-two supported gaps. The worst-table
source construction must still supply these hypotheses.
`exists_supported_pureRoot_zeroDebt_of_saturatedGaps`
(`UniformEquilibrium/Diagnostics/Quitting/SaturatedMembershipPureVertex.lean`)
selects one supported deterministic root with zero full behavioral debt.
It requires a sure opponent for each player, supported gaps in `{0,2}`, and
total debt below two. This finite-player statement does not require Fin4
or a minimum hypothesis. It selects a pure profile, not correlated play.
`not_membershipStretch_coherent_positiveMinimum_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/InverseMembershipStretchExclusion.lean`)
rules out supported coherent preferences at a four-player unpadded root
with two sure quitters, under the same positive-minimum, unit-bound and
infimum-ordering hypotheses. It derives the strict-half bound internally
and constructs one supported pure root with zero full debt at both tables.
`exists_twoSureRoot_with_supported_negativeGap_of_membershipStretch_carrierMinimum`
(`UniformEquilibrium/Diagnostics/Quitting/InverseMembershipStretchCarrier.lean`)
realizes a carrier minimum with zero Never and singleton masses by one
two-sure root, preserving the entire payoff/cap pair and terminal law.
Under the same table bounds and infimum ordering, every choice of preferred
actions has a negative original gap on a supported draw.
`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchSupportedReversal.lean`
chooses averaged-best actions from the actual root endpoints. A negative
supported original gap and positive final debts then force opposite strict
supported gaps for one player at both tables. It does not construct the
minimum source or require pointwise optimal actions.
Its actual two-sure positive-minimum theorem chooses those directions and
produces the opposite strict gaps internally from the literal table
correspondence, actual minimum, and infimum ordering.
`exists_sureOwner_strictOptionalReversal_of_membershipStretch_positiveMinimum_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/ThreeSureMembershipReversal.lean`)
specializes the actual minimum comparison to a root with three sure quitters.
It forces the remaining player to mix strictly, and identifies a sure player
whose Continue-minus-Quit gap has opposite strict signs at the two supported
optional configurations, at both reward tables. The same input root is
retained.
`exists_opposedSureOwner_optionalReversals_of_membershipStretch_positiveMinimum_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/ThreeSureOpposedMembershipReversals.lean`)
strengthens this to two distinct sure owners with opposite strict orientations
at both tables. The optional marginal is reselected only in the comparison
argument; its full behavioral debts are recomputed at the new root by
`UniformEquilibrium/Diagnostics/Quitting/SingleOptionalMembershipRows.lean`.
Old-table global attainment is established before applying all-player ties.
`exists_sameOrientation_comparison`
(`MathUE/SignedAffineRowComparison.lean`) supplies the common-probability
comparison for arbitrary indexed signed rows, including the optional
zero-positive row. The exact regression in
`MathUE/SignedAffineRowRegression.lean` has old envelope minimum `25/99`,
strictly above the new contact `1/4`; it is an affine-row example, not a
positive-gap quitting game. The worst-table and singleton-fiber producers
are supplied by
`exists_membershipStretch_singletonFiber_source_of_positiveInf`
(`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchWorstTableSource.lean`).
It selects a whole-cube maximizing original table, one common stretch and a
maximizer on the entire closed own-singleton fiber from a raw positive
behavioral infimum. Reward continuity delegates to the canonical robustness
bound; `UniformEquilibrium/Quitting/OwnSingletonRewardChart.lean` gives the
literal independent coordinate chart, without a payoff translation.
`exists_membershipStretch_source_opposedReversals_of_no_uniformPayoff_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchOpposedSource.lean`)
retains those same witnesses before every attained three-sure root request.
It also retains a positive quantitative floor over all eleven nonsingleton
sure coalitions, invariant under arbitrary own-singleton reselection, from
`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchSureCoalitionSource.lean`.
The exact full behavioral coalition formula and affine-stretch identity are
owned by `UniformEquilibrium/Diagnostics/Quitting/SureCoalitionExploitability.lean`.
No attained three-sure root, elimination of the opposed-orientation branch,
or same-weight common-calendar source is constructed by these results.
`UniformEquilibrium/Diagnostics/Quitting/Regression/MembershipStretchCountBoundary.lean`
gives complete four-player tables testing the pure-vertex count. At the
critical half-debt boundary, every supported pure vertex has nonzero full
debt. Both displayed mixed roots are explicitly proved not to be global
minima: actual all-Never strictly improves their maximum debt.
`UniformEquilibrium/Diagnostics/Quitting/Regression/MembershipStretchTimingBoundary.lean`
keeps all nonsingleton entries fixed while changing one own singleton.
The unpadded two-sure cap remains zero, but one all-Continue prefix restores
that singleton as a deviation payoff. A one-sure root also exposes it.
The full-cap changes are evaluated explicitly, including the zero-to-one case.

`UniformEquilibrium/Quitting/Boundary/Holonomy/All.lean` has two complementary compactness modes.
Fixed-cutoff and fixed-last lifts retain the actual root block, endpoints, and
provenance.  Tangent compactness retains only bounded coefficient coordinates
and normalized safety obstructions.  Neither mode closes the escaping-length
problem: the first cannot compactify unbounded literal length, and the second
does not prove realized-image closedness or provide a decoder.

The general reverse diagnostics are:

- arbitrarily thin eventual payoff/deviation intervals are equivalent to
  uniform-payoff existence;
- a fixed target is uniform exactly when it has a bounded excess-work
  certificate;
- positive tail width and late exploitability gaps give exact nonexistence
  witnesses;
- for finite quitting games, existence of some fixed positive terminal
  exploitability gap is exactly equivalent to nonexistence; and
- convergence of transition kernels alone does not preserve uniform-payoff
  targets.

The checked debt-ratio interfaces separate source mathematics from the Fin4
attachment:

- `quittingTerminalExploitabilityInf_sq_div_two_bound_le_debtSumInf_sub`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticDebtRatioSeparation.lean`)
  proves the global gap `eta^2 / (2 * M)` between positive terminal
  exploitability infimum `eta` and total-debt infimum under reward bound
  `M > 0`; the same module exposes the weaker square-root form.
- `quittingTerminal_exactResponse_debtRatioCrossing`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticDebtRatioResponse.lean`)
  consumes a supplied source, a maximal-debt payer, and an attained complete
  response. It returns exact response gain, zero target payer debt, both
  ordered ratio comparisons, and positive target debt increase. It is not a
  response selector.
- `nonempty_quittingDebtRatioApproximateResponseSource`,
  `QuittingDebtRatioApproximateResponseSource.ratioCrossing_le_liminf_target_debtExcess`,
  and
  `QuittingDebtRatioApproximateResponseSource.eventually_half_ratioCrossing_le_target_debtExcess`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticDebtRatioCarrierResponse.lean`)
  select an actual cofinal carrier sequence with one fixed maximal-debt payer,
  attach literal approximate responses, and give the liminf and eventual-half
  target excess floors without assuming response attainment.
- `exists_eventually_nonempty_finFourDebtRatioResponsePaidCapPort_of_no_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourDebtRatioChamberPaidCapPort.lean`)
  chooses a minimum carrier point from failure of a Fin4 uniform-equilibrium
  payoff and, under `D_* < 2 * eta` and `0 < gamma < eta`, attaches a
  separately selected actual paid-cap port at every sufficiently late target.

The first three layers provide `M` and `L`; the carrier and Fin4 layers
also provide the stated actual-source `A`. No layer has downstream `C`:
the paid-cap trichotomy and its descent-or-inert outputs remain unconsumed.

`QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge` and
`TerminalSemanticGlobalDebtBarrierCertificate.Certificate.floor_le_sum_finiteDeadlineEscapeCharge`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`)
escalate a supplied behavioral realization of a finite-deadline stopping Nash
profile to the unrestricted terminal game.  The only residual charge is the
opponent survival probability to the deadline times the positive singleton
self-reward.  The module is a consumer: it does not construct the finite mixed
Nash equilibrium or its behavioral realization.

The integrated quantile-clock hierarchy gives an escape-aware finite polynomial
lower/upper architecture for the unrestricted terminal problem.
`quittingTerminalSemanticPair_eq_stoppingLawProfile` and
`quittingFiniteClockSemanticReachable_isCompact`, together with
`quittingFiniteClockSemanticReachable_isConnected`
(`UniformEquilibrium/Quitting/Paths/FiniteClockTerminalSemantics.lean`) state the literal
stopping-law reconstruction and compact connected finite-clock center before
any quantile argument.  From a supplied positive global terminal gap,
`exists_quittingFiniteClockDoubleFullGapCosource`
(`Research/Quitting/FiniteClockDoubleFullGapCosource.lean`) uses the connected
clock-one center to produce one actual finite-clock source, two distinct
full-gap debtors, and a pure date-or-Never response attaining each debtor's
unrestricted behavioral cap.  The theorem does not give a chronology or make
the two responses compatible with one Nash--Bellman spine.
`hasEscapeAwareQuantileClockCompression_of_normalized`
(`UniformEquilibrium/Quitting/Paths/CommonQuantileClockTransport.lean`) and
`escapeAwareQuantileClock_normalized_quantitative_bracket`
(`UniformEquilibrium/Quitting/Paths/CommonQuantileClockApproximation.lean`) compress every
actual behavioral profile to a literal finite-clock independent product law,
retain `Never`, control the unrestricted cap, and give the exact general
`2 * n * (n - 1) / M` bracket.  The lower values converge to the true
executable exploitability infimum.  `finiteClockPolynomialSemanticImage_eq_reachable`
(`Research/Quitting/FiniteClockPolynomialCenter.lean`) identifies the exact
real feasible image of the rational marginal-simplex/payoff/cap graph with the
literal finite-clock semantic center.
`exists_finiteClockStoppingLaws_exploitability_le` and
`exists_fin4_calendarUniformStoppingLaws_exploitability_le`
(`UniformEquilibrium/Quitting/Paths/QuantitativeFiniteClockSource.lean`)
internally select actual independent complete stopping laws, bounding their
unrestricted behavioral exploitability by the actual infimum plus twice the
common-quantile radius. For four players, positive level `j` gives support
`8 * j + 1` and error `24 / j`. At a prescribed depth of at least nine,
the error is `24 / (((clock - 1) / 8 : Nat) : Real)` and tends to zero.
The same laws precede every larger calendar, retaining their literal Never
atoms and full behavioral caps. These are actual source producers, not
payoff-only compression, but they do not prove that the infimum is zero or
construct the tilted tester weights. Finally,
`quantileClockLowerQueryFeasible_iff` and
`ratCast_le_quittingTerminalExploitabilityInf_normalized_of_certificate`
(`Research/Quitting/EscapeAwareQuantileClockPolynomialLower.lean`) present the
unboxed multi-center lower query exactly and turn any supplied rational
sum-of-squares polynomial infeasibility identity into a genuine all-behavior
lower bound.  The separate final-shell route now makes its own finite
expression system executable.
`finFourRationalSingleShellProblemValue_eq_finFourSingleShellLower` and
`exists_finFourRationalSingleShellSearch_of_lt_lower`
(`Research/Quitting/FinFourRationalSingleShellLower.lean`) give exact value
equality and strict lower-search completeness.  Complete rational finite-clock
profile enumeration supplies the upper search.  `finFourExactScaleStep` and
`exists_finFourExactScaleStep`
(`Research/Quitting/FinFourExactScaleResolution.lean`) therefore resolve every
positive rational scale of every normalized rational Fin4 table.  A lower
event supplies an actual terminal gap and no-uniform-payoff conclusion; at
zero infimum,
`quittingGame_exists_uniformEquilibriumPayoff_of_finFourExactScale_infimum_eq_zero`
selects one fixed payoff from profiles which may vary with the error.
For a lower event, `finFourExactScaleStep_lower_doubleFullGapCosource`
(`Research/Quitting/FinFourFiniteClockDoubleFullGapCosource.lean`) specializes
the generic co-source at gap `epsilon / 8`, while
`finFourExactScaleStep_lower_exists_checkedDoubleGapCode` finds a finite exact
rational enumeration witness with two distinct literal gains at least
`epsilon / 16`.  The rational payload keeps the two candidates fixed and
preserves their reduced gains; it does not preserve cap attainment under
approximation.
Finally, `exists_finFourCounterexampleStep_iff_exists_real_infimum_pos`
(`Research/Quitting/FinFourCounterexampleSemidecision.lean`) states the global
existential recursive-enumerability equivalence.  The independent checker in
`Research/Quitting/FinFourIndependentCertificateSoundness.lean` derives the
unrestricted infimum lower bound, terminal gap, and no-uniform-payoff result
from the accepted finite tree itself.  On one supplied normalized rational
table with positive unrestricted infimum,
`exists_finFourFixedTableCounterexampleStep_of_infimum_pos`
(`Research/Quitting/FinFourFixedTableCounterexampleSearch.lean`) proves finite
termination of the table-specific scale/stage dovetail.  No positive instance
is produced, the stage search is not a decision procedure for a supplied real
table, and nontermination has no conclusion.  The executable expression/tree
layer is specialized to this exact finite system rather than a general CAD/QE
implementation.

`exists_finiteDeadlineTimingNash_terminalDebt_le` and
`exists_threeDateTimingNash_terminalDebt_le_exactMaximum`
(`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingNashDebt.lean`)
do construct fresh finite timing-game Nash laws, realize their exact Never
atoms behaviorally, and control the full behavioral deviation cap.  The
literal law disintegration, Bellman peel, positive-reach tail-Nash transfer,
and one-step profile-spine identities are stated in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`.
The three-date factor is exactly `20 - 8 * sqrt 6 < 5/12`.  The Research
consumer
`escapeAwareQuantileClockLower_finFour_normalized_eq_zero_of_le_fiftyNine`
(`Research/Quitting/FiniteDeadlineTimingNashDebtHierarchy.lean`) places the
result in the actual finite-clock hierarchy through normalized Fin4 level
`59`; it proves no positive value at level `60`.

The retained-tail variant is checked in
`UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingNash.lean`
and
`UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`.
`IsQuittingRetainedTailFiniteTimingNash.debt_le_deletedReturn_mul_tailDebt`
upgrades supplied finite-stop and pass-through timing inequalities to the
full behavioral deviation cap with the exact player-deleted survival factor.
`hostPunishmentDebt_le` and `punishmentDebt_le` control a literal graft after
replacing its retained tail by one supplied host punishment.  Given a positive
terminal gap, reward bound `R > 0`, and coordinatewise punishment separation,
`terminalGap_retainedTailFiniteTimingNash_jointReturn_ge` gives the exact joint
return floor `gamma^2 / (2 * R * (gamma + 2 * R))`; the named positivity
corollary proves that floor is strict.  A stronger complementary rigidity
layer is checked in
`Research/Quitting/NearMinimumRetainedTailTimingNashIdentity.lean`.
`nonidentity_exactRoot_uniformOpponentAbsorption_ge` gives every coordinate
the same opponent-absorption floor `kappa / (kappa + 2 * M)`, without a
player-cardinality loss.  If the actual tail excess is below
`kappa * D_* / (2 * M)`,
`nearMinimum_rootNashAgainstPayoff_eq_allContinue` forces any exact endpoint
Nash root against its prescribed payoff to be all Continue.
`nearMinimum_literalExactRootStack_eq_replicate_allContinue` propagates this
backward through a supplied `IsQuittingLiteralExactRootStack`.  The missing
normal-form recursion is now checked in
`UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingRealization.lean`:
`quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff` retains the
literal behavioral tail, `retainedTimingLawTail_isNash_of_isNash_of_positiveContinue`
and `retainedTimingCurrentRoot_isZeroEndpointNash_of_isNash` give the credible
conditional suffix and current root, and
`nearMinimum_retainedTailFiniteTimingNash_eq_pureNeverProfile` makes every
positive-`Never` near-minimum mixed Nash law literally pure `Never`.  This
generic no-go has `M` and `L`.  No theorem derives the separated actual tail
and coordinate punishments from the Fin4 source, converts every selected mixed
Nash law into the retained-tail return-floor certificate, obtains positive
joint `Never` mass, or packages the eventual Fin4 identity no-go.  Thus there
is still no Fin4 `A` or `C`, prescribed-payoff/cap closure, or uniform-equilibrium
conclusion.

The local periodic-anchor route has two separate Research interfaces.
`localPeriodicAnchor_theoremA`
(`Research/Quitting/LocalPeriodicAnchorObstructions.lean`) consumes the
explicit minimum-tube, hazard, and positive-absorption hypotheses for one
supplied cyclic root family and returns an unrestricted behavioral
exploitability gap of `eta / (2 * card(I))`; it is a conditional obstruction,
not a producer of cyclic roots from an arbitrary game.  The generic
finite-cycle estimate `exists_player_base_ge_eta_div_two_card`
(`MathUE/FiniteCycleAggregate.lean`) is game-independent aggregation
infrastructure.  The packet-facing Fin4 theorem
`finFourPeriodicAnchor_false_of_packet_family`
(`Research/Quitting/FinFourPeriodicAnchorResidualAdapter.lean`) consumes a
fixed reward and matrix together with returned product blocks, individual
hazard mesh, eventual uniform value/anchor bounds, positive hazards, and
vector-norm signed-seam convergence; it derives the additive linearization,
extracts a normalized kernel, and contradicts the Fin4 hard residual.  It
does not construct the blocks or those packet hypotheses from arbitrary games.

The Research same-stage endpoint components remain conditional local routes.
`dispatchedClosedSegment_offset_edge_certificate`,
`dispatchedClosedSegment_offset_edge_full_certificate`, and
`dispatchedClosedSegment_offset_literal_profile_update`
(`Research/Quitting/SameStageEndpointMonodromy.lean`) retain, at every offset,
the positive endpoint edge, its full routed-target certificate, and the
literal one-date profile update.  The edge certificate includes the exact
best-action field `QuittingSameStageEndpointEdge.action_eq_best`;
`dispatchedClosedSegment_player_circulation` gives the exact player debt sum
over the period.
`finFourTraceCodeSupport_card_eq_period`,
`finFourTrace_stageMass_ge_liveMass`,
`finFourTrace_offset_gain_certificate`, and
`finFourTrace_common_or_complementary_exact`
(`Research/Quitting/FinFourSameStageEndpointMonodromy.lean`) transfer support
cardinality and an all-offset live-mass floor to the Fin4 trace, give an
action-certified gain of at least `lambda * debt / 8` at every offset, and
make the complementary-pair conclusion an exact Fin4 complement equality.
`finFourTrace_period_le_eight_and_geometry` gives the ordered-cycle bound and
common-player/complementary-pair alternative.  The final composition
`quittingPartialPurification_then_finFourSameStage_dispatch` is conditional on
the displayed carrier, minimum-debt, mass, and low-tail hypotheses: it yields a
singleton route or a finite dispatch with this geometry.

The Research-only capstone
`uniformPayoff_or_nonempty_finFourProducerResidual`
(`Research/Quitting/FinFourProducerAtlas/Coverage.lean`) now supplies those
local hypotheses on one selected low-tail row: every bounded Fin4 reward table
has a uniform-equilibrium payoff or one source-carrying member of the six-tag
family.  Every tag retains the same source minimum point and causal atom.  The
minimum-singleton tag closes before row selection but retains the common
source chronology.  The tail-escape tag retains its `SelectedRows` family and
strict subsequence, while the four low-tail tags retain that same family and
one literal low row through the bounded same-date dispatch.
`FinFourTerminalSingletonProducer.exists_singleton_with_stageMass_floor_and_postDateTail_eq`,
`FinFourMonodromyProducer.edge_gain_floor_mu_square_div_sixty_four`,
`FinFourMonodromyProducer.edge_mover_debt`, and
`FinFourMonodromyProducer.edge_stageMass_noLoss`
(`Research/Quitting/FinFourProducerAtlas/Leaves.lean`) expose the terminal
singleton's mass floor with preserved post-date semantics, the exact
`mu^2 D_*/64` cycle-gain floor, exact mover-debt decrease, and no-loss routed
mass.
This result has `M`, `L`, and `A`, but no `C`.  The tags are not a uniqueness or
pairwise-exclusivity theorem, and `FinFourProducerResidual.completionContract`
only names four open obligations.  No recursive descent, rank, backward
compiler, regeneration, chronology return, or downstream uniform-payoff
consumer is constructed.

The stronger same-stage no-go
`sameStageEndpointTrace_false_of_visitedSupport_card_le_four`
(`Research/Quitting/SameStageEndpointMonodromyImpossible.lean`) works on an
arbitrary finite ambient player type: if the union of all coalitions visited
in one simple dispatched period has cardinality at most four, pair vertices
are terminal and exact positive mover-debt subtraction makes the remaining
period impossible.  Its literal Fin4 adapters
`not_nonempty_finFourMonodromyProducer`,
`not_nonempty_finFourCommonHostMonodromyProducer`, and
`not_nonempty_finFourComplementaryPairMonodromyProducer` delete both
monodromy leaves without reselecting the source.  The lossless eliminator
`FinFourProducerResidual.withoutMonodromy` and global theorem
`uniformPayoff_or_nonempty_finFourProducerResidualWithoutMonodromy` retain the
same surviving sources and witnesses in a four-tag residual.  This branch
deletion has `M`, `L`, `A`, and `C`, but it neither consumes the singleton or
tail-escape tags nor proves a uniform-equilibrium payoff or atlas completion.
The packet's five-player sharpness example is not checked in Lean.

The exact boundary regressions are deliberately distinct.  The sharp two-date
table, canonical Nash law, law uniqueness, and exact terminal debt are owned
respectively by
`UniformEquilibrium/Diagnostics/Quitting/TwoDateTimingNashSharpnessCore.lean`,
`UniformEquilibrium/Diagnostics/Quitting/TwoDateTimingNashSharpnessUniqueness.lean`,
and `UniformEquilibrium/Diagnostics/Quitting/TwoDateTimingNashSharpness.lean`.
They give a unique full mixed Nash law and exact unrestricted debt `1/2`.  The
different
fixed-prefix table in
`UniformEquilibrium/Diagnostics/Quitting/FixedPrefixArbitraryTailBarrier.lean`
has an all-behavior suffix barrier `>= 1/4`, but
`prefixTimingGame_not_existsUniqueNash`
(`UniformEquilibrium/Diagnostics/Quitting/FixedPrefixTimingNashNonuniqueness.lean`)
shows that its full two-date timing game is not unique.  Its freshly
reselected same-table profiles have exact debt `2/L` and a fixed uniform
payoff.  Separately, the hard-deadline table has a unique timing Nash at every
deadline, exact debt above `1/4`, and worst-table limit `1/4`, while its own
non-Nash finite-clock family also has vanishing debt.  These theorems exclude
exact hard-tail Nash selection and fixed-prefix tail attachment as universal
vanishing producers; they do not establish a positive all-profile gap.

`TerminalSemanticGlobalDebtBarrierCertificate.Certificate.ofPotential` and
`TerminalSemanticGlobalDebtBarrierCertificate.Certificate.ofApproximatePotentialLimit`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticGlobalDebtBarrierCertificate.lean`)
turn an exact separated Lyapunov potential, or a supplied pointwise limit of
vanishing-error potentials, into a global semantic-debt barrier.  The limit
consumer does not supply the compactness theorem needed to extract a common
limit from a family of finite certificates.

`UniformEquilibrium/Quitting/Debt/Ledger/TruncatedLedgerCapCounterexample.lean` adds a certificate-specific
fence: even a solved two-player zero-solo game need not admit a common-cutoff
truncated-ledger package.  The package compiler is sound, but its hypothesis is
not a necessary normal form for equilibrium existence.

`UniformEquilibrium/Diagnostics/Quitting/CyclicKofNFeasibilityObstruction.lean`
separates the cyclic compiler from a producer: constant, phase-varying, and
player-and-phase positive hazards on a prescribed proper translated block all
fail for one bounded self-membership reward, although that game has a trivial
full-support uniform payoff.  Independently,
`UniformEquilibrium/Diagnostics/Quitting/CyclicKofNSupportedRootRetentionNoGo.lean`
shows that positive retention of one fixed chronological singleton atom over
the finite orbit prefix cannot generate a proper rotating supported-root word.

These characterize or falsify proposed routes.  They are not forward
construction mechanisms.

## Semantic fences

The following distinctions are load-bearing across the toolkit:

1. probabilistic stopped-law accounting is not strategic law realization;
2. a public response or detector is not a credible punishment certificate;
3. positive occupation circulation does not transport a continuation target
   without a separate harmonicity or target-identification theorem;
4. compact coefficient projections do not imply closedness of the set of
   realized strategic blocks;
5. terminal approximate Nash, fixed-profile uniform approximation, and a
   uniform-equilibrium payoff are different notions until a named bridge is
   invoked;
6. a fixed-target closure theorem and target-free existence closure solve
   different problems;
7. positive debt on one explicit legal chain is not positivity of the optimized
   minimum over all chains;
8. the general polynomial Bellman variety is not the physical
   vanishing-discount domain until an explicit slice such as `0 < disc ≤ 1` is
   imposed;
9. a neutral or subsingleton promotion socket—including a vacuous `CellFiber`
   instance—is not realization, compatibility, or an all-accuracy producer;
   and
10. a global occupation that cancels signed defects across different recurrent
    SCCs is not one legal path.  Flow synthesis must choose one reachable
    recurrent component or prove a separate strategic common-randomization
    theorem; and
11. the three branch propositions in
    `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`
    are source vocabulary, not the source characterization.  Nothing states or
    proves the equivalence between existence of approximate equilibria and the
    disjunction of the branches, and the instant-punishment branch is written
    in a constant-row shape that is sufficient for, but not equivalent to, the
    source's.

## Universal declaration leaves

Consult [`STATUS.md`](STATUS.md) for the generated declaration kind of the
general and finite-quitting propositions. The truncated-ledger package is a
valid conditional compiler, while its universal-producer claim is refuted by
the two-player counterexample indexed above. The positive compilers narrow
what a universal producer must supply, but are not silently an arbitrary-game
producer.

For new work, first identify the row above whose required input is closest to
the available data.  If no row accepts it, record the missing adapter or
producer explicitly.  In particular, failed subgame reinsertion should preserve
the entering player or marked join inequality, and failed flow synthesis should
preserve the recurrent component and componentwise separator rather than
creating another parallel compiler surface.
