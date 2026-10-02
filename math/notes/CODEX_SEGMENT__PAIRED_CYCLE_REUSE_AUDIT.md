# Paired-cycle implementation and premium-neighborhood reuse audit

Read-only source audit of
`math/exports/ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_FINITE_SELECTOR.md` and the root
dependency note. This records inspected declaration interfaces and proposed
compositions, not new checked declarations. No Lean checks were run for this audit.

## Highest-value reuse

1. Construct the rectangle zero, then use the exact periodic compiler.
   `Math.Topology.exists_rectangular_zero_of_strict_face_signs`
   (`MathUE/Topology/RectangularPoincareMiranda.lean`) accepts arbitrary finite
   coordinate types and requires globally continuous field data. Define the
   cleared field polynomial directly; agreement with the divided gap is needed
   only on the rectangle, where every denominator is positive.
   `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
   `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
   (`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`) consume exact
   phase recursion, exact phase Nash, and opponent-deleted cycle contraction.
   They already quantify over unrestricted behavioral deviations. Their phase
   argument is arbitrary; literal suffix identification can use
   `quittingCyclicRootSequence_add` from the same file.

2. Do not silently use the stronger rectangular periodic adapter.
   `exists_uniformEquilibriumPayoff_of_periodic_rectangular_face_signs`
   (`UniformEquilibrium/Quitting/Cycles/PeriodicRectangularFaceSign.lean`)
   requires strict inactive gaps for actual cyclic terminal values at EVERY
   rectangle point. The packet proves its value/incentive estimates at the
   simultaneous zero. Therefore direct Miranda followed by `PeriodicCompiler`
   has the matching hypotheses. A useful bounded API generalization would require
   inactive gaps only at common field zeros: the current proof invokes them only
   after selecting such a zero. This generalization is proposed, not checked here.

3. Reuse cap folds for the finite truncation upper bound.
   `quittingContinuationBestResponseValue_literalRootStack_eq_capFold` and
   `quittingFiniteRootWordCap_sub_le_opponentSurvival_mul_posPart`
   (`UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean`) identify
   complete behavioral caps with scalar word folds and bound a positive tail-cap
   discrepancy. In particular, the displayed inequality immediately gives
   monotonicity in the tail cap. The packet's all-Never tail cap is
   `max singleton 0`, bounded by its resumed equilibrium value. Comparing the
   same word over these two tails supplies the upper bound once the literal
   truncation/word identification is installed. This avoids a second full
   behavioral-deviation proof. The early pure-time attainer still needs its own
   bounded Bellman calculation; cap monotonicity alone does not give equality.

4. Reuse literal payoff transport for the geometric identity.
   `quittingTerminalPayoff_literalRootStackProfile_sub_eq_jointSurvival_mul`
   (`UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean`)
   gives the exact difference when the tail is replaced by all-Never.
   `quittingCyclicPrefixWeight_mul_card`
   (`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`) evaluates survival
   over complete turns as a power. Thus the payoff formula needs finite-word and
   periodic-survival identifications, not another infinite-series calculation.

5. Normalize certificates, not finite terminal payoffs.
   `quittingRootSuccessorPayoff_playerwiseAffine` and
   `isZeroQuittingRootNash_playerwiseAffine`
   (`UniformEquilibrium/Quitting/Root/PlayerwiseAffineReward.lean`) transport the
   phase certificate. Opponent contraction is unchanged, so recompiling identifies
   the normalized actual periodic payoff with the affine displayed value. This
   avoids importing any false finite-payoff translation invariance. Apply the
   cap-preserving truncation result afresh to the transformed certificate.

## Important exact-interface distinctions

- The packet scales ONLY the pivot column by the reciprocal pivot singleton;
  other columns are shifted by their own singleton without scaling.
  `quittingSinglePivotNormalizedReward`
  (`UniformEquilibrium/Quitting/Root/SinglePivotNormalization.lean`) instead
  divides EVERY shifted column by the pivot singleton. Use the playerwise affine
  constructor and prove `IsSinglePivotSingletonTable` directly. Otherwise the
  packet's nonpivot bound `6/5` is not the stated bound.
- The normalized pivot bound `5/3` uses the pivot being active in the initial
  pair, hence its initial value is its explicit Quit endpoint. The coarse raw
  value bound `21/10` and singleton lower bound `9/10` alone give only `7/3`.
- The censor is inclusive: `censorLateFiniteStoppingLaw law cutoff` retains
  finite dates at most `cutoff`. For K full cycles of length m, use cutoff
  `m*K - 1` and deadline `m*K`, with positivity from m and K. The law-realization
  theorem `exists_finiteDeadlineTimingLaws_of_censoredLaws`
  (`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineStoppingLawRealization.lean`)
  requires cutoff strictly below deadline. Its companion
  `finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws` preserves the actual
  laws, not merely the prescribed payoff.
- `censorLateFiniteStoppingLaw_none_toReal_eq`
  (`MathUE/ProbabilityMassFunction/ExactLateFiniteCensor.lean`) gives the exact
  Never increment. `exists_finiteDeadlineTimingProfile_approximation`
  (`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`)
  gives only approximate payoff/full-cap control and cannot replace exact cap
  preservation or the packet's displayed geometric laws.
- `singlePivot_fullExploitability_eq_max_menuExploitability_scalar`
  (`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`) accepts
  every actual finite-menu law; exact finite-menu Nash is NOT a premise.
  Consequently the packet's two scalar bounds follow from one full-exploitability
  bound without constructing a new menu equilibrium.
- `sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile`
  (`UniformEquilibrium/Quitting/Cycles/PeriodicRootResponseSystem.lean`) already
  reduces the unrestricted periodic cap to Never and first-cycle pure dates.
  This is useful independent reuse, but alone does not name the packet's first
  active phase as an attainer, nor preserve the cap after censoring.

## Bounded missing helpers, in dependency order

1. Pair indexing/support identities, one-pair endpoint and passive affine maps,
   explicit rational face bounds, polynomial continuity, and the common zero.
2. Displayed phase-value construction with policy recursion, active equality,
   quiet-phase inequality, and opponent-deleted contraction. Compile immediately.
3. A generic literal-word/all-Never cap comparison from the existing cap-fold
   inequality; an early pure-time attainer; and exact censor/live-root identity.
4. Periodic individual stopping-law atoms and Never mass, the actual finite-law
   realization, exact cap/payoff/debt formulas, and geometric accuracy selection.
5. The packet-specific playerwise affine chart and its sharper initial bounds.
   Its finite-average quantitative absorption-time bound is additional to the
   qualitative uniform-payoff compiler and should not be marked covered by it.

## Premium-neighborhood surfaces worth exposing

- A short composition of
  `hasProductLowQuittingPremium_iff_weakSupportPeeling_of_nonnegative`
  (`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSupportPeelingConverse.lean`)
  with `weakPeeling_iff_every_boxedExactRoot_singletonLowerBoundary`
  (`UniformEquilibrium/Quitting/Classification/NonnegativePremiumBoxBoundary.lean`)
  would expose a direct geometric iff for product-low on the nonnegative-premium
  cone. It retains a bounded reward table and a strictly padded box, but needs
  no singleton signs or nonempty player premise. This wrapper is not checked here.
- `hasProductLowQuittingPremium_of_noLargerOwnPremium`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumMonotonicity.lean`)
  applies without nonnegative premiums and without passive-reward restrictions.
  Mutual premium domination therefore gives class invariance under identical
  participant premiums; it does not identify equilibria or their payoffs.
- The paired region is not an application of the nonnegative-premium class
  theorem: its unrestricted remaining rewards can violate global nonnegativity,
  and its active-pair violation already excludes product-low. Its explicit
  equilibrium is a complementary sufficient family, not a stronger class theorem.

No second finite-selector implementation was started. No new mathematical
claims, numerical algorithm, uniqueness, rational root selection, or extension
to odd player sets is supplied by this audit.
