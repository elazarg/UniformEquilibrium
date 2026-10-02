# Polynomial and premium connections; stopping-law equality bridge

Author: CODEX_ROOT, recording two bounded Astra mining passes on 2026-09-06.
The mining passes were read-only and did not run Lean. Checked implementation
status below is supplied separately by the root's builds.

## Polynomial packet status

The main characterization is pushed in `98ea672`; its boundary examples
passed a silent full build and repository checks in pushed `bc9a439`.
The frozen packet is archived under `math/formalized/`, with full mapping in
`POLYNOMIAL_FORWARD_CERTIFICATES_LEAN_COVERAGE.md`. The independent audit found
no substantive Section 7 omission. No arbitrary-game producer, concrete
negative polynomial, degree bound, or new checking algorithm is claimed.

## Connections worth exposing in Lean

1. The literal three-owner cycle admits explicit periodic payoff theorems.
   The existing polynomial consequence only states payoff existence.
   Use chronological roots `[halfRoot 1, halfRoot 2, halfRoot 0]`, with
   values `[u1,u2,u0]`, in `GameTheory.ThreeOwnerRobustCycle`
   (`UniformEquilibrium/Quitting/Examples/ThreeOwnerRobustCycle.lean`).
   Deleted cycle survival is one quarter for players 0--2 and one eighth
   for player 3. The existing
   `eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff`,
   `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate`, and
   `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
   (`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`) should yield
   each displayed vector as a uniform payoff and actual exact periodic
   terminal Nash. This adapter is proposed, not yet checked.
2. `quittingRowεPerfect_of_tail_close`
   (`UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRootSequence.lean`)
   admits the sharper tolerance `error + distance`, instead of
   `error + 2*distance`. Endpoint-minus-prescribed-value coefficients have
   absolute value at most one. This strengthening is proposed, not yet checked.
3. Removing a nonnegative terminal shift bounded by `t` costs at most `t`
   in terminal regret, not `2*t`. For every prescribed or deviating profile,
   the payoff change is the shift times its absorption probability.
   `quittingTerminalPayoff_playerwiseAffine`
   (`UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean`) supplies
   the exact identity. The sharp nonnegative-shift transfer is integrated in
   `UniformEquilibrium/Quitting/Terminal/TerminalAffineNashTransfer.lean`,
   full-build checked and pushed in `ebd6f6a`.
4. Nonnegative singleton rewards already imply punishment normality, even
   with negative own premiums, by `quittingPunishmentValue_le_max_solo`
   (`UniformEquilibrium/Quitting/Stationary/MinMax.lean`). They do not imply
   punishment equality. This is an existing checked API consequence.
5. The stationary upward-translation estimate already has factor two in
   `quittingRootCoordinateNashDefect_stationaryUpwardTranslate_le`
   (`UniformEquilibrium/Quitting/Stationary/UpwardTranslation.lean`). Do not
   replace it by the general support-local factor-three bound.

## Shared implementation for the premium packets

The weighted support criterion contains the ordered criterion and the global
strictly positive weighting criterion. The game-semantic proof should be
shared through a low active Quit endpoint at each absorbing root. The
normalized weights must be reweighted by the coordinate scales before
renormalizing; keeping the old weights is not valid in general.

The generic row, periodic generator, full-response consumer, and normalization
are full-build checked and pushed in `ebd6f6a`. The original-game theorem
`exists_uniformEquilibriumPayoff_of_supportwiseBalance`
(`UniformEquilibrium/Quitting/Classification/Existence/SupportwisePremiumUniformPayoff.lean`)
applies to every finite nonempty player set with nonnegative singleton payoffs
and the literal supportwise weighted premium condition. No equilibrium source
is an input. The weighting may depend on the support and may have zero entries.
The output of the final extraction retains periodicity and every-suffix
terminal Nash, not a positive absorption floor for the extracted profile.

The ordered packet's all-root boundary equivalence and smooth-drift exclusion
retain nonnegative own premiums. They are separate from its signed-premium
semantic theorem and are not supplied by the weighted criterion alone.

## Infinite overlapping-clock equality

The one-row equality cases are integrated in
`MathUE/Probability/OverlappingFirstStoppingEquality.lean` and
`MathUE/Probability/OverlappingFirstStoppingPositiveContinueEquality.lean`.
The complete infinite-law lift is full-build checked and pushed in `dfdbee8`:
`overlappingMass_sqrt_sum_eq_one_iff_deterministic_or_chronological`
(`MathUE/Probability/OverlappingFirstStoppingChronologicalEquality.lean`).
It includes both mass-one endpoints and all three positive chronological
configurations for arbitrary complete PMFs. The following records its proof
route, not an additional unimplemented requirement.

Use `ScalarHazard.shift` from
`MathUE/Probability/DiscreteHazardConditionalMixture.lean`. Define the two
residual event masses using the stopping laws of the three shifted hazards.
Peel their convergent series at date zero and apply `survival_succ_left` to
obtain `current = current-row pair mass + joint survival * next`.
This identity works at zero joint survival and involves no conditional-law
division. The global inequality already bounds the two next masses.

Feed those actual masses into the positive-continuation one-row equality
theorem. It returns either an all-zero row, preserving both masses, or one
of the two deterministic future endpoints. Extracting equality from finite
truncations is unnecessary and can fail because every truncation may be strict.

The mass-one lemma states that first-and-second stopping
together strictly before the third has probability one exactly when the first
two laws share one deterministic finite atom and the third survives through
that date. Its proof compares each event term with the first atom mass; the
nonnegative deficits have sum zero. One positive atom forces the second atom
and third survival to equal one, and singleton reduction forces the first
atom to equal one as well. It is integrated in
`MathUE/Probability/OverlappingFirstStoppingDeterministicAtom.lean`.

Least-active-date selection, the row equality alternatives, and this mass-one
lemma then give the chronological classification with a strictly later
deterministic date in the positive-continuation case.

The literal maximum over fifteen Fin4 pair projections, its attained crossing,
all-profile exploitability consequence, and complete-clock numerical boundary
examples are also full-build checked in `dfdbee8`. The affine mass bounds are
still supplied hypotheses; projected feasibility is not joint six-coordinate
realizability. The finite-marginal two-supported-maximizer argument is
integrated and full-build checked in `3c6d97a`, both for generic finite
trilinear kernels (`MathUE/TwoCoordinateSparseSimplex.lean`) and literal
finite-date stopping laws
(`MathUE/Probability/FiniteOverlapSparseMaximizer.lean`). The generic theorem
preserves the first expectation and increases the second, so it applies to
any continuous objective monotone in the second coordinate, not just the
square-root objective. Its finite-date feasibility adapter is full-build
checked in `88709a1`;
no exact arbitrary two-mass realization or infinite-support compression is
claimed. The overlap packet is archived with its separate coverage record.

The product-low premium condition now has its own original-game periodic
and uniform-payoff producer, full-build checked in `3c6d97a`; supportwise and
ordered criteria reuse it. Its scope is any finite nonempty player set with
nonnegative singleton rewards. The strict four-player separating family is
full-build checked in `88709a1`; it is not a producer for arbitrary Fin4 games.

Downward closure of product-low premiums under pointwise decreases of
participant premiums is full-build checked and pushed in `c2789f0`:
`hasProductLowQuittingPremium_of_noLargerOwnPremium`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumMonotonicity.lean`).
Passive rewards remain arbitrary. This does not preserve failure of
supportwise balance. The same checkpoint proves that every violation can
be moved inward while preserving its exact active support, via
`not_hasProductLowQuittingPremium_iff_exists_inwardViolation`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumInwardViolation.lean`).
No quantifier-elimination implementation follows from that theorem.

The supportwise packet's full coverage audit passed at `c2789f0`; it is
archived with `math/formalized/SUPPORTWISE_WEIGHTED_PREMIUMS_LEAN_COVERAGE.md`.
The class uses one canonical certificate across its predicate, feasible
set, aggregate inequality, and positive-weight low-player conclusion.

## Additional formalization consequences

The nonnegative-premium class collapse is full-build checked and pushed in
`3ff01be`. In that region product-low, weak support peeling, supportwise
balance, and positive-premium player ranking are equivalent. Consequently
every product-low table outside supportwise balance has a strictly negative
participant premium. These declarations are in
`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSupportPeelingConverse.lean`.

The following additions are full-build checked and pushed in `68a8ccc`.
The full Lean check was silent; trust, imports, proof duplicates, redundant
telescopes, documentation, and diff checks passed:

- `not_differentiable_absorptionDrift_of_nonnegative_productLow`
  (`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSmoothDrift.lean`)
  needs only differentiability at all points of the padded box, not a
  continuously differentiable neighborhood. Signed singleton levels remain
  allowed. The generic lower-boundary argument and singleton exact-root
  construction are separate reusable modules.
- `weakPeeling_iff_every_boxedExactRoot_singletonLowerBoundary`
  (`UniformEquilibrium/Quitting/Classification/NonnegativePremiumBoxBoundary.lean`)
  retains every boxed annotation and every absorbing exact root. Failure
  constructs the strictly interior successor directly. The declared reward
  bound need not separately be assumed nonnegative, and the player type need
  not be assumed nonempty. The independent Astra static audit checked the
  inactive-player constraints, common parameter, and empty-type case.
- `isQuittingNormalPlayer_of_singleton_nonneg`
  (`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`)
  makes item 4 above a literal named theorem with no premium-sign premise.
  Nonnegative own premiums additionally give exact punishment equality at
  every nonnegative singleton, in
  `UniformEquilibrium/Quitting/Classification/NonnegativePremiumPunishment.lean`.
- The fixed-radius floor-free packet producer uses the existing smooth
  capacity separator directly; no polynomial re-encoding is required.
  It keeps one reward-bound-plus-two radius for all positive tolerances and
  nonnegative charges. Floor restoration under nonnegative singletons then
  supplies an independent Fin4 uniform-payoff route, without using the
  periodic approximate-equilibrium producer.

The ordered packet's literal Section 9 payoff-table fixtures are full-build
checked and pushed in `94d58d2`. The packet is archived byte-for-byte with
`math/formalized/ORDERED_QUITTING_PREMIUMS_LEAN_COVERAGE.md`.
None of these consequences is a producer for arbitrary Fin4 games.

## Terminology correction

The copied-response formula in the positive-survival packet is ordinary
mixed-root regret, not supported-action regret. The checked formula and
precise correction are recorded in
`math/feedback/FIN4_POSITIVE_SURVIVAL_ESCAPING_EXACT_CAP_CLOCK__BY_CODEX_ROOT.md`.
The frozen export remains unchanged.
