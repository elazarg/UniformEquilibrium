# Crossed-matching complete-claim audit

## Scope and evidence

This is a declaration-level static audit of the whole
`math/exports/CROSSED_MATCHING_UNIFORM_EQUILIBRIUM.md`, not a compiler or full-build
record. The root reviewer confirmed that no missing main raw producer or weak
reward-closure step was identified. Complete packet coverage does not follow:
its boundary examples and comparison claims are separate obligations.

The established producer, matrix, children, and rate results below have checked
owners in the shared build record. Both the response-quotient and proper-three
stationary results are integrated and passed their targeted checks, the full
silent build and exhaustive production axiom audit. These checks are
build-owner evidence, not compilation performed in this audit. The approved Section 8
boundary-example module is implementation
work, not evidence that the obligations below are already discharged.

## Main producer and semantic coverage

In `UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`:

- `RawSource` and `WeakRawSource` require precisely the singleton comparisons,
  scheduled participant comparison, and twelve outsider caps. Own singleton
  values and unused reward coordinates may be signed; no rates, root certificate,
  target, or favorable inverse is supplied to these raw predicates.
- `exists_exact_cycle_of_standardQ_all_initial` produces one proper hazard vector
  before every initial phase and accuracy, with actual terminal value, full
  behavioral terminal Nash, and uniform-payoff conclusions.
- `exists_uniformEquilibriumPayoff` uses the original-game no-payoff-to-Q theorem
  in the non-Q alternative. It does not claim a proper periodic producer there.
- `WeakRawSource.strictPerturbation`, `singletonPerturbation_distance`, and
  `exists_uniformEquilibriumPayoff_of_weak` implement the twelve-entry singleton
  perturbation and original fixed-target reward closure. This is not convergence
  of a selected periodic strategy.
- `exists_exact_cycle_of_positive_inverse_all_initial` is the separate
  inverse-positive branch; its `InverseRawSource` does not require the favorite
  sign pattern, but does require nonnegative scheduled premiums, nonpositive
  passive increments, negative scheduled gaps, and the caps.
- `exists_uniformEquilibriumPayoff_of_reindexed_strict`,
  `exists_uniformEquilibriumPayoff_of_reindexed_weak`, and
  `exists_uniformEquilibriumPayoff_of_reindexed_inverse` supply the relabeling
  facades.
- `scheduledPair_exact_profile` and `scheduledPair_oneDate_exactHorizon` give
  the pure scheduled-pair alternative, including exact Nash at every finite
  horizon, under the stated participant/cap and two outsider-sign tests.

The actual odds producer is `exists_positive_odds_of_matching_standardQ`
(`MathUE/LinearProgramming/CrossedMatchingPositiveOdds.lean`). It uses the
radius-first inverse bounds and scaled-eigenpoint exclusion, not an assumed
positive root. The additional constant-inverse producer is
`exists_positive_odds_of_positive_inverse`
(`MathUE/LinearProgramming/PositiveInverseTwoPairOdds.lean`). Neither asserts
uniqueness or continuous selection of odds.

`exists_quantitative_cycle_of_standardQ`,
`exists_quantitative_cycle_of_positive_inverse`,
`ExactCycleRates.delivery_printed`, and `ExactCycleRates.deviation_gain_printed`
(`UniformEquilibrium/Quitting/Cycles/CrossedMatchingFiniteHorizon.lean`) cover
the printed delivery and arbitrary behavioral-deviation bounds. The underlying
bounds are stronger than the packet's conservative constants.

### Remaining pure-pair rate output

The exact finite-horizon Nash assertion and a generic M/N delivery bound are
already present; do not reprove them. The remaining public specialized output
is, for the actual one-date pure-pair profile, every player, and every integer
N > 0:

    finiteAveragePayoff(N) = ((N - 1) / N) * r(P),
    |finiteAveragePayoff(N) - r(P)| = |r(P)| / N ≤ M / N.

Here subtraction/division in the displayed ratio are real arithmetic and M
bounds the relevant absolute reward. The date-zero absorption reward is zero.
Keep the positive-horizon guard: the formula is not an assertion about division
by zero at horizon zero.

The rate follows immediately from
`abs_finiteAveragePayoff_sub_terminal_quietAfterDeadline_le`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineHorizonError.lean`) with
deadline 1, `quittingOneDateThenNeverProfile_quietAfter_one`
(`UniformEquilibrium/Quitting/Root/OneDateNeverHorizonNash.lean`), and
`oneDateThenNever_payoff_of_nonempty`
(`UniformEquilibrium/Quitting/Root/PureSureSetExactHorizons.lean`). The existing
same-profile consumer already uses this generic bound internally.

The literal identity needs only a finite-sum adapter to
`finiteAveragePayoff_eq_sum_expectedStagePayoff`, using
`expectedStagePayoff_eq_terminal_of_quietAfter_one`
(`UniformEquilibrium/Quitting/Root/OneDateNeverHorizonNash.lean`) for positive
dates and the existing zero absorbed mass at date zero. This is a public
specialization/finite-sum normalization obligation, not missing mathematical
input or a new finite-horizon estimate. Delivery needs only a nonempty pure
coalition, not Nash or two participants; those stronger assumptions belong to
the exact-Nash consumer.

## Section 8: priority literal regressions

No corresponding literal declarations were located in the existing crossed
fixture owners. These are important boundary tests even though the general
producer is already available:

1. Favorable gap 13/4, harmful gaps -1, premium -1/2, K = 0, arbitrary signed
   singleton vector, cap equalities, and arbitrary unused rewards. Produce
   X = 1, q = 1/2, U = s - 1/4, W = s + 1/2, actual endpoint identities,
   B(X)X = N-positive(X) = 3/2, and the actual exact-profile consumer.
2. Favorable gap 17/4 and K = -1 with the same negative premium. Produce the
   printed values and moved-system value 5/2. Then alter one outsider triple
   reward from 1 to 4 and prove its actual passive Quit endpoint is 7/4 > 3/2,
   so the unchanged profile fails Nash. An endpoint calculation alone should not
   be advertised as an actual strategic counterexample without the consumer.
3. Mixed K = (1, 1/2, -1, -1/2), favorable gaps
   (9/4, 11/4, 17/4, 15/4), premium -1/2, signed singletons and cap equalities:
   exact odds, values, moved-system vector, and failure of both pure scheduled-pair
   alternatives. Preserve the signed source rather than substituting Section 9.
4. H > 2, harmful gaps -1, premium -1, K = 0: positive singleton inverse but
   no positive solution of the original odds equations. Also apply weak UE and
   the pure-pair alternative when the caps hold. This refutes extension of the
   proper producer to the weak boundary, not weak UE existence.

Reuse `passiveEquation` (`MathUE/LinearProgramming/CrossedMatchingOdds.lean`),
the existing `TwoPairOdds` endpoint/value identities, and the actual phase
compiler. No second general odds or behavioral proof is needed.

## Section 9: present coverage

- `reward_rows`, `exact_terminal_and_fixedProfile`, and
  `exists_open_reward_neighborhood`
  (`UniformEquilibrium/Quitting/Examples/CrossedMatchingFixture.lean`) give the
  literal sixty-coordinate source, actual profile, and full reward neighborhood.
- `principal_det_eq`, `matrix_isR0`, `matrix_positive_inverse`, and
  `matrix_r0Degree_eq_one`
  (`UniformEquilibrium/Quitting/Examples/CrossedMatchingFixtureMatrix.lean`) give
  the principal inventory and full-matrix conclusions.
- `exists_unsafe_witness_for_every_proper_child`
  (`UniformEquilibrium/Quitting/Examples/CrossedMatchingFixtureChildren.lean`)
  supplies all fourteen actual child terminal-Nash/zero-Never witnesses and the
  weighted child-debt obstruction. It does not rule out a separately selected
  safe child profile.
- `finiteAverage_delivery_le_printed` and
  `finiteAverage_deviation_gain_le_printed`
  (`UniformEquilibrium/Quitting/Examples/CrossedMatchingFixtureFiniteHorizon.lean`)
  supply the printed fixture rates.
- Integrated, with targeted and full-build checks:
  `affine_responseInvariant_injective_of_nonzero_scale`
  (`UniformEquilibrium/Quitting/Examples/CrossedMatchingFixtureResponseQuotients.lean`).
  It handles all block maps and even signed nonzero player scales. It asserts
  response nonmembership, not strategic or degree invariance under translations.
- Integrated, with targeted and full-build checks:
  `not_exact_stationaryNash_of_three_proper_support` and
  `not_exact_stationaryNash_reindex_of_three_proper_support`
  (`UniformEquilibrium/Quitting/Examples/CrossedMatchingFixtureStationary.lean`).
  These use actual stationary payoff and full terminal Nash; they do not exclude
  full-support stationary profiles.

## Section 9: remaining actual comparison declarations

The following were not located in the crossed fixture owners. Finite arithmetic
already available in those owners should be reused, but does not itself state
these comparisons.

1. Harmful principal pair is R₀ and not Q, with the stated offset witness;
   every triple inverse has negative diagonal entries. Principal determinants
   alone do not discharge the corresponding matrix-criterion nonmembership.
2. Exact trap census 02, 13, and the full set; greatest core equals the full set;
   no pure coalition Nash, including all Never.
3. Product-low and supportwise nonpositive weighted-premium failure; empty
   maximal protected set; global weighted-floor failure; pair-trap and
   larger-trap-charge comparisons; nonnegative terminal-upper-weight chamber
   exclusion for every nonzero nonnegative weight.
4. Concrete singleton-sign exclusions for the old paired schedule, favorable
   Hamiltonian cycle, integral tournament, and every deleted cyclic-child
   pattern, with the stated relabeling/positive-scaling scope.
5. Visible period-three affine-cylinder exclusion through singleton-gap ratios;
   the stated four-phase two-solo floor/Continue obstruction. Do not generalize
   this to arbitrary period-three or four-phase behavioral strategies.
6. Negative lower-face witnesses for every ordered selected pair, with actual
   guard nonmembership adapters, including weak guards and their neighborhood
   producers; the zero-gap comparison with the literal sharpReward family.
7. Conditional-face-range exclusion for every blocker and every permitted
   auxiliary bound, not merely failure of one chosen certificate.
8. Unique eligible scheduled matching and failure, under all eligible labels,
   of the all-nonpositive-passive inverse branch, either pure-pair alternative,
   and common-premium/common-ratio subclasses.
9. The printed Section 9 moved-system numerical vector is not exposed by a
   dedicated literal equality, although its original odds equations and actual
   endpoint consumer are present.

The proper-three and affine-response exclusions have clean targeted checks
and pass the full integration gate; neither status is inferred from adjacent
checked helpers. This does not complete the remaining packet comparisons.
None of these comparisons asserts absence of all stationary, periodic, or child
strategies, or completion of the arbitrary four-player quitting-game problem.
