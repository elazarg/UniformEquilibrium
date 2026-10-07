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
build-owner evidence, not compilation performed in this audit. Section 8's
boundary examples and source-free one-date delivery identities are integrated
and have passed their named target checks, the full silent build and exhaustive
production axiom audit. This does not complete the remaining Section 9 comparisons.

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

### Source-free pure-pair delivery

`oneDateThenNever_finiteAveragePayoff_eq_of_nonempty`,
`oneDateThenNever_abs_finiteAveragePayoff_error_eq_of_nonempty` and
`oneDateThenNever_abs_finiteAveragePayoff_error_le_of_nonempty`
(`UniformEquilibrium/Quitting/Root/PureSureSetExactHorizons.lean`) give, for any
actual nonempty one-date pure coalition, every player and every integer N > 0:

    finiteAveragePayoff(N) = ((N - 1) / N) * r(P),
    |finiteAveragePayoff(N) - r(P)| = |r(P)| / N ≤ M / N.

Here subtraction/division in the displayed ratio are real arithmetic and M
bounds the relevant absolute reward. The date-zero absorption reward is zero.
Keep the positive-horizon guard: the formula is not an assertion about division
by zero at horizon zero.

The generic actual-profile identities are
`finiteAveragePayoff_eq_terminal_of_quietAfter_one` and
`abs_finiteAveragePayoff_sub_terminal_of_quietAfter_one`
(`UniformEquilibrium/Quitting/Root/OneDateNeverHorizonNash.lean`). Their finite-sum
proof uses the existing positive-date stage identity and zero absorbed mass
at date zero; the bound delegates the canonical deadline-one estimate.
Delivery needs only a nonempty pure
coalition, not Nash or two participants; those stronger assumptions belong to
the exact-Nash consumer.

## Section 8: literal boundary regressions

`UniformEquilibrium/Quitting/Examples/CrossedMatchingBoundaryExamples.lean`
supplies the following targeted-checked tests, without restricting unused
entries or signed own singletons. The packet's broader Section 9 comparisons
remain separate.

1. Favorable gap 13/4, harmful gaps -1, premium -1/2, K = 0, arbitrary signed
   singleton vector, cap equalities, and arbitrary unused rewards:
   X = 1, q = 1/2, U = s - 1/4, W = s + 1/2, actual endpoint identities,
   B(X)X = N-positive(X) = 3/2, and the actual exact-profile consumer.
2. Favorable gap 17/4 and K = -1 with the same negative premium give the
   printed values and moved-system value 5/2. Altering one outsider triple
   reward from 1 to 4 makes its actual passive Quit endpoint 7/4 > 3/2 and
   gives actual date-zero gain 1/4 and `capViolation_not_terminalNash` against
   the unchanged opponents. `capViolation_not_rawSource` identifies the failed cap.
3. Mixed K = (1, 1/2, -1, -1/2), favorable gaps
   (9/4, 11/4, 17/4, 15/4), premium -1/2, signed singletons and cap equalities:
   exact odds, values, moved-system vector, strictly positive singleton inverse
   via `mixed_positive_inverse`, and failure of both pure scheduled-pair
   alternatives, via `mixed_pair_passive_test_fails`.
4. H > 2, harmful gaps -1, premium -1, K = 0: positive singleton inverse but
   no positive solution of the original odds equations, together with weak UE
   and the pure-pair alternative when the caps hold. This refutes extension of the
   proper producer to the weak boundary, not weak UE existence.

The source-free `balanced_exactFamily` needs only increments at least -1 and
the exact balance, not strict matching signs or Q. Printed strict raw membership
is a separate theorem. `weak_rawSource` requires only H ≥ 0; positive inverse
and no positive original odds use H > 2. `family_unused` retains every
unmentioned coordinate. The proof reuses `passiveEquation`
(`MathUE/LinearProgramming/CrossedMatchingOdds.lean`), `TwoPairOdds` endpoint
identities and the existing actual phase/pure-pair compilers. No second odds
existence or behavioral-deviation proof is supplied or needed.

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
