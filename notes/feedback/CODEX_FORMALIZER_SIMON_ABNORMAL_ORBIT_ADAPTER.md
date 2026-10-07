# Simon's abnormal-player orbit adapter

## Target and source boundary

`question1_affirmative_implies_all_quitting_games`
(`Literature/Simon2012.lean`) asks whether `Question1Affirmative` implies
`HasQuitApproximateEquilibria G` for every finite quitting game `G`, including
games with abnormal players. The conclusion is approximate-equilibrium
existence, not selection of one fixed uniform-equilibrium payoff target.

The primary reference is Simon, *A Topological Approach to Quitting Games*,
Mathematics of Operations Research 37(1), 180–195 (2012),
[DOI 10.1287/moor.1110.0524](https://doi.org/10.1287/moor.1110.0524),
Section 5, pages 194–195. A fresh attempt to read those pages was unsuccessful:
the publisher PDF route redirected to its abstract and the indexed Citeseer
PDF returned HTTP 403. No local full paper was located in the inspected
Literature or notes directories. The earlier source audit in
[SIMON_REMAINING_SOURCES](CODEX_FORMALIZER_SIMON_REMAINING_SOURCES.md)
records a sketch of an artificial boundary modification, not formulas or a
complete verification. This note does not claim a fresh primary-proof read
or that the published assertion is false or mathematically open.

## The consumer distinction that must be preserved

All declarations in this section are in `Literature/Simon2012.lean`.

- `theorem4_1` assumes `Question1Affirmative` and that every player is normal.
  It already constructs the Section 4 data via `lemma4_5`. The unfinished
  numerical `lemma4_4` is not needed by that route.
- `ExtendedUnrestrictedOrbitCondition.hasQuitApproximateEquilibria` also
  explicitly requires `∀ n, IsNormalPlayer G n`. It handles the instant and
  stationarily generated alternatives internally. An unrestricted extended
  orbit for an abnormal game therefore does **not** meet this consumer.
- `ExtendedUnrestrictedOrbitCondition.toExtendedOrbitCondition` requires
  all-normality, failure of the stationarily generated branch, failure of
  the instant branch, and the unrestricted orbit condition. Its rational-tail
  construction cannot simply be reused without the normality hypothesis.
- `ExtendedOrbitCondition.hasQuitApproximateEquilibria` requires only the
  actual `ExtendedOrbitCondition G`. This is the appropriate normality-free
  final consumer. It delegates to the existing periodization direction in
  `Literature/Simon2007.lean`, not its unfinished reverse implication.

The last condition means: for every positive accuracy, produce an extended
orbit of the actual `FRow G accuracy` correspondence, with every point of every
active segment in `IsRational G accuracy`, and with
`HasUnboundedExtendedVariation`. These are genuine correspondence membership,
pointwise rationality, and Euclidean variation obligations; an unbounded orbit
of an unspecified artificial graph is insufficient.

## Existing reusable source components

The following components are already present in `Literature/Simon2012.lean`;
their existing check provenance is recorded in the main Simon source audit.
No new compiler check was performed for this dependency review.

- `minimumAbnormalGap_pos`, `exists_section5Accuracy`, and
  `soloPayoff_add_three_mul_lt_minMaxQuit_of_section5Accuracy` give the finite
  positive abnormal gap and the literal restriction `0 < accuracy < gap / 3`.
- `exists_section5ModifiedC_fullDimensionalPolytopeCover_of_section3Constants`
  supplies a positive finite polytope cover of the literal modified domain,
  retaining normal-player pieces and distinct abnormal-pair intersections.
  Its inputs are the standing player count, payoff scale, positive structure
  parameter at most one, structure-motion parameter, and Section 3 constants.
  Compactness and contractibility are also supplied by
  `section5ModifiedC_compact_contractible_of_section3Constants`.
- `isCompact_section5ArtificialBoundary`,
  `section5ArtificialBoundary_exists_two_low_coordinates`, and
  `section5ArtificialNeighborhood_at_gap_sixth` give the compact artificial
  locus, two low abnormal coordinates, and an actual open collar disjoint
  from the corresponding rational region. Collar disjointness is not an
  orbit-escape theorem.
- `section5SoloSegment_eq_quittingOneStagePayoff`,
  `section5SoloSegment_mem_lowerGlueFiber`, and
  `section5ArtificialBoundary_exists_reciprocal_solo_drift` supply literal
  continuous singleton-response segments and quantitative local drift.
  They do not prove that those segments preserve the modified frontier or
  specify a compatible global homotopy and graph.

Generic reusable topology is in `MathUE/Topology/SimonViabilityQuestion.lean`:
`QuestionOneHypotheses.fullGraph_compact`,
`QuestionOneHypotheses.exists_escapeScale`,
`IsInfiniteOrbit.exists_tendsto_subsequence_of_compact_graph`, and
`ExtendedOrbitData.exists_tendsto_segmentStart_subsequence_of_compact_graph`.
These consume actual graph hypotheses; they do not construct the abnormal
glue or establish its rational-tail property.

## Required implementation specification

After disposing of the already handled instant, stationarily generated,
all-normal, and at-most-two-player branches, the remaining input is an actual
game with an abnormal player and arbitrarily small requested accuracy. The
next substantive construction should have two coordinated outputs:

1. **Actual modified Question 1 data.** Choose the gap-dependent positive
   structure and accuracy parameters internally. On `Section5ModifiedC`,
   construct the straight-line homotopy, compact neighborhood, and compact
   local/full graphs. Prove `Question1Hypotheses` for those literal data.
   In particular, fix the whole modified frontier; ensure that terminal
   diagonal points occur only on that frontier; provide contractible local
   fibers containing their source; include the homotopy image in the full
   graph; and produce one positive common scale for both small-edge inclusion
   and the piecewise distance/nontrivial-segment condition. A cutoff that
   creates diagonal terminal points at interior collar points does not meet
   these hypotheses.
2. **Normality-free orbit transport.** For the same constructed full graph,
   turn the orbit supplied by `Question1Conclusion` into an actual
   `ExtendedOrbitData (FRow G requestedAccuracy)` whose active points are all
   rational, including retained segment starts and stitch points, and whose
   total Euclidean extended variation is unbounded. Any removal of
   artificial edges, segment deletion, or reindexing must preserve these
   properties and the extended-orbit transition requirements. This transport
   must not assume all-normality or merely return
   `ExtendedUnrestrictedOrbitCondition G`. The resulting construction is
   required for every positive requested accuracy; a chosen finite collection
   of good rows does not provide this quantifier or the orbit transitions.

Applying `Question1Affirmative` to the first output and the transport to its
conclusion would supply `ExtendedOrbitCondition G`, after which the existing
normality-free consumer closes the desired approximate-equilibrium claim.
The Section 4 graph-to-orbit bridge is a useful proof pattern, but its
all-normal hypotheses are not discharged by the Section 5 collar facts.

The coupled construction in these two steps was not found among the existing
declarations, and a complete accessible source proof was not obtained in this
review. It should not be assigned as a routine wrapper around the checked
local drift or an assumed favorable graph. The next source request should
ask for the explicit modified homotopy/glue and the rational-orbit transport
verification together; alternatively, a complete independent proof of the
same all-game implication would suffice. No new mathematical proof is asserted
by this implementation specification.
