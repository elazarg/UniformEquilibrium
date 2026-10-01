# Simon: proved components and remaining formalization

The unfinished Lean proofs below remain formalization work. A missing proof
in the repository does not by itself identify a gap in the paper. Specific
source questions and refuted intermediate claims are distinguished where
they arise.

## Corrected Lemma 5

`everyNormalSoloQuitterHarmsNormal_of_not_stationarilyGenerated`
(`Literature/Simon2007.lean`) proves the harm clause without a sign restriction
on the normal quitter's singleton payoff. It reuses the production
stationary-prefix-and-punishment construction, not an open paper theorem.

`exists_compactMotionParameter_of_not_branches` in the same file proves
uniform motion and survival bounds on any fixed compact continuation set,
under failure of the instant and stationarily generated branches. The rate
is chosen before all continuation vectors and product rows.
`exists_correctedUniformMotionAt_of_not_branches` specializes this to the
distance-one feasible neighborhood. The two corresponding 2012 statements
reuse these results with the paper's Euclidean norm; the common payoff,
support, and branch adapters belong to the 2007 file.

The positive-normal-player clause remains: do failure of both branches force
some normal player to have strictly positive singleton payoff? The other two
clauses above do not imply this sign conclusion. An all-Continue stationary
equilibrium is not by definition a stationary-prefix-and-punishment witness.
No general conversion between those two notions is proved by this work.
This records a remaining source obligation, not a counterexample to the
corrected lemma.

## Fixed-start compactness and the nonconvergent-orbit case

`exists_infinite_fRow_orbit_of_finite_orbits` (`Literature/Simon2007.lean`)
constructs one infinite actual orbit from finite actual orbits of every length
in one compact carrier, all starting at the same point. The closed graph is
proved for the paper's support-local one-stage equilibrium rows and actual
payoff map; it is not a supplied graph certificate. Simon (2012) reuses that
owner rather than maintaining a second support-closedness proof.

`EscapeWitness.isCompact_caseCarrier` in the same file derives compactness
of the literal escape carrier from the witness's closedness and distance-one
feasibility condition. The finite-length alternative retains the same start.
It does not equate confined paths with an unrestricted iterate fiber.

`hasQuitApproximateEquilibria_of_nonconvergent_exact_orbit`
(`Literature/Simon2007.lean`) proves Theorem 4's nonconvergent-orbit implication
for all-normal games. One actual nonconvergent exact orbit supplies every
positive-error orbit family; the existing rational-tail, finite-return and
cyclic-profile producers give actual approximate equilibria. No escape carrier,
equilibrium component, five-way equivalence, or unfinished Lemma 5 is used.
The full Theorem 4 still needs the remaining alternatives and their source
construction. Both Simon modules pass silent named checks; separate transitive
axiom checks of the new declarations use only the three standard axioms.

## Extended orbits

`ExtendedOrbitCondition.hasQuitApproximateEquilibria`
(`Literature/Simon2007.lean`) proves the rational extended-orbit-to-equilibrium
direction without excluding either solved branch. Its cyclic-orbit producer
uses bounded-prefix extraction and periodization under failure of the instant
branch; the instant case already supplies approximate equilibria.

`ExtendedUnrestrictedOrbitCondition.hasQuitApproximateEquilibria`
(`Literature/Simon2012.lean`) drops rationality of the supplied extended orbit
when all players are normal. It handles the instant and stationarily
generated branches directly; in the remaining case the checked prefix
removal yields a rational extended orbit. The public equilibrium conclusion
therefore needs neither branch exclusion. The rationalization theorem
retains those exclusions where they are used.

These proofs are independent of the unfinished equilibrium-to-orbit
directions in the full equivalences. Extracting them from the larger proof
bodies removes that unnecessary dependency; it does not prove a missing
forward implication.

The compact-graph cluster machinery is also available independently of the
game-specific localization argument. In
`MathUE/Topology/SimonViabilityQuestion.lean`,
`IsInfiniteOrbit.exists_tendsto_subsequence_of_compact_graph` supplies a
convergent strict subsequence of an ordinary infinite orbit.
`ExtendedOrbitData.point_mem_initial_union_snd_of_compact_graph` puts every
valid extended-orbit point in one compact carrier, handling both finite
endpoint stitches and infinite-segment limits.
`ExtendedOrbitData.exists_tendsto_segmentStart_subsequence_of_compact_graph`
supplies a convergent strict subsequence of actual segment starts when there
are infinitely many segments. These statements do not yet prove that the
cluster is feasible or that an unbounded tail stays in the required payoff
box.

`section4J_target_mem_lowerGlueFiber` (`Literature/Simon2012.lean`) proves
that every edge of the actual Section 4 graph moves inside the convex join
of its source and the feasible payoff set. It uses
`section4Y_mem_lowerGlueFiber` for the homotopy image and
`gluedFiber_subset_lowerGlueFiber` for the glued correspondence. These
statements do not depend on Lemma 4.4. The quantitative line-segment distance
estimate and the orbit-length telescope are also checked.
`feasible_of_tendsto_subsequence_of_unbounded_section4J_orbit` in the same
file proves that every convergent subsequence limit of an unbounded ordinary
orbit is feasible. `exists_feasible_cluster_of_unbounded_section4J_orbit`
constructs such a limit and a strict convergent subsequence from compactness
of the actual graph; no cluster is a supplied input. These declarations
passed a silent named build.

`ExtendedOrbitData.potential_nextStart_le_point`
(`MathUE/Topology/ExtendedOrbit.lean`) propagates a continuous decreasing
potential across either a finite endpoint stitch or an infinite-segment
limit. Only the next segment's activity is required, not infinitely many
segments. Simon's paper-specific orbit record is explicitly mapped to this
generic interface. The Euclidean segment-variation estimate and removal of
bounded predecessors before an unbounded segment are also checked in
`Literature/Simon2012.lean`.

`ExtendedOrbitData.IsProgressiveClusterPoint.potential_le_point`
(`MathUE/Topology/ExtendedOrbit.lean`) compares a continuous decreasing
potential at a progressive cluster with every earlier valid orbit point.
`ExtendedOrbitData.not_hasUnboundedExtendedVariationWith_of_potential`
in the same file rules out unbounded extended variation when a continuous
lower-bounded decreasing potential pays a fixed positive multiple of each
valid edge cost. Its finite-segment case includes the final segment; its
infinite-segment case telescopes through finite and infinite stitches.
These generic declarations passed a silent named build. The coordinate
floor corollary is now `ExtendedOrbitData.floor_le_coordinate_of_unbounded_variation`
in the same file. `section4J_floor_le_coordinate_of_unbounded_extended_orbit`
(`Literature/Simon2012.lean`) applies it to the actual Section 4 graph,
using the checked edge drift and an explicit half-payoff-box hypothesis at
every valid orbit point. The Simon module passed a silent named build; a
separate axiom check reports only the three standard axioms. This does not
prove the global half-box condition or Lemma 4.4.

`exists_nearFeasible_unbounded_section4J_tail` in that file covers both
an unbounded segment and infinitely many bounded-variation segments. From
an unbounded extended orbit in the compact actual Section 4 graph, it
constructs an unbounded extended orbit in the same graph starting arbitrarily
near a feasible payoff. No limit or convergent subsequence is supplied by
the caller. The theorem and its private bounded-segment estimates passed a
silent named build and a separate standard-axiom check.

`extendedOrbitStaysIn_halfPayoffBox_of_nearFeasible` in the same file
propagates the required coordinate bound through every valid point and
every finite or infinite stitch. It uses only the payoff normalization,
the actual Section 4 graph, and an initial distance at most one sixth of
the payoff scale from the feasible set. It does not require compactness,
unbounded variation, normality, or Lemma 4.4.
`exists_unbounded_section4J_tail_in_halfPayoffBox` combines this invariant
with the preceding construction. Both declarations passed the full silent
build and separate standard-axiom checks.

`exists_unbounded_fRow_extendedOrbit_of_unbounded_section4J_orbit`
(`Literature/Simon2012.lean`) constructs an unrestricted extended orbit of
the ordinary quitting correspondence from an unbounded orbit in the actual
Section 4 graph. The construction selects a rational start and keeps the
tail's points, counts, stitches and unbounded variation. It does not require
an all-edge small-step bound. The actual cutoff vanishes on every required
edge in the rational half-payoff box.

`theorem4_1` in the same file proves Theorem 4.1 under its stated affirmative
answer to Question 1, without an additional continuation-bound premise.
The proof handles the instant and stationarily generated branches and
cardinalities at most two, then transfers nonsingular perturbations back to
the original normal game. `lemma4_5` supplies the actual graph hypotheses
using an internally derived compact continuation bound and a smaller positive
common step scale. Both declarations pass the silent named build and separate
transitive checks with only the three standard axioms. Question 1 itself is
not proved, and the conclusion does not select a fixed uniform payoff target.

## Section 5 source components

`section5_abnormalSolo_pseudoEquilibrium` (`Literature/Simon2012.lean`)
constructs the literal small constant solo-quitting profile under the source's
additional no-harm singleton comparisons. Its prescribed payoff is the actual
owner's singleton vector, every other player has the requested full behavioral
regret bound, and the abnormal owner strictly improves by Never, whose payoff
is zero. This is not an equilibrium of the whole game.
`soloPayoff_add_three_mul_lt_minMaxQuit_of_section5Accuracy` and
`section5ModifiedC_outside_normalPieces_exists_two_low_coordinates` in that
file prove the printed three-accuracy separation and retain the actual
intersection of two distinct abnormal-player pieces. All three declarations
pass the silent named module check and separate transitive checks using only
the three standard axioms. They do not construct the Section 5 boundary
homotopy or correspondence and do not supply the Section 4 zero-quitter bound.

`section5ArtificialBoundary_exists_two_low_coordinates` and
`section5ArtificialNeighborhood_at_gap_sixth` (`Literature/Simon2012.lean`)
give the closed artificial-boundary carrier and an actual metric neighborhood
disjoint from the rational region, at one sixth of the minimum abnormal-player
gap. `section5ArtificialBoundary_exists_reciprocal_solo_drift` supplies the
two reciprocal local directions using actual solo-segment payoffs in the
lower glue. These statements pass the silent named build and separate
standard-axiom checks. They are components of the requested modification,
not the modified homotopy and correspondence or their orbit-escape proof.

The published Section 5, pages 194--195, specifies the retained normal-player
pieces and abnormal-pair intersections. It asks for an artificial modification
of the homotopy and correspondence near the boundary outside the normal pieces,
with the structure parameter depending on the minimum abnormal-player gap.
It does not give a formula for that modification, the parameter choice, or
the required eventual escape from its artificial edges. Completing this
source adapter requires those constructions and their compatibility and
Question 1 checks. The printed description alone is not such an adapter;
the checked geometry and solo-profile components above do not supply one.

## Section 4 cutoff and coordinate drift

Simon (2012), printed page 191, makes the cutoff vanish at distance at least
δ from the lower boundary. The ω attribution in the earlier Lean interface
was incorrect; this is a correction to the formalization, not a paper error.

`exists_section4Cutoff` (`Literature/Simon2012.lean`) constructs a continuous
cutoff for every positive radius and every truncation parameter, including an
empty lower boundary. It uses the canonical metric infimum distance after
the Euclidean coordinate identification.
`section4_coordinate_drift_of_radius_le_one` in the same file extracts the
coordinate drift argument for any supplied cutoff radius at most one,
without unused branch exclusions or domain-membership assumptions.
`lemma4_3` specializes this to the printed δ; `lemma4_3_omega` gives the
ω specialization. Both radius bounds follow from the stated parameters.
This does not change or discharge the requirements of `lemma4_5`.

`continuous_section4H`, `section4H_isStraightLineOn`, and
`section4H_eq_diagonal_on_frontier` in the same file prove joint continuity,
straightness, and fixing of the full truncated-domain frontier for the actual
constructed homotopy. The endpoint identities are explicit. Frontier fixing
uses the cutoff value one on the lower boundary and the actual inverse's
zero-quitting identity on the exterior closure.

`isContractibleSet_truncatedW` in the same file proves contractibility under
the weak lower-corner bounds `0 ≤ R+1` and `-(R+1) ≤ SoloPayoff G j` for every
player. The actual coordinate pieces are convex and have that corner in
common; their union is the literal truncated domain. The proof reuses
Mathlib's star-convex contractibility theorem through
`isContractibleSet_iff_contractibleSpace`
(`MathUE/Topology/SimonViabilityQuestion.lean`). No separate contraction
construction is assumed.

`truncatedPieces_areFullDimensionalCompactConvexPolytopes`
(`Literature/Simon2012.lean`) supplies full-dimensionality of every actual
piece from the standing Section 3 constants. The proof identifies each piece
with a clipped coordinate rectangle and derives strict lower-corner slack
from the paper's scale bounds. The generic
`isFullDimensionalCompactConvexPolytope_Icc`
(`MathUE/Topology/SimonViabilityQuestion.lean`) supplies the literal finite
corner convex hull, compactness, and nonempty ambient interior. Weak slack
is sufficient for the contractibility result above but not for this
full-dimensionality result.

`section4H_terminal_diagonal_mem_frontier` (`Literature/Simon2012.lean`)
proves terminal-diagonal exclusion for the actual homotopy under the standing
Section 4 hypotheses. Zero quitting gives a frontier point. Positive quitting
at a fixed one-stage payoff bounds that payoff by the terminal rewards;
Lemma 3.4 and the coordinate drift then exclude an interior diagonal point.
This does not discharge the other fields of Lemma 4.5.

`upperGlueRow_payoff_separation` (`Literature/Simon2012.lean`) proves the
quantitative payoff-separation estimate on the actual active-player cube
when at least two players are active. Under the uniform matrix estimate of
`Corollary4_1Statement`, positive accuracy less than one third of its constant,
and the literal upper-glue cap and support conditions, the payoff distance
bounds the row distance from below. An exact finite coordinate telescope
constructs the secant matrix, and the proof bounds its entries against the
singleton-difference matrix.

`isContractibleSet_upperGlueFiber` in the same file proves contractibility of
every actual upper fiber at this scale. For at least two active players the
payoff map is an injective continuous map from the compact admissible row
domain, giving a homeomorphism onto the fiber. For one active player the fiber
is the affine image of the interval from zero to the minimum of the cap and
one; no extra upper bound on the cap is assumed. `isContractibleSet_gluedFiber`
combines this with the existing lower-fiber theorem using the literal branch
definition. These are pointwise contractibility statements, not a continuous
choice of contractions across base points.

`lowerGlueFiber_piece_escape_at_section4Omega` in the same file proves
Property (7)'s lower-neighborhood branch at the actual common scale. For
each requested truncated piece, its owner's singleton terminal reward is
a constructed feasible target in that piece. The theorem supplies the step
length, nonincreasing distance to the piece, and the entire segment in the
literal glued fiber. It does not use the unfinished Lemma 4.4.

`upperGlueFiber_piece_escape_at_section4Omega` proves the upper branch under
the same Section 4 constants and normality assumptions. Its target is the
payoff of the requested player quitting alone at the stated cap; scaling
that one row gives the entire segment in the same fiber.
`gluedFiber_piece_escape_at_section4Omega` combines both branches, proving
Property (7) for the actual correspondence at the common Section 4 scale.

## Remaining Section 4 assembly

`abs_quitPayoff_withReward_sub_le_of_reward_close` and
`isQuitEpsilonEquilibrium_original_of_reward_close`
(`Literature/Simon2012.lean`) transfer the production reward-robustness
estimate to the paper's profiles and deviations. A terminal reward error
of at most the tolerance changes a fixed profile's payoff by at most that
tolerance, and increases its equilibrium error by at most twice the
tolerance. No new tail-sum argument is needed.
`allNormal_quitApproximateEquilibria_of_nonsingular_case` in the same file
composes this estimate with the checked normality-preserving perturbation.
It reduces the all-normal conclusion to the nonsingular case; it does not
supply the remaining orbit construction in that case.

`not_mem_lowerNeighborhood_of_mem_halfPayoffBox` and
`gluedFiber_subset_fRow_of_mem_halfPayoffBox` in the same file prove the
lower-glue exclusion used in Theorem 4.1. Their input places every coordinate
of the actual point between minus half and plus half of the payoff bound.
The second theorem then puts the actual glued fiber inside the paper's
quitting correspondence. The preceding extended-orbit localization and
half-payoff-box invariant supply those bounds from an unbounded extended
orbit in the compact Section 4 graph. The conversion of the joined graph's
remaining terminal-image edges is not yet complete.

`section4J_smallStep_mem_fRow_of_mem_halfPayoffBox`
(`Literature/Simon2012.lean`) now converts every actual small-step Section 4
edge whose source lies in the half-payoff box into an ordinary quitting
correspondence edge. It uses the checked local containment branches, not the
missing global upper bound in Lemma 4.4.
`exists_samePoints_fRow_extendedOrbit_of_section4J_smallSteps` in the same
file retains the chosen orbit's points, segment counts and lengths, both
stitch clauses, and Euclidean variation. Its named build is silent and a
separate transitive axiom check reports only the three standard axioms.
The all-edge small-step premise remains explicit: Question 1 supplies an
unrestricted Section 4 orbit, not an orbit in its small-step subgraph.
The half-box producer chooses a localized tail; the transport preserves that
chosen tail, not every point of the original orbit.

For the literal data in `lemma4_5` (`Literature/Simon2012.lean`), the domain
contractibility, polytope pieces, union decomposition, homotopy straightness,
initial diagonal, frontier fixing, terminal-diagonal exclusion, and actual
fiber contractibility, and boundary-piece escape have component proofs.
`truncatedW_eq_iUnion_fin` in the same file supplies the
finite-index union; positive piece count follows from the player-count
hypothesis. `lemma4_5` in the same Literature file assembles all seven
conditions. `isCompact_phi_preimage_truncatedW` and
`exists_uniform_continuationBound_survivalSlack_of_phi_mem_truncatedW`
derive a finite bound for every actual inverse point over the truncated
domain. The common Question 1 step scale can therefore be decreased without
changing the inverse, cutoff, homotopy or graphs. Small-step containment and
boundary-piece escape hold at that same decreased scale. No part of the open
numerical `lemma4_4` is assumed. The named build is silent and the separate
transitive axiom check reports only `propext`, `Classical.choice`, and `Quot.sound`.

`isCompact_gluedNeighborhood_of_section3Constants`
(`Literature/Simon2012.lean`) proves compactness of the actual neighborhood.
The lower-neighborhood theorem explicitly assumes a nonempty lower boundary;
the source-scale adapter supplies it. The empty-boundary convention is also
literal: `lowerNeighborhood_eq_univ_of_lowerBoundary_eq_empty` in that file
identifies the lower neighborhood with the whole space at nonnegative
accuracy when its boundary is empty.

`frontier_truncatedW_subset_interior_gluedNeighborhood` in the same file
proves the required frontier inclusion for every positive neighborhood
radius and arbitrary truncation parameter. `isContractibleSet_lowerGlueFiber`
proves contractibility of every actual lower fiber: it is the convex join
of its base point and the feasible payoff set.

The graph's first-coordinate containment, base-point fiber membership, and
both defining inclusions into the joined graph are proved by the direct
`mem_gluedNeighborhood_of_mem_gluedFiber`, `self_mem_gluedFiber`,
`homotopyTerminalImage_subset_section4J`, and `gluedGraph_subset_section4J`
adapters in the same file.

`QuittingOneStagePayoff.mem_of_convex` (`Literature/Simon2007.lean`)
generalizes the one-stage feasibility theorem to every convex carrier
containing the continuation and terminal rewards. Its application
`upperGlueFiber_subset_lowerGlueFiber` (`Literature/Simon2012.lean`) proves
compatibility on the entire overlap, including the switching boundary.
`isCompact_gluedGraph` proves compactness of the actual graph for a
nonnegative quitting cap and nonempty lower boundary; the source-scale
adapter above supplies the latter. `isCompact_section4J` combines it with
the compact terminal image of the continuous homotopy.

The upper-fiber estimates are not conclusions of `corollary4_1` alone.
Separate unrelated scale choices would not prove the final common-scale field.

For Property (6), Case 1, contractibility of the upper payoff image does
not justify membership of a straight segment.
`section4Y_mem_gluedFiber_of_section4X_mem_lowerNeighborhood`
(`Literature/Simon2012.lean`) proves the required fiber membership whenever
the actual first coordinate lies in the lower neighborhood. It uses the
one-stage payoff's membership in the convex lower fiber and assumes no
small-step or scale bound.
`section4X_mem_lowerNeighborhood_of_positive_cutoff_small_quit` in the same
file supplies that membership for positive cutoff and the stated small-
quitting bound under the literal common-scale small-step premise. The exact
one-stage affine identity and structure-map correction bound control the
distance to the original base point. Zero quitting is included. Both the
cutoff and the small-step premise use the same Section 4 radius; neither
Lemma 4.4 nor star-convexity of the upper image is assumed.
`section4_terminal_mem_gluedGraph_of_quitProbability_eq_zero` in the same
file handles zero quitting for every cutoff value: both terminal coordinates
equal the original base point, which lies on the truncated frontier and in
the literal glued graph.
`section4Omega_lt_terminalStep_of_bounded_positive_cutoff` proves that positive
cutoff and a first endpoint inside the reward box but outside the lower
neighborhood force a terminal step larger than the common radius.
`section4_terminal_mem_gluedGraph_of_bounded_positive_cutoff_smallStep`
states the resulting small-step containment directly. Neither theorem needs
a lower bound on quitting probability or the global part of Lemma 4.4.
The proof's low-coordinate drift is now a separate private theorem in the
same file: under the stated bounded positive-cutoff hypotheses, some
coordinate is below its min-max value by more than half the motion parameter
and rises by at least the squared motion parameter divided by one thousand
times the payoff scale. The public distance bound consumes this stronger
coordinate statement. This refactoring passed a silent named build,
independent declaration-level review, and a separate transitive standard-axiom
check.
`section4J_coordinate_floor_or_drift_of_mem_halfPayoffBox` in the same file
now supplies the corresponding estimate for every coordinate of every actual
Section 4 graph edge whose source lies in the half-payoff box. It preserves
the min-max floor minus one third of the motion parameter, and raises a
coordinate below that floor by at least the squared motion parameter divided
by one thousand times the payoff scale. The terminal and glued branches are
both covered. The proof uses the checked positive-bound form of the earlier
coordinate-drift lemma, not Lemma 4.4's unfinished global upper bound. It
passed a silent named build and a separate transitive standard-axiom check.
The recurrent-coordinate consequence for an unbounded extended orbit
staying in the half-payoff box is the theorem above. Producing or retaining
that box is supplied by the checked near-feasible tail and invariant above;
it does not supply the all-edge small-step premise.
The positive-cutoff branches are assembled in `lemma4_5` at its internally
chosen smaller common step scale.

`section4_terminal_mem_fRow_of_cutoff_eq_zero` in the same file puts every
zero-cutoff terminal endpoint in the ordinary one-stage payoff correspondence.
`section4Omega_lt_terminalStep_of_zero_cutoff_large_quit` proves that zero
cutoff and quitting at least the paper's threshold force a terminal step
larger than the common radius. No continuation-box assumption or global
part of Lemma 4.4 is used. Inside the motion box the proof uses the existing
uniform motion estimate; above it the reward bound suffices; below it the
quantitative form of Simon (2007), Lemma 6, gives the required displacement.
Both declarations passed a silent named build; the large-quitting theorem
also passed an independent declaration-level review. Separate transitive
axiom checks for these declarations and the shared threshold estimate
found only the standard three permitted axioms.

`section4_terminal_mem_gluedGraph_of_zero_cutoff_positive_small_quit`
in the same file proves the remaining small-positive-quitting branch at zero
cutoff. The common-radius small-step premise and the local structure-map
correction estimate give the actual upper-neighborhood coordinate bounds;
the same product row satisfies its support and cap constraints. The theorem
handles the lower-neighborhood priority in the definition of the glued
fiber. It passed a silent named build, independent declaration-level
review, and a separate transitive standard-axiom check. It does not use the
global upper bound in Lemma 4.4, which remains
unproved. The bounded-continuation, positive-cutoff case above instead uses
the supported-coordinate bound and coordinate drift.

`section4_terminal_mem_gluedGraph_of_zero_cutoff_smallStep` in the same
file combines the zero-quitting, small-positive-quitting, and large-quitting
cases into the complete zero-cutoff containment theorem at the common
Section 4 scale. It passed a silent named build and a separate transitive
standard-axiom check. The remaining containment case has positive cutoff,
large quitting probability, and a first endpoint outside both the lower
neighborhood and the payoff box.

The three quantitative ingredients for that remaining case are checked:
positive cutoff and exclusion from the lower neighborhood give base-point
separation greater than one quarter of the accuracy; outside the payoff box,
the one-stage displacement is at least two thirds of the payoff scale times
the quitting probability; terminal interpolation multiplies this lower bound
by one minus the cutoff. Their private proofs in the same file passed a
silent named build and a separate transitive standard-axiom check. The
coefficient estimate and common-scale contradiction are proved inside
`lemma4_5`, using the compact inverse bound. The actual inverse-point distance
is bounded by `(R + 1 + B) * card G.Player`, where compactness supplies `B > 0`
internally. Decreasing the existential Question 1 step scale closes this
branch without the printed zero-quitter upper-coordinate estimate.

`lemma4_4` in the same Literature file is still open in its full stated form.
Its supported positive-quitting-coordinate bound is proved.
`continuationCoordinate_ge_neg_half_radius_of_mem_truncatedW` also proves
the lower bound for every continuation coordinate under the full Section 3
assumptions, by the published maximal-quitter argument. The global upper
bound remains unproved. The checked
counterexamples refute the isolated zero-quitter inference and a formulation
without the standing assumptions, not the full lemma. Independent source
review confirms the distinction: the sentence on printed page 192 infers
that the structure-map coordinate dominates the continuation coordinate
when the player does not quit. Expanding the definition leaves a term
minus the total quitting probability times that continuation coordinate,
so the asserted sign does not follow from the definition and one-stage
equilibrium alone. The remaining claim is that every zero-quitting player's
continuation coordinate is at most the truncation radius plus one, under
all the standing Section 3 hypotheses. Neither the global lower bound nor
the supported-coordinate estimate proves it. The current
`lemma4_5` assumes an ω cutoff; the corrected δ statement of `lemma4_3` does
not by itself establish a δ version of `lemma4_5`.

`theorem4_1` uses `exists_nonsingularPerturbation` to preserve normality, the
actual Section 4 orbit localization and cutoff elimination, and the
unrestricted orbit-to-equilibrium consumer. The same profiles transfer back
to the original game. Its only external conclusion premise is
`Question1Affirmative`; it does not cover the abnormal-player branch.

### Remaining Simon (2012) declarations

- `lemma4_4` (`Literature/Simon2012.lean`):
  `continuationCoordinate_ge_neg_half_radius_of_mem_truncatedW` supplies every
  lower coordinate bound, and `supportedContinuation_abs_le_half_radius`
  supplies both bounds when the player quits with positive probability. The
  missing premise is the upper bound `z.1.1 j ≤ R + 1` for a zero-quitting
  player under the theorem's full standing hypotheses.
- `question1_affirmative_implies_all_quitting_games`
  (`Literature/Simon2012.lean`): `lemma5_1`, `minimumAbnormalGap_pos`,
  `exists_section5Accuracy`, and the actual `Section5ModifiedC` supply the
  Section 5 setup. Its compactness and contractibility are checked, and
  `exists_section5ModifiedC_fullDimensionalPolytopeCover_of_section3Constants`
  in that file constructs a positive finite cover by literal normal-player
  pieces and distinct abnormal-pair intersections. Every piece is a
  full-dimensional compact convex polytope under the standing Section 3
  constants. These declarations pass a silent named build and a separate
  transitive audit with only the three permitted axioms. The paper sketches,
  but does not verify, the modified boundary homotopy and glue or their seven
  Question 1 hypotheses. Those source constructions remain; the all-normal
  `theorem4_1` does not cover this abnormal-player branch.

For the abnormal-player branch, the printed final paragraph specifies that
the homotopy and glue must change near the new artificial frontier and that
the structure parameter must depend on the minimum abnormal gap. It gives no
formula for those modifications or their compatible orbit transport. The
next source construction must fix the whole modified frontier, preserve the
contractible local fibers and both common-step properties, and ensure that
an unbounded selected orbit yields an actual quitting-correspondence tail.
The checked local reciprocal singleton directions alone do not specify this
joint construction. An independent proof of the same all-game Question 1
consumer would also close the declaration; no particular interpolation
formula is required by the result-level interface.

Neither remaining `sorry` has a source-complete proof obtainable solely by
assembling the currently checked declarations.

## Markov variation

`MarkovSemantics.expectedMarkovVariation_le_of_finiteProductionBound`
(`Literature/Simon2007.lean`) reduces Lemma 2 to a finite-horizon global bound
by the number of states. The same file proves qualitative finiteness under
time homogeneity and supplies the actual cylinder-law adapters.
The separate math workspace records the self-contained question in
`math/questions/FINITE_HOMOGENEOUS_MARKOV_MARTINGALE_VARIATION.md`:
for every finite homogeneous kernel, horizon, and unit-interval
backward-harmonic value, the expected total absolute martingale increment
is at most the state count. The exact state-owned decomposition is already
`finiteExpectedSpaceTimeMarkovVariation_eq_sum_stateOwned`
(`MathUE/Probability/HarmonicStateAccount.lean`). No replacement proof of
the global bound is formalized.

The proposed per-state renewal input is false:
`SevenStateVisitEpochCounterexample.not_homogeneousBackwardHarmonicVisitEpochPrinciple`
(`MathUE/Probability/HarmonicVisitEpoch.lean`) gives a homogeneous finite
chain with a unit-interval time-dependent backward-harmonic value whose
single-state account exceeds one. It does not refute the total-state bound.
A proof of that global bound cannot assume the per-state estimate.

## Chain reduction

`lemma1` (`Literature/Simon2007.lean`) is proved for the specified normalized
reduction data, including retained roots, actual composite laws, and the
reduced transition law. It does not construct that data from every
chain-reducibility witness. The root-action and simultaneous-root-retention
questions, and the checked trace and advantage comparisons, are recorded in
[the chain-reduction source note](CODEX_FORMALIZER_SIMON_CHAIN_REDUCTION_SOURCE_QUESTION.md).

## Remaining Simon (2007) declarations

The ten live `sorry` occurrences in `Literature/Simon2007.lean` have these
nearest checked dependencies and unresolved inputs:

| Declaration | Checked boundary | Missing input |
| --- | --- | --- |
| `ApproximateEquilibriaImplyPerfect` | `EpsilonSelfPerfect.mono` only transports a supplied perfection witness across tolerances. | Simon [16]'s equilibrium-to-perfection construction for the actual stochastic-game law; no checked witness extractor supplies the common good set and local action inequalities. |
| `theorem1` | `EpsilonViable.mono` and the paper's `CumulativeAdvantage`/`AdvantageCrossingEvent` are available. | The behavioral-profile patching and payoff estimate from self-perfection, viability, and the crossing-event bound to the stated equilibrium constant. |
| `lemma2` | `MarkovSemantics.finiteExpectedVariation_eq_production` and `MarkovSemantics.expectedMarkovVariation_le_of_finiteProductionBound` give the cylinder-law adapter and exact finite-horizon reduction. | The global state-count finite-horizon variation inequality; the proposed single-state renewal bound is false, as noted above. |
| `lemma5` | `everyNormalSoloQuitterHarmsNormal_of_not_stationarilyGenerated` and `exists_correctedUniformMotionAt_of_not_branches` apply under the *corrected* stronger branch exclusion and restricted carrier. | The printed 2007 hypotheses and unrestricted global motion conclusion are not supplied by those results. The 2012 correction changes both; this is not a Lean transport task. |
| `lemma5_corrected_2012` | `everyNormalSoloQuitterHarmsNormal_of_not_stationarilyGenerated` and `exists_correctedUniformMotionAt_of_not_branches` prove its harm and motion/survival clauses. `Literature.Simon2012.lemma2_1_part1`, `lemma2_1_part2`, and `lemma2_1` reuse this declaration. | The positive-normal-player clause under failure of the instant and stationarily generated branches, exactly the source obligation in “Corrected Lemma 5” above. The 2012 theorems cannot be imported back to discharge it. |
| `theorem3` | `CyclicOrbitCondition.hasQuitApproximateEquilibria`, `FiniteNearOrbitCondition.toCyclicOrbitCondition`, and `CyclicOrbitCondition.toInfiniteOrbitCondition_of_uniformRho` assemble the other edges. | Its local `HasQuitApproximateEquilibria → CyclicOrbitCondition` hole, as well as the open printed `lemma5` it invokes. The checked `hasQuitApproximateEquilibria_imp_cyclicOrbitCondition_of_firstCrossingExtraction` requires a separate extraction premise and corrected motion. |
| `theorem3_corrected_2012` | `CyclicOrbitCondition.toInfiniteOrbitCondition_of_corrected_motion` and the same orbit compilers cover the non-forward edges; `Literature.Simon2012.theorem2_1` only transports this very declaration to Euclidean norm. | `lemma5_corrected_2012` plus `HasCorrectedFirstCrossingPathExtraction` (or an equivalent equilibrium-to-cyclic proof). The conditional checked first-crossing compiler does not construct its extraction premise. |
| `KohlbergMertensStatement` | `MatrixEquilibriumGraph` and `MatrixNorm` express the matrix-game target. | The external Kohlberg–Mertens homotopy theorem in the stated straight/proper form; no checked homotopy construction is present. |
| `lemma8` | `repeatedF_eq_iterate_of_no_sure_quit` identifies the repeated payoff correspondence under the no-sure-quit premise. | A connected-component lifting argument for the repeated-equilibrium graph over connected compact `D`, using the matrix-equilibrium topology (including the open Kohlberg–Mertens input), not just payoff-set equality. |
| `theorem4` | `lemma10` preserves the restricted escape region and `lemma11_of_crossHarm` reaches a critical point by a finite restricted orbit under its explicit motion/cross-harm inputs. | The final critical-point-to-approximate-equilibrium assembly, including the requisite equilibrium-component/topological step and discharge of the corrected Lemma 5 inputs. The checked critical-point orbit alone is not an equilibrium. |

None of these ten is currently a source-complete theorem awaiting only a
non-circular Lean transport: the apparently matching 2012 statements depend
on the corresponding open 2007 declarations.
