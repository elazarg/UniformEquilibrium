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
build and separate standard-axiom checks. The graph-to-quitting-orbit and
Lemma 4.5 assembly remain Lean work.

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

For the literal data in `lemma4_5` (`Literature/Simon2012.lean`), the domain
contractibility, polytope pieces, union decomposition, homotopy straightness,
initial diagonal, frontier fixing, terminal-diagonal exclusion, and actual
fiber contractibility, and boundary-piece escape have component proofs.
`truncatedW_eq_iUnion_fin` in the same file supplies the
finite-index union; positive piece count follows from the player-count
hypothesis. These components still need assembly into the full statement.
The remaining field to prove in `QuestionOneHypotheses`
(`MathUE/Topology/SimonViabilityQuestion.lean`) is small-step containment at
the same scale already used for boundary-piece escape.

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
The subsequent recurrent-coordinate argument for extended orbits remains
formalization work.
The remaining positive-cutoff branches and their assembly remain to be
formalized.

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
remaining coefficient estimate and the common-scale contradiction are not
yet proved.

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

For `theorem4_1`, `exists_nonsingularPerturbation` in the same file already
constructs the perturbation and preserves normality. The standalone
extended-orbit-to-equilibrium direction, reward transfer, and the preceding
joined-graph localization and half-box results are also proved. The remaining
work is the source-required cutoff elimination and assembly through
Lemma 4.5, followed by the existing quitting-orbit and perturbation consumers.

## Markov variation

`MarkovSemantics.expectedMarkovVariation_le_of_finiteProductionBound`
(`Literature/Simon2007.lean`) reduces Lemma 2 to a finite-horizon global bound
by the number of states. The same file proves qualitative finiteness under
time homogeneity and supplies the actual cylinder-law adapters.

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
