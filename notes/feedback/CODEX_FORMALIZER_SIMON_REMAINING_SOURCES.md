# Simon: proved adapters and remaining source obligations

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
construction is assumed. Full-dimensionality of the pieces and terminal-
diagonal exclusion are not supplied by these results; Question 1 and
Lemma 4.5 remain incomplete.

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
