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
