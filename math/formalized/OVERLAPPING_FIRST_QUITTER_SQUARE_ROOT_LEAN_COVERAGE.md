# Overlapping first-quitter square-root law coverage

Author: CODEX_ROOT. Checked integration: `3c6d97a`, pushed after a silent
`lake --quiet --iofail build` and repository checks. Independent Astra
completion audit found no remaining substantive mathematical conclusion.

Frozen source:
`OVERLAPPING_FIRST_QUITTER_SQUARE_ROOT_LAW_AND_FIN4_PAIR_CONSUMER.md`, SHA-256
`54915eef3f41ac292d35c579895ffda3e0755ec209d0d4e135765e25d611a565`.

## Coverage map

- `twoOverlappingFirstStoppingMasses_sqrt_sum_le_one`
  (`MathUE/Probability/OverlappingFirstStopping.lean`) covers arbitrary
  complete independent stopping laws, including positive Never mass.
  Incomparable-coalition and all-distinct-pair consequences are supplied by
  that module and `MathUE/Probability/IndependentFirstStoppingPair.lean`.
- `overlappingMass_sqrt_sum_eq_one_iff_deterministic_or_chronological`
  (`MathUE/Probability/OverlappingFirstStoppingChronologicalEquality.lean`)
  gives the full equality classification: both degenerate endpoints and
  the three positive chronological shapes, initial silent dates, literal
  later deterministic atoms, and unrestricted irrelevant tails. The proof
  uses the exact infinite recurrence and mass-one rigidity, not equality
  inferred from finite truncations.
- `quittingBehaviorExactFiniteFirstCoalitionMass_eq_terminalOutcomeMass`
  (`UniformEquilibrium/Quitting/Paths/BehaviorFirstStoppingPairLaw.lean`)
  identifies the complete-law formula with actual execution probabilities.
  `exists_actual_finFour_pairProjection_sharpProfile`
  (`UniformEquilibrium/Quitting/Paths/FinFourPairSharpness.lean`) constructs
  actual sharp profiles for every pair of distinct Fin4 edges.
- `exists_pair_terminalOutcomeMass_eq_one_of_terminalPairMass_eq_one`
  and `uniformSixPairTerminalLaw_noncharacterization`
  (`UniformEquilibrium/Quitting/Paths/PairOnlyTerminalLawRigidity.lean`)
  prove pair-only rigidity and exclude the uniform six-pair simplex point
  despite all its pairwise inequalities.
- `UniformEquilibrium/Quitting/Terminal/FinFourAllPairCrossingConsumer.lean`
  proves the literal fifteen-projection count, attained maximum crossing,
  all-profile exploitability bound, projected-feasibility equivalence,
  pure-time response, and conditional no-uniform-payoff consumer. The
  single-pair version remains in `PairMassForcingConsumer.lean`.
- `UniformEquilibrium/Quitting/Examples/OverlappingFirstStoppingBoundary.lean`
  computes the complete stationary half-hazard law and denominator-twelve
  equality example, and refutes the naive three-root ledger and extension
  to nested coalitions. It retains the all-zero-row equality degeneracy
  and the two strict-loss boundary cases.
- `exists_twoSupported_canonicalOverlap_maximizer_on_dates`
  (`MathUE/Probability/FiniteOverlapSparseMaximizer.lean`) proves the optional
  finite-menu maximizer statement for canonical complete stopping laws.
  Exact indicator/embedding identities and inverse reconstruction ensure
  all laws on the chosen dates plus Never are included. The generic core,
  `MathUE/TwoCoordinateSparseSimplex.lean`, works for arbitrary pairs of
  finite trilinear expectations, preserving one and improving the other.

## Scope

Pair-projection feasibility is not joint six-coordinate realizability.
The affine mass bounds remain supplied hypotheses, not an arbitrary-game
producer. Sparse maximizers need not be unique, and not every maximizer is
claimed sparse. Historical exhaustive-search counts were not reproduced;
the packet explicitly labels them falsification evidence, not its proof.
The exact displayed examples are proved. No new polygon datatype or
particular geometric proof architecture is required by these results.
