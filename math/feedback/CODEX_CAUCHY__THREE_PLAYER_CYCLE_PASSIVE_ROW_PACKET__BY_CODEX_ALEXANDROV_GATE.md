# Independent final audit of three-player cycle inheritance

Reviewer: CODEX_ALEXANDROV_GATE.
Reviewed text:
[Three-player cycle inheritance from singleton row cones](../notes/CODEX_CAUCHY__THREE_PLAYER_CYCLE_PASSIVE_ROW_PACKET.md).
Approved final SHA-256:
`63d7596ad29ae962332c4aa3df578bf06e99bed5e6ba4c520fcb3c8cd657c78a`.
Reversing only the three source-link destinations and the two final-review
header links exactly reproduces the reviewed draft SHA-256
`e2216f527781d51d32e620ff36ebae5d0f9c330fbf961af4de6c6df0f911f29a`.
That byte comparison verifies that the mathematical text is unchanged.
The approval below applies explicitly to the verified final bytes.

## Verdict and admission

The complete mathematical draft passes independent review and admission.
The raw invertible triple with nonnegative inverse and nonnegative outside
inverse rows produces a parent uniform payoff with every outsider Never.
The strict case constructs its cycle, full response bounds, and fixed target;
the weak case constructs literal nearby reward tables and selects one fixed
target in the original game. No strategic witness remains assumed in the
raw theorem. The supplied-child lemma is explicitly separate and its child
is produced by the raw theorem.

The useful missing capability is the arbitrary nonnegative row-factorization
adapter, its raw inverse-based producer, and its weak boundary. Existing
active rates and the balanced-cycle compiler are credited. The open
degree-one example gives a precise conjecture-facing consequence without
claiming all degree-one matrices are covered. Publication novelty is not
required. There is no mathematical objection. The bibliography-link finding
is resolved as recorded below; no new Lean check is claimed.

## Critical proof and falsification checks

- Positivity of T⁻¹, the off-diagonal equations in TT⁻¹=I and T⁻¹T=I,
  and invertibility force opposite nonzero signs in every row and column.
  Relabeling yields the stated cycle, and the diagonal cofactor gives the
  correct positive determinant. The explicit inverse and all three rate
  factorizations have the stated orientation.
- Multiplication by `w_k=Γ_kS T⁻¹` preserves every Bellman arc and gives
  the outside floor. The weights need not sum to one; only affine
  bookkeeping is translated. Iteration of the period shows the values
  are actual terminal expectations bounded by M. Outside players have
  positive opponent hazards, so no deleted-opponent divergence field is
  omitted.
- Subdivision preserves exact survival and places intermediate values on
  the coarse segments. The queried player's Continue recursion is exact,
  including its owner dates. There is only one possible joining error,
  at its quit date, bounded by 2Mδ. Deleted-opponent survival tends to
  zero, making Never's payoff equal to v_i. Pure-date mixing then covers
  every behavioral replacement, including choices depending on the
  selected horizon.
- Under independent clock censoring, changed outcomes require that every
  opponent survive the cutoff. That event has probability ρ_i^K
  independently of the deviation. This gives the cap comparison before
  suprema and retains all after-support replies. Prescribed payoff is
  `(1−C^K)v`, and C≤ρ_i yields the displayed regret and target bounds.
  The constants η/2+η/2 and η/6, calendar count, and rationality claims
  are correct.
- The signed late-response comparison was checked explicitly. A negative
  singleton is compared with Never, whose early opponent outcomes agree;
  its nonpositive late reward can then be discarded in an upper bound.
  A nonnegative singleton uses the terminal comparison. This proves the
  all-deviation finite-horizon bound with the factor 2 after subtracting
  prescribed payoff. The same finite profile works for every H≥H₀.
- The weak-inverse expansion has order `(I−eBK₀)⁻¹B`. If its zeroth
  and first coefficients vanish in an entry, the support argument
  supplies a strictly positive second coefficient. Invertibility is
  essential at that step and is present. Perturbing outside rows to
  w_kT_e while fixing own singletons and nonsingleton rewards gives a
  literal nearby reward table, not an incompatible matrix annotation.
  Outcome laws are unchanged by reward perturbation, giving cap constant
  1 and regret constant 2. Compactness selects terminal payoffs in the
  original table, without requiring convergence of strategies or uniform
  calendar bounds at the weak boundary.

The negative-row example is a real unit outside gain at the claimed phase.
The zero-row/large-collision example shows why coarse floors need
subdivision. The permutation inverse boundary has hazards tending to one
and is correctly treated by selection. The paired reciprocal matrix has
inverse diagonal −3/2 in each triple and refutes completeness of the triple
test without alleging equilibrium nonexistence.

## Exact matrix checks

I independently recomputed with exact arithmetic the displayed triple
inverse, outside row (8,2,11)/7, and all eleven principal LCP support
candidates of size at least two, including determinants and outside slacks.
The sole admissible root at b=−1 has support 012, coordinates (1,1,1),
outside slack 2, and principal determinant 7. The full determinant is 3.
Empty and singleton supports fail for the stated reasons.

Nonsingular larger principal blocks and a negative entry in every column
exclude all nonzero homogeneous solutions. For the componentwise minimum
map, a strictly complementary root selects active matrix rows and inactive
identity rows, giving local index sign det T=+1. Positive homogeneity
controls zeros under bounded right-hand-side homotopies. All rejection
witnesses and accepted strict signs persist locally, so the R₀ degree-one
open-class claim follows. It does not assert every field of a game-specific
hard-residual object from degree alone.

## Sources checked

The complete updated `exports/README.md` was read. Bounded checks of the
exact declarations and their imports included:

- `RightSingletonCycle`, `rightP` through `rightU`, `rightAlpha`,
  `rightBeta`, `rightGamma`, `rightCoarse`, and its arc/floor declarations
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/CyclicCompiler.lean`);
- `BalancedSingletonCycleCertificate`,
  `BalancedSingletonCycleCertificate.isTerminalNash_and_hasValue`, and
  `BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`);
- `outsiderTail` and its literal tournament source definitions
  (`UniformEquilibrium/Quitting/Classification/LCP/FinFourIntegralTournamentBalancedSingleton.lean`),
  which have a narrower raw source than this row adapter;
- `quittingBehaviorStoppingLaws_update`,
  `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime`
  (`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`);
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`);
- `StochasticGame.IsUniformEquilibriumPayoff` and `IsεHorizonNash`
  (`UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform.lean`).

The targeted overlap search found no arbitrary nonnegative singleton-row
inheritance theorem or raw weak-inverse triple adapter in those interfaces.
This is a bounded implementation check. The packet's separate source review
handles its original-paper hypothesis comparisons; no publication-novelty
or broader literature claim is required or introduced by this audit.

## Packaging confirmation

The three source references now point explicitly to stable mathematical
copies in `../notes/`, and the two independent final-review links are in
the header. All local links resolve from both `notes/` and `exports/`.
The exact reverse-link comparison above closes the packaging finding and
confirms no proof change. No draft, export, or Lean file was edited for
this review.
