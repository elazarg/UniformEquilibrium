Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Bounded Single-Pivot Decision Reduction

Frozen draft patches only. No Lean or Lake command ran. No shared-checkout file,
Git state, cache, module inventory, or living document was changed.

## Patch Order and Exact Dependencies

1. `15_LITERAL_POSITIVE_SCALING.patch` adds
   `UniformEquilibrium/Quitting/Transform/PositivePayoffScaling.lean`.
   Independent of future-wave patches 01–14. Requires the existing literal
   quitting-game construction and stochastic-game positive-affine payoff API.
2. `16_ACTUAL_BOUNDED_SINGLE_PIVOT.patch` adds
   `UniformEquilibrium/Diagnostics/Quitting/FinFourBoundedSinglePivotNormalization.lean`.
   Requires 15 and the already integrated actual Fin4 single-pivot normalization
   owner. Uses the existing canonical finite reward bound.
3. `17_DECISION_PRESERVING_POLYNOMIAL_JOIN.patch` adds
   `UniformEquilibrium/Diagnostics/Quitting/FinFourBoundedSinglePivotPolynomialObstruction.lean`.
   Requires 16 and frozen 14, with 14's original dependency closure. No dependence
   on 13's separate nonquasiconvex join.

## Source and Canonical Reuse

Source: `math/exports/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md`,
the full Adapter and semantic consumer normalization argument. Both packets
were fully read before their respective drafts.

Literal game owner:
`quittingGame` in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`.
Its live stage payoff is zero and its absorbed payoff repeats the terminal
table. Common scaling therefore agrees with whole-game affine scaling with
zero shift. The identity is on the entire `StochasticGame` structure, including
states, actions, transitions, discount, and payoff. No terminal-only translation
is asserted to preserve strategic behavior.

Canonical semantic owners:
`StochasticGame.affinePayoff`,
`StochasticGame.isUniformEquilibriumPayoff_affinePayoff_iff`, and
`StochasticGame.isUniformEquilibriumPayoff_of_affinePayoff`, all in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Transform/Payoff/AffinePayoff.lean`.
Patch 15 invokes them rather than reproving finite-horizon expectations,
accuracy rescaling, behavior profiles, histories, or deviation semantics.

Actual normalization owner:
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`.
Its literal normalized table has the canonical singleton shape and actual
no-UE conclusion. The proof selects no strategy or minimum supplied by a caller.

Finite bound owners:
`quittingRewardBound` and `abs_reward_le_quittingRewardBound` in
`UniformEquilibrium/Quitting/RewardBound.lean`. The Archimedean library's
`exists_nat_ge` selects a natural base above the actual normalized finite table's
canonical bound; `divisor = base + 1` guarantees positivity. The positive scale
is the rational-real reciprocal `1 / divisor`; rewards themselves remain real.
`one_div_mul_cancel` supplies the exact unit bound.

Fresh certificate owner: frozen 14's
`quittingGame_noUniformPayoff_iff_noSureRoot_and_restricted_rationalPotential`.
It derives actual normality from the newly scaled nonnegative singletons and
calls the existing characterization with reward bound one, on exactly box three.
The producer in 17 invokes this characterization afresh only after constructing
the literal bounded no-UE table. No old polynomial is moved to a new box.

## Quantifier and Same-Witness Contract

Patch 16 takes only an arbitrary real Fin4 reward table and its bare no-UE
hypothesis. It internally produces a pivot and an integer divisor at least one,
bounds the actual normalized table, and proves that its literal positive scaling
is unit bounded, has singleton vector `(1 / divisor) e_p`, and has no UE.

Patch 17 takes the same bare source data and produces a fresh rational tolerance
and polynomial internally. `IsQuittingBoundedSinglePivotPolynomialObstruction`
contains the literal bound, positive singleton scale, no-sure-root clause,
robust box-three certificate, actual canceled total degree at least three,
failure of all individual degrees being at most one, and the existing full
adaptive minimum conditions for that identical expression. The latter quantify
over every global minimum, including upper-face minima.

The final declaration
`exists_finFour_no_uniformPayoff_iff_exists_boundedSinglePivotPolynomialObstruction`
is the decision-level equivalence. Its reverse direction forgets restrictions
and invokes the original characterization's converse through 14. No source
rationality, supplied candidate, supplied minimum, favorable strategy, uniform
denominator cutoff, constructed counterexample, or Fin4 solution is claimed.

## Trust and Verification

No new trust mechanism or axiom declaration is introduced. Expected axioms are
only the project's admitted foundational trio, inherited through the reused
owners; this is not an executed axiom audit. The draft contains no `sorry`,
`admit`, `native_decide`, `set_option`, unsafe declaration, or `implemented_by`.
Lexical searches found none, and the non-import added Lean lines are at most
100 characters. These checks are not Lean compilation or the project trust scan.

Root is the sole compiler and integrator. After dependencies and the current
full gate, targeted checks in order are:

1. `UniformEquilibrium.Quitting.Transform.PositivePayoffScaling`;
2. `UniformEquilibrium.Diagnostics.Quitting.FinFourBoundedSinglePivotNormalization`;
3. `UniformEquilibrium.Diagnostics.Quitting.FinFourBoundedSinglePivotPolynomialObstruction`.

Root owns umbrella imports, generated axiom inventory, trust/import checks, and
the proportional final integration gate. The main static elaboration points
left for that compiler are structure congruence in the literal scaling identity
and dependent rewriting of that identity in the existing UE proposition.

## Frozen Hashes

- 15: `cb2cce6999741864bc34dd1bbc3afbc02c9644e32ac02261c0b7590322e567a7`
- 16: `6a105959544aba5b3a651cac41274b64085009708d5251a80fbd8dde69e96d1d`
- 17: `81fc37eb702f07351344583dcb95306dae510ffa4f6828d8a6c6d60287e15b0a`
