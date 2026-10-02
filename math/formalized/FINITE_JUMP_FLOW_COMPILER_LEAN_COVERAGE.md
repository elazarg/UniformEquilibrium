# Finite jump–flow compiler: Lean coverage

Packet: [FINITE_JUMP_FLOW_COMPILER_AND_ZENO_ERASURE_BOUNDARY.md](FINITE_JUMP_FLOW_COMPILER_AND_ZENO_ERASURE_BOUNDARY.md).
Moved unchanged from `exports/` after targeted checks, a named build, and
independent review of the sharp local bounds and literal execution.

## Finite compiler

[`FiniteJumpFlowCompiler.lean`](../../UniformEquilibrium/Quitting/EssentialAPS/FiniteJumpFlowCompiler.lean)
defines the data-bearing `CompatibleFiniteJumpFlowWord`. Every original jump
root, flow owner, mass, and compatibility proof is retained. The mesh schedule
is indexed by occurrence, so repeated identical operations can have different
mesh sizes. Every flow uses a strictly positive number of rows.

- `rootThenContinuation_coefficient_error_and_debt_le` proves the exact
  joint-survival payoff-error and opponent-survival debt-error bounds.
- `quittingTerminalSemanticDebt_repeatedSingletonProfile_other_le_max`
  proves the sharp outsider maximum bound. The owner bound is
  `quittingTerminalSemanticDebt_repeatedSingletonProfile_owner_le`.
- `CompatibleFiniteJumpFlowWord.execute` constructs the actual ordinary
  behavioral profile, keeping every supplied jump root literal.
- `CompatibleFiniteJumpFlowWord.execute_error_and_debt_le` separates the
  unchanged target error from the accumulating debt error.
- `CompatibleFiniteJumpFlowWord.execute_common_error_bound` gives the
  stated common-error formula. `CompatibleFiniteJumpFlowWord.execute_exploitability_le`
  states the unrestricted behavioral exploitability bound directly.
- `CompatibleFiniteJumpFlowWord.isUniformEquilibriumPayoff` transports a
  supplied fixed uniform-payoff tail through every finite ordering.

The safe local bounds are short corollaries of the sharper bounds. Unused
intermediate bookkeeping and duplicate weaker proofs were removed.

## Infinite cutoff boundary

The existing
`quittingTerminalDeviationDebt_literalRootStack_eq_blockAct`
([`LiteralExactPrefixStack.lean`](../../UniformEquilibrium/Quitting/Root/LiteralExactPrefixStack.lean))
gives finite cutoff composition of the exact clipped debt actions. Its
`quittingLiteralTerminalDebtBlocks` list explicitly builds every block against
the corresponding executable suffix profile, and its aggregate uses the
generic `Block.concatList` action. Joint-survival payoff transport is
separately stated in
[`FiniteWordSemanticSplice.lean`](../../UniformEquilibrium/Quitting/Root/FiniteWordSemanticSplice.lean).
No theorem asserts an infinite compiler without the required cutoff erasure
or an actual terminal semantic tail.

[`AllMinusOneLiveBoundary.lean`](../../UniformEquilibrium/Quitting/Examples/AllMinusOneLiveBoundary.lean)
proves the exact all-Continue self-loop and root Nash at the constant payoff
one, but every actual terminal payoff is nonpositive. Its
`phantom_not_uniformEquilibriumPayoff` is the explicit failure of semantic
completion at that live boundary.

## Verification

Targeted Lean checks and named dependency builds passed. Independent static
review checked packet formulas (1) and (5)–(8), arbitrary occurrence-indexed
meshes, literal roots, complete behavioral caps, and the infinite-boundary
scope. The integrated full `lake build`, including the exhaustive axiom audit,
passed with 11435 jobs. Trust, import-graph, documentation, duplicate-proof,
reward-bound, and redundant-hypothesis checks passed.
