# Root, singleton-flow, and cap-pin Lean coverage

The following three frozen packets are covered by checked Lean declarations.
Their files were moved from `exports/` without changing their contents.

## Fixed cap-pin expenditure

Packet: [FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md](FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md).

The existing pointwise and finite ledgers are completed by
`fixedCapPin_prefixChain_visitSet_finite_and_ncard_le`,
`fixedCapPin_carrierPrefixChain_visitSet_finite_and_ncard_le`,
`fixedCapPin_reentry_visitSet_finite_and_ncard_le`,
`fixedCapPin_carrierReentry_visitSet_finite_and_ncard_le`, and
`fixedCapPin_reentry_visitSet_finite_and_ncard_le_coordinateSeams` in
[`FixedCapPinDebtVisitBudget.lean`](../../UniformEquilibrium/Diagnostics/Quitting/FixedCapPinDebtVisitBudget.lean).
These prove finite visit sets and the explicit floor-cardinality bounds under
summable errors, replenishment, or coordinate seams. Carrier membership gives
the initial `2 * M` bound. They do not construct a renewed source or prove its
seams summable.

## Exact root and proper singleton-flow closure

Packet: [EXACT_ONE_JUMP_AND_PROPER_SINGLETON_FLOW_CLOSURE.md](EXACT_ONE_JUMP_AND_PROPER_SINGLETON_FLOW_CLOSURE.md).

- `isUniformEquilibriumPayoff_rootSuccessor_of_isZeroRootNash` in
  [`ExactSuccessorClosure.lean`](../../UniformEquilibrium/Quitting/Root/ExactSuccessorClosure.lean)
  covers every exact product root, including zero-survival roots.
- `isUniformEquilibriumPayoff_singletonArc_of_viable_proper` and
  `IsProperViableSingletonFlowChain.isUniformEquilibriumPayoff` in
  [`ProperSingletonFlowClosure.lean`](../../UniformEquilibrium/Quitting/EssentialAPS/ProperSingletonFlowClosure.lean)
  cover one proper viable segment and any finite chain.
- `isUniformEquilibriumPayoff_singletonArc_before_rootSuccessor` in
  [`JumpFlowClosure.lean`](../../UniformEquilibrium/Quitting/EssentialAPS/JumpFlowClosure.lean)
  composes the two closures.
- `ExactRootNonconvexityRegression.exact_root_successor_range` and
  `ExactRootNonconvexityRegression.not_convex_exact_root_successor_range` in
  [`ExactRootNonconvexityRegression.lean`](../../UniformEquilibrium/Quitting/Examples/ExactRootNonconvexityRegression.lean)
  identify the full exact-root image of the displayed two-player table and
  prove it nonconvex. The quantifier covers arbitrary product roots. This
  does not assert that the set of uniform-equilibrium payoffs is nonconvex.

The flow proof reuses `IdealSingletonCarrierBridge.idealSingletonSemanticPair_mem_carrier`:
its arbitrary-reward statement already supplies the finite singleton-block
approximation and complete behavioral caps. No normalization or three-player
hypothesis was added.

## Same-profile singleton handoff

Packet: [FIN4_UNIQUE_SURE_ROOT_SAME_PROFILE_SINGLETON_HANDOFF.md](FIN4_UNIQUE_SURE_ROOT_SAME_PROFILE_SINGLETON_HANDOFF.md).

[`SureRootSingletonHandoff.lean`](../../UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SureRootSingletonHandoff.lean)
proves the restriction to the same induced Nash point, the original root and
stationary-profile equalities, and the literal owner Always Continue repair.
`QuittingTerminalExploitabilityWitness.exists_sureRootHandoff_with_paidAtom_and_floorDispatch`
retains that handoff and its paid endpoint atom, then gives a free player's
punishment-floor failure or the repaired exact orbit with vanishing absorption
and no fixed positive-threshold charged recurrence. The implementation works
for any finite player type and only requires a sure owner; uniqueness is not
needed by this consumer.

## First-root dichotomy

The source-level assembly, common subsequence, finite cap responses, and
stationary Never reset are covered separately in
[FIRST_EXACT_ROOT_DICHOTOMY_LEAN_COVERAGE.md](FIRST_EXACT_ROOT_DICHOTOMY_LEAN_COVERAGE.md).
That record includes the exact-root and outsider-reactivation regression.

## Verification

Targeted Lean checks and independent semantic reviews passed. The full
`lake build`, including `AxiomAudit`, passed with 11421 jobs. The uniqueness
declarations were also checked with `#print axioms`; they use only `propext`,
`Classical.choice`, and `Quot.sound`. The trust, import-graph, documentation,
proof-duplicate, and telescope-hypothesis checks passed.

The subsequent first-root compactification, response, and complete-dichotomy
additions passed a full `lake build` including the exhaustive axiom audit
with 11435 jobs, as recorded in their separate coverage note.
