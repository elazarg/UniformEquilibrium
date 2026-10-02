# Zero-joint cap ledger: Lean coverage

Packet: [CAP_ANCHORED_ZERO_JOINT_LEDGER_AND_HOST_ROTATION_BOUNDARY.md](CAP_ANCHORED_ZERO_JOINT_LEDGER_AND_HOST_ROTATION_BOUNDARY.md).
Moved unchanged from `exports/` after targeted checks and named builds.

## Exact ledger and source consequences

[`FiniteWordWeightedCapDefectLedger.lean`](../../UniformEquilibrium/Quitting/Root/FiniteWordWeightedCapDefectLedger.lean)
retains the existing aggregate ledger and adds
`quittingFiniteWordPlayerCapDefectLedger`, its nonnegativity, the literal
playerwise telescope
`quittingTerminalDeviationDebt_literalRootStack_eq_playerLedger_add`, and
`quittingFiniteWordPlayerCapDefectLedger_append`. Every defect is computed
against the complete cap of the actual suffix. The aggregate ledger equals
the sum of these coordinate ledgers.

[`ZeroJointCapLedgerBoundary.lean`](../../UniformEquilibrium/Quitting/Root/ZeroJointCapLedgerBoundary.lean)
proves:

- `terminalExploitability_tendsto_zero_iff_playerLedger_tendsto_zero` and
  `exists_uniformPayoff_of_zeroJoint_playerLedgers`;
- `not_two_positive_deletedClock_limits_of_joint_zero`,
  `exists_fixedHost_subsequence`, and
  `fullyScreened_append_and_not_exploitability_tendsto_zero_of_outerLedger`;
- `minimum_le_liminf_capLedger` and the eventual half-minimum lower bound;
- `exists_positive_minimum_and_fixed_capLedger_payer_of_no_uniformPayoff`,
  which derives a positive global minimizer and selects one fixed player on
  a strict subsequence with ledger at least one eighth of that minimum.

The exact survival append laws are in
[`LiteralRootStackSurvival.lean`](../../UniformEquilibrium/Quitting/Root/LiteralRootStackSurvival.lean).
The reusable ledger and append results were moved out of Research, not copied.

## Literal two-profile boundary

[`HostClearingBoundary.lean`](../../UniformEquilibrium/Quitting/Examples/HostClearingBoundary.lean)
keeps the original host-clock profile distinct from the marked profile.
[`HostClearingCapLedgerBoundary.lean`](../../UniformEquilibrium/Quitting/Examples/HostClearingCapLedgerBoundary.lean)
adds `marked_outsider_capDefect` and `marked_outsider_capLedger`, both exactly
one at the marked profile with its actual diagonal tail. These complement the
checked original clocks, marked host debt zero, and outsider Quit gain one.

The fixed payer is an aggregate ledger obstruction. It is not a uniformly
defective single row, a paid chronological edge, or a renewed source. The
uniform-payoff consumer remains conditional on vanishing ledgers; the
no-uniform-payoff source consequence supplies a positive ledger instead.

## Verification

Targeted Lean checks and named builds passed for the promoted ledger, survival
append laws, zero-joint boundary, and regression modules. Independent review
checked the source and append statements; parent review checked the added
host-rotation and screening/nonvanishing corollaries. The integrated full
`lake build`, including the exhaustive axiom audit, passed with 11435 jobs.
Trust, import-graph, documentation, duplicate-proof, reward-bound, and
redundant-hypothesis checks passed. The cap-stack foundation was moved out of
Diagnostics so the promoted ledger has no reverse architectural dependency.
