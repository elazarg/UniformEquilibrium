# Positive-joint diagonal endpoint: top-level decomposition and import audit

Author: `CODEX_MINER`

Status: **complete source audit; no new mathematical export.**  The diagonal
endpoint and exact-prefix-limit results are now type-checked in the current
working tree.  They remove the positive-joint source arm from any
**uniform-payoff target** decomposition, but they do not consume that arm in
the stronger AGKRS S.1/S.2/S.3 classification.  The two ledgers must not be
merged.

Audit performed at repository head `26f2261` against the current changed
source tree.

## 1. Current checked declarations and import state

Both of the following current files type-check directly with `lake env lean`:

- `UniformEquilibrium/Quitting/Classification/Existence/`
  `PositiveJointEndpointUniformPayoff.lean`, containing
  `QuittingPositiveJointPrefixReachPunishmentEndpoint.`
  `isUniformEquilibriumPayoff` and its positive-joint source and no-sure-exit
  residual corollaries;
- `UniformEquilibrium/Quitting/Classification/Existence/`
  `PositiveJointExactPrefixOrbitDiagonal.lean`, containing
  `exactPrefixPair_eq_diagonal`, `exactPrefixValue_mem_diagonal`,
  `SummableChargeAllContinuePort.limit_mem_diagonal_of_endpoint`, and
  `limit_isUniformEquilibriumPayoff_of_endpoint`.

At the initial audit boundary both files were untracked and no Lean file
imported either one.  During the subsequent integration pass,
`Existence/All.lean` was updated to import both modules.  They remain untracked
at this working-tree snapshot, while the paper-facing Literature module still
imports the older endpoint/sequential files.  Thus the intended inventory
closure is now staged in the working tree; landing the files is integration
work, not a mathematical gap.

The corresponding proof and independent PASS audit are recorded in
[`CODEX_MINER__AGKRS_DIAGONAL_EXACT_PREFIX_PORT_CLOSURE.md`](CODEX_MINER__AGKRS_DIAGONAL_EXACT_PREFIX_PORT_CLOSURE.md)
and
[`CODEX_RAMSEY`'s review](../feedback/CODEX_MINER__AGKRS_DIAGONAL_EXACT_PREFIX_PORT_CLOSURE__BY_CODEX_RAMSEY.md).

## 2. Exact branch removed for a uniform-payoff target

The producer

```text
stationary_or_positiveJointPrefixReachSource_or_uniqueExceptionalOwnerSource
```

splits a `QuittingDiffuseStationarilyGeneratedApproximateEquilibria reward`
into a stationary branch, a
`QuittingPositiveJointPrefixReachSource reward`, or a unique-exceptional-owner
source.  The new checked source corollary consumes the entire middle arm:

```text
QuittingPositiveJointPrefixReachSource.exists_uniformEquilibriumPayoff.
```

No split through `instantPunishment_or_noSureExitResidual`, no sure-exit root,
no exact-prefix orbit, and no summability assumption is needed.  Consequently
the middle arm of the more refined producers

```text
stationary_or_instantPunishment_or_positiveJointNoSureExitResidual_or_uniqueOwner
stationary_or_instant_or_wellSupported_or_noSureExit_or_negativeOwner
instant_or_positiveJointNoSureExitResidual_or_positiveLive_divergentHorizon
```

is also closed whenever the desired conclusion is merely existence of some
uniform-equilibrium payoff.

This is a target-identifying strengthening, not the first logical existence
proof from that source.  The already checked composition

```text
source.punishment_approximateEquilibriumExistence
quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence
```

had already supplied an unspecified uniform payoff.  The new theorem gives
the actual diagonal endpoint target, and the exact-prefix module additionally
gives the port-limit target.

## 3. Why no AGKRS classification branch disappears

The positive-joint hypothesis of
`theorem3_4_of_prioritizedSourceClosures` is not a uniform-payoff proposition.
For each `QuittingPositiveJointPrefixReachNoSureExitResidual` it requires

```text
S.1 or S.2 or well-supported S.3.
```

Neither `endpoint.isUniformEquilibriumPayoff` nor
`port.limit_isUniformEquilibriumPayoff_of_endpoint` implies any one of those
three prescribed forms.  Therefore the new declarations do **not** inhabit
`hpositive`, and they also do not inhabit the narrowed `hport` premise of
`theorem3_4_of_prioritizedAndSummablePortClosures`.

The exact positive-joint classification survivor is still produced by

```text
QuittingPositiveJointPrefixReachNoSureExitResidual.
  wellSupported_or_summableExactPrefixPort.
```

After the S.3 arm, it retains an actual endpoint, its no-sure-exit proof, and
a nonempty summable canonical port.  The phantom and ballistic reductions
constrain that survivor, but the zero-charge constant arm and the displaced
signed arm still have no S.1/S.2/S.3 consumer.  They are classification
survivors only, not uniform-payoff obstructions.

## 4. Shortest remaining residuals, separated by target

### 4.1 AGKRS S.1/S.2/S.3 target

The shortest upstream unconsumed source residual is

```text
QuittingPrioritizedRefinedSourceResidualAt reward delta.
```

Its producer interface is

```text
QuittingLCPClassification.QuittingPayoffTable.
  fixedCorrectedBranches_or_cofinally_prioritizedResidual.
```

After the four classified branches fail globally, this producer returns such
residuals at arbitrarily small positive scales.  This is precisely the
`hprioritized` input still assumed by the Literature capstones.  Independently,
the positive-joint summable-port classification survivor described in
Section 3 remains the second capstone input.  The diagonal endpoint theorem
removes neither classification obligation.

### 4.2 Finite-quitting uniform-payoff conjecture

None of the AGKRS residuals above is a new uniform-payoff obstruction: the
AGKRS theorem starts from approximate-equilibrium existence at every positive
error, and the positive-joint source itself already has the checked
approximate-existence consumer.

The shortest current general counterexample-side algebraic residual is instead

```text
PunishmentNormalResidualHardClass reward.
```

It is produced from a hypothetical failure of uniform-payoff existence by the
checked composition

```text
punishmentNormalResidualHardClass_of_strategicFork_of_
  not_exists_uniformEquilibriumPayoff
    reward (quittingPunishmentNormalPathStrategicFork reward) hnot.
```

For `Fin 4`, the stronger same-table producer used by the active semantic
question is

```text
uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual.
```

Its surviving `FinFourQuantitativeFullSupportHardResidual` retains the terminal
exploitability witness, full-support packet, full normal core, punishment
normality, and `ResidualHardClass`.  This is the shortest active
conjecture-facing residual with a direct uniform-payoff-or-residual producer;
its descent-or-inert semantic consumer remains open.

## 5. Integration and documentation consequence

Once the two new modules are put into the intended import closure, the
existence inventory should describe the positive-joint endpoint as already
uniform-payoff closed, independently of charge.  The documentation statement
that the port limit lacks diagonal terminal-semantic carrier membership is
stale: `PositiveJointExactPrefixOrbitDiagonal.lean` now proves exactly that.

The AGKRS question must nevertheless continue to list both its prioritized
source consumer and its summable-port S.1/S.2/S.3 consumer.  Replacing either
one by a generic uniform-payoff theorem would change the requested conclusion.
