# Coverage audit for the interval amendment

Auditor: `CODEX_RAMSEY`

Verdict: **the reviewed interval amendment is mathematically PASSed but is not
yet covered by the checked Lean declarations inspected below.**  The packet
currently resides in `formalized/` with both the passive-core theorem and the
interval-sandwich extension.  That directory placement therefore overstates
coverage unless a newer interval row adapter exists outside the inspected
source chain.

## Lifecycle resolution

The original split repaired the overstatement while the interval theorem was
unchecked. The missing Lean coverage has since been supplied by
`IsLiteralStrictFiniteOddIntervalBlockerCore.toStationaryFace` and
`isUniformEquilibriumPayoff_of_literalStrictFiniteOddIntervalBlockerCore` in
`UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCoreRowAdapter.lean`.
The reviewed interval result has therefore been merged back into the single
combined formalized record
`formalized/ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE.md`, and there is no
overlapping interval packet in `exports/`. The constant-passive declarations
remain separately named and their narrower scope is preserved in that record.

## Checked declarations found

The current files

```text
UniformEquilibrium/Quitting/Classification/Existence/FiniteOddBlockerCore.lean
UniformEquilibrium/Quitting/Classification/Existence/FiniteOddBlockerCoreRowAdapter.lean
UniformEquilibrium/Quitting/Classification/Existence/OddBlockerCoreRowAdapter.lean
```

contain the abstract finite odd-core stationary theorem and literal row
adapters whose continuation hypothesis is a constant passive baseline.  In
particular, the inspected adapter declarations include

```text
IsLiteralStrictFiniteOddBlockerCore
IsLiteralStrictFiniteOddBlockerCore.toStationaryFace
isUniformEquilibriumPayoff_of_literalStrictFiniteOddBlockerCore
IsLiteralStrictThreeBlockerCore
excludedValue_eq_baseline_of_passive_rows
IsLiteralStrictThreeBlockerCore.toStationaryFace
isUniformEquilibriumPayoff_of_literalStrictThreeBlockerCore
```

and `OddBlockerCoreRowAdapter.lean` explicitly derives

```text
excludedValue = (1-continueMassExcl)*baseline
```

from equality of every continuation row to that baseline.

## Missing reviewed amendment

The amended packet instead permits coalition-dependent continuation rewards
and assumes only the literal extrema sandwich

```text
L_i^+ < C_i^- <= C_i^+ < H_i^-.
```

Its proof uses the weaker normalized bound

```text
C_i^- <= N_i <= C_i^+
```

and face liminf/limsup estimates; it does not have a constant passive value.
A narrow search found no checked declaration named or implementing
`CoreIntervalBlockerSandwich`, no interval-extrema row adapter, and no theorem
whose literal source hypothesis matches this amendment.

## Required lifecycle repair

The passive-core result may remain represented as formalized.  The interval
amendment should remain an export target until its actual-data adapter and
stationary theorem are checked, or the packet should be split so that only the
passive portion is represented as formalized.  This audit makes no
mathematical objection to the amendment: it has two independent falsification
PASSes and a delta whole-packet PASS.  The issue is only Lean coverage and
directory semantics.
