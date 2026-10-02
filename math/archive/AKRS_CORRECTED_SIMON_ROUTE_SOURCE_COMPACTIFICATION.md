# Optional corrected-Simon source compactification architecture

## Disposition

This is an optional alternative proof architecture, not an open result or an
active formalization target.  The forward S.1/S.2/S.3 implication of AGKRS
Theorem 3.4 is already proved by
`QuittingPayoffTable.stationary_or_instantPunishment_or_sequentiallyPerfectAbsorbing`
in `UniformEquilibrium/Quitting/Classification/Existence/AGKRSTheorem34.lean`.
Nothing in this record is needed by that theorem or by the current Fin4
frontier.

## Alternative architecture

Start from one actual arbitrary-behavior approximate-equilibrium source for a
finite quitting payoff table and pass through Simon's corrected pointwise
classification, whose fourth output is stationarily generated.

Can the extraction and compactification be made source-faithful so that:

1. the selected source retains every positive joint-prefix reach and fixed
   exceptional-owner datum used by later suffix arguments; and
2. each diffuse stationarily generated output yields literal S.1, S.2, or a
   well-supported completely absorbing S.3 sequence?

The terminal-jump output must be allowed to land in S.2.  Equivalently, a
selector which has already retained failure of S.2 may eliminate that output
and request S.1 or S.3 from the residual branch.  The unconditional interface

```text
diffuse stationarily generated source -> S.1 or S.3
```

is stronger than the source proof justifies and is not the intended target.

## Existing comparison

The checked direct route sends the approximate-equilibrium family to an
actual vanishing-Never root-sequence source, an absorbing completion, and one
chronological limit.  A terminal total jump gives S.2; absence of one gives
S.3; the preceding zero-solo alternative gives S.1.  Thus solving the optional
question above would clarify the corrected-Simon factorization, not strengthen
the established forward trichotomy.

## Nonanswers

- discarding the stationarily generated output;
- returning an abstract compact point without its actual source data;
- assuming S.2 failure without retaining it in the selector; or
- presenting a proposition-valued compiler without producing its source.
