# Strict-inert fixed-table semidecision: initial triage

## Status

Initial assessment only. Not independently reviewed, not Lean-checked in the
incoming bundle, and not an export candidate.

The incoming `strict_inert` packet has low but nonzero value. Its fixed-reward
filter is a plausible and simple adapter to the checked global Fin4
counterexample semidecision. It does not consume, eliminate, or construct a
strict normalized-inert machine.

## Claim being assessed

For a normalized rational Fin4 reward code `rewardCode`, define a fixed-table
filter by running the checked global semidecision stage and retaining its
certificate exactly when the emitted reward code equals `rewardCode`.

The proposed completeness statement assumes

```text
source : FinFourMinimumAtomProducer reward bound
rewardCode.realReward = reward.
```

It concludes that the filter emits a finite exact counterexample certificate
for `rewardCode`.

## Valid core

The checked theorem

```text
exists_finFourCounterexampleStep_of_rational_infimum_pos
```

in `Research/Quitting/FinFourCounterexampleSemidecision.lean` says that every
normalized rational reward code with positive unrestricted terminal
exploitability infimum occurs at a finite global stage. Filtering that output
by decidable equality of reward codes preserves the witnessing stage.

A `FinFourMinimumAtomProducer` contains a hard residual, and that residual
retains a positive terminal exploitability witness on the same reward table.
The standard comparison from a terminal gap to the exploitability infimum
therefore supplies the positivity premise required by the semidecision.

Subject to compilation, the proposed fixed-table origin and completeness
lemmas are consequently sound.

## Why this is not a strict-inert result

The argument never uses an inert inequality or normalized-inert geometry. The
premise `FinFourMinimumAtomProducer` is already available only in the
positive-gap counterexample regime: its residual contains the global terminal
exploitability witness that the certificate will re-express.

Thus the logical content is

```text
supplied positive all-behavior gap on a rational table
  -> the already complete exact semidecision eventually certifies that table.
```

It is not

```text
local strict-inert data -> positive global gap,
```

and it does not prove that a strict-inert table exists or is impossible. It
therefore gives no progress on the missing strict-inert consumer.

The arbitrary proposition parameter `P` merely threads an already supplied
fact through the existential conclusion. It establishes meaningful
same-source attachment only when the chosen `P` is itself dependently indexed
by the same `reward`, `source`, and packet. In its generic form, it adds no
mathematical relation between the certificate and `P`.

## Computational qualification

The definition is executable, but it is an inefficient fixed-table procedure:
it scans the global natural-number enumeration and discards every certificate
for other tables. A direct fixed-code resolver would have the same
semidecision guarantee without paying for the outer reward enumeration.

Termination is justified only because the positive-infimum premise is already
supplied. Nontermination for local inert data without a source proves nothing.

## Incoming validation status

The bundle includes a Lean file and patch, but its build log says only
`NO_ROOT`; it supplies no successful kernel build. Consequently none of the
new declaration names should receive a Lean seal from this bundle.

## Source audit

The declarations inspected for this triage were:

- `finFourCounterexampleStep`;
- `exists_finFourCounterexampleStep_of_rational_infimum_pos`;
- `exists_finFourCounterexampleStep_of_real_infimum_pos`; and
- `exists_finFourCounterexampleStep_iff_exists_real_infimum_pos`

in `Research/Quitting/FinFourCounterexampleSemidecision.lean`, together with
the definition of `FinFourMinimumAtomProducer` in
`Research/Quitting/FinFourProducerAtlas/Source.lean`.

## Disposition

Retain as a minor interface observation and a useful warning against treating
source-attached positive-gap data as a producer from local strict-inert
constraints. Do not send it to the export gate unless a later task specifically
needs a fixed-code certificate adapter and the declaration is compiled.
