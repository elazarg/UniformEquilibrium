# Review of corrected Fin4 terminal-exit theorem

## Verdict

Pass as an honest refined-boundary result. The correction properly retracts
the false paid-row-to-near-return implication and replaces it by the checked
paid-cap-port trichotomy.

It does not close the renewable terminal exits. A more accurate descriptive
name would be “paid-exit cap-port refinement.”

## Generic paid-row adapter

Given a positive global minimum, an actual profile, and an attained
`QuittingPaidFirstDisagreementRow`, the proposed construction of
`QuittingPaidCapLiftedSource` is definitionally valid. The checked
`nonempty_summablePort` and
`chargedNearReturn_or_quantitativeDebtDescent_or_inertStall` then give exactly

```text
ChargedNearReturn
or QuantitativeDebtDescent
or InertStall.
```

Only `ChargedNearReturn` contains the exact cumulative punishment-floor path
and its uniform-payoff consumer. This fixes the principal semantic error in
the earlier document: payoff premium is not identified with absorption
charge.

## Off-minimum specialization

`FullReplacementCluster.HasOffMinimumPaidFirstDisagreement` retains:

- strict endpoint separation;
- one fixed nonmover observer and positive gain; and
- eventually an actual paid row on the literal full-replacement profiles.

Selecting one rank from that eventual set is sufficient to instantiate the
generic paid-cap source without changing the profile or reward table. Thus the
off-minimum paid exit genuinely enters the exact trichotomy. It is a second
dispatch, not a terminal consumer.

## Charge-collapse theorem

The claimed sequence result is correct and is already nearly contained in the
checked pointwise estimate

```text
totalAbsorption
  <= (initialDebt - minimumDebt) / minimumDebt.
```

For a fixed positive minimum debt and initial debts tending to it, the
right-hand side tends to zero; nonnegativity then gives
`totalAbsorption -> 0` by squeezing.

This has an important conceptual consequence: a normalized paid premium near
the minimum fibre cannot be converted by this cap lift into a uniform positive
absorption-charge floor. The near-return arm must come from a genuinely
off-minimum source or from additional structure; it cannot be inferred from
the tangent normalization alone.

## Resulting frontier

The renewable support trace still terminates, but its exits now refine as

```text
positive tangent slope                 (open)
flat support entry                     (open)
off-minimum paid first disagreement
  -> charged near-return               (consumed: UE)
   | quantitative semantic-debt descent (open: no renewable rank)
   | inert all-Continue stall           (open)
```

Thus the correction is useful progress in organizing the paid exit, while
explicitly preserving the two real remaining descendants.

## Formal status

The generic adapter and sequence squeeze are not claimed checked in the
packet. Their mathematics is straightforward from the named checked
declarations. No new Lean seal is assigned here.

Sources inspected:

- `PR_76/FIN4_TERMINAL_EXIT_CLOSURE_CORRECTED.md`;
- `PaidCapLiftedSummablePort.lean`;
- `PaidCapPortExactTrichotomy.lean`;
- `PaidCapMinimumFiberContraction.lean`; and
- `FlatCirculationSupportRankElimination.lean`.
