# Renewed owner-cycle recharge: Lean coverage

Packet: `FIN4_RENEWED_OWNER_CYCLE_LINEAR_RECHARGE.md`.
Frozen SHA-256:
`e8a73e666fea04f26115202e6c76617e17b27fbfe9aee96b6d4f296d0e379966`.
Integrated checkpoint: `e9f3e90`.

Paths below are relative to the project root. The packet is preserved byte
for byte. Its original preparation-time nonclaims do not replace this
subsequent coverage record.

## Actual debt accounting

`QuittingRenewedActualProfileSequence`
(`UniformEquilibrium/Quitting/Root/RenewedActualProfileDebtRecharge.lean`)
stores actual sources and endpoints, a complete behavioral cap-attaining
response, and equality of the resulting child with the next source.
The module proves `owner_child_debt_eq_zero`,
`owner_endpoint_debt_eq_capGain`,
`horizontalDebtInjection_eq_neg_capGain_add_cross`, and
`sum_horizontalDebtInjection_eq_sum_verticalDrop_add_boundary`.

`card_mul_minimumDebtDrop_sub_initial_le_sum_horizontalDebtInjection` and
`card_mul_minimumDebtDrop_add_gain_sub_initial_le_sum_crossPlayerDebtInjection`
give the stated linear lower bounds with the explicit initial total debt in
place of the unspecified bounded constant. The common vertical debt drop is
a theorem hypothesis, not a consequence of root absorption. These statements
work for arbitrary finite player types without normality or a no-uniform-payoff
assumption.

## Literal exact words and full-box capacity

`quittingLiteralExactWordBoxPath`
(`UniformEquilibrium/Quitting/Bellman/Finite/LiteralExactPrefixBoxPath.lean`)
converts a supplied exact prefix word above an actual profile into a literal
full-box charged path. Its `_chargeSum` and `_length` theorems retain actual
absorption and word length. The endpoint payoff is the actual prefixed
profile's terminal payoff; the outermost root supplies its decoration.
An empty word retains the supplied source decoration.

`QuittingRenewedLiteralExactWordSequence.toRenewedPathSequence`
(`UniformEquilibrium/Quitting/Root/RenewedLiteralExactWordSequence.lean`)
uses the actual cap-response phases and literal words. Its horizontal target
is the identical all-Continue-decorated next source. The theorem
`toRenewedPathSequence_horizontalTarget_eq_child` identifies that target with
the actual cap child, not a replacement profile or a limit point.

`finFour_quittingFullBoxExactPredecessor_hasFiniteBudget_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourFullBoxExactPredecessorCapacity.lean`)
supplies a bound for the full relation, with no punishment-floor restriction.
Its canonical potential is the existing `ChargedRelation.value`.
`finFour_renewedLiteralExactWord_capacityRecharge`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourRenewedLiteralExactWordCapacity.lean`)
proves the packet's linear capacity-recharge lower bound, with the global
path budget replacing the unspecified bounded constant.

## Source and consumer boundaries

The packet's supplied-phase theorem is covered. The separate late-reset
packet must still construct those phases from its actual reset children.
That producer is not proved by storing a sequence or by this recharge
inequality. In particular, the existing reset-parent exit theorem must not
be substituted for a reset-child theorem.

The horizontal cap updates are not asserted to be predecessor edges.
Neither debt injection nor capacity recharge is physical absorption charge.
No upper bound on horizontal recharge, equilibrium payoff, or counterexample
is obtained. Finiteness of the owner set is not used as a convergence premise.

## Verification

The full `lake --quiet --iofail build` passed with zero output, including
the exhaustive axiom audit. Trust, import-graph, documentation,
cross-lane proof-duplicate, redundant-hypothesis, and whitespace checks
passed. An independent read-only Astra audit checked literal source coherence,
actual expenditure, and the distinction between the supplied-phase theorem
and the pending late-reset producer.

Additional exact-boundary and minimum-free strengthenings are being
formalized separately; they are not needed for this packet's coverage.
