# Membership-stretch source and inverse-stretch consumer

Author: CODEX_ROOT. Bounded dependency audit of the two accepted exports.
This is an implementation record, not a Lean coverage seal.

## Source construction

`MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md` constructs
an original full-cube worst reward table, stretches its nonsingleton
membership edges, and then maximizes over the four remaining own-singleton
coordinates. The original table and the same positive stretch parameter
must remain available in the output. Final-table contact inequalities alone
cannot replace that provenance.

The source-side implementation dependencies are:

1. Whole-strategy reward robustness and the worst-table maximum. Existing
   Research interfaces must be checked and promoted before production use.
2. The literal edge stretch, preservation of own singleton coordinates,
   uniform reward distance, and strict pure-coalition regret separation.
3. Singleton-fiber maximization with the other 56 coordinates fixed.
4. The packet's common-calendar, softmax-envelope, and silent-profile
   construction, retaining its fixed table and common owner weights.

These steps are not replaced by a structure assuming the final source
fields. No source construction from this packet is claimed integrated here.

## Consumer and independent prerequisites

`INVERSE_MEMBERSHIP_STRETCH_SURE_CORE_SIGN_REVERSAL.md` uses an unpadded
root at date zero, followed by Never, with at least two sure quitters.
Its complete payoff/cap pair attains a positive global maximum-debt minimum.
The consumer compares that same actual root at the original and final tables.

Two independent prerequisites can be implemented before the source:

- All player debts equal the maximum at a positive global maximum-debt
  minimum, using the singleton margin and a literal solo prefix.
- At an attained positive minimum for a unit-cube four-player table, the
  maximum debt is strictly less than one half, using the actual all-Never
  competitor and the same singleton margin.

These are now integrated in
`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`.
`minimumTerminalSemantic_maximumDebt_allPlayersTie` and
`minimumTerminalSemantic_maximumDebt_lt_half` apply to carrier minima for
every finite nonempty player type, not only Fin4. The actual-profile
corollaries extend a supplied attained global minimum to the carrier by
closure continuity. The existing complete-cap solo-prefix formula and MAX
singleton margin supply the proof; signed singletons are allowed.
Full production build and complete repository gate passed, and the module
is pushed in `0a8af85`; independent static review found no defect. No positive minimum
or attaining best response is produced. This player-count generality and
carrier-level statement strengthen the packet's attained Fin4 formulation.

The complete two-endpoint response formula is already supplied by
`oneDateProductQuittingContinuationBestResponseValue_oneDateThenNever_sureQuitter`
(`UniformEquilibrium/Diagnostics/Quitting/OneDateProductRootCaps.lean`). It
requires one sure opponent of the selected player, not root Nash. The
endpoint-mixture identity in `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`
then supports the local debt-as-losing-gap expectation layer, now checked and
pushed in `89f2946` as `ScreenedMembershipDebt.lean`. Its full behavioral debt
identity needs one sure opponent and supported coherent preferences, not root
Nash or a global minimum. Generic pure-update expectation was extracted into
`MathUE/PMFProduct/PureUpdateExpectation.lean`; the existing potential-game API
delegates to it. Full silent build and complete repository gate passed.
The signed edge transform, zero-or-saturated equality cases, and finite
supported-vertex counting argument are integrated. The same-root minimum
comparison and Fin4 exclusion passed the full silent build and repository
gate in `5d3dc4c`, with an independent static adversarial review. The
original global minimum is attained before the all-player tie theorem is
applied. The selected pure vertex has zero full debt at both literal tables.
The global comparison uses both table minima; local stationary conditions
do not suffice.

The strict-margin two-sure product-base realization is attached in
`UniformEquilibrium/Diagnostics/Quitting/InverseMembershipStretchCarrier.lean`.
It passed the full silent build and complete repository gate in `4fe83d8`.
It retains the entire semantic pair and terminal law at one
unpadded root, not merely the minimum objective value. The actual
averaged-best supported-reversal layer and its three-sure specialization
passed the same gate. The latter constructs a sure owner and two distinct
supported optional configurations with opposite strict gaps at both tables,
and forces genuine optional mixing. The actual two-sure opposite-sign source
theorem and all scalar, complete-table count, and timing boundaries are now
checked in `d9c5cd9`, after the full silent build and complete repository gate.
An independent static audit found all substantive packet content covered.
The inverse-stretch packet is archived byte-identically in `formalized/`,
with its exact declaration map in `INVERSE_MEMBERSHIP_STRETCH_LEAN_COVERAGE.md`.
The weak-margin silently padded realization is not interchangeable with it:
an earlier date can expose own-singleton caps that differ between tables.

## Opposed-reversal continuation

`THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS.md` was read in full.
It depends on the same original/final table correspondence and the preceding
inverse-stretch consumer, but narrows exactly the three-sure branch further.
Its maximum-debt tie and strict-half prerequisites are already supplied by
the pushed generic module above, despite their remaining ordinary-math status
in the export's source correspondence.

The new proof work is a signed affine-row comparison with one common optional
hazard, followed by a complete screened-root cap adapter and the original-table
global comparison. The three cases compare the old reversing-row value to the
final minimum; equality needs the optional player's strict slack. Old global
attainment must be established before invoking old-table all-player ties.
The final output is two distinct sure owners with opposite strict membership
reversals. That opposed branch and the two-sure branch remain unconsumed.
This packet is queued after its source and inverse-stretch dependencies;
its new affine-row/actual-source consumers are not yet assigned.

## Nonclaims

Neither packet proves that all minimum sources have zero Never or singleton
mass. The inverse-stretch consumer excludes pointwise coherent supported
preferences, not the remaining sign-reversing branch. No new UE-existence
class, unconditional minimum attainment, or counterexample follows here.
