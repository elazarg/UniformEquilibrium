# Inverse membership stretch: Lean coverage checklist

This checklist covers the supplied proofs in
`INVERSE_MEMBERSHIP_STRETCH_SURE_CORE_SIGN_REVERSAL.md`.
The declarations below are checked conditional consumers of actual tables,
profiles, and carrier points. They do not construct the upstream original
worst table or singleton-fiber maximizing final table. The final implementation is pushed in commit `d9c5cd9`. The full
`lake --quiet --iofail build` passed silently, including the exhaustive axiom
audit. Documentation, 113 script tests, 33 experiment reproductions, import
reachability, proof-duplicate, reward-bound, redundant-hypothesis, trust, and
whitespace checks passed on the final source snapshot. An independent Sol
static review found all substantive packet conclusions and boundaries covered.

The packet was moved here byte-for-byte. Its SHA-256 is
`70d9ea22fd61290b1f24fbccdb0df57980a66518e87b7322a61efba810ad5aa7`.
Coverage synthesis: CODEX_ROOT, using the Astra checklist and independent review.

## Global minimum facts: packet Section 3

- `minimumTerminalSemantic_maximumDebt_allPlayersTie` and
  `quittingTerminalDeviationDebt_eq_exploitability_of_attained_positive_minimum`
  (`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`)
  prove all-player ties at positive global MAX minima, respectively on the
  semantic carrier and for actual profiles. The actual-to-carrier minimum
  bridge is `terminalSemantic_minimum_of_actualMinimum` in the same file.
- `minimumTerminalSemantic_maximumDebt_lt_half` and
  `quittingTerminalExploitability_lt_half_of_attained_positive_minimum`
  (same file) prove the strict-half bound. These statements work for arbitrary
  finite nonempty player types, with signed own singletons and unit reward bounds.

## Literal stretch and same-root comparison: Sections 1, 2, and 4

- `quittingTerminalDeviationDebt_oneDateThenNever_eq_losingMass_mul_gap` and
  `quittingTerminalDeviationDebt_oneDateThenNever_eq_expect_of_supported_coherent`
  (`UniformEquilibrium/Diagnostics/Quitting/ScreenedMembershipDebt.lean`)
  are exact unrestricted behavioral-debt identities for the unpadded root.
  The first uses actual averaged-best endpoints; the second needs nonnegativity
  only on product support. `quittingDirectedMembershipGap_update` identifies
  the directed gap's independence of the owner's sampled action.
- `quittingMembershipStretchedReward`,
  `QuittingAgreesWithMembershipStretch`, and
  `quittingDirectedMembershipGap_eq_stretch_on_support`
  (`UniformEquilibrium/Diagnostics/Quitting/MembershipStretch.lean`)
  retain the original table, final table, common stretch parameter, and root.
  Final own singletons may be reselected. The constructed-table unit bound,
  unchanged own singleton, and displacement bound are also proved there.
  The displacement bound is **not** asserted for arbitrary final singleton reselection.
- `le_signedEndpointGapStretch`,
  `signedEndpointGapStretch_eq_self_iff_of_nonneg`, and the bounded-gap
  sign equivalences (`MathUE/SignedEndpointStretch.lean`) give the scalar
  comparison, equality cases zero or two, and sign transport.
- `quittingTerminalDeviationDebt_original_le_final_of_membershipStretch` and
  `losingMass_pos_and_membershipGap_saturated_of_equal_positive_debt`
  (`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchDebtComparison.lean`)
  compare the full debts, derive positive losing mass before cancellation,
  and conclude supportwise saturation using finite-PMF expectation equality.
- `membershipStretch_sameRoot_minimumEquality_and_supportedSaturation`
  (`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchMinimumEquality.lean`)
  proves the actual original-root minimum by the global infimum chain before
  invoking original-table all-player ties. Original/final infimum ordering
  remains an explicit hypothesis supplied by the separate source construction.

## Supported vertex and literal source reversals: Sections 5, 7, and 8

- `exists_supported_pureRoot_zeroDebt_of_saturatedGaps`
  (`UniformEquilibrium/Diagnostics/Quitting/SaturatedMembershipPureVertex.lean`)
  selects a deterministic supported vertex with every full debt zero when
  total root debt is below two. Its counting identity is exact; no correlated
  lottery over replacement profiles is played. The statement is generic in
  the finite player type and requires only a sure opponent for each owner.
- `exists_supported_pureRoot_zeroDebt_at_both_membershipStretch_tables` and
  `not_membershipStretch_coherent_positiveMinimum_finFour`
  (`UniformEquilibrium/Diagnostics/Quitting/InverseMembershipStretchExclusion.lean`)
  retain the **same** supported vertex at both tables and prove the Fin4
  contradiction. Strict half is derived from actual minimum attainment,
  not imposed as another source hypothesis.
- `exists_supported_oppositeMembershipGaps_of_membershipStretch_positiveMinimum_finFour`
  (`UniformEquilibrium/Diagnostics/Quitting/MembershipStretchSupportedReversal.lean`)
  is the literal two-sure source consumer. It chooses actual final averaged-best
  directions internally, proves all full debts positive, and returns one owner's
  opposite strict supported gaps at both original and final tables.
- `exists_twoSureRoot_with_supported_negativeGap_of_membershipStretch_carrierMinimum`
  (`UniformEquilibrium/Diagnostics/Quitting/InverseMembershipStretchCarrier.lean`)
  consumes a positive joint carrier minimum with zero Never/singleton masses.
  It uses the strict-margin product-base realization and retains the entire
  prescribed-payoff/full-cap pair **and** terminal law of one unpadded root.
- `exists_sureOwner_strictOptionalReversal_of_membershipStretch_positiveMinimum_finFour`
  (`UniformEquilibrium/Diagnostics/Quitting/ThreeSureMembershipReversal.lean`)
  delegates the common source argument to the two-sure consumer. If all players
  other than a named optional player are sure, it proves the optional marginal
  lies strictly between zero and one and produces a sure owner's opposite
  Continue-minus-Quit signs at the two distinct canonical optional configurations,
  at both tables. It does not assume optional mixing or pointwise best actions.

## Exact boundary checks: Section 6

- `signedEndpointGapStretch_at_quarter_zero_one_two`,
  `signedEndpointGapStretch_zero_fixes_nonsaturated_one`, and
  `signedEndpointGapStretch_two_atom_signed_mean_lt_original`
  (`MathUE/SignedEndpointStretch.lean`) record the exact scalar values,
  failure of saturation inference at zero stretch, and the signed-average
  decrease despite a positive original mean.
- `membershipCountExample_mixedRoot_debt`,
  `membershipCountExample_expected_losingOwnerCount`, and
  `membershipCountExample_critical_pureDebtVector`
  (`UniformEquilibrium/Diagnostics/Quitting/Regression/MembershipStretchCountBoundary.lean`)
  compute the complete successful and critical-half tables, with their exact
  independent root probabilities, actual full mixed/pure debts, and integer counts.
  `membershipCountExample_critical_half_does_not_force_supported_zeroDebt`
  states the literal critical-half counterexample.
  `membershipCountExample_allNever_strictly_better` and
  `membershipCountExample_mixedRoot_not_global_minimum` explicitly show that
  neither displayed mixed root is a global minimum.
- `membershipScreening_singleton_zero_one_cap_boundary`
  (`UniformEquilibrium/Diagnostics/Quitting/Regression/MembershipStretchTimingBoundary.lean`)
  proves the complete-cap timing seam: changing only an own singleton from zero
  to one leaves the two-sure unpadded cap zero but changes the padded cap and
  one-sure unpadded cap from zero to one. Agreement off own singletons, unit
  reward bounds, and the exact endpoint/cap formulas are proved in the same file.

## Nonclaims retained

No theorem here produces the upstream worst-table/singleton-fiber source,
asserts that every minimizing source has zero Never and singleton mass,
transports calendar-labelled multipliers through root realization, or consumes
the remaining sign-reversing branch. This packet does not prove the Fin4
uniform-equilibrium conjecture. Its global minima are MAX minima over the
full actual-profile/semantic-carrier domains, never SUM or fixed-calendar minima.
