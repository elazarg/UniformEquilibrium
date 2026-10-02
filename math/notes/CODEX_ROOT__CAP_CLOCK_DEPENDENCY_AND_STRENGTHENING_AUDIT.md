# Cap-clock dependencies and checked strengthenings

Author: CODEX_ROOT, recording the independent Astra audit on 2026-09-06.
Checkpoint: `98ea672`, pushed after a silent full build and repository checks.
This mining pass inspected declarations and imports; it did not run additional
Lean checks or derive an equilibrium producer.

## Subsequent integration checkpoints

`bc9a439` and `7e7a4de` are pushed after silent full builds and repository
checks. They integrate the exact cap-clock transport, actual reversed-block
hazard adapter, summable finite-window survival, actual child cap pin and
uniform debt/absorption exit, copied-response residual debt, payoff and root
limits, literal nested cap children, one fixed outsider's copied response,
coherent cap selection, and the expanded outsider endpoint difference.
The exact public interfaces and their boundaries are recorded in
`docs/TOOLKIT.md`.

`dfdbee8` is pushed after a silent full build and repository checks. It adds
the actual infinite survival product and owner debt floor, literal complete
marked-suffix profile and live-root preservation, and exact reach multipliers.
The deadline paid-row theorem now jointly retains the prescribed-support
source, bounded finite-or-Never cap-attaining recipient, cap-attainment
equality, payoff gap, and row witness identities. These are literal theorem
conclusions, not merely witnesses chosen inside the proof.

The positive-survival packet is archived after the silent full build of
`3c6d97a`. Its original-source composition now retains child absorption by
the deadline, the common front limit, and the selected paid observer's debt
and receiving response gain. See
`math/formalized/POSITIVE_SURVIVAL_EXACT_CAP_CLOCK_LEAN_COVERAGE.md`.
The packet's phrase support-Nash defect is corrected in the separate feedback
record: its displayed copied-response formula is ordinary mixed-root regret.

The nested-child packet's owner-root Nash clause, three separate summable
seam terms, and fixed-outsider theorem with the literal infinite-product
floor are integrated in `3c6d97a`. The final reset/shift exclusivity and forced
opponent-survival limit adapters are full-build checked and pushed in
`88709a1`. The packet is archived with
`math/formalized/NESTED_TERMINAL_CAP_CHILD_LEAN_COVERAGE.md`. Selecting the
outsider independently at every depth is not used.

The signed-reset packet is fully covered through `c2789f0`, including the
explicit infinite weighted series, owner-deleted coalition expansion, and
scalar finite-variation boundary tests. It is archived with the separate
`math/formalized/SIGNED_CAP_CHILD_HOLONOMY_LEAN_COVERAGE.md` record.
The actual late selection and joint half-gap transport/child-reset assembly
are checked through `c2789f0`. The renewed source and zero-survival split
are checked and pushed in `1a40773`, after a silent full build. The producer
starts at the unchanged late-reset child, not at a newly installed cap.
The late-reset packet is archived with
`math/formalized/LATE_RESET_SOURCE_RENEWAL_LEAN_COVERAGE.md`.

The unique-sure packet is also archived through `1a40773`, with
`math/formalized/UNIQUE_SURE_SHIFTED_CAP_RAY_LEAN_COVERAGE.md`.
Its theorem accepts any supplied actual exact-prefix ray and a supplied
positive exploitability gap. The old anchor needs a sure row by its finite
deadline, not exactly at that deadline. The literal last-zero child retains
the new owner's shifted finite-or-Never cap; the original anchor's zero debt
and deadline survive the relevant unilateral deviations. No decreasing rank
or universal renewal charge is asserted.

In the installation packet, the literal stationary suffix, full semantic equality,
off-minimum two-cut exit, and fixed proper-segment root expenditure are
checked through `c2789f0`. The final expenditure premise generalization
from all-index to eventual source bounds is full-build checked and pushed
in `3ccfa78`. The packet is archived with
`math/formalized/CAP_INSTALLATION_SEGMENT_LEAN_COVERAGE.md`.

## Dependency-first assignments

### Exact cap transport and literal genealogy

Reuse `exists_pureTimeCap_zero_or_map_succ_of_suffixAttainer`,
`quittingPureTimeBehaviorStrategy_optionMap_succ_eq`, and
`update_quittingRootThenContinuationProfile_pureTime_succ_eq`
(`UniformEquilibrium/Quitting/Root/PureTimeCapPrefixSelection.lean`).
Finite-or-Never attainment under an opponent deadline is already supplied by
`exists_pureTime_le_deadline_or_never_terminalPayoff_eq_cap`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineCapSelection.lean`).
It requires one distinct opponent's sure live row, not a bound on every
counterfactual clock. Never and simultaneous stopping at the deadline remain.

The missing adapter should derive shifted attainment after an exact root
against the actual suffix payoff. Positive own Continue probability should
suffice for the opponent-survival debt equality; joint survival positivity
belongs only in the subsequent strict-positivity claim. Iterate this to the
literal quit time equal to the prefix length and the product debt identity.
A copied outsider response instead scales its gain by joint survival.
Transported attainment and child equality must be proved, not supplied fields.

This chunk is assigned to a Sol formalizer. It feeds the positive-survival,
nested-child, signed-reset, and unique-sure packets.

### Reverse exact words and hazard bounds

Reuse the reverse stacks and literal profile identities in
`UniformEquilibrium/Quitting/Paths/ReversePrefixStoppingLaw.lean`,
`quittingLiteralExactWordBoxPath`
(`UniformEquilibrium/Quitting/Bellman/Finite/LiteralExactPrefixBoxPath.lean`),
and `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`).

The required adapter derives one bound for every partial marginal-hazard sum
of a literal infinite exact-prefix sequence under Fin4 no-uniform-payoff.
No normality or positive-singleton premise needs adding. Separate the resulting
summability, uniformly near-one late finite-window survival, positive survival
from time zero when every root survives, and finiteness of zero-survival roots.
`one_sub_sum_range_le_prod_one_sub` (`MathUE/DivergentChargeRecurrence.lean`)
already gives the needed finite-window bound; logarithmic infinite products
are unnecessary. Front-escape consumers must retain the exact tail-Never
hypotheses of the reverse-prefix stopping-law theorems.

### Late-reset exit must start at the actual child

`eventually_every_exactRoot_has_debtDrop_and_absorption_at_immediateQuitCapReset`
(`UniformEquilibrium/Quitting/Root/NestedImmediateQuitCapExactPrefixExit.lean`)
solves its root at the parent payoff. It is not the late-reset packet's child
adapter. On actual children with a fixed observer debt at least `delta`,
Quit-zero cap attainment, and vanishing generating-row opponent absorption,
derive child cap proximity to the singleton and use
`fixedCapPin_coordinateDebtDrop` and `fixedCapPin_totalDebtDrop`
(`UniformEquilibrium/Diagnostics/Quitting/FixedCapPinCoordinateDebtDrop.lean`).
Retain the packet's debt expenditure `min (delta/2) (delta^2/(16*M))` and
absorption floor `min 1 (delta/(16*M))`. The subsequent root is exact against
that child's actual payoff, not the parent's.

### Installation segment and two-cut return

This is largely independent of the preceding three chunks. The one-profile
collar theorem `exists_eventual_offMinimum_collar_of_completeCap_tendsto_singleton`
(`UniformEquilibrium/Diagnostics/Quitting/CompleteCapSingletonLimitCollar.lean`)
should expose its compact-slab argument uniformly over actual profiles with
the same cap-coordinate bound. Then use debt convexity and exact law affinity
in `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`.

`ScalarHazard.shift_convexMix` and `BooleanHazard.shift_convexMix`
(`MathUE/Probability/DiscreteHazardConditionalMixture.lean`) support the literal
surviving-suffix adapter. Equal stopping laws alone do not imply arbitrary full
behavioral profiles are equal. The artificial silent mark in
`SilentPaddingTwoCutSource.lean` is not the packet's cap-installation row.

## Checked results stronger than packet estimates

- `abs_quittingForcedContinueOwnerCorrection_le_two_mul`
  (`UniformEquilibrium/Quitting/Root/ForcedContinuePayoffDisplacement.lean`)
  gives `2*M`, where the packet allows `4*M`.
- `abs_terminalChildPayoffDisplacement_next_sub_le` in the same file uses
  this sharper owner-hazard correction.
- `abs_quittingForcedContinueEndpointRemainder_le_four_mul`
  (`UniformEquilibrium/Quitting/Root/ImmediateQuitCapDisplacement.lean`)
  gives `4*M`, where the packet allows `6*M`.
- `exists_tendsto_terminalChildPayoffDisplacement`
  (`UniformEquilibrium/Quitting/Root/TerminalChildPayoffDisplacementSequence.lean`)
  needs only summability of forced-child absorption and owner hazard, not
  full hazard summability, no-uniform-payoff, exact Nash, or a distinct observer.

The analytic polynomial theorem in `98ea672` also allows arbitrary finite
dimension, a box not containing the rewards, and arbitrary real floor vectors.
See `CODEX_ROOT__POLYNOMIAL_SEPARATOR_LEAN_DEPENDENCY_AUDIT.md` for exact names.

## Further strengthenings and proposals

`exists_terminalChildPayoffDisplacement_limit_le_neg_of_frequently_quitZeroCap`
(`UniformEquilibrium/Quitting/Root/CofinalImmediateQuitCapDisplacementLimit.lean`)
now gives the full bound `-delta`, instead of `-delta/2`. It is full-build
checked and pushed in `88709a1`, and the literal coherent dichotomy consumes
the stronger result.

The latest Astra pass also found that the finite reset estimate's positive
Continue premise follows from its positive debt floor. Removing that premise
propagates to the limiting theorem and removes early positive joint survival
from the signed dichotomy. It does not remove positivity from the
infinite-product fixed-debtor theorem. These premise removals are also
full-build checked in `88709a1`.

The earliest-absorption proof of pair-only terminal rigidity appears to work
for any fixed cardinality at least two: if off-cardinality finite terminal
mass is zero and some finite absorption has positive mass, one coalition has
mass one. Thus allowing Never initially should still give the dichotomy all
Never or one deterministic fixed-cardinality coalition. The local product-row
lemma already supports every such cardinality; the global abstraction is not
yet checked. Cardinality one must remain excluded.

A supplied polynomial potential can also feed the existing arbitrary-path
recharge telescope, retaining empty words and zero charges. This would give
a polynomial-valued horizontal recharge necessity. It would not construct
renewed phases or show that cap installations are robust edges.

## Remaining source boundary

The four remaining cap-clock/reset exports require compatible actual sequence and
phase selections. The polynomial characterization constructs its certificate,
and the recharge theorems already account for supplied phases. Neither by
itself supplies those missing actual sources or their downstream consumers.
