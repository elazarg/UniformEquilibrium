# Renewable barrier saturation: Lean coverage

Packet: [RENEWABLE_CAP_ORBIT_UNIVERSAL_BARRIER_SATURATION_NO_GO.md](RENEWABLE_CAP_ORBIT_UNIVERSAL_BARRIER_SATURATION_NO_GO.md).
Moved unchanged from `exports/` after independent review, targeted checks,
named builds, and a full build. Frozen SHA-256:
`a6c46dfab4d2fe993a61a6121f32e8999c53a7f73b480e8e8c188938c99d0809`.

## Universal hull and raw-debt floor

`quittingUniversalPrefixHull` in
`UniformEquilibrium/Quitting/ControllerTester/RenewableBarrierSaturation.lean`
is the closure of actual finite arbitrary-product-root semantic prefixes.
The module proves closedness, compactness in any invariant reward box,
and invariance under every product-root prefix.

`exists_minimizer_rawMaximumDebt_universalPrefixHull_eq_sInf_wordInf_of_box`
states equation (3) with the literal raw maximum debt on both sides. Seeds
may be outside the behavioral carrier, raw debt may be negative, and the
ambient reward bound is arbitrary rather than fixed to the canonical box.
The generic continuous-objective proof requires a lower bound only on that
box. Carrier and canonical-box statements delegate to this proof.

`quittingUniversalPrefixHull_union_never_eq_carrier` and
`exists_globalMinimum_unionNeverHull_eq_sInf_rawBarrier` give equations
(4) and (5), retaining the carrier-seed restriction.

`sum_quittingRenewableBarrierLift_eq` gives the exact finite telescope.
`canonicalRawBarrier_renewableLedger_and_limsup` specializes it to the
literal raw-debt word infimum and proves equation (8). Source carrier
membership and finite-prefix ancestry supply the required bounds and
prefix monotonicity. There is no assumed monotonicity across response seams
and no absorption-to-envelope strict increase.

## Concrete boundary

`UniformEquilibrium/Diagnostics/Quitting/RenewableTwoClockRegression.lean`
defines the literal four-player table and four finite-clock profiles.
`response_cycle_profiles` retains the four actual unilateral updates;
`response_cycle_exact_caps_and_gains` proves complete behavioral cap
attainment and gain one on every edge. The four `rawMaximumDebt` statements
give raw debt one at every source.

`cycle_source_rawMaximumDebt_wordInf_eq_zero` proves raw envelope zero at
all four states. `exists_cycleHull_minimum_rawMaximumDebt_eq_zero` gives
the attained raw-debt floor of their entire universal-prefix hull, not only
the displayed source values. The actual `sentinelProfile` is terminal Nash
against every unilateral behavioral deviation and attains global carrier
raw-debt minimum zero, as stated by
`sentinelProfile_isZeroAsymptoticNash` and
`sentinelProfile_isMinimum_rawMaximumDebt`.

This is a route exclusion, not a positive-minimum game or a counterexample
to uniform-equilibrium existence. A charged predecessor phase and a cap
replacement do not acquire an additional raw-envelope comparison here.

## Verification

Both modules passed targeted warning-as-error checks and named builds.
Independent reviews checked the general hull/ledger and concrete regression;
the final review prompted explicit raw-objective and cycle-hull statements.
The full `lake build`, including `AxiomAudit`, passed with 11445 jobs.
Trust, import-graph, documentation, and cross-lane duplicate checks passed.
