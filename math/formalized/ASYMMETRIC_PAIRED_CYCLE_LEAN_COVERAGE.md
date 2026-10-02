# Asymmetric paired-cycle packet: Lean coverage

Author: CODEX_ROOT. Audit date: 2026-09-07.
Frozen source SHA-256:
`79801826f5e86be6f15ce055ed2b20fb9a78be2f00a95e2f300236135ab219d6`.
The source packet is preserved byte-for-byte.

All substantive packet clauses are covered by integrated Lean declarations.
The final integration is commit `7d59db0`, after a silent full build and
the complete local CI gate: documentation, 113 script tests, 33 experiment
programs, import graph, proof duplicates, reward-bound and order-hypothesis
checks, telescope checks, trust scan, and diff check. The script tests used
`TMPDIR=/var/tmp` because unrelated `/tmp/.git` triggers a safety test;
no test was skipped or weakened. The final trust scan covered 3188 modules.
All relevant production modules are imported by the umbrella and axiom audit.
An independent Astra agent audited the literal declarations and imports and
returned PASS; that review was static, not an independent build.

## Raw source and infinite equilibrium

`GameTheory.PairedCycle.exists_exact_allSuffix_uniformPayoff_of_rawRegion`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleEquilibrium.lean`) constructs
one strictly interior hazard vector from the exact raw reward conditions
and an ordered partition of the entire player set into at least two pairs.
The same actual cyclic profile is exact terminal Nash at every live suffix
against unrestricted behavioral deviations. Its actual value is a fixed
uniform-equilibrium payoff and strictly exceeds every singleton.

The simultaneous polynomial field and all stated rational face estimates
are proved in `MathUE/PairedAffineClearedField.lean` and
`MathUE/PairedAffineIntervalEstimates.lean`. Literal product-root identities
and inactive-player incentives are connected in
`UniformEquilibrium/Quitting/Root/PairedProductRoot.lean`.
The actual values at every phase are identified in
`UniformEquilibrium/Quitting/Cycles/PairedCycleValues.lean`.

## Finite laws, full caps, and horizon bounds

`GameTheory.PairedCycle.exists_one_hazards_all_finiteTruncations_of_rawRegion`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleFiniteSource.lean`) retains
one hazard vector before all phases, truncation lengths, and accuracies.
For every positive cycle count K the literal independent truncation has
payoff `(1-C^K)*v`, full behavioral cap `v`, and debt `C^K*v`, with the
stated geometric error. The early pure-date cap attainer is constructed,
not assumed. The geometric atoms, Never mass and exact censor identity
are in `UniformEquilibrium/Quitting/Cycles/PairedCycleStoppingLaws.lean`.

`GameTheory.PairedCycle.finiteAverage_deviation_error_le` and
`GameTheory.PairedCycle.summable_liveMass_update_and_tsum_le_geometric`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleFiniteHorizon.lean`) give
the absolute terminal/finite-average error and the actual live-probability
tail-sum bound uniformly over every behavioral deviation. The latter is
the tail-sum form of expected absorption date plus one; a separate
random-variable expectation interface is not asserted. The reward bound
covers every coordinate used by deviations, including unnamed coalitions.

## Separation and open regions

`GameTheory.PairedCycle.not_productLow_of_rawRegion` and
`GameTheory.PairedCycle.not_finiteWordWeakSingletonExclusion_of_rawRegion`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleClassSeparation.lean`)
prove both class failures. The finite-word failure uses one actual finite
truncation strictly above all singletons, not just the infinite payoff.

`GameTheory.PairedCycle.strictRawRegion_nonempty_open_subset_rawRegion`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleOpenRegion.lean`) proves
nonemptiness and openness in the full reward space, with an explicit
center table. Unnamed reward entries remain unrestricted.

## Canonical Fin4 source

`GameTheory.PairedCycle.fin4Pivot_infinite_exact_of_selected`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Infinite.lean`) applies
the literal pivot-only scaling/nonpivot shift to the same infinite profile.
Its deviations absorb almost surely. Finite profiles are truncated afresh
after transformation; no translation identity ignores their Never mass.
The transformed value strictly exceeds `(1,0,0,0)` by
`GameTheory.PairedCycle.fin4PivotValue_gt_singleton_of_selected`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Menu.lean`).

`GameTheory.PairedCycle.exists_one_hazards_fin4PivotMenus_all_accuracies`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Source.lean`) constructs
one hazard vector and one menu family before all accuracies. Each positive
cycle count has the exact transformed payoff/cap identities and both
canonical menu inequalities with error at most `(5/3)*(99/100)^(4*K)`.
The attained repair minimum retains those menus' actual nonpivot laws in
`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Repair.lean`.

`GameTheory.PairedCycle.fin4CanonicalChart`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Chart.lean`) is a
homeomorphism from 56 freely varying real coordinates to the canonical
singleton affine space. Its nonempty relatively open region and actual
raw-table preimages supply the small-pivot-repair consumer in
`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4OpenRegion.lean`.

## Scope

The packet's stated class has mathematical, Lean, actual-source, and
downstream-consumer evidence. No odd-player extension, arbitrary outside
player completion, universal normalized-table producer, or general Fin4
existence theorem follows. Finite truncations have positive debt tending
to zero, not exact Nash. No rational residual or selected late-pivot-repair
algorithm is claimed by this packet or its coverage record.
