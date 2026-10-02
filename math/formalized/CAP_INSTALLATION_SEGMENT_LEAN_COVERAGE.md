# Cap-installation segment and two-cut return coverage

Author: CODEX_ROOT. Integration through `3ccfa78` passed the silent full
build and trust, import-graph, duplicate, telescope, and documentation checks.
An independent Astra review checked the packet's quantitative conclusions
and the eventual hypotheses supplied by the actual stationary source.

Frozen packet: `FIN4_CAP_INSTALLATION_SEGMENT_COLLAR_AND_TWO_CUT_PORT_RETURN.md`,
SHA-256 `65909c7782d9f32a526f3c948a81786eb162262fd094ecf807ae0017cd76ed00`.

## Declaration map

- `capResponseSegment_ownerCap_eq` and
  `capResponseSegment_ownerDebt_eq_oneSub_mul`
  (`UniformEquilibrium/Diagnostics/Quitting/CapResponseSegmentCollar.lean`)
  give the actual private stopping-law mixture, constant complete own cap,
  and affine owner debt at an attained response.
- `exists_offMinimum_collar_on_completeCap_singletonSlab`
  (`UniformEquilibrium/Diagnostics/Quitting/CompleteCapSingletonSlabCollar.lean`)
  gives a uniform collar on a closed singleton-cap slab. The stronger slab
  argument supplies the packet's collar directly, without a separate
  tail-cluster construction. No supplied minimizer or compact parameter
  space is needed.
  `eventually_capResponseSegment_debtSum_ge_min_add`
  in the segment module applies this uniformly over the entire closed
  parameter interval, including the fully installed endpoint.
- `eventually_capResponseSegment_exactRoot_debtDrop_and_absorption`
  (`UniformEquilibrium/Diagnostics/Quitting/CapResponseSegmentExactRootExpenditure.lean`)
  proves both packet floors for every sufficiently late exact root at any
  fixed proper parameter. Attainment and original debt need hold only
  eventually, matching the actual source. The prescribed-payoff bound is
  derived from the reward bound. Parameter zero is also allowed.
- `quittingStationaryQuitNowSegment_semanticPair`,
  `quittingStationaryQuitNowSegment_suffix_one_eq_source`, and
  `prefixed_quittingStationaryQuitNowSegment_suffix_two_eq_source`
  (`UniformEquilibrium/Diagnostics/Quitting/StationaryQuitNowSegment.lean`)
  prove full payoff/cap equality and literal unchanged stationary tails.
  Equality holds even at null continuation histories; no positive-survival
  premise is added. The installed row's hazard is at least its parameter.
- `exists_quittingStationaryQuitNowSegmentTwoCut_offMinimum`
  (`UniformEquilibrium/Diagnostics/Quitting/StationaryQuitNowSegmentTwoCutReturn.lean`)
  constructs the actual roots and cuts, retains the entry reach, and proves
  the off-minimum exit inequality using the packet's declared hazard scale.
  `MathUE/ExponentialExcessScale.lean` proves the scale positive and its
  exponential threshold bound directly.

## Scope

The segment identities and quantitative estimates hold for arbitrary finite
player sets under the stated data. The structured Fin4 stationary source
supplies those data separately. The two-cut result is stronger than requiring
near-minimum convergence: the original off-minimum source already satisfies
the exit arm pointwise. It does not exclude simultaneous paid splices, force
a paid-splice output, return to a minimum, renew an exact chronology, or
produce terminal approximate Nash or a uniform payoff. The fixed-root debt
floor does not extend to the fully installed endpoint.
