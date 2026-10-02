# Weighted packets and pivot repair: proof-mining audit

Author: CODEX_ROOT, recording the independent Astra agent's static audit.
Audit date: 2026-09-06. Production checkpoint: `97b0f46`.

## Question and status

Which useful theorem interfaces can be obtained from the completed weighted
finite-packet reduction and actual pivot-repair formalization, without assuming
an arbitrary-game producer? The audit also inspected the overlapping-clock and
nested-reset interfaces. The static audit itself supplied no new Lean proofs.
Subsequent checked strengthenings are identified explicitly below; the other
proposed combinations remain unproved until their own Lean declarations are
checked. This note is not an export.

All games below are finite quitting games with private independent behavioral
randomization, zero Never payoff, and unrestricted unilateral behavioral
deviations. A uniform payoff target is fixed before every accuracy request.
A finite-packet box is fixed before every accuracy and charge request.

## Specified-target repair characterization

For a fixed reward table, distinguished pivot, and payoff vector `v`, the
following is a useful missing interface:

```text
v is a uniform-equilibrium payoff iff
for every ε>0 there are a positive finite deadline, actual finite nonpivot
laws, and a feasible pivot-repair mass such that
  objective < ε
  and every coordinate of prescribedPayoff differs from v by less than ε.
```

The existing `smallPivotRepairValue_iff_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairUniformPayoffCharacterization.lean`)
already covers arbitrary signed rewards and every supplied pivot, but quantifies
existentially over the target. The target-preserving version can combine:

- `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
  (`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`);
- `exists_feasible_mass_payoff_eq_and_objective_le`
  (`UniformEquilibrium/Quitting/Terminal/PivotRepairSourceCompression.lean`);
- `exists_law_payoff_eq_and_exploitability_le_objective_add`
  (`UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralApproximation.lean`)
  and the existing terminal-target acceptance theorem.

The boundary realization preserves the prescribed payoff exactly even when
the behavioral repair infimum is not attained. This is a proposed composition
of known results, not a producer of approximants for arbitrary games.

## Exact outer infimum and finite deadlines

The same maps suggest that the infimum over all finite-opponent repair values
equals the unrestricted behavioral exploitability infimum, independently of
the pivot. One direction uses arbitrary-error realization of feasible masses;
the other uses `exists_finiteDeadlineTimingProfile_approximation` followed by
actual source compression.

A stronger finite-dimensional package would minimize jointly over finite
opponent simplices and feasible mass coordinates at each deadline. It needs
joint continuity in the opponents, which is not supplied by the fixed-opponent
`continuous_objective` and `exists_objective_minimizer`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean`). Compactness
should then give attainment and deadline inclusion should give monotonicity.
This elementary analysis is still proposed work. It does not give behavioral
attainment, joint convexity, an effective deadline, or convergence to zero.

## Pair-law adapter and consumer

The generic pair and incomparable-overlapping-coalition inequalities are proved
in `MathUE/Probability/IndependentFirstStoppingPair.lean` and
`MathUE/Probability/OverlappingFirstStopping.lean`. The pending overlapping-clock
export still needs the literal behavioral-profile terminal-coalition adapter
and its conditional negative consumer. The relevant source bridge is
`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.

Combining the overlapping and disjoint coalition results should also cover
any incomparable coalitions each of size at least two. This is a small generic
adapter, not a characterization of the full coalition-law body.

Valid pair-law inequalities should not tighten the exact inner pivot-repair
LP: its provisional laws already realize every feasible point's prescribed
terminal outcome distribution. The relaxed first-atom boundary affects cap
realization, not that prescribed distribution. A literal coalition-law adapter
would make this observation a short checked consequence.

## Weaker local reset hypotheses

The local half-wall and exact-prefix exits in
`UniformEquilibrium/Quitting/Root/NestedImmediateQuitCapExactPrefixExit.lean`
now accept convergence of the selected player's opponent absorption to zero
directly. This strengthening is proved in Lean, integrated, and passed a silent
full build at `8b7f1ad`. The declarations include
`eventually_terminalPayoff_le_singleton_sub_half_at_immediateQuitCapReset` and
`eventually_every_exactRoot_has_debtDrop_and_absorption_at_immediateQuitCapReset`.
The nested source, positive eventual debt floor, reward bound, and reset
conditions are retained. Summability remains a hypothesis of the separate
simultaneous payoff-limit theorem. No regenerated source is supplied.

## Checked finite burn-in strengthenings

The polynomial-forward export assumes bounded annotations throughout its finite
burn-in window. The checked theorem
`quittingPunishmentFloor_le_of_finite_endpointErrors_after_burnIn`
(`UniformEquilibrium/Quitting/Bellman/Finite/FiniteEndpointErrorPunishmentFloor.lean`)
needs only `-B ≤ value 0 player` for each player. No later annotation bound or
initial upper bound is needed. For finite players, a positive coordinate reward
bound `M`, normality, positive target error `τ`, and both endpoint inequalities
with error `ζ ≤ min (τ/2) (τ²/(8*M))`, any fixed cutoff satisfying
`M+B < L*τ²/(8*M)` gives the punishment-minus-`τ` floor at every endpoint from
`L` through the finite horizon. The core needs neither `ζ ≥ 0` nor `M ≤ B`.
It assumes no exact Bellman equation or actual-tail realization. This stronger
declaration passed a silent full build and was pushed in `0ab32a9`.

Consequently the same-box producer equivalences also need no `M ≤ B`:
`hasFloorFreeExactFiniteForwardPackets_iff_exact` and
`hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted`
(`UniformEquilibrium/Quitting/Projective/FloorFreeForwardPacketInputRemoval.lean`)
hold for every supplied coordinate-box radius `B`. Normality and a positive
coordinate reward bound remain. These declarations are integrated in `3a786b2`
and passed the silent full build, trust, import-graph, documentation,
duplicate-proof, and redundant-hypothesis checks. The suffix
construction retains the literal shifted roots and values, and chooses its
cutoff before the requested charge. These are producer equivalences, not
existence of a producer for an arbitrary game.

## Checked stationary translation strengthening

For an actual stationary terminal `e`-Nash profile, write `U` for its literal
payoff, `a` for one-stage absorption, and `alpha_i` for the probability that
every opponent of player `i` Continues. The literal Never deviation proves
`Continue_i(U)-U_i <= e*(1-alpha_i)`. Consequently, translating to `U+2e`
gives ordinary root regret at most `2e*a`, improving the export's stated
`3e*a`. The Bellman residual is exactly `2e*a`. This does not improve the
general support-local, nonstationary translation bound.

The declarations are
`quittingRootContinuePayoff_sub_stationaryPayoff_le`,
`quittingRootCoordinateNashDefect_stationaryUpwardTranslate_le`, and
`quittingStationaryUpwardTranslate_sub_successor_eq`
(`UniformEquilibrium/Quitting/Stationary/UpwardTranslation.lean`). They work
for arbitrary finite player types, use unrestricted behavioral Nash, and
include the zero-absorption case. The cap/punishment floor is proved for the
same actual stationary profile.

`exists_stationaryAbsorbingRoot_generating_weightedPackets`
(`UniformEquilibrium/Quitting/Projective/StationaryAbsorptionWeightedForwardPacket.lean`)
chooses one stationary source per requested tolerance before every later
charge request. Each resulting packet carries literal equalities for the
same root and translated payoff. One positive singleton reward ensures
positive absorption for sufficiently small errors; normality is not needed.
The fixed coordinate box has radius `M+2`. These results passed a silent
full build and all repository checks and are integrated in `1bb413a`.

## Proposed one-sided weighted seam estimate

For a nested cap child, let `Δ_i=W_i−U_i`, force owner `b` to Continue, and
retain outsider `i`'s Quit probability `q_i`. The audit proposed

```text
ordinaryRegret_i(bar_q,W)
  ≤ 4M q_b + bar_s_i (q_i max(Δ_i,0) + (1−q_i) max(−Δ_i,0)).
```

The suggested proof couples the two opponent roots and then uses the two
positive parts of the Quit-minus-Continue gap. This estimate has not been
independently reviewed or checked in Lean. It should not be used as a supplied
packet theorem yet.

Even successful seam control on one summable genealogy cannot supply weighted
packets of every charge. Source renewal, compatible concatenation, and unbounded
physical charge remain separate requirements. No arbitrary-game packet producer
or solution of the Fin4 conjecture was found in this audit.

## Next check

Formalize the specified-target composition from the named sources.
Keep the outer-attainment proposal and weighted seam
estimate separate from those known-proof implementation tasks.
