# Summable-tail normal floors and fixed reset exits: Lean coverage

Packet: `FIN4_SUMMABLE_WAIST_NORMAL_FLOOR_AND_FIXED_RESET_EXIT.md`.
Frozen SHA-256:
`6506e3fb0326a2d790e9902c0e14fa420708cd64ab928c2ef2080701d6cb2556`.

Paths below are relative to the project root. The exported packet is retained
unchanged. Its preparation-time nonclaim about Lean coverage is superseded
by this separate record.

## Normal-floor theorem

`punishmentValue_le_of_normal_of_summable_exactNashBellmanTail` and
`summableExactNashBellmanTail_floorSafe_of_allNormal`
(`UniformEquilibrium/Quitting/Bellman/Finite/SummableExactNashBellmanPunishmentFloor.lean`)
prove Theorem A for arbitrary finite player types and an arbitrary finite
common bound on rewards and displayed values. The tail has literal chronological
Bellman equations and exact root Nash against the next value; its joint
absorption charge is summable. Every normal player is above its unrestricted
behavioral punishment value at every date. The canonical reward-box theorems
are specializations, not an additional restriction on the general result.

`value_le_of_punishmentValue_violation_of_exactNashBellmanTail` factors the
bound-free propagation argument. Boundary convergence and singleton domination
are supplied by the existing absorption-path boundary theorems.

## Singleton-gap exit

`quittingTerminalSemanticPrefix_debtDrop_and_minAbsorption_of_carrier`
(`UniformEquilibrium/Quitting/Root/SingletonGapSemanticDebtDescent.lean`)
proves Theorem B for every exact independent product root against the supplied
prescribed payoff. The same literal semantic prefix remains in the actual
carrier and satisfies both bounds:

- total-debt drop at least `min d0 (min (ε/2) (ε*d0/(8*M)))`;
- joint absorption at least `min 1 (ε/(8*M))`.

The implementation only needs the chosen payoff coordinate bounded by `M`,
along with the reward bound; it derives positivity of `M` from the strict
singleton gap. `singletonGapDebtDrop_and_absorptionFloors_pos` states positivity
of both constants under the packet's positive parameters. The underlying
`quittingTerminalSemanticPrefix_totalDebtDrop_and_absorption_of_singleton_gap`
also gives the stronger absorption estimate `ε/(ε+2*M)`.

## Cofinal cap resets

The following declarations are in
`UniformEquilibrium/Quitting/Root/NestedImmediateQuitCapExactPrefixExit.lean`:

- `exists_nestedPayoffLimit_le_singleton_sub_debtFloor_of_cofinal_quitCap`
  proves simultaneous coordinatewise convergence of the actual nested-profile
  payoffs and bounds the selected limit by its singleton reward minus the
  full fixed debt floor.
- `eventually_terminalPayoff_le_singleton_sub_half_at_immediateQuitCapReset`
  gives the eventual half-floor separation at reset indices directly.
- `eventually_every_exactRoot_has_debtDrop_and_absorption_at_immediateQuitCapReset`
  proves Theorem C's two bounds for every exact root at the literal parent
  payoff: `min δ (min (δ/4) (δ²/(16*M)))` and `min 1 (δ/(16*M))`.
- `frequently_every_exactRoot_has_debtDrop_and_absorption_of_frequently_immediateQuitCapReset`
  retains the cofinal conclusion when resets are cofinal.
- `eventually_resetChild_totalDebt_ge_minimum_add_fixedDrop` gives the fixed
  separation from any supplied lower bound on carrier debt; attainment of
  that lower bound is unnecessary.
- `fixedDebtFloor_exactPrefixDrop_and_absorptionFloors_pos` records positivity
  of the common constants.

The hypotheses retain literal nesting, actual behavioral profiles, one fixed
observer, an eventual positive debt floor, and complete-cap attainment by
immediate Quit at reset indices. The local exit declarations are stronger than
the packet: only the observer's opponent absorption must tend to zero. The
full payoff-limit declaration still assumes summable displayed marginal hazards.
The output is at the parent indexed `n` when the reset is at `n+1`, matching
the packet's displayed formula. Caps range over all behavioral deviations.

## Hypothesis sharpness

`UniformEquilibrium/Diagnostics/Quitting/SummableTailAndSingletonGapBoundaries.lean`
reuses existing two-player counterexamples to prove the packet's two sharpness
claims. These are alternative reward tables, not computations of the particular
tables printed in the packet.

`nonnormal_allContinue_constant_tail_below_punishment` packages an explicitly
bounded constant tail, exact all-Continue Nash and Bellman equations, summable
zero absorption, failure of normality, and strict punishment-floor violation.

`equality_wall_positiveDebt_zero_charge_and_drop` packages an actual carrier
pair with positive coordinate debt and exact singleton equality, an exact
all-Continue root, carrier preservation, zero absorption, and zero total-debt
drop. Thus neither normality in A nor strict singleton separation in B can
be omitted in the general statements.

## Remaining source obligations and verification

Theorems A and B need no nested-child producer. Theorem C consumes a supplied
nested sequence and reset hypotheses. Constructing that sequence and its
fixed debtor from the intended cap-child source belongs to the separate
nested-child packets. No theorem here regenerates that source after the
debt-spending exact prefix, consumes the eventual shifted-cap arm, or proves
uniform-payoff existence.

The general-floor, full-limit, and boundary declarations were directly checked
with warnings as errors and zero diagnostics. The final integrated full
`lake --quiet --iofail build` passed with zero output, including the exhaustive
axiom audit. Trust, import-graph, documentation, cross-lane proof-duplicate,
redundant-hypothesis, and diff checks passed. The source audit separately
verified the already-integrated quantitative exits and their quantifiers.
