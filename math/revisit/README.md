# Formalization Revisit Queue

This directory retains export packets that contain useful mathematics but are
not suitable for the active formalization queue as written.

A packet belongs here when at least one of the following holds:

- a stated claim is false or needs corrected hypotheses;
- the useful conjecture-facing content is already proved in Lean, while a
  remaining claim is not worth prioritizing;
- a substantial checked subset exists, but the packet cannot honestly move to
  `formalized/`; or
- completing it requires new infrastructure whose value should be reassessed
  before implementation; or
- the prospective handoff needs self-contained prerequisites or a review
  matching the exact manuscript.

Record what is checked, what prevents promotion, and what would justify
revisiting it. Keep that disposition outside any frozen manuscript.
Historical copies can still cite an old path under `exports/`. For a moved
packet, look for the same basename here. A repaired target returns to
`exports/` after the normal gate. A result moves to `formalized/` when
checked Lean declarations cover its useful scope.

## Handoffs to prepare

- [Zero singleton column](ZERO_SINGLETON_COLUMN_EQUIVALENCE.md).
  The [core proof for review](../notes/CODEX_CURATION__ZERO_SINGLETON_COLUMN_CORE.md)
  includes the closed payoff-and-cap translation for a prescribed owner,
  the clock completion, and the equality of the absorbing, prescribed-owner,
  and maximal signed regret infima. The complete manuscript also retains the
  four-column Never bound and two signed families, with their own
  prerequisites and review scope.
- [Universal rank three](EVERY_FOUR_PLAYER_QUITTING_GAME_PASSES_THE_THIRD_ORDER_TEST.md).
  Include the finite training and validation orders, the quantile transfer,
  the prescribed-clock result, and the 20-plus-one singleton split. The
  matched case also uses the inverse-column calculation and a diffuse race
  on three owners. The
  [recorded reviews](../feedback/CODEX_ROOT__RESET_AND_INCOMING_CONTROLS__BY_INDEPENDENT_REVIEWS.md#conditional-order-tests-and-the-universal-convex-hull-problem)
  distinguish rank-three obedience from the rank-four supplement.
- [Singleton sign census](TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md).
  Bring the sign screening and exact 21-class computation into one
  reproducible handoff. Track the tied cases and later inverse-column and
  behavioral refinements with the review scope for each.
- [Membership stretch](MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md),
  [three-sure minima](THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS.md),
  and [screened roots](GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md).
  Compare the handoffs against the reviewed
  [membership notebook](../notes/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md),
  [three-sure notebook](../notes/THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS.md),
  and [screened-root manuscript](../notes/CODEX_SCREEN_GATE__GENERIC_SCREENED_ROOT_EXPORT_PACKET.md),
  respectively. The three-sure notebook also retains the 684-case rational
  regression. Keep the reviewed versions available until a final handoff
  reconciles the changes and preserves their separate evidence.
- [Fixed-zero signed collision bridge](SIGNED_COLLISION_BRIDGE_UNIFORM_EQUILIBRIUM.md).
  Keep the specified algebraic payoff and the calendar whose regret is
  confined to the initial joining opportunity. The
  [all-real parameter theorem](../exports/SIGNED_COLLISION_PARAMETER_UNIFORM_EQUILIBRIUM.md)
  covers its existence class. The sharper payoff or calendar conclusion
  would justify a separate formalization task.

Other interdependent packets here cover additive and matched reward
families, finite-rank order tests, sparsity, and quiet-player lifts. Preserve
the scope and exact examples of each result when packaging shared
prerequisites. A hash in a review identifies its artifact and scope.
For the [renewable block reduction](RENEWABLE_PERIODIC_BLOCKS_AND_FINITE_PAYOFF_GRAPH.md),
keep the raw-margin theorem and the physical period bound together. The
claim about coverage of the full residual also uses the raw exclusions
in [joint recipient and reverse degree](JOINT_RECIPIENT_AND_REVERSE_DEGREE_UNIFORM_EQUILIBRIUM.md).

## Existing theorem families to compare with Lean

These are mathematical references for source and coverage comparison.
Restore a handoff when it has a precise increment beyond the corresponding
checked declarations and the increment passes the normal gate.

| Retained material | Scope to check before promotion |
| --- | --- |
| [Small premium cores](PREMIUM_CORE_AT_MOST_TWO.md), [attractive triple cores](JOINING_ATTRACTIVE_TRIPLE_CORE_UNIFORM_EQUILIBRIUM.md), [mixed-sign triple cores](MIXED_SIGN_TRIPLE_PREMIUM_CORE_UNIFORM_EQUILIBRIUM.md) | Identify which raw classes, weak boundary cases, and actual-source returns the existing premium-core results cover. |
| [Common leaver](COMMON_LEAVER_WITH_SIGNED_PREMIUMS.md), [support-specific leavers](SUPPORT_SPECIFIC_LEAVERS_WITH_SIGNED_PREMIUMS.md), [weighted floor](WEIGHTED_FLOOR_RETURN_UNIFORM_EQUILIBRIUM.md), [boxed charges](BOXED_NASH_CHARGES_UNIFORM_EQUILIBRIUM.md) | Compare the protected-owner and charge hypotheses against the available consumers. Keep the exact separations between those hypotheses. |
| [Quiet lifts](NONNEGATIVE_SINGLETON_FINITE_QUIET_LIFTS.md), [passive-triple chamber](PASSIVE_TRIPLE_CAP_CHAMBER_UNIFORM_EQUILIBRIUM.md), [proper support chamber](TWO_LEDGER_PROPER_SUPPORT_CHAMBER_UNIFORM_EQUILIBRIUM.md) | Identify any uncovered raw reward regions and specify the required finite-stage or fixed-target transfer. |
| [Random earliest collision](RANDOM_EARLIEST_COLLISION_PAYOFF_KERNEL_BRIDGE.md) | Identify the remaining source-to-consumer step on the original full cap and law carrier. Preserve the finite/Never comparisons and the exact tie obstructions. |
