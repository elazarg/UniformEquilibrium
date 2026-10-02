# Finite-calendar raw-table tests: implementation dependencies

Author: CODEX_ROOT. Packet read in full on 2026-09-07.
Frozen SHA-256 of `FINITE_CALENDAR_PAYOFF_EXCLUSION_RAW_TABLE_TESTS.md`:
`55db4eb51e4b309de13498bdbabfa1e808b5e3fde35a5fb3a31dc4483e5bb99f`.
This is a bounded source audit and implementation plan, not a Lean seal.

## Dependency order

1. Whole-vector payoff realization on the fixed calendar: for a finite
   nonempty player type of cardinality n, every point in the closure of
   actual payoff vectors has one independent finite timing-law profile on
   n(n+1) dates plus Never, with each marginal supported on at most n+1
   actions. Preserve all prescribed payoff coordinates simultaneously.
2. The literal polynomial first-coalition map and its equality to the payoff
   of the finite timing profile. Fin4 uses twenty dates and eighty-four
   probability variables, including Never separately for each player.
3. Strict deficit, weak subset exclusion, and nonconcentrated-weight
   exclusion are equivalent to the displayed finite-calendar predicates.
   The positive strict margin is obtained from compactness. The group
   condition retains one uniform positive mixing parameter before the
   profile quantifier, but its pair of players may depend on the profile.
4. Attach the actual strict-deficit, group-exclusion, and weak-exclusion
   selectors as they are completed. Realization preserves prescribed
   payoffs only, so none of their cap calculations can be transferred from
   the original profile to its compressed representative.
5. Rational witness extraction, semialgebraic statements, and exact boundary
   fixtures are separate surfaces. The packet explicitly does not require
   an implemented quantifier-elimination engine for the mathematical
   finite-calendar equivalences or their game consumers.

## Inspected reusable mathematics

`Math.LinearAlgebra.exists_nonnegative_finiteCombination_eq_support_card_le`
(`MathUE/LinearAlgebra/FiniteConicSparseCombination.lean`) already preserves
every coordinate of a nonnegative finite combination with support bounded
by the coordinate dimension. Apply it to the payoff vector augmented by a
constant-one coordinate, using `Option player` for the coordinate type.
The added coordinate enforces total weight one and gives the n+1 support
bound. Restrict generators to the original positive-support actions first,
so the sparse replacement cannot introduce a previously absent date.
The checked clock-law implementation below uses this route.

Mathlib's `convexHull_eq_union` and
`eq_pos_convex_span_of_mem_convexHull` in
`Mathlib/Analysis/Convex/Caratheodory.lean` provide an alternative affine
route. No new Caratheodory theorem needs to be developed.

`quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect`
(`UniformEquilibrium/Quitting/Paths/FiniteStoppingLawMixture.lean`) is the
whole-observer affine replacement bridge. The mixed player and payoff
observer are distinct parameters; keeping only the mixer's own payoff is
insufficient. Each player must be compressed against the current opponents,
not against one frozen original profile.

`exists_finiteDeadlineTimingLaws_of_censoredLaws` and
`finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineStoppingLawRealization.lean`)
preserve literal laws and profiles. The deadline menu is `Option (Fin K)`:
it represents exactly dates below K plus Never. Censoring is inclusive, so
the cutoff must be strictly below that deadline. These theorems do not
provide the common increasing calendar-rank map or sparse support bound.

## Boundaries to retain

- The compressed calendar is common to all players and preserves ties as
  well as strict order. Separate unrelated date relabelings are invalid.
- The compact limit is taken in a fixed finite product simplex, then
  recompressed to restore sparse support. There is no assertion of
  terminal-payoff continuity for arbitrary infinite stopping-law limits.
- Rejecting group exclusion has a profile depending on the tested mixing
  parameter; it does not supply one profile defeating all parameters.
- The calendar bound applies to payoff realization, not to equilibrium
  word length or cap realization. Equal prescribed payoffs can have
  different complete response caps.
- The qualitative designated-subset implication is generic over finite player
  types: only the designated owners need nonnegative singleton rewards.
  A bounded audit found the required prescribed-payoff margins in
  `positive_minimum_nonnegativeOwner_quadraticMargins`, rather than just
  a cap margin. Actual-profile approximation then supplies a simultaneous
  strict payoff witness. The composed consumer is now integrated in
  `UniformEquilibrium/Quitting/Paths/FiniteWordWeakSubsetSelection.lean` as
  `exists_uniformEquilibriumPayoff_of_actualWeakSubsetExclusion` and its raw
  counterpart. The constructive finite-word replacement passed the full
  silent build and complete repository gate in pushed `d9c5cd9`. It requires signs only
  on the designated set and chooses one preemption certificate before all
  accuracies. Its date bound depends on that table's preemption gap; the
  reward-table-uniform rational threshold algorithm is separate work.

## Checked first realization layer

`exists_sparseFiniteStoppingLawMixture_wholePayoff_eq`
(`UniformEquilibrium/Quitting/Paths/SparseWholePayoffFiniteMixture.lean`)
is full-build checked and pushed in `dfe13e4`. It sparsifies a finite
mixture of one player's arbitrary strategies within its original positive
support, preserving all observer payoffs simultaneously. No global finite
generator type is required; its finite support supplies that type locally.
The proof uses the augmented-coordinate sparse-combination route above.
It preserves prescribed payoffs only, not complete response caps.

The common calendar-rank map is full-build checked and pushed in `17f06d5`,
in `UniformEquilibrium/Quitting/Paths/CommonStoppingCalendarRetiming.lean`.
It reuses Mathlib's finite-set order isomorphism; only supported dates are
ranked. Independent outcome-law equality retains ties and Never, and
every finite retimed date is below the union calendar cardinality, bounded
by n(n+1) under the marginal support hypothesis.

Sequential compression and final common-calendar bounds are full-build
checked and pushed in `22f7516`, in
`UniformEquilibrium/Quitting/Paths/SparseWholePayoffFiniteStoppingProfile.lean`.
Every update uses the current opponents; the final finite laws preserve
all payoffs, have at most n+1 marginal support points and finite dates
below n(n+1). Repeated players in the update list are permitted.

Fixed-calendar compact realization is integrated in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffClosure.lean`
(pushed commit `7d59db0`, silent full build 43048, complete repository
gate 2461). The actual behavioral payoff set equals the fixed
finite-calendar payoff image and is compact. Every closure payoff has
an exact sparse realization on that calendar. The limit is taken in
the full finite simplex and recompressed afterward. The literal payoff
polynomial equality and degree bound are integrated in pushed commit
`e192288`, after silent full build 87897 and complete repository gate
34229. Raw fixed-calendar predicates are integrated in pushed commit
`11809f7` and passed silent full build 57334 and complete static gate 33928.
The ordered-pair group-exclusion test and actual payoff-set semialgebraicity
are full-build checked and pushed in `33552e5`. The finite-word equivalences
are integrated in `FiniteCalendarFiniteWordPayoffEquivalence.lean`; their
targeted check passed silently. They apply to arbitrary payoff predicates
on nonempty finite player types, not to response-cap predicates.
The shared real quantifier
eliminator and closed rational-formula decision are implemented in
`MathUE/RealQuantifierElimination/QuantifierElimination.lean` and passed a
strict silent full build, using the actual recursive sign-diagram producer.
Arbitrary real-coefficient reification and finite-coordinate semialgebraic
projection are full-build checked and pushed in `f9899cb`. Polynomial-map
images and preimages are full-build checked and pushed in `26d7245`.
Joint reward/calendar polynomials, strict/weak accepted reward-table sets,
and finite-word equivalences passed the full integration build and repository
gate and are pushed in `1f5e4dd`. The group-exclusion accepted-table set,
reciprocal parameter recovery, and strict-deficit/group/weak implication
adapters passed full silent build and complete repository gate and are pushed
in `0a8af85`. Independent static reviews found no defects. These results retain
the actual raw predicate definitions and quantifier order. Rational strict,
weak-subset, and group-exclusion Boolean tests are now integrated and pushed
through `5d3dc4c`, with a full silent build and complete repository gate.
The shared reward-parameter formulas and certified-algebraic versions of
all three tests passed the full silent build and complete repository gate
in `4fe83d8`, which is pushed. Correctness concerns every real table denoted
by the encoding.
This supplies recognition, not counterexample extraction or reciprocal search.
This is not a full-packet seal or a claim of remote CI success.

## Remaining Section 6 fixtures

A bounded static audit found no complete literal seal for these fixtures:

- All-Never and pure-coalition raw points are integrated in
  `FiniteCalendarPurePoints.lean`, including zero Never payoff and literal
  coalition reward evaluation at any finite date. Full build passed.
- The strict-deficit example and zero-table contrast are integrated and pushed
  in `35e2cb9` as `StrictDeficitAndZeroBoundaryTables.lean`: margin one for
  the strict table, failure of every positive strict margin for the zero
  table, and group/weak exclusion for the zero table. The full silent build
  and complete repository gate passed.
- Weak singleton-subset exclusion without group/strict exclusion is checked
  and pushed in `89f2946` as `FiniteCalendarWeakExclusionBeyondGroupBoundary.lean`.
  The pure-zero counterwitness is also unrestricted exact terminal Nash.
- The two-disjoint-pair group-exclusion example is checked and pushed in
  `89f2946` as `FiniteCalendarGroupExclusionBeyondDeficitBoundary.lean`, including
  the actual Fin4 clock adapter and separate correlated convex-hull witness.
  It also explicitly refutes product-low premiums. The required actual
  square-root inequality is already supplied by
  `quittingBehaviorFirstStoppingPairMass_sqrt_add_sqrt_le_one`
  (`UniformEquilibrium/Quitting/Paths/BehaviorFirstStoppingPairLaw.lean`),
  with the same module's equality to terminal outcome masses. It covers
  both disjoint and overlapping pairs. No new clock geometry is needed;
  a six-player reward example is not interchangeable with the Fin4 fixture.
- The full-coalition exact Nash example outside all three classes is
  integrated and pushed in `36e9ced` as
  `FiniteCalendarPredicateFailureExactNashBoundary.lean`. The same actual
  full-quitting profile is unrestricted exact terminal Nash and defeats
  every positive strict margin, every group-weight cap, and every owner
  subset. The full silent build and complete repository gate passed.
- Equal payoff with different caps is now integrated and pushed in `0a8af85`
  as `EqualPayoffDifferentBehavioralCaps.lean`: both actual chronological
  profiles have payoff zero, with unrestricted player-zero caps one and zero.

The general strict-deficit-to-group and group-to-weak implications are no
longer missing source proofs; their integration status is recorded above.
