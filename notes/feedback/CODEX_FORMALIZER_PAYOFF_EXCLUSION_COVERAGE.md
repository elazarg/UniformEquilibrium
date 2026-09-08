# Payoff-exclusion packet coverage audit

This is a source-only formalization audit of the following final export
packets against the canonical Lean declarations present on 2026-09-08:

- `FINITE_CALENDAR_PAYOFF_EXCLUSION_RAW_TABLE_TESTS.md`;
- `PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS.md`; and
- `FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION.md`.

No Lean build, cache write, or theorem-level axiom check was run for this
audit. Exact theorem truth remains the declaration under its imports. None of
the three packets is marked closed here, because each still has at least one
literal claimed conclusion without a matching canonical declaration.

## Finite-calendar payoff exclusion

The fixed-calendar payoff representation and compactness claims are covered by
`quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff`,
`isCompact_quittingActualTerminalPayoffSet`, and
`exists_sparse_finiteCalendarLaws_of_mem_closure_actualPayoff` in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffClosure.lean`.

The arbitrary-predicate equivalence between actual payoffs, raw calendar
payoffs, and literal finite root words is covered by
`forall_finiteCalendarRawPayoff_iff_forall_actualTerminalPayoff` in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPredicates.lean` and by
`quittingFiniteCalendarRawPayoff_eq_finiteRootWordPayoff`,
`forall_finiteRootWordPayoff_iff_forall_actualTerminalPayoff`, and
`forall_finiteCalendarRawPayoff_iff_forall_finiteRootWordPayoff` in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarFiniteWordPayoffEquivalence.lean`.

The strict-deficit, weak-subset, and nonconcentrated-group raw/actual predicate
equivalences are in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPredicates.lean`. The
strict compact margin is
`hasQuittingFiniteCalendarRawStrictExclusion_iff_exists_positive_actual`.
The ordered-pair characterization of group exclusion is covered by
`hasQuittingActualNonconcentratedGroupExclusion_iff_orderedPair` and its raw
and existential variants in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarOrderedPairGroupExclusion.lean`.
The game-independent capped-simplex reduction is in
`MathUE/FiniteCappedSimplexPairReduction.lean` and does not require a separate
cardinality-at-least-two hypothesis. The maximal designated-owner reduction is
in `UniformEquilibrium/Quitting/Paths/FiniteCalendarWeakSubsetMaximalOwners.lean`.

The explicit payoff polynomials, their evaluations, and their degree bounds
are in `UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPolynomial.lean`.
The arbitrary-term formulas and their truth lemmas are in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffFormula.lean` and
`UniformEquilibrium/Quitting/Paths/FiniteCalendarExclusionFormula.lean`.
The payoff set and the strict, weak, and group reward-table predicates have
semialgebraicity theorems in the corresponding
`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffSemialgebraic.lean`,
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRewardTableSemialgebraic.lean`,
and
`UniformEquilibrium/Quitting/Paths/FiniteCalendarGroupRewardTableSemialgebraic.lean`.

Rational raw decisions are implemented by the `decideHas*` declarations and
their `eq_true_iff` theorems in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawStrictDecision.lean`,
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawWeakSubsetDecision.lean`, and
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawGroupDecision.lean`. Fixed reciprocal decisions and
terminating reciprocal searches are in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarReciprocalParameterDecision.lean` and
`UniformEquilibrium/Quitting/Paths/FiniteCalendarReciprocalSearch.lean`. Isolated algebraic reward parameters
are covered for every denoted real table by
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawIsolatedRootDecision.lean`,
`UniformEquilibrium/Quitting/Root/IsolatedRootRewardParameters.lean`, and
`UniformEquilibrium/Quitting/Root/IsolatedRootRewardCoverage.lean`. Strict and weak algebraic rejection
witnesses are in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawAlgebraicRejectionWitnesses.lean`; the
group rejection quantifiers correctly remain one counterexample calendar for
each candidate common group parameter.

The seven boundary items in Section 6 have literal declarations in:

- `UniformEquilibrium/Quitting/Paths/FiniteCalendarPurePoints.lean`;
- `UniformEquilibrium/Quitting/Examples/StrictDeficitAndZeroBoundaryTables.lean`;
- `UniformEquilibrium/Quitting/Examples/FiniteCalendarWeakExclusionBeyondGroupBoundary.lean`;
- `UniformEquilibrium/Quitting/Examples/FiniteCalendarGroupExclusionBeyondDeficitBoundary.lean`;
- `UniformEquilibrium/Quitting/Paths/FiniteCalendarStrictDeficitGroupWeakImplications.lean`;
- `UniformEquilibrium/Quitting/Examples/FiniteCalendarPredicateFailureExactNashBoundary.lean`; and
- `UniformEquilibrium/Diagnostics/Quitting/EqualPayoffDifferentBehavioralCaps.lean`.

Finite strict-deficit and group-exclusion selectors are covered in both exact
and executable-rational forms. Real designated weak-subset selection and its
fixed uniform-payoff consumer are covered by
`UniformEquilibrium/Quitting/Paths/FiniteWordWeakSubsetSelection.lean`. The
sign-free qualitative four-player implication is covered by
`exists_uniformEquilibriumPayoff_of_finFour_signFreeWeakSubsetExclusion` and
its raw corollary in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSignFreeWeakSubsetUniformPayoff.lean`.

The finite-calendar packet is not completely drained because its Section 5
also invokes the table-uniform executable rational weak selector and the
strict-deficit exact every-suffix profile described below.

## Actual selectors and exact suffix limits

Exact finite strict-deficit selection, geometric decay, terminal approximate
Nash, and a fixed uniform payoff are in
`UniformEquilibrium/Quitting/Paths/StrictDeficitFiniteWords.lean` and
`UniformEquilibrium/Quitting/Paths/StrictDeficitFiniteWordRates.lean`. The executable rational counterpart,
including the same literal word and strict debt below the requested accuracy,
is in `UniformEquilibrium/Quitting/Paths/ExecutableRationalStrictDeficitStep.lean`,
`UniformEquilibrium/Quitting/Paths/ExecutableRationalStrictDeficitRates.lean`, and
`UniformEquilibrium/Quitting/Paths/ExecutableRationalStrictDeficitSource.lean`.

Exact finite group-exclusion selection and reciprocal decay are in
`UniformEquilibrium/Quitting/Paths/GroupExclusionFiniteWords.lean` and
`UniformEquilibrium/Quitting/Paths/GroupExclusionFiniteWordRates.lean`.
The executable rational counterpart is in
`UniformEquilibrium/Quitting/Terminal/GroupExclusionApproximatePrefixStep.lean`,
`UniformEquilibrium/Quitting/Paths/ExecutableRationalGroupExclusionStep.lean`,
`UniformEquilibrium/Quitting/Paths/ExecutableRationalGroupExclusionRates.lean`, and
`UniformEquilibrium/Quitting/Paths/GroupExclusionFiniteWordSource.lean`. Its current first-hit result has strict
debt below the requested accuracy and uses the packet constant
`[32M + (8rho-rho^2)D0]/rho^2`.

Real designated weak-subset selection, with singleton signs only on the
designated subset, is in
`UniformEquilibrium/Quitting/Paths/FiniteWordWeakSubsetSelection.lean`. The executable
rational selected-owner engine for the branch where all designated owners are
strictly preempted is in
`UniformEquilibrium/Quitting/Paths/ExecutableRationalSelectedOwnerStep.lean`,
`UniformEquilibrium/Quitting/Paths/ExecutableRationalSelectedOwnerRates.lean`, and
`UniformEquilibrium/Quitting/Paths/ExecutableRationalWeakSubsetSelection.lean`.

The exact deadline horizon estimate is in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineHorizonError.lean` and has
the stronger error `D + 2MN/H`. The selected same-word menu and pivot bounds
are in `UniformEquilibrium/Quitting/Paths/WeakExclusionFiniteWordMenuRate.lean`.

The generic four-player two-pair reward-table entrance of equation (10) is
covered by `hasQuittingActualNonconcentratedGroupExclusion_half_of_twoPairRewardBounds`
and its raw counterpart in
`UniformEquilibrium/Quitting/Paths/TwoPairGroupExclusion.lean`. The favorable-pair
bound need not be nonnegative. The actual pair-mass and Never adapters are in
`UniformEquilibrium/Quitting/Paths/BehaviorFirstStoppingPairLaw.lean`; they reuse
the endpoint-retaining square-root ledger and complete stopping-law limit.

The following are genuine remaining obligations:

1. There is no strict-deficit instantiation constructing one infinite profile
   that is exact terminal Nash at every literal suffix and then proving its
   finite-horizon uniformity. The finite approximants and fixed-payoff
   consumer do not imply this stronger same-profile assertion.
2. The packet's parametric two-player negative-singleton strict-deficit table
   and proof of nonexistence of an exact terminal Nash profile are absent.
   `UniformEquilibrium/Diagnostics/Quitting/TwoPlayerNegativeFiniteMenuBoundary.lean`
   concerns a different constant
   negative reward and only computes a punishment value.
3. The table-uniform dyadic executable rational weak-subset algorithm and its
   `O(n + (M/epsilon)^2 log(16nM/epsilon))` row bound are absent. Current real
   weak-subset selection is fixed-table, and the rational engine covers only
   the all-designated-preempted branch; an executable rational unpreempted
   solo exit and the combined rational selector are still missing.
4. The separate-cross-mass determinant of equation (18) is covered by
   `quittingIndependentTerminalOutcomeLaw_twoPair_crossMassDeterminant` and
   `quittingBehaviorTwoPair_crossMassDeterminant` in
   `UniformEquilibrium/Quitting/Paths/TwoPairCrossMassDeterminant.lean`.
   They retain arbitrary independent complete stopping laws, Never, and ties.
   Equation (19)'s actual and raw reward-table consumers are in
   `UniformEquilibrium/Quitting/Paths/TwoPairCrossMassRewardExclusion.lean`.
   The displayed numerical fixture and long-word regression remain to be
   supplied.

The checked equation (19) consumer strengthens the packet's coefficient
assumptions: the favorable coefficients can have either sign, and the two
loss coefficients need only be nonnegative, not strictly positive. The
product bound and designated-owner singleton signs are retained. This does
not extend coverage to reward tables without the displayed row inequalities.

## Cap-threshold blocks and weak exclusion

The real arbitrary-source cap-threshold block is
`exists_literal_capThreshold_block_debtSum_le_quadraticDrop` in
`UniformEquilibrium/Quitting/Paths/FiniteSoloCapThresholdDescent.lean`, with
the first-hit, affine, and debt identities in
`UniformEquilibrium/Quitting/Root/TerminalSemanticSoloCapThreshold.lean`.
The executable rational block is
`executableRationalCapThresholdBlock_length_and_debtSum_le` in
`UniformEquilibrium/Quitting/Paths/ExecutableRationalCapThresholdBlock.lean`;
it has the claimed `3C^2/(128M+24C)` decrease and uses the canonical rational
root-grid and first-hit scan.

The positive-minimum cap and payoff margins are
`positive_minimum_preemptedOwner_quadraticMargins` and its prescribed,
nonnegative-owner, and four-player corollaries in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.
The generic payoff-envelope square-root consequence and its minimum wrappers
are in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPayoffEnvelope.lean`.

The fixed-table real and rational all-preempted renewal constructions are in
`UniformEquilibrium/Quitting/Paths/FiniteWordSelectedOwnerStep.lean`,
`UniformEquilibrium/Quitting/Paths/FiniteWordSelectedOwnerRates.lean`,
`UniformEquilibrium/Quitting/Paths/ExecutableRationalSelectedOwnerStep.lean`,
and `UniformEquilibrium/Quitting/Paths/ExecutableRationalSelectedOwnerRates.lean`.
The rational definitions select a
maximum blocker for each owner and the minimum of those ownerwise maximum
gaps. The signed-owner finite unpreempted exit is in
`UniformEquilibrium/Quitting/Paths/FiniteUnpreemptedSoloExit.lean`; the full
real weak-subset composition is in
`UniformEquilibrium/Quitting/Paths/FiniteWordWeakSubsetSelection.lean`.

The following literal cap-threshold obligations remain:

1. There is no full executable rational weak selector including the
   unpreempted branch. Consequently the packet's statement for every rational
   weak-exclusion table is stronger than the current rational consumer.
2. The table-uniform weak accuracy-threshold construction remains absent; the
   current fixed-preemption-gap rate is intentionally a different bound.
3. The three semantic regression fixtures with first hits at 59 and 30 and
   the below-singleton skip are absent. No canonical source occurrence of the
   displayed `95/96` or `157/160` recurrences was found.
4. The exact definition
   `rho_pay = max(0, sup_actual min_i(U_i-s_i))` and a direct theorem applying
   the generic payoff-envelope result to that definition are absent. The
   generic square-root implication is present, so this is a narrow adapter,
   not a missing analytic argument.

## Stale status statements

Statements in the final packets saying that these are only ordinary
mathematical proofs, that Lean implementation can begin, or that no generic
real quantifier-elimination implementation is present are stale. The actual
RCF quantifier-elimination endpoint, rational raw decisions, reciprocal
searches, exact and rational finite strict/group selectors, real and rational
cap-threshold blocks, quadratic minimum margins, and fixed-table weak
selectors are canonical. Old Research-path references to cap accounting are
also superseded by production declarations.

The packets' stated nonclaims about arbitrary canonical four-player quitting
games and strategy-class completeness remain valid and are not counted as
missing promised results.
