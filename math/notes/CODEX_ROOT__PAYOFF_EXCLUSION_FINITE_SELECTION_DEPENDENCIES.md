# Payoff-exclusion finite selectors: formalization dependencies

Author: CODEX_ROOT. The two packets below were read in full on 2026-09-07.
This is a dependency plan, not a Lean seal for their new constructions.
The existing cap-clock and ordered-premium proof assignments continue first.

## Frozen inputs

- `FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION.md`:
  SHA-256 `3b579e7796de1c8302c0c77766c2da0c6e0e00c3cfdf32745c45549c3f7321ec`.
- `PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS.md`:
  SHA-256 `a7a4562e3362483be31b541b4328e41f2c352edcab8947c4e2ae28ead9a3f0aa`.

## Shared first layer

Both packets need the same approximate auxiliary-prefix debt budget and
below-singleton absorption estimate. The exact coordinate budget is already
`quittingTerminalSemanticDebt_prefix_le_auxiliaryNash`
(`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`). Its checked
statement assumes exact root Nash and permits a coordinatewise nonnegative
shift. Extend the same calculation with literal root-regret terms, then sum
for a common scalar shift. Do not count an arbitrary-root ledger as a root
selector. Exact finite-game existence and rational finite-grid selection are
separate constructors.

The cap-Continue accounting lemma
`quittingTerminalSemanticDebt_prefix_eq_of_capContinue`
(`Research/Quitting/TerminalSemanticWeightedDebtAxisInsertion.lean`) is
reusable but still in Research. It must be promoted with narrow imports
before a production theorem imports it; the surrounding tentative weighted
axis development need not move with it. Its cap-branch premise must be
proved at each first-threshold step, not silently retained past the hit.

## Parallel branches after the shared layer

1. Cap-threshold packet: literal solo-prefix recurrence up to the first cap
   crossing, finite crossing bound from a preemptor, final auxiliary root,
   then total-debt bound using the maximum of old debt and owner cap margin.
   The old debt alone is insufficient. The finite word must be constructed
   against the entire old source; cap attainment is not an input.
2. Positive-minimum consequence: vary the solo hazard, select a fixed
   crossing label and carrier limit, then apply the auxiliary row to obtain
   the explicit quadratic margin. Existing qualitative singleton margins
   do not supply its constant.
3. Payoff-exclusion packet: strict-deficit and nonconcentrated-weight
   finite recursion, retaining geometric or reciprocal rates respectively.
   Weak-subset exclusion uses its own charged-step/solo-block/stationary-exit
   algorithm. It does not depend on the first packet's quadratic collar.
4. Independent-clock entrances: retain the two crossed masses in the
   determinant inequality, and the Never mass in the two-pair square-root
   entrance. Then attach the literal reward-table inequalities to the
   relevant exclusion predicate. A correlated reward-hull separator is not
   an interchangeable premise.
5. Exact suffix limit: use the strict-deficit sequence's positive absorption
   floor and a diagonal limit of reversed finite words. Preserve the actual
   suffix index and prove finite-response inequalities before controlling
   Never by the late-clock limit. Joint absorption does not imply
   opponent-deleted absorption. This exact-result branch requires all
   singleton rewards nonnegative; the finite selectors have weaker signs.
6. Rational implementation and regression fixtures: finite rational root
   grid, exact complete finite-word cap evaluation, termination and date
   bounds. A noncomputable existential real-root selector is not the
   rational algorithm. Its arithmetic complexity is not claimed.

## Existing conclusions and nonclaims

`minimumTerminalSemantic_singletonMargin`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`)
gives the qualitative minimum cap margin. The stronger strict-minimum
payoff theorem is
`exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`).
Neither declaration constructs the new finite words or their date bounds.

The final fixed-target consumer is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
The packets must supply its actual unrestricted approximate equilibria.
They do not prove weak exclusion on arbitrary Fin4 tables, preserve debt
decrease when every owner cap margin exceeds total debt, or settle the
general conjecture. No packet is archived on the strength of this plan.

## Implementation checkpoint

The coordinate defect ledger, its exact-root corollary, the common-shift
total ledger, and the exact/approximate below-singleton absorption floors
are full-build checked and pushed in `68a8ccc`. The modules are
`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`,
`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDefectBudget.lean`, and
`UniformEquilibrium/Quitting/Root/BelowSingletonRootAbsorption.lean`.
The full Lean check was silent and the repository checks passed.

The strict-deficit selector must store literal finite words and their actual
profiles. The existing actual exact-prefix ray chooses roots against the
actual prescribed payoff; it is not the auxiliary-continuation recursion.
The exclusion hypothesis is only on finite words, not arbitrary carrier
points. The actual word recursion and its exact/approximate one-step
contraction are full-build checked and pushed in `94d58d2`, in
`UniformEquilibrium/Quitting/Paths/StrictDeficitFiniteWords.lean` and
`UniformEquilibrium/Quitting/Terminal/PayoffExclusionStrictDeficitStep.lean`.
The generic geometric bounds are in `MathUE/GeometricMinimumRecurrence.lean`.
Their exact global-rate instantiation, actual finite-word full behavioral
approximate Nash selector, and fixed-uniform-payoff consequence are
full-build checked and pushed in `bb454f6`, in
`UniformEquilibrium/Quitting/Paths/StrictDeficitFiniteWordRates.lean`.
Singleton signs are unrestricted for these finite results. Rational
selection and the exact infinite all-suffix limit remain separate work.

The same checkpoint proves the literal first-threshold solo block in
`UniformEquilibrium/Quitting/Root/TerminalSemanticSoloCapThreshold.lean`.
Its output retains the distinct crossing player, first-hit interval,
logarithmic step bound, affine payoff/cap formulas through the hit, and
total-debt bound by the larger of source debt and owner cap margin.
The final auxiliary-row assembly is full-build checked and pushed in
`bb454f6`, in
`UniformEquilibrium/Quitting/Paths/FiniteSoloCapThresholdDescent.lean`.
Its final actual-source theorem constructs the word and stated length/debt
bounds without a supplied word, crossing, or root. The auxiliary-row bound
also permits debts below half the selected upper bound; that unused
restriction was removed during review. Positive-minimum quadratic cap and
prescribed-payoff margins, including the nonnegative-owner and signed Fin4
consequences, are full-build checked and pushed in `19d1f5f`, in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.
The proof reuses the existing qualitative margin and takes a carrier limit;
it does not claim that limit is an actual full-pair profile. The packet's
payoff-envelope square-root bound is full-build checked in `17f06d5`, in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPayoffEnvelope.lean`.
It accepts an upper bound witnessed by some owner at every actual profile;
it does not require a separately supplied supremum functional.
The general nonpreempted-owner fixed-payoff theorem
is in `UniformEquilibrium/Quitting/Classification/Existence/SoloPreemptionUniformPayoff.lean`.

## Additional independent packet

`ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_FINITE_SELECTOR.md` was read in full.
Frozen SHA-256:
`79801826f5e86be6f15ce055ed2b20fb9a78be2f00a95e2f300236135ab219d6`.
It is independent of the exclusion selectors: rectangular simultaneous
root selection produces one actual cycle on an entire even-sized paired
player set, followed by unrestricted all-suffix terminal Nash and exact
cap-preserving finite truncations. The Fin4 single-pivot consumer follows
only after transforming the infinite profile, whose unilateral deviations
absorb almost surely. Finite truncations have positive Never mass and do
not admit an unqualified terminal-payoff translation identity.
The existing special-table paired cycle is not this reward-region producer.
Its scalar pair/face estimates and polynomial simultaneous-hazard selection
are full-build checked and pushed in `6bb9aa4`, in
`MathUE/PairedAffineIntervalEstimates.lean` and
`MathUE/PairedAffineClearedField.lean`. These game-independent helpers do
not yet construct the actual cyclic game profile or its truncation caps.
The literal two-active-player root and its exact payoff, active-response,
joining-response, and quiet-incentive identities are full-build checked in
`19d1f5f`, in `UniformEquilibrium/Quitting/Root/PairedProductRoot.lean`.
The actual cyclic-value identification and raw-reward exact all-suffix
producer are full-build checked and pushed in `dfe13e4`, in
`UniformEquilibrium/Quitting/Cycles/PairedCycleValues.lean` and
`UniformEquilibrium/Quitting/Cycles/PairedCycleEquilibrium.lean`.
The latter selects one hazard vector, proves full behavioral terminal Nash
at every literal suffix, and proves a uniform payoff at each actual initial
phase value. Exact finite-truncation payoffs, full caps, debts, early pure-date
attainers, geometric errors, finite-menu realization, censoring and calendar
atoms are full-build checked and pushed in `17f06d5`. The source theorem
in `UniformEquilibrium/Quitting/Cycles/PairedCycleFiniteSource.lean` selects
one hazard vector before all truncation counts and positive accuracies.
The combined paired-menu/pivot adapter and quantitative finite-average
bounds are full-build checked through `40b3eba`. The raw Fin4 producer
chooses one hazard vector and one menu family before all accuracies.
Its literal nonpivot laws feed an attained pivot-repair minimum and the
existing small-repair source. The original infinite cyclic profile has
the stated reciprocal-horizon delivery/deviation bounds and a summable
uniform absorption clock. The transformed infinite profile is exact Nash
at every suffix under arbitrary positive playerwise affine changes,
without a nonnegative transformed-singleton assumption.
Class separation, strict open-region witnesses, the literal transformed
Fin4 infinite profile, the canonical 56-coordinate chart, the strict
transformed-singleton bound, and the absolute deviation boundary bound
are integrated in pushed commit `7d59db0`. Full build 43048 was silent;
complete repository gate 2461 passed. Independent Astra review passed.
The byte-identical source is archived under
`math/formalized/ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_FINITE_SELECTOR.md`, with
clause coverage in `math/formalized/ASYMMETRIC_PAIRED_CYCLE_LEAN_COVERAGE.md`.
The subsequent mining pass proved the weaker initial-value hypothesis
for affine truncation caps, integrated in pushed commit `e192288` after
silent full build 87897 and complete repository gate 34229.
These commits were pushed through `6406c12` after the remote CI repair
run at `3fdb5c2` passed. The new head's remote run is separate from the
completed local validation.
See the detailed static reuse audit in
`math/notes/CODEX_SEGMENT__PAIRED_CYCLE_REUSE_AUDIT.md`.

Commit `6bb9aa4` checks the nonconcentrated-weight exact auxiliary absorption
floor and debt decrease, together with the literal finite-word recursion,
in `UniformEquilibrium/Quitting/Terminal/GroupExclusionExactPrefixStep.lean`
and `UniformEquilibrium/Quitting/Paths/GroupExclusionFiniteWords.lean`.
One concentration constant is fixed before the word quantifier; weights
may depend on the actual word. The global reciprocal rate, literal
finite-word full behavioral approximate Nash selector, and fixed-payoff
consumer are full-build checked and pushed in `57c5ef9`, in
`UniformEquilibrium/Quitting/Paths/GroupExclusionFiniteWordRates.lean`.
These exact-root results impose no singleton signs. Rational root-grid
selection remains separate work.

The same commit proves weak-exclusion renewal into actual finite words
of arbitrarily small total debt when every owner is strictly preempted,
in `UniformEquilibrium/Quitting/Paths/FiniteWordWeakExclusionDescent.lean`.
Its direct fixed-uniform-payoff consumer is full-build checked in `dfe13e4`:
`exists_uniformEquilibriumPayoff_of_finiteWordWeakExclusion_allPreempted`.
The common preemption gap is selected internally from the pointwise
witnesses. Unlike the packet's nonnegative-singleton headline, this
all-preempted branch is sign-free. Quantitative phase/date bounds and the
finite unpreempted-owner branch are full-build checked in `17f06d5`, in
`UniformEquilibrium/Quitting/Paths/FiniteWordWeakExclusionRates.lean` and
`UniformEquilibrium/Quitting/Paths/FiniteUnpreemptedSoloExit.lean`.
The qualitative descent theorem now uses the same selected words as the
quantitative bounds; its duplicate local recursion was removed.
`UniformEquilibrium/Quitting/Paths/FiniteWordWeakExclusionSelection.lean`
joins the alternatives into the nonnegative-singleton finite selector and
fixed uniform-payoff result. Rational algorithms and boundary fixtures
remain work; no full-packet seal follows from the real-table selector.

Bounded source checks for that packet:
`Math.Topology.exists_rectangular_zero_of_strict_face_signs`
(`MathUE/Topology/RectangularPoincareMiranda.lean`) returns an interior
simultaneous zero but requires a globally continuous field. The cleared
field should therefore be defined by its polynomial expression, not by
totalized division followed by multiplication and an unjustified global
continuity assertion. Equality to the rational field is needed only inside
the hazard rectangle.
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
(`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`) already consume
exact policy recursion, exact phase Nash, and playerwise opponent-cycle
contraction. Their root cycles are generic in both finite dimensions; the
new work is producing the certificate from the paired reward region and
proving the literal finite truncation cap identities. The named single-pivot
full-exploitability identity consumes an actual finite-deadline timing law,
so that law realization must also be retained in the final adapter.
