# Reviewed theory candidates and the outside-field retry

Author: CODEX_LARCH. Research selection after bounded investigations, 2026-09-07.

## Main judgment

There is still useful mathematics to import from outside game theory. The
best candidates in this pass concern preserving information under strategic
interventions and making simultaneous response constraints compatible. Their
value comes from concrete reductions with explicit failure cases, rather
than another broad compactness, transport, or control analogy.

Three subagents developed sketches and cross-reviewed them; I developed two
additional candidates and reviewed the synthesis. The linked records separate
ordinary mathematical deductions, established source ingredients, and missing
game-specific production. None is Lean-checked here or exported. No result
settles UE, and no unrestricted finite-calendar normal form is claimed.

This follows the [initial bounded survey](CODEX_LARCH__MISSING_THEORY_SURVEY.md)
and incorporates a second visit to `math/ideas/` prompted by the user's
outside-field question. The sibling multitubes theory was not investigated.

## 1. Highest priority: quantitative support repair preserving full caps

**Outside fields:** robust constraint satisfaction, product-distribution
rounding, quantitative rigidity, and resilience under interventions.

The core observation is that an outcome simplification becomes strategically
safe when at least two players still quit surely: replacing one player's
whole law leaves an opponent who forces absorption. This allows one coupling
to control every unilateral response before taking the supremum.

The [quantitative geometry note](CODEX_LARCH_GEOMETRY__OBSERVATION_STABILITY_THEORY.md)
derives two concrete Fin4 estimates. With bounded rewards:

- singleton-plus-Never mass ε gives approximation of the entire payoff and
  full-cap vector by a two-sure-quitter root with error O(ε^(1/3));
- mass ℓ outside pairs gives approximation by one pure-pair root with error
  O(ℓ), including its full caps.

The orders are sharp for the stated law-approximation conclusions. A bit
distinguishing an immediate root from a root after a silent prefix is
necessary for cap preservation. Six raw unpadded pair checks nevertheless
suffice for a lower-bound screen because padding can only increase caps.

The [Boolean-constraint extension](CODEX_LARCH_GEOMETRY__BOOLEAN_CONSTRAINT_REPAIR_UNDER_INTERVENTIONS.md)
allows any prescribed family H of nonsingleton coalitions. Small mass outside
H forces approximation by one of finitely many product-root families supported
in H, again with full cap control. Their supports are compatible Boolean
intervals, so each model is a low-dimensional cube of optional quitters.
The interval classification was already present; quantitative intervention-safe
repair is the candidate addition. The final exponent and review provenance
are recorded in that note.

**Concrete strategic use.** If every model supported in H has exploitability
at least g>0, low-exploitability actual profiles must put a quantitative amount
of mass outside H. For the existing VANISH table, the minimum over all
two-sure roots is exactly 1/3: this gives a concrete lower bound on the
singleton-plus-Never mass of sufficiently accurate terminal Nash sources.
It localizes where such sources can live; it does not exclude their existence.

**Why this ranks first.** It strengthens law-only geometry into a statement
about unrestricted strategic behavior and applies to actual supplied laws.
It unifies several partial exact-face results without a large general theory.
It also beats the initial survey's unspecified semialgebraic power estimate
by elementary source-specific inequalities.

**Missing next step.** Find one incentive argument forcing small forbidden
mass on the same source, or one repair operation that tolerates the explicit
payoff/cap approximation error. A positive minimum alone supplies neither.
Do not spend another pass optimizing constants before obtaining that input.

Overlap matters: [FRECHET's independent pair-transfer note](CODEX_FRECHET_CYCLE__PAIR_CONCENTRATION_FULL_CAP_TRANSFER_AND_FORCING_GAP.md)
already obtains full-cap transfer from concentration near one pair and the
same six-pair screen. The additional content here is explicit leakage-to-pair
control, sharp singleton stability, and arbitrary forbidden-family repair.

## 2. Best consolidation: causal identification and hidden-cap completion

**Outside fields:** competing-risks survival analysis, inverse problems,
and partial identification.

The [causal sketch](CODEX_LARCH_DUAL__COMPETING_RISKS_CAP_FIBERS.md)
asks what one finite DATED terminal outcome law determines about deviations.
The answer is unexpectedly small: all full caps are determined except
possibly one player's.

Observed row masses divided by observed reach recover each independent
quitting hazard. Identification can end only at a sure-absorption row.
Two sure quitters shield every unilateral deviation from hidden tails.
With a unique sure quitter, only that player's deviation can expose them.
Its possible cap values have an explicitly characterized interval closure.

Existing stationary punishment supplies approximate minimizers of that one
cap while preserving the exact dated law, all prescribed payoffs, and all
other caps. Thus one gets a canonical cap-minimizing completion for any
supplied realizable finite dated law. The product-compatibility test is finite
polynomial algebra; its strategic minimization uses an existing producer.

**Why useful.** This could replace several separate finite-law, erasure,
sure-root, and punishment arguments by one identification theorem. It also
suggests searching over observable dated laws and completing their invisible
tails systematically. Finite observed absorption does not mean every
counterfactual stopping law has finite support.

**Boundary.** Undated coalition laws have less information. Moving compact
response graphs have much more complicated fibers. This finite exact
classification does not repair their known replacement or infinity-fiber
no-gos, nor produce useful dated laws from arbitrary game data.

## 3. Best speculative strategic import: quadratic hidden convexity

**Outside fields:** second-order optimization, quadratic alternatives, and
semidefinite rank constraints.

The [common-acceleration sketch](CODEX_LARCH_JOINT__MULTILATERAL_REPAIR_THEORY.md)
first states the actual compatibility problem: choose one feasible law
direction and one acceleration that improve every tied response. Its exact
finite dual requires favorable curvature against the entire family of
blocking response multipliers. One negative square is insufficient.

The [quadratic compatibility note](CODEX_LARCH__QUADRATIC_COMPATIBILITY_AND_RANK_ONE_OBSTRUCTION.md)
then gives a condition where the nonlinear search simplifies. Restrict to a
fixed product face containing the source in its relative interior and its
specified first-order-flat subspace. If the full balancing-multiplier polytope
is nonempty and has at most two extreme points, Dines's quadratic-range convexity yields an exact
alternative: one common improving direction, or one globally PSD weighted
curvature form. The classical quadratic input and its precise hypotheses are
[documented in the primary-source article](https://www.aimsciences.org/article/doi/10.3934/jimo.2020169).

If that flat subspace additionally splits into independent player blocks,
multiaffinity forces a PSD obstruction to vanish identically: failure of
repair becomes exact cancellation of mixed interactions. Those extra
hypotheses are explicit and are not inferred from the player count.

An exact three-form example shows the limit: every test improves under a
mixed covariance while no single direction improves them all. A feasible
semidefinite relaxation can therefore represent the wrong object. It cannot
be converted to an independent product-profile perturbation by averaging.

**Next test.** Compute the complete flat space and all balancing multipliers
for one existing actual source family. Two effective extremes, common
diagonalization, or another verified joint-range property would make the
outside theorem applicable. Without such structure this remains a diagnostic.

## 4. Lower-priority survivors

**Control and switching.** The
[control sketch](CODEX_LARCH_JOINT__OUTSIDE_FIELD_CONTROL_AND_REPAIR_BARRIERS.md)
shows that a supplied joint descent path can be followed by finitely many
one-player law changes with arbitrarily small exploitability overshoot.
Quadratic descent has a sharp inverse-square-root switching cost in an exact
example. This explains a distinction between exact monotone coordinate traps
and small-overrun repair. It produces neither the joint path nor a chronology
of reached histories. Fixed coordinate resets commute, so the proposed
nonholonomic Lie-bracket interpretation was rejected.

**Transient strategic selection.** The
[general-stochastic sketch](CODEX_LARCH__TRANSIENT_STRATEGIC_SELECTION_THEORY.md)
uses a common all-action expected-duration potential to construct a stationary
Nash selector among solved UE children. Action-dependent selection and
unbounded exit times are allowed; stopped accounting yields one fixed parent
UE target. This combines familiar fixed-point and stochastic-control methods
and plausibly completes a useful special-class interface. Its common duration
hypothesis fails for unrestricted all-Continue in a quitting game.

These are worth retaining as small coherent results if a current consumer
needs them. They should not displace the direct quitting questions simply
because their stronger assumptions make them easier to finish.

## 5. Ideas rejected or substantially demoted

- **Repair LP dual equals exclusion weight:** refuted, including every optimal
  dual selection, on the existing exact trap. The
  [dual note](CODEX_LARCH_DUAL__REPAIR_EXCLUSION_THEORY.md) isolates the missing
  response-premium term and the maximum-versus-total-debt mismatch.
- **Another first-order joint repair theory:** substantial overlap with
  NOETHER's existing complete-pivot envelope and joint trap escape. The
  second-order common-compatibility question survives that overlap.
- **Generic payoff-fiber correction:** a right inverse would help, but its
  uniform feasibility on the actual source is still the hard assumption.
  The causal finite-law completion is a narrower version with a real producer.
- **A larger universal response state:** existing continuation-state notes
  already expose failures of horizontal replacement and arbitrary compact
  infinity fibers. The causal sketch stays below that complexity boundary.
- **Classical occupation nonemptiness:** a possible small completion, but
  no missing strategic use was found in this pass.

## 6. What the outside-field retry changes

The early nonstrategic reductions have not made outside mathematics
irrelevant. They have changed the object it must preserve. An outcome law
alone omits precisely the counterfactual behavior that can determine a cap.
A scalar gain omits the other tied responses. A sequence of strategy updates
omits the requirement of being an actually reached gameplay chronology.

The most effective imports in this pass address one of those omissions
directly. The support-repair theorem preserves unilateral interventions.
The causal theorem identifies the remaining hidden intervention. Quadratic
hidden convexity tests whether several strategic inequalities can hold for
one actual perturbation. These are concrete organizing theories rather than
new names for the unresolved producer.

There is also a useful universality check: adding one sure date-zero quitter
embeds any finite binary normal-form game's complete response functions on
a face of a quitting game. Purely local multilinear claims must survive that
test. Special stopping chronology or source-minimum structure must therefore
enter any stronger game-specific deduction.

## 7. Cost-effective next investigation

1. Choose one actual reward-table family already used by repair/exclusion
   work. Enumerate only the forbidden-support models relevant to its known
   incentive inequalities, and test the required same-source mass bound.
2. For one existing finite-law candidate producer, determine whether it
   retains dated masses. If so, apply the causal canonical completion and
   measure the exact cap improvement without altering payoffs.
3. On one actual response-preserving perturbation family, compute the full
   dual curvature set before building any second-order machinery. Continue
   only if its structure is smaller than the generic obstruction.

The scale-saving method was to use frontier/toolkit routes and compressed
formalized/export packets to identify exact source declarations, then search
nearby notes for overlap and falsifiers. Agents were split by concrete
mathematical question and then cross-reviewed, rather than each scanning
the whole codebase. The old ideas catalogue was used to avoid repeating
already tested metaphors. This leaves a selective audit, not a claim that
every missing theory or recent file was examined.

## Verification and records

Each developed candidate links its independent review. Reviews checked
ordinary algebra, quantifiers, complete response coverage, and explicit
counterexamples. Corrections included a boundary tangent-space restriction,
the general pivot approximation constant, and reducing twelve pair-model
screening cases to six. Stronger support-repair bounds arose during review;
the author note records that provenance separately from independent checks.

No Lean source, export, commit, issue, or shared index was created by this
investigation. The notes and feedback are local conference records in the
gitignored `math/` lane. `python scripts/check_docs.py` passed. A separate
local Markdown-link check passed for all ten LARCH notes and eleven associated
feedback records present at handoff. Mathematical confidence here comes from
the sketches and their reviews, not from Lean compilation.
