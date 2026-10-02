# Implicit-theory mining: second bounded round

Author: CODEX_LARCH. Research and static source audit, 2026-09-07.

## Current result and scope

Two coherent theory candidates survive: **finite-feature clock geometry**
and **controlled observable compression**. Both have ordinary mathematical
proofs or detailed sketches and independent reviews linked below. They are
not Lean-checked here. Their value is structural explanation and unification;
an equilibrium existence advance is not required for retaining them.

The user clarified that other agents are pursuing UE solutions. A concrete
residual-account application is therefore isolated in the
[UE handoff](CODEX_LARCH__UE_RESIDUAL_TRANSPORT_HANDOFF.md). We do not continue
its source-production work as part of theory mining.

No Lean source, export, shared index, or commit was created by this round.
Concurrent worktree changes belong to other work and were preserved.

## 1. Finite-feature clock geometry

### Mathematical object

A random time takes values in ℕ∪{∞}. Observe it using finitely many marked
before/tie/after reward shapes, allowing every finite test date. The induced
distance on clock laws is exactly a maximum of cumulative-mass and atom
functionals, with an optional Never-mass term. This is an intrinsic
observation geometry, rather than a generic TV upper estimate.

The quitting specialization follows because deterministic opponent clocks
produce exactly these marked tests and randomized independent opponents
average them. The test shapes are finite; the time menu is not.

### Results developed

- An exact coefficient formula for the seminorm and its null directions.
- Exact distance to proper laws: Never mass times an explicit coefficient
  constant κ. Proper laws are closed when κ>0 and dense when κ=0.
- A complete topology and total-boundedness classification. Any nonzero
  cumulative coefficient gives the TV topology and a complete law space;
  uniform late finite mass controls precompactness. With only atom tests,
  uniform late atom size replaces mass tightness.
- If atoms and Never mass are both observed but cumulative mass is not,
  the law space is incomplete. Its completion has coordinates (x,l) with
  x≥0 and Σx≤l≤1. The defect l−Σx records diffuse finite mass separately
  from Never mass 1−l. This is an exact boundary, not an analogy.
- Adding payoff observers takes a finite union of test families. One added
  cumulative observer can change the geometry from the diffuse-defect case
  to the complete TV-topology case.

The classification explains why finite-total-mass tails, late atoms,
Never mass, and actual-law realization play different roles in nearby
approximation statements. TV topology does not imply a global inverse norm
bound; the notes explicitly distinguish topology, uniformity, and completion.

Sources include `QuittingStrategicallyWithin`
(`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdog.lean`),
`IsQuittingProperStrategicallyApproximable`
(`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`),
and the generic stopping-law tail and proper-approximation modules.

The prior Ramsey notebook already has a sufficient diffuse-Never example.
The candidate adds necessity, the exact distance, and the classification;
it does not claim to have discovered that positive example. The two watchdog
files are one development episode, not independent historical evidence.

Detailed records:

- [Seminorm and proper-law closure](CODEX_LARCH_ROUND2_DUAL__STRATEGIC_CLOCK_SEMINORM.md),
  [independent review](../feedback/CODEX_LARCH_ROUND2_DUAL__STRATEGIC_CLOCK_SEMINORM__BY_CODEX_LARCH_JOINT.md).
- [Completion and compactness](CODEX_LARCH_ROUND2_DUAL__STRATEGIC_CLOCK_COMPLETION.md),
  [independent review](../feedback/CODEX_LARCH_ROUND2_DUAL__STRATEGIC_CLOCK_COMPLETION__BY_CODEX_LARCH.md).

**Assessment:** the strongest result of this round. A coherent exact
classification is absent from the sampled source interfaces and prior notes.
No claim of external novelty or a complete corpus audit is made.

## 2. Controlled observable compression

### Mathematical object

Instead of retaining the entire state distribution, retain its values on a
linear space W of observables. Generate W by closing desired outputs under
the relevant transition operators. This gives a canonical quotient of
distributions, which need not be a quotient of physical states.

This organizes code patterns currently separated among full-state
invisibility, residual transport, deterministic quotient lifting, and
failure of witness lists to survive continuation. The underlying mathematics
is largely established linear observability, ordered vector spaces, and
lumpability; the proposed contribution is their useful common organization.

### Results developed

- A finite minimal invariant-space construction. If every intervention row
  agrees with the baseline on W, expected retained observables agree under
  arbitrary history-dependent controls. Polynomial or finite-phase families
  admit finite coefficient checks for every time-varying calendar.
- The positive states of W form K=conv{state evaluations}. Positive unital
  dynamics always have a finite stochastic vertex cover. An affine positive
  encoding of K into distributions on its vertices exists exactly when K
  is a simplex. Such a cover preserves means, not automatically observation
  histories, controller information, or independent action factorization.
- W itself represents a deterministic state quotient exactly when it is a
  unital pointwise algebra, equivalently a vector lattice. A simplex K is
  insufficient: some physical state evaluations can be interior points.
- Conditioning by a retained nonnegative likelihood g descends exactly when
  multiplication by g preserves W. Closure under all retained likelihoods
  forces the algebra condition. Preserving means or even having a simplex
  positive state image does not suffice for conditioning.
- Closure under all state-dependent Markov controls has a sharp local test:
  every state where an action changes a retained prediction must have its
  singleton indicator in W. This yields a finite closure algorithm using
  single-row switches, without enumerating all feedback policies.
- Even a partition algebra invariant under all Markov feedback matrices
  need not preserve the same full-history policy. An exact four-state
  example uses remembered information discarded by the quotient.

These are one connected theory candidate, not several independently counted
discoveries. The distinctions identify exactly which additional closure
property a proposed compression needs for its intended operation.

Named code instances include
`finiteAveragePayoff_scheduledPlayerOwned_le_of_invisible`
(`UniformEquilibrium/VanishingDiscount/Analytic/PlayerOwned/InvisiblePlayerOwnedDeviationBoundary.lean`),
`PlayerOwnedCalendarResidualAccount`
(`UniformEquilibrium/VanishingDiscount/Analytic/PlayerOwned/CommonPotentialPayoffBoundary.lean`),
`IsStronglyLumpable` and `QuotientGluingInterface`
(`MathUE/Probability/QuotientShadowLift.lean`), and
`exists_terminalSemantic_commonWitness_noncompositionality`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCommonWitnessNoncompositionality.lean`).

Detailed records:

- [Linear observable closure](CODEX_LARCH_ROUND2_OBSERVATION__FINITE_OBSERVABLE_CLOSURE_FOR_RESIDUAL_TRANSPORT.md),
  [independent review](../feedback/CODEX_LARCH_ROUND2_OBSERVATION__FINITE_OBSERVABLE_CLOSURE_FOR_RESIDUAL_TRANSPORT__BY_CODEX_LARCH.md).
- [Positive realizations and observable algebras](CODEX_LARCH_ROUND2_OBSERVATION__POSITIVE_REALIZATIONS_AND_OBSERVABLE_ALGEBRAS.md),
  [independent review](../feedback/CODEX_LARCH_ROUND2_OBSERVATION__POSITIVE_REALIZATIONS_AND_OBSERVABLE_ALGEBRAS__BY_CODEX_LARCH_JOINT.md).
- [Feedback closure and the memory obstruction](CODEX_LARCH__OBSERVABLE_FEEDBACK_CLOSURE_AND_MEMORY.md),
  [independent review](../feedback/CODEX_LARCH__OBSERVABLE_FEEDBACK_CLOSURE_AND_MEMORY__BY_CODEX_LARCH_OBSERVATION.md).

**Assessment:** a strong consolidation candidate, with exact distinctions
and counterexamples. Its generic utility is more established than any new
UE application. Finite dimension alone does not guarantee useful compression:
closure may fill the entire state-function space.

## 3. Rejected or already-covered candidates

The [summable seam checkpoint](CODEX_LARCH_ROUND2_REPAIR__SUMMABLE_SEAM_MINING_CHECKPOINT.md)
found that signed affine recurrence, infinite boundary series, and one-sided
defect accounting already exist. An exact zero-hazard example retains an
order-one outsider seam. No new summability theory or positive bridge was
identified. Pursuing its remaining producer conditions would be UE-solving.

The [common-witness/projection screen](CODEX_LARCH_ROUND3_JOINT__WITNESS_INTERCHANGE_MINING_CHECKPOINT.md)
likewise found substantial
existing abstractions: continuation lattice gluing, compact proof-relevant
adapters, finite signed compatibility, and inverse-limit constructions.
Rephrasing these as a universal common-realization problem does not establish
a missing theory. Its separate checkpoint records the exact inspected
interfaces and rejected existential interchanges.

## 4. What worked in the search

The [first pilot](CODEX_LARCH__CROSS_EPISODE_PATTERN_MINING.md) ranked repeated
proof shapes and found only already-connected helpers. This round used
bounded statement, hypothesis, and boundary-case comparisons instead.

The productive signals were:

1. A universal observation predicate with only a coarse sufficient metric:
   derive its intrinsic tests and classify the resulting topology.
2. Repeated requirements that a statistic survive an operation: identify
   the smallest test space closed under that operation, then distinguish
   linear, positive, event, and controller-information closure.

Imports, prior mining notes, exports/formalized records, and actual source
statements served as rejection checks. Dates helped avoid local duplication
but were not treated as mathematical evidence. Bulk migration dates and
nearby additions were explicitly discounted. No new whole-codebase semantic
index was built; the surviving results came from a small number of source
neighborhoods and independent mathematical development.

The next theory-mining pass should look for other places where the code uses
a coarse sufficient topology or repeatedly repairs closure under a specific
operation. It should not use remaining UE proof obligations as its primary
ranking criterion. The two current candidates are substantial enough for
review and consolidation before expanding their scope further.
