# Evaluation of Terra proof-mining prototypes

**Date:** 2026-08-06

**Repository point:** `42459d79`

## Outcome

Three independent experimental Lean developments were produced and then
strengthened after first-pass review. All compile directly, contain no
`sorry`, `admit`, unsafe declarations, or new axioms, and leave production
source untouched at the point of evaluation.

After review, the finished cyclic-exposure result was promoted to
[`MathUE/CyclicExposure.lean`](../../MathUE/CyclicExposure.lean). The existing
three-player lower-bound and optimizer-classification proofs now consume that
module; the hazard and phase-occupation files remain experimental.

The axiom audits printed by the files report only the repository-standard
classical axioms:

```text
propext, Classical.choice, Quot.sound
```

The experiments are locally excluded by `.git/info/exclude`, so their absence
from `git status` is not evidence that the files were not created.

## Evaluation criteria

Each prototype was checked for:

1. direct compilation with `lake env lean`;
2. absence of placeholders and nonstandard axioms;
3. a nonvacuous theorem rather than definitions alone;
4. usefulness outside the proof in which the idea was discovered;
5. a clear, bounded route to production promotion.

## 1. Discrete hazard stopping laws

**Artifact:** [`MathUE/Probability/DiscreteHazardStopping.lean`](../../MathUE/Probability/DiscreteHazardStopping.lean)

**Verdict:** promotion candidate after dependency inversion. Grade: **A-**.

The file exposes two APIs.

The Boolean API wraps the stopping-law construction currently implemented in
`QuittingBehaviorStoppingLaw`. It provides survival, finite stop atoms, the
never atom, the normalized `PMF (Option Nat)`, convergence, and the bounded
expectation expansion.

The scalar API is the more important result. A `ScalarHazard` carries a
sequence `stop : Nat -> Real` with pointwise probability bounds. Its public
statements use only scalar quantities:

```text
survival h n = product_{t<n} (1 - h.stop t)
stopMass h t = survival h t * h.stop t
sum_{t<n} stopMass h t = 1 - survival h n
HasSum (stopMass h) (1 - neverMass h)
```

It also proves exact `none` and `some t` atom formulas, the expectation
expansion, scalar survival monotonicity and recursion, and deterministic
marked stopping-law atom/expectation formulas.

### What is genuinely reusable

- Client theorems no longer mention quitting games.
- The finite-product and atom interfaces are suitable for one-live-state
  absorbing models, optimal stopping, and marked terminal events.
- The marked law preserves the stopping date in the mark, so the map is
  injective on finite atoms and the atom formula is exact.

### Limitation before promotion

The experiment still imports `QuittingBehaviorStoppingLaw` and delegates the
countable normalization/PMF construction through it. Production promotion
should invert this dependency:

1. move the underlying construction and proofs to
   `Math/Probability/DiscreteHazardStopping.lean`;
2. make the quitting file an adapter importing that module;
3. retain compatibility aliases temporarily if downstream churn is large.

`PMF.bernoulli` and `PMF.bernoulli_apply` produce deprecation warnings. The
advertised replacement is a measure-valued API rather than a `PMF`, so this is
an upstream API mismatch, not a failed proof. A production version should
either construct the two-point PMF directly or isolate the deprecated use in
one adapter.

## 2. Phase occupation and bias duality

**Artifact:** [`MathUE/Probability/PhaseOccupationDuality.lean`](../../MathUE/Probability/PhaseOccupationDuality.lean)

**Verdict:** strong specification and weak-duality layer; not yet the proposed
strong-duality theorem. Grade: **B+**.

The file defines:

- a cyclic phase type `ZMod P`;
- real phase-state-action occupations;
- normalized nonnegative occupation feasibility;
- phase-shifted flow in all-test-functions form;
- the ordinary pointwise incoming/outgoing flow equations;
- phase-average reward and phase-indexed bias feasibility.

The important landed experimental theorems are:

```text
hasPointwisePhaseShiftFlow_of_hasPhaseShiftFlow
hasPhaseShiftFlow_of_hasPointwisePhaseShiftFlow
hasPointwisePhaseShiftFlow_iff_hasPhaseShiftFlow
phaseAverageReward_le_bias
phaseAverageReward_le_phaseSlack
```

The equivalence is the key matrix-compiler bridge. One direction tests flow
against phase-state indicators. The other expands finite PMF expectations,
uses the pointwise equations, and reindexes the cyclic phase sum. The weak
duality theorem then pairs occupation flow with a pointwise bias inequality,
so every feasible occupation has average reward at most every feasible slack
`g`.

`OneStateExample.feasible` supplies a concrete nonvacuity witness.

### What is genuinely reusable

- The semantic occupation object is independent of policies and marginal-law
  paths.
- `HasPhaseBias` is definitionally equivalent to the existing
  `Math.Probability.HasPhaseSlack` vocabulary.
- Pointwise flow is now available in precisely the finite linear form needed
  for an LP matrix.

### Missing big theorem

The experiment does **not** prove strong duality or construct a bias from an
occupation upper bound. Importing `StrongDuality` alone is not enough. The
remaining compiler must:

1. index variables by phase-state-action triples;
2. encode each flow equality as two weak inequalities;
3. encode normalization and nonnegativity;
4. represent free bias variables by positive/negative parts;
5. identify the LP dual constraints with `HasPhaseSlack`;
6. establish attainment/nonemptiness for the relevant primal problem.

This is now a sharply delimited mechanical theorem rather than an ambiguous
stochastic problem. The weak-duality and flow-equivalence layer is suitable
for promotion even if strong duality is developed separately.

## 3. Sharp cyclic exposure theorem

**Artifact:** [`UniformEquilibrium/Quitting/Punishment/SharedPunishment.lean`](../../UniformEquilibrium/Quitting/Punishment/SharedPunishment.lean)

**Verdict:** promoted algebraic core; game-semantic lift remains. Grade:
**A**.

For finite nonempty `ι`, `CyclicNeighbours` provides inverse successor and
predecessor maps and defines

```text
exposure x i = x (next i) * (1 - x (prev i)).
```

The main results are:

```text
exists_exposure_le_quarter
exposure_fair
eq_fair_of_forall_quarter_le_exposure
forall_quarter_le_exposure_iff_eq_fair
```

Thus some exposure is always at most `1/4`, the fair row attains `1/4` at
every coordinate, and the fair row is the unique maximizer of the minimum
exposure.

The proof is stronger and cleaner than the initially suggested product proof.
A maximum coordinate gives the `1/4` upper bound. For rigidity, the lower
bounds force `x i <= x (next (next i))`; summing increments over the finite
permutation makes every inequality an equality, reducing each coordinate to
the sharp scalar inequality `x(1-x) <= 1/4`.

No single-orbit, minimum orbit length, or exclusion of fixed/two-cycles is
needed for this algebraic theorem. The existing three-player exposure lemma is
recovered as a specialization.

### What is genuinely reusable

- The result is independent of PMFs and quitting payoffs.
- It gives both the sharp value and optimizer classification.
- The hypotheses are minimal enough to apply componentwise to any finite
  permutation system.

### Missing game-semantic theorem

The file does not claim arbitrary-cycle shared-punishment excess `3/4`. That
lift still needs:

1. a generic cyclic quitting reward table;
2. finite-coordinate product-PMF projection/evaluation lemmas;
3. individual punishment floors equal to `-1`;
4. the first-row bound for arbitrary behavior plans;
5. the nonpositive-tail argument showing fair-first-row optimality;
6. translation of exposure rigidity into optimizer classification.

The algebraic theorem removes the only difficult optimizer inequality from
that list. The remaining work is mostly semantic and API assembly.

## Verification record

The following commands all exited with status zero:

```powershell
lake env lean Experiments/DiscreteHazardStopping.lean
lake env lean Experiments/PhaseOccupationDuality.lean
lake env lean Experiments/QuittingSharedPunishmentCycle.lean
```

The first command emits only the two documented Bernoulli deprecation
warnings. Each file ends with `#print axioms` commands for its principal
theorems.

## Promotion order

1. **Cyclic exposure core.** Small, self-contained, sharp, and immediately
   useful. Decide whether its permanent home is a general finite inequality
   module or beside shared-punishment infrastructure.
2. **Discrete hazard stopping.** High leverage, but move the implementation
   before changing imports so `Math` does not depend on `GameTheory`.
3. **Phase occupation weak duality.** Promote the semantic objects and flow
   equivalence, then implement the strong-duality matrix compiler as a second
   change with explicit acceptance tests.

None of these experiments alone closes the quitting producer. Together they
validate three claims from the source note: the hazard layer is extractable,
the arbitrary-cycle `1/4` optimizer theorem is near, and the phase-occupation
converse has a concrete finite LP boundary rather than a missing stochastic
idea.
