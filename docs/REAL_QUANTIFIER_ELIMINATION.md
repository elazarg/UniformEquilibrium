# Real quantifier elimination

The library implements real quantifier elimination for rational polynomial
formulas, with arbitrary finite Boolean and quantifier nesting. The actual
recursive producer and the correctness theorems pass strict, silent Lean
checks. Projection of arbitrary-real-coefficient semialgebraic sets is also
proved. The game-specific predicate encodings remain separate adapters.

## Available components

- `MathUE/Polynomial/DensePolynomial.lean` implements coefficient-list
  arithmetic, differentiation, and terminating even-exponent pseudo-division.
  Its identity holds after any operation-preserving evaluation into a
  commutative ring. Remainders have smaller formal length than a nonempty
  divisor. At a divisor root, nonzero evaluated leading coefficient gives
  exact preservation of the dividend's sign in the remainder. Polynomial
  interpretation and degree lemmas connect the executable representation
  to Mathlib's polynomial analysis.
- `MathUE/RealQuantifierElimination/RingExpression.lean` supplies rational
  expression syntax, rational and real evaluation, variable renaming, and
  finite sums and products. `MathUE/RealQuantifierElimination/QuantifierFreeFormula.lean`
  supplies the shared sign-test syntax and its evaluation lemmas without
  importing the elimination algorithm.
  `MathUE/RealQuantifierElimination/CoefficientSignBranch.lean` proves that
  finite coefficient-sign trees compile to truth-equivalent Boolean formulas
  at every real environment. It does not generate a sign diagram.
  `MathUE/RealQuantifierElimination/CoefficientSignBranchInvariants.lean`
  supplies structural all-leaf predicates and a proof-aware bind, distinct
  from real-environment selection.
- `MathUE/RealQuantifierElimination/PolynomialEvaluation.lean` interprets
  expression coefficients in the dense polynomial kernel.
  `MathUE/RealQuantifierElimination/CoefficientTrimming.lean` branches on
  leading coefficients, preserving every real evaluation while removing
  specialized leading zeroes. Each selected nonempty result has polynomial
  degree equal to its formal length minus one.
- `MathUE/RealQuantifierElimination/UnivariateCompilation.lean` compiles
  variable zero to the polynomial indeterminate and the remaining variables
  to coefficient expressions. Evaluation agrees with the original expression
  at every bound value and real parameter environment.
- `MathUE/Polynomial/RealSignCell.lean` supplies interval root and sign
  lemmas. `MathUE/Polynomial/OrderedRealSignDiagram.lean` proves the ordered
  cell partition, exact diagram dimensions, removable-cut deletion, and
  bounded root-insertion transformations. These transformations consume
  previously established row signs and derivative conditions.
- `MathUE/Polynomial/InfinitySign.lean` derives signs at both infinities
  from polynomial coefficients, including zero and constant polynomials.
  It supplies root-free cell signs and bounded, half-line, and whole-line
  root criteria; the unbounded monotone cases require no supplied limits.
- `MathUE/Polynomial/LocalSignReconstruction.lean` implements sign-row
  reconstruction on each bounded interval, ray, or whole-line cell.
  Correctness includes all roots introduced into that cell. Its source-diagram
  consumer derives the nonzero derivative sign from reduced root coverage
  and the selected polynomial's positive degree.
- `MathUE/RealQuantifierElimination/PolynomialFamilyMeasure.lean` supplies
  the well-founded lexicographic measure on formal polynomial families.
  `MathUE/RealQuantifierElimination/PolynomialFamilyReplacement.lean`
  replaces a chosen maximal nonconstant polynomial by its derivative and
  aligned pseudo-remainders, preserving the other column positions and
  proving strict measure decrease.
  `MathUE/RealQuantifierElimination/PolynomialFamilyReduction.lean`
  proves strict decrease for shortening or removing lower-degree columns.
- `MathUE/RealQuantifierElimination/PolynomialFamilyPreprocessing.lean`
  trims and classifies each original column at every real environment.
  Removed zero columns are zero polynomials, constant columns have fixed
  nonzero signs, and retained columns have specialized positive degree.
  `MathUE/RealQuantifierElimination/PolynomialFamilyDiagramRestoration.lean`
  restores complete diagrams in original column order, preserving the same
  cuts and the exact nonzero-root predicate.
  `MathUE/RealQuantifierElimination/PolynomialFamilyPreprocessingBounds.lean`
  proves measure nonincrease for every syntactic leaf, including unreachable
  branches, and composes it with the strict recursive-step decrease.
- `MathUE/Polynomial/RemainderCutSignInference.lean` finds a vanishing
  divisor in a point row and returns its aligned remainder's sign. The
  actual pseudo-division identity proves the inferred sign equals the
  selected polynomial's sign; a failed scan identifies a removable cut.
- `MathUE/Polynomial/SignDiagramCondensation.lean` projects away auxiliary
  columns and deletes their cuts, preserving an exact reduced diagram for
  nonzero retained polynomials. Empty retained families are allowed.
  `MathUE/Polynomial/TaggedRowCondensation.lean` preserves the original
  order and payloads of retained point rows under the same deletion rule.
- `MathUE/Polynomial/GlobalSignReconstruction.lean` traverses all local
  insertions and removes derivative-only cuts.
  `MathUE/Polynomial/SignDiagramReconstruction.lean` supplies its point
  signs by executable pseudo-remainder inference and preserves them through
  auxiliary-cut removal. The resulting sign-list-only pipeline proves exact
  reduced realization for the selected polynomial and retained family.
- `MathUE/Logic/SignFormulaFiniteAtoms.lean` extracts atom occurrences in
  syntax order and evaluates their finite sign rows, preserving formula
  truth without assuming decidable equality on the atom type.
- `MathUE/RealQuantifierElimination/OneVariableDiagramConsumer.lean`
  turns a correctly realized diagram tree into a quantifier-free formula
  equivalent to one-variable existential quantification. This is a consumer
  of diagrams, not their producer.
- `MathUE/RealQuantifierElimination/PolynomialFamilyFocusSelection.lean`
  selects a maximal-length polynomial using only natural-number comparisons.
  `MathUE/RealQuantifierElimination/FocusedSignReconstruction.lean`
  reconstructs the literal replacement family in its original column order.
  Its derivative-leading coefficient condition is derived from the original
  trimmed nonconstant input.
- `MathUE/RealQuantifierElimination/PolynomialFormula.lean` defines
  arbitrary nested quantified formulas and their real semantics. Rational
  evaluation decides closed quantifier-free formulas with checked agreement
  to real truth.
- `signDiagram_correct`
  (`MathUE/RealQuantifierElimination/SignDiagramProducer.lean`) proves that
  the executable well-founded producer returns an exact reduced sign diagram
  at every real parameter environment. It derives the reconstruction inputs
  from preprocessing and restores the original family, including zero and
  constant columns.
- `eliminateQuantifiers_holdsAt_iff` and `decideClosedFormula_eq_true_iff`
  (`MathUE/RealQuantifierElimination/QuantifierElimination.lean`) prove
  correctness of the actual full eliminator and closed rational decision
  procedure. Neither theorem takes a producer or eliminator as a hypothesis.
- `IsSemialgebraic` (`MathUE/Semialgebraic/Basic.lean`) describes ordinary
  finite Boolean combinations of signs of real-coefficient multivariate
  polynomials, with Boolean closure and coordinate pullbacks.
  `exists_rationalReification`
  (`MathUE/RealQuantifierElimination/RealCoefficientReification.lean`)
  represents every such formula using rational syntax with finitely many
  fixed real parameters. `IsSemialgebraic.image_coordinate_projection`
  and `IsSemialgebraic.forall_coordinates`
  (`MathUE/Semialgebraic/Projection.lean`) prove closure under projection
  and universal quantification over any finite block. These consume the
  actual eliminator, not an assumed projection theorem.
- `IsSemialgebraic.preimage_polynomialMap` and
  `IsSemialgebraic.image_polynomialMap`
  (`MathUE/Semialgebraic/PolynomialMap.lean`) apply this interface to
  actual finite tuples of real multivariate polynomials. Substitution
  proves the preimage result; projecting the polynomial graph proves the
  image result. Empty source and output dimensions are allowed.

`decideHasProductLowQuittingPremium_eq_true_iff`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumDecision.lean`)
connects executable rational-table decision to the original product-low
quitting-premium property, including the empty-player case.
`isSemialgebraic_hasProductLowQuittingPremium_rewardTables`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumSemialgebraic.lean`)
proves semialgebraicity of that class with all real reward entries free.
The premium polynomial itself is defined in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumPolynomial.lean`,
without importing quantifier elimination. Its fixed-reward specialization
has degree at most one in each opponent's hazard and zero in the player's
own hazard, with total degree at most the number of opponents, by
`degrees_quittingFixedRewardPremiumPolynomial_le`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumHazardDegree.lean`).
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRewardTableSemialgebraic.lean`
proves semialgebraicity of strict-exclusion and weak-subset-exclusion
acceptance sets with the reward entries themselves as free coordinates.
`UniformEquilibrium/Quitting/Paths/FiniteCalendarGroupRewardTableSemialgebraic.lean`
proves the group-exclusion version, retaining its uniform parameter outside
the calendar quantifier.
These set-theoretic results do not yet supply executable raw-table tests.

`IsolatedRealRootData.validate_eq_true_iff` and
`decideAtIsolatedRoots_eq_true_iff_exists`
(`MathUE/RealQuantifierElimination/IsolatedRealRootParameters.lean`) extend
the decision interface to certified isolated roots. Each input contains
only rational polynomial coefficients and rational interval endpoints.
Validation checks existence and uniqueness of a real root in the open
interval, permitting repeated polynomial roots. Decision then constrains
the formula's parameters to those roots and applies rational quantifier
elimination. It never computes or compares an unencoded real value.
`isAlgebraic_iff_exists_isolatedRealRootData` and
`exists_certifiedIsolatedRootParameters`
(`MathUE/RealQuantifierElimination/IsolatedRealRootCoverage.lean`) prove
that these descriptions cover exactly the algebraic reals, including every
finite tuple. Coverage is existential, not a computable encoder from an
unencoded real number.
`decideHasProductLowQuittingPremiumAtIsolatedRoots_eq_true_iff`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumIsolatedRootDecision.lean`)
instantiates this interface for product-low quitting reward tables. Its
correctness holds for every actual real table denoted by the certified
entries. `UniformEquilibrium/Quitting/Root/RewardTableParameters.lean`
provides the shared computable reward-entry enumeration and inverse
parameter maps; it has no quantifier-elimination dependency. Rational and
algebraic decision share the expression frontend in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumFormula.lean`.
`exists_certifiedIsolatedRootQuittingReward_of_isAlgebraic`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumIsolatedRootCoverage.lean`)
supplies a denoting encoding for every coordinatewise algebraic actual table;
the same module proves that every certified input denotes a real table.

## Endpoint and coefficient scope

The two implemented endpoints are a computable
`eliminateQuantifiers : PolynomialFormula n -> QuantifierFreeFormula n` with
truth preservation at every environment `Fin n -> Real`, and a computable
`decideClosedFormula : PolynomialFormula 0 -> Bool` whose answer is true exactly when the
closed formula is true over the reals. Arbitrary finite nesting and alternating
existential/universal quantifiers are included. No real comparison belongs to
the executable code. Classical reasoning in correctness proofs is permissible.

Use rational ring-expression syntax with variables indexed by `Fin n`. The
constructors are rational constants, variables, negation, addition, and
multiplication. Polynomial inequalities become sign tests on one expression.
The algorithm is permitted to be inefficient; canonical expansion is not an
endpoint requirement. All real reward entries remain free variables. For
semialgebraic sets with arbitrary real coefficients, finitely many additional
free variables represent those coefficients and are specialized after QE.
The checked real-coefficient projection theorem uses this parameter
representation; it does not compute on an unrestricted real-number encoding.

The target is real semantics first. Generalization to arbitrary instances of
Mathlib `IsRealClosed` is a separate task: the pinned class does not yet provide
the polynomial analysis needed below, and even lists its real instance as a
TODO. A completed real theorem must be described at that actual scope.

## Implementation interfaces

The interfaces below describe how the checked components fit together.

- `RingExpression n`: the expression syntax above, with evaluation at `Fin n -> Real`.
- Coefficient polynomials use `Math.DensePolynomial (RingExpression n)`,
  with coefficients in ascending order. An empty list
  represents zero. `evalAt p rho x` uses Horner evaluation. List length is a
  formal upper bound; it need not equal the specialized polynomial degree.
- Reuse Mathlib `SignType` directly, whose constructors are `neg`, `zero`, and `pos`.
  Do not introduce a duplicate project sign enum.
- `QuantifierFreeFormula n := Math.PolynomialSignCell.SignFormula (RingExpression n)`.
  The existing generic `SignFormula` and `SignFormula.Holds` reside in
  `MathUE/Logic/SignFormula.lean`; `MathUE/PolynomialSignCell.lean` imports
  them for its topology results. `SignFormula.eval` evaluates a sign assignment
  using Boolean operations, with a proved equivalence to `Holds`.
- `PolynomialFormula n`: sign atoms and Boolean connectives, plus `ex` and `all` on
  `PolynomialFormula (n+1)`. Elimination implements universal quantification by negated
  existence. Fix the bound
  variable at index zero and shift outer variables by `Fin.succ`.
- `CoefficientSignBranch n alpha`: leaves in `alpha`, or a `RingExpression n` test
  with negative, zero, and positive child branches.
  Its semantic relation selects the child whose guard has that sign at `rho`.
  No executable real-valued evaluator is needed. Prove exhaustiveness,
  single-path uniqueness, `map`/`bind` semantics, and compilation of a tree
  with `QuantifierFreeFormula n` leaves into one such formula using guarded disjunctions.
- `signDiagram : List (Math.DensePolynomial (RingExpression n)) ->
  CoefficientSignBranch n (List (List SignType))` is the
  core output. For every `rho`, the selected leaf has a real ordered
  cell decomposition realizing every sign entry. The cut points are witnesses
  in the correctness theorem, not executable real numbers in the output.

`Realizes ps rows` asserts existence of a strictly increasing
finite list of real cuts, exactly `2*cuts.length+1` nonempty alternating cells,
correct row width, and correct signs for all points in each cell. Its reduced
form also asserts that every cut is a root of some nonzero specialized input
polynomial and that every root of such a polynomial is a cut. Identically zero
polynomials have sign zero everywhere and do not create cuts. Extra-cut diagrams
may be useful internally, but reduction must restore this exact invariant.

## Dependency structure

Stages 1–6 below are implemented. Stage 7 describes their consumer boundary.

1. Executable dense polynomial kernel, independent of real analysis.
   Implement list operations, Horner evaluation, differentiation, and bounded
   pseudo-division. Prove evaluation identities and structural length bounds.
   A homomorphism to Mathlib `Polynomial Real` can support proofs only.
   Do not put Mathlib's noncomputable field division into executable definitions.
   Raw expression syntax is not a commutative ring under syntactic equality.
   Therefore kernel definitions take a coefficient type with only zero, one,
   addition, negation, and multiplication operations, not `CommRing` laws.
   Prove correctness after applying an evaluator into a genuine `CommRing`
   that preserves those operations. Derivative natural scalars can use repeated
   addition, or a natural-cast operation with its evaluator-preservation lemma.
   This interface supports both rational coefficients and unevaluated syntax.
   The evaluator records preservation of coefficient operations only; it has
   no quantifier-elimination or sign-diagram completeness hypothesis.

2. Real sign-cell mathematics, independent of expression syntax.
   Prove strict derivative sign implies strict monotonicity on a closed cell;
   characterize all interior roots and signs from endpoint signs; establish the
   two unbounded-cell versions from polynomial leading-term behavior. Prove
   deletion of a cut whose retained polynomial columns have no zero there.

3. Symbolic coefficient branching, independent of cell geometry.
   Implement `CoefficientSignBranch`, truth-preserving compilation, and trimming. Trimming
   branches on the last coefficient, deleting it on the zero branch. A nonzero
   branch certifies the specialized degree equals formal length minus one.
   Zero polynomials and constants must terminate without asking for derivatives
   or division by zero.

4. Finite sign-matrix reconstruction, dependent on 1 and 2.
   Given a diagram for the derivative, other input polynomials, and the required
   pseudo-remainders, infer the removed polynomial's signs at retained cuts;
   discard remainder-only cuts; insert at most one new root in each interval;
   delete the derivative column and its now irrelevant cuts. Prove both cell
   coverage and every row's realization, including shared and repeated roots.

5. Complete recursive sign-diagram producer, dependent on 1, 3, and 4.
   Choose an input with maximal positive formal degree. Replace it by its
   derivative, retain the other inputs, and add its pseudo-remainders by the
   derivative and retained nonconstant inputs. All added polynomials have
   smaller formal degree than the removed one. A lexicographic measure
   `(maximum list length, number of inputs with that maximum,
   sum of input lengths plus number of inputs)` decreases. The first two
   components handle the main reconstruction call; the third handles trimming
   or removing lower-degree zero/constant inputs. Make every
   recursive-call inequality explicit. Different zero/nonzero branches may
   have different degrees and diagrams.
   Termination bounds must hold for every syntactic branch leaf, including
   leaves unreachable by a real environment. Correctness of selected leaves
   alone cannot justify recursive calls inside a branch callback. Supply a
   structural all-leaf invariant and a proof-aware branch bind, or equivalent
   attached leaf data, so each recursive call carries its measure bound.

6. One-variable elimination and arbitrary formula recursion, dependent on 5.
   Extract the body's polynomial list, evaluate its Boolean skeleton on each
   sign row, and disjoin successful leaves with their branch guards. Prove
   existential truth equivalence at every real free environment. Structural
   recursion handles all quantifiers. Closed quantifier-free evaluation uses rational
   arithmetic and proves its equality/order transfer to Real.
   Only finitely many atoms occur in a formula; extract and reindex that finite
   family. Do not require `Finite (RingExpression n)` merely to reuse the
   existing sign-cell topology results.

7. Consumer adapters, dependent on 6.
   Product-low formulas use rational reward constants for executable decision,
   or real reward variables for a uniform quantifier-free table characterization. The fixed
   calendar predicates must preserve their stated quantifiers: in particular
   group exclusion has `exists lambda, forall x`, and must not be reduced to an
   existential-only frontend. Semialgebraic projection is the existential case
   of the theorem, with Boolean closure and iteration giving alternating cases.

Stage 4 joins the algebraic and geometric components; stage 5 supplies the
well-founded recursion. Stage 6 calls that concrete producer.

## Pseudo-division and boundary requirements

Return an exponent `k`, quotient `q`, and remainder `r` satisfying
`lc(b)^k * evalAt a = evalAt b * evalAt q + evalAt r`, with formal remainder
length less than the nonempty divisor's length. At a divisor root, do not
identify dividend and remainder signs unless scaling is positive. A convenient
interface returns an even exponent: if ordinary pseudo-division has odd `k`,
multiply its quotient and remainder by `lc(b)` and increment `k`. Under the
nonzero-leading-coefficient branch, the resulting scale is strictly positive.
This avoids threading parity-dependent sign flips through reconstruction.

Remove a zero divisor before pseudo-division. A nonzero constant has no roots
and its remainder is zero; it needs no geometric column. Zero coefficients may
appear after specializing parameters even when their syntax is nonzero: every
use of an exact degree must have an explicit branch proof. Algebraic top-term
cancellation in dense pseudo-division should explicitly drop the canceled
coefficient after proving the evaluation identity; raw expression syntax need
not simplify `a*b-b*a` definitionally.

Repeated roots cause no squarefree restriction: roots shared with the derivative
are already cuts, and insertion only occurs on cells where the derivative has
strict nonzero sign. Shared roots between distinct polynomials give one cut,
possibly several zero columns. The empty input family has the single whole-line
cell with an empty sign row. Unbounded cells require the signs at both ends of
infinity, including parity at negative infinity; bounded IVT alone is insufficient.

## Inspected reusable declarations

- `Math.PolynomialSignCell.SignFormula` and `SignFormula.Holds`
  (`MathUE/Logic/SignFormula.lean`): generic Boolean sign syntax and
  semantics; the polynomial sign-cell topology does not implement
  ordered real root diagrams or geometric reconstruction.
- `SignType` ([Mathlib/Data/Sign/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Sign/Defs.lean)):
  existing finite decidable sign type.
- `Polynomial.hasDerivAt` and `Polynomial.deriv`
  ([Mathlib/Analysis/Calculus/Deriv/Polynomial.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Calculus/Deriv/Polynomial.lean)).
- `strictMonoOn_of_deriv_pos`, `strictAntiOn_of_deriv_neg`
  ([Mathlib/Analysis/Calculus/Deriv/MeanValue.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean)).
- `intermediate_value_Ioo`, `intermediate_value_Ioo'`
  ([Mathlib/Topology/Order/IntermediateValue.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Order/IntermediateValue.lean)).
- `Polynomial.isEquivalent_atTop_lead`, `Polynomial.isEquivalent_atBot_lead`,
  `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg`
  ([Mathlib/Analysis/Polynomial/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Polynomial/Basic.lean)).
- `Polynomial.degree_mod_lt`, `Polynomial.map_mod`
  ([Mathlib/Algebra/Polynomial/FieldDivision.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Algebra/Polynomial/FieldDivision.lean)):
  proof-level division facts;
  this module is explicitly in a noncomputable section.
- `IsRealClosed` ([Mathlib/FieldTheory/IsRealClosed/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/FieldTheory/IsRealClosed/Basic.lean)):
  limited abstract
  foundations, not a QE API.

## Proof references

The chosen proof route is Cohen-Hormander's recursive sign diagrams, presented
in McLaughlin and Harrison, *A Proof-Producing Decision Procedure for Real
Arithmetic* (2005), Sections 3.1-3.3. That work explains reconstruction through
derivatives, remainders, interval signs, and coefficient case splitting. Its
HOL Light implementation produces checked proofs for particular runs; it does
not itself supply an internally verified total Lean function.
[Author-hosted paper](https://www.cs.cmu.edu/~seanmcl/papers/McLaughlin-CADE-2005.pdf).

Cohen and Mahboubi, *Formal proofs in real algebraic geometry* (2012), gives a
fully verified algebraic QE route based on pseudo-remainders. This establishes
that the required completeness and execution properties are known mathematics
with a prior formal precedent. It is a larger alternative because it requires
sign determination and associated algebraic counting infrastructure.
[Journal paper](https://lmcs.episciences.org/844).

Kosaian, Tan, and Platzer, *A First Complete Algorithm for Real Quantifier
Elimination in Isabelle/HOL* (2023), verifies a Tarski/BKR hybrid with general
multivariate formula elimination. This is another complete precedent, not a
Lean import or proof of this implementation.
[Author paper](https://arxiv.org/abs/2209.10978).

No practical complexity bound is claimed. The implementation proves termination
and universal correctness; its coefficient branching can produce large trees.
`Experiments/RealQuantifierEliminationRegression.lean` records small executable
tests separately from proofs through the correctness theorem. The executable
polynomial tests use one quantified variable; they do not establish practical
performance for alternating polynomial formulas or game-table inputs.
Nor does finite-dimensional quantifier elimination decide the uniform-equilibrium
conjecture: that would require a finite formula equivalent to the original
strategy and horizon quantifiers.
