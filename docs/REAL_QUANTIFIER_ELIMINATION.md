# Real quantifier elimination: constructive implementation contract

This is an implementation plan for known mathematics. The complete
quantifier-elimination and decision theorems remain unproved here.
The checked components and remaining dependencies are described below.

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
  expression syntax, rational and real evaluation, and variable renaming.
  `MathUE/RealQuantifierElimination/CoefficientSignBranch.lean` proves that
  finite coefficient-sign trees compile to truth-equivalent Boolean formulas
  at every real environment. It does not generate a sign diagram.
- `MathUE/Polynomial/RealSignCell.lean` supplies interval root and sign
  lemmas. `MathUE/Polynomial/OrderedRealSignDiagram.lean` proves the ordered
  cell partition, exact diagram dimensions, removable-cut deletion, and
  bounded root-insertion transformations. These transformations consume
  previously established row signs and derivative conditions.

Specialization trimming, polynomial asymptotic signs, complete reconstruction,
the recursive sign-diagram producer, formula elimination, and the two packet
adapters remain to be completed. Targeted checks of the available components
do not establish those later stages.

## Endpoint and coefficient scope

The two completion endpoints are a computable
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
This yields projection closure with real coefficients without pretending to
compute on an unrestricted real-number encoding.

The target is real semantics first. Generalization to arbitrary instances of
Mathlib `IsRealClosed` is a separate task: the pinned class does not yet provide
the polynomial analysis needed below, and even lists its real instance as a
TODO. A completed real theorem must be described at that actual scope.

## Implementation interfaces

The interfaces below specify how the components fit together. The full
formula type and sign-diagram producer are still proposed interfaces.

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
- `PolynomialFormula n`: sign atoms and Boolean connectives, plus `exists` on
  `PolynomialFormula (n+1)`. Universal quantification is negated existence. Fix the bound
  variable at index zero and shift outer variables by `Fin.succ`.
- `CoefficientSignBranch n alpha`: leaves in `alpha`, or a `RingExpression n` test
  with negative, zero, and positive child branches.
  Its semantic relation selects the child whose guard has that sign at `rho`.
  No executable real-valued evaluator is needed. Prove exhaustiveness,
  single-path uniqueness, `map`/`bind` semantics, and compilation of a tree
  with `QuantifierFreeFormula n` leaves into one such formula using guarded disjunctions.
- `signDiagram : List (Math.DensePolynomial (RingExpression n)) ->
  CoefficientSignBranch n (List (List SignType))` is the
  eventual core output. For every `rho`, the selected leaf has a real ordered
  cell decomposition realizing every sign entry. The cut points are witnesses
  in the correctness theorem, not executable real numbers in the output.

`DiagramRealizes ps rho rows` must assert existence of a strictly increasing
finite list of real cuts, exactly `2*cuts.length+1` nonempty alternating cells,
correct row width, and correct signs for all points in each cell. Its reduced
form also asserts that every cut is a root of some nonzero specialized input
polynomial and that every root of such a polynomial is a cut. Identically zero
polynomials have sign zero everywhere and do not create cuts. Extra-cut diagrams
may be useful internally, but reduction must restore this exact invariant.

## Dependency DAG and implementable chunks

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

Chunks 1, 2, and 3 can be assigned independently with the interfaces above.
Chunk 4 is the principal join and chunk 5 is the principal termination join.
Chunk 6 alone is not completion if it accepts the missing eliminator as data.

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

## Proof references and remaining work

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
Lean import or proof of our proposed implementation.
[Author paper](https://arxiv.org/abs/2209.10978).

Risk estimate: this is a substantial multi-session library development, likely
several thousand Lean lines even with existing polynomial analysis. The exact
size has not been measured. The difficult work is exhaustive diagram
reconstruction, symbolic specialization, and the total recursive producer.
Completion requires a computable implementation and its universal correctness
theorem, including the recursive sign-diagram producer.
