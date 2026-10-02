# Product-low decision procedure: formalization boundary

Author: CODEX_ROOT. This records a library dependency, not an open mathematical
claim or a failure of the explicit product-low family proof.

## Known mathematical result

Let a finite quitting game have rational terminal rewards. For each player i
and nonempty coalition S containing i, put d_i(S) = r_i(S) - r_i({i}). For a
vector q of independent Quit probabilities define

    h_i(q) = sum over T contained in I minus {i} of
      (product over j in T of q_j)
      (product over j in I minus (T union {i}) of (1-q_j))
      d_i(T union {i}).

The product-low condition says that every nonzero q in [0,1]^I has some i
with q_i > 0 and h_i(q) <= 0. Its failure is the finite disjunction, over
nonempty active subsets A, of the following real feasibility problems:

    q_j = 0 for j outside A;
    0 < q_i <= 1 and h_i(q) > 0 for every i in A.

These are finite systems of polynomial inequalities with rational
coefficients. Real-closed-field quantifier elimination decides their
feasibility. This is known mathematics; no new conjecture is involved.

## Minimal usable Lean interface

A terminating computable function should take a finite player count and its
rational terminal-reward table and return a Boolean, with a theorem that the
answer is true exactly when `HasProductLowQuittingPremium` holds for the
real-valued embedding of that table. The function must not use
`Classical.propDecidable` as an alleged algorithm. Its proof may use the
project's permitted logical axioms. No complexity bound, efficient
implementation, rational witness for arbitrary semialgebraic systems, or
algorithm on unrestricted real-number encodings is required.

A generic decision procedure for finite rational polynomial sign systems
would also suffice, provided it supplies a checked soundness and completeness
theorem. Algebraic input coefficients are an optional extension, not a
prerequisite for the rational-table interface. Passive reward coordinates
need not enter the calculation.

## Current evidence and nonclaim

A bounded search of the pinned Mathlib model-theory sources found no
real-closed-field quantifier-elimination or semialgebraic decision API.
This is a search result, not proof that no reusable implementation exists
elsewhere. The project now supplies its own checked implementation below.

The user has authorized implementing this shared dependency. The maintained
contract and dependency graph are in `docs/REAL_QUANTIFIER_ELIMINATION.md`.
The chosen route is real polynomial sign-diagram elimination, with
executable symbolic coefficient arithmetic and correctness for arbitrary
real free-parameter environments. The actual recursive sign-diagram producer,
arbitrary nested quantifier elimination, and rational closed-formula decision
are integrated and passed a strict silent full build. The current declarations
are `signDiagram_correct` in
`MathUE/RealQuantifierElimination/SignDiagramProducer.lean`, and
`eliminateQuantifiers_holdsAt_iff` and `decideClosedFormula_eq_true_iff` in
`MathUE/RealQuantifierElimination/QuantifierElimination.lean`. They take no
producer or eliminator hypothesis. Their finite-dimensional real semantics
do not decide UE itself. The product-low rational-table encoding and actual
semantic adapter are now integrated in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumDecision.lean`.
`decideHasProductLowQuittingPremium_eq_true_iff` proves exact equivalence to
the original PMF-root condition, universally testing real hazards even though
the input rewards are rational. Ordered finite enumeration and rational
closed-formula evaluation make the decision executable without a real oracle.
The empty-player case is explicitly proved. The full integration build and
complete repository gate passed; the implementation is pushed in `1f5e4dd`.
An independent static audit found no semantic or computability defect.

The explicit family in
`UniformEquilibrium/Quitting/Examples/ProductLowFinFourFamily.lean` is proved
by its literal endpoint formulas and exhaustive support argument; it does
not depend on quantifier elimination. The generic product-low equilibrium
producer likewise assumes the table condition, not a decision algorithm.
The rational-table interface is supplied. Semialgebraicity with reward entries
as free variables and the decision-to-periodic/UE consumers passed the full
integration build and repository gate and are pushed in `0a8af85`.
The same commit supplies certified rational-polynomial isolating intervals,
executable validation, and formula decision at those roots. Existential
coverage of every real-algebraic value passed the full integration build and
repository gate and is pushed in `64b38b3`. An independent static review
confirmed coverage of repeated roots and the existential encoding scope.
The product-low encoded-algebraic frontend and its same-table coverage
companion passed the full silent build and complete repository gate and are
pushed in `36e9ced`. Independent review found no semantic, computability,
or binder defect. All useful packet content is covered; the frozen packet
is now under `math/formalized/` with
`PRODUCT_LOW_QUITTING_PREMIUMS_LEAN_COVERAGE.md`. The requested Astra
proof-mining pass is complete. Its proposals and nonclaims are recorded in
`CODEX_ASTRA_MINER__MAXIMUM_DEBT_COLLARS_AND_WITNESS_RICH_CAP_INTERFACES.md`;
they are not new checked theorems.
