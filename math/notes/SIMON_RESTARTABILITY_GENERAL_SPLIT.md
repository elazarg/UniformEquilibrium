# Simon restartability for a finite polytope split

## Setting

Let `P_1,...,P_m` be compact full-dimensional convex polytopes with compact
union `K`, and let `G ⊆ K × K` be Simon’s compact correspondence. An edge may
start in one polytope and end in another. Local escape data may be attached
to a piece or to a boundary face. The cost is a nonnegative metric variation.

## Question

Construct or refute a finite labelled restart system: compact nonempty sets
`R_j ⊆ P_j` and a directed finite label graph such that each `x ∈ R_j` has a
legal successor in some `R_k` with edge cost at least the label-dependent
positive amount, and every infinite label path has unbounded cumulative cost.
Then prove that the resulting finite prefixes are compatible and satisfy the
full Simon graph constraints. If this stronger formulation is false, state
the weakest split/reprojection condition that still yields one diverging
budget schedule.

## Why this is useful

It is the actual finite-union version of restartability. It prevents a proof
from reusing a local edge after it has left the polytope on which the edge was
certified, and would feed `QuestionOneConclusion` without hidden chronology.

## Checked inputs and consumers

- `QuestionOneHypotheses.fullGraph_compact` and
  `QuestionOneHypotheses.localGraph_subset_fullGraph`
  (`MathUE/Topology/SimonViabilityQuestion.lean`) provide the graph carrier.
- `graphCoordinateBox_compact` and
  `coordinateBox_relationGraph_eq`
  (`MathUE/Topology/SimonViabilityBudgetCompiler.lean`) provide a compact
  common box for graph endpoints.
- `exists_compatible_edgeBudgetedFinitePrefixes_of_restartableExtension`
  (`MathUE/Topology/CompactEdgeBudgetedPrefixRelation.lean`) consumes a
  restart set once one has been identified.

## Not proved

The existing one-edge escape theorem does not retain a piece label or prove a
finite recurrent split. Compactness of the union alone does not provide
restartability.

## Acceptable answers

A positive answer supplies the labelled sets, transition proof, and a
positive cumulative-cost argument. A negative answer supplies exact compact
polytopes and a correspondence satisfying the hypotheses but forcing every
label path to return with arbitrarily small cost or leave all restart sets.

## Dependencies

None required.
