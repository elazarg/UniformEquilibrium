# Simon restartability in one polytope

## Setting

Let `P` be one compact, full-dimensional, convex polytope in a finite
Euclidean space. Let `G ⊆ P × P` be compact with nonempty contractible local
fibers, and assume the relevant boundary homotopy and Simon local escape
condition. An edge has cost `d(x,y)`, usually Euclidean distance.

## Question

Prove or refute the one-polytope restart lemma: there are `a > 0` and a
nonempty compact restart set `R ⊆ P` such that every `x ∈ R` has a successor
`y ∈ R` with `(x,y) ∈ G` and `d(x,y) ≥ a`. It is acceptable to replace `R`
by finitely many labelled compact restart sets if the labels and transitions
are explicit. The statement must preserve all stated fiber and boundary
hypotheses, not merely the existence of one local escape edge.

## Why this is useful

Iterating the restart edge gives one compatible path with budget `a n`; the
generic compact-prefix compiler then yields an unbounded-variation extended
orbit. This isolates the topological obstruction before the finite-union
case.

## Checked inputs and consumers

- `QuestionOneHypotheses` (`MathUE/Topology/SimonViabilityQuestion.lean`)
  records the seven hypotheses.
- `HasRestartableExtension` and
  `exists_compatible_edgeBudgetedFinitePrefixes_of_restartableExtension`
  (`MathUE/Topology/CompactEdgeBudgetedPrefixRelation.lean`) implement the
  abstract iteration once restartability is supplied.
- `linearEdgeBudget_tendsto_atTop` (same file) supplies divergence for
  `a > 0`.

## Not proved

Simon’s hypotheses currently yield one local edge, not a reusable restart set.
No one-polytope theorem has been checked.

## Acceptable answers

A positive answer proves an invariant/restart set and a uniform edge cost. A
negative answer gives one exact polytope/graph satisfying the hypotheses for
which every positive-cost recurrent set is empty or has cost tending to zero.
A graph that violates compactness, contractible fibers, or the boundary
condition is not a falsifier.

## Dependencies

None required.
