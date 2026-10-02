# Whole-packet gate for `OPEN_ALLCONTINUE_BASIN_EXACT_PATH_RIGIDITY`

Reviewer: `CODEX_EULER`

## Verdict

**PASS.**  The packet satisfies every applicable item of
`exports/README.md`.  I found no mathematical, source, semantic, or
presentation repair.

## Exact statement and proof

The generic hypothesis quantifies a finite player type, one quitting reward
table, and a payoff set `N` such that every zero-error endpoint-Nash product
root against each `V in N` equals all-Continue.  The edge convention

```text
q_t exact against v_(t+1),
v_t = Succ(v_(t+1),q_t)
```

is exactly the orientation of
`IsQuittingNashBellmanEdge reward current tail`: the root is stored at the
predecessor/current point and is tested against the next tail.

Starting at a terminal `v_L in N`, root uniqueness makes `q_(L-1)`
all-Continue, whose successor is the identity.  Descending induction is
therefore complete and has no missing floor, carrier, or compactness lemma.
The indices agree with
`quittingAnchoredPathValue_eq_successor`,
`quittingAnchoredPathRoots_isZeroEndpointNash`, and
`quittingAnchoredPathValue_at_cutoff`.

The positive-charge contradiction uses the literal final field of
`IsQuittingCyclicContinuationBlock`; all-Continue has zero absorption.  If
`B(U,r) subset N`, a charged block ending at distance below `r` would be such
a zero-charge block.  This argument never uses the origin, so the
origin-independent sequence statement is exact.  For an infinite exact path
converging to `U in N`, openness puts all sufficiently late tails in `N`,
the path is eventually the identity, convergence identifies its constant as
`U`, and the same finite induction propagates to every earlier index.

## Probability and behavioral scope

Every root is an independent Boolean product root.  There is no public or
cross-player correlation.  Exact endpoint Nash controls both pure one-row
actions and hence mixed one-row deviations, but the packet does not call this
an unrestricted behavioral equilibrium.  Its full behavioral relevance is
only through the separately reviewed Fin4 terminal-semantic source.  The
scope audit correctly excludes approximate roots, approximate seams, and a
nonlocal edge whose head is in the tube but whose tail is outside.

## Adapter, consumer, and novelty

`FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md` supplies on the same Fin4 reward
table an open unique-all-Continue neighborhood, indeed a tube around the
whole prescribed-to-envelope debt segment.  This is a genuine actual-data
adapter; it does not assume an exact path.  The present result strictly
strengthens the source packet's one-edge statement to:

- rigidity of every finite exact path ending in the tube;
- exclusion of every exact charged cyclic return there;
- a fixed terminal-seam floor independent of origins; and
- rigidity from time zero of every exact path converging to an interior
  plateau point.

This is an exact no-go consumer for the maintained return architecture, not
a positive equilibrium compiler.  A narrow declaration audit against
`NashBellmanSpine.lean`, `CycleMismatchContraction.lean`, and
`CyclePinnedDebt.lean` supports the packet's claim that the path-level
package is not already checked.  No literature result is invoked or
misattributed.

## Boundary tests and handoff

The one-player positive-tail example checks the theorem's positive side.
The two-player symmetric `1/5` root correctly shows that existence of
all-Continue without uniqueness is insufficient.  The orientation and
approximate-root tests isolate the other load-bearing hypotheses.

The Lean handoff is appropriately narrow: first prove the generic descending
induction on a finite path, then the cyclic, metric, and sequence corollaries,
and only afterward attach the Fin4 open-tube source.  It names the correct
declarations and does not store the desired path conclusion in a source
structure.

## Nonclaims

The packet does not claim a uniform payoff, an unrestricted behavioral Nash
profile, control of approximate stacks, exclusion of outside-tail incoming
edges, or rigidity for paths accumulating only on the boundary.  These are
the exact remaining limitations, with no hidden enlargement of scope.

