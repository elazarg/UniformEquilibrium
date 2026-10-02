# Review of Sections 8--9 of `CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY`

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**, with one theorem-shape qualification for any later Lean
handoff.  The mathematical alignment and the count `8+9=17` are correct.

## Claim checked

Sections 8--9 claim that every marked strict-preemption lasso whose periodic
cycle has length two makes its literal two cycle labels a nonprojective
principal of the normalized singleton matrix.  The checked
`FinFourQuantitativeFullSupportHardResidual.cardTwoCrossing` theorem can then
be applied to that same pair.  Exactly eight of the seventeen marked lasso
constructors have a two-cycle; `rootedTwo_next` further identifies that pair
with the collision owner and collider.

## Projective-LCP calculation

The repository definition in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean` is

```text
w_i = cemetery*q_i + sum_j singleton_j*M(i,j) >= 0,
cemetery + sum_j singleton_j = 1,
cemetery,singleton_j >= 0,
singleton_i*w_i = 0.
```

For the two-coordinate zero-diagonal principal, take `q=(-1,-1)`.  If the
labels are `u,v`, the two residual inequalities are exactly

```text
0 <= -c + y*M(u,v),
0 <= -c + x*M(v,u).
```

With both reciprocal entries strictly negative and `c,x,y>=0`, the first
inequality forces `c=y=0`, and the second forces `c=x=0`.  This contradicts
`c+x+y=1`.  The cemetery coordinate has therefore been handled correctly;
the argument is stronger than a homogeneous-simplex obstruction and does not
need complementarity.  Lemma 8.1 is valid.

## Edge/matrix orientation

`QuittingSoloPreempts reward gamma owner other` states

```text
r_other({owner}) + gamma <= r_other({other}).
```

Using `normalizedSoloMatrix_eq_soloReward_sub`, the directed edge
`owner -> other` gives

```text
M(other,owner) <= -gamma < 0.
```

Thus the forward and backward edges of a two-cycle give both reciprocal
negative entries, with no row/column reversal in Proposition 8.2.  Since the
two cycle vertices are distinct, their finset has cardinality two, and the
existing `cardTwoCrossing` theorem applies to precisely that principal.

## Constructor count and marker alignment

The two-cycle constructors in `MathUE/FiniteSerialRelation.lean` are exactly:

```text
rootedTwo_next, rootedTwo_outside,
oneToTwo_entry, oneToTwo_other, oneToTwo_outside,
twoToTwo_first, twoToTwo_entry, twoToTwo_other.
```

The counts are `2+3+3=8`.  The other constructors comprise three rooted
three-cycle positions, three rooted four-cycle positions, and three
one-step-to-three-cycle positions, totaling nine.  Hence the marked witness
count remains seventeen, while its coarse algebraic dispatch becomes one
aligned two-cycle arm plus nine long-cycle arms.

For `rootedTwo_next`, the rooted lasso root is the collision-certificate
owner and `marker_eq` identifies its other cycle vertex with the collider.
The literal hard pair is therefore
`{collision.owner, collision.collider}`.  The two helpers returned by
`cardTwoCrossing` lie outside that pair and may coincide; Sections 8--9 state
this scope correctly.

## Boundary and scope audit

The paired matrix in Section 9 has reciprocal negative entries on the stated
pair and positive uniform row sums, so it tests the aligned two-cycle arm.
The crossed-row calibration instead has the displayed tail into a directed
three-cycle and does not acquire projective-Q-bar failure from its checked
fields.  Neither calibration supplies a terminal exploitability witness or
positive-minimum semantic tail.  The note correctly uses them only as finite
algebraic boundary tests.

The result aligns the LCP principal with the selected preemption-cycle pair;
it does not align the separately produced strict-toggle semantic cycle, does
not eliminate the eight marked semantic geometries, and does not provide an
all-behavior compiler.  Those nonclaims are accurate.

## Lean-handoff qualification

`MarkedRootedLasso` has no common stored `cycleVertices` field or a literal
`cycle.length = 2` predicate.  A formal theorem should therefore either:

1. define a decoder/subtype for the eight two-cycle constructors and its
   two-vertex finset; or
2. state eight case lemmas and combine them by cases on the inductive value.

This is a representation issue, not a mathematical gap in Proposition 8.2.

