# Minimal robust capacity through the actual one-sided smoothing producer

Owner: CODEX_RADO_BOUNDARY.

Status: completed bounded source-strength test, ordinary mathematics.
The exact comparison below is valid under finite global outer capacity.
The attempted extra condition at a smooth or polynomial minimum reduces
to a property of EVERY bounded potential. No barrier is excluded, no
equilibrium is constructed, and no new conditional interface is proposed.

## 1. One selected question and literal source

The current no-UE implication does not merely assume an arbitrary H.
It produces finite robust charge capacity, convolves that capacity, and
approximates the resulting derivative by a rational polynomial. Could
the capacity's pointwise minimality or zero infimum force an additional
boundary value at the produced potential's minimum, unavailable to a
general polynomial certificate?

Fix a bounded Fin4 table r with |r_i(S)| ≤ M and zero Never. Use the
CURRENT floor-free relation: an edge (v,q,w) has independent root q,
absorption a(q), and, for every i,

    |w_i−F_i(q,v)| ≤ δ a(q),       e_i(q,v) ≤ δ a(q).

Annotations are arbitrary boxed vectors. There is no payoff realization,
punishment floor, support condition, positive-charge floor, or selected
root. The root and target in each path are retained literally.

For B≥0 and 0<ε≤1, write

    R₋ = R(r, ε/4, B),       R₊ = R(r, ε, B+1),
    V₋(v) = sup charges of finite R₋ paths starting at v,
    V₊(z) = sup charges of finite R₊ paths starting at z,
    β₋, β₊ = their global finite-path charge suprema.

Assume R₊ has finite budget. This is a genuine produced condition in
the current no-UE source, not an added strategic witness. Specifically,
under the normality and positive-singleton hypotheses of
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`,
the proof obtains rational ε>0 with ε≤1 and finite capacity at radius
M+3; it then uses B=M+2. No-UE also excludes the separate sure-root exit.
The following comparison itself needs only finite outer capacity.

## 2. What capacity really optimizes

For either finite-budget relation, the capacity is its least nonnegative
supersolution:

    V(target)+charge ≤ V(source),       V≥0,

and every nonnegative function with this edge inequality dominates V.
Moreover

    inf V = 0,       sup V = β,       oscillation(V)=β.  (1)

These are actual declarations `isLeast_value`, `sInf_range_value`,
`sSup_range_value`, and `budget_eq_oscillation_value` in
`MathUE/ChargedPathBudget.lean`. The zero is an INFIMUM; this theorem
does not produce a state where V=0. The source gives Borel measurability
of the all-horizon capacity, not its continuity or lower semicontinuity.
Finite-horizon attainment and upper semicontinuity do not change that
statement about the supremum over all horizons.

## 3. Exact inner/outer comparison

For every h with 0≤h_i≤ε/4, common translation of every source and
target in an R₋ path gives an R₊ path. It preserves each literal root,
length, and charge. The source proves the sharper estimates

    translated Bellman residual ≤ (ε/2)a,
    translated ordinary Nash defect ≤ (ε/2)a.

The shifted states remain in the box of radius B+1. Thus, taking path
suprema under the finite outer budget,

    V₋(v) ≤ V₊(v+h)                                  (2)

for every v∈[−B,B]^4 and every such common h. In particular R₋ has
finite budget. This is a CROSS-TOLERANCE, CROSS-BOX comparison, not
monotonicity of one capacity function in its state coordinate.

Let k be the actual normalized nonnegative one-sided smooth kernel,
written in positive-shift coordinates. It samples only 0<h_i<ε/4.
The produced smooth function is

    S(v) = ∫ k(h) V₊(v+h) dh                          (3)

on the inner box. Formula (3) is literal there: every sampled point lies
inside the outer box, so the zero extension outside that box contributes
no boundary zero to this integral.

Integrating (2), and using 0≤V₊≤β₊, gives

    0 ≤ V₋(v) ≤ S(v) ≤ β₊.                           (4)

The actual smoothing theorem separately proves that S is a potential
for R₋. Let

    m = min_[−B,B]^4 S.

It exists because S is smooth and the inner box is compact. Then S−m
is a nonnegative R₋ supersolution. Capacity minimality therefore gives
the stronger exact quantitative statement

    0 ≤ V₋(v) ≤ S(v)−m ≤ β₊−m,                      (5)
    β₋ ≤ oscillation(S on the inner box) ≤ β₊−m.

This is the surviving source comparison. It does not identify S with V₋,
or identify either budget with the oscillation of S. The outer capacity
is optimal for R₊; S is only a supersolution for the smaller R₋.

## 4. The proposed minimum/boundary use stops

At any minimizer z of S, (5) gives V₋(z)=0. Consequently there is no
positive-charge R₋ path starting there. That sounds stronger than mere
drift, but it is not extra information from the producer: for ANY bounded
potential H on R₋, telescoping gives

    V₋(v) ≤ H(v)−inf H.

At an attained H-minimum the same zero-capacity conclusion follows.
In particular, finite root Nash existence at that annotation supplies
only all-Continue; an absorbing root would contradict minimality. The
known singleton-face argument further places every C¹ potential minimum
strictly above every own singleton. Neither consequence distinguishes
the capacity-produced S from an arbitrary smooth barrier.

The tempting next inference would be m=0 because inf V₊=0. It is not
an inference furnished by this producer. The infimum in (1) ranges over
the OUTER box, need not be attained, and gives no zero neighborhood.
The convolution averages positive shifts, not an optimizing point of
V₊. A nonnegative normalized average preserves a lower bound of zero;
it does not supply an upper bound of zero at an inner minimizer. Likewise,
the zero extension makes S vanish sufficiently far outside the boxes,
but those points are outside the relation on which its drift is retained.

Even if an additional argument established m=0, the immediate conclusion
V₋(z)=0 is already the arbitrary-potential statement above. Further
information about a positive-measure family of OUTER zero-capacity
states would require a separate, actual-relation argument; none is
produced or assumed here.

This records a failed proof implication, not a counterexample to a
stronger theorem about a hypothetical no-UE table. No solved-table
calibration is used to deny any consequence of positive global capacity.

## 5. What reaches the rational polynomial

The final approximation is of derivatives, not of a prescribed boundary
value. In the actual proof put

    D = max(1, M+B+ε/4).

A rational polynomial P is chosen with derivative error from S at most
1/(2D) on the inner box, and H=2P supplies the required unit charge
drift. The mean-value estimate yields, for all v,w in that box,

    |[H(v)−H(w)]−2[S(v)−S(w)]| ≤ ||v−w||∞/D.          (6)

Thus this particular construction retains an increment comparison,
up to the chosen approximation error. It does not retain a named zero,
an exact minimum value, Bellman equality, a coordinatewise derivative
sign, or capacity minimality. A rational constant can be added without
changing any edge drift, further emphasizing that a boundary level is
not a semantic output of the characterization.

The normalized-capacity bound at an H-minimum remains valid, but again
because H is a potential, not because it was produced by convolution.
Equations (5) and (6) give no return and no sign contradiction for the
actual quitting-root relation.

## 6. Source record and disposition

The `docs/TOOLKIT.md` current polynomial route was followed only to:

- `RobustChargedRelationCapacity.lean`: finite-horizon attainment and
  `measurable_quittingRobustChargedRelation_value`;
- `RobustChargedRelationTranslation.lean`: common vector translation,
  both half-tolerance bounds, and unchanged charge;
- `RobustChargedRelationSmoothing.lean`: zero extension, its bounds,
  `quittingRobustSmoothedCapacity`, and
  `quittingRobustChargedEdge_charge_add_smoothedCapacity_target_le_source`;
- `MathUE/Analysis/OneSidedCapacitySmoothing.lean`: the actual kernel's
  nonnegative normalization, support, and convolution identity;
- `MathUE/ChargedPathBudget.lean`: the capacity, minimality, infimum,
  oscillation, and telescoping declarations used above;
- `RobustChargedRelationPolynomialPotential.lean`,
  `RobustChargedRelationPolynomialSeparator.lean`, and
  `MathUE/Interval/RationalPolynomialChargedDrift.lean`: the literal
  derivative approximation and doubling used in (6);
- `PolynomialForwardCertificateCharacterization.lean`: the actual
  no-UE → finite outer capacity → smoothing → rational H source chain.

The unqualified Quitting source filenames in this list are in
`UniformEquilibrium/Quitting/Projective/`. The already completed
[convex-potential note](CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY.md)
and [separable-potential note](CODEX_RADO_BOUNDARY__NONCONVEX_SEPARABLE_POLYNOMIAL_DRIFT_EXCLUSION.md)
supply the known strict location of C¹ minima; it is not re-proved here.

Stop this selected operation. The exact finite-capacity comparison (5)
survives, but the proposed additional minimum condition was already
present for arbitrary H. No continuity, equality, or one-sided gradient
sign is silently added to the produced capacity. The remaining question
of whether some other property of this actual capacity can exclude a
barrier is not pursued in this pass. No Lean build or export was made.
