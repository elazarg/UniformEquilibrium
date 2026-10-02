# Review of common second-order stopping-law repair

Reviewer: CODEX_LARCH_DUAL.

Reviewed note:
[common second-order repair](../notes/CODEX_LARCH_JOINT__MULTILATERAL_REPAIR_THEORY.md).

Status: independent ordinary-mathematical review, not a Lean check. The finite
Taylor criterion, dual signs, and exact calibration are valid. Two local
clarifications are requested: the relative-interior sentence must explicitly
restrict the optimization to the chosen face, and the general boundary
approximation constant is 2M rather than M under an absolute reward bound M.
Neither changes the candidate's qualitative conclusion. No arbitrary-source
UE progress is established by the current sketch.

## 1. The common acceleration criterion is valid

For the product simplex, p+εv+ε²w remains feasible for all sufficiently small
positive ε exactly under the displayed first- and second-order tangent
conditions: the coordinate sums vanish, v is nonnegative at zero source
coordinates, and w is nonnegative where both p and v vanish. At a zero
source coordinate with positive v, any fixed finite w is allowed. Positive
source coordinates remain positive for sufficiently small ε. There is no
missing separate upper-bound condition: nonnegativity and sum one imply it.

The expansion has the correct coefficient for the convention ε²w:

    ε Dg[v] + ε²(Dg[w]+½D²g[v,v]).

The finite tester set justifies the uniform remainder and a positive gap for
inactive tests. Strictly negative first-order rows dominate any second-order
term. The displayed conclusion with c/2 follows for sufficiently small ε.
No differentiability of the maximum is assumed or needed.

## 2. Dual signs and strict alternative are correct

For fixed v, write q=(Q_a(v)) and C=L(W_v). The primal question is whether
q+C intersects the open strictly negative orthant. If it does not, separation
gives a nonzero λ≥0 such that

    λ·L(w)≥0 for all w∈W_v,          λ·q≥0.

The first sign follows also by scaling w: a negative λ·L(w) would make the
separated functional arbitrarily negative. Normalize λ to sum one. This is
exactly the note's Λ_v and its nonnegative-curvature obstruction. Conversely,
such a λ precludes strict negativity by averaging. Since Λ_v is a closed
subset of the finite simplex, it is compact, so strict negativity for each
of its elements gives a uniform negative maximum. Thus equation (5) has the
correct cone orientation and the correct treatment of the empty dual set.

The quantifier warning is essential: one common v must work against all
blocking λ. The argument does not license exchanging the search over v with
the dual maximum.

### Requested boundary clarification

The sentence “At a source in the relative interior of the chosen face, W_v
is its tangent space” needs an explicit restriction of the optimization to
that face. Relative interior in a minimal face alone is insufficient if
outside-face atoms remain legal. Even for v tangent to the minimal face,
an outside-face zero coordinate may open at order ε², so W_v has a one-sided
direction and is not a vector space.

The simplest example is the interval [0,1], p=0, v=0: p is in the relative
interior of its minimal face {0}, but W_v=[0,∞), not the zero tangent space.
The corrected sentence can say: “If the optimization is restricted to a face
F and p lies in its relative interior, W_v is the tangent space of F.”
Alternatively use an interior point of the full domain. The primary formula
(3) is already correct; this is a correction to its subsequent interpretation.

## 3. Exact calibration independently checked

With pivot 0 surely stopping at zero, player 1's prescribed reward is
−(1−a)+ab=−1+a+ab. Its date-zero response pays b; every later response and
Never pays −1. Thus B_1=b on the whole square, including endpoints.
Player 2 is symmetric. The pivot earns 1, and no response can exceed 1;
player 3 has identically zero rewards and cap.

Therefore the only potentially maximal debts are

    1−a+b−ab,        1+a−b−ab,

and their maximum is 1+|a−b|−ab. At (0,0), all legal first-order slopes are
|h−k|≥0, while the diagonal has exact decrease −ε². All positive-time and
Never response tests for players 1 and 2 have source gain zero, hence are
strictly inactive against source maximum one. The example genuinely shows
second-order improvement of the full cap objective on the specified face.

Its limitation is correctly stated: it is not a positive global minimum or
an arbitrary-law coordinate trap. It demonstrates the mathematical need for
the proposed order of expansion, not a new difficult quitting-game class.

## 4. Pivot implementation: a constant needs its hypothesis

The exact objective and behavioral approximation APIs support the qualitative
claim that a strict O(ε²) mass-model improvement can be implemented by actual
laws with error o(ε²). However, under a general absolute reward bound M, the
inspected declaration
`exists_law_boundary_approximation_of_reward_bound`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralApproximation.lean`)
gives error 2M times the inserted first-atom mass α.

The sharper Mα bound belongs to
`exists_law_boundary_approximation_of_reward_bound_of_later_zero`
in the same file and assumes every nonpivot's own singleton reward is zero.
The general statement should use 2Mα or explicitly say M bounds the relevant
tie-minus-later coefficient. Choosing α=o(ε²) works with either constant;
this correction does not alter the theorem sketch or its consumer.

If the admissible late mass also tends to zero, choose α below that mass as
well as below the desired error scale. Positive late mass permits such a
choice at each ε; zero late mass is an exactly implemented boundary case.

## 5. Usefulness assessment

The candidate has a real local consumer: it converts several response-square
calculations into a single actual product-law perturbation controlling the
entire response envelope. Its main benefit is a precise finite compatibility
test, replacing an invalid inference from one negative square or one favorable
multiplier. This is a useful unification target.

The conjecture-facing producer remains substantial. A critical direction
alone is not enough; the full dual curvature family must have uniformly
favorable sign, and near-minimum errors must be smaller than the resulting
decrease. Generic second-order calculus cannot provide these facts at a true
positive global minimum. The note says this explicitly and should retain it.

I recommend a bounded source test before a library: take one already
constructed actual payoff/cap-preserving family, calculate its complete
critical cone and Λ_v, and see whether the table/clock structure restricts
that family beyond generic KKT conditions. If the only output is another
certificate saying a hypothetical global minimum is locally minimal, stop.

No Lean build, numerical optimization, or external theorem verification was
run for this review. The finite algebra above was checked directly; the
behavioral approximation constants were checked in the named source file.
