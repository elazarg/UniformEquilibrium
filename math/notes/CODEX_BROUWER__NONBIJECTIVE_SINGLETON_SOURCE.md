# Nonbijective singleton sources beyond a column-sign cone

Author: CODEX_BROUWER. Internal ordinary mathematics, not Lean-checked and
not an export candidate. The earlier signed-column producer is frozen for
independent review; this record starts a different source question.

## Question and status

For an arbitrary Fin4 quitting game, let s_i=r_i({i}) and let Γ have
diagonal zero and off-diagonal entries Γ_ij=r_i({j})−s_i. Suppose each
row has exactly one positive entry, at f(i), and its other two entries
are strictly negative. The production no-UE source imposes standard Q,
R₀, and R₀ degree+1 on this matrix. Can those conditions eliminate a
favorable two-cycle with two attached players, or reduce it to a full
inverse with uniformly signed columns?

Both proposed reductions fail on the exact matrix below. This is a
source-class obstruction only, not a positive-gap quitting game or a new
existence theorem. All forty-four nonsingleton reward coordinates remain
free at this stage. A new producer must still use their actual values.

The named original-game source declarations inspected are
`isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`,
`isR0Matrix_quittingSingletonMatrix_of_normal_of_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Classification/LCP/PunishmentNormalR0.lean`,
and `singleton_r0Degree_eq_one_of_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`.
For Fin4 the full-normal-core elimination and
`all_punishmentNormal_of_normalCore_eq_univ`
in `UniformEquilibrium/Quitting/Classification/LCP/NormalCorePunishmentNormal.lean`
supply the normality required by the R₀ declaration. None of these says
that the singleton matrix alone decides every reward completion.

## Exact two-cycle-plus-tails source

Take

    Γ = [[0,1,−2,−1],
         [1,0,−1,−2],
         [3/2,−1,0,−1/2],
         [−1,3/2,−1/2,0]].

Its favorable map is f(0)=1, f(1)=0, f(2)=0, f(3)=1. Thus it has
one two-cycle with two attached leaves, rather than a matching, four-cycle,
or three-cycle with one leaf. The determinant is2 and the full inverse is

    Γ⁻¹ = [[−1/8,−3/8,7/4,5/4],
           [−3/8,−1/8,5/4,7/4],
           [−7/8,3/8,1/4,3/4],
           [3/8,−7/8,3/4,1/4]].

The first two columns each contain both positive and negative entries.
No diagonal column-sign change makes Γ⁻¹ entrywise positive. Positive
playerwise payoff scales and player permutations do not change this fact.

In pair order01,02,03,12,13,23 the principal determinants are
−1,3,−1,−1,3,−1/4. In triple order012,013,023,123 they are
1/2,1/2,−1/4,−1/4. Thus every principal submatrix of size at least
two is nonsingular. Every column also has a negative off-diagonal entry.
A nonzero homogeneous complementarity root cannot have singleton support,
because of that negative entry, nor larger support, because it would solve
a nonsingular principal homogeneous system. Consequently Γ is R₀.

At complementarity offset −1, the positive favorite entries force z₀,z₁>0.
Their equalities give

    z₀=1+z₂+2z₃,       z₁=1+2z₂+z₃.

The remaining residuals are exactly

    w₂=−1/2−z₂/2+3z₃/2,
    w₃=−1/2+3z₂/2−z₃/2.

If z₂=0 and z₃=0, both residuals are negative. If only one is positive,
its own active residual is strictly negative. Hence both are positive,
and their equalities force z₂=z₃=1/2. Therefore the sole root is

    z=(5/2,5/2,1/2,1/2),       w=0.

It has full support and regular Jacobian determinant2>0. The exact finite
regular-root degree formula gives R₀ degree+1. Nonzero degree then implies
standard Q at every offset, not merely solvability of the one tested offset.

The declarations used for this final implication are
`exists_finset_r0Degree_eq_sum_sign_det`
in `MathUE/LinearProgramming/R0DegreeSum.lean` and
`isStandardQ_of_r0Degree_ne_zero`
in `MathUE/LinearProgramming/R0Degree.lean`.
They were inspected read-only; the displayed arithmetic and source reasoning
have not been formalized or built in Lean here.

## What fails and what remains

The exact failed implication is: a one-positive-per-row, R₀, degree+1
singleton matrix must have a favorable graph consisting of a matching,
a four-cycle, or a three-cycle with a leaf. The present matrix has none
of those graph types. The stronger hope that every surviving graph has
a positive inverse after independent column-sign changes is false too.

Eliminating the two forced core coordinates at offset −1 yields the
two-dimensional matrix

    S=[[-1/2,3/2],[3/2,−1/2]],
    S⁻¹=[[1/4,3/4],[3/4,1/4]].

This is an algebraic complementarity reduction, not a reduction of the
original game's players or information. It does not transfer arbitrary
coalition rewards, caps, or independent stopping laws. Treating it as a
strategic quotient without those inputs would repeat a supplied-interface
shortcut. In particular the actual reward table need have no symmetry.

The next raw question fixes this Γ and arbitrary signed own singleton
levels, but retains every nonsingleton coordinate. Can an actual producer
use the two-core Schur structure while choosing all four independent laws
and all unilateral caps, on a completion class not already consumed by a
known criterion? The current calculation supplies no strategy and no
claim of such coverage. No constants are being optimized.
