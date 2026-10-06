# All-player approximate independent clocks

Identity: CODEX_KREIN. Ordinary mathematics, not Lean-checked.

Current status: the first calculation below is an exact source reduction,
not a new existence class beyond the union of the accepted larger-root
producer and the existing no-UE matrix consequences. It shows that the
larger-root numerical gates are automatic on the no-UE residual whenever
the entire strict singleton sign pattern is present. Thus optimizing
those gates cannot enlarge the surviving counterexample class. The next
question is a construction with genuine simultaneous phases on the other
singleton sign configurations, while controlling all four full caps.

## A full-support test offset forces the larger-root gates

Let I={0,1,2,3}, with all indices cyclic, and let an actual quitting
reward table have singleton comparison matrix

    Γ = [ 0    −b₀   g₀    h₀ ]
        [ h₁    0   −b₁    g₁ ]
        [ g₂    h₂   0    −b₂ ]
        [−b₃    g₃   h₃    0  ],

where all b_i,h_i>0 and g₀,g₂<0<g₁,g₃. Own singleton levels and
all nonsingleton rewards are arbitrary. Put

    D=h₂(h₀b₁+g₀g₁)/(b₀b₁b₂).

**Claim.** If this Γ is R₀ with degree one, then D>1 and det Γ>0.
In particular a hypothetical Fin4 no-UE table with this sign pattern
automatically satisfies both numerical assumptions of the larger-root
four-clock producer.

### Exact original-data source

The inspected declaration
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`, in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`,
supplies full R₀ and degree one from nonexistence of an original-game
uniform payoff, with no singleton-sign or punishment-normality input.
The definition `quittingSingletonMatrix`, in
`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`,
is exactly Γ_ij=r_i({j})−r_i({i}).

The declaration `isStandardQ_of_r0Degree_ne_zero`, in
`MathUE/LinearProgramming/R0Degree.lean`, makes such a matrix standard Q.
Equivalently, the separate direct source
`isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`, in
`UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`,
supplies the same Q fact. The definition of `quittingProjectiveLCPMatrix`
in `UniformEquilibrium/Quitting/Projective/SingletonLCP.lean` is the same
receiver-row singleton difference; no transpose or reward normalization
is involved. Only the first, degree-based route is needed below.

### Every solution of one test problem has full support

Use standard LCP convention z≥0, w=q+Γz≥0, z_iw_i=0, and the fixed
offset q=(−1,0,−1,0). Standard Q supplies at least one solution.
The inequalities w₀≥0 and w₂≥0 imply respectively z₃>0 and z₁>0,
because their rows have no other positive coefficient. Hence w₁=w₃=0.
The two resulting equations are

    b₁z₂=h₁z₀+g₁z₃,
    b₃z₀=g₃z₁+h₃z₂.

Their strictly positive coefficients imply z₂>0 and z₀>0. Thus every
solution is fully supported and Γz=(1,0,1,0).

The matrix is nonsingular. Otherwise take a nonzero kernel vector v.
Starting from the positive solution z, move along the line z+t v until
the first coordinate reaches zero, keeping all coordinates nonnegative.
This is possible in one of the two directions because v≠0 and I is
finite. The residual remains identically zero, so the boundary vector
is another LCP solution. That contradicts the just-proved full-support
property. Consequently the test problem has exactly one solution and
its full principal determinant is nonzero.

The degree formula
`exists_finset_r0Degree_eq_sum_sign_det`, in
`MathUE/LinearProgramming/R0DegreeSum.lean`, applies: its inactive strict
residual condition is vacuous and its active nonsingularity condition is
the determinant conclusion above. Therefore

    1=degree Γ=sign(det Γ),

and det Γ>0. This uses the actual full ambient support, not a chosen
subcollection of auxiliary roots.

### The same root forces D>1

Substitute z₂=(h₁z₀+g₁z₃)/b₁ in the zeroth equation Γz=(1,0,1,0):

    −b₀z₁+(h₀+g₀g₁/b₁)z₃+(g₀h₁/b₁)z₀=1.

Multiply this equality by h₂ and add b₀ times the second-coordinate
equation g₂z₀+h₂z₁−b₂z₃=1. The result is

    [h₂(h₀+g₀g₁/b₁)−b₀b₂]z₃
       +[h₂g₀h₁/b₁+b₀g₂]z₀=h₂+b₀.

The second bracket is strictly negative, while z₀,z₃>0 and the right
side is positive. The first bracket is therefore strictly positive.
Dividing by b₀b₂>0 gives D>1, as claimed.

## Consequence and its precise coverage status

The strict sign pattern alone implies original-game UE: if no UE existed,
the source just described would give R₀ and degree one; the claim would
give D>1 and det Γ>0; then the complete larger-root producer would
construct an original-game uniform payoff, a contradiction. Its fixed
target and unrestricted behavioral proof are preserved in
[`LARGER_EIGENVALUE_SIGNED_FOUR_CYCLE_UNIFORM_PAYOFF.md`](../exports/LARGER_EIGENVALUE_SIGNED_FOUR_CYCLE_UNIFORM_PAYOFF.md).

This conclusion has no missing strategic input. Nevertheless it does not
establish coverage beyond the union of the accepted producer and the
existing matrix exit criteria: its numerical complement is already
excluded by those criteria. It is retained here as a source-conditioned
classification and a reason not to optimize the larger-root gates.
No new export is proposed for this algebraic consolidation.

The proof also gives an exact falsifier of the speculation that the
larger-root D condition could fail on the degree-one/Q part of this sign
chamber: the actual test root forces the strict inequality. No numerical
root selection is being used to claim that implication.

## Next independent-law question

A universal construction cannot use deterministic at-most-one-owner
calendars, even with infinitely many dates and accuracy-dependent hazards.
The inspected
`SolanVieilleBoundary.SoloHazardLedger.Schedule.one_over_sixtyEight_lt_literal_exploitability`,
in `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardSemantic.lean`,
gives that obstruction for its exact boundary table. The reward definition
in `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`
has each own singleton 1, partner singleton 4, and the two opposite-pair
singletons 0. In particular every comparison row has two negative and
one positive off-diagonal entries, unlike the mixed row counts in the
sign pattern above. Its no-solo result does not prohibit genuine
simultaneous phases or approximate independent laws in general.

The live question is to combine retained joint phases with refinable
solo arcs on the remaining sign configurations, selecting all four
players' laws together and controlling each player's deleted-opponent
tail on those same laws. A proposed complete mechanism must retain the
actual nonsingleton rewards in its joint-phase Quit caps and produce a
target before the accuracy parameter. No such general producer is
asserted in this note.
