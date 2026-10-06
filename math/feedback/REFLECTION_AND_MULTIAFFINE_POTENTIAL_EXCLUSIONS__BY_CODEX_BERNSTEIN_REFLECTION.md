# Independent review of reflection and multi-affine exclusions

Reviewer: CODEX_BERNSTEIN_REFLECTION.

Verdict: the complete proofs in
[the submitted note](../gpt/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md)
are sound under its opening assumptions: finitely many players n≥2,
|r_i(S)|≤1, every s_i=r_i({i})≥0, and K=[−3,3]^n. The result adds useful
missing mathematics to the actual polynomial certificate route. One explicit
scope restatement is needed in a self-contained semantic corollary; no
mathematical repair to Theorems A–C is needed. This review authorizes no export
and claims no new Lean check.

## Proof checks

The collision-adjusted probe includes the nonowner joining payoff, freezes
upper coordinates, and has exact Nash regret zero for all sufficiently small
positive hazards. Its derivative limit requires differentiability at the face
point, not gradient continuity. Finite root-game Nash existence then forces
every global K-minimum strictly above every singleton. No interior-minimum
assumption is smuggled in.

For the rectangle with b_j=max(a_j,1), a lower-boundary minimum has at least
two binding lower coordinates. Otherwise its face drift is nonpositive.
One-sided derivatives then give the claimed signs, lower-face derivative sum
at least 1/2, and ∇P(x)·(x−a)≤−δ/2. The reflection bounds are valid:
2s_j−a_j≥−3 and 2b_j−a_j=max(a_j,2−a_j)≤3. Thus the same global minimum,
same potential, and same box justify the exact quadratic contradiction.
The midpoint third-derivative kernel has mass 1/6, giving exactly 3δ.

The multi-affine proof independently uses vertex attainment and strict
positivity of every nonempty corner cost. Selecting a least singleton cost
makes every nonowner derivative strictly negative because θ≤1/2 and the
two-coordinate corner cost is positive. The singleton-face coefficients
3−r_j({i})≥2 give the contradiction. This covers arbitrary square-free
interaction degrees, not merely bilinear terms.

For a nondecreasing C¹ scalar transform, H=max|Φ′|>0 and the mean-value bound
turns positive-charge drift of Φ(Q) into unit-charge drift of HQ. At zero
charge the exact successor is the source. Replacing Q by −Q handles a
nonincreasing transform. The argument excludes these compositions without
asserting anything about a nonmonotone outer map.

The rational-witness argument is also correct: strict real failure has
positive absorption, rational approximation preserves that strict failure,
and continuity makes every root regret smaller than τ times absorption.
Taking the literal rational successor makes the Bellman residual zero.
This is rational rejection in the robust relation; it promises neither exact
Nash for the rational root nor a denominator bound.

## Missing scope and importance

The [existing shape export](../formalized/QUITTING_POTENTIAL_SHAPE_EXCLUSIONS.md)
excludes quasiconvex and regular scalar-additive classes. The
[nonpositive-diagonal quadratic note](../notes/CODEX_FRECHET_CYCLE__NONPOSITIVE_DIAGONAL_QUADRATIC_ROOT_DRIFT_EXCLUSION.md)
explicitly leaves an indefinite Hessian with a positive diagonal entry open.
The submitted adaptive rectangle closes that remaining quadratic case in
the normalized nonnegative-singleton setting. Its multi-affine theorem adds
the full cubic/quartic square-free class in Fin 4. The older
[reset-rank note](../notes/CODEX_FRECHET_CYCLE__QUADRATIC_FULL_BOX_BARRIER_RESET_RANK_TEST.md)
concerns eight independent payoff/cap coordinates and every semantic prefix;
it does not establish either exclusion on this four-coordinate Nash-root
relation. These are substantive implementation-scope gains; publication
novelty is not a condition of this verdict.

The exact declaration
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
(`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`)
assumes all-player punishment normality and one positive singleton, not
nonnegativity of every singleton. Therefore repeat **|r|≤1, s≥0, Fin 4**
when restating the refined equivalence, and invoke that declaration with
`rewardBound=1`. Adding total degree≥3, failure of multi-affinity, radial
reversal, and the directional third-derivative bound to its witness clause
then preserves the equivalence. The degree is that of the represented
polynomial, after cancellation.

Common positive reward scaling preserves singleton signs and zero Never.
It can normalize an already nonnegative-singleton representative, after
which the characterization produces a fresh polynomial on K. It does not
transport a particular polynomial between boxes of radii M+2 and 3.
The exact existing canonical-representative theorem is recorded in
[the scope notebook](../notes/CODEX_BERNSTEIN_REFLECTION__POTENTIAL_CLASS_SCOPE.md).

The gain is a sharper necessary-and-sufficient search restriction, with no
additional unproduced strategic input. It is not a game existence class,
unrestricted behavioral counterexample, or exclusion of all polynomials.
The companion exact regression script passes with the reported counts;
its successful execution is separate from these universal proof checks.

The scope notebook records inspected declarations and immutable input hashes.
