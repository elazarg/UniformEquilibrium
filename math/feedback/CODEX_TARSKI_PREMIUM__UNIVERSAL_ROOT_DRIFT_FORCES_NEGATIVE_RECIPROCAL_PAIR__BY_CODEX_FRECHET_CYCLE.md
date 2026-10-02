# Independent review: universal root drift and reciprocal singleton signs

Reviewer: CODEX_FRECHET_CYCLE.

Reviewed source:
[TARSKI's checkpoint](../notes/CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR.md),
SHA256 `5266a7c40cbc5a2699db96c8523be5e6a87dc801ad113e243fece6a3c8192662`.
The author kept these bytes stable during review. No other review was read.
The current repository head inspected was `33552e5`.

## Verdict

The C¹ exact-root theorem is sound ordinary mathematics: a universal
positive-absorption drift potential forces a nonnegative vector with
strictly negative singleton quadratic energy, hence a negative reciprocal
pair. The boundary minimization, exact root eligibility, upper-face signs,
and transpose convention all check.

The stated normal-Fin4 semantic corollary is TRUE, but its claimed new
raw-table coverage is SUBSUMED. The CURRENT checked unconditional
projective-Q-bar Snell consumer already solves every finite quitting table
whose normalized singleton matrix is copositive. For zero diagonal this
includes exactly the candidate's pairwise reciprocal-nonnegative condition.
It does not need normality or a positive singleton as extra assumptions.

This is a substantive source-correspondence correction to Section 5, not
a counterexample to Sections 1–3. No new UE-class export should be based
on this corollary. The standalone C¹ obstruction remains a mathematical
diagnostic, not a producer for the remaining mixed-sign branch.

## 1. Exact theorem and independent proof reconstruction

Let a finite nonempty player set have bounded terminal rewards, singleton
vector s, Γ_ij=r_i({j})−s_i, and padded box K=[−B,B]^I with B>M.
Assume H is C¹ near K and decreases by at least the absorption mass on
EVERY exact root Nash edge at EVERY annotation v∈K. The annotation need
not be strategically feasible. Successors belong to K by convexity of
the box and the reward bound.

At x_i=s_i, x_j>s_j for j≠i, let only i Quit with small hazard t.
Owner i is exactly indifferent. A nonowner j's Quit-minus-Continue gap is

    (1−t)(s_j−x_j)+t[r_j({i,j})−r_j({i})].

Its first term is strictly negative and its second is bounded, so a common
sufficiently small positive t makes every nonowner prefer Continue. Thus
the tested root is EXACT Nash. Dividing the asserted drift by t gives
∇H(x)·(x−r({i}))≥1. At a weak intersection, perturb nonowner coordinates
toward B and pass to the limit in the gradient. This uses a potentially
different small t for each perturbation; no false uniform eligibility at
the intersecting face is assumed. Upper coordinates already equal to B
are allowed, since the root successor segment stays in K.

Now minimize H on the compact lower boundary L of ∏[s_i,B]. If precisely
one coordinate i is pinned, its eligible small solo root has successor
inside L, contradicting strict charged decrease and minimality. Hence the
set J of pinned coordinates has at least two members. For j∈J, a small
increase preserves another pin, giving ∂_jH≥0. Nonpinned interior
coordinates have zero derivative. A nonpinned upper coordinate has
∂_jH≤0, since decreasing that coordinate remains feasible in L.

For every i∈J, the face inequality therefore implies

    Σ_(j∈J) ∂_jH(x)[s_j−r_j({i})]≥1.

Indeed the omitted upper-face terms are nonpositive, because they are
∂_jH(x)[B−r_j({i})], and the other omitted terms are zero. Set ρ equal
to the active derivatives on J and zero elsewhere. Then ρ≥0 and ρ≠0.
The displayed inequalities read (Γᵀρ)_i≤−1 for i∈J. Multiplication
by ρ_i and summation gives

    −ρᵀΓρ≥Σ_iρ_i>0.

There is no transpose error: the double sum can equally be written with
Γ or Γᵀ inside this scalar quadratic form. Since Γ has zero diagonal,

    ρᵀΓρ=Σ_(i<j)ρ_iρ_j(Γ_ij+Γ_ji).

Negativity forces a pair with both weights positive and strictly negative
reciprocal sum. All one-sided boundary terms have been retained. Neither
convexity of H, an interior critical point, root uniqueness, nor semantic
minimum data enters this argument.

## 2. Actual polynomial consumer: logically correct, but not new coverage

I inspected the exact declaration
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.
Its hypotheses are indeed Fin4, a coordinate reward bound, actual
punishment normality for all players, and a positive own singleton. Its
no-uniform implication constructs the rational polynomial; it is not an
assumed separator or conditional capacity producer.

I also inspected `IsQuittingFloorFreeRobustEdge`,
`QuittingRobustChargedEdge`, and `quittingFloorFreeRobustChargedRelation`
in `Projective/RobustChargedRelation.lean`, and `IsPotential` in
`MathUE/ChargedPathBudget.lean`. An exact Nash root with its exact successor
has zero residual and zero regret, so it is admissible at every positive
tolerance. The edge charge is exactly its absorption mass, and the
potential direction is target potential plus charge at most source
potential. Thus the constructed polynomial satisfies the manuscript's
exact-edge assumption and is globally C¹. There is no hidden floor,
repeatable sure root, actual-payoff annotation, or selected-root exception.

Consequently the manuscript's contradiction under reciprocal-nonnegative
Γ is logically valid. The sure-root alternative is correctly handled by
the existing semantic equivalence, not repeated against its own output.

## 3. Complete existing-class composition

The narrower audit that stopped at the copositive-to-standard-Q theorem
missed the current strategic consumer. Here is the complete composition.

1. **Every principal is copositive.** If M is copositive and A is a
   nonempty player subset, extend any nonnegative vector on A by zero
   off A. Its quadratic form for M equals that for the principal M_A.
   Hence M_A is copositive. In the present zero-diagonal setting this
   also follows directly from the nonnegative reciprocal-pair sums.

2. **Every copositive principal is projective Q.** Split on whether M_A
   has a homogeneous simplex solution. If it does, use
   `isProjectiveQMatrix_iff_standard_or_homogeneous` in
   `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.
   If it does not, use
   `isR0Matrix_iff_not_singletonLCPFeasible` in
   `MathUE/LinearProgramming/CopositiveQ.lean` to obtain R₀. Then
   `copositive_isR0Matrix_isStandardQ` in that same file gives standard Q.
   The exact production bridge is `isStandardQ_iff_isStandardQMatrix`,
   or directly `isStandardQMatrix_of_copositive_of_isR0Matrix`, in
   `UniformEquilibrium/Quitting/Classification/LCP/CopositiveQBridge.lean`.
   The same projective-Q convention split now finishes this branch too.
   `HasHomogeneousSimplexSolution` is literally an abbreviation for
   `SingletonLCPFeasible`; there is no sign or normalization conversion.

3. **Hence M is projective Q-bar.** The inspected definition
   `IsProjectiveQBarMatrix` in `LCP/MatrixClasses.lean` says exactly
   projective Q on EVERY nonempty principal submatrix. It is not standard
   completely-Q, which would incorrectly exclude homogeneous principals.

4. **The strategic consumer is currently unconditional.** Apply
   `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
   `UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`.
   Its only mathematical premise is
   `IsProjectiveQBarMatrix (normalizedSoloMatrix reward)`. It concludes
   an ordinary uniform-equilibrium payoff for the actual finite quitting
   game, with unrestricted behavioral deviations. It does not assume a
   separate path producer, all-player normality, or positive singleton.
   Its neighboring punishment-normal principal version is likewise now
   unconditional; the ambient version already suffices here.

The candidate's Γ is exactly `normalizedSoloMatrix reward`, by its
definition and `normalizedSoloMatrix_eq_projectiveLCPMatrix` in
`LCP/Normalization.lean`. It is also exactly
`quittingSingletonSoloEffect` in `Classification/SingletonPacketEnergy.lean`.
No terminal affine shift is performed in this argument.

The older `punishmentNormalResidualHardClass_of_producer_of_not_exists_uniformEquilibriumPayoff`
in `LCP/NormalPrincipalQBar.lean` explicitly takes a strategic producer
as a premise. Reading only that older conditional interface would miss
the current result in the Snell file. The inspected
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
in `Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
already invokes the unconditional Snell consumer to exclude full
projective Q-bar from every same-table counterexample residual.

Therefore this copositive class is fully covered by current named
production facts, regardless of whether its six-pair special-case wrapper
has a dedicated declaration name. The candidate's proposed negative-pair
restriction on normal Fin4 counterexamples follows from that existing
coverage. Combined with the checked reciprocal-NONPOSITIVE class, the
mixed-positive/negative necessary condition is also not new coverage.

## 4. Boundary and falsification checks

- At an intersecting singleton face, a solo root can fail Nash because
  another indifferent owner prefers to join. The manuscript does not use
  it there: it proves the gradient inequality by approach from strict
  coordinates. This is essential and correct.
- At an upper box face, the derivative need not vanish. Its actual sign
  is nonpositive and its factor B−r_j({i}) is positive. The proof drops
  a NONPOSITIVE contribution, yielding the stated lower bound rather
  than reversing it.
- With one player, the singleton annotation and an absorbing own root
  give a charged self-loop, so no H exists. The singleton-boundary
  argument reaches exactly this impossibility; no distinct pair is
  manufactured in that vacuous case.
- Negative reciprocal energy is only necessary. For two players take
  singleton rewards (0,−1), (−1,0), and pair reward (0,0). Then Γ has
  both off-diagonals −1. At annotation (0,0), both players quitting
  surely is exact root Nash and returns (0,0) with charge 1. Hence no
  universal H exists despite the negative pair. This is a fully specified
  finite root test, not a negative equilibrium example.
- Direct substitution in `ThreeOwnerRobustCycle.reward` yields the
  displayed Γ and reciprocal sums 1 on core pairs and 0 on outsider
  pairs. Its named checked UE theorem is indeed a regression only.
  The displayed signed four-cycle vector ρ=(1,0,1,0) has energy −2,
  so that test is also arithmetically correct and only necessary.

I reread HILBERT's singleton-face note and the earlier convex-potential
exclusion. The new boundary-gradient argument removes the convexity
assumption at the price of a negative-energy conclusion, which those
limited local/convex arguments did not supply. Its source-independent C¹
statement should be retained honestly on that basis, separately from the
already solved copositive semantic class.

No author note, export, Lean source, or shared index was changed. The
author and coordinator were notified of the exact subsumption chain
before this review was completed. The next live work is mixed-sign
root/cap geometry, not polishing an already covered UE-class wrapper.
