# Independent review: universal root drift and reciprocal singleton signs

Reviewer: CODEX_NOETHER_SUPPORT.

Verdict: the C¹ root theorem and the stated normal-Fin4 semantic implication
PASS. The proposed removal of normality and positive-singleton assumptions
from the Fin4 existence corollary is also valid. However, the raw
reciprocal-NONNEGATIVE class is ALREADY covered, for arbitrary finite player
sets, by a short composition of current copositive/projective-Q-bar sources.
The result must not be presented as new UE-class coverage.

Reviewed source:
[TARSKI's note](../notes/CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR.md),
all 264 lines through EOF, frozen SHA256
`5266a7c40cbc5a2699db96c8523be5e6a87dc801ad113e243fece6a3c8192662`.
No other review of this candidate was read. I independently found and
reported the projective-Q-bar composition before receiving the parent's
message that another reviewer had found the same overlap. No author or
export file was edited. This is mathematical source inspection, not a Lean
build or new formalization.

## 1. Exact theorem and independent reconstruction

For a finite nonempty player set, arbitrary bounded rewards, padded box
K=[−B,B]^I with B>M, and H continuously differentiable near K, assume

    H(v)−H(F(q,v))≥a(q)

for EVERY boxed annotation v and EVERY exact product-root Nash q at v.
The annotation need not be a feasible payoff or punishment vector. The
accepted conclusion is a nonzero ρ≥0 with ρᵀΓρ<0, where
Γ_ij=r_i({j})−s_i and Γ_ii=0. Thus some reciprocal sum is negative.

### Eligible edges and their boundary limit

At x_i=s_i and x_j>s_j for j≠i, a root in which only i Quits with
probability t makes i indifferent. The exact nonowner Quit advantage is

    (1−t)(s_j−x_j)+t[r_j({i,j})−r_j({i})].

It is negative for all sufficiently small positive t, simultaneously for
the finitely many nonowners. Thus the edge really is exact Nash, its charge
is t, and its successor is x+t(r({i})−x). Both endpoints remain in K,
including when a nonowner starts at B. Dividing the drift inequality by t
and taking t↓0 gives

    ∇H(x)·(x−r({i}))≥1.

For weak inequalities x_j≥s_j, moving the other coordinates toward B makes
all of them strict because B>s_j. Continuity of the gradient passes the
inequality to the limit. The proof correctly allows the eligible hazard
to depend on this approach point. It never claims a uniform solo-root
eligibility radius at intersecting singleton faces.

### The lower-boundary minimum and all gradient signs

The set L of points in ∏[s_i,B] with at least one lower-pinned coordinate
is nonempty and compact. Let x minimize H on L and J={i:x_i=s_i}.

If J={i}, the small eligible solo-i edge has successor still in L: its
i coordinate stays s_i and the other coordinates stay above their lower
faces for small t. It strictly decreases H, a contradiction. This includes
the one-player case without an omitted special hypothesis.

Consequently |J|≥2. A positive coordinate direction at j∈J remains in L
because another coordinate is pinned, so g_j≥0. A nonactive interior
coordinate has g_j=0. At a nonactive upper coordinate, the feasible negative
direction gives g_j≤0. These signs are all in the correct orientation.

For each i∈J, an upper coordinate contributes
g_j(B−r_j({i}))≤0 to the singleton-face inequality, while nonactive
interior coordinates contribute zero. Removing the nonpositive terms
therefore gives the STRONGER lower-active inequality

    Σ_(j∈J) g_j(s_j−r_j({i}))≥1,       i∈J.

Set ρ_j=g_j on J and zero elsewhere. Then ρ≥0 and ρ≠0. In matrix notation
the displayed component inequality is

    −(Γᵀρ)_i≥1,       i∈J.

Multiplying by ρ_i and summing gives

    −ρᵀΓᵀρ≥Σ_iρ_i>0.

The scalar ρᵀΓᵀρ equals ρᵀΓρ, so the manuscript's quadratic sign is
correct. Zero diagonal then gives

    ρᵀΓρ=Σ_(i<j)ρ_iρ_j(Γ_ij+Γ_ji).

A negative value forces a negative reciprocal pair with both weights
positive. No symmetry of Γ, convexity of H, common punishment realizer,
selected exact-root branch, or Hessian condition was used.

## 2. Exact robust-polynomial and unconditional Fin4 consumers

I read the complete declaration
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.
Its hypotheses are all-player punishment normality and a positive own
singleton, with a coordinate reward bound. Its no-UE side produces the
no-sure-root statement AND an actual rational polynomial potential on the
box of radius rewardBound+2, at positive rational tolerance.

The definitions in `Quitting/Projective/RobustChargedRelation.lean` impose
no hidden punishment floor: both endpoints are boxed, and both the Bellman
residual and root regret are bounded by tolerance times absorption. An
exact Nash root with target F has both errors zero, so it is a legitimate
edge at every positive tolerance. `ChargedRelation.IsPotential` in
`MathUE/ChargedPathBudget.lean` means target potential plus charge is at
most source potential, exactly the sign used in the note. Polynomial
evaluation is C¹ on the whole ambient space. Thus the root theorem really
contradicts the checked negative certificate; it is not merely a verifier
of a supplied actual terminal profile.

The proposed unconditional Fin4 strengthening is valid on the SAME table:

1. If all own singletons are nonpositive, all Never has zero prescribed
   payoff and every unilateral payoff is nonpositive. The exact production
   conclusion is `quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo`
   in `Quitting/Punishment/ZeroSoloDisjunct.lean`, also exported existentially
   as `exists_uniformEquilibriumPayoff_of_zeroSolo`.
2. Otherwise some singleton is positive. Under a supposition of no UE,
   `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
   in `Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
   supplies a residual with the field `all_punishmentNormal` at that very
   reward table. Its definition is the actual behavioral punishment bound
   P_i≤s_i, as checked in `Quitting/Classification/AbnormalPlayers.lean`.
3. The polynomial characterization therefore applies and gives the
   contradiction under reciprocal nonnegativity.

No reward normalization or change of table is involved in this removal.
No punishment infimum or full behavioral best-response supremum is assumed
attained. The sure-root clause is retained logically; no stationarily
repeated sure root is smuggled into the drift argument.

## 3. Decisive existing-class composition

The raw conclusion is not new class coverage. The following independent
source composition already proves it, without normality, a positive
singleton, or the Fin4 restriction.

For a zero-diagonal Γ, pairwise reciprocal nonnegativity is exactly
copositivity: the quadratic identity in Section1 is nonnegative on every
nonnegative vector. Every principal submatrix is also copositive, by
extending its vector by zero. Fix any nonempty principal A.

- If `SingletonLCPFeasible A` holds, it is precisely the homogeneous
  simplex alternative of the projective matrix convention.
- Otherwise `isR0Matrix_iff_not_singletonLCPFeasible` in
  `MathUE/LinearProgramming/CopositiveQ.lean` gives `IsR0Matrix A`.
  The checked theorem
  `isStandardQMatrix_of_copositive_of_isR0Matrix` in
  `Quitting/Classification/LCP/CopositiveQBridge.lean` then gives standard Q.
- In either case `isProjectiveQMatrix_iff_standard_or_homogeneous` in
  `Quitting/Classification/LCP/MatrixClasses.lean` gives projective Q for A.

Doing this for EVERY nonempty principal is exactly
`IsProjectiveQBarMatrix Γ`. The matrix definitions use receiver rows and
quitter columns, with NO transpose or sign change.
`normalizedSoloMatrix_eq_projectiveLCPMatrix` and the underlying definitions
in `Quitting/Classification/LCP/Normalization.lean` and
`Quitting/Projective/SingletonLCP.lean` identify this Γ with the production
normalized solo matrix.

Finally `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
`Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean` is an
unconditional actual uniform-payoff consumer for arbitrary finite player
types. It has no supplied decoder, normality, singleton-sign, or Fin4
hypothesis. This completes the prior-coverage proof.

The manuscript correctly observes that copositive-plus-R0 gives only
standard Q by itself, but stopping there misses the homogeneous alternative
on each principal and the current unconditional Q-bar consumer. No single
newly named `copositive_to_QBar` declaration is needed for this exact
composition. It also explains why the existing integral-tournament class
is only an example, not the full relevant coverage boundary.

The existing `exists_uniformEquilibriumPayoff_of_pairwise_reciprocalSolo_nonpos`
in `Quitting/Classification/SingletonPacketEnergy.lean` has the opposite
sign and does not itself subsume the new condition. Combining it with the
Q-bar composition already forces any hypothetical Fin4 counterexample to
have both a positive and a negative reciprocal pair. That necessary sign
mixture is therefore not new UE-class narrowing either.

## 4. Falsification and regression checks

- At an intersecting singleton face, a solo root need NOT be exact Nash.
  With s_2=x_2=0 and a join-minus-solo premium 1, its nonowner gain is t>0.
  At x_2=ε, the gain is t−(1−t)ε, and the root is eligible exactly when
  t≤ε/(1+ε). This verifies the need for the nonuniform approach used in
  Section2 of the candidate, rather than invalidating its limiting step.
- At an upper-box coordinate, the gradient is nonpositive, not zero or
  nonnegative. The candidate keeps its negative contribution with the
  correct sign before extracting the supported vector.
- The Γᵀ in the component inequality cannot be silently dropped. It
  disappears only after multiplication by the SAME vector on both sides
  of the scalar quadratic form; I checked that step explicitly.
- Direct integer evaluation of the production `ThreeOwnerRobustCycle.reward`
  gives exactly the displayed singleton vector and Γ matrix: core pair
  sums are 1 and the three pairs with owner 3 have sum 0.
- The displayed stress matrix has energy −2 at (1,0,1,0), as claimed.
  Passing the negative-pair test is not sufficient for a drift potential;
  its already solved status is therefore consistent.
- The all-zero reciprocal boundary, a singleton player set, tied lower
  coordinates, zero gradient coordinates, and upper-face minimizers do
  not expose a missing eligibility or positivity premise.

The core lower-boundary argument is a sound source-independent C¹
certificate obstruction. HILBERT's full singleton-face calculation and
FRECHET's all-anchor calculation were checked as mathematical inputs, not
as reviews; the present use of a lower-boundary minimizer is a different
direct derivation. Its strategic class consequence is nevertheless already
covered by the checked composition in Section3.

This bounded review is complete. No extended export gate or new class
packaging is recommended. A genuinely new continuation of this route must
consume matrices with mixed reciprocal signs or other still-uncovered
structure, not restate reciprocal nonnegativity as a new solved class.
