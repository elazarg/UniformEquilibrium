# Scope of quadratic and multi-affine potential exclusions

Identity: CODEX_BERNSTEIN_REFLECTION.

Status: independent ordinary-mathematical review complete for
[the submitted reflection note](../gpt/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md).
Its proofs are sound in the normalized nonnegative-singleton setting.
[The associated feedback](../feedback/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS__BY_CODEX_BERNSTEIN_REFLECTION.md)
requests an explicit repetition of that setting in the semantic corollary.
No Lean compilation, source edit, export, or commit is part of this review.

## Exact question and answer

Given n≥2 players, terminal rewards |r_i(S)|≤1, own singletons s≥0,
zero live/Never reward, and independent root hazards q_i∈[0,1], can a
quadratic or multi-affine P satisfy

    P(v)−P(F(v,q))≥A(q)

for every v∈K=[−3,3]^n and every exact Nash root against v, where
F(v,q)=Pr(all Continue)v+Σ_(S≠∅)Pr(S)r(S) and A(q)=1−Pr(all Continue)?

No. Exact root Nash controls a one-stage unilateral action with a fixed
continuation annotation. The annotation need not be realized by a behavioral
profile. The relation quantifies over all such annotations and roots; it
does not choose an orbit, permit correlation, or replace unrestricted
behavioral deviations by root deviations in a semantic conclusion.

The two independent arguments are complete: reflection of a boundary
minimum in a rectangle depending on a global K-minimum excludes arbitrary
quadratics; strict corner-cost comparison excludes all multi-affine
polynomials. The adaptive rectangle is what removes the positive-diagonal
gap left by the prior quadratic reflection. The rational robust rejection
and C¹ monotone scalar-transform corollaries are valid as stated.

## Concrete functional separation

The quadratic

    Q(z)=z₀²+2z₀z₁−z₁²+z₂²+2z₂z₃−z₃²

has positive diagonal entries and indefinite Hessian. On [0,2]^4 its values
at (1,1,1,1)±h e₁ are Q(1,1,1,1)−h², so it is not quasiconvex.
It is not playerwise additive. It is not even a C¹ scalar composition of
C¹ playerwise summands on that box: wherever its first two partials are
nonzero, such a representation forces ∂₀Q/∂₁Q=f₀′(z₀)/f₁′(z₁).
But the actual ratio is (z₀+z₁)/(z₀−z₁). At z₀∈{1,2} and
z₁∈{1/4,1/2}, its two opposite-corner products are 25/9 and 27/7,
which differ. This is a literal class-separation test, not a proposed
certificate passing the other necessary conditions. Cubic and quartic
multi-affine polynomials also lie beyond the quadratic-only exclusion.

The existing reset-rank result uses a different domain, [−R,R]^4×[−R,R]^4,
and monotonicity under every semantic prefix. Its arbitrary-quadratic
conclusion cannot be transferred to the present payoff-only root relation.

## Exact semantic and normalization scope

For Fin 4 with |r|≤1, every s_i≥0, all-player punishment normality, and
some s_i>0, let E_τ be the full robust relation on K: both endpoint boxes,
root regrets at the source ≤τA, and Bellman residual ≤τA. The inspected
polynomial characterization, used with bound one, gives exactly

    ¬UE(r) ↔ no punishment-vector sure Nash root and
      ∃ rational τ∈(0,1/4], ∃ rational polynomial P,
        P has unit-charge drift on E_τ,
        totalDegree(P)≥3, and P is not multi-affine.

The forward implication keeps the polynomial produced by the existing
theorem and applies the exclusions; the reverse implication forgets the
shape conditions. Its polynomial also obeys the reviewed radial and third-
derivative restrictions. No extra strategic witness remains to be produced
for this reduction.

The original characterization itself allows signed singleton coordinates.
Positive common scaling cannot change their signs. For a supplied game
with s≥0 choose a positive rational λ with λ|r_i(S)|≤1. Every finite-horizon
and terminal payoff, deviation gain, and punishment value scales by λ;
zero live/Never reward remains zero. Hence uniform-payoff existence and
normality are preserved. Invoke the characterization afresh on λr at
bound one. The transformed singleton need only remain positive, not one.
No fixed-box certificate transport follows from this observation.

There is an existing stronger decision-level bridge:
`exists_finFour_no_uniformPayoff_iff_exists_singlePivot`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`)
states that existence of any Fin4 counterexample is equivalent to existence
of a canonical single-pivot counterexample. Its forward producer
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` outputs that
literal normalized table, singleton vector, normality, and nonexistence of
a uniform payoff. This relies on actual semantic transport machinery; it
is not inferred from an affine chart definition. A fresh common scaling
then reaches the reviewed normalized class. Neither this bridge nor the
new exclusions claims a coefficient-degree bound or closes the conjecture.

## Inspected exact sources

The bounded route was `docs/TOOLKIT.md`'s robust polynomial characterization,
with `docs/FRONTIER.md`'s single-pivot normalization entry used only for the
normalization question. Source inspection was at repository head
`5aac30ad2553dadd5895dc79fbc4f1f5680d7570`; no new build is asserted.

- `IsQuittingFloorFreeRobustEdge`, `quittingRobustChargedEdgeResidual`,
  `quittingRobustChargedEdgeRegret`, `quittingFloorFreeRobustChargedRelation`
  (`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`).
- `ChargedRelation.IsPotential` (`MathUE/ChargedPathBudget.lean`).
- `quittingRootSuccessorPayoff`, `quittingRootQuitPayoff`,
  `quittingRootContinuePayoff`, `IsεQuittingRootEndpointNash`
  (`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`), and
  `quittingRootCoordinateNashDefect`
  (`UniformEquilibrium/Quitting/Root/NashDefect.lean`).
- `exists_isZeroQuittingRootNash`
  (`UniformEquilibrium/Quitting/Root/NashExistence.lean`), whose import is
  `UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed`.
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  (`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`),
  importing the robust separator, finite-capacity producer, and converse
  polynomial consumer.
- `IsQuittingNormalPlayer`
  (`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`).
- `quittingSoloReward_singlePivotNormalized`,
  `abs_quittingSinglePivotNormalizedReward_le`
  (`UniformEquilibrium/Quitting/Root/SinglePivotNormalization.lean`);
  `quittingPlayerwiseUnitNormalization_singleton`
  (`UniformEquilibrium/Quitting/Root/PlayerwiseUnitNormalization.lean`);
  `singlePivotNormalized_standardQ_iff`
  (`UniformEquilibrium/Quitting/Classification/LCP/SinglePivotNormalizationTransport.lean`).
  These chart/matrix facts alone are not a semantic normalization proof.
- `isεAsymptoticNash_playerwiseScale`,
  `IsεAsymptoticNash.of_nonnegative_terminalShift`
  (`UniformEquilibrium/Quitting/Terminal/TerminalAffineNashTransfer.lean`);
  `quittingPunishmentValue_singlePivotNormalized`
  (`UniformEquilibrium/Quitting/Punishment/SinglePivotPunishment.lean`);
  `uniformEquilibriumPayoffSet_singlePivotNormalized`
  (`UniformEquilibrium/Quitting/Punishment/SinglePivotUniformPayoff.lean`);
  both normalization declarations cited in the preceding section.

The complete existing shape export and relevant portions of both FRECHET
notes were compared. Narrow searches in the Projective and MathUE/Interval
subtrees found no corresponding all-quadratic/all-multi-affine exclusion.
This is a bounded implementation-overlap finding. No literature-derived
claim or publication-priority claim is made.

## Input integrity and verification

Original SHA-256 values, recorded before review-file edits:

| Input | SHA-256 |
| --- | --- |
| `gpt/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md` | `809b1eded85f5f6153fdad74984e432ebc1f53fb997f86101d5bb644d3e36028` |
| `gpt/VERIFY_REFLECTION_AND_MULTIAFFINE_EXCLUSIONS.py` | `93d4559d7613b32b461825be2872b0c9abfa1bdfae9b9d76a3a8e602dd9c0962` |
| `exports/QUITTING_POTENTIAL_SHAPE_EXCLUSIONS.md` | `9dcc9d37b444a5c65e4b301aed41082f52cc9e74a3caa7f27a20e5f51cab4e6b` |
| `notes/CODEX_FRECHET_CYCLE__NONPOSITIVE_DIAGONAL_QUADRATIC_ROOT_DRIFT_EXCLUSION.md` | `a96984e9d52edd13dbc6d6a4d237193f31ec80ba498b8d4b1caf81c0b44486bc` |
| `notes/CODEX_FRECHET_CYCLE__QUADRATIC_FULL_BOX_BARRIER_RESET_RANK_TEST.md` | `668368fc2ee6aa3f4a6a41342ef626bc81302e9942e9d04c1acbd403c4e35b40` |

`python gpt/VERIFY_REFLECTION_AND_MULTIAFFINE_EXCLUSIONS.py` passes: 160
reflection identities, 201 box cases, 36 multi-affine derivative cases,
120 collision-adjusted exact probes, 11 kernel monomials, and the paired
fixture's four face identities and exact spectrum. These are finite
regressions, independent of the universal proof verdict.

Next requested check: restate the semantic corollary with bound one and
every own singleton nonnegative explicitly; retain the fixed-box warning.
The mathematical question still open is whether any coupled polynomial
with repeated-coordinate terms and total degree at least three can satisfy
the full robust relation in the remaining conjecture class.
