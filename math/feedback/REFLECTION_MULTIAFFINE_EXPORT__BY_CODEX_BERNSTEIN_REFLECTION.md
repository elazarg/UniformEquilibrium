# Final independent gate: reflection and multi-affine exclusions

Reviewer: CODEX_BERNSTEIN_REFLECTION.

Decision: **accept** the complete mathematical packet at
[`notes/CODEX_ALEXANDROV_GATE__REFLECTION_MULTIAFFINE_EXPORT_PACKET.md`](../notes/CODEX_ALEXANDROV_GATE__REFLECTION_MULTIAFFINE_EXPORT_PACKET.md),
SHA-256
`4226de1af95adad10a1cd9b90049586195146e237b0d5811e675ca7618a61a2d`.
I read the complete frozen bytes and independently checked the arguments
and the exact source-to-conclusion chain. No mathematical objection remains.
This is approval as ordinary mathematical evidence for external
formalization, not a new Lean, adapter, or consumer seal.

## Mathematical correctness

The full statement retains finite n≥2, |r_j(S)|≤1, all own singleton
levels nonnegative, K=[−3,3]ᴵ, and every exact Nash root at every boxed
annotation. The collision correction includes each nonowner's simultaneous
joining reward and freezes upper coordinates. Its derivative limit needs
only differentiability. Finite Nash existence and compactness then put
every global minimum strictly above all singleton levels without asserting
that it is an interior point.

The adaptive rectangle contains that same minimum and dominates the
singleton reward columns. Its lower-boundary minimizer has at least two
binding coordinates, giving the required one-sided derivative signs and
radial reversal. The reflected point remains in the same original box;
the lower estimate uses the singleton signs and the upper estimate uses
b_j=max(a_j,1). The quadratic identity then contradicts global minimality
without any Hessian-sign restriction. The separately proved midpoint
integral identity has kernel mass 1/6 and yields exactly the directional
third-derivative bound 3δ.

The multi-affine proof preserves strict positivity of all nonempty vertex
costs. Choosing the smallest singleton cost makes every nonowner face
derivative strictly negative, including the endpoint θ=1/2. This excludes
all square-free degrees. The scalar-transform argument correctly obtains
unit drift for HQ by the mean-value theorem, covers zero-charge identity
edges, and handles decreasing transforms by replacing Q with −Q.

Rational rejection uses a strict real violating edge with positive
absorption, continuity, and rational density within the closed boxes.
The rational successor has zero Bellman residual. The root is only
robust-approximate Nash, exactly as stated; no exact rational root or
denominator bound is inferred.

## Semantic chain and strategic inputs

The semantic corollary explicitly repeats **Fin4, reward bound one, every
s_i≥0, and some s_i>0**. Its self-contained punishment definition agrees
with `quittingBestReplyValue` and `quittingPunishmentValue`
(`UniformEquilibrium/Quitting/Stationary/MinMax.lean`). The argument deriving
normality from s_i≥0 agrees with
`isQuittingNormalPlayer_of_singleton_nonneg`
(`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`).
Consequently normality need not be separately assumed in (PC).

I checked
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
(`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`)
and its converse in
`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateConsumer.lean`.
At bound one their box is exactly K. The forward theorem produces the
polynomial; the new restrictions apply to that witness. The reverse
implication simply forgets the restrictions. No polynomial or smooth
potential producer is added as a premise.

For arbitrary hypothetical Fin4 counterexamples,
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`)
produces the literal canonical table and its no-UE statement. Its output
singleton vector agrees with `IsSinglePivotSingletonTable`
(`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`).
The packet then proves common positive scaling directly for identical
behavioral histories, finite-horizon payoffs, terminal payoffs, deviations,
and punishment extrema. This agrees with
`quittingTerminalPayoff_playerwiseAffine`
(`UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean`) at zero
shift and `isεAsymptoticNash_playerwiseScale`
(`UniformEquilibrium/Quitting/Terminal/TerminalAffineNashTransfer.lean`).
It invokes the characterization afresh on the scaled game. No strategic
input is unproduced, and no arbitrary terminal translation or old fixed-box
certificate transport is inferred. Real rewards are not silently made
rational.

## Importance, falsification, and remaining gate

The packet provides a strict narrowing of an existing equivalent polynomial
obstruction, rather than a conditional strategy-construction interface.
It requires no exceptional conditional admission. The earlier quasiconvex
and regular scalar-additive exclusions do not cover these whole classes;
the prior nonpositive-diagonal quadratic note explicitly leaves positive
diagonal entries open. The eight-coordinate reset-rank result concerns a
different semantic relation. Bounded source searches found no implemented
equivalent exclusion; publication novelty is not required.

I checked the collision, boundary reflection, signed-singleton, and
multi-affine sign falsifiers, and reran the exact companion checker. All
reported counts and fixture values agree. The packet preserves the full
root-versus-behavior distinction, gives a concrete Lean handoff, and
claims neither all-polynomial exclusion nor resolution of the conjecture.

The reviewed draft hash and the original source/export hashes remained
unchanged. No Lean compilation was performed. This review supplies an
affirmative independent mathematical gate for the exact hash above; the
coordinator retains responsibility for final review-link and byte-integrity
checks before placing those same bytes in the export queue.
