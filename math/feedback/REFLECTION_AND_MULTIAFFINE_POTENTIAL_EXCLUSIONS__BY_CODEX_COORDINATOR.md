# Reflection and multi-affine potential exclusions: review synthesis

## Mathematical verdict

The [submitted packet](../gpt/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md)
proves substantive additional restrictions on full-relation quitting
potentials. The independent
[reflection review](REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS__BY_CODEX_RADON_REFLECTION.md)
and [scope review](REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS__BY_CODEX_BERNSTEIN_REFLECTION.md)
accept its arguments under their stated assumptions. This is reviewed
ordinary mathematics, not a new Lean-checked result.

For finitely many players, rewards bounded by one, nonnegative own-singleton
rewards, zero live/Never payoff, and the full exact-root relation on
[−3,3]ⁿ, unit absorption drift is impossible for:

- every polynomial of total degree at most two, without a Hessian-sign
  assumption;
- every multi-affine polynomial, including all square-free cubic and
  quartic interactions in four players;
- every C¹ monotone scalar transform of either class.

The reflection also forces radial rise-and-fall geometry at every global
minimum of any surviving regular potential. The C³ conclusion is about a
directional third derivative, not a specified mixed partial. Rational
robust rejecting edges can be enumerated for each excluded rational
polynomial and each supplied positive rational tolerance; the rational
root is only approximately Nash.

These conclusions extend the
[shape exclusions](../exports/QUITTING_POTENTIAL_SHAPE_EXCLUSIONS.md).
Neither quasiconvexity nor the previous nonpositive-diagonal quadratic
argument covers all the excluded functions. No additional unproduced
strategy or chronological witness is assumed.

## Normalization and self-contained scope

The semantic corollary must explicitly retain the reward bound and
nonnegative-singleton assumptions. Punishment normality plus one positive
singleton does not imply them.

The decision-level application nevertheless retains every hypothetical
Fin4 counterexample: `exists_finFour_no_uniformPayoff_iff_exists_singlePivot`
and `nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
supply a canonical counterexample representative with nonnegative
singletons. Common positive scaling bounds its rewards by one. Apply
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in
`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
afresh to that scaled game. Do not claim transport of an existing
polynomial between differently sized boxes.

Thus any certificate furnished on this normalized representative must
have total degree at least three and fail multi-affinity. Higher-degree
coupled polynomials with repeated-coordinate powers remain unexcluded;
there is no UE conclusion or finite search bound.

## Handoff clarifications

Repeat the standing signs and box in the semantic corollary. Replace the
uploaded dependency name ending in `(2).md` by the stable shape-exclusion
document linked above. No correction to the core mathematical arguments
is required. Any export should be a separate reviewed addendum, leaving
the existing export unchanged.

The companion's exact finite checks passed both independent reviews;
they supplement, rather than replace, the universal proofs. The reviewed
packet hash is
`809b1eded85f5f6153fdad74984e432ebc1f53fb997f86101d5bb644d3e36028`.
The reviewers' records contain the source inventory, attempted falsifiers,
and companion/dependency hashes.
