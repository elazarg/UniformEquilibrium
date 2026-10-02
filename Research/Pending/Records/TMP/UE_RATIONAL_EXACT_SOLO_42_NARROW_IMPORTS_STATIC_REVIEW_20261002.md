Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Unit42 narrow-import overlay: static review

PASS, import-only. Inspected the full immutable `42_RATIONAL_EXACT_SOLO_REJECTION.patch`, both new direct owners, and the replaced aggregate owner. No signature or proof body changes occur.

Overlay: `/tmp/UE_RATIONAL_EXACT_SOLO_42_NARROW_PROBE_IMPORTS_20261002.patch`.
Verified SHA256: `f7c84c91ca9b485891fe6f9f99f58ab0fb4bb05b932e12fa5f92ba5b5993a4f3`.

The overlay replaces `UniformEquilibrium.Quitting.Projective.FullExactRootPotentialFaceDrift` with exactly:

- `MathUE.Analysis.CollisionAdjustedDrift`, the owner of `Math.tendsto_collisionAdjusted_potential_differenceQuotient` actually used by42;
- `UniformEquilibrium.Quitting.Root.CollisionAdjustedSingletonProbe`, the owner of the actual source/root/successor/correction expressions, the affine successor identity, and `exists_small_rates_quittingSingletonProbe` actually used by42.

The old aggregate imports those same two modules plus `ExactRootPotentialRestriction`. Unit42 does not call its `IsQuittingFullExactRootPotential.singletonFace_drift` theorem or its aggregate probe-quotient wrapper. Its face violation continues to come from the already explicit `SingletonBoxStandardQFaceExclusion` import and genuine face-only standard-Q exclusion, not a stronger full-root potential premise.

All rational closed-face, internally chosen owner/rate/source, exact Nash, absorption, literal solo probabilities, boxed successor, same-polynomial and strict drop conclusions remain byte-for-byte unchanged. No compiler or shared application was run here; any latent transitive-import elaboration issue remains for root's named check. No concrete missing declaration was found by this static dependency inspection.
