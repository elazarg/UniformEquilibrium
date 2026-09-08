# Auxiliary discounted localization: available source construction

This formalizer feedback records the completed source construction needed
before the integer-LCP-degree argument. The generic constructions apply to
arbitrary finite player types; the four-player corollary below discharges
their R0 premise. They formalize the discounted
source argument; they do not construct an integer degree or prove the
remaining LCP criterion.

## Actual source and complete endpoint

`quittingDiscountedBellmanAssignment_of_hazard_fixedPoint`
(`UniformEquilibrium/Quitting/Bellman/Discounted/FixedPointLift.lean`)
lifts every supplied cube fixed point of the actual discounted clipped map
to a complete polynomial Bellman assignment. It retains the discount,
live hazards, actual quotient value, and absorbed-state rewards of the
same table. No fixed point is selected by this theorem.

`exists_analyticBellmanGerm_at_discountedFixedPoint_hazardCluster`
(`UniformEquilibrium/Quitting/Bellman/Discounted/ClusterCompletion.lean`)
starts from a supplied hazard cluster of actual positive-discount fixed
points. Compactness of their bounded values provides a compatible value
cluster along a nontrivial refinement of the same source filter. The
resulting analytic germ has exactly the complete limiting assignment as
its endpoint. Neither a value cluster nor a curve-selection theorem is
an additional input.

## Original-game consumer and quantifiers

`exists_uniformEquilibriumPayoff_of_auxiliaryDiscounted_hazardCluster`
(`UniformEquilibrium/Quitting/Classification/AuxiliaryDiscountedLocalization.lean`)
applies the construction to the canonical auxiliary reward table. If the
limiting root absorbs, the existing punishment-admissible-cycle consumer
gives a uniform-equilibrium payoff of the original game at the translated
compatible value limit. Its signed sole-quitter case is already handled;
there is no extra normality hypothesis.

`auxiliaryDiscounted_fixedPoint_sum_lt_of_no_uniformEquilibriumPayoff`
(in the same module) states the uniform consequence: if the original game
has no uniform-equilibrium payoff, then for every positive tolerance there
is a positive discount threshold such that every auxiliary cube fixed point
at every positive discount complement below that threshold and at most one
has total hazard below the tolerance. The threshold is chosen before both
the discount and the fixed point. This is not a convergence theorem for
only one selected family.

The unscaled theorem requires neither an R0 matrix hypothesis nor integer
degree.

## Four-player scaled control

`finFour_auxiliaryDiscounted_fixedPoint_scaled_sum_lt_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`)
also bounds total hazard divided by discount, uniformly over all actual
auxiliary cube fixed points at sufficiently small positive discounts. One
positive radius and threshold precede both discount and root. The only
substantive premise is absence of an original four-player uniform payoff.

The construction obtains original punishment normality from the existing
four-player hard residual, excludes homogeneous singleton solutions to get
full R0, and transfers that matrix property to the actual auxiliary reward
by terminal-shift cancellation. It uses no auxiliary strategic-equivalence
claim. The actual displacement supplies the exact perturbed LCP, while
`abs_quittingDiscountedSingletonRemainder_le`
(`UniformEquilibrium/Quitting/Stationary/DiscountedQuadraticRemainder.lean`)
supplies its quadratic remainder bound from the same reward table.

`hasFDerivAt_quittingDiscountedDisplacement_zero`
(`UniformEquilibrium/Quitting/Stationary/DiscountedAmbientDerivative.lean`)
identifies the ambient derivative of the same literal displacement.
`tendstoUniformlyOn_quittingDiscountedDisplacement_scaled`
(`UniformEquilibrium/Quitting/Stationary/DiscountedUniformScaling.lean`)
proves convergence of minus displacement divided by discount to the
singleton-matrix affine map, uniformly on every fixed bounded signed set.
The actual polynomial's ambient differentiability and uniqueness of the
derivative within the full-dimensional cube justify this comparison; the
probabilistic remainder inequality is not asserted outside the cube.

The remaining construction is integer degree with the required invariance
and excision laws. The existing parity
machinery is not a substitute for integer degree. See the bounded discovery
map in [CODEX_FORMALIZER_SIGNED_DEGREE_DISCOVERY_MAP.md](CODEX_FORMALIZER_SIGNED_DEGREE_DISCOVERY_MAP.md).

## Verification scope

The canonical modules passed targeted silent builds. An independent static
review checked the full assignment, source refinements, quantifier order,
and original-game translation. Their exhaustive axiom audit is supplied
by the production `AxiomAudit` target, not by this note.
