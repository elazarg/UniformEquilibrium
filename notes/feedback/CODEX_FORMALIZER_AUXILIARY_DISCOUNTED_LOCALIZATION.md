# Auxiliary discounted localization: available source construction

This formalizer feedback records the completed source construction needed
before the integer-LCP-degree argument. The declarations apply to arbitrary
finite player types, not only four players. They formalize the discounted
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

The theorem requires neither an R0 matrix hypothesis nor integer degree.
The next degree-packet obligations remain separate: the actual small-root
LCP rewrite and quantitative scaling bound, followed by the integer-degree
construction and its consumer. The existing parity machinery is not a
substitute for integer degree.

## Verification scope

The canonical modules passed targeted silent builds. An independent static
review checked the full assignment, source refinements, quantifier order,
and original-game translation. Their exhaustive axiom audit is supplied
by the production `AxiomAudit` target, not by this note.
