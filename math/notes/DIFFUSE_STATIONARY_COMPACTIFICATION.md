# Diffuse stationarily-generated compactification

Status: structural classification note; no longer a conjecture-closing
question because the generated branch already has a checked direct
uniform-payoff consumer.

## Setting

Assume a finite quitting reward table has a diffuse stationarily-generated
approximate-equilibrium family. After subsequence extraction, its finite
stationary-prefix horizon is fixed or diverges, and its one-stage live mass
tends to zero or to a positive limit. In the positive-live divergent-horizon
case, the limit retains a stationary-prefix value, a punishment tail/cap, and
an all-player deviation inequality.

## Question

Prove that every residual diffuse family yields either a stationary
uniform-equilibrium payoff or a well-supported absorbing sequence (with the
instant-punishment case included only where justified). Equivalently, prove
the exact hypothesis of
`fixedThreeQuittingBranches_of_pointwiseAlternative_of_diffuseCompactification`.
The proof must preserve the actual punishment endpoint and must handle the
all-Continue phantom separately; it may not identify forward value with
punishment value without proof.

## Why this is useful

This is now a structural classification question, not a missing payoff
consumer: stationarily generated approximate equilibria already compile
directly to a uniform-equilibrium payoff.  A positive answer would remove the
fourth residual branch and recover the intended classical three-way
classification without losing the punishment endpoint.

## Checked inputs and consumers

- `fixedThreeQuittingBranches_of_pointwiseAlternative_of_diffuseCompactification`
  (`UniformEquilibrium/Quitting/Classification/Existence/CorrectedFixedBranch.lean`)
  is the exact compactification consumer.
- `exists_uniformEquilibriumPayoff_or_stationaryPrefix_residual`
  (`UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedWitnessRegimes.lean`)
  identifies the residual regimes.
- `wellSupported_or_exists_allContinuePhantom_of_stationaryPrefix_family` and
  `QuittingPositiveLiveStationaryPrefixLimit.exists_punishmentTail_realizers`
  (`UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedPositiveLiveLimit.lean`)
  retain the positive-live data and punishment tail.
- `limitProfile_not_isExactNash` and
  `not_tendsto_terminalPayoff_to_limit`
  (`UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedCompactnessObstruction.lean`)
  are checked warnings against naive phantom compactification.
- `quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence`
  (`UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedBranch.lean`)
  explains why resolving this structural split is no longer required merely
  to consume a generated approximate-equilibrium family.

## Not proved

The diffuse residual has not been shown to enter either stationary or
well-supported absorption. The phantom example shows that a naive limit
identification is false.

## Acceptable answers

A positive answer gives the two-way residual compactification with all caps
and deviations. A negative answer gives a valid diffuse family whose limit is
neither branch, or proves that the implication needs an explicit additional
hypothesis. A phantom example alone is only a falsifier of a naive stronger
claim.

## Dependencies

None required.
