# Featured theorems

This directory is a reader-facing showcase of results that, to the project
maintainers' current knowledge and judgment, are both novel and interesting or
useful beyond the uniform-equilibrium conjecture program. These are not
priority claims. Corrections about prior art, significance, or presentation
are welcome.

The catalog has at most ten featured theorem families. A slot should point to
one substantial result and may mention its important corollaries, rather than
listing many small lemmas. Adding an eleventh candidate requires merging or
retiring an existing slot. The cap is editorial and can be reconsidered during
a catalog review.

Inclusion does not create an API-stability promise. Each feature module repeats
the lead theorem statement under `Theorems.*` and proves it by delegating to
the canonical declaration. The original module remains the proof's source of
truth; `import Theorems` collects the reader-facing statements.

## Current catalog

| Family | Lead declaration | Why it is here |
| --- | --- | --- |
| Charged paths and potentials | `Theorems.ChargedPaths.finiteBudget_iff_exists_boundedPotential` | Finite nonnegative path budget is equivalent to a bounded potential, with exact minimum-oscillation duality attained by budget-to-go. |
| Charged-path renewal | `Theorems.ChargedSelection.renewal_iff_unboundedFiniteCharge_implies_divergentPath` | Characterizes when arbitrarily large finite charge consolidates into one divergent infinite path. |
| Collision mass | `Theorems.CollisionMass.collisionMass_le_choose_card_mul_absorption_sq` | Bounds the mass of at least two independent successes quadratically in total absorption. |
| Phase-occupation duality | `Theorems.PhaseOccupationDuality.exists_optimal_occupation_and_bias` | Produces matching optimal occupation and bias witnesses for feasible finite periodic occupation problems. |
| Bounded discrepancy | `Theorems.BoundedDiscrepancy.exists_walk_iff_connectedIntegerCirculation` | A bounded-discrepancy infinite walk over finite integer data is equivalent to a finite reachable connected zero-charge circulation, and an eventually periodic witness suffices. |
| Cyclic exposure | `Theorems.CyclicExposure.exists_exposure_le_quarter` | Gives a sharp one-quarter exposure bound and characterizes the unique fair optimizer. |
| Flow holonomy | `Theorems.FlowHolonomy.zeroHolonomy_iff_exists_accountPotential` | Turns a circulation inequality into an exact account-potential criterion. |
| Owner-visible lifting | `Theorems.TypedLifting.hasTypedLift_iff_validOnVisible` | Identifies exactly what an owner-local dual certificate can see and includes a cross-owner cancellation falsifier. |
| Mixed-owner obstruction | `Theorems.MixedObstruction.coupledFeasible_or_genuinelyMixedObstruction` | Refines a finite Farkas alternative so coupled failure has a normalized obstruction involving at least two owners. |

See [Catalog.lean](Catalog.lean) for companion declarations and canonical
module imports.
