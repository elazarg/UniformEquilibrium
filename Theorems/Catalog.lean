import Theorems.BoundedDiscrepancy
import Theorems.ChargedSelection
import Theorems.ChargedPaths
import Theorems.CollisionMass
import Theorems.CyclicExposure
import Theorems.FlowHolonomy
import Theorems.MixedObstruction
import Theorems.PhaseOccupationDuality
import Theorems.TypedLifting

/-!
# Featured theorem catalog

This module collects a deliberately small set of substantial, project-owned
results that appear useful outside the uniform-equilibrium conjecture program.
Each feature module repeats its lead statement and delegates the proof to the
canonical module; the underlying result remains owned there.

## Bounded charged paths and optimal potentials

`Theorems.ChargedPaths.finiteBudget_iff_exists_boundedPotential` characterizes
finite nonnegative path budgets by bounded potentials.
`Math.ChargedPathBudget.ChargedRelation.budget_eq_oscillation_value` gives the
sharp oscillation duality, attained by the budget-to-go potential.

## Renewal and divergent charged paths

`Theorems.ChargedSelection.renewal_iff_unboundedFiniteCharge_implies_divergentPath`
characterizes exactly when arbitrarily large finite charge consolidates into
one divergent infinite path.

## Quadratic collision mass

`Theorems.CollisionMass.collisionMass_le_choose_card_mul_absorption_sq`
bounds the mass of two or more independent successes quadratically in total
absorption, with the finite pair count as coefficient.

## Finite phase-occupation duality

`Theorems.PhaseOccupationDuality.exists_optimal_occupation_and_bias` gives
matching optimal occupation and bias witnesses for every feasible finite
periodic occupation problem.

## Bounded discrepancy and finite circulations

`Theorems.BoundedDiscrepancy.exists_walk_iff_connectedIntegerCirculation`
characterizes bounded-discrepancy infinite walks by reachable connected
zero-charge integer circulations and yields eventually periodic witnesses.

## Sharp cyclic exposure

`Theorems.CyclicExposure.exists_exposure_le_quarter` gives the sharp
one-quarter bound. The companion `all_exposures_ge_quarter_iff_fair`
characterizes its unique fair optimizer.

## Flow holonomy and account potentials

`Theorems.FlowHolonomy.zeroHolonomy_iff_exists_accountPotential` characterizes
nonpositive circulation holonomy by a scalar account potential.

## Owner-visible dual lifting

`Theorems.TypedLifting.hasTypedLift_iff_validOnVisible` characterizes
owner-typed lifts through the owner-visible relaxation. The canonical module's
`CrossOwnerCancellation` example proves that full-system validity need not
admit any owner-typed lift.

## Mixed-owner Farkas obstruction

`Theorems.MixedObstruction.coupledFeasible_or_genuinelyMixedObstruction`
separates coupled feasibility from a normalized positive obstruction that
genuinely involves distinct owners.
-/
