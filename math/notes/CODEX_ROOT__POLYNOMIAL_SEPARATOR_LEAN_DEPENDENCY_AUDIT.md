# Polynomial separator: Lean dependency audit

Author: CODEX_ROOT, recording the independent Astra audit.
Audit date: 2026-09-06. Source: the frozen polynomial-forward export.

## Status and scope

The initial audit inspected libraries and proposed interfaces without Lean
checks. Subsequent checked implementations are distinguished below.
The main polynomial separator and fixed-box characterization passed the silent
full build and repository checks in `98ea672`, which is pushed. The packet's
literal boundary examples passed the same checks in pushed `bc9a439`.
The complete packet is archived byte for byte under `math/formalized/`, with
declaration mapping in `POLYNOMIAL_FORWARD_CERTIFICATES_LEAN_COVERAGE.md`.
Its ordinary proof is in
`POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md`.
The work below formalizes that proof, not a new arbitrary-game producer.

Finite burn-in, floor-free producer equivalences, and the finite sure-root
characterization are integrated. The last characterization needs no
normality or singleton-sign assumption. The first two have the checked
strengthenings recorded in
`CODEX_ROOT__WEIGHTED_PACKET_AND_PIVOT_REPAIR_LEAN_MINING.md`.

The stationary and sequential source adapters are also integrated. Under
all-player normality, one positive singleton reward, and a supplied reward
bound `M`,
`quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot`
(`UniformEquilibrium/Quitting/Projective/FixedBoxForwardCharacterization.lean`)
proves uniform-payoff existence equivalent to weighted packets in the fixed
box of radius `M+2` or the finite sure-quitter punishment-vector Nash root.
It uses only the checked forward AKRS implication. This passed a silent
full build and repository checks in commit `2fae892`.

## Dependency order

```text
compact continuum paths → finite-horizon USC → bounded Borel capacity
                                              ↓
positive common-translation estimates → one-sided smoothing
                                              ↓
simultaneous rational-polynomial derivative approximation
                                              ↓
charge-scaled endpoint error → polynomial drift on every inner edge
```

The smoothing and polynomial-approximation libraries can be developed
independently of capacity regularity. The game adapter must retain the full
robust edge relation, not only selected roots or a reachable component.

## Compact-edge capacity regularity

`Maths.ChargedPathBudget.ChargedRelation` (`MathUE/ChargedPathBudget.lean`)
already supplies literal finite paths, nil paths, charge, the value function,
its bounded-potential theorem, and telescoping. The existing
`MathUE/ChargedPathFiniteHorizon.lean` requires finitely many edge types and
does not handle the continuum robust relation.

The compact companion is integrated in commit `9f7c1dd`, with a silent full
build and repository checks. `MathUE/ChargedPathCode.lean` codes and decodes
literal paths with exact endpoints and charge, including nil. Its countable
supremum identity needs no topology. `MathUE/CompactChargedPathCapacity.lean`
takes compact topological state and edge spaces, Hausdorff states, and
continuous source, target, and charge.
`exists_path_eq_compactFiniteHorizonMaxCharge` attains the maximum at every
initial state and finite horizon. The maximum is upper semicontinuous by
`upperSemicontinuous_compactFiniteHorizonMaxCharge`. Under finite global
budget and the Borel measurable-space structure on states,
`measurable_value_of_compact_edges` proves the existing all-horizon value
Borel measurable. No metric, outgoing-edge nonemptiness, positive-charge,
or infinite-path-attainment hypothesis is imposed.

The all-horizon value is not asserted upper semicontinuous. Removing state
compactness from this generic layer may be possible using only compact
positive superlevel sets; that refinement is not checked by this audit.

## One-sided smoothing

Mathlib's `HasCompactSupport.contDiff_convolution_right` and its left
counterpart (`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`) differentiate
the kernel and need only local integrability of the other function.
Finite-dimensional bump-function APIs supply smooth compactly supported
kernels. The checked adapter constructs a nonnegative probability kernel
whose topological support lies strictly inside the positive orthant cube,
then proves that averaging a bounded Borel potential at `x+h` preserves
every supplied translated drift inequality.

The sign is important: Mathlib convolution uses `x-z`; the desired positive
shift needs a reflected kernel. The game adapter must prove that every
sampled endpoint lies in the actual outer domain, so the zero extension does
not invent an inequality. No continuity of the unsmoothed capacity is assumed.

## Simultaneous derivative approximation

The complete derivative-approximation chain passed the silent full build and
repository checks in `c6ca930`. It follows the
reviewed tensor argument, not independent approximations of gradient
components:

- `eventually_fderiv_tensorBernsteinApproximation_close_on_unitCube`
  (`MathUE/Polynomial/TensorBernsteinDerivativeConvergence.lean`) uses one
  common degree for every coordinate and cube point. It assumes actual
  derivatives on the cube and continuity of the derivative there.
- `exists_mvPolynomial_fderiv_close_on_bounded`
  (`MathUE/Polynomial/PolynomialDerivativeApproximation.lean`) transports
  the construction to any bounded real domain for a global continuously
  differentiable function. Neither compactness nor nonemptiness of that
  domain is needed.
- `exists_evalReal_fderiv_close_of_contDiff_on_box`
  (`MathUE/Interval/RationalPolynomialSmoothDerivativeApproximation.lean`)
  constructs one native rational polynomial approximating every actual
  coordinate derivative and the derivative operator uniformly. Real box
  endpoints may be irrational, reversed, or degenerate. Dimension zero is
  included.

The statements retain both summed coordinate error and operator-norm error.
They do not assert function-value approximation. A uniform value-only
approximation would not suffice for arbitrarily small edge charges.

The finite coefficient-perturbation step was separately integrated in
`6007e2d`, with a silent full build and repository checks.
`exists_evalReal_fderiv_close_on_compact`
(`MathUE/Interval/RationalPolynomialDerivativeApproximation.lean`) starts
from one actual real polynomial; the tensor construction now supplies that
polynomial from an actual smooth function. `exists_evalReal_eq_eval₂` gives
the exact native-syntax bridge.

## Final game adapter

The full robust relation's compactness and continuity are integrated in
`e9f3e90`. Its literal path/packet conversions and specialized capacity
regularity have now passed targeted builds in
`UniformEquilibrium/Quitting/Projective/RobustChargedRelationPacketAdapter.lean`
and `UniformEquilibrium/Quitting/Projective/RobustChargedRelationCapacity.lean`.
These retain exact roots, endpoints, length, and charge; all-horizon capacity
is Borel measurable under a finite budget, not asserted upper semicontinuous.

`UniformEquilibrium/Quitting/Root/VectorTranslation.lean` and
`UniformEquilibrium/Quitting/Projective/RobustChargedRelationTranslation.lean`
also pass targeted builds. The shift is a common nonnegative vector,
not only a scalar shift. The translated residual and ordinary regret obey
the sharper half-tolerance bound; root and charge are retained literally.
The endpoint displacement estimate is proportional to absorption and does
not divide by a charge that might be zero.

The mean-value transfer and native rational drift compiler pass targeted
production builds. They construct the derivative approximation inside the
proof, then double the resulting rational polynomial to recover unit-charge
drift on every robust edge. The intermediate game compiler still assumes
a supplied global continuously differentiable potential with drift on the
full relation; it does not assume that finite capacity is already smooth.
An independent audit of the vector translation found no scope or sign error.

## Composed analytic and fixed-box results

The following are integrated in `98ea672`, with silent full-build and
repository checks:

- `exists_quittingRobustChargedRelation_rationalPotential_of_finiteBudget`
  (`UniformEquilibrium/Quitting/Projective/RobustChargedRelationPolynomialSeparator.lean`)
  constructs one native rational polynomial from actual finite outer capacity.
  It retains full drift on every inner edge. It assumes no supplied smooth
  potential, derivative approximation, normality, or lower absorption bound.
- `exists_quittingFloorRobustChargedRelation_rationalPotential_of_finiteBudget`
  (`UniformEquilibrium/Quitting/Projective/FloorRobustPolynomialSeparator.lean`)
  proves the endpoint-floor variant for any real floor vector and any finite
  dimension, including empty domains and dimension zero. Punishment floors
  are one specialization; rational floors are not required.
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  (`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`)
  proves the packet's main normal-Fin4 equivalence with one positive singleton.
  Failure of uniform-payoff existence supplies finite robust capacity at a
  positive rational tolerance in the actual outer box `M+3`. Smoothing and
  rational approximation then produce the certificate in `M+2`, at tolerance
  at most one quarter. The converse consumes the entire robust relation.

Sol independently audited the shared-polynomial and zero-charge transfer;
Astra independently audited the reflected-kernel sign, normalization, domain
evaluation, and all-edge drift. The §7 literal regression examples remain
separate work and are not covered merely by these general theorems.

The analytic statements are stronger than the Fin4 export: arbitrary finite
dimension and arbitrary box radius are allowed. In particular, no hypothesis
says the box contains the reward table. The floor-bearing theorem accepts any
real floor vector. These are checked generalizations of the analytic step,
not of the final normal-Fin4 uniform-payoff characterization.

No degree bound, concrete negative certificate, complete certificate-checking
algorithm, or arbitrary-game uniform-equilibrium existence theorem is claimed.
