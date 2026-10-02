# Negative-side ideas: conjecture-relevance triage

**Status (2026-08-26): COMPLETE INTERNAL TRIAGE.**  This is a source audit,
not a new theorem and not an export candidate.  I inspected the README and
claim files in the nine requested directories and compared them narrowly with
the maintained frontier and current checked declarations.

## Question

Which negative/counterexample-side idea directories still contain a genuinely
new lead for the finite-quitting uniform-equilibrium conjecture, as opposed to
a checked duplicate, a known regression, an unsupported producer, or a topic
without a current consumer?

The classifications below concern the **current mathematical frontier**, not
the historical value of the work.

## Ranked result

### Tier 1: useful open producers, but no present conjecture reduction

#### 1. `PositiveWelfareSeparator` — best surviving lead

The downstream mechanism is real: positive security weights together with a
global weighted occupation ceiling and bounded Bellman bias give a uniform
payoff.  Finite LP duality for a fixed positive weight is also useful.  The
missing statement is exactly WS3: robust failure of local repairs must produce
one **global** separator with every coordinate strictly positive.

This is neither proved nor supported by ordinary Farkas separation.  A local
separator may have mixed signs and may cease to separate on a different
continuation cell.  The idea file records this failure correctly.

Maintained seam: convert failure of a finite family of local repair systems
into a single all-occupation welfare normal `alpha >> 0`.  This would be a
genuine producer for the already checked welfare-ceiling consumer.

Exact next test: build the smallest rational quitting table for which all of
the proposed local repair polyhedra fail robustly, enumerate the global
occupation polytope, and solve the normalized dual problem

\[
  \alpha_i\ge t,\qquad \sum_i\alpha_i=1,
\]

maximizing `t`.  If the optimum is nonpositive, WS3 is false at its proposed
scope.  If it is positive, the proof must explain why the local certificates
assemble into that one global occupation system.  This is the highest-value
test among the nine directories.

#### 2. `VanishingDiscountResponseSynthesis` — viable conditional route

VD1 is a supplied-certificate verifier.  VD2 (resolvent-to-Poisson passage on
one analytic, support-stable finite architecture) and VD3 (a general producer)
remain open.  The directory correctly identifies the two main obstructions:
unbounded normalized bias and support/domain chattering.

Maintained seam: obtain a bounded gain--bias/public-response packet from an
**actual supplied** discounted certificate family.  Without such a family the
idea does not touch the current quitting-game residual.

Exact next test: fix one finite architecture and either (a) prove eventual
support/domain stability plus a uniform oscillation bound for normalized
continuation values, or (b) give a rational multichain family whose active
support chatters cofinally and admits no fixed-domain gain--bias limit.  This is
less immediate than the welfare test because the producer input itself is not
currently supplied by the maintained Fin4 or paid residuals.

### Tier 2: mathematically valid tools or regressions, already subsumed

#### 3. `ZeroSumMertensNeymanComposition` — checked implementation supersedes it

The proposed Puiseux/algebraic-value branch and bounded-variation account
assembly are now represented by checked declarations, notably
`boundedVariationOn_of_polynomial_root` and
`tailEVariation_vanishes_of_polynomial_root` in
`MathUE/AlgebraicSelection.lean`, and the account and payoff consumers in
`UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/AccountStrategyPuiseux.lean`
and `AccountStrategyAlgebraic.lean`.  The latter includes
`PuiseuxDiscountedValueSelection.isUniformEquilibriumPayoff` and the normalized
analytic-reparameterization consumer.

Thus the directory is historically useful but is not a new negative-side
lead.  Singular/nonregular branches remain a boundary of some individual
theorems, not evidence for a counterexample route.

#### 4. `StationaryRepairExhaustion` — core dichotomy checked, remaining screens incomplete

The full stationary cap and the stationary regret infimum dichotomy are now
checked in `UniformEquilibrium/Quitting/Stationary/RegretDichotomy.lean`, with
the zero-infimum approximate-stationary branch and positive-regret witness
packaged explicitly.  Nonattainment and block-pair examples correctly show why
compactness or a narrow stationary grammar is not complete.

The unfinished block-pair exclusions are candidate screens only.  They neither
control unrestricted behavioral strategies nor produce a counterexample.
Accordingly this directory is subsumed as a theorem source and useful only as
a regression catalogue.

#### 5. `StaticStationaryRepairBoundary` — exact cautionary regression

The calibrated table refutes the narrow static repair grammars, while an exact
mixed stationary profile repairs the same table.  The earlier positive-gap
interpretation is explicitly retracted.  This is a sound no-go against a proof
architecture, not a surviving conjecture lead.

#### 6. `BoundedPublicControllerSynthesis` — sound verifier class, no completeness

Fixed-controller verification/synthesis is a useful semialgebraic tool.  The
finite-public completeness hope is already rejected by clock/private-memory
phenomena, and no source-derived node bound is supplied.  A corrected
fixed-architecture rejection certificate could improve tooling, but it would
still be a verifier/screen rather than a conjecture decision unless paired
with a completeness theorem.  No such current seam is supplied here.

### Tier 3: independent or stale meta-directions without a maintained consumer

#### 7. `InvertedCounterexampleSearch` — bookkeeping useful; proposed completeness stale

The constraint ledger is useful historical bookkeeping.  Its current README
correctly says that a positive terminal gap plus finite canonical
floor-prefix capacity—not bounded cycles—is the relevant search object.
Older material that treats a universal bounded cycle length or a rational
semialgebraic barrier as a completeness criterion is therefore stale or open,
not a proved finite reduction.  Rectangular and debt-only barriers have known
no-go results, while general semialgebraic completeness has no current
consumer.

No exact next computation here dominates the maintained literal-prefix and
paid-cap residuals.  If revived, the honest test is to exhibit a rational
positive-floor instance whose least invariant requires structure outside the
proposed semialgebraic template; bounded-period failure alone is not evidence.

#### 8. `HarmonicPotentialNashGeometry` — valid finite geometry, irrelevant at present

The flatness statement for pure Nash equilibria of harmonic games and the
edge-defect estimate are finite normal-form facts.  The proposed norm estimate
and, more importantly, a producer of a harmonic residual from quitting-game
data are absent.  There is no stochastic/all-behavior consumer.  This should
remain independent unless a maintained residual is first shown to lie in the
required harmonic class.

#### 9. `wild` — survey and methods, not one live mathematical lane

The directory describes itself accurately as a survey portfolio.  Most
concrete ideas have either been promoted elsewhere or demoted:

- Noether/gauge arguments recover survival contraction but no existence
  theorem;
- numerical backward-error tools are useful for falsifying candidate tables,
  but bounded computational failure is not completeness;
- positive-amplitude/projective geometry overlaps the checked tangent/LCP/Qbar
  language without a new producer;
- open-games, cryptographic, physics, representation-theoretic, and signal
  processing files supply analogies or special-class questions, not a current
  counterexample construction;
- the sharding pilot is research methodology, not mathematics.

The only reusable negative-side asset is validated numerical screening.  It
should be used to falsify a precisely stated finite producer, not promoted as
its own conjecture route.

## Unsupported or false inferences to avoid

1. Robust failure of several local repair systems does **not** by itself give
   a positive global welfare normal.
2. Pointwise convergence of discounted values does **not** give a bounded bias
   or one stable response architecture.
3. Failure of stationary or bounded-controller searches does **not** imply a
   positive unrestricted behavioral gap.
4. Failure to find a bounded cycle does **not** decide canonical floor-prefix
   feasibility.
5. A harmonic/projective/numerical representation is not a producer from an
   arbitrary quitting table.

## Sources inspected

- all README and claim files at the top level of the nine requested
  `ideas/` directories;
- `docs/FRONTIER.md` and `docs/TOOLKIT.md`;
- `UniformEquilibrium/Quitting/Stationary/RegretDichotomy.lean`;
- `MathUE/AlgebraicSelection.lean`;
- `UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/AccountStrategyPuiseux.lean`;
- `UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/AccountStrategyAlgebraic.lean`.

## Recommendation

Do one bounded exact LP falsification campaign for
`PositiveWelfareSeparator`.  Keep `VanishingDiscountResponseSynthesis` parked
until a concrete discounted certificate family is supplied.  Treat the other
seven directories as checked regressions, subsumed implementations, survey
material, or tooling—not as active conjecture leads.
