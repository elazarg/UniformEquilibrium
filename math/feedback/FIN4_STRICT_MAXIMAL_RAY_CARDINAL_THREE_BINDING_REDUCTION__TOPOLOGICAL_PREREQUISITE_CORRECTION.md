# The topological prerequisite of the binding-cardinality packet is narrower than stated

Formalizer: external Lean formalization agent
Target: [`FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION.md`](../exports/FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION.md)

Verdict: **The packet's stated prerequisite — a signed finite-game
equilibrium-component index layer — is heavier than its own argument needs,
and an earlier reading of this packet as blocked on that layer was wrong.  A
mod-two index suffices, the repository already took that route, and the
conditional reduction consuming it is written.  Two items remain, both
identified.  Nothing new is checked here, so the export is not claimed as
accepted.**

## The correction

The packet's Lean handoff asks for "a trustworthy finite-game
component-index layer: isolating neighborhoods, local degree, perturbation
invariance, strict-pure and mixed-coordination signs, deletion of strict
non-best actions, and the global index sum", and its exact statement justifies
the cardinal-two exclusion by component indices summing to `+1`, strict pure
equilibria at `+1`, and a regular mixed coordination equilibrium at `-1`.

The argument does not use those signs.  It uses only that the local
contribution differs from the global one.  Since `+1` and `-1` are both `1`
modulo two, the same contradiction follows from a mod-two index, where the
local contribution is `0` and the global is `1`.  Nothing else in the
cardinal-two calculation reads the sign.

That is the route the repository took.

## What the repository already has

`Research/Topology/ModTwoBoxComplementarityParity.lean` states the interface.
Its own module docstring describes it as the smallest topological interface
needed by the strict-ray binding-cardinality argument — this packet's
argument, named.  `ModTwoBoxComplementarityParitySpec` carries a regularity
predicate and four fields:

```text
globalParity_eq_one
localParity_eq_global_of_solutionSet_subset          (excision)
localParity_eq_of_common_isolating_homotopy          (homotopy invariance)
localParity_eq_card_of_finite_regular                (finite regular count)
```

`ModTwoBoxComplementarityParitySpec.exists_solution_not_mem_of_localParity_ne_one`
is the packet's reasoning in mod-two form: a local parity different from the
global odd parity forces a solution outside the displayed isolating
neighborhood.

`Research/Quitting/Root/EndpointNashBoxComplementarity.lean` bridges endpoint
Nash roots to box complementarity;
`QuittingEndpointNashBoxBridge.isSolution_iff_isZeroQuittingRootNash`
identifies the two solution notions at a fixed cap.

`Research/Quitting/FinFourProducerAtlas/StrictRayBindingCardinality.lean` is
the consumer, already written as a conditional reduction taking a parity
theory and a local binding-pair certificate as explicit data.
`FinFourBindingPairParityCertificate` supplies the cardinal-one exclusion and,
in the pair case, a `FinFourBindingPairFiniteCapParityWitness`: a late finite
time, an endpoint-Nash bridge at that cap, an isolating neighborhood
containing every solution, and a `FinFourBindingPairLocalParityZero` witness.
`bindingFinset_card_ne_two_of_unique_allContinue` is the cardinal-two
exclusion and
`bindingFinset_eq_univ_or_card_eq_three_of_unique_allContinue` its
consequence.  The certificate's own docstring states that no field asserts it
exists.

Toward an implementation,
`Research/Topology/BoxComplementaritySpernerLocalCount.lean` defines the
mod-two count of complete Sperner simplices anchored in a displayed set and
proves finite-set coherence, excision, global count one, and fine-mesh collar
clearing; `Research/Topology/BoxComplementaritySpernerEventualLocalParity.lean`
proves that an open set containing the whole solution set has local count
eventually one modulo two
(`BoxComplementarityProblem.eventually_localCompleteSimplexParity_eq_one`).

The base theorem is proved upstream, not here: `strong_cubical_sperner` in the
pinned `fixed-point-theorems` dependency,
`FixedPointTheorems/cubical_sperner.lean` — every proper labeling of a finite
cubical grid has an odd number of complete top-dimensional simplices.

## What actually remains

Two items, not one.

1. **An inhabitant of `ModTwoBoxComplementarityParitySpec`.**  The local-count
   module states explicitly that it asserts no subdivision invariance, no
   homotopy invariance, no eventual local parity, and no spec inhabitant; the
   eventual-parity module adds that it constructs no cross-resolution
   subdivision invariance, homotopy invariance, or regularity theory.  Those
   are what an inhabitant needs.
2. **The local binding-pair certificate at finite cap**, indexed by a
   sufficiently late finite time, with its isolating neighborhood around the
   finite-cap mixed point or solo segment.

The eventual-parity module points at a shortcut that may avoid item 1: to
obtain a contradiction it is enough to compute zero local parity eventually
for the explicit finite-cap binding-pair component at the same resolutions.
That would pair the checked eventual local parity one against an eventual
local parity zero at matching meshes, without a resolution-independent parity
theory.

## Two points of the packet's own scope, stated correctly

The packet does not claim unconditional cardinality three, and it is right not
to.  Uniqueness of all Continue at the limiting cap is not unconditional on
the checked ray, so the packet states an exhaustive split: a
positive-absorption exact root at the limiting cap, full binding, or
cardinality three.  The Lean consumer matches that shape exactly.
`positiveAbsorptionExactRoot_at_capLimit_or_bindingFinset_eq_univ_or_card_eq_three`
returns the positive-absorption root when uniqueness fails, and only the
uniqueness arm contracts a proper binding face to cardinality three.

The packet is also right that `Literature/Simon2007.lean` records only a
`sorry`-marked Kohlberg--Mertens statement and is not a checked source for a
component-index package.  The mod-two route makes that gap irrelevant to this
argument instead of closing it: nothing above needs the signed statement, so
nothing above waits on that transcription.

## Seals

Nothing is checked here beyond what the repository held before this report.
The parity interface is an open specification: `M` for the mathematics it
states, `L` for the interface and its one consequence theorem, and no `A` or
`C`, since no inhabitant exists and no producer supplies the binding-pair
certificate.  The strict-ray reduction is conditional on both supplied
objects, so its cardinality conclusion carries no seal of its own beyond that
conditional form.  The export packet remains at most `M`.
