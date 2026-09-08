# Integer degree and specified-endpoint curve selection: library audit

Status: bounded static formalization audit by CODEX_FORMALIZER. No build,
cache write, production edit, or new mathematical theorem is claimed here.
The report records exact declarations under their current imports and proposed
implementation contracts. It does not infer current compilation from file
presence. The two relevant packets were read in full:
`INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md` and
`INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md`.

Ownership: this report belongs under `notes/feedback/`. No `AGENTS.md` exists
in that previously absent directory; the repository instructions apply.
The earlier mining report in `math/notes/` was written before the ownership
correction and has been left unchanged, not moved or reverted.

## Outcome

The specified-endpoint analytic curve-selection library is **already present**,
unconditionally and with real coefficients. A small endpoint-preserving Bellman
wrapper is missing from the inspected neighborhood, not the geometric theorem.
This explicitly supersedes the curve-selection-library gap claim in the earlier
`math/notes/CODEX_ASTRA_MINER__RETAINED_SELECTION_WITNESSES_AND_LCP_BOUND_REUSE.md`.
That math-owned note remains unchanged; the correction is recorded here only.

An integer-valued Brouwer-degree implementation with the packet's laws was
**not found** in the pinned topology/analysis dependencies, MathUE topology,
or nearby Research parity development. Existing fixed-point and mod-two
theorems do not provide it. This is the substantial library task.

The general LCP packet should share one actual discounted Bellman source with
the predecessor. It does not require an implicit-function theorem or a
classification of the actual scaled roots. Even the sample matrix's regular
root calculation needs only local **affine** degree, not the general
differentiable local-degree theorem.

## 1. Unconditional curve selection through the supplied point

### Exact available theorem

`Math.CurveSelection.PolynomialSignCellArc.hasPositiveCoordinateAnalyticArcAt_signCell`
(`MathUE/CurveSelection/PolynomialSignCellArc.lean`) has the contract

```text
{index variable : Type*} [Finite index] [Fintype variable]
P : index → MvPolynomial variable ℝ
signs : SignPattern index
coordinate : variable
x0 : variable → ℝ
x0 coordinate = 0
x0 ∈ closure (signCell P signs ∩ {x | 0 < x coordinate})
  ⇒ HasPositiveCoordinateAnalyticArcAt
      (signCell P signs) (ContinuousLinearMap.proj coordinate) x0
```

There is no regular-point, algebraic-input, supplied-curve, Puiseux-selection,
or sign-cell nonsingularity premise. The 378-line capstone proof was read in
full. It constructs its lex-selected source, a regular localized chart,
algebraic coordinate relations, and the final arc. It does not merely unpack
a field asserting the desired selection theorem.

`HasPositiveCoordinateAnalyticArcAt`
(`MathUE/AnalyticCoordinateCurve.lean`) means there exist an actual function
`arc : ℝ → E` and radius `eta > 0`, analytic at zero, with `arc 0 = x0`,
the designated coordinate zero at `x0`, and all `0 < t < eta` in the target
set with positive designated coordinate. Thus this is analytic **at** the
prescribed endpoint, not merely analytic on a punctured interval.

`HasPositiveCoordinateAnalyticArcAt.toHasAnalyticPowerCurveAt` in that file
already reparameterizes the same ambient arc to an exact positive power in
the designated coordinate. It invokes `exists_analytic_power_parameterization`
(`MathUE/AnalyticPowerNormalization.lean`); no new inverse-function or power
normalization proof is needed.

### Dependency and integration checks

`positiveCoordinateArc_of_eventual_source_relations_some` and its parent
`positiveCoordinateArc_of_eventual_source_relations`
(`MathUE/CurveSelection/SourceFinalization.lean`) were read in full. They
synchronize the finitely many eventual algebraic relations, select one
increasing subsequence, and invoke
`Math.CurveSelection.AlgebraicApproach.hasAnalyticPowerCurveAt_signCell_of_algebraic_approach`
before projecting back to the original coordinates.

The capstone imports the actual `MathUE/CurveSelection/` implementation,
including algebraicity and finalization. This audit did not recursively
re-audit every proof in that sizeable library. It did verify that `MathUE.lean`
and `AxiomAudit.lean` import the capstone. This is a static integration fact,
not a newly run exhaustive axiom check.

Production already consumes the theorem:
`StochasticGame.analyticBellmanGermExistence`
(`UniformEquilibrium/VanishingDiscount/Analytic/Accounting/AnalyticBellmanExistence.lean`)
proves unconditional germ existence for finite games with nonempty finite
action sets. `UniformEquilibrium.lean` and `AxiomAudit.lean` import that module.

Reading only `HasBellmanSignCellCurveSelection`
(`UniformEquilibrium/VanishingDiscount/Bellman/CurveGate.lean`) would therefore
misidentify a discharged gate as an unimplemented library theorem.

## 2. Small missing literal endpoint wrapper

The unconditional germ-existence endpoint chooses a closure point itself.
The new packet instead needs the particular limit of an alleged escaping
sequence. The correct small theorem is:

```text
G finite; actions finite and decidable
assign0 : BellmanVar G → ℝ
assign0 disc = 0
assign0 ∈ closure
  (G.polynomialBellmanSolutionSet ∩ {assign | 0 < assign disc})
  ⇒ ∃ germ : G.AnalyticBellmanGerm, germ.endpoint = assign0
```

Do not add a global action-nonemptiness premise merely to obtain a Fink point:
the supplied closure hypothesis replaces that existence step. Keep the usual
finite player/state/action and decidable index hypotheses needed by the
existing Bellman syntax. This wrapper is a proposed composition, not yet
checked in this audit.

Proof dependencies, in order:

1. `signInvariant_polynomialBellmanSolutionSet` and the finite family
   `bellmanConstraintPoly` already describe the full assignment set.
2. `signInvariant_eq_iUnion_signCell`, `selectedPatterns`, and finite-union
   closure in `MathUE/PolynomialSignCell.lean` choose one cell approaching
   **the supplied** `assign0` through positive discount. The existing proof
   of `exists_vanishingDiscount_bellmanSignCell` in `CurveGate.lean` contains
   this reduction after its unrelated Fink-based endpoint choice.
3. Apply the unconditional sign-cell arc theorem and enlarge its target with
   `HasPositiveCoordinateAnalyticArcAt.mono`.
4. `StochasticGame.exists_analyticBellmanGerm_of_positiveCoordinateArc`
   (`UniformEquilibrium/VanishingDiscount/Bellman/Germ.lean`) returns the germ
   together with literal endpoint equality. Its proof and the alternative
   `analyticBellmanGermOfPowerCurve_endpoint` were inspected.

This route needs neither general semialgebraic projection nor a fresh
semialgebraic curve-selection engine. A generic `IsSemialgebraic` wrapper can
later collect a finite formula's atoms and use the same finite-cell theorem,
but it is not a prerequisite of the actual Bellman consumer.

### Actual source lift still required

For the quitting packet, first construct the full assignment for each actual
discounted root/value pair: live hazards and their complements, live values,
constant absorbing actions and rewards at all fifteen absorbed states, and
the same discount coordinate. Prove each assignment solves the full Bellman
system and that the complete assignments converge to the specified assignment.
The wrapper does not supply this bridge from a root-only polynomial graph.

The eventual original-game consumer is
`isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/AuxiliaryShift.lean`).
That module is generic in the finite player type at this declaration. Its
signed sole-owner punishment branch must remain intact. Neither an arbitrary
germ nor a prescribed-payoff limit alone substitutes for the same endpoint's
positive absorption.

## 3. Integer-degree infrastructure: what was and was not found

The bounded search covered topological degree, local degree, degree homotopy,
excision, determinant orientation, sphere homology, and winding terminology in
MathUE, Research topology, and the pinned Mathlib topology, analysis, and
algebraic-topology subtrees. It also inspected the pinned fixed-point package.
This is not a claim about all external Lean projects or unpublished code.

Available pieces:

- `brouwer_fixed_point`
  (`.lake/packages/fixed-point-theorems/FixedPointTheorems/brouwer.lean`)
  proves a fixed point for a continuous self-map of a nonempty compact convex
  finite-dimensional set. It does not attach an integer index to its roots.
- `boxComplementarity_completeSimplex_card_odd`
  (`Research/Topology/BoxComplementarityCubicalSperner.lean`) is an actual
  finite-grid odd-cardinality theorem.
- `boxComplementarityLocalCompleteSimplexParity_univ`, local disjoint-union
  additivity, and `relativeCubicalPrism_boundaryParity_eq`
  (`Research/Topology/BoxComplementaritySpernerLocalCount.lean`) are mod-two
  results. The relative-prism theorem assumes its finite incidence data and
  boundary classification; it does not build a continuous signed degree.
- `ModTwoBoxComplementarityParitySpec`
  (`Research/Topology/ModTwoBoxComplementarityParity.lean`) explicitly declares
  an open supplied structure. Its homotopy/excision laws are fields, not an
  implemented parity invariant. Replacing `ZMod 2` by `ℤ` in such a structure
  would not implement the missing theory.
- `spernerChainStepSet_card` and the raised-coordinate/chain-position lemmas
  (`Research/Topology/CubicalSpernerKuhnChain.lean`) expose actual Kuhn-grid
  geometry. `dist_boxComplementarityGridPoint_le_one_div_of_simplex` and
  `BoxComplementarityProblem.isSolution_of_completeSimplexAnchorPoint_tendsto`
  (`Research/Topology/BoxComplementaritySpernerApproximation.lean`) provide
  mesh estimates and a solution limit, not signed refinement invariance.
- `AlgebraicTopology.singularHomologyFunctor`
  (pinned `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`) and
  `TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`
  (neighboring `HomotopyInvariance.lean`) exist. This search did not locate the
  required punctured-space/sphere generator calculation, relative excision,
  and orientation-to-determinant package from which the packet's integer degree
  could be read off immediately.
- Pinned `Mathlib/Analysis/InnerProductSpace/Orientation.lean` has genuine
  determinant/orientation identities for bases. These concern linear algebra,
  not degree of a nonlinear continuous map.

No claim that parity distinguishes `+1` and `-1` is permissible: they have the
same image in `ZMod 2`. The sample's three local signs `-1,-1,+1` illustrate
the failure of that substitution directly.

## 4. Minimal honest integer-degree contracts

Use the standard oriented coordinates `E = Fin n → ℝ`; no manifold API is
needed. The main consumer has `n=4`. A mathematical degree value is integer-
valued and may be noncomputable, but its construction and invariance theorems
must be proved, not supplied as fields.

For a bounded open `U`, a map continuous on `closure U`, and target `y`
avoided on `frontier U`, the needed contracts are:

1. **Normalization and affine orientation.** Identity has degree one when
   `y∈U`. For an invertible matrix `A` and `a∈U`, the map
   `x ↦ A*(x-a)` has degree `sign(det A)` at zero.
2. **Homotopy invariance.** A jointly continuous map on
   `[0,1] × closure U`, avoiding `y` on the entire time-boundary cylinder,
   has equal endpoint degrees. Pointwise avoidance with a changing domain
   is not the stated hypothesis.
3. **Excision.** If an open subdomain `V⊆U` contains every zero relative to
   `closure U`, restricting the domain to `V` preserves degree. This must
   retain the complete zero set, including proper-support and nonisolated roots.
4. **Finite additivity and empty-zero normalization.** Pairwise disjoint open
   neighborhoods covering all zeros contribute the sum of their degrees;
   a zero-free domain has degree zero. Nonzero degree then implies a zero.
5. **Positive domain/output dilation.** For positive scalars `c,d`, the degree
   of `x ↦ c*f(x/d)` on `d*U` at zero equals the degree of `f` on `U` at zero.
   Both orientation signs are positive.
6. **Boundary perturbation stability.** A perturbation uniformly smaller than
   the positive boundary distance from `f` to zero preserves degree. This is
   a consequence of the straight-line homotopy theorem, not another axiom.

All domains used directly in the main comparison are open boxes; local sample
calculations use finitely many small disjoint neighborhoods. A boxes-first
construction can be a meaningful first milestone, provided its excision and
additivity really suffice for those uses. It must not require roots to be
regular or finite merely to define degree. A polished general-domain API is
secondary to an actual proved invariant on the required domains.

### Construction route and genuine cost

The closest concrete source is the finite Kuhn triangulation, suggesting a
classical signed piecewise-linear degree construction. This is a design choice,
not a completed proof or a claim that the existing parity proof can simply be
retyped over integers. The missing work includes oriented face incidence and
cancellation, signed counts for affine simplices, refinement/prism invariance,
and approximation independence for continuous maps with a boundary margin.

A homological construction is an alternative, but the inspected homology
infrastructure does not remove the sphere/relative orientation work. An
integral or regular-value construction would need additional supporting
analysis not identified here. Do not start any of these as an unbounded tactic
exercise: freeze a precise construction plan and its first independently
testable signed-cancellation milestone before implementation. This is a
multi-session library project, not a small missing game adapter.

## 5. Dependency-ordered implementation tasks

**Small and immediately reusable:**

1. Add the specified-complete-endpoint Bellman wrapper of section 2. No new
   geometric theorem or action-nonemptiness producer is needed.
2. Construct the literal discounted quitting displacement and its complete
   Bellman assignment lift. Prove its value denominator positive, all lower/
   interior/upper face conditions, full-response Bellman bound, and bounded
   value. Then use task 1 to exclude every nonzero root cluster under no UE.
3. Prove the actual first-order displacement expansion and use the existing
   `Math.LinearProgramming.sum_le_of_isStandardLCPSolution`
   (`MathUE/LinearProgramming/R0Margin.lean`). Once upper faces are excluded,
   `D=λa-Γq+e` makes `q` an exact LCP solution with right-hand side
   `-λa-e`. Absorbing the quadratic remainder under the separately proved
   uniform smallness gives the bounded `q/λ` region. No approximate-LCP theory
   or positive support hypothesis is required.

**Independent large library chain:**

4. Prove a signed finite-mesh orientation/cancellation kernel on an actual
   triangulation. A supplied incidence specification is only an intermediate
   lemma until the concrete mesh is shown to satisfy it.
5. Construct the integer degree and prove its mesh/approximation independence,
   common-domain homotopy invariance, excision, normalization, and additivity.
   Derive positive dilations and boundary perturbation stability.
6. Define `κ(Γ)` using the actual min-map at right-hand side zero on a box.
   Existing `R0` boundedness supplies a common box along each bounded segment
   of right-hand sides. Prove box and right-hand-side independence by tasks
   4–5, not by assuming a degree package in the theorem's input.

**Final known packet joins:**

7. For the clipped discounted map use the expanded box `(-1,2)^4`; all fixed
   points lie in the strategy cube. The center homotopy gives degree one.
   On a smaller scaled box prove the upper clip inactive but retain the lower
   clip exactly. Excision, positive dilations, and uniform boundary convergence
   identify this degree with the full min-LCP degree at the actual anchor.
8. Verify the sample's finite support inventory. Strict active coordinates and
   strict inactive slacks make its min-map locally exactly affine, with matrix
   blocks `[Γ_SS Γ_S,Sᶜ; 0 I]`. Affine orientation plus excision already gives
   each determinant sign; no general differentiable local-index theorem is
   needed for these calculations.
9. Recover the inverse-nonnegative class at the all-ones test right-hand side,
   after the actual no-UE-to-full-matrix-`R0` dispatch. Its unique positive root
   is locally affine too. Do not separately implement strict-interior IFT or
   reward approximation as a prerequisite of this shorter recovery.

The packet's generic R0/degree-one residual is not proved empty. None of the
proposed tasks changes its mathematical conclusion, removes no-UE from the
all-fixed-point localization source, or replaces actual full assignments with
a selected root graph.

## Next check

First implement and strictly check only the small supplied-endpoint wrapper.
The root should independently verify this report's unconditional capstone
discovery under its current cache epoch. Before any integer-degree coding,
choose the concrete signed construction and its first finite cancellation
theorem; no new abstract degree specification should be presented as closure.
