/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.MetrizableMarkedAbsorptionPath

/-!
# Finite realized compression of enriched exact seams

Boundary holonomy alone gives a bounded-length approximate representative,
but does not record enough data to certify a splice.  Production already
provides a richer compact metric semantic target for finite marked absorption
paths.  It jointly retains the completed absorption law, holonomy, exact-D
entry and exit anchors, terminal packet, entry debt, and the full compact
marked-stage graph.

This module applies one general compact-range argument twice.

1. Every finite semantically coherent cylinder is close to one of finitely
   many genuinely realized finite cylinders, hence to one with uniformly
   bounded stage-cardinality.
2. More importantly, an exact composable pair is encoded together with its
   composition.  The finite net is selected from actual exact seams.  Thus a
   source seam is approximated simultaneously by a bounded-complexity exact
   seam in its outer, inner, and composed enriched semantics.

The metric on the production semantic target is supplied by Urysohn
metrization.  The result is therefore qualitative and non-effective: it does
not turn a desired coordinatewise error into an explicit radius or stage
bound.  It does show that exact seam compatibility itself causes no new
compactness obstruction when the seam triple is compressed as one object.
-/

noncomputable section

namespace Research.QuittingEnrichedSeamCompression

open GameTheory
open GameTheory.MetrizableMarkedAbsorptionCompletion

/-! ## A reusable compact realized-range lemma -/

variable {Source Target : Type}

/-- A map into a compact metric target has a finite positive-resolution net
whose centers are values of actual sources. -/
theorem exists_finite_realized_range_codebook
    [PseudoMetricSpace Target] [CompactSpace Target]
    (encode : Source → Target)
    (resolution : ℝ) (hresolution : 0 < resolution) :
    ∃ representatives : Set Source,
      representatives.Finite ∧
      ∀ source : Source,
        ∃ representative ∈ representatives,
          dist (encode source) (encode representative) < resolution := by
  have hclosureCompact : IsCompact (closure (Set.range encode)) :=
    isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)
  obtain ⟨codebook, hcodesRealized, hcodesFinite, hcover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure
      hclosureCompact hresolution
  let representative : {code // code ∈ codebook} → Source :=
    fun code => Classical.choose (hcodesRealized code.2)
  have hrepresentative (code : {code // code ∈ codebook}) :
      encode (representative code) = code.1 :=
    Classical.choose_spec (hcodesRealized code.2)
  let representatives : Set Source := Set.range representative
  have hrepresentativesFinite : representatives.Finite := by
    letI : Fintype {code // code ∈ codebook} := hcodesFinite.fintype
    exact Set.finite_range representative
  refine ⟨representatives, hrepresentativesFinite, ?_⟩
  intro source
  have hsource : encode source ∈ Set.range encode := ⟨source, rfl⟩
  rcases Set.mem_iUnion.mp (hcover hsource) with ⟨code, hcodeCover⟩
  rcases Set.mem_iUnion.mp hcodeCover with ⟨hcode, hball⟩
  let indexedCode : {code // code ∈ codebook} := ⟨code, hcode⟩
  refine ⟨representative indexedCode, ⟨indexedCode, rfl⟩, ?_⟩
  rw [hrepresentative indexedCode]
  simpa only [Metric.mem_ball] using hball

/-- Any natural-valued source complexity is uniformly bounded on the finite
realized codebook. -/
theorem exists_uniform_cost_approximate_representative
    [PseudoMetricSpace Target] [CompactSpace Target]
    (encode : Source → Target) (cost : Source → ℕ)
    (resolution : ℝ) (hresolution : 0 < resolution) :
    ∃ costBound : ℕ, ∀ source : Source,
      ∃ representative : Source,
        cost representative ≤ costBound ∧
        dist (encode source) (encode representative) < resolution := by
  obtain ⟨representatives, hfinite, hcover⟩ :=
    exists_finite_realized_range_codebook encode resolution hresolution
  have hcostsFinite : (cost '' representatives).Finite := hfinite.image cost
  obtain ⟨costBound, hcostBound⟩ := hcostsFinite.bddAbove
  refine ⟨costBound, ?_⟩
  intro source
  obtain ⟨representative, hrepresentative, hclose⟩ := hcover source
  refine ⟨representative, ?_, hclose⟩
  apply hcostBound
  exact ⟨representative, hrepresentative, rfl⟩

/-! ## Literal chronological generation cost -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A proof-relevant numerical shadow of source-free chronological
generation.  A realized block costs its literal number of rows; an exact
splice costs the sum. -/
inductive HasLiteralGenerationCost
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    MarkedAbsorptionCylinder ι → ℕ → Prop
  | realized {anchor : QuittingCalibratedTerminalAnchor reward}
      (source : RealizedMarkedAbsorptionCylinder reward anchor) :
      HasLiteralGenerationCost reward
        (MarkedAbsorptionCylinder.ofRealized source) source.block.length
  | splice {outer inner : MarkedAbsorptionCylinder ι}
      {outerCost innerCost : ℕ}
      (houter : HasLiteralGenerationCost reward outer outerCost)
      (hinner : HasLiteralGenerationCost reward inner innerCost)
      (hseam : MarkedAbsorptionCylinder.IsComposable outer inner) :
      HasLiteralGenerationCost reward (outer.compose inner)
        (outerCost + innerCost)

/-- Every chronologically generated cylinder has some finite literal row
cost. -/
theorem exists_literalGenerationCost
    {cylinder : MarkedAbsorptionCylinder ι}
    (hchronology :
      MarkedAbsorptionCylinder.IsChronologicallyGenerated reward cylinder) :
    ∃ cost, HasLiteralGenerationCost reward cylinder cost := by
  induction hchronology with
  | realized source =>
      exact ⟨source.block.length, HasLiteralGenerationCost.realized source⟩
  | splice houter hinner hseam ihouter ihinner =>
      obtain ⟨outerCost, houterCost⟩ := ihouter
      obtain ⟨innerCost, hinnerCost⟩ := ihinner
      exact ⟨outerCost + innerCost,
        HasLiteralGenerationCost.splice houterCost hinnerCost hseam⟩

/-- A coherent finite semantic path with one retained literal generation-cost
witness. -/
structure CostedFiniteMarkedAbsorptionPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  finite : FiniteMarkedAbsorptionPath reward
  cost : ℕ
  generated : HasLiteralGenerationCost reward finite.1 cost

/-- The cost witnesses over one fixed finite path form an inhabited type. -/
structure LiteralGenerationCostWitness
    (finite : FiniteMarkedAbsorptionPath reward) where
  cost : ℕ
  generated : HasLiteralGenerationCost reward finite.1 cost

theorem nonempty_literalGenerationCostWitness
    (finite : FiniteMarkedAbsorptionPath reward) :
    Nonempty (LiteralGenerationCostWitness finite) := by
  obtain ⟨cost, hcost⟩ :=
    exists_literalGenerationCost finite.2.chronology
  exact ⟨⟨cost, hcost⟩⟩

def chosenLiteralGenerationCostWitness
    (finite : FiniteMarkedAbsorptionPath reward) :
    LiteralGenerationCostWitness finite :=
  Classical.choice (nonempty_literalGenerationCostWitness finite)

/-- Choose one literal generation-cost witness for a coherent finite path. -/
def costedFiniteLift (finite : FiniteMarkedAbsorptionPath reward) :
    CostedFiniteMarkedAbsorptionPath reward :=
  ⟨finite, (chosenLiteralGenerationCostWitness finite).cost,
    (chosenLiteralGenerationCostWitness finite).generated⟩

/-! ## Enriched finite cylinders -/

/-- Number of distinct marked stages retained by the source-free finite
cylinder.  Exact duplicate semantic stages are intentionally counted once. -/
def finiteStageCost (finite : FiniteMarkedAbsorptionPath reward) : ℕ :=
  finite.1.stages.ncard

/-- Every finite coherent cylinder has a uniformly bounded-stage realized
representative close in the complete enriched semantic target. -/
theorem exists_uniform_stageCost_enriched_representative
    (resolution : ℝ) (hresolution : 0 < resolution) :
    ∃ stageBound : ℕ, ∀ finite : FiniteMarkedAbsorptionPath reward,
      ∃ representative : FiniteMarkedAbsorptionPath reward,
        finiteStageCost representative ≤ stageBound ∧
        dist (completeMetrizable finite)
          (completeMetrizable representative) < resolution := by
  exact exists_uniform_cost_approximate_representative
    (completeMetrizable (reward := reward)) finiteStageCost
      resolution hresolution

/-- Strengthening of the preceding result from distinct semantic-stage count
to an actual finite chronological-generation row count. -/
theorem exists_uniform_literalCost_enriched_representative
    (resolution : ℝ) (hresolution : 0 < resolution) :
    ∃ rowBound : ℕ, ∀ finite : FiniteMarkedAbsorptionPath reward,
      ∃ (representative : FiniteMarkedAbsorptionPath reward) (rowCost : ℕ),
        HasLiteralGenerationCost reward representative.1 rowCost ∧
        rowCost ≤ rowBound ∧
        dist (completeMetrizable finite)
          (completeMetrizable representative) < resolution := by
  obtain ⟨rowBound, hrepresentative⟩ :=
    exists_uniform_cost_approximate_representative
      (fun source : CostedFiniteMarkedAbsorptionPath reward =>
        completeMetrizable source.finite)
      (fun source => source.cost) resolution hresolution
  refine ⟨rowBound, ?_⟩
  intro finite
  obtain ⟨representative, hcost, hclose⟩ :=
    hrepresentative (costedFiniteLift finite)
  exact ⟨representative.finite, representative.cost,
    representative.generated, hcost, by
      simpa [costedFiniteLift] using hclose⟩

/-! ## Exact seams compressed jointly with their composition -/

/-- Compact target for the enriched semantics of the outer block, inner
block, and their exact composition. -/
abbrev ExactSeamSemanticTarget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  MetrizableMarkedAbsorptionPath reward ×
    (MetrizableMarkedAbsorptionPath reward ×
      MetrizableMarkedAbsorptionPath reward)

/-- Joint semantic encoding of an actual exact seam. -/
def finiteExactSeamSemanticTarget (seam : FiniteExactSeam reward) :
    ExactSeamSemanticTarget reward :=
  (completeMetrizable seam.outer,
    (completeMetrizable seam.inner,
      completeMetrizable seam.compose))

/-- Total distinct-stage cost of the two inputs to an exact seam. -/
def finiteExactSeamStageCost (seam : FiniteExactSeam reward) : ℕ :=
  finiteStageCost seam.outer + finiteStageCost seam.inner

/-- An exact seam together with literal generation-cost witnesses for both
input cylinders. -/
structure CostedFiniteExactSeam
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  seam : FiniteExactSeam reward
  outerCost : ℕ
  innerCost : ℕ
  outerGenerated :
    HasLiteralGenerationCost reward seam.outer.1 outerCost
  innerGenerated :
    HasLiteralGenerationCost reward seam.inner.1 innerCost

def costedFiniteExactSeamLift (seam : FiniteExactSeam reward) :
    CostedFiniteExactSeam reward :=
  let outer := chosenLiteralGenerationCostWitness seam.outer
  let inner := chosenLiteralGenerationCostWitness seam.inner
  ⟨seam, outer.cost, inner.cost, outer.generated, inner.generated⟩

def costedFiniteExactSeamSemanticTarget
    (seam : CostedFiniteExactSeam reward) :
    ExactSeamSemanticTarget reward :=
  finiteExactSeamSemanticTarget seam.seam

def costedFiniteExactSeamRowCost
    (seam : CostedFiniteExactSeam reward) : ℕ :=
  seam.outerCost + seam.innerCost

/-- There is a nonconstructive uniform stage bound for approximate
representatives chosen from actual exact seams.  The joint target also records
the composed result, so compatibility is not reconstructed from two
independently selected blocks. -/
theorem exists_uniform_stageCost_exactSeamRepresentative
    (resolution : ℝ) (hresolution : 0 < resolution) :
    ∃ stageBound : ℕ, ∀ seam : FiniteExactSeam reward,
      ∃ representative : FiniteExactSeam reward,
        finiteExactSeamStageCost representative ≤ stageBound ∧
        dist (finiteExactSeamSemanticTarget seam)
          (finiteExactSeamSemanticTarget representative) < resolution := by
  exact exists_uniform_cost_approximate_representative
    (finiteExactSeamSemanticTarget (reward := reward))
      finiteExactSeamStageCost resolution hresolution

/-- Literal-row version of exact-seam compression.  The representative seam
comes with actual chronological generation witnesses whose total row cost is
uniformly bounded. -/
theorem exists_uniform_literalCost_exactSeamRepresentative
    (resolution : ℝ) (hresolution : 0 < resolution) :
    ∃ rowBound : ℕ, ∀ seam : FiniteExactSeam reward,
      ∃ (representative : FiniteExactSeam reward)
          (outerCost innerCost : ℕ),
        HasLiteralGenerationCost reward representative.outer.1 outerCost ∧
        HasLiteralGenerationCost reward representative.inner.1 innerCost ∧
        outerCost + innerCost ≤ rowBound ∧
        dist (finiteExactSeamSemanticTarget seam)
          (finiteExactSeamSemanticTarget representative) < resolution := by
  obtain ⟨rowBound, hrepresentative⟩ :=
    exists_uniform_cost_approximate_representative
      (costedFiniteExactSeamSemanticTarget (reward := reward))
      costedFiniteExactSeamRowCost resolution hresolution
  refine ⟨rowBound, ?_⟩
  intro seam
  obtain ⟨representative, hcost, hclose⟩ :=
    hrepresentative (costedFiniteExactSeamLift seam)
  exact ⟨representative.seam, representative.outerCost,
    representative.innerCost, representative.outerGenerated,
    representative.innerGenerated, hcost, hclose⟩

/-- Expanded form: one bounded-complexity exact seam simultaneously
approximates the outer enriched block, the inner enriched block, and their
composed enriched block. -/
theorem exists_exactSeamRepresentative_simultaneous
    (resolution : ℝ) (hresolution : 0 < resolution) :
    ∃ stageBound : ℕ, ∀ seam : FiniteExactSeam reward,
      ∃ representative : FiniteExactSeam reward,
        finiteExactSeamStageCost representative ≤ stageBound ∧
        dist (completeMetrizable seam.outer)
            (completeMetrizable representative.outer) < resolution ∧
        dist (completeMetrizable seam.inner)
            (completeMetrizable representative.inner) < resolution ∧
        dist (completeMetrizable seam.compose)
            (completeMetrizable representative.compose) < resolution := by
  obtain ⟨stageBound, hrepresentative⟩ :=
    exists_uniform_stageCost_exactSeamRepresentative
      (reward := reward) resolution hresolution
  refine ⟨stageBound, ?_⟩
  intro seam
  obtain ⟨representative, hcost, hclose⟩ := hrepresentative seam
  refine ⟨representative, hcost, ?_⟩
  simpa [finiteExactSeamSemanticTarget, Prod.dist_eq, max_lt_iff] using hclose

/-- A concrete projection of the enriched result.  At any requested
exact-D tolerance, one uniformly bounded representative exact seam has close
outer entry/exit and inner entry/exit anchors.  Its own middle seam remains
an exact equality, not an approximate reconstruction. -/
theorem exists_exactSeamRepresentative_anchors_close
    (anchorTolerance : ℝ) (htolerance : 0 < anchorTolerance) :
    ∃ stageBound : ℕ, ∀ seam : FiniteExactSeam reward,
      ∃ representative : FiniteExactSeam reward,
        finiteExactSeamStageCost representative ≤ stageBound ∧
        dist (finiteEntryAnchor seam.outer)
            (finiteEntryAnchor representative.outer) < anchorTolerance ∧
        dist (finiteExitAnchor seam.outer)
            (finiteExitAnchor representative.outer) < anchorTolerance ∧
        dist (finiteEntryAnchor seam.inner)
            (finiteEntryAnchor representative.inner) < anchorTolerance ∧
        dist (finiteExitAnchor seam.inner)
            (finiteExitAnchor representative.inner) < anchorTolerance ∧
        representative.outer.1.exitAnchor =
          representative.inner.1.entryAnchor := by
  have hentryUniform : UniformContinuous
      (metrizableEntryAnchor (reward := reward)) :=
    CompactSpace.uniformContinuous_of_continuous
      continuous_metrizableEntryAnchor
  have hexitUniform : UniformContinuous
      (metrizableExitAnchor (reward := reward)) :=
    CompactSpace.uniformContinuous_of_continuous
      continuous_metrizableExitAnchor
  obtain ⟨entryRadius, hentryRadius, hentry⟩ :=
    (Metric.uniformContinuous_iff.mp hentryUniform)
      anchorTolerance htolerance
  obtain ⟨exitRadius, hexitRadius, hexit⟩ :=
    (Metric.uniformContinuous_iff.mp hexitUniform)
      anchorTolerance htolerance
  let radius := min entryRadius exitRadius
  have hradius : 0 < radius := by
    exact lt_min hentryRadius hexitRadius
  obtain ⟨stageBound, hrepresentative⟩ :=
    exists_exactSeamRepresentative_simultaneous
      (reward := reward) radius hradius
  refine ⟨stageBound, ?_⟩
  intro seam
  obtain ⟨representative, hcost, houter, hinner, _hcomposed⟩ :=
    hrepresentative seam
  have houterEntry := hentry
    (lt_of_lt_of_le houter (min_le_left entryRadius exitRadius))
  have houterExit := hexit
    (lt_of_lt_of_le houter (min_le_right entryRadius exitRadius))
  have hinnerEntry := hentry
    (lt_of_lt_of_le hinner (min_le_left entryRadius exitRadius))
  have hinnerExit := hexit
    (lt_of_lt_of_le hinner (min_le_right entryRadius exitRadius))
  refine ⟨representative, hcost, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using houterEntry
  · simpa using houterExit
  · simpa using hinnerEntry
  · simpa using hinnerExit
  · exact representative.2


end Research.QuittingEnrichedSeamCompression
