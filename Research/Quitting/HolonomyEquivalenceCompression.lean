/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.AllTailRepairValue

/-!
# Exact and approximate strategic classes of finite quitting blocks

Unordered singleton occupation forgets chronology.  Boundary holonomy is the
smallest landed replacement tested here: for every player it retains two
prescribed affine coefficients and three best-response max-affine
coefficients.

This module separates two assertions which should not be conflated.

* Equality of holonomy is an exact equivalence relation on finite root blocks.
  It preserves prescribed finite evaluation, finite Bellman best response,
  and hence boundary regret for every terminal boundary value.
* For every positive resolution, the common compact coefficient box admits a
  finite codebook.  The coordinate Lipschitz estimate converts membership in
  a code cell into a uniform bound on all bounded boundary gains.
* The centers may be chosen from actually realized blocks.  Finiteness then
  gives a nonconstructive uniform length bound, even after restricting to an
  arbitrary source-intrinsic eligible class.

Thus this is an exact finite-dimensional quotient and a finite approximate
semantic realization theorem.  It supplies neither an effective length bound
nor source-relative splice admissibility for unrecorded boundary data.
-/


noncomputable section

namespace Research.QuittingHolonomyEquivalenceCompression

open GameTheory Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A nonempty finite chronological block cut out of an arbitrary root
sequence.  `extra` means that the block has `extra + 1` rows. -/
structure FiniteQuittingBlock (ι : Type) where
  roots : ℕ → ι → PMF Bool
  start : ℕ
  extra : ℕ

/-- The exact five-coordinate-per-player semantic summary of a finite block.
-/
def FiniteQuittingBlock.holonomy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : FiniteQuittingBlock ι) : QuittingBoundaryHolonomy ι :=
  quittingFiniteBoundaryHolonomy reward block.roots block.start block.extra

/-- Exact strategic equivalence of finite blocks at a fixed reward table. -/
def HolonomyEquivalent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : FiniteQuittingBlock ι) : Prop :=
  first.holonomy reward = second.holonomy reward

theorem holonomyEquivalent_equivalence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Equivalence (HolonomyEquivalent reward) := by
  constructor
  · intro block
    rfl
  · intro first second h
    exact h.symm
  · intro first second third h₁ h₂
    exact h₁.trans h₂

omit [Fintype ι] [DecidableEq ι] in
/-- The five raw coordinates lose no information from a bundled holonomy.
They forget source chronology, but not its scalar boundary action. -/
theorem coordinates_injective :
    Function.Injective
      (QuittingBoundaryHolonomy.coordinates :
        QuittingBoundaryHolonomy ι →
          QuittingBoundaryHolonomyCoordinates ι) := by
  intro first second hcoordinates
  apply QuittingBoundaryHolonomy.ext
  · funext who
    apply QuittingAffineSummary.ext
    · exact congrArg (fun coordinates => (coordinates.1 who).1) hcoordinates
    · exact congrArg (fun coordinates => (coordinates.1 who).2) hcoordinates
  · funext who
    apply QuittingMaxAffineSummary.ext
    · exact congrArg (fun coordinates => (coordinates.2 who).1) hcoordinates
    · exact congrArg (fun coordinates => (coordinates.2 who).2.1) hcoordinates
    · exact congrArg (fun coordinates => (coordinates.2 who).2.2) hcoordinates

theorem holonomyEquivalent_iff_coordinates_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : FiniteQuittingBlock ι) :
    HolonomyEquivalent reward first second ↔
      (first.holonomy reward).coordinates =
        (second.holonomy reward).coordinates := by
  constructor
  · exact congrArg QuittingBoundaryHolonomy.coordinates
  · intro hcoordinates
    exact coordinates_injective (ι := ι) hcoordinates

/-- Exact holonomy equivalence preserves prescribed policy evaluation for
every player and every terminal continuation value. -/
theorem finiteTerminalHazardValue_eq_of_holonomyEquivalent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : FiniteQuittingBlock ι)
    (h : HolonomyEquivalent reward first second)
    (who : ι) (terminalValue : ℝ) :
    quittingFiniteTerminalHazardValue reward first.roots who
        (fun time => first.roots time who) terminalValue first.start
        (first.extra + 1) =
      quittingFiniteTerminalHazardValue reward second.roots who
        (fun time => second.roots time who) terminalValue second.start
        (second.extra + 1) := by
  rw [← quittingFiniteBoundaryHolonomy_prescribed_eval,
    ← quittingFiniteBoundaryHolonomy_prescribed_eval]
  have heval := congrArg
    (fun holonomy : QuittingBoundaryHolonomy ι =>
      (holonomy.prescribed who).eval terminalValue) h
  simpa [FiniteQuittingBlock.holonomy] using heval

/-- Exact holonomy equivalence preserves the full finite Bellman stopping
value for every player and every terminal unilateral value. -/
theorem finiteTerminalBestResponseValue_eq_of_holonomyEquivalent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : FiniteQuittingBlock ι)
    (h : HolonomyEquivalent reward first second)
    (who : ι) (terminalValue : ℝ) :
    quittingFiniteTerminalBestResponseValue reward first.roots who
        terminalValue first.start (first.extra + 1) =
      quittingFiniteTerminalBestResponseValue reward second.roots who
        terminalValue second.start (second.extra + 1) := by
  rw [← quittingFiniteBoundaryHolonomy_bestResponse_eval,
    ← quittingFiniteBoundaryHolonomy_bestResponse_eval]
  have heval := congrArg
    (fun holonomy : QuittingBoundaryHolonomy ι =>
      (holonomy.bestResponse who).eval terminalValue) h
  simpa [FiniteQuittingBlock.holonomy] using heval

/-- Consequently exact holonomy equivalence preserves every boundary regret
calculation, including an arbitrary supplied terminal debt `beta`. -/
theorem finiteBoundaryGap_eq_of_holonomyEquivalent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : FiniteQuittingBlock ι)
    (h : HolonomyEquivalent reward first second)
    (who : ι) (beta terminalValue : ℝ) :
    (first.holonomy reward).gap who beta terminalValue =
      (second.holonomy reward).gap who beta terminalValue := by
  rw [h]

/-! ## Finite approximate classes -/

/-- Every point of the coefficient box bundles into a legitimate
affine/max-affine holonomy.  It need not be realized by a quitting word. -/
def holonomyOfBoxCoordinate
    (coefficientBound : ℝ)
    (coordinates : QuittingBoundaryHolonomyCoordinates ι)
    (hcoordinates : coordinates ∈
      quittingBoundaryHolonomyCoefficientBox ι coefficientBound) :
    QuittingBoundaryHolonomy ι where
  prescribed who := {
    intercept := (coordinates.1 who).1
    survival := (coordinates.1 who).2
    survival_nonneg :=
      (hcoordinates.1 who (Set.mem_univ who)).2.1 }
  bestResponse who := {
    early := (coordinates.2 who).1
    tail := (coordinates.2 who).2.1
    survival := (coordinates.2 who).2.2
    survival_nonneg :=
      (hcoordinates.2 who (Set.mem_univ who)).2.2.1 }

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem holonomyOfBoxCoordinate_coordinates
    (coefficientBound : ℝ)
    (coordinates : QuittingBoundaryHolonomyCoordinates ι)
    (hcoordinates : coordinates ∈
      quittingBoundaryHolonomyCoefficientBox ι coefficientBound) :
    (holonomyOfBoxCoordinate coefficientBound coordinates hcoordinates).coordinates =
      coordinates := by
  rfl

omit [DecidableEq ι] in
/-- Sup-metric closeness of the five coordinate families controls the
weighted coordinate distance used by the boundary-gain Lipschitz theorem. -/
theorem coordinateDistance_lt_of_coordinates_dist_lt
    (continuationBound resolution : ℝ)
    (hbound : 0 ≤ continuationBound)
    (first second : QuittingBoundaryHolonomy ι)
    (hclose : dist first.coordinates second.coordinates < resolution)
    (who : ι) :
    first.coordinateDistance continuationBound second who <
      (3 + 2 * continuationBound) * resolution := by
  have hresolution : 0 < resolution :=
    lt_of_le_of_lt dist_nonneg hclose
  rw [Prod.dist_eq, max_lt_iff] at hclose
  have hprescribed := (dist_pi_lt_iff hresolution).mp hclose.1 who
  have hbestResponse := (dist_pi_lt_iff hresolution).mp hclose.2 who
  rw [Prod.dist_eq, max_lt_iff] at hprescribed hbestResponse
  have htailSurvival := hbestResponse.2
  rw [Prod.dist_eq, max_lt_iff] at htailSurvival
  have hintercept :
      |(first.prescribed who).intercept -
          (second.prescribed who).intercept| < resolution := by
    simpa [QuittingBoundaryHolonomy.coordinates, Real.dist_eq] using
      hprescribed.1
  have hprescribedSurvival :
      |(first.prescribed who).survival -
          (second.prescribed who).survival| < resolution := by
    simpa [QuittingBoundaryHolonomy.coordinates, Real.dist_eq] using
      hprescribed.2
  have hearly :
      |(first.bestResponse who).early -
          (second.bestResponse who).early| < resolution := by
    simpa [QuittingBoundaryHolonomy.coordinates, Real.dist_eq] using
      hbestResponse.1
  have htail :
      |(first.bestResponse who).tail -
          (second.bestResponse who).tail| < resolution := by
    simpa [QuittingBoundaryHolonomy.coordinates, Real.dist_eq] using
      htailSurvival.1
  have hbestResponseSurvival :
      |(first.bestResponse who).survival -
          (second.bestResponse who).survival| < resolution := by
    simpa [QuittingBoundaryHolonomy.coordinates, Real.dist_eq] using
      htailSurvival.2
  have hweightedBestResponse :
      continuationBound *
          |(first.bestResponse who).survival -
            (second.bestResponse who).survival| ≤
        continuationBound * resolution :=
    mul_le_mul_of_nonneg_left hbestResponseSurvival.le hbound
  have hweightedPrescribed :
      continuationBound *
          |(first.prescribed who).survival -
            (second.prescribed who).survival| ≤
        continuationBound * resolution :=
    mul_le_mul_of_nonneg_left hprescribedSurvival.le hbound
  unfold QuittingBoundaryHolonomy.coordinateDistance
  nlinarith

/-- At every positive resolution there are finitely many approximate
holonomy classes covering every finite quitting block, independently of its
length.  Centers lie in the common coefficient box. -/
theorem exists_finite_holonomy_coordinate_codebook
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (resolution : ℝ) (hresolution : 0 < resolution) :
    ∃ codebook : Set (QuittingBoundaryHolonomyCoordinates ι),
      codebook ⊆ quittingBoundaryHolonomyCoefficientBox ι
          (quittingRewardBound reward) ∧
      codebook.Finite ∧
      ∀ block : FiniteQuittingBlock ι,
        ∃ code ∈ codebook,
          dist (block.holonomy reward).coordinates code < resolution := by
  obtain ⟨codebook, hsubset, hfinite, hcover⟩ :=
    (isCompact_quittingBoundaryHolonomyCoefficientBox
      ι (quittingRewardBound reward)).finite_cover_balls hresolution
  refine ⟨codebook, hsubset, hfinite, ?_⟩
  intro block
  have hmem : (block.holonomy reward).coordinates ∈
      quittingBoundaryHolonomyCoefficientBox ι
        (quittingRewardBound reward) := by
    exact quittingFiniteBoundaryHolonomy_coordinates_mem_box
      reward block.roots block.start block.extra
  rcases Set.mem_iUnion.mp (hcover hmem) with ⟨code, hcodeCover⟩
  rcases Set.mem_iUnion.mp hcodeCover with ⟨hcode, hball⟩
  exact ⟨code, hcode, by simpa only [Metric.mem_ball] using hball⟩

/-- Coordinates which are actually generated by some finite common root
block. -/
def realizedFiniteHolonomyCoordinates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingBoundaryHolonomyCoordinates ι) :=
  {coordinates | ∃ block : FiniteQuittingBlock ι,
    (block.holonomy reward).coordinates = coordinates}

theorem realizedFiniteHolonomyCoordinates_subset_box
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    realizedFiniteHolonomyCoordinates reward ⊆
      quittingBoundaryHolonomyCoefficientBox ι
        (quittingRewardBound reward) := by
  rintro coordinates ⟨block, rfl⟩
  exact quittingFiniteBoundaryHolonomy_coordinates_mem_box
    reward block.roots block.start block.extra

/-- The approximate code centers can be chosen from the realized subset,
even though that subset need not be closed. -/
theorem exists_finite_realized_holonomy_coordinate_codebook
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (resolution : ℝ) (hresolution : 0 < resolution) :
    ∃ codebook : Set (QuittingBoundaryHolonomyCoordinates ι),
      codebook ⊆ realizedFiniteHolonomyCoordinates reward ∧
      codebook.Finite ∧
      ∀ block : FiniteQuittingBlock ι,
        ∃ code ∈ codebook,
          dist (block.holonomy reward).coordinates code < resolution := by
  have hboxCompact := isCompact_quittingBoundaryHolonomyCoefficientBox
    ι (quittingRewardBound reward)
  have hclosureCompact :
      IsCompact (closure (realizedFiniteHolonomyCoordinates reward)) :=
    hboxCompact.of_isClosed_subset isClosed_closure
      (closure_minimal
        (realizedFiniteHolonomyCoordinates_subset_box reward)
        hboxCompact.isClosed)
  obtain ⟨codebook, hsubset, hfinite, hcover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure
      hclosureCompact hresolution
  refine ⟨codebook, hsubset, hfinite, ?_⟩
  intro block
  have hrealized : (block.holonomy reward).coordinates ∈
      realizedFiniteHolonomyCoordinates reward := ⟨block, rfl⟩
  rcases Set.mem_iUnion.mp (hcover hrealized) with ⟨code, hcodeCover⟩
  rcases Set.mem_iUnion.mp hcodeCover with ⟨hcode, hball⟩
  exact ⟨code, hcode, by simpa only [Metric.mem_ball] using hball⟩

/-- Every finite block is close to one member of a finite set of genuinely
realized finite blocks. -/
theorem exists_finite_realized_block_codebook
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (resolution : ℝ) (hresolution : 0 < resolution) :
    ∃ representatives : Set (FiniteQuittingBlock ι),
      representatives.Finite ∧
      ∀ block : FiniteQuittingBlock ι,
        ∃ representative ∈ representatives,
          dist (block.holonomy reward).coordinates
            (representative.holonomy reward).coordinates < resolution := by
  obtain ⟨codebook, hrealized, hfinite, hcover⟩ :=
    exists_finite_realized_holonomy_coordinate_codebook
      reward resolution hresolution
  let representative : {code // code ∈ codebook} → FiniteQuittingBlock ι :=
    fun code => Classical.choose (hrealized code.2)
  have hrepresentative (code : {code // code ∈ codebook}) :
      ((representative code).holonomy reward).coordinates = code.1 :=
    Classical.choose_spec (hrealized code.2)
  let representatives : Set (FiniteQuittingBlock ι) :=
    Set.range representative
  have hrepresentativesFinite : representatives.Finite := by
    letI : Fintype {code // code ∈ codebook} := hfinite.fintype
    exact Set.finite_range representative
  refine ⟨representatives, hrepresentativesFinite, ?_⟩
  intro block
  obtain ⟨code, hcode, hclose⟩ := hcover block
  let indexedCode : {code // code ∈ codebook} := ⟨code, hcode⟩
  refine ⟨representative indexedCode, ?_, ?_⟩
  · exact ⟨indexedCode, rfl⟩
  · rw [hrepresentative indexedCode]
    exact hclose

/-- **Nonconstructive bounded-length realization.**  At every positive
coordinate resolution there is a uniform row bound, independent of the
source horizon, such that every finite block is close to a block obeying that
bound.  No effective formula for the bound is asserted. -/
theorem exists_uniform_length_approximate_holonomy_representative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (resolution : ℝ) (hresolution : 0 < resolution) :
    ∃ rowBound : ℕ, ∀ block : FiniteQuittingBlock ι,
      ∃ representative : FiniteQuittingBlock ι,
        representative.extra + 1 ≤ rowBound ∧
        dist (block.holonomy reward).coordinates
          (representative.holonomy reward).coordinates < resolution := by
  obtain ⟨representatives, hfinite, hcover⟩ :=
    exists_finite_realized_block_codebook reward resolution hresolution
  have hlengthsFinite :
      ((fun block : FiniteQuittingBlock ι => block.extra + 1) ''
        representatives).Finite := hfinite.image _
  obtain ⟨rowBound, hrowBound⟩ := hlengthsFinite.bddAbove
  refine ⟨rowBound, ?_⟩
  intro block
  obtain ⟨representative, hrepresentative, hclose⟩ := hcover block
  refine ⟨representative, ?_, hclose⟩
  apply hrowBound
  exact ⟨representative, hrepresentative, rfl⟩

/-- The compactness argument works inside any chosen class of source blocks.
Thus every source-intrinsic constraint can be retained by the finite
representatives; what this does not retain is a relation between a source and
its replacement, such as an unrecorded seam anchor. -/
theorem exists_finite_eligible_block_codebook
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (eligible : Set (FiniteQuittingBlock ι))
    (resolution : ℝ) (hresolution : 0 < resolution) :
    ∃ representatives : Set (FiniteQuittingBlock ι),
      representatives.Finite ∧
      representatives ⊆ eligible ∧
      ∀ block ∈ eligible,
        ∃ representative ∈ representatives,
          dist (block.holonomy reward).coordinates
            (representative.holonomy reward).coordinates < resolution := by
  let realized : Set (QuittingBoundaryHolonomyCoordinates ι) :=
    (fun block : FiniteQuittingBlock ι =>
      (block.holonomy reward).coordinates) '' eligible
  have hrealizedBox : realized ⊆
      quittingBoundaryHolonomyCoefficientBox ι
        (quittingRewardBound reward) := by
    rintro coordinates ⟨block, _hblock, rfl⟩
    exact quittingFiniteBoundaryHolonomy_coordinates_mem_box
      reward block.roots block.start block.extra
  have hboxCompact := isCompact_quittingBoundaryHolonomyCoefficientBox
    ι (quittingRewardBound reward)
  have hclosureCompact : IsCompact (closure realized) :=
    hboxCompact.of_isClosed_subset isClosed_closure
      (closure_minimal hrealizedBox hboxCompact.isClosed)
  obtain ⟨codebook, hcodesRealized, hcodesFinite, hcover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure
      hclosureCompact hresolution
  let representative : {code // code ∈ codebook} → FiniteQuittingBlock ι :=
    fun code => Classical.choose (hcodesRealized code.2)
  have hrepresentativeEligible (code : {code // code ∈ codebook}) :
      representative code ∈ eligible :=
    (Classical.choose_spec (hcodesRealized code.2)).1
  have hrepresentativeCoordinates (code : {code // code ∈ codebook}) :
      ((representative code).holonomy reward).coordinates = code.1 :=
    (Classical.choose_spec (hcodesRealized code.2)).2
  let representatives : Set (FiniteQuittingBlock ι) :=
    Set.range representative
  have hrepresentativesFinite : representatives.Finite := by
    letI : Fintype {code // code ∈ codebook} := hcodesFinite.fintype
    exact Set.finite_range representative
  refine ⟨representatives, hrepresentativesFinite, ?_, ?_⟩
  · rintro block ⟨code, rfl⟩
    exact hrepresentativeEligible code
  · intro block hblock
    have hrealized : (block.holonomy reward).coordinates ∈ realized :=
      ⟨block, hblock, rfl⟩
    rcases Set.mem_iUnion.mp (hcover hrealized) with ⟨code, hcodeCover⟩
    rcases Set.mem_iUnion.mp hcodeCover with ⟨hcode, hball⟩
    let indexedCode : {code // code ∈ codebook} := ⟨code, hcode⟩
    refine ⟨representative indexedCode, ⟨indexedCode, rfl⟩, ?_⟩
    rw [hrepresentativeCoordinates indexedCode]
    simpa only [Metric.mem_ball] using hball

/-- Every source-intrinsic eligible class has a nonconstructive uniform
length bound for approximate holonomy representatives inside that same
class. -/
theorem exists_uniform_length_eligible_holonomy_representative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (eligible : Set (FiniteQuittingBlock ι))
    (resolution : ℝ) (hresolution : 0 < resolution) :
    ∃ rowBound : ℕ, ∀ block ∈ eligible,
      ∃ representative ∈ eligible,
        representative.extra + 1 ≤ rowBound ∧
        dist (block.holonomy reward).coordinates
          (representative.holonomy reward).coordinates < resolution := by
  obtain ⟨representatives, hfinite, heligible, hcover⟩ :=
    exists_finite_eligible_block_codebook
      reward eligible resolution hresolution
  have hlengthsFinite :
      ((fun block : FiniteQuittingBlock ι => block.extra + 1) ''
        representatives).Finite := hfinite.image _
  obtain ⟨rowBound, hrowBound⟩ := hlengthsFinite.bddAbove
  refine ⟨rowBound, ?_⟩
  intro block hblock
  obtain ⟨representative, hrepresentative, hclose⟩ := hcover block hblock
  refine ⟨representative, heligible hrepresentative, ?_, hclose⟩
  apply hrowBound
  exact ⟨representative, hrepresentative, rfl⟩

/-- The bounded-length realized representative also approximates every
bounded boundary gain uniformly over players and attached continuation
values. -/
theorem exists_uniform_length_boundary_gain_representative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuationBound resolution : ℝ)
    (hbound : 0 ≤ continuationBound)
    (hresolution : 0 < resolution) :
    ∃ rowBound : ℕ, ∀ block : FiniteQuittingBlock ι,
      ∃ representative : FiniteQuittingBlock ι,
        representative.extra + 1 ≤ rowBound ∧
        ∀ (v w : ι → ℝ),
          (∀ who, |v who| ≤ continuationBound) →
          (∀ who, |w who| ≤ continuationBound) →
          ∀ who,
            |(block.holonomy reward).coRealizedGain v w who -
              (representative.holonomy reward).coRealizedGain v w who| <
                (3 + 2 * continuationBound) * resolution := by
  obtain ⟨rowBound, hrepresentative⟩ :=
    exists_uniform_length_approximate_holonomy_representative
      reward resolution hresolution
  refine ⟨rowBound, ?_⟩
  intro block
  obtain ⟨representative, hlength, hclose⟩ := hrepresentative block
  refine ⟨representative, hlength, ?_⟩
  intro v w hv hw who
  have hdistance :
      (block.holonomy reward).coordinateDistance continuationBound
          (representative.holonomy reward) who <
        (3 + 2 * continuationBound) * resolution :=
    coordinateDistance_lt_of_coordinates_dist_lt
      continuationBound resolution hbound
        (block.holonomy reward) (representative.holonomy reward) hclose who
  exact (QuittingBoundaryHolonomy.coRealizedGain_lipschitz
    continuationBound (block.holonomy reward)
      (representative.holonomy reward) v w hv hw who).trans_lt hdistance

/-- Boundary gain computed directly from five raw coordinates. -/
def coordinateBoundaryGain
    (coordinates : QuittingBoundaryHolonomyCoordinates ι)
    (v w : ι → ℝ) (who : ι) : ℝ :=
  max (coordinates.2 who).1
      ((coordinates.2 who).2.1 + (coordinates.2 who).2.2 * w who) -
    ((coordinates.1 who).1 + (coordinates.1 who).2 * v who)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coRealizedGain_eq_coordinateBoundaryGain
    (holonomy : QuittingBoundaryHolonomy ι)
    (v w : ι → ℝ) (who : ι) :
    holonomy.coRealizedGain v w who =
      coordinateBoundaryGain holonomy.coordinates v w who := by
  rfl

/-- The finite coordinate codebook is strategically meaningful: on any
bounded continuation box, every actual finite block is uniformly close to
one code center for every player's boundary gain. -/
theorem exists_finite_boundary_gain_codebook
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuationBound resolution : ℝ)
    (hbound : 0 ≤ continuationBound)
    (hresolution : 0 < resolution) :
    ∃ codebook : Set (QuittingBoundaryHolonomyCoordinates ι),
      codebook ⊆ quittingBoundaryHolonomyCoefficientBox ι
          (quittingRewardBound reward) ∧
      codebook.Finite ∧
      ∀ block : FiniteQuittingBlock ι,
        ∃ code ∈ codebook,
          dist (block.holonomy reward).coordinates code < resolution ∧
          ∀ (v w : ι → ℝ),
            (∀ who, |v who| ≤ continuationBound) →
            (∀ who, |w who| ≤ continuationBound) →
            ∀ who,
              |(block.holonomy reward).coRealizedGain v w who -
                coordinateBoundaryGain code v w who| <
                (3 + 2 * continuationBound) * resolution := by
  obtain ⟨codebook, hsubset, hfinite, hcover⟩ :=
    exists_finite_holonomy_coordinate_codebook reward resolution hresolution
  refine ⟨codebook, hsubset, hfinite, ?_⟩
  intro block
  obtain ⟨code, hcode, hclose⟩ := hcover block
  have hcodeBox := hsubset hcode
  refine ⟨code, hcode, hclose, ?_⟩
  intro v w hv hw who
  let center := holonomyOfBoxCoordinate
    (quittingRewardBound reward) code hcodeBox
  have hdistance :
      (block.holonomy reward).coordinateDistance continuationBound center who <
        (3 + 2 * continuationBound) * resolution := by
    apply coordinateDistance_lt_of_coordinates_dist_lt
      continuationBound resolution hbound
    simpa [center] using hclose
  have hgain := (QuittingBoundaryHolonomy.coRealizedGain_lipschitz
    continuationBound (block.holonomy reward) center v w hv hw who).trans_lt
      hdistance
  simpa [center, coordinateBoundaryGain] using hgain


end Research.QuittingHolonomyEquivalenceCompression
