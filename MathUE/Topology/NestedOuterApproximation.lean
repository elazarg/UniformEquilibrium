/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Quantitative nested outer approximation

This file isolates the game-independent topology behind finite-center outer
hierarchies.  A sequence of compact center sets approximates every point of an
attainable set with a radius tending to zero, while every center retains
provenance in the attainable closure.  The finite intersections of the
corresponding closed distance neighborhoods then decrease exactly to that
closure.

For a continuous objective with an explicit distance modulus, its infima on
the outer set and on the last center set give a certified bracket.  This file
does not assert that the center sets have semialgebraic presentations.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Math
namespace Topology

variable {Point : Type*} [PseudoMetricSpace Point]

/-- Data sufficient for a shrinking nested hierarchy of compact centers. -/
structure NestedOuterApproximation (Point : Type*) [PseudoMetricSpace Point] where
  /-- The points supplied by executable or otherwise concrete data. -/
  attainable : Set Point
  /-- The compact center at resolution `level`. -/
  center : ℕ → Set Point
  /-- The certified approximation radius at each resolution. -/
  radius : ℕ → ℝ
  attainable_nonempty : attainable.Nonempty
  center_nonempty : ∀ level, (center level).Nonempty
  center_compact : ∀ level, IsCompact (center level)
  center_subset_closure : ∀ level, center level ⊆ closure attainable
  radius_nonneg : ∀ level, 0 ≤ radius level
  radius_tendsto_zero : Tendsto radius atTop (𝓝 0)
  attainable_infDist_le : ∀ point ∈ attainable, ∀ level,
    0 < level → Metric.infDist point (center level) ≤ radius level

namespace NestedOuterApproximation

variable (system : NestedOuterApproximation Point)

/-- The closed outer neighborhood at one positive resolution level. -/
def outerNeighborhood (level : ℕ) : Set Point :=
  {point | Metric.infDist point (system.center level) ≤ system.radius level}

/-- The finite intersection of all positive outer neighborhoods through
`horizon`.  At horizon zero there are no constraints. -/
def nestedOuter (horizon : ℕ) : Set Point :=
  {point | ∀ level, 0 < level → level ≤ horizon →
    point ∈ system.outerNeighborhood level}

theorem outerNeighborhood_isClosed (level : ℕ) :
    IsClosed (system.outerNeighborhood level) := by
  exact isClosed_le (Metric.continuous_infDist_pt (system.center level))
    continuous_const

theorem attainable_subset_outerNeighborhood {level : ℕ} (hlevel : 0 < level) :
    system.attainable ⊆ system.outerNeighborhood level := by
  intro point hpoint
  exact system.attainable_infDist_le point hpoint level hlevel

theorem closure_attainable_subset_outerNeighborhood
    {level : ℕ} (hlevel : 0 < level) :
    closure system.attainable ⊆ system.outerNeighborhood level := by
  exact closure_minimal
    (system.attainable_subset_outerNeighborhood hlevel)
    (system.outerNeighborhood_isClosed level)

theorem closure_attainable_subset_nestedOuter (horizon : ℕ) :
    closure system.attainable ⊆ system.nestedOuter horizon := by
  intro point hpoint level hlevel _
  exact system.closure_attainable_subset_outerNeighborhood hlevel hpoint

theorem attainable_subset_nestedOuter (horizon : ℕ) :
    system.attainable ⊆ system.nestedOuter horizon :=
  subset_closure.trans (system.closure_attainable_subset_nestedOuter horizon)

theorem center_subset_nestedOuter (centerLevel horizon : ℕ) :
    system.center centerLevel ⊆ system.nestedOuter horizon :=
  (system.center_subset_closure centerLevel).trans
    (system.closure_attainable_subset_nestedOuter horizon)

theorem nestedOuter_succ_subset (horizon : ℕ) :
    system.nestedOuter (horizon + 1) ⊆ system.nestedOuter horizon := by
  intro point hpoint level hlevel hle
  exact hpoint level hlevel (hle.trans (Nat.le_succ horizon))

theorem nestedOuter_antitone : Antitone system.nestedOuter := by
  intro first second hle point hpoint level hlevel hlevelFirst
  exact hpoint level hlevel (hlevelFirst.trans hle)

theorem nestedOuter_isClosed (horizon : ℕ) :
    IsClosed (system.nestedOuter horizon) := by
  rw [show system.nestedOuter horizon =
      ⋂ level : Fin (horizon + 1),
        if 0 < level.1 then system.outerNeighborhood level.1 else Set.univ by
    ext point
    simp only [nestedOuter, mem_setOf_eq, mem_iInter,
      mem_ite_univ_right]
    constructor
    · intro h level hlevel
      exact h level.1 hlevel (Nat.le_of_lt_succ level.2)
    · intro h level hlevel hle
      exact h ⟨level, Nat.lt_succ_iff.mpr hle⟩ hlevel]
  exact isClosed_iInter fun level => by
    split_ifs
    · exact system.outerNeighborhood_isClosed level.1
    · exact isClosed_univ

/-- Membership in every finite outer intersection is exactly membership in
the attainable closure.  No realization of a closure point is inferred. -/
theorem mem_closure_attainable_iff_mem_all_nestedOuter (point : Point) :
    point ∈ closure system.attainable ↔
      ∀ horizon, point ∈ system.nestedOuter horizon := by
  constructor
  · intro hpoint horizon
    exact system.closure_attainable_subset_nestedOuter horizon hpoint
  · intro hpoint
    have hdist_le : ∀ level, 0 < level →
        Metric.infDist point (closure system.attainable) ≤
          system.radius level := by
      intro level hlevel
      calc
        Metric.infDist point (closure system.attainable) ≤
            Metric.infDist point (system.center level) :=
          Metric.infDist_le_infDist_of_subset
            (system.center_subset_closure level)
            (system.center_nonempty level)
        _ ≤ system.radius level :=
          hpoint level level hlevel (le_refl level)
    have hdist_nonpos : Metric.infDist point (closure system.attainable) ≤ 0 := by
      apply ge_of_tendsto'
        (system.radius_tendsto_zero.comp (tendsto_add_atTop_nat 1))
      intro level
      exact hdist_le (level + 1) (Nat.zero_lt_succ level)
    have hdist_zero : Metric.infDist point system.attainable = 0 := by
      rw [← Metric.infDist_closure]
      exact le_antisymm hdist_nonpos Metric.infDist_nonneg
    exact (Metric.mem_closure_iff_infDist_zero
      system.attainable_nonempty).mpr hdist_zero

theorem iInter_nestedOuter :
    (⋂ horizon, system.nestedOuter horizon) = closure system.attainable := by
  ext point
  simp only [mem_iInter]
  exact (system.mem_closure_attainable_iff_mem_all_nestedOuter point).symm

section Objective

variable (score : Point → ℝ)

/-- The objective infimum on the executable set. -/
def attainableInf : ℝ := sInf (score '' system.attainable)

/-- The certified lower objective at one finite outer horizon. -/
def lowerValue (horizon : ℕ) : ℝ :=
  sInf (score '' system.nestedOuter horizon)

/-- The upper objective supplied by the final compact center. -/
def upperValue (level : ℕ) : ℝ :=
  sInf (score '' system.center level)

variable {floor modulus : ℝ}

omit [PseudoMetricSpace Point] in
private theorem score_image_bddBelow
    (hscoreFloor : ∀ point, floor ≤ score point) (set : Set Point) :
    BddBelow (score '' set) := by
  exact ⟨floor, by rintro value ⟨point, -, rfl⟩; exact hscoreFloor point⟩

theorem floor_le_lowerValue
    (hscoreFloor : ∀ point, floor ≤ score point) (horizon : ℕ) :
    floor ≤ system.lowerValue score horizon := by
  apply le_csInf
  · exact (system.attainable_nonempty.mono
      (system.attainable_subset_nestedOuter horizon)).image score
  · rintro value ⟨point, -, rfl⟩
    exact hscoreFloor point

theorem floor_le_upperValue
    (hscoreFloor : ∀ point, floor ≤ score point) (level : ℕ) :
    floor ≤ system.upperValue score level := by
  apply le_csInf
  · exact (system.center_nonempty level).image score
  · rintro value ⟨point, -, rfl⟩
    exact hscoreFloor point

/-- The upper value is attained by a literal point of the compact center. -/
theorem exists_mem_center_score_eq_upperValue
    (hscoreContinuous : Continuous score) (level : ℕ) :
    ∃ point ∈ system.center level,
      score point = system.upperValue score level := by
  obtain ⟨point, hpoint, hsInf, -⟩ :=
    (system.center_compact level).exists_sInf_image_eq_and_le
      (system.center_nonempty level) hscoreContinuous.continuousOn
  exact ⟨point, hpoint, hsInf.symm⟩

private theorem attainableInf_le_of_mem_closure
    (hscoreFloor : ∀ point, floor ≤ score point)
    (hscoreContinuous : Continuous score)
    {point : Point} (hpoint : point ∈ closure system.attainable) :
    system.attainableInf score ≤ score point := by
  let upper : Set Point :=
    {candidate | system.attainableInf score ≤ score candidate}
  have hclosed : IsClosed upper :=
    isClosed_le continuous_const hscoreContinuous
  have hattainable : system.attainable ⊆ upper := by
    intro candidate hcandidate
    exact csInf_le (score_image_bddBelow score hscoreFloor
      system.attainable) ⟨candidate, hcandidate, rfl⟩
  exact (closure_minimal hattainable hclosed) hpoint

theorem lowerValue_le_attainableInf
    (hscoreFloor : ∀ point, floor ≤ score point) (horizon : ℕ) :
    system.lowerValue score horizon ≤ system.attainableInf score := by
  apply le_csInf
  · exact (system.attainable_nonempty.image score)
  · rintro value ⟨point, hpoint, rfl⟩
    exact csInf_le
      (score_image_bddBelow score hscoreFloor
        (system.nestedOuter horizon))
      ⟨point, system.attainable_subset_nestedOuter horizon hpoint, rfl⟩

theorem attainableInf_le_upperValue
    (hscoreFloor : ∀ point, floor ≤ score point)
    (hscoreContinuous : Continuous score) (level : ℕ) :
    system.attainableInf score ≤ system.upperValue score level := by
  apply le_csInf
  · exact (system.center_nonempty level).image score
  · rintro value ⟨point, hpoint, rfl⟩
    exact system.attainableInf_le_of_mem_closure score hscoreFloor
      hscoreContinuous (system.center_subset_closure level hpoint)

theorem upperValue_sub_lowerValue_le
    (hscoreFloor : ∀ point, floor ≤ score point)
    (hmodulusNonneg : 0 ≤ modulus)
    (hscoreModulus : ∀ first second,
      |score first - score second| ≤ modulus * dist first second)
    {level : ℕ} (hlevel : 0 < level) :
    system.upperValue score level - system.lowerValue score level ≤
      modulus * system.radius level := by
  have houterNonempty : (system.nestedOuter level).Nonempty :=
    system.attainable_nonempty.mono
      (system.attainable_subset_nestedOuter level)
  have hlower : system.upperValue score level - modulus * system.radius level ≤
      system.lowerValue score level := by
    apply le_csInf (houterNonempty.image score)
    rintro value ⟨point, hpoint, rfl⟩
    have hneighborhood := hpoint level hlevel (le_refl level)
    obtain ⟨center, hcenter, hnearest⟩ :=
      (system.center_compact level).exists_infDist_eq_dist
        (system.center_nonempty level) point
    have hcenterUpper : system.upperValue score level ≤ score center :=
      csInf_le (score_image_bddBelow score hscoreFloor
        (system.center level)) ⟨center, hcenter, rfl⟩
    have hscoreClose : score center ≤
        score point + modulus * system.radius level := by
      have habs := hscoreModulus center point
      have hdist : dist center point ≤ system.radius level := by
        rw [dist_comm, ← hnearest]
        exact hneighborhood
      have hmul : modulus * dist center point ≤
          modulus * system.radius level :=
        mul_le_mul_of_nonneg_left hdist hmodulusNonneg
      have hsigned : score center - score point ≤
          modulus * system.radius level :=
        (le_abs_self _).trans (habs.trans hmul)
      linarith
    linarith
  linarith

theorem quantitative_bracket
    (hscoreFloor : ∀ point, floor ≤ score point)
    (hscoreContinuous : Continuous score)
    (hmodulusNonneg : 0 ≤ modulus)
    (hscoreModulus : ∀ first second,
      |score first - score second| ≤ modulus * dist first second)
    {level : ℕ} (hlevel : 0 < level) :
    system.lowerValue score level ≤ system.attainableInf score ∧
    system.attainableInf score ≤ system.upperValue score level ∧
    system.upperValue score level - system.lowerValue score level ≤
      modulus * system.radius level := by
  exact ⟨system.lowerValue_le_attainableInf score hscoreFloor level,
    system.attainableInf_le_upperValue score hscoreFloor hscoreContinuous level,
    system.upperValue_sub_lowerValue_le score hscoreFloor hmodulusNonneg
      hscoreModulus hlevel⟩

end Objective

end NestedOuterApproximation
end Topology
end Math
