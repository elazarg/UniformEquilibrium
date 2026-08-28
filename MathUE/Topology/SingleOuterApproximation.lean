/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import MathUE.Topology.NestedOuterApproximation

/-!
# One-shell quantitative outer approximation

The cumulative hierarchy is useful for convergence, but a fixed-accuracy
resolver needs only one positive-resolution shell.  This file gives that
single shell its own lower value and proves the same sharp quantitative
bracket.  It does not assert nesting or convergence of the single shells.
-/

namespace Math.Topology

open Filter Set
open scoped Topology

noncomputable section

variable {Point : Type*} [PseudoMetricSpace Point]

namespace NestedOuterApproximation

variable (system : NestedOuterApproximation Point)

omit [PseudoMetricSpace Point] in
private theorem shellScoreImage_bddBelow
    (score : Point → ℝ) (floor : ℝ)
    (hscoreFloor : ∀ point, floor ≤ score point) (set : Set Point) :
    BddBelow (score '' set) := by
  exact ⟨floor, by rintro value ⟨point, -, rfl⟩; exact hscoreFloor point⟩

/-- Minimum score on one closed outer neighborhood. -/
def shellLowerValue (score : Point → ℝ) (level : ℕ) : ℝ :=
  sInf (score '' system.outerNeighborhood level)

/-- One-shell lower values inherit a pointwise score floor. -/
theorem floor_le_shellLowerValue
    (score : Point → ℝ) (floor : ℝ)
    (hscoreFloor : ∀ point, floor ≤ score point)
    {level : ℕ} (hlevel : 0 < level) :
    floor ≤ system.shellLowerValue score level := by
  apply le_csInf
  · exact (system.attainable_nonempty.mono
      (system.attainable_subset_outerNeighborhood hlevel)).image score
  · rintro value ⟨point, -, rfl⟩
    exact hscoreFloor point

/-- The one-shell lower value is below the attainable infimum. -/
theorem shellLowerValue_le_attainableInf
    (score : Point → ℝ) (floor : ℝ)
    (hscoreFloor : ∀ point, floor ≤ score point)
    {level : ℕ} (hlevel : 0 < level) :
    system.shellLowerValue score level ≤ system.attainableInf score := by
  apply le_csInf
  · exact system.attainable_nonempty.image score
  · rintro value ⟨point, hpoint, rfl⟩
    exact csInf_le
      (shellScoreImage_bddBelow score floor hscoreFloor
        (system.outerNeighborhood level))
      ⟨point, system.attainable_subset_outerNeighborhood hlevel hpoint, rfl⟩

/-- The center-to-shell objective gap is controlled by the score modulus. -/
theorem upperValue_sub_shellLowerValue_le
    (score : Point → ℝ) (floor modulus : ℝ)
    (hscoreFloor : ∀ point, floor ≤ score point)
    (hmodulusNonneg : 0 ≤ modulus)
    (hscoreModulus : ∀ first second,
      |score first - score second| ≤ modulus * dist first second)
    {level : ℕ} (hlevel : 0 < level) :
    system.upperValue score level - system.shellLowerValue score level ≤
      modulus * system.radius level := by
  have houterNonempty : (system.outerNeighborhood level).Nonempty :=
    system.attainable_nonempty.mono
      (system.attainable_subset_outerNeighborhood hlevel)
  have hlower : system.upperValue score level - modulus * system.radius level ≤
      system.shellLowerValue score level := by
    apply le_csInf (houterNonempty.image score)
    rintro value ⟨point, hpoint, rfl⟩
    obtain ⟨center, hcenter, hnearest⟩ :=
      (system.center_compact level).exists_infDist_eq_dist
        (system.center_nonempty level) point
    have hcenterUpper : system.upperValue score level ≤ score center :=
      csInf_le (shellScoreImage_bddBelow score floor hscoreFloor
        (system.center level)) ⟨center, hcenter, rfl⟩
    have hscoreClose : score center ≤
        score point + modulus * system.radius level := by
      have habs := hscoreModulus center point
      have hdist : dist center point ≤ system.radius level := by
        rw [dist_comm, ← hnearest]
        exact hpoint
      have hmul : modulus * dist center point ≤
          modulus * system.radius level :=
        mul_le_mul_of_nonneg_left hdist hmodulusNonneg
      have hsigned : score center - score point ≤
          modulus * system.radius level :=
        (le_abs_self _).trans (habs.trans hmul)
      linarith
    linarith
  linarith

/-- Sharp one-shell lower/actual/upper bracket. -/
theorem shell_quantitative_bracket
    (score : Point → ℝ) (floor modulus : ℝ)
    (hscoreFloor : ∀ point, floor ≤ score point)
    (hscoreContinuous : Continuous score)
    (hmodulusNonneg : 0 ≤ modulus)
    (hscoreModulus : ∀ first second,
      |score first - score second| ≤ modulus * dist first second)
    {level : ℕ} (hlevel : 0 < level) :
    system.shellLowerValue score level ≤ system.attainableInf score ∧
      system.attainableInf score ≤ system.upperValue score level ∧
      system.upperValue score level - system.shellLowerValue score level ≤
        modulus * system.radius level := by
  exact ⟨system.shellLowerValue_le_attainableInf score floor hscoreFloor hlevel,
    system.attainableInf_le_upperValue score hscoreFloor
      hscoreContinuous level,
    system.upperValue_sub_shellLowerValue_le score floor modulus hscoreFloor
      hmodulusNonneg hscoreModulus hlevel⟩

end NestedOuterApproximation

end

end Math.Topology
