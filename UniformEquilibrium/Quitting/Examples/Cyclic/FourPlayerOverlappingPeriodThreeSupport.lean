import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreePolynomialSystem
import UniformEquilibrium.Quitting.Cycles.PeriodThreeClearedGap

/-!
# The overlapping period-three support word

This file states the support combinatorics and strict hazard bounds of the
concrete eight-coordinate chart as literal theorems.
-/

noncomputable section

namespace GameTheory.FourPlayerOverlappingPeriodThree

open Set

/-- The three overlapping active-player blocks. -/
def overlappingPeriodThreeSupport : Fin 3 → Finset Player
  | 0 => {1, 2}
  | 1 => {0, 1, 3}
  | 2 => {0, 2, 3}

/-- The three supports are literally `{1,2}`, `{0,1,3}`, and
`{0,2,3}` in chronological order. -/
theorem overlappingPeriodThreeSupport_values :
    overlappingPeriodThreeSupport 0 = {1, 2} ∧
      overlappingPeriodThreeSupport 1 = {0, 1, 3} ∧
      overlappingPeriodThreeSupport 2 = {0, 2, 3} := by
  decide

/-- Membership in the normalized closed unit cube. -/
def IsNormalizedHazardPoint (z : HazardCoordinate → ℝ) : Prop :=
  z ∈ Icc (fun _ => -1) (fun _ => 1)

/-- Every active hazard remains strictly positive throughout the normalized
box, and inactive hazards are exactly zero. -/
theorem hazardOfNormalized_pos_iff_mem_support
    {z : HazardCoordinate → ℝ} (hz : IsNormalizedHazardPoint z)
    (phase : Fin 3) (who : Player) :
    0 < hazardOfNormalized z phase who ↔
      who ∈ overlappingPeriodThreeSupport phase := by
  change (∀ coordinate, -1 ≤ z coordinate) ∧
    (∀ coordinate, z coordinate ≤ 1) at hz
  rcases hz with ⟨hlower, hupper⟩
  fin_cases phase <;> fin_cases who <;>
    simp [hazardOfNormalized, overlappingPeriodThreeSupport,
      hazardCenter, hazardRadius] <;>
    norm_num <;>
    linarith [hlower 0, hlower 1, hlower 2, hlower 3,
      hlower 4, hlower 5, hlower 6, hlower 7]

/-- Every hazard outside the displayed support is exactly zero. -/
theorem hazardOfNormalized_eq_zero_of_not_mem_support
    (z : HazardCoordinate → ℝ)
    (phase : Fin 3) (who : Player)
    (hnot : who ∉ overlappingPeriodThreeSupport phase) :
    hazardOfNormalized z phase who = 0 := by
  fin_cases phase <;> fin_cases who <;>
    simp [hazardOfNormalized, overlappingPeriodThreeSupport] at hnot ⊢

/-- All eight active hazards remain strictly below one, and inactive hazards
are zero, throughout the normalized box. -/
theorem hazardOfNormalized_lt_one_of_mem_support
    {z : HazardCoordinate → ℝ} (hz : IsNormalizedHazardPoint z)
    {phase : Fin 3} {who : Player}
    (hmem : who ∈ overlappingPeriodThreeSupport phase) :
    hazardOfNormalized z phase who < 1 := by
  change (∀ coordinate, -1 ≤ z coordinate) ∧
    (∀ coordinate, z coordinate ≤ 1) at hz
  rcases hz with ⟨hlower, hupper⟩
  fin_cases phase <;> fin_cases who <;>
    simp [hazardOfNormalized, overlappingPeriodThreeSupport,
      hazardCenter, hazardRadius] at hmem ⊢ <;>
    norm_num at hmem ⊢ <;>
    linarith [hupper 0, hupper 1, hupper 2, hupper 3,
      hupper 4, hupper 5, hupper 6, hupper 7]

/-- The concrete chart is a probability-valued hazard word throughout its
closed normalized box. -/
theorem hazardOfNormalized_mem_unitInterval
    {z : HazardCoordinate → ℝ} (hz : IsNormalizedHazardPoint z) :
    ∀ phase who,
      0 ≤ hazardOfNormalized z phase who ∧
        hazardOfNormalized z phase who ≤ 1 := by
  intro phase who
  change (∀ coordinate, -1 ≤ z coordinate) ∧
    (∀ coordinate, z coordinate ≤ 1) at hz
  rcases hz with ⟨hlower, hupper⟩
  fin_cases phase <;> fin_cases who <;>
    simp [hazardOfNormalized, hazardCenter, hazardRadius] <;>
    constructor <;>
    norm_num <;>
    linarith [hlower 0, hlower 1, hlower 2, hlower 3,
      hlower 4, hlower 5, hlower 6, hlower 7,
      hupper 0, hupper 1, hupper 2, hupper 3,
      hupper 4, hupper 5, hupper 6, hupper 7]

/-- The active-slot enumeration covers exactly the displayed support word. -/
theorem activeSlot_is_enumerated_iff_mem_overlappingPeriodThreeSupport
    (phase : Fin 3) (who : Player) :
    (∃ coordinate, activeSlot coordinate = (phase, who)) ↔
      who ∈ overlappingPeriodThreeSupport phase := by
  fin_cases phase <;> fin_cases who <;>
    simp [activeSlot, overlappingPeriodThreeSupport] <;>
    decide

/-- Every player faces a strictly positive opponent hazard already in phase
zero throughout the normalized box. -/
theorem exists_positive_phase_zero_opponent
    {z : HazardCoordinate → ℝ} (hz : IsNormalizedHazardPoint z)
    (who : Player) :
    ∃ other : Player,
      other ≠ who ∧ 0 < hazardOfNormalized z 0 other := by
  fin_cases who
  · exact ⟨1, by decide,
      (hazardOfNormalized_pos_iff_mem_support hz 0 1).mpr (by decide)⟩
  · exact ⟨2, by decide,
      (hazardOfNormalized_pos_iff_mem_support hz 0 2).mpr (by decide)⟩
  · exact ⟨1, by decide,
      (hazardOfNormalized_pos_iff_mem_support hz 0 1).mpr (by decide)⟩
  · exact ⟨1, by decide,
      (hazardOfNormalized_pos_iff_mem_support hz 0 1).mpr (by decide)⟩

/-- The concrete period-three block contracts every player's fixed-opponent
continuation probability. -/
theorem hazardOfNormalized_fixedOpponentContraction
    {z : HazardCoordinate → ℝ} (hz : IsNormalizedHazardPoint z) :
    let h0 : ∀ phase who, 0 ≤ hazardOfNormalized z phase who :=
      fun phase who => (hazardOfNormalized_mem_unitInterval hz phase who).1
    let h1 : ∀ phase who, hazardOfNormalized z phase who ≤ 1 :=
      fun phase who => (hazardOfNormalized_mem_unitInterval hz phase who).2
    ∀ who,
      (∏ phase : Fin 3,
        quittingStationaryFixedOpponentsContinueMass
          (quittingBlockCycle (hazardOfNormalized z) h0 h1 phase) who) < 1 := by
  dsimp only
  intro who
  obtain ⟨other, hother, hpositive⟩ := exists_positive_phase_zero_opponent hz who
  exact prod_fixedOpponentsContinueMass_quittingBlockCycle_lt_one_of_pos
    (fun phase player => (hazardOfNormalized_mem_unitInterval hz phase player).1)
    (fun phase player => (hazardOfNormalized_mem_unitInterval hz phase player).2)
    who other 0 hother hpositive

end GameTheory.FourPlayerOverlappingPeriodThree

end
