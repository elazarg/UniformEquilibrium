import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseHalfRawCoverage
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingPerturbation

/-! # The exact numerical full-table radii preserve the literal raw guards -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

private theorem source_lower_gap
    (center : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcenter : center = halfCeilingReward ∨ center = unitCeilingReward)
    (who : Fin 4) (hwho : who = 0 ∨ who = 1)
    (own other : Finset (Fin 4)) (hown : own ⊆ {2, 3}) (hother : other ⊆ {2, 3})
    (hnonempty : other.Nonempty) :
    1 ≤ weightOfReward center (insert who own) who - weightOfReward center other who := by
  have hpowerset : ({2, 3} : Finset (Fin 4)).powerset = {∅, {2}, {3}, {2, 3}} := by
    decide
  have hown' := Finset.mem_powerset.mpr hown
  have hother' := Finset.mem_powerset.mpr hother
  rw [hpowerset] at hown' hother'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hown' hother'
  rcases hcenter with rfl | rfl
  all_goals rcases hwho with rfl | rfl
  all_goals rcases hown' with rfl | rfl | rfl | rfl
  all_goals rcases hother' with rfl | rfl | rfl | rfl
  all_goals norm_num at hnonempty
  all_goals norm_num +decide [weightOfReward, halfCeilingReward, unitCeilingReward,
    coalitionCode]

private theorem source_joining_gap
    (who partner : Fin 4) (hpair : (who = 0 ∧ partner = 1) ∨ (who = 1 ∧ partner = 0))
    (outsider : Finset (Fin 4)) (hsubset : outsider ⊆ {2, 3}) :
    1 ≤ weightOfReward unitCeilingReward (insert partner outsider) who -
      weightOfReward unitCeilingReward (insert who (insert partner outsider)) who := by
  have hpowerset : ({2, 3} : Finset (Fin 4)).powerset = {∅, {2}, {3}, {2, 3}} := by
    decide
  have h := Finset.mem_powerset.mpr hsubset
  rw [hpowerset] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rcases h with rfl | rfl | rfl | rfl
  all_goals norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode]

private theorem lowerRanking_of_coordinate_error
    (center other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcenter : center = halfCeilingReward ∨ center = unitCeilingReward)
    (error : ℝ) (herror : error < 1 / 2)
    (hclose : ∀ terminal who, |other terminal who - center terminal who| ≤ error)
    (who partner : Fin 4) (hpair : (who = 0 ∧ partner = 1) ∨ (who = 1 ∧ partner = 0)) :
    QuittingCrossedStrictLowerRanking other who partner := by
  have hwho : who = 0 ∨ who = 1 := hpair.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hcarrier : quittingCrossedRawOutsiders who partner = {2, 3} := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  intro own coalition hown hcoalition hnonempty
  rw [hcarrier] at hown hcoalition
  have hgap := source_lower_gap center hcenter who hwho own coalition hown hcoalition hnonempty
  have h := Maths.FiniteInequality.abs_sub_differences_le
    (weightOfReward center (insert who own) who) (weightOfReward center coalition who)
    (weightOfReward other (insert who own) who) (weightOfReward other coalition who) error
    (abs_weightOfReward_sub_le_of_coordinate_error center other error hclose
      (insert who own) (Finset.insert_nonempty who own) who)
    (abs_weightOfReward_sub_le_of_coordinate_error center other error hclose
      coalition hnonempty who)
  have hlower := (abs_le.mp h).1
  linarith

private theorem unitJoining_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (herror : error < 1 / 2)
    (hclose : ∀ terminal who, |other terminal who - unitCeilingReward terminal who| ≤ error)
    (who partner : Fin 4) (hpair : (who = 0 ∧ partner = 1) ∨ (who = 1 ∧ partner = 0)) :
    QuittingCrossedStrictUnitJoining other who partner := by
  have hcarrier : quittingCrossedRawOutsiders who partner = {2, 3} := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  intro outsider hsubset
  rw [hcarrier] at hsubset
  have hgap := source_joining_gap who partner hpair outsider hsubset
  have h := Maths.FiniteInequality.abs_sub_differences_le
    (weightOfReward unitCeilingReward (insert partner outsider) who)
    (weightOfReward unitCeilingReward (insert who (insert partner outsider)) who)
    (weightOfReward other (insert partner outsider) who)
    (weightOfReward other (insert who (insert partner outsider)) who) error
    (abs_weightOfReward_sub_le_of_coordinate_error unitCeilingReward other error hclose
      (insert partner outsider) (Finset.insert_nonempty partner outsider) who)
    (abs_weightOfReward_sub_le_of_coordinate_error unitCeilingReward other error hclose
      (insert who (insert partner outsider)) (Finset.insert_nonempty who _) who)
  have hlower := (abs_le.mp h).1
  linarith

/-- The actual eighteen coefficients stay strict throughout the packet's half radius. -/
theorem halfCeiling_strictBernsteinUpper_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (herror : error < 1 / 100)
    (hclose : ∀ terminal who, |other terminal who - halfCeilingReward terminal who| ≤ error) :
    QuittingHalfStrictBernsteinUpper other := by
  have hzero : 0 ≤ error := (abs_nonneg _).trans (hclose ⟨{0}, by simp⟩ 0)
  constructor
  · intro first second
    have h := (abs_le.mp (abs_quittingHalfFirstResidual_coefficient_sub_le
      halfCeilingReward other error hclose first second)).2
    have hfactor := mul_le_mul_of_nonneg_right
      (Math.halfSurvivalBernsteinErrorFactor_le_two first second) hzero
    have hmargin :
        Math.quadraticTensorBernsteinCoefficient (quittingHalfFirstResidual halfCeilingReward)
          first second ≤ -1 / 12 := by
      rw [halfCeiling_firstCoefficient]
      fin_cases first <;> fin_cases second <;> norm_num [halfCeiling_firstBernsteinArray]
    linarith
  · intro first second
    have h := (abs_le.mp (abs_quittingHalfSecondResidual_coefficient_sub_le
      halfCeilingReward other error hclose first second)).2
    have hfactor := mul_le_mul_of_nonneg_right
      (Math.halfSurvivalBernsteinErrorFactor_le_two first second) hzero
    have hmargin :
        Math.quadraticTensorBernsteinCoefficient (quittingHalfSecondResidual halfCeilingReward)
          first second ≤ -1 / 12 := by
      rw [halfCeiling_secondCoefficient]
      fin_cases first <;> fin_cases second <;> norm_num [halfCeiling_secondBernsteinArray]
    linarith

/-- Every one of the sixty raw reward coordinates is free within the exact half radius. -/
theorem halfCeiling_strictRawGuards_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (herror : error < 1 / 100)
    (hclose : ∀ terminal who, |other terminal who - halfCeilingReward terminal who| ≤ error) :
    QuittingHalfStrictRawGuards other := by
  refine ⟨?_, ?_, halfCeiling_strictBernsteinUpper_of_coordinate_error other error herror hclose⟩
  · exact lowerRanking_of_coordinate_error halfCeilingReward other (Or.inl rfl)
      error (by linarith) hclose 0 1 (Or.inl ⟨rfl, rfl⟩)
  · exact lowerRanking_of_coordinate_error halfCeilingReward other (Or.inl rfl)
      error (by linarith) hclose 1 0 (Or.inr ⟨rfl, rfl⟩)

/-- All finite unit guards persist at the literal unit radius, without equality constraints. -/
theorem unitCeiling_strictRawGuards_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (herror : error < 1 / 1000)
    (hclose : ∀ terminal who, |other terminal who - unitCeilingReward terminal who| ≤ error) :
    QuittingCrossedStrictRawUnitGuards other 0 1 := by
  constructor
  · exact lowerRanking_of_coordinate_error unitCeilingReward other (Or.inr rfl)
      error (by linarith) hclose 0 1 (Or.inl ⟨rfl, rfl⟩)
  · exact lowerRanking_of_coordinate_error unitCeilingReward other (Or.inr rfl)
      error (by linarith) hclose 1 0 (Or.inr ⟨rfl, rfl⟩)
  · exact unitJoining_of_coordinate_error other error (by linarith) hclose
      0 1 (Or.inl ⟨rfl, rfl⟩)
  · exact unitJoining_of_coordinate_error other error (by linarith) hclose
      1 0 (Or.inr ⟨rfl, rfl⟩)

end GameTheory.GuardedCrossedResponseExamples
