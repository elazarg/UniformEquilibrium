import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseHalfRawCoverage

/-! # Attained literal guard margins of the two crossed-source tables

Every margin below is read from the actual table, and every upper coefficient
is the canonical sample transform of its actual residual.
-/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open QuittingFinFourEndpointRows Math.Finset

/-- The outsider coalitions in printed order: empty, 2, 3, 23. -/
def crossedSourceOutsiderCoalition : Fin 4 → Finset (Fin 4) :=
  ![∅, {2}, {3}, {2, 3}]

/-- The nonempty outsider coalitions in printed order: 2, 3, 23. -/
def crossedSourceNonemptyOutsiderCoalition : Fin 3 → Finset (Fin 4) :=
  ![{2}, {3}, {2, 3}]

private def crossedSourceRecipient (selected : Fin 2) : Fin 4 :=
  if selected = 0 then 0 else 1

private def crossedSourcePartner (selected : Fin 2) : Fin 4 :=
  if selected = 0 then 1 else 0

/-- One of the twelve literal lower comparisons for the selected recipient. -/
def crossedSourceLowerMargin
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (selected : Fin 2) (own : Fin 4) (other : Fin 3) : ℝ :=
  weightOfReward reward
      (insert (crossedSourceRecipient selected) (crossedSourceOutsiderCoalition own))
      (crossedSourceRecipient selected) -
    weightOfReward reward (crossedSourceNonemptyOutsiderCoalition other)
      (crossedSourceRecipient selected)

/-- The positive direction of the literal unit-ceiling joining comparison. -/
def unitCeilingJoiningMargin (selected : Fin 2) (outsiders : Fin 4) : ℝ :=
  weightOfReward unitCeilingReward
      (insert (crossedSourcePartner selected) (crossedSourceOutsiderCoalition outsiders))
      (crossedSourceRecipient selected) -
    weightOfReward unitCeilingReward
      (insert (crossedSourceRecipient selected)
        (insert (crossedSourcePartner selected) (crossedSourceOutsiderCoalition outsiders)))
      (crossedSourceRecipient selected)

theorem unitCeiling_joiningMargins_first (outsiders : Fin 4) :
    unitCeilingJoiningMargin 0 outsiders = ![7, 1, 1, 1] outsiders := by
  fin_cases outsiders <;>
    norm_num +decide [unitCeilingJoiningMargin, crossedSourceRecipient,
      crossedSourcePartner, crossedSourceOutsiderCoalition, weightOfReward,
      unitCeilingReward, coalitionCode]

theorem unitCeiling_joiningMargins_second (outsiders : Fin 4) :
    unitCeilingJoiningMargin 1 outsiders = ![7, 1, 2, 2] outsiders := by
  fin_cases outsiders <;>
    norm_num +decide [unitCeilingJoiningMargin, crossedSourceRecipient,
      crossedSourcePartner, crossedSourceOutsiderCoalition, weightOfReward,
      unitCeilingReward, coalitionCode]

private theorem half_lower_first (own : Fin 4) (other : Fin 3) :
    1 ≤ crossedSourceLowerMargin halfCeilingReward 0 own other := by
  fin_cases own <;> fin_cases other <;>
    norm_num +decide [crossedSourceLowerMargin, crossedSourceRecipient,
      crossedSourceOutsiderCoalition, crossedSourceNonemptyOutsiderCoalition,
      weightOfReward, halfCeilingReward, coalitionCode]

private theorem half_lower_second (own : Fin 4) (other : Fin 3) :
    1 ≤ crossedSourceLowerMargin halfCeilingReward 1 own other := by
  fin_cases own <;> fin_cases other <;>
    norm_num +decide [crossedSourceLowerMargin, crossedSourceRecipient,
      crossedSourceOutsiderCoalition, crossedSourceNonemptyOutsiderCoalition,
      weightOfReward, halfCeilingReward, coalitionCode]

private theorem unit_lower_first (own : Fin 4) (other : Fin 3) :
    1 ≤ crossedSourceLowerMargin unitCeilingReward 0 own other := by
  fin_cases own <;> fin_cases other <;>
    norm_num +decide [crossedSourceLowerMargin, crossedSourceRecipient,
      crossedSourceOutsiderCoalition, crossedSourceNonemptyOutsiderCoalition,
      weightOfReward, unitCeilingReward, coalitionCode]

private theorem unit_lower_second (own : Fin 4) (other : Fin 3) :
    1 ≤ crossedSourceLowerMargin unitCeilingReward 1 own other := by
  fin_cases own <;> fin_cases other <;>
    norm_num +decide [crossedSourceLowerMargin, crossedSourceRecipient,
      crossedSourceOutsiderCoalition, crossedSourceNonemptyOutsiderCoalition,
      weightOfReward, unitCeilingReward, coalitionCode]

/-- Each of the half table's two lower-ranking minima is attained and equals one. -/
theorem halfCeiling_lowerMargin_minimum (selected : Fin 2) :
    IsLeast (Set.range (fun index : Fin 4 × Fin 3 =>
      crossedSourceLowerMargin halfCeilingReward selected index.1 index.2)) 1 := by
  constructor
  · refine ⟨(0, 0), ?_⟩
    fin_cases selected <;>
      norm_num +decide [crossedSourceLowerMargin, crossedSourceRecipient,
        crossedSourceOutsiderCoalition, crossedSourceNonemptyOutsiderCoalition,
        weightOfReward, halfCeilingReward, coalitionCode]
  · rintro value ⟨⟨own, other⟩, rfl⟩
    fin_cases selected
    · exact half_lower_first own other
    · exact half_lower_second own other

/-- Each of the unit table's two lower-ranking minima is attained and equals one. -/
theorem unitCeiling_lowerMargin_minimum (selected : Fin 2) :
    IsLeast (Set.range (fun index : Fin 4 × Fin 3 =>
      crossedSourceLowerMargin unitCeilingReward selected index.1 index.2)) 1 := by
  constructor
  · refine ⟨(0, 0), ?_⟩
    fin_cases selected <;>
      norm_num +decide [crossedSourceLowerMargin, crossedSourceRecipient,
        crossedSourceOutsiderCoalition, crossedSourceNonemptyOutsiderCoalition,
        weightOfReward, unitCeilingReward, coalitionCode]
  · rintro value ⟨⟨own, other⟩, rfl⟩
    fin_cases selected
    · exact unit_lower_first own other
    · exact unit_lower_second own other

/-- Each joining array has attained minimum one, not merely a positive lower bound. -/
theorem unitCeiling_joiningMargin_minimum (selected : Fin 2) :
    IsLeast (Set.range (unitCeilingJoiningMargin selected)) 1 := by
  constructor
  · refine ⟨1, ?_⟩
    fin_cases selected
    · change unitCeilingJoiningMargin 0 1 = 1
      rw [unitCeiling_joiningMargins_first]
      norm_num
    · change unitCeilingJoiningMargin 1 1 = 1
      rw [unitCeiling_joiningMargins_second]
      norm_num
  · rintro value ⟨outsiders, rfl⟩
    fin_cases selected
    · change 1 ≤ unitCeilingJoiningMargin 0 outsiders
      rw [unitCeiling_joiningMargins_first]
      fin_cases outsiders <;> norm_num
    · change 1 ≤ unitCeilingJoiningMargin 1 outsiders
      rw [unitCeiling_joiningMargins_second]
      fin_cases outsiders <;> norm_num

/-- An actual half-table upper coefficient, indexed over both selected recipients. -/
def halfCeilingUpperCoefficient (index : Fin 2 × Fin 3 × Fin 3) : ℝ :=
  if index.1 = 0 then
    Math.quadraticTensorBernsteinCoefficient (quittingHalfFirstResidual halfCeilingReward)
      index.2.1 index.2.2
  else
    Math.quadraticTensorBernsteinCoefficient (quittingHalfSecondResidual halfCeilingReward)
      index.2.1 index.2.2

private theorem half_first_upper_le (first second : Fin 3) :
    Math.quadraticTensorBernsteinCoefficient (quittingHalfFirstResidual halfCeilingReward)
      first second ≤ -1 / 12 := by
  rw [halfCeiling_firstCoefficient]
  fin_cases first <;> fin_cases second <;> norm_num [halfCeiling_firstBernsteinArray]

private theorem half_second_upper_le (first second : Fin 3) :
    Math.quadraticTensorBernsteinCoefficient (quittingHalfSecondResidual halfCeilingReward)
      first second ≤ -1 / 12 := by
  rw [halfCeiling_secondCoefficient]
  fin_cases first <;> fin_cases second <;> norm_num [halfCeiling_secondBernsteinArray]

/-- The greatest of all eighteen actual upper coefficients is attained at recipient 0,
first index 1, second index 0, and equals minus one twelfth. -/
theorem halfCeiling_upperCoefficient_maximum :
    IsGreatest (Set.range halfCeilingUpperCoefficient) (-1 / 12) := by
  constructor
  · refine ⟨(0, 1, 0), ?_⟩
    norm_num [halfCeilingUpperCoefficient, halfCeiling_firstCoefficient,
      halfCeiling_firstBernsteinArray]
  · rintro value ⟨⟨selected, first, second⟩, rfl⟩
    fin_cases selected
    · simpa [halfCeilingUpperCoefficient] using half_first_upper_le first second
    · simpa [halfCeilingUpperCoefficient] using half_second_upper_le first second

/-- The unit table's second half-face sure-outsider corner is the literal positive 3/2. -/
theorem unitCeiling_halfSecondSureOutsidersResidual :
    quittingHalfSecondResidual unitCeilingReward 1 1 = 3 / 2 := by
  have hmass : continueMassExcl (halfSecondRow 1 1) 1 = 0 :=
    quittingCrossed_continueMassExcl_partner_one (halfSecondRow 1 1) 1 2
      (by decide) (by norm_num [halfSecondRow])
  rw [quittingHalfSecondResidual, quittingDiscountedDisplacement, hmass,
    sigmaValue_eq_pureQuitEndpointRowSum, excludedValue_eq_excludedEndpointRowSum]
  simp only [pureQuitEndpointRowSum, excludedEndpointRowSum, Fin.sum_univ_succ]
  simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ,
    halfSecondRow]
  norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode]

end GameTheory.GuardedCrossedResponseExamples
