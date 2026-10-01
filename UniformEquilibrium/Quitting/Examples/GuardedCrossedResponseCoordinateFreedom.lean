import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRowTranslation
import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseHalfRawCoverage

/-! # Literal unrestricted outsider coordinates and arbitrary signed singleton levels

All twenty-two outsider-recipient nonsingleton entries may be replaced
independently without changing the singleton matrix or selected guard rows.
Terminal row translations then allow any four signed own-singleton levels.
Each resulting table gets its own equilibrium from the source producer.
This does not assert arbitrary-profile strategic equivalence under translations.
-/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open QuittingLCPClassification

/-- The actual nonempty-coalition coordinates free of all selected raw tests. -/
abbrev HalfOutsiderRewardCoordinate :=
  {coordinate : {S : Finset (Fin 4) // S.Nonempty} × Fin 4 //
    coordinate.1.1.card ≠ 1 ∧ (coordinate.2 = 2 ∨ coordinate.2 = 3)}

/-- There are eleven nonsingleton coalitions for each of the two outsider recipients. -/
theorem card_halfOutsiderRewardCoordinate : Fintype.card HalfOutsiderRewardCoordinate = 22 := by
  decide

/-- Replace exactly these actual twenty-two coordinates, leaving every other entry alone. -/
def quittingHalfOutsiderCompletion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (free : HalfOutsiderRewardCoordinate → ℝ) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal who =>
    if h : terminal.1.card ≠ 1 ∧ (who = 2 ∨ who = 3) then
      free ⟨(terminal, who), h⟩ else reward terminal who

theorem quittingHalfOutsiderCompletion_free
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (free : HalfOutsiderRewardCoordinate → ℝ) (coordinate : HalfOutsiderRewardCoordinate) :
    quittingHalfOutsiderCompletion reward free coordinate.1.1 coordinate.1.2 = free coordinate := by
  simp [quittingHalfOutsiderCompletion, coordinate.property]

/-- The freedom is genuinely independent, not a redundant parameterization. -/
theorem quittingHalfOutsiderCompletion_injective
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    Function.Injective (quittingHalfOutsiderCompletion reward) := by
  intro first second heq
  funext coordinate
  have h := congrFun (congrFun heq coordinate.1.1) coordinate.1.2
  simpa only [quittingHalfOutsiderCompletion_free] using h

theorem quittingHalfOutsiderCompletion_selected
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (free : HalfOutsiderRewardCoordinate → ℝ) (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (who : Fin 4) (hselected : who = 0 ∨ who = 1) :
    quittingHalfOutsiderCompletion reward free terminal who = reward terminal who := by
  rcases hselected with rfl | rfl <;> simp [quittingHalfOutsiderCompletion]

theorem quittingHalfOutsiderCompletion_singleton
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (free : HalfOutsiderRewardCoordinate → ℝ) (owner who : Fin 4) :
    quittingHalfOutsiderCompletion reward free
        ⟨{owner}, Finset.singleton_nonempty owner⟩ who =
      reward ⟨{owner}, Finset.singleton_nonempty owner⟩ who := by
  simp [quittingHalfOutsiderCompletion]

theorem quittingHalfOutsiderCompletion_singletonMatrix
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (free : HalfOutsiderRewardCoordinate → ℝ) :
    quittingSingletonMatrix (quittingHalfOutsiderCompletion reward free) =
      quittingSingletonMatrix reward := by
  ext who owner
  simp only [quittingSingletonMatrix, quittingHalfOutsiderCompletion_singleton]

/-- Every selected raw comparison and coefficient is unchanged by the twenty-two entries. -/
theorem quittingHalfOutsiderCompletion_strictRawGuards_iff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (free : HalfOutsiderRewardCoordinate → ℝ) :
    QuittingHalfStrictRawGuards (quittingHalfOutsiderCompletion reward free) ↔
      QuittingHalfStrictRawGuards reward := by
  have hfirst := quittingCrossedStrictLowerRanking_congr_recipient reward
    (quittingHalfOutsiderCompletion reward free) 0 1
    (fun terminal => quittingHalfOutsiderCompletion_selected reward free terminal 0 (Or.inl rfl))
  have hsecond := quittingCrossedStrictLowerRanking_congr_recipient reward
    (quittingHalfOutsiderCompletion reward free) 1 0
    (fun terminal => quittingHalfOutsiderCompletion_selected reward free terminal 1 (Or.inr rfl))
  have hpolyFirst : quittingHalfFirstResidual (quittingHalfOutsiderCompletion reward free) =
      quittingHalfFirstResidual reward := by
    funext x y
    exact quittingDiscountedDisplacement_congr_recipient reward _ 0
      (fun terminal => quittingHalfOutsiderCompletion_selected reward free terminal 0 (Or.inl rfl))
      0 (halfFirstRow x y)
  have hpolySecond : quittingHalfSecondResidual (quittingHalfOutsiderCompletion reward free) =
      quittingHalfSecondResidual reward := by
    funext x y
    exact quittingDiscountedDisplacement_congr_recipient reward _ 1
      (fun terminal => quittingHalfOutsiderCompletion_selected reward free terminal 1 (Or.inr rfl))
      0 (halfSecondRow x y)
  constructor
  · intro h
    exact ⟨hfirst.mp h.lowerFirst, hsecond.mp h.lowerSecond,
      ⟨by simpa only [hpolyFirst] using h.upper.first,
        by simpa only [hpolySecond] using h.upper.second⟩⟩
  · intro h
    exact ⟨hfirst.mpr h.lowerFirst, hsecond.mpr h.lowerSecond,
      ⟨by simpa only [hpolyFirst] using h.upper.first,
        by simpa only [hpolySecond] using h.upper.second⟩⟩

/-- The source half table with any four signed singleton levels and any
twenty-two outsider nonsingleton entries, all interpreted as final actual rewards. -/
def halfCeilingRewardWithFreedom (solo : Payoff (Fin 4))
    (free : HalfOutsiderRewardCoordinate → ℝ) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  quittingHalfOutsiderCompletion
    (quittingPlayerwiseAffineReward halfCeilingReward 1
      (fun who => solo who - halfCeilingReward ⟨{who}, Finset.singleton_nonempty who⟩ who)) free

theorem halfCeilingRewardWithFreedom_ownSingleton
    (solo : Payoff (Fin 4)) (free : HalfOutsiderRewardCoordinate → ℝ) (who : Fin 4) :
    halfCeilingRewardWithFreedom solo free ⟨{who}, Finset.singleton_nonempty who⟩ who =
      solo who := by
  rw [halfCeilingRewardWithFreedom, quittingHalfOutsiderCompletion_singleton]
  simp [quittingPlayerwiseAffineReward]

theorem halfCeilingRewardWithFreedom_free
    (solo : Payoff (Fin 4)) (free : HalfOutsiderRewardCoordinate → ℝ)
    (coordinate : HalfOutsiderRewardCoordinate) :
    halfCeilingRewardWithFreedom solo free coordinate.1.1 coordinate.1.2 = free coordinate :=
  quittingHalfOutsiderCompletion_free _ free coordinate

theorem halfCeilingRewardWithFreedom_source
    (solo : Payoff (Fin 4)) (free : HalfOutsiderRewardCoordinate → ℝ) :
    quittingSingletonMatrix (halfCeilingRewardWithFreedom solo free) = sourceSingletonMatrix ∧
      QuittingHalfStrictRawGuards (halfCeilingRewardWithFreedom solo free) := by
  constructor
  · rw [halfCeilingRewardWithFreedom, quittingHalfOutsiderCompletion_singletonMatrix,
      quittingSingletonMatrix_playerwiseTranslation, halfCeiling_singletonMatrix]
  · apply (quittingHalfOutsiderCompletion_strictRawGuards_iff _ _).mpr
    exact (quittingHalfStrictRawGuards_playerwiseTranslation_iff _ _).mpr
      halfCeiling_strictRawGuards

/-- The producer applies anew to every actual completion, with no magnitude
or sign bounds on the free coordinates or singleton levels. -/
theorem halfCeilingRewardWithFreedom_stationaryTerminalNash_uniformPayoff
    (solo : Payoff (Fin 4)) (free : HalfOutsiderRewardCoordinate → ℝ) :
    ∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
      0 < hazardOfRoot root 0 ∧ hazardOfRoot root 0 < 1 / 2 ∧
      0 < hazardOfRoot root 1 ∧ hazardOfRoot root 1 < 1 / 2 ∧
      (∃ outsider, outsider ≠ 0 ∧ outsider ≠ 1 ∧ 0 < hazardOfRoot root outsider) ∧
      value = quittingTerminalPayoff (halfCeilingRewardWithFreedom solo free)
        (quittingStationaryProfile (halfCeilingRewardWithFreedom solo free) root) ∧
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame (halfCeilingRewardWithFreedom solo free)).IsεAsymptoticNash
        (quittingTerminalPayoff (halfCeilingRewardWithFreedom solo free)) 0
        (quittingStationaryProfile (halfCeilingRewardWithFreedom solo free) root) ∧
      (quittingGame (halfCeilingRewardWithFreedom solo free)).IsUniformEquilibriumPayoff
        none value := by
  obtain ⟨hmatrix, hraw⟩ := halfCeilingRewardWithFreedom_source solo free
  apply exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_halfStrictRaw _ _ _ hraw
  · rw [hmatrix, sourceSingletonMatrix_det]
    norm_num
  · rw [hmatrix]
    exact sourceSingletonMatrix_inverse_pos

end GameTheory.GuardedCrossedResponseExamples
