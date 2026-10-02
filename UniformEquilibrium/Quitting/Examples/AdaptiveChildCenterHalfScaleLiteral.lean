import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterCapAndHalfScale

/-! # Literal rationality and the full cap of the same half-scaled center -/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

/-- One rational table realizes EVERY coordinate of the actual half-scaled reward. -/
theorem halfReward_has_rational_table :
    ∃ table : {S : Finset (Fin 4) // S.Nonempty} → Fin 4 → ℚ,
      ∀ terminal who, (table terminal who : ℝ) = halfReward terminal who := by
  have hcoordinate : ∀ terminal : {S : Finset (Fin 4) // S.Nonempty}, ∀ who : Fin 4,
      ∃ value : ℚ, (value : ℝ) = halfReward terminal who := by
    intro terminal who
    fin_cases who
    · by_cases hzero : (0 : Fin 4) ∈ terminal.1
      · exact ⟨1 / 2, by norm_num [halfReward, scaleQuittingReward, reward, hzero]⟩
      · by_cases htwo : (2 : Fin 4) ∈ terminal.1
        · exact ⟨1, by norm_num [halfReward, scaleQuittingReward, reward, hzero, htwo]⟩
        · exact ⟨0, by norm_num [halfReward, scaleQuittingReward, reward, hzero, htwo]⟩
    · by_cases hone : (1 : Fin 4) ∈ terminal.1
      · by_cases hzero : (0 : Fin 4) ∈ terminal.1
        · exact ⟨1 / 2, by norm_num [halfReward, scaleQuittingReward, reward, hone, hzero]⟩
        · exact ⟨-1 / 2, by norm_num [halfReward, scaleQuittingReward, reward, hone, hzero]⟩
      · exact ⟨0, by norm_num [halfReward, scaleQuittingReward, reward, hone]⟩
    · by_cases htwo : (2 : Fin 4) ∈ terminal.1
      · by_cases hone : (1 : Fin 4) ∈ terminal.1
        · exact ⟨1 / 2, by norm_num [halfReward, scaleQuittingReward, reward, htwo, hone]⟩
        · exact ⟨-1 / 2, by norm_num [halfReward, scaleQuittingReward, reward, htwo, hone]⟩
      · exact ⟨0, by norm_num [halfReward, scaleQuittingReward, reward, htwo]⟩
    · by_cases hthree : (3 : Fin 4) ∈ terminal.1
      · exact ⟨1 / 2, by norm_num [halfReward, scaleQuittingReward, reward, hthree]⟩
      · exact ⟨0, by norm_num [halfReward, scaleQuittingReward, reward, hthree]⟩
  choose table htable using hcoordinate
  exact ⟨table, htable⟩

/-- The SAME actual center profile has its entire unrestricted cap scaled by half. -/
theorem halfReward_profile_fullCap_eq_half_target :
    quittingContinuationBestResponse halfReward profile =
      fun who => (1 / 2 : ℝ) * target who := by
  funext who
  exact (quittingContinuationBestResponseValue_scaleQuittingReward
    (by norm_num : (0 : ℝ) ≤ 1 / 2) reward profile who).trans
    (congrArg (fun value : ℝ => (1 / 2 : ℝ) * value)
      (congrFun profile_fullCap_eq_target who))

end GameTheory.AdaptiveChildCenter
