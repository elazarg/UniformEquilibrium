import UniformEquilibrium.Quitting.Punishment.SinglePivotPunishment
import UniformEquilibrium.Quitting.Paths.ProfileNeverMass
import UniformEquilibrium.Quitting.Terminal.SingletonJointNeverDebt

/-! # Actual profile debt and Never-mass bounds under normalization -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The signed singleton cylinder inequality in literal joint-survival form. -/
theorem quittingLiveMassLimit_mul_singleton_le_terminalDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingLiveMassLimit reward profile * reward (quittingSingletonTerminal who) who ≤
      quittingTerminalDeviationDebt reward profile who := by
  rw [quittingLiveMassLimit_eq_prod_hazardNeverMass]
  simpa only [quittingBehaviorStoppingLaw_none_toReal] using
    prod_stoppingLaw_none_mul_singleton_le_terminalDebt reward profile who

/-- A positive singleton bounds the source's actual Never mass by full debt. -/
theorem quittingLiveMassLimit_le_exploitability_div_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (hsolo : 0 < quittingSoloReward reward who who) :
    letI : Nonempty ι := ⟨who⟩
    quittingLiveMassLimit reward profile ≤
      quittingTerminalExploitability reward profile / quittingSoloReward reward who who := by
  letI : Nonempty ι := ⟨who⟩
  apply (le_div_iff₀ hsolo).mpr
  exact (quittingLiveMassLimit_mul_singleton_le_terminalDebt reward profile who).trans
    (quittingTerminalDeviationDebt_le_exploitability reward profile who)

/-- Every actual normalized source has Never mass at most its full exploitability. -/
theorem quittingLiveMassLimit_singlePivotNormalized_le_exploitability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (profile : (quittingGame (quittingSinglePivotNormalizedReward reward pivot)).BehaviorProfile)
    (hpivot : quittingSoloReward reward pivot pivot ≠ 0) :
    letI : Nonempty ι := ⟨pivot⟩
    quittingLiveMassLimit (quittingSinglePivotNormalizedReward reward pivot) profile ≤
      quittingTerminalExploitability
        (quittingSinglePivotNormalizedReward reward pivot) profile := by
  letI : Nonempty ι := ⟨pivot⟩
  have h := (quittingLiveMassLimit_mul_singleton_le_terminalDebt
    (quittingSinglePivotNormalizedReward reward pivot) profile pivot).trans
    (quittingTerminalDeviationDebt_le_exploitability
      (quittingSinglePivotNormalizedReward reward pivot) profile pivot)
  rw [quittingSoloReward_singlePivotNormalized reward pivot pivot hpivot] at h
  simpa using h

/-- The transformed full debt is an exact expression in the same original
profile's finite-date cap and its actual all-Never probability. -/
theorem quittingTerminalDeviationDebt_singlePivotNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot who : ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hpivot : 0 < quittingSoloReward reward pivot pivot) :
    quittingTerminalDeviationDebt (quittingSinglePivotNormalizedReward reward pivot) profile who =
      (quittingFinitePureReplyValue reward profile who - quittingTerminalPayoff reward profile who -
        quittingSinglePivotOffset reward pivot who * quittingLiveMassLimit reward profile) /
          quittingSoloReward reward pivot pivot := by
  unfold quittingTerminalDeviationDebt
  rw [quittingContinuationBestResponseValue_singlePivotNormalized reward pivot who profile hpivot,
    quittingTerminalPayoff_singlePivotNormalized reward pivot who profile]
  ring

/-- Forward profile transport needs a positive pivot, but not punishment
normality. Full exploitability scales by the displayed uniform constant. -/
theorem quittingTerminalExploitability_singlePivotNormalized_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (profile : (quittingGame reward).BehaviorProfile) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpivot : 0 < quittingSoloReward reward pivot pivot) :
    letI : Nonempty ι := ⟨pivot⟩
    quittingTerminalExploitability (quittingSinglePivotNormalizedReward reward pivot) profile ≤
      (1 / quittingSoloReward reward pivot pivot +
        bound / quittingSoloReward reward pivot pivot ^ 2) *
          quittingTerminalExploitability reward profile := by
  letI : Nonempty ι := ⟨pivot⟩
  have hbound : 0 ≤ bound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal pivot) pivot)
  have hreach := quittingLiveMassLimit_le_exploitability_div_singleton reward profile pivot hpivot
  rw [quittingTerminalExploitability_eq_max_debt]
  apply QuittingBoundaryHolonomy.finitePlayerMax_le
  intro who
  rw [quittingTerminalDeviationDebt_singlePivotNormalized reward pivot who profile hpivot]
  have hfinite := quittingFinitePureReplyValue_le_bestReplyValue reward profile who
  have hdebt := quittingTerminalDeviationDebt_le_exploitability reward profile who
  have hoffset := neg_le_of_abs_le (abs_quittingSinglePivotOffset_le reward pivot who hreward)
  have hneg := mul_le_mul_of_nonneg_right hoffset (quittingLiveMassLimit_nonneg reward profile)
  have hcap : quittingFinitePureReplyValue reward profile who -
      quittingTerminalPayoff reward profile who -
        quittingSinglePivotOffset reward pivot who * quittingLiveMassLimit reward profile ≤
      quittingTerminalExploitability reward profile +
        bound * quittingLiveMassLimit reward profile := by
    change quittingContinuationBestResponseValue reward profile who -
      quittingTerminalPayoff reward profile who ≤ _ at hdebt
    change quittingFinitePureReplyValue reward profile who ≤
      quittingContinuationBestResponseValue reward profile who at hfinite
    linarith
  calc
    _ ≤ (quittingTerminalExploitability reward profile +
        bound * quittingLiveMassLimit reward profile) / quittingSoloReward reward pivot pivot :=
      div_le_div_of_nonneg_right hcap hpivot.le
    _ ≤ (quittingTerminalExploitability reward profile + bound *
        (quittingTerminalExploitability reward profile / quittingSoloReward reward pivot pivot)) /
          quittingSoloReward reward pivot pivot := by
      apply div_le_div_of_nonneg_right _ hpivot.le
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hreach hbound)
    _ = _ := by
      field_simp [ne_of_gt hpivot]

end GameTheory
