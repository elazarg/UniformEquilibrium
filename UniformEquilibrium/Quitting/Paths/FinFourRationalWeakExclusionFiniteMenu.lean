import UniformEquilibrium.Quitting.Paths.RationalWeakExclusionTwoBranchSelection
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineHorizonError
import UniformEquilibrium.Quitting.Terminal.SinglePivotFiniteMenuSource

/-! # Same-word rational four-player menu and late-pivot bounds

The literal singleton vector is (1,0,0,0). Both displayed-menu error and the
pivot's post-cutoff scalar refer to the exact independent laws of the computed
two-branch word, not to a second selector or a replaced pivot law. No target is
computed; the underlying selector retains Never and every late reply.
-/

noncomputable section

namespace GameTheory

private theorem rationalFinFourSinglePivot_bound_pos
    (reward : RationalQuittingReward 4)
    (hcanonical : ∀ who, reward (quittingSingletonTerminal who) who =
      if who = 0 then 1 else 0) {M : ℚ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) : 0 < M := by
  have hbound := hreward (quittingSingletonTerminal 0) 0
  rw [hcanonical 0, ite_eq_left rfl, abs_one] at hbound
  linarith

/-- Arbitrary positive rational accuracy controls BOTH finite-menu errors on
the SAME independent laws and full-cap pair of the actual two-branch output. -/
theorem executableRationalWeakExclusionTwoBranchWord_finFour_menu_and_latePivot
    (reward : RationalQuittingReward 4)
    (hcanonical : ∀ who, reward (quittingSingletonTerminal who) who =
      if who = 0 then 1 else 0)
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward Finset.univ)
    (M : ℚ) (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    let hM := rationalFinFourSinglePivot_bound_pos reward hcanonical hreward
    let word := executableRationalWeakExclusionTwoBranchWord
      reward Finset.univ hWE M hM hreward accuracy haccuracy
    ∃ mixed : Fin 4 → PMF (Option (Fin word.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length who choice : ℝ)) ∧
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
            word.length mixed) =
        (rationalQuittingFiniteWordSemanticPair reward word).toReal ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
            (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
              word.length mixed)) ≤ (accuracy : ℝ) ∧
      quittingFiniteDeadlineMenuExploitability (rationalQuittingRewardToReal reward)
          word.length mixed ≤ (accuracy : ℝ) ∧
      quittingFiniteDeadlineNeverPayoff (rationalQuittingRewardToReal reward)
          word.length mixed 0 +
          quittingFiniteDeadlineOpponentNeverProduct word.length mixed 0 -
          quittingTerminalPayoff (rationalQuittingRewardToReal reward)
            (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
              word.length mixed) 0 ≤ (accuracy : ℝ) ∧
      (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
        (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) (accuracy : ℝ)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) ∧
      (∀ horizon, 0 < horizon → ∀ who,
        |(quittingGame (rationalQuittingRewardToReal reward)).finiteAveragePayoff none horizon
              (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
                word.length mixed) who -
            quittingTerminalPayoff (rationalQuittingRewardToReal reward)
              (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
                word.length mixed) who| ≤ (M : ℝ) * word.length / horizon) ∧
      ∀ horizon, 0 < horizon →
        (quittingGame (rationalQuittingRewardToReal reward)).IsεHorizonNash none horizon
          ((accuracy : ℝ) + 2 * (M : ℝ) * (word.length + 1) / horizon)
          (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
            word.length mixed) := by
  dsimp only
  have hM := rationalFinFourSinglePivot_bound_pos reward hcanonical hreward
  let word := executableRationalWeakExclusionTwoBranchWord
    reward Finset.univ hWE M hM hreward accuracy haccuracy
  have hsingleton : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who := by
    intro who
    rw [hcanonical who]
    split <;> norm_num
  obtain ⟨mixed, hmass, hpair, hdebt, hnash⟩ :=
    executableRationalWeakExclusionTwoBranchWord_finiteLaws
      reward Finset.univ hWE M hM hreward accuracy haccuracy
      (fun who _ => hsingleton who)
  have hcanonicalReal : IsSinglePivotSingletonTable
      (rationalQuittingRewardToReal reward) 0 := by
    intro who
    change (reward (quittingSingletonTerminal who) who : ℝ) = _
    rw [hcanonical who]
    split <;> norm_num
  have hboundReal : ∀ terminal who,
      |rationalQuittingRewardToReal reward terminal who| ≤ (M : ℝ) := by
    intro terminal who
    change |(reward terminal who : ℝ)| ≤ (M : ℝ)
    exact_mod_cast hreward terminal who
  have hsingletonReal : ∀ who,
      0 ≤ rationalQuittingRewardToReal reward (quittingSingletonTerminal who) who := by
    intro who
    change (0 : ℝ) ≤ (reward (quittingSingletonTerminal who) who : ℝ)
    exact_mod_cast hsingleton who
  have haccuracyReal : (0 : ℝ) ≤ accuracy := by exact_mod_cast haccuracy.le
  have hexploit := quittingTerminalExploitability_le_of_isεAsymptoticNash
    (rationalQuittingRewardToReal reward)
    (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
      word.length mixed) haccuracyReal hnash
  have hmax := singlePivot_fullExploitability_eq_max_menuExploitability_scalar
    (rationalQuittingRewardToReal reward) 0 hcanonicalReal word.length mixed
  refine ⟨mixed, hmass, hpair, hdebt, ?_, ?_, hnash, ?_, ?_⟩
  · exact (le_max_left _ _).trans (hmax ▸ hexploit)
  · exact (le_max_right _ _).trans (hmax ▸ hexploit)
  · intro horizon hhorizon who
    exact abs_finiteAveragePayoff_sub_terminal_finiteDeadline_le
      (rationalQuittingRewardToReal reward) word.length horizon mixed who
      (fun terminal => hboundReal terminal who) hhorizon
  · intro horizon hhorizon
    exact isHorizonNash_finiteDeadline_of_terminalNash_add_one
      (rationalQuittingRewardToReal reward) word.length horizon mixed hnash
      hboundReal hsingletonReal hhorizon

end GameTheory
