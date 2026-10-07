import UniformEquilibrium.Quitting.Cycles.NegativePremiumCyclicChildSource
import UniformEquilibrium.Quitting.Cycles.PeriodicFiniteHorizonRate
import Mathlib.Data.Finset.Lattice.Fold

/-! # Exact finite-horizon constants for negative-premium cyclic-child sources

The magnitude is the maximum of all sixty absolute original reward coordinates.
The opponent products and the common constant are computed from actual rates.
Both signed boundary errors use the same original opponent clock.
-/

noncomputable section

namespace GameTheory.NegativePremiumCyclicChild

abbrev Coordinate := {S : Finset Player // S.Nonempty} × Player

def rewardMagnitude (reward : Reward) : ℝ :=
  Finset.univ.sup' ⟨(quittingSingletonTerminal 0, 0), Finset.mem_univ _⟩
    (fun coordinate : Coordinate => |reward coordinate.1 coordinate.2|)

theorem abs_reward_le_magnitude (reward : Reward)
    (terminal : {S : Finset Player // S.Nonempty}) (who : Player) :
    |reward terminal who| ≤ rewardMagnitude reward :=
  Finset.le_sup' (f := fun coordinate : Coordinate => |reward coordinate.1 coordinate.2|)
    (Finset.mem_univ (terminal, who))

theorem rewardMagnitude_nonneg (reward : Reward) : 0 ≤ rewardMagnitude reward :=
  (abs_nonneg (reward (quittingSingletonTerminal 0) 0)).trans
    (abs_reward_le_magnitude reward _ _)

def reciprocalGap (rates : Rates) (who : Player) : ℝ :=
  1 / (1 - opponentProduct rates who)

theorem reciprocalGap_pos (rates : Rates) (who : Player) : 0 < reciprocalGap rates who := by
  have hcontract := cycle_contracts rates who
  rw [cycle_opponentProduct] at hcontract
  exact one_div_pos.mpr (sub_pos.mpr hcontract)

def maximumReciprocalGap (rates : Rates) : ℝ :=
  Finset.univ.sup' ⟨0, Finset.mem_univ _⟩ (reciprocalGap rates)

theorem reciprocalGap_le_maximum (rates : Rates) (who : Player) :
    reciprocalGap rates who ≤ maximumReciprocalGap rates :=
  Finset.le_sup' (f := reciprocalGap rates) (Finset.mem_univ who)

theorem maximumReciprocalGap_pos (rates : Rates) : 0 < maximumReciprocalGap rates :=
  (reciprocalGap_pos rates 0).trans_le (reciprocalGap_le_maximum rates 0)

def coordinateConstant (reward : Reward) (rates : Rates) (who : Player) : ℝ :=
  3 * rewardMagnitude reward * reciprocalGap rates who

/-- The packet constant: three times the actual reward magnitude times the
maximum reciprocal of the four actual opponent-contraction gaps. -/
def horizonConstant (reward : Reward) (rates : Rates) : ℝ :=
  3 * rewardMagnitude reward * maximumReciprocalGap rates

theorem horizonConstant_nonneg (reward : Reward) (rates : Rates) :
    0 ≤ horizonConstant reward rates := by
  exact mul_nonneg (mul_nonneg (by norm_num) (rewardMagnitude_nonneg reward))
    (maximumReciprocalGap_pos rates).le

theorem coordinateConstant_le (reward : Reward) (rates : Rates) (who : Player) :
    coordinateConstant reward rates who ≤ horizonConstant reward rates :=
  mul_le_mul_of_nonneg_left (reciprocalGap_le_maximum rates who)
    (mul_nonneg (by norm_num) (rewardMagnitude_nonneg reward))

theorem opponentClock_le (reward : Reward) (rates : Rates) (who : Player) (horizon : ℕ) :
    quittingOpponentLiveCesaro reward
      (quittingCyclicBehaviorProfile reward (cycle rates) 0) who horizon ≤
        (3 * reciprocalGap rates who) / (horizon : ℝ) := by
  have hclock := quittingOpponentLiveCesaro_cyclicBehaviorProfile_le reward
    (cycle rates) 0 who horizon (cycle_contracts rates who)
  rw [cycle_opponentProduct] at hclock
  simpa only [reciprocalGap, mul_one_div, Nat.cast_ofNat] using hclock

/-- Prescribed delivery with the player-specific constant. -/
theorem delivery_le_coordinateConstant (reward : Reward) (rates : Rates)
    (who : Player) (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame reward).finiteAveragePayoff none horizon
        (quittingCyclicBehaviorProfile reward (cycle rates) 0) who -
      quittingTerminalPayoff reward
        (quittingCyclicBehaviorProfile reward (cycle rates) 0) who| ≤
      coordinateConstant reward rates who / (horizon : ℝ) := by
  have hdelivery := finiteAverage_delivery_le_of_opponentLiveCesaro_bound reward
    (quittingCyclicBehaviorProfile reward (cycle rates) 0) who horizon hhorizon
    (rewardMagnitude reward) (3 * reciprocalGap rates who)
    (fun terminal => abs_reward_le_magnitude reward terminal who)
    (opponentClock_le reward rates who horizon)
  convert hdelivery using 1
  simp only [coordinateConstant]
  ring

/-- Any complete behavioral replacement has both signed boundary errors
bounded by the same original opponent clock. -/
theorem deviation_boundary_le_coordinateConstant (reward : Reward) (rates : Rates)
    (who : Player) (deviation : (quittingGame reward).BehaviorStrategy who)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (quittingCyclicBehaviorProfile reward (cycle rates) 0) who deviation)
        who - quittingTerminalPayoff reward
        (Function.update (quittingCyclicBehaviorProfile reward (cycle rates) 0) who deviation)
        who| ≤ coordinateConstant reward rates who / (horizon : ℝ) := by
  have hboundary := abs_finiteAveragePayoff_update_sub_terminal_le_opponentLiveCesaro
    reward (quittingCyclicBehaviorProfile reward (cycle rates) 0) who deviation horizon hhorizon
      (rewardMagnitude reward) (fun terminal => abs_reward_le_magnitude reward terminal who)
  have hclock := mul_le_mul_of_nonneg_left
    (opponentClock_le reward rates who horizon) (rewardMagnitude_nonneg reward)
  apply hboundary.trans
  convert hclock using 1
  simp only [coordinateConstant]
  ring

/-- A complete behavioral replacement is bounded by the same fixed terminal
target plus one boundary charge, not two. -/
theorem deviation_payoff_le_target_coordinateConstant (reward : Reward) (rates : Rates)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingCyclicBehaviorProfile reward (cycle rates) 0))
    (who : Player) (deviation : (quittingGame reward).BehaviorStrategy who)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (quittingCyclicBehaviorProfile reward (cycle rates) 0) who deviation)
        who ≤ quittingTerminalPayoff reward
          (quittingCyclicBehaviorProfile reward (cycle rates) 0) who +
        coordinateConstant reward rates who / (horizon : ℝ) := by
  have hboundary := (abs_le.mp (deviation_boundary_le_coordinateConstant
    reward rates who deviation horizon hhorizon)).2
  have hterminal := hnash who deviation
  simp only [add_zero] at hterminal
  linarith

theorem deviation_payoff_le_target (reward : Reward) (rates : Rates)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingCyclicBehaviorProfile reward (cycle rates) 0))
    (who : Player) (deviation : (quittingGame reward).BehaviorStrategy who)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (quittingCyclicBehaviorProfile reward (cycle rates) 0) who deviation)
        who ≤ quittingTerminalPayoff reward
          (quittingCyclicBehaviorProfile reward (cycle rates) 0) who +
        horizonConstant reward rates / (horizon : ℝ) := by
  exact (deviation_payoff_le_target_coordinateConstant
    reward rates hnash who deviation horizon hhorizon).trans (add_le_add le_rfl
      (div_le_div_of_nonneg_right (coordinateConstant_le reward rates who)
        (Nat.cast_nonneg horizon)))

theorem deviation_gain_le_coordinateConstant (reward : Reward) (rates : Rates)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingCyclicBehaviorProfile reward (cycle rates) 0))
    (who : Player) (deviation : (quittingGame reward).BehaviorStrategy who)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (quittingCyclicBehaviorProfile reward (cycle rates) 0) who deviation)
        who - (quittingGame reward).finiteAveragePayoff none horizon
          (quittingCyclicBehaviorProfile reward (cycle rates) 0) who ≤
        2 * coordinateConstant reward rates who / (horizon : ℝ) := by
  have hgain :=
    finiteAverage_deviation_gain_le_of_exact_terminalNash_and_opponentLiveCesaro_bound
      reward (quittingCyclicBehaviorProfile reward (cycle rates) 0) hnash who deviation
      horizon hhorizon (rewardMagnitude reward) (3 * reciprocalGap rates who)
      (fun terminal => abs_reward_le_magnitude reward terminal who)
      (opponentClock_le reward rates who horizon)
  convert hgain using 1
  simp only [coordinateConstant]
  ring

theorem horizonNash_of_terminalNash (reward : Reward) (rates : Rates)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingCyclicBehaviorProfile reward (cycle rates) 0))
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame reward).IsεHorizonNash none horizon
      (2 * horizonConstant reward rates / (horizon : ℝ))
      (quittingCyclicBehaviorProfile reward (cycle rates) 0) := by
  intro who deviation
  have hgain := deviation_gain_le_coordinateConstant
    reward rates hnash who deviation horizon hhorizon
  have hcommon : 2 * coordinateConstant reward rates who / (horizon : ℝ) ≤
      2 * horizonConstant reward rates / (horizon : ℝ) := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (coordinateConstant_le reward rates who) (by norm_num))
      (Nat.cast_nonneg horizon)
  simpa only [add_comm] using sub_le_iff_le_add.mp (hgain.trans hcommon)

def horizonThreshold (reward : Reward) (rates : Rates) (accuracy : ℝ) : ℕ :=
  max 1 ⌈2 * horizonConstant reward rates / accuracy⌉₊

theorem threshold_spec (reward : Reward) (rates : Rates) {accuracy : ℝ}
    (haccuracy : 0 < accuracy) {horizon : ℕ}
    (hhorizon : horizonThreshold reward rates accuracy ≤ horizon) :
    0 < horizon ∧ 2 * horizonConstant reward rates / (horizon : ℝ) ≤ accuracy := by
  have hceil : ⌈2 * horizonConstant reward rates / accuracy⌉₊ ≤ horizon :=
    (le_max_right _ _).trans hhorizon
  have hpositive : 0 < horizon := by
    have hle : 1 ≤ horizon := (le_max_left _ _).trans hhorizon
    omega
  refine ⟨hpositive, ?_⟩
  have hbound := (Nat.le_ceil (2 * horizonConstant reward rates / accuracy)).trans
    (show (⌈2 * horizonConstant reward rates / accuracy⌉₊ : ℝ) ≤ horizon by
      exact_mod_cast hceil)
  apply (div_le_iff₀ (show 0 < (horizon : ℝ) by exact_mod_cast hpositive)).mpr
  have hproduct := (div_le_iff₀ haccuracy).mp hbound
  nlinarith only [hproduct]

/-- The raw signed table supplies the profile and target before accuracy;
all finite-horizon bounds use the exact constant computed from original rewards. -/
theorem SignedRawTable.exists_quantitative_fixed_target {loss : ℝ}
    {own scale : Payoff Player} {reward : Reward} (table : SignedRawTable loss own scale reward) :
    ∃ (rates : Rates) (target : Payoff Player),
      let profile := quittingCyclicBehaviorProfile reward (cycle rates) 0
      quittingTerminalPayoff reward profile = target ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 profile ∧
      (∀ horizon, 0 < horizon →
        (∀ who, |(quittingGame reward).finiteAveragePayoff none horizon profile who -
          target who| ≤ horizonConstant reward rates / (horizon : ℝ)) ∧
        (∀ who (deviation : (quittingGame reward).BehaviorStrategy who),
          (quittingGame reward).finiteAveragePayoff none horizon
            (Function.update profile who deviation) who ≤
              target who + horizonConstant reward rates / (horizon : ℝ)) ∧
        (quittingGame reward).IsεHorizonNash none horizon
          (2 * horizonConstant reward rates / (horizon : ℝ)) profile) ∧
      ∀ accuracy, 0 < accuracy → ∀ horizon,
        horizonThreshold reward rates accuracy ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon accuracy profile ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon profile who -
            target who| ≤ accuracy := by
  obtain ⟨canonical, hterminal, hnash, _, _⟩ := table.exists_terminalNash_fixed_target
  let rates := canonical.rates
  let target := fun who => own who + scale who * (canonical.value 0 who - 1)
  have hdelivery (horizon : ℕ) (hhorizon : 0 < horizon) (who : Player) :
      |(quittingGame reward).finiteAveragePayoff none horizon
          (quittingCyclicBehaviorProfile reward (cycle rates) 0) who - target who| ≤
        horizonConstant reward rates / (horizon : ℝ) := by
    have herror := delivery_le_coordinateConstant reward rates who horizon hhorizon
    rw [hterminal] at herror
    exact herror.trans (div_le_div_of_nonneg_right
      (coordinateConstant_le reward rates who) (Nat.cast_nonneg horizon))
  refine ⟨rates, target, hterminal, hnash, ?_, ?_⟩
  · intro horizon hhorizon
    refine ⟨hdelivery horizon hhorizon, ?_,
      horizonNash_of_terminalNash reward rates hnash horizon hhorizon⟩
    intro who deviation
    have hbound := deviation_payoff_le_target reward rates hnash who deviation horizon hhorizon
    rw [hterminal] at hbound
    exact hbound
  · intro accuracy haccuracy horizon hhorizon
    obtain ⟨hpositive, hbudget⟩ := threshold_spec reward rates haccuracy hhorizon
    refine ⟨(horizonNash_of_terminalNash reward rates hnash horizon hpositive).mono hbudget, ?_⟩
    intro who
    have hhalf : horizonConstant reward rates / (horizon : ℝ) ≤
        2 * horizonConstant reward rates / (horizon : ℝ) := by
      exact div_le_div_of_nonneg_right
        (by nlinarith only [horizonConstant_nonneg reward rates]) (Nat.cast_nonneg horizon)
    exact (hdelivery horizon hpositive who).trans (hhalf.trans hbudget)

end GameTheory.NegativePremiumCyclicChild
