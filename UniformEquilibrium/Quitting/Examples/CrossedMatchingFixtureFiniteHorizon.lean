import UniformEquilibrium.Quitting.Examples.CrossedMatchingFixture
import UniformEquilibrium.Quitting.Cycles.CrossedMatchingFiniteHorizon

/-! # Explicit reciprocal-horizon bounds for the crossed-matching fixture

One rational hazard vector supplies both phase-dependent profiles. The stronger
delivery and unilateral-regret constants are `77 / N` and `154 / N`; the printed
`154 / N` and `308 / N` constants follow by weakening these bounds.
-/

noncomputable section

namespace GameTheory.CrossedMatchingFixture

open PairedCycle

theorem reward_bound (terminal : {S : Finset (Fin 4) // S.Nonempty}) (player : Fin 4) :
    |reward terminal player| ≤ 14 := by
  obtain ⟨row, rfl⟩ := Math.Finset.finFourCoalitionRowEquiv.surjective terminal
  rw [reward_rows]
  fin_cases row <;> fin_cases player <;> norm_num

theorem opponentCycleSurvival_eq (player : Fin 4) :
    PairedCycle.opponentCycleSurvival (TwoPairOdds.hazard odds) player =
      (![5 / 9, 8 / 15, 5 / 9, 8 / 15] : Fin 4 → ℝ) player := by
  have hproduct := Finset.prod_erase_mul Finset.univ
    (fun other : Fin 4 => 1 - TwoPairOdds.hazard odds other) (Finset.mem_univ player)
  change PairedCycle.opponentCycleSurvival (TwoPairOdds.hazard odds) player *
    (1 - TwoPairOdds.hazard odds player) = _ at hproduct
  norm_num [Fin.prod_univ_succ, TwoPairOdds.hazard, odds] at hproduct
  fin_cases player <;> norm_num [TwoPairOdds.hazard, odds] at hproduct ⊢ <;> linarith

theorem timeConstant_eq (player : Fin 4) :
    PairedCycle.CrossedMatching.timeConstant (TwoPairOdds.hazard odds) player =
      (![11 / 2, 37 / 7, 11 / 2, 37 / 7] : Fin 4 → ℝ) player := by
  rw [PairedCycle.CrossedMatching.timeConstant, opponentCycleSurvival_eq]
  fin_cases player <;> norm_num

theorem timeConstant_le (player : Fin 4) :
    PairedCycle.CrossedMatching.timeConstant (TwoPairOdds.hazard odds) player ≤ 11 / 2 := by
  rw [timeConstant_eq]
  fin_cases player <;> norm_num

theorem exactCycleRates (initial : Fin 2) :
    PairedCycle.CrossedMatching.ExactCycleRates reward (TwoPairOdds.hazard odds)
      (TwoPairOdds.hazard_proper odds_positive) initial := by
  apply PairedCycle.CrossedMatching.exactCycleRates_of_terminal_certificate
  · simpa only [PairedCycle.CrossedMatching.profileAt, profile, phaseValue_eq] using
      (exact_terminal_and_fixedProfile initial).1
  · simpa only [PairedCycle.CrossedMatching.profileAt, profile] using
      (exact_terminal_and_fixedProfile initial).2.1
  · simpa only [phaseValue_eq] using
      (exact_terminal_and_fixedProfile initial).2.2.2

theorem finiteAverage_delivery_le (initial : Fin 2) (player : Fin 4)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame reward).finiteAveragePayoff none horizon (profile initial) player -
      phaseValues initial player| ≤ 77 / (horizon : ℝ) := by
  have hsharp : |(quittingGame reward).finiteAveragePayoff none horizon
      (profile initial) player - phaseValues initial player| ≤
        14 * PairedCycle.CrossedMatching.timeConstant (TwoPairOdds.hazard odds) player /
          (horizon : ℝ) := by
    simpa only [PairedCycle.CrossedMatching.profileAt, profile, phaseValue_eq] using
      (exactCycleRates initial).delivery 14 player (fun terminal => reward_bound terminal player)
        horizon hhorizon
  apply hsharp.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg horizon)
  calc
    14 * PairedCycle.CrossedMatching.timeConstant (TwoPairOdds.hazard odds) player ≤
        14 * (11 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (timeConstant_le player) (by norm_num)
    _ = 77 := by norm_num

theorem finiteAverage_deviation_gain_le (initial : Fin 2) (player : Fin 4)
    (deviation : (quittingGame reward).BehaviorStrategy player)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (profile initial) player deviation) player -
      (quittingGame reward).finiteAveragePayoff none horizon (profile initial) player ≤
        154 / (horizon : ℝ) := by
  have hsharp : (quittingGame reward).finiteAveragePayoff none horizon
      (Function.update (profile initial) player deviation) player -
    (quittingGame reward).finiteAveragePayoff none horizon (profile initial) player ≤
      2 * 14 * PairedCycle.CrossedMatching.timeConstant (TwoPairOdds.hazard odds) player /
        (horizon : ℝ) := by
    simpa only [PairedCycle.CrossedMatching.profileAt, profile] using
      (exactCycleRates initial).deviation_gain 14 player
        (fun terminal => reward_bound terminal player) deviation horizon hhorizon
  apply hsharp.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg horizon)
  calc
    2 * 14 * PairedCycle.CrossedMatching.timeConstant (TwoPairOdds.hazard odds) player ≤
        (2 * 14) * (11 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (timeConstant_le player) (by norm_num)
    _ = 154 := by norm_num

theorem isHorizonNash (initial : Fin 2) (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame reward).IsεHorizonNash none horizon (154 / (horizon : ℝ))
      (profile initial) := by
  intro player deviation
  have hgain := finiteAverage_deviation_gain_le initial player deviation horizon hhorizon
  linarith

theorem finiteAverage_delivery_le_printed (initial : Fin 2) (player : Fin 4)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame reward).finiteAveragePayoff none horizon (profile initial) player -
      phaseValues initial player| ≤ 154 / (horizon : ℝ) :=
  (finiteAverage_delivery_le initial player horizon hhorizon).trans
    (div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg horizon))

theorem finiteAverage_deviation_gain_le_printed (initial : Fin 2) (player : Fin 4)
    (deviation : (quittingGame reward).BehaviorStrategy player)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (profile initial) player deviation) player -
      (quittingGame reward).finiteAveragePayoff none horizon (profile initial) player ≤
        308 / (horizon : ℝ) :=
  (finiteAverage_deviation_gain_le initial player deviation horizon hhorizon).trans
    (div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg horizon))

end GameTheory.CrossedMatchingFixture
