import UniformEquilibrium.Quitting.Cycles.CrossedMatchingPhaseSource
import UniformEquilibrium.Quitting.Cycles.PairedCycleFiniteHorizon

/-! # Quantitative horizons for the actual crossed-matching cycles

One selected hazard vector precedes every initial phase and horizon. Signed
reward tables are allowed. The primary constants are `M * C / N` for delivery
and `2 * M * C / N` for arbitrary behavioral deviation gains; the printed
packet constants are their conservative weakenings.
-/

noncomputable section

namespace GameTheory.PairedCycle.CrossedMatching

open Math.LinearProgramming

def profileAt (reward : Reward) (q : Fin 4 → ℝ)
    (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1) (initial : Fin 2) :
    (quittingGame reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward (cycle fin4Schedule q (properUnitBounds q hproper)) initial

def timeConstant (q : Fin 4 → ℝ) (player : Fin 4) : ℝ :=
  1 + 2 / (1 - opponentCycleSurvival q player)

theorem timeConstant_pos (q : Fin 4 → ℝ)
    (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1) (player : Fin 4) :
    0 < timeConstant q player := by
  have hcontracts := cycle_opponents_contract fin4Schedule q (properUnitBounds q hproper)
    (fun player => (hproper player).1) player
  rw [prod_cycle_opponentsContinue] at hcontracts
  have hgap : 0 < 1 - opponentCycleSurvival q player := sub_pos.mpr hcontracts
  unfold timeConstant
  positivity

theorem opponentLiveCesaro_le_timeConstant (reward : Reward) (q : Fin 4 → ℝ)
    (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1)
    (initial : Fin 2) (player : Fin 4) (horizon : ℕ) :
    quittingOpponentLiveCesaro reward (profileAt reward q hproper initial) player horizon ≤
      timeConstant q player / (horizon : ℝ) := by
  have hclock := quittingOpponentLiveCesaro_cyclicBehaviorProfile_le reward
    (cycle fin4Schedule q (properUnitBounds q hproper)) initial player horizon
    (cycle_opponents_contract fin4Schedule q (properUnitBounds q hproper)
      (fun player => (hproper player).1) player)
  rw [prod_cycle_opponentsContinue] at hclock
  apply hclock.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg horizon)
  unfold timeConstant
  exact le_add_of_nonneg_left zero_le_one

/-- Actual outputs for one fixed phase profile, not hypotheses of a raw reward criterion. -/
structure ExactCycleRates (reward : Reward) (q : Fin 4 → ℝ)
    (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1) (initial : Fin 2) : Prop where
  terminal_value : quittingTerminalPayoff reward (profileAt reward q hproper initial) =
    twoPairPhaseValue reward fin4Schedule q initial
  terminal_nash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
    (profileAt reward q hproper initial)
  uniform_payoff : (quittingGame reward).IsUniformEquilibriumPayoff none
    (twoPairPhaseValue reward fin4Schedule q initial)
  delivery : ∀ (bound : ℝ) (player : Fin 4),
    (∀ terminal, |reward terminal player| ≤ bound) → ∀ horizon : ℕ, 0 < horizon →
      |(quittingGame reward).finiteAveragePayoff none horizon
          (profileAt reward q hproper initial) player -
        twoPairPhaseValue reward fin4Schedule q initial player| ≤
          bound * timeConstant q player / (horizon : ℝ)
  deviation_gain : ∀ (bound : ℝ) (player : Fin 4),
    (∀ terminal, |reward terminal player| ≤ bound) →
      ∀ (deviation : (quittingGame reward).BehaviorStrategy player)
        (horizon : ℕ), 0 < horizon →
        (quittingGame reward).finiteAveragePayoff none horizon
            (Function.update (profileAt reward q hproper initial) player deviation) player -
          (quittingGame reward).finiteAveragePayoff none horizon
            (profileAt reward q hproper initial) player ≤
              2 * bound * timeConstant q player / (horizon : ℝ)

theorem exactCycleRates_of_terminal_certificate (reward : Reward) (q : Fin 4 → ℝ)
    (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1) (initial : Fin 2)
    (hvalue : quittingTerminalPayoff reward (profileAt reward q hproper initial) =
      twoPairPhaseValue reward fin4Schedule q initial)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (profileAt reward q hproper initial))
    (hpayoff : (quittingGame reward).IsUniformEquilibriumPayoff none
      (twoPairPhaseValue reward fin4Schedule q initial)) :
    ExactCycleRates reward q hproper initial := by
  refine ⟨hvalue, hnash, hpayoff, ?_, ?_⟩
  · intro bound player hreward horizon hhorizon
    have hdelivery := finiteAverage_delivery_le_of_opponentLiveCesaro_bound reward
      (profileAt reward q hproper initial) player horizon hhorizon bound
      (timeConstant q player) hreward
      (opponentLiveCesaro_le_timeConstant reward q hproper initial player horizon)
    simpa only [hvalue] using hdelivery
  · intro bound player hreward deviation horizon hhorizon
    exact finiteAverage_deviation_gain_le_of_exact_terminalNash_and_opponentLiveCesaro_bound
      reward (profileAt reward q hproper initial) hnash player deviation horizon hhorizon
      bound (timeConstant q player) hreward
      (opponentLiveCesaro_le_timeConstant reward q hproper initial player horizon)

/-- The raw matching and Q tests select ONE vector before all phases and horizons. -/
theorem exists_quantitative_cycle_of_standardQ {reward : Reward} (hraw : RawSource reward)
    (hQ : IsStandardQ (quittingProjectiveLCPMatrix reward)) :
    ∃ (q : Fin 4 → ℝ) (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1),
      ∀ initial : Fin 2, ExactCycleRates reward q hproper initial := by
  obtain ⟨q, hproper, hresult⟩ := exists_exact_cycle_of_standardQ_all_initial hraw hQ
  refine ⟨q, hproper, fun initial => ?_⟩
  exact exactCycleRates_of_terminal_certificate reward q hproper initial
    (hresult initial).1 (hresult initial).2.1 (hresult initial).2.2.2

/-- No matching-sign or Q premise is added to the inverse-positive alternative. -/
theorem exists_quantitative_cycle_of_positive_inverse {reward : Reward}
    (hraw : InverseRawSource reward) :
    ∃ (q : Fin 4 → ℝ) (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1),
      ∀ initial : Fin 2, ExactCycleRates reward q hproper initial := by
  obtain ⟨q, hproper, hresult⟩ := exists_exact_cycle_of_positive_inverse_all_initial hraw
  refine ⟨q, hproper, fun initial => ?_⟩
  exact exactCycleRates_of_terminal_certificate reward q hproper initial
    (hresult initial).1 (hresult initial).2.1 (hresult initial).2.2.2

theorem ExactCycleRates.delivery_printed {reward : Reward} {q : Fin 4 → ℝ}
    {hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1} {initial : Fin 2}
    (hrates : ExactCycleRates reward q hproper initial)
    (bound : ℝ) (player : Fin 4) (hreward : ∀ terminal, |reward terminal player| ≤ bound)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame reward).finiteAveragePayoff none horizon
        (profileAt reward q hproper initial) player -
      twoPairPhaseValue reward fin4Schedule q initial player| ≤
        2 * bound * timeConstant q player / (horizon : ℝ) := by
  have hbound : 0 ≤ bound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal player))
  have htime := (timeConstant_pos q hproper player).le
  have hnonnegative : 0 ≤ bound * timeConstant q player / (horizon : ℝ) := by positivity
  have htwice : 2 * bound * timeConstant q player / (horizon : ℝ) =
      2 * (bound * timeConstant q player / (horizon : ℝ)) := by ring
  rw [htwice]
  linarith [hrates.delivery bound player hreward horizon hhorizon]

theorem ExactCycleRates.deviation_gain_printed {reward : Reward} {q : Fin 4 → ℝ}
    {hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1} {initial : Fin 2}
    (hrates : ExactCycleRates reward q hproper initial)
    (bound : ℝ) (player : Fin 4) (hreward : ∀ terminal, |reward terminal player| ≤ bound)
    (deviation : (quittingGame reward).BehaviorStrategy player)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (profileAt reward q hproper initial) player deviation) player -
      (quittingGame reward).finiteAveragePayoff none horizon
        (profileAt reward q hproper initial) player ≤
          4 * bound * timeConstant q player / (horizon : ℝ) := by
  have hbound : 0 ≤ bound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal player))
  have htime := (timeConstant_pos q hproper player).le
  have hnonnegative : 0 ≤ 2 * bound * timeConstant q player / (horizon : ℝ) := by positivity
  have htwice : 4 * bound * timeConstant q player / (horizon : ℝ) =
      2 * (2 * bound * timeConstant q player / (horizon : ℝ)) := by ring
  rw [htwice]
  linarith [hrates.deviation_gain bound player hreward deviation horizon hhorizon]

end GameTheory.PairedCycle.CrossedMatching
