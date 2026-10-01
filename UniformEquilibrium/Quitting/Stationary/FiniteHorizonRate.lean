import UniformEquilibrium.Quitting.Cycles.PeriodicFiniteHorizonRate
import UniformEquilibrium.Quitting.Stationary.Root

/-! # Explicit finite-horizon rate for contracting stationary terminal Nash -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The period-one specialization of the canonical cyclic survival bound. -/
theorem quittingOpponentLiveCesaro_stationary_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (horizon : ℕ)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1) :
    quittingOpponentLiveCesaro reward (quittingStationaryProfile reward root) who horizon ≤
      (1 / (1 - quittingStationaryFixedOpponentsContinueMass root who)) / (horizon : ℝ) := by
  have hprofile : quittingCyclicBehaviorProfile reward (fun _ : Fin 1 => root) 0 =
      quittingStationaryProfile reward root := rfl
  have hcycle : (∏ phase : Fin 1,
      quittingStationaryFixedOpponentsContinueMass ((fun _ : Fin 1 => root) phase) who) < 1 := by
    simpa only [Fin.prod_univ_one] using hcontracts
  simpa only [hprofile, Fin.prod_univ_one, Nat.cast_one] using
    quittingOpponentLiveCesaro_cyclicBehaviorProfile_le reward (fun _ : Fin 1 => root)
      0 who horizon hcycle

/-- Every complete behavioral reply against the SAME stationary opponents
has two-sided terminal/horizon error with the literal playerwise denominator. -/
theorem abs_finiteAveragePayoff_update_stationary_sub_terminal_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (horizon : ℕ) (hhorizon : 0 < horizon)
    (bound : ℝ)
    (hreward : ∀ terminal, |reward terminal who| ≤ bound)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1) :
    |(quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (quittingStationaryProfile reward root) who deviation) who -
      quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) who deviation) who| ≤
      bound / ((1 - quittingStationaryFixedOpponentsContinueMass root who) * (horizon : ℝ)) := by
  have hbound : 0 ≤ bound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal who))
  have hclock := mul_le_mul_of_nonneg_left
    (quittingOpponentLiveCesaro_stationary_le reward root who horizon hcontracts) hbound
  have hscaled : bound * quittingOpponentLiveCesaro reward
      (quittingStationaryProfile reward root) who horizon ≤
        bound / ((1 - quittingStationaryFixedOpponentsContinueMass root who) *
          (horizon : ℝ)) := by
    simpa only [div_div, mul_one_div] using hclock
  exact (abs_finiteAveragePayoff_update_sub_terminal_le_opponentLiveCesaro reward
    (quittingStationaryProfile reward root) who deviation horizon hhorizon
      bound hreward).trans hscaled

/-- Prescribed delivery is the no-change specialization of the all-reply estimate. -/
theorem abs_finiteAveragePayoff_stationary_sub_terminal_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (horizon : ℕ) (hhorizon : 0 < horizon)
    (bound : ℝ)
    (hreward : ∀ terminal, |reward terminal who| ≤ bound)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1) :
    |(quittingGame reward).finiteAveragePayoff none horizon
        (quittingStationaryProfile reward root) who -
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
      bound / ((1 - quittingStationaryFixedOpponentsContinueMass root who) * (horizon : ℝ)) := by
  simpa only [Function.update_eq_self] using
    abs_finiteAveragePayoff_update_stationary_sub_terminal_le reward root who
      ((quittingStationaryProfile reward root) who) horizon hhorizon bound hreward hcontracts

/-- Actual terminal Nash yields a player-specific finite-horizon regret bound.
No contraction of the deviator's own clock is needed. -/
theorem finiteAveragePayoff_update_stationary_le_add_playerwise_error
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (horizon : ℕ) (hhorizon : 0 < horizon)
    (bound : ℝ)
    (hreward : ∀ terminal, |reward terminal who| ≤ bound)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root)) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (quittingStationaryProfile reward root) who deviation) who ≤
      (quittingGame reward).finiteAveragePayoff none horizon
          (quittingStationaryProfile reward root) who +
        2 * bound /
          ((1 - quittingStationaryFixedOpponentsContinueMass root who) * (horizon : ℝ)) := by
  have hdelivery := abs_finiteAveragePayoff_stationary_sub_terminal_le reward root who
    horizon hhorizon bound hreward hcontracts
  have hreply := abs_finiteAveragePayoff_update_stationary_sub_terminal_le reward root who
    deviation horizon hhorizon bound hreward hcontracts
  have hterminal := hnash who deviation
  simp only [add_zero] at hterminal
  have hdouble :
      bound / ((1 - quittingStationaryFixedOpponentsContinueMass root who) * (horizon : ℝ)) +
        bound / ((1 - quittingStationaryFixedOpponentsContinueMass root who) * (horizon : ℝ)) =
      2 * bound /
        ((1 - quittingStationaryFixedOpponentsContinueMass root who) * (horizon : ℝ)) := by
    ring
  linarith [(abs_le.mp hdelivery).1, (abs_le.mp hreply).2]

/-- Exact stationary terminal Nash and a positive uniform deleted-clock gap
give regret at most `2M/(gap·H)` against every behavioral deviation. -/
theorem isHorizonNash_stationary_of_terminalNash_and_opponentGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (bound gap : ℝ) (hbound : 0 ≤ bound) (hgap : 0 < gap)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hopponents : ∀ who, quittingStationaryFixedOpponentsContinueMass root who ≤ 1 - gap)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root))
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame reward).IsεHorizonNash none horizon (2 * bound / (gap * (horizon : ℝ)))
      (quittingStationaryProfile reward root) := by
  intro who deviation
  have hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    linarith [hopponents who]
  have hinverse : 1 / (1 - quittingStationaryFixedOpponentsContinueMass root who) ≤
      1 / gap :=
    one_div_le_one_div_of_le hgap (by linarith [hopponents who])
  have hclock : quittingOpponentLiveCesaro reward (quittingStationaryProfile reward root)
      who horizon ≤ 1 / (gap * (horizon : ℝ)) := by
    calc
      _ ≤ (1 / (1 - quittingStationaryFixedOpponentsContinueMass root who)) /
          (horizon : ℝ) := quittingOpponentLiveCesaro_stationary_le _ _ _ _ hcontracts
      _ ≤ (1 / gap) / (horizon : ℝ) :=
        div_le_div_of_nonneg_right hinverse (Nat.cast_nonneg horizon)
      _ = _ := div_div _ _ _
  have hscaled : bound * quittingOpponentLiveCesaro reward
      (quittingStationaryProfile reward root) who horizon ≤
      bound / (gap * (horizon : ℝ)) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hclock hbound
  have hdelivery := (abs_finiteAveragePayoff_sub_terminal_le_opponentLiveCesaro reward
    (quittingStationaryProfile reward root) who horizon hhorizon bound hbound
      (fun terminal => hreward terminal who)).trans hscaled
  have hdeviation := (finiteAveragePayoff_update_le_terminal_add_opponentLiveCesaro'
    reward (quittingStationaryProfile reward root) who deviation horizon hhorizon
      bound hbound (fun terminal => hreward terminal who)).trans
        (add_le_add le_rfl hscaled)
  have hterminal := hnash who deviation
  simp only [add_zero] at hterminal
  have hlower := (abs_le.mp hdelivery).1
  have hdouble : bound / (gap * (horizon : ℝ)) + bound / (gap * (horizon : ℝ)) =
      2 * bound / (gap * (horizon : ℝ)) := by ring
  linarith

end GameTheory
