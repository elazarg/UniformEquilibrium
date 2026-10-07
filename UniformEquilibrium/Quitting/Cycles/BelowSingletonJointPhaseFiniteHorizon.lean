import UniformEquilibrium.Quitting.Cycles.BelowSingletonJointPhaseSource
import UniformEquilibrium.Quitting.Cycles.PairedCycleFiniteHorizon

/-! # Quantitative horizons for the selected below-singleton cycles

The actual same profile is retained at every initial phase and every positive
horizon. The printed time constant includes the extra initial live-state date.
Signed rewards and unrestricted behavioral replacements are allowed.
-/

noncomputable section

namespace GameTheory.PairedCycle.BelowSingleton

def profileAt (reward : Reward) (t : ℝ) (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (initial : Fin 2) : (quittingGame reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward
    (cycle fin4Schedule (fun _ => 1 - t)
      (properUnitBounds _ (fun _ => ⟨by linarith [ht.2], by linarith [ht.1]⟩))) initial

def timeConstant (t : ℝ) : ℝ := 1 + 2 / (1 - t ^ 3)

private theorem survival_lt_one {t : ℝ} (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    t ^ 3 < 1 :=
  pow_lt_one₀ (by linarith [ht.1]) ht.2 (by decide)

theorem timeConstant_pos {t : ℝ} (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    0 < timeConstant t := by
  unfold timeConstant
  have hgap : 0 < 1 - t ^ 3 := sub_pos.mpr (survival_lt_one ht)
  positivity

theorem opponentCycleSurvival_eq {t : ℝ} (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (player : Fin 4) :
    (∏ phase, quittingStationaryFixedOpponentsContinueMass
      (cycle fin4Schedule (fun _ => 1 - t)
        (properUnitBounds _ (fun _ => ⟨by linarith [ht.2], by linarith [ht.1]⟩)) phase)
      player) = t ^ 3 := by
  rw [prod_cycle_opponentsContinue]
  simp [opponentCycleSurvival]

theorem opponentLiveCesaro_le_timeConstant
    (reward : Reward) {t : ℝ} (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (initial : Fin 2) (player : Fin 4) (horizon : ℕ) :
    quittingOpponentLiveCesaro reward (profileAt reward t ht initial) player horizon ≤
      timeConstant t / (horizon : ℝ) := by
  have hsurvival := opponentCycleSurvival_eq ht player
  have hclock := quittingOpponentLiveCesaro_cyclicBehaviorProfile_le reward
    (cycle fin4Schedule (fun _ => 1 - t)
      (properUnitBounds _ (fun _ => ⟨by linarith [ht.2], by linarith [ht.1]⟩)))
    initial player horizon (by rw [hsurvival]; exact survival_lt_one ht)
  rw [hsurvival] at hclock
  change quittingOpponentLiveCesaro reward (profileAt reward t ht initial) player horizon ≤ _
    at hclock
  apply hclock.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg horizon)
  unfold timeConstant
  norm_num

private theorem exact_terminal_and_nash
    {reward : Reward} {scale : Fin 4 → ℝ} {favorable premium passive t : ℝ}
    (hraw : RawFamily reward scale favorable premium passive)
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hroot : Math.PairedBelowSingleton.polynomial favorable premium passive t = 0)
    (initial : Fin 2) :
    quittingTerminalPayoff reward (profileAt reward t ht initial) =
        twoPairPhaseValue reward fin4Schedule (fun _ => 1 - t) initial ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (profileAt reward t ht initial) := by
  have hresult := twoPair_exact_terminal_and_fixedProfile reward fin4Schedule
    (fun _ => 1 - t) (fun _ => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    (passive_continue hraw ht hroot) (fun player => (passive_quit_lt hraw ht player).le) initial
  exact ⟨hresult.1, hresult.2.1⟩

/-- The stronger delivery bound for the actual profile at every initial phase. -/
theorem finiteAverage_delivery_le_timeConstant
    {reward : Reward} {scale : Fin 4 → ℝ} {favorable premium passive t bound : ℝ}
    (hraw : RawFamily reward scale favorable premium passive)
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hroot : Math.PairedBelowSingleton.polynomial favorable premium passive t = 0)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (initial : Fin 2) (player : Fin 4) (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame reward).finiteAveragePayoff none horizon
        (profileAt reward t ht initial) player -
      twoPairPhaseValue reward fin4Schedule (fun _ => 1 - t) initial player| ≤
        bound * timeConstant t / (horizon : ℝ) := by
  have hterminal := (exact_terminal_and_nash hraw ht hroot initial).1
  have herror := finiteAverage_delivery_le_of_opponentLiveCesaro_bound reward
    (profileAt reward t ht initial) player horizon hhorizon bound (timeConstant t)
    (fun terminal => hreward terminal player)
    (opponentLiveCesaro_le_timeConstant reward ht initial player horizon)
  rw [hterminal] at herror
  exact herror

/-- The stronger regret bound for every history-dependent behavioral replacement. -/
theorem finiteAverage_deviation_gain_le_timeConstant
    {reward : Reward} {scale : Fin 4 → ℝ} {favorable premium passive t bound : ℝ}
    (hraw : RawFamily reward scale favorable premium passive)
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hroot : Math.PairedBelowSingleton.polynomial favorable premium passive t = 0)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (initial : Fin 2) (player : Fin 4)
    (deviation : (quittingGame reward).BehaviorStrategy player)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (profileAt reward t ht initial) player deviation) player -
      (quittingGame reward).finiteAveragePayoff none horizon
        (profileAt reward t ht initial) player ≤
      2 * bound * timeConstant t / (horizon : ℝ) := by
  exact finiteAverage_deviation_gain_le_of_exact_terminalNash_and_opponentLiveCesaro_bound
    reward (profileAt reward t ht initial)
    (exact_terminal_and_nash hraw ht hroot initial).2
    player deviation horizon hhorizon bound (timeConstant t)
    (fun terminal => hreward terminal player)
    (opponentLiveCesaro_le_timeConstant reward ht initial player horizon)

/-- The packet's conservative delivery constant, obtained by weakening the stronger bound. -/
theorem finiteAverage_delivery_le
    {reward : Reward} {scale : Fin 4 → ℝ} {favorable premium passive t bound : ℝ}
    (hraw : RawFamily reward scale favorable premium passive)
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hroot : Math.PairedBelowSingleton.polynomial favorable premium passive t = 0)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (initial : Fin 2) (player : Fin 4) (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame reward).finiteAveragePayoff none horizon
        (profileAt reward t ht initial) player -
      twoPairPhaseValue reward fin4Schedule (fun _ => 1 - t) initial player| ≤
        2 * bound * timeConstant t / (horizon : ℝ) := by
  have hsharp := finiteAverage_delivery_le_timeConstant hraw ht hroot hreward
    initial player horizon hhorizon
  have hbound : 0 ≤ bound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal player) player)
  have htime := (timeConstant_pos ht).le
  have hnonnegative : 0 ≤ bound * timeConstant t / (horizon : ℝ) := by positivity
  have htwice : 2 * bound * timeConstant t / (horizon : ℝ) =
      2 * (bound * timeConstant t / (horizon : ℝ)) := by ring
  rw [htwice]
  linarith

/-- The packet's conservative regret constant for every complete behavioral replacement. -/
theorem finiteAverage_deviation_gain_le
    {reward : Reward} {scale : Fin 4 → ℝ} {favorable premium passive t bound : ℝ}
    (hraw : RawFamily reward scale favorable premium passive)
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hroot : Math.PairedBelowSingleton.polynomial favorable premium passive t = 0)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (initial : Fin 2) (player : Fin 4)
    (deviation : (quittingGame reward).BehaviorStrategy player)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (profileAt reward t ht initial) player deviation) player -
      (quittingGame reward).finiteAveragePayoff none horizon
        (profileAt reward t ht initial) player ≤
      4 * bound * timeConstant t / (horizon : ℝ) := by
  have hsharp := finiteAverage_deviation_gain_le_timeConstant hraw ht hroot hreward
    initial player deviation horizon hhorizon
  have hbound : 0 ≤ bound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal player) player)
  have htime := (timeConstant_pos ht).le
  have hnonnegative : 0 ≤ bound * timeConstant t / (horizon : ℝ) := by positivity
  have htwo : 2 * bound * timeConstant t / (horizon : ℝ) =
      2 * (bound * timeConstant t / (horizon : ℝ)) := by ring
  have hfour : 4 * bound * timeConstant t / (horizon : ℝ) =
      4 * (bound * timeConstant t / (horizon : ℝ)) := by ring
  rw [htwo] at hsharp
  rw [hfour]
  linarith

theorem finiteHorizonNash_at_printed_rate
    {reward : Reward} {scale : Fin 4 → ℝ} {favorable premium passive t bound : ℝ}
    (hraw : RawFamily reward scale favorable premium passive)
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hroot : Math.PairedBelowSingleton.polynomial favorable premium passive t = 0)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (initial : Fin 2) (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame reward).IsεHorizonNash none horizon
      (4 * bound * timeConstant t / (horizon : ℝ)) (profileAt reward t ht initial) := by
  intro player deviation
  have hgain := finiteAverage_deviation_gain_le hraw ht hroot hreward
    initial player deviation horizon hhorizon
  linarith

/-- The scalar rate is produced from raw reward data, before all horizon tests. -/
theorem exists_selected_rate_all_horizon_bounds
    {reward : Reward} {scale : Fin 4 → ℝ} {favorable premium passive : ℝ}
    (hraw : RawFamily reward scale favorable premium passive) :
    ∃ t : ℝ, ∃ ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1,
      Math.PairedBelowSingleton.polynomial favorable premium passive t = 0 ∧
      ∀ bound : ℝ, (∀ terminal player, |reward terminal player| ≤ bound) →
        ∀ initial : Fin 2, ∀ horizon : ℕ, 0 < horizon →
          (∀ player, |(quittingGame reward).finiteAveragePayoff none horizon
              (profileAt reward t ht initial) player -
            twoPairPhaseValue reward fin4Schedule (fun _ => 1 - t) initial player| ≤
              2 * bound * timeConstant t / (horizon : ℝ)) ∧
          (quittingGame reward).IsεHorizonNash none horizon
            (4 * bound * timeConstant t / (horizon : ℝ)) (profileAt reward t ht initial) := by
  obtain ⟨t, ht, hroot⟩ := Math.PairedBelowSingleton.exists_selected_root
    hraw.favorable_gt hraw.passive_lt
  refine ⟨t, ht, hroot, ?_⟩
  intro bound hreward initial horizon hhorizon
  exact ⟨fun player => finiteAverage_delivery_le hraw ht hroot hreward
      initial player horizon hhorizon,
    finiteHorizonNash_at_printed_rate hraw ht hroot hreward initial horizon hhorizon⟩

end GameTheory.PairedCycle.BelowSingleton
