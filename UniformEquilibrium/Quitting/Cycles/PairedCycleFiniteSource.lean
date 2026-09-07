import UniformEquilibrium.Quitting.Cycles.PairedCycleFiniteTruncation

/-! # One raw-region hazard selection for every finite accuracy -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem eventually_geometric_error_le (count : ℕ) (hcount : 0 < count)
    (error : ℝ) (herror : 0 < error) :
    ∃ cutoff : ℕ, 1 ≤ cutoff ∧ ∀ turns ≥ cutoff,
      21 / 10 * (99 / 100 : ℝ) ^ (count * turns) ≤ error := by
  have hbase : (99 / 100 : ℝ) ^ count < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have htendsto : Tendsto
      (fun turns : ℕ => 21 / 10 * (99 / 100 : ℝ) ^ (count * turns)) atTop (nhds 0) := by
    simpa only [pow_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (show 0 ≤ (99 / 100 : ℝ) ^ count by positivity) hbase).const_mul (21 / 10 : ℝ)
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.mp (htendsto.eventually (gt_mem_nhds herror))
  exact ⟨max 1 cutoff, le_max_left _ _, fun turns hturns =>
    (hcutoff turns ((le_max_right _ _).trans hturns)).le⟩

/-- The same finite truncation is close to the fixed periodic payoff target. -/
theorem finiteProfile_payoff_error_le_geometric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (initial : Fin period) (turns : ℕ) (hturns : 1 ≤ turns) (player : ι) :
    |quittingTerminalPayoff reward
        (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period))
        player - value reward schedule q hq initial player| ≤
      21 / 10 * (99 / 100 : ℝ) ^ (Fintype.card ι * turns) := by
  have hdebt := finiteProfile_debt_le_geometric reward schedule hregion q hq
    hinterior hzero initial turns hturns player
  have hnonneg := quittingTerminalDeviationDebt_nonneg reward
    (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period)) player
  rw [quittingTerminalDeviationDebt,
    finiteProfile_cap_eq_value reward schedule hregion q hq hinterior hzero
      initial turns hturns player] at hdebt hnonneg
  rw [abs_sub_comm, abs_of_nonneg hnonneg]
  exact hdebt

/-- The raw table chooses one hazard vector. Every initial phase and every finite
cycle count use that vector, with exact caps and debts; increasing the count provides
all positive accuracies without changing the target payoff or selecting new hazards. -/
theorem exists_one_hazards_all_finiteTruncations_of_rawRegion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hperiod : 2 ≤ period) (hregion : RawRegion reward schedule) :
    ∃ q : ι → ℝ, ∃ hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2),
      let hq := unitBoundsOfInterior q hinterior
      (∀ player, playerGap schedule.partner (singleton reward)
        (partnerReward reward schedule) (jointReward reward schedule)
        (quietRows reward schedule) q player = 0) ∧
      (∀ initial start, (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingRootSequenceProfile reward
          (quittingCyclicRootSequence (cycle schedule q hq) initial) start)) ∧
      (∀ initial, (quittingGame reward).IsUniformEquilibriumPayoff none
        (value reward schedule q hq initial)) ∧
      (∀ initial turns, 1 ≤ turns → ∀ player,
        quittingTerminalPayoff reward
            (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period))
            player = (1 - jointCycleSurvival q ^ turns) *
              value reward schedule q hq initial player ∧
        quittingContinuationBestResponseValue reward
            (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period))
            player = value reward schedule q hq initial player ∧
        quittingTerminalDeviationDebt reward
            (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period))
            player = jointCycleSurvival q ^ turns * value reward schedule q hq initial player) ∧
      (∀ error : ℝ, 0 < error → ∃ cutoff : ℕ, 1 ≤ cutoff ∧
        ∀ turns ≥ cutoff, ∀ initial,
          (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) error
            (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period)) ∧
          ∀ player, |quittingTerminalPayoff reward
              (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period))
              player - value reward schedule q hq initial player| ≤ error) := by
  obtain ⟨q, hinterior, hzero, _, _, _, hallSuffix, huniform⟩ :=
    exists_exact_allSuffix_uniformPayoff_of_rawRegion reward schedule hperiod hregion
  let hq := unitBoundsOfInterior q hinterior
  refine ⟨q, hinterior, hzero, hallSuffix, huniform, ?_, ?_⟩
  · intro initial turns hturns player
    exact ⟨finiteProfile_payoff_eq reward schedule q hq initial turns player,
      finiteProfile_cap_eq_value reward schedule hregion q hq hinterior hzero
        initial turns hturns player,
      finiteProfile_debt_eq reward schedule hregion q hq hinterior hzero
        initial turns hturns player⟩
  · intro error herror
    have hcard : 0 < Fintype.card ι := by
      rw [schedule.card_players]
      omega
    obtain ⟨cutoff, hone, hcutoff⟩ := eventually_geometric_error_le
      (Fintype.card ι) hcard error herror
    refine ⟨cutoff, hone, fun turns hturns initial => ?_⟩
    constructor
    · intro player deviation
      have hnash := finiteProfile_isGeometricNash reward schedule hregion q hq
        hinterior hzero initial turns (hone.trans hturns) player deviation
      have hbound := hcutoff turns hturns
      linarith
    · intro player
      exact (finiteProfile_payoff_error_le_geometric reward schedule hregion q hq
        hinterior hzero initial turns (hone.trans hturns) player).trans (hcutoff turns hturns)

end GameTheory.PairedCycle
