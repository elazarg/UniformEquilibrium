import UniformEquilibrium.Quitting.Cycles.PairedCycleStoppingLaws
import UniformEquilibrium.Quitting.Cycles.PeriodicFiniteHorizonRate

/-! # Same-profile quantitative finite-horizon bounds for paired cycles -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

def opponentCycleSurvival (q : ι → ℝ) (player : ι) : ℝ :=
  ∏ other ∈ Finset.univ.erase player, (1 - q other)

theorem prod_cycle_opponentsContinue (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (player : ι) :
    (∏ phase, quittingStationaryFixedOpponentsContinueMass (cycle schedule q hq phase) player) =
      opponentCycleSurvival q player := by
  change (∏ phase, quittingStationaryContinueMass
    (Function.update (cycle schedule q hq phase) player (PMF.pure false))) = _
  simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [Finset.prod_comm]
  have hcoordinate (other : ι) :
      (∏ phase : Fin period,
        ((Function.update (cycle schedule q hq phase) player (PMF.pure false))
          other false).toReal) =
        if other = player then 1 else 1 - q other := by
    by_cases hother : other = player
    · subst other
      simp
    · simp only [Function.update_of_ne hother, if_neg hother]
      exact prod_cycle_ownContinue schedule q hq other
  simp_rw [hcoordinate]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ player)]
  simp only [ite_true, mul_one]
  apply Finset.prod_congr rfl
  intro other hother
  rw [if_neg (Finset.mem_erase.mp hother).1]

theorem opponentCycleSurvival_le_geometric (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (1 / 100 : ℝ) 1) (player : ι) :
    opponentCycleSurvival q player ≤ (99 / 100 : ℝ) ^ (Fintype.card ι - 1) := by
  calc
    _ ≤ ∏ _other ∈ Finset.univ.erase player, (99 / 100 : ℝ) := by
      apply Finset.prod_le_prod
      · intro other _
        exact sub_nonneg.mpr (hq other).2
      · intro other _
        linarith [(hq other).1]
    _ = _ := by simp [div_pow]

omit [DecidableEq ι] in
/-- Uniform opponent-cycle contraction gap, with the deleted-player exponent. -/
theorem opponent_geometric_lt_one (schedule : Schedule ι period) (player : ι) :
    (99 / 100 : ℝ) ^ (Fintype.card ι - 1) < 1 := by
  have hperiod := (schedule.phase player).pos
  have hcard := schedule.card_players
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

theorem opponentLiveCesaro_le_geometric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (initial : Fin period) (player : ι) (horizon : ℕ) :
    quittingOpponentLiveCesaro reward
        (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial) player horizon ≤
      ((period : ℝ) / (1 - (99 / 100 : ℝ) ^ (Fintype.card ι - 1))) / (horizon : ℝ) := by
  have hbound := quittingOpponentLiveCesaro_cyclicBehaviorProfile_le reward
    (cycle schedule q hq) initial player horizon
    (cycle_opponents_contract schedule q hq
      (fun player => by linarith [(hinterior player).1]) player)
  rw [prod_cycle_opponentsContinue] at hbound
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg horizon)
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg period)
    (sub_pos.mpr (opponent_geometric_lt_one schedule player))
  have h := opponentCycleSurvival_le_geometric q
    (fun player => ⟨(hinterior player).1.le, (hq player).2⟩) player
  linarith

/-- Prescribed finite-average delivery for the same infinite cyclic profile. -/
theorem finiteAverage_payoff_error_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (initial : Fin period) (player : ι) (horizon : ℕ) (hhorizon : 0 < horizon)
    (bound : ℝ) (hreward : ∀ terminal, |reward terminal player| ≤ bound) :
    |(quittingGame reward).finiteAveragePayoff none horizon
        (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial) player -
        value reward schedule q hq initial player| ≤
      bound * ((period : ℝ) / (1 - (99 / 100 : ℝ) ^ (Fintype.card ι - 1))) /
        (horizon : ℝ) := by
  have hbound : 0 ≤ bound := (abs_nonneg _).trans (hreward (quittingSingletonTerminal player))
  have herror := abs_finiteAveragePayoff_sub_terminal_le_opponentLiveCesaro reward
    (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
    player horizon hhorizon bound hbound hreward
  rw [quittingTerminalPayoff_cyclicBehaviorProfile] at herror
  have hclock := mul_le_mul_of_nonneg_left
    (opponentLiveCesaro_le_geometric reward schedule q hq hinterior initial player horizon) hbound
  exact herror.trans (by simpa only [mul_div_assoc] using hclock)

/-- Every unrestricted behavioral replacement has the same explicit one-sided
finite-average boundary error, without changing the prescribed profile. -/
theorem finiteAverage_deviation_le_terminal_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (initial : Fin period) (player : ι)
    (deviation : (quittingGame reward).BehaviorStrategy player)
    (horizon : ℕ) (hhorizon : 0 < horizon)
    (bound : ℝ) (hreward : ∀ terminal, |reward terminal player| ≤ bound) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
          player deviation) player ≤
      quittingTerminalPayoff reward
          (Function.update (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
            player deviation) player +
        bound * ((period : ℝ) / (1 - (99 / 100 : ℝ) ^ (Fintype.card ι - 1))) /
          (horizon : ℝ) := by
  have hbound : 0 ≤ bound := (abs_nonneg _).trans (hreward (quittingSingletonTerminal player))
  have herror := finiteAveragePayoff_update_le_terminal_add_opponentLiveCesaro' reward
    (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
    player deviation horizon hhorizon bound hbound hreward
  have hclock := mul_le_mul_of_nonneg_left
    (opponentLiveCesaro_le_geometric reward schedule q hq hinterior initial player horizon) hbound
  exact herror.trans (add_le_add le_rfl (by simpa only [mul_div_assoc] using hclock))

/-- Against the selected exact cycle, every deviation's finite average is
bounded by the fixed periodic target plus the explicit boundary error. -/
theorem finiteAverage_deviation_le_value_add_of_selected
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (initial : Fin period) (player : ι)
    (deviation : (quittingGame reward).BehaviorStrategy player)
    (horizon : ℕ) (hhorizon : 0 < horizon)
    (bound : ℝ) (hreward : ∀ terminal, |reward terminal player| ≤ bound) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
          player deviation) player ≤
      value reward schedule q hq initial player +
        bound * ((period : ℝ) / (1 - (99 / 100 : ℝ) ^ (Fintype.card ι - 1))) /
          (horizon : ℝ) := by
  have hnash := isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate reward
    (cycle schedule q hq) (value reward schedule q hq) initial
    (quittingCyclicTerminalValue_eq_rootSuccessorPayoff reward (cycle schedule q hq))
    (cycle_isZeroRootNash_of_selected reward schedule hregion q hq hinterior hzero)
    (cycle_opponents_contract schedule q hq
      (fun player => by linarith [(hinterior player).1]))
  have hterminal := hnash player deviation
  rw [quittingTerminalPayoff_cyclicBehaviorProfile] at hterminal
  change quittingTerminalPayoff reward _ player ≤
    value reward schedule q hq initial player + 0 at hterminal
  have hfinite := finiteAverage_deviation_le_terminal_add reward schedule q hq hinterior
    initial player deviation horizon hhorizon bound hreward
  linarith

/-- The same profile is horizon Nash at the explicit reciprocal-horizon rate. -/
theorem finiteHorizonNash_of_selected
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (initial : Fin period) (horizon : ℕ) (hhorizon : 0 < horizon)
    (bound : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    (quittingGame reward).IsεHorizonNash none horizon
      (2 * bound * ((period : ℝ) / (1 - (99 / 100 : ℝ) ^ (Fintype.card ι - 1))) /
        (horizon : ℝ)) (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial) := by
  intro player deviation
  have hdelivery := finiteAverage_payoff_error_le reward schedule q hq hinterior
    initial player horizon hhorizon bound (fun terminal => hreward terminal player)
  have hdeviation := finiteAverage_deviation_le_value_add_of_selected reward schedule hregion
    q hq hinterior hzero initial player deviation horizon hhorizon bound
    (fun terminal => hreward terminal player)
  have hlower := (abs_le.mp hdelivery).1
  have heq : 2 * bound * ((period : ℝ) /
      (1 - (99 / 100 : ℝ) ^ (Fintype.card ι - 1))) / (horizon : ℝ) =
      2 * (bound * ((period : ℝ) /
        (1 - (99 / 100 : ℝ) ^ (Fintype.card ι - 1))) / (horizon : ℝ)) := by ring
  rw [heq]
  linarith

/-- Every finite prefix of the live-time tail sum is uniformly bounded under
every unilateral behavioral replacement. -/
theorem sum_liveMass_update_le_geometric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (initial : Fin period) (player : ι)
    (deviation : (quittingGame reward).BehaviorStrategy player) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon, quittingLiveMass reward
      (Function.update (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
        player deviation) time) ≤
      (period : ℝ) / (1 - (99 / 100 : ℝ) ^ (Fintype.card ι - 1)) := by
  by_cases hzero : horizon = 0
  · subst horizon
    simp only [Finset.range_zero, Finset.sum_empty]
    exact div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr
      (opponent_geometric_lt_one schedule player)).le
  have hhorizon : (horizon : ℝ) ≠ 0 := by exact_mod_cast hzero
  have hclock := opponentLiveCesaro_le_geometric reward schedule q hq hinterior
    initial player horizon
  unfold quittingOpponentLiveCesaro at hclock
  have hsum := mul_le_mul_of_nonneg_left hclock (Nat.cast_nonneg horizon)
  have hleft (sum : ℝ) : (horizon : ℝ) * ((horizon : ℝ)⁻¹ * sum) = sum := by
    field_simp
  have hright (bound : ℝ) : (horizon : ℝ) * (bound / (horizon : ℝ)) = bound := by
    field_simp
  rw [hleft, hright] at hsum
  apply le_trans _ hsum
  apply Finset.sum_le_sum
  intro time _
  exact quittingLiveMass_update_le_opponentOnly reward _ player deviation time

/-- The live-time tail series is summable and satisfies a uniform
absorption-clock bound, simultaneously for all behavioral deviations. -/
theorem summable_liveMass_update_and_tsum_le_geometric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (initial : Fin period) (player : ι)
    (deviation : (quittingGame reward).BehaviorStrategy player) :
    Summable (fun time => quittingLiveMass reward
      (Function.update (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
        player deviation) time) ∧
    (∑' time, quittingLiveMass reward
      (Function.update (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
        player deviation) time) ≤
      (period : ℝ) / (1 - (99 / 100 : ℝ) ^ (Fintype.card ι - 1)) := by
  have hnonneg : ∀ time, 0 ≤ quittingLiveMass reward
      (Function.update (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
        player deviation) time := fun _ => ENNReal.toReal_nonneg
  have hbound := sum_liveMass_update_le_geometric reward schedule q hq hinterior
    initial player deviation
  exact ⟨summable_of_sum_range_le hnonneg hbound,
    Real.tsum_le_of_sum_range_le hnonneg hbound⟩

/-- Raw-table producer of one fixed profile per initial phase, with the same
explicit finite-average delivery and deviation bounds at every positive horizon.
The canonical finite reward bound includes all otherwise unrestricted coordinates. -/
theorem exists_one_hazards_all_finiteHorizon_bounds_of_rawRegion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hperiod : 2 ≤ period) (hregion : RawRegion reward schedule) :
    ∃ q : ι → ℝ, ∃ hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2),
      let hq := unitBoundsOfInterior q hinterior
      (∀ player, playerGap schedule.partner (singleton reward)
        (partnerReward reward schedule) (jointReward reward schedule)
        (quietRows reward schedule) q player = 0) ∧
      ∀ initial horizon, 0 < horizon →
        (∀ player, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial) player -
            value reward schedule q hq initial player| ≤
          quittingRewardBound reward * ((period : ℝ) /
            (1 - (99 / 100 : ℝ) ^ (Fintype.card ι - 1))) / (horizon : ℝ)) ∧
        (∀ player (deviation : (quittingGame reward).BehaviorStrategy player),
          (quittingGame reward).finiteAveragePayoff none horizon
              (Function.update (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
                player deviation) player ≤
            value reward schedule q hq initial player +
              quittingRewardBound reward * ((period : ℝ) /
                (1 - (99 / 100 : ℝ) ^ (Fintype.card ι - 1))) / (horizon : ℝ)) ∧
        (quittingGame reward).IsεHorizonNash none horizon
          (2 * quittingRewardBound reward * ((period : ℝ) /
            (1 - (99 / 100 : ℝ) ^ (Fintype.card ι - 1))) / (horizon : ℝ))
          (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial) := by
  obtain ⟨q, hinterior, hzero⟩ := exists_hazards_of_rawRegion reward schedule hperiod hregion
  let hq := unitBoundsOfInterior q hinterior
  refine ⟨q, hinterior, hzero, fun initial horizon hhorizon => ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro player
    exact finiteAverage_payoff_error_le reward schedule q hq hinterior initial player
      horizon hhorizon (quittingRewardBound reward)
      (fun terminal => abs_reward_le_quittingRewardBound reward terminal player)
  · intro player deviation
    exact finiteAverage_deviation_le_value_add_of_selected reward schedule hregion q hq
      hinterior hzero initial player deviation horizon hhorizon (quittingRewardBound reward)
      (fun terminal => abs_reward_le_quittingRewardBound reward terminal player)
  · exact finiteHorizonNash_of_selected reward schedule hregion q hq hinterior hzero
      initial horizon hhorizon (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward)

/-- Both signs of the terminal/finite-average boundary error are uniformly
controlled for every behavioral deviation against the same cyclic profile. -/
theorem finiteAverage_deviation_error_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (initial : Fin period) (player : ι)
    (deviation : (quittingGame reward).BehaviorStrategy player)
    (horizon : ℕ) (hhorizon : 0 < horizon)
    (bound : ℝ) (hreward : ∀ terminal, |reward terminal player| ≤ bound) :
    |(quittingGame reward).finiteAveragePayoff none horizon
        (Function.update (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
          player deviation) player -
      quittingTerminalPayoff reward
        (Function.update (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
          player deviation) player| ≤
      bound * ((period : ℝ) / (1 - (99 / 100 : ℝ) ^ (Fintype.card ι - 1))) /
        (horizon : ℝ) := by
  have hbound : 0 ≤ bound := (abs_nonneg _).trans (hreward (quittingSingletonTerminal player))
  have herror := abs_finiteAveragePayoff_sub_terminal_le_opponentLiveCesaro reward
    (Function.update (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
      player deviation) player horizon hhorizon bound hbound hreward
  have hsame : quittingOpponentOnlyProfile reward
      (Function.update (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial)
        player deviation) player =
      quittingOpponentOnlyProfile reward
        (quittingCyclicBehaviorProfile reward (cycle schedule q hq) initial) player := by
    unfold quittingOpponentOnlyProfile
    exact Function.update_idem _ _ _
  unfold quittingOpponentLiveCesaro at herror
  rw [hsame] at herror
  have hclock := mul_le_mul_of_nonneg_left
    (opponentLiveCesaro_le_geometric reward schedule q hq hinterior initial player horizon) hbound
  exact herror.trans (by simpa only [mul_div_assoc, quittingOpponentLiveCesaro] using hclock)

end GameTheory.PairedCycle
