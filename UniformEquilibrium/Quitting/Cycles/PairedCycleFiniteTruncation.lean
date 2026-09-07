import UniformEquilibrium.Quitting.Cycles.PairedCycleEquilibrium
import UniformEquilibrium.Quitting.Cycles.CyclicFiniteWord

/-! # Exact finite truncations of one simultaneously selected paired cycle -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

/-- Joint survival through one complete cycle, indexed by the actual player labels. -/
def jointCycleSurvival (q : ι → ℝ) : ℝ := ∏ player, (1 - q player)

theorem prod_cycle_continueMass (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) :
    (∏ phase, quittingStationaryContinueMass (cycle schedule q hq phase)) =
      jointCycleSurvival q := by
  have hphase (phase : Fin period) :
      quittingStationaryContinueMass (cycle schedule q hq phase) =
        (1 - q (schedule.first phase)) * (1 - q (schedule.second phase)) := by
    unfold cycle
    rw [continueMass_root (schedule.first_ne_second phase)]
    simp
  simp_rw [hphase]
  unfold jointCycleSurvival
  rw [← Equiv.prod_comp schedule.label (fun player => 1 - q player)]
  simp [Fintype.prod_prod_type, Schedule.first, Schedule.second, mul_comm]

/-- First visit to the player's own pair, from any specified initial phase. -/
def firstActiveTime (schedule : Schedule ι period) (initial : Fin period) (player : ι) : ℕ :=
  ((finCycle initial).symm (schedule.phase player)).val

omit [Fintype ι] [DecidableEq ι] in
theorem firstActiveTime_lt_period (schedule : Schedule ι period)
    (initial : Fin period) (player : ι) : firstActiveTime schedule initial player < period :=
  ((finCycle initial).symm (schedule.phase player)).isLt

omit [Fintype ι] [DecidableEq ι] in
theorem orbit_firstActiveTime (schedule : Schedule ι period)
    (initial : Fin period) (player : ι) :
    quittingCyclicOrbit initial (firstActiveTime schedule initial player) =
      schedule.phase player := by
  unfold firstActiveTime
  rw [orbit_eq_finCycle, Equiv.apply_symm_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem orbit_ne_owner_before_firstActiveTime (schedule : Schedule ι period)
    (initial : Fin period) (player : ι) (time : ℕ)
    (htime : time < firstActiveTime schedule initial player) :
    quittingCyclicOrbit initial time ≠ schedule.phase player := by
  intro heq
  have hlt := firstActiveTime_lt_period schedule initial player
  have hinj := orbit_injective_below_period initial (lt_trans htime hlt) hlt
    (heq.trans (orbit_firstActiveTime schedule initial player).symm)
  omega

theorem cycle_quiet_continue_eq_value
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (phase : Fin period) (player : ι)
    (hquiet : phase ≠ schedule.phase player) :
    quittingRootContinuePayoff reward (value reward schedule q hq (finRotate period phase))
        (cycle schedule q hq phase) player = value reward schedule q hq phase player := by
  have hvalue := congrFun (quittingCyclicTerminalValue_eq_rootSuccessorPayoff reward
    (cycle schedule q hq) phase) player
  rw [quittingRootSuccessorPayoff_eq_endpointMix, cycle_outside schedule q hq hquiet] at hvalue
  simpa [value] using hvalue.symm

/-- One early finite pure response attains the original periodic value exactly. -/
theorem finiteProfile_firstActiveTime_attains_value
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (initial : Fin period) (turns : ℕ) (hturns : 1 ≤ turns) (player : ι) :
    quittingTerminalPayoff reward
        (Function.update (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial
          (turns * period)) player
          (quittingPureTimeBehaviorStrategy reward player
            (some (firstActiveTime schedule initial player)))) player =
      value reward schedule q hq initial player := by
  refine quittingTerminalPayoff_cyclicWord_pureTime_eq reward (cycle schedule q hq)
    (value reward schedule q hq) (quittingAlwaysContinueProfile reward) initial
    (turns * period) (firstActiveTime schedule initial player) player ?_ ?_ ?_
  · exact lt_of_lt_of_le (firstActiveTime_lt_period schedule initial player)
      (by simpa using Nat.mul_le_mul_right period hturns)
  · intro offset hoff
    exact cycle_quiet_continue_eq_value reward schedule q hq _ player
      (orbit_ne_owner_before_firstActiveTime schedule initial player offset hoff)
  · rw [orbit_firstActiveTime, cycle_quit_active,
      value_active_eq_selected reward schedule hregion q hq hinterior hzero]

/-- Cutting after complete turns preserves every player's full replacement cap. -/
theorem finiteProfile_cap_eq_value
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (initial : Fin period) (turns : ℕ) (hturns : 1 ≤ turns) (player : ι) :
    quittingContinuationBestResponseValue reward
        (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period))
        player = value reward schedule q hq initial player := by
  apply le_antisymm
  · apply quittingContinuationBestResponseValue_cyclicFiniteProfile_le reward _
      (cycle_isZeroRootNash_of_selected reward schedule hregion q hq hinterior hzero)
    have hv := (value_bounds_of_selected reward schedule hregion q hq hinterior hzero
      (quittingCyclicOrbit initial (turns * period)) player).1
    have hs := (hregion.own player).singleton_lower
    exact max_le (by change 0 ≤ value reward schedule q hq _ player; linarith)
      (by exact hv.le)
  · rw [← finiteProfile_firstActiveTime_attains_value reward schedule hregion q hq
      hinterior hzero initial turns hturns player]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue reward _ player _

theorem finiteProfile_payoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (initial : Fin period) (turns : ℕ) (player : ι) :
    quittingTerminalPayoff reward
        (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period))
        player =
      (1 - jointCycleSurvival q ^ turns) * value reward schedule q hq initial player := by
  rw [quittingTerminalPayoff_cyclicFiniteProfile_mul_card, prod_cycle_continueMass]
  rfl

theorem finiteProfile_debt_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (initial : Fin period) (turns : ℕ) (hturns : 1 ≤ turns) (player : ι) :
    quittingTerminalDeviationDebt reward
        (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period))
        player = jointCycleSurvival q ^ turns * value reward schedule q hq initial player := by
  rw [quittingTerminalDeviationDebt, finiteProfile_cap_eq_value reward schedule hregion q hq
    hinterior hzero initial turns hturns player, finiteProfile_payoff_eq]
  ring

omit [DecidableEq ι] in
theorem jointCycleSurvival_nonneg (q : ι → ℝ) (hq : ∀ player, q player ≤ 1) :
    0 ≤ jointCycleSurvival q := by
  exact Finset.prod_nonneg fun player _ => sub_nonneg.mpr (hq player)

omit [DecidableEq ι] in
theorem jointCycleSurvival_le_geometric (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (1 / 100 : ℝ) 1) :
    jointCycleSurvival q ≤ (99 / 100 : ℝ) ^ Fintype.card ι := by
  calc
    _ ≤ ∏ _player : ι, (99 / 100 : ℝ) := by
      apply Finset.prod_le_prod
      · intro player _
        exact sub_nonneg.mpr (hq player).2
      · intro player _
        linarith [(hq player).1]
    _ = _ := by simp [div_pow]

omit [DecidableEq ι] in
theorem jointCycleSurvival_pow_le_geometric (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (1 / 100 : ℝ) 1) (turns : ℕ) :
    jointCycleSurvival q ^ turns ≤ (99 / 100 : ℝ) ^ (Fintype.card ι * turns) := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (jointCycleSurvival_nonneg q (fun player => (hq player).2))
    (jointCycleSurvival_le_geometric q hq) turns

/-- The exact debt has the stated uniform geometric bound, for every player. -/
theorem finiteProfile_debt_le_geometric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (initial : Fin period) (turns : ℕ) (hturns : 1 ≤ turns) (player : ι) :
    quittingTerminalDeviationDebt reward
        (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period))
        player ≤ 21 / 10 * (99 / 100 : ℝ) ^ (Fintype.card ι * turns) := by
  rw [finiteProfile_debt_eq reward schedule hregion q hq hinterior hzero initial turns hturns]
  have hpow := jointCycleSurvival_pow_le_geometric q
    (fun player => ⟨(hinterior player).1.le, (hq player).2⟩) turns
  have hnonneg := pow_nonneg (jointCycleSurvival_nonneg q (fun player => (hq player).2)) turns
  have hv := (value_bounds_of_selected reward schedule hregion q hq hinterior hzero
    initial player).2
  calc
    _ ≤ jointCycleSurvival q ^ turns * (21 / 10) := mul_le_mul_of_nonneg_left hv hnonneg
    _ ≤ _ := by nlinarith

/-- Every complete behavioral replacement obeys the geometric terminal Nash bound. -/
theorem finiteProfile_isGeometricNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (initial : Fin period) (turns : ℕ) (hturns : 1 ≤ turns) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      (21 / 10 * (99 / 100 : ℝ) ^ (Fintype.card ι * turns))
      (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period)) := by
  intro player deviation
  have hcap := quittingTerminalPayoff_update_le_continuationBestResponseValue reward
    (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period))
    player deviation
  have hdebt := finiteProfile_debt_le_geometric reward schedule hregion q hq
    hinterior hzero initial turns hturns player
  unfold quittingTerminalDeviationDebt at hdebt
  linarith

end GameTheory.PairedCycle
