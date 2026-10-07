import MathUE.CyclicChildNegativePremiumRates
import UniformEquilibrium.Quitting.Cycles.PeriodicCompiler
import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile
import UniformEquilibrium.Quitting.Root.PairedProductRoot
import UniformEquilibrium.Quitting.Root.SingletonRootEndpoints
import UniformEquilibrium.Quitting.Stationary.MinMax
import Mathlib.Tactic.FinCases

/-! # Endpoints for the negative-premium cyclic-child construction

Only the five literal rows and twelve joining caps are table hypotheses.
The remaining coalition coordinates are not restricted.
-/

noncomputable section

namespace GameTheory.NegativePremiumCyclicChild

open _root_.Math.Probability _root_.Math.CyclicChildNegativePremium

abbrev Player := Fin 4
abbrev Reward := {S : Finset Player // S.Nonempty} → Payoff Player

structure RawTable (loss : ℝ) (reward : Reward) : Prop where
  loss_mem : loss ∈ Set.Ioc (0 : ℝ) 1
  singleton_zero : reward (quittingSingletonTerminal 0) = ![1, 0, 0, 0]
  singleton_one : reward (quittingSingletonTerminal 1) = ![2, 1, 4, 0]
  singleton_two : reward (quittingSingletonTerminal 2) = ![2, 0, 1, 4]
  singleton_three : reward (quittingSingletonTerminal 3) = ![0, 4, 0, 1]
  joint : reward ⟨{0, 3}, by simp⟩ = ![1 - loss, 3, -1, 1 - loss]
  one_zero : reward ⟨{1, 0}, by simp⟩ 1 ≤ 1 - loss
  one_three : reward ⟨{1, 3}, by simp⟩ 1 ≤ 1 + loss
  one_both : reward ⟨{1, 0, 3}, by simp⟩ 1 ≤ 1
  two_zero : reward ⟨{2, 0}, by simp⟩ 2 ≤ 1 - loss
  two_three : reward ⟨{2, 3}, by simp⟩ 2 ≤ 1
  two_both : reward ⟨{2, 0, 3}, by simp⟩ 2 ≤ 1 - loss
  zero_one : reward ⟨{0, 1}, by simp⟩ 0 ≤ 1 + loss
  three_one : reward ⟨{3, 1}, by simp⟩ 3 ≤ 1
  two_one : reward ⟨{2, 1}, by simp⟩ 2 ≤ 1 + loss
  zero_two : reward ⟨{0, 2}, by simp⟩ 0 ≤ 1
  three_two : reward ⟨{3, 2}, by simp⟩ 3 ≤ 1 + loss
  one_two : reward ⟨{1, 2}, by simp⟩ 1 ≤ 1

structure Rates where
  p : ℝ
  y : ℝ
  z : ℝ
  w : ℝ
  p_mem : p ∈ Set.Icc (0 : ℝ) 1
  y_mem : y ∈ Set.Ioo (0 : ℝ) 1
  z_mem : z ∈ Set.Ioo (0 : ℝ) 1
  w_mem : w ∈ Set.Ioo (0 : ℝ) 1

def jointRoot (rates : Rates) : Player → PMF Bool :=
  PairedCycle.root 0 3 (quittingHazardCoin rates.p rates.p_mem.1 rates.p_mem.2)
    (quittingHazardCoin rates.y rates.y_mem.1.le rates.y_mem.2.le)

def soloOne (rates : Rates) : Player → PMF Bool :=
  quittingSoloStationaryRoot 1
    (quittingHazardCoin rates.z rates.z_mem.1.le rates.z_mem.2.le)

def soloTwo (rates : Rates) : Player → PMF Bool :=
  quittingSoloStationaryRoot 2
    (quittingHazardCoin rates.w rates.w_mem.1.le rates.w_mem.2.le)

def cycle (rates : Rates) : Fin 3 → Player → PMF Bool :=
  ![jointRoot rates, soloOne rates, soloTwo rates]

def lowA (loss : ℝ) (rates : Rates) : Payoff Player :=
  ![1 - loss * rates.y, 1 + 3 * rates.y - rates.p, 1, 1 - loss * rates.p]

def lowB (loss : ℝ) (rates : Rates) : Payoff Player :=
  ![(1 - loss * rates.y) / (1 - rates.y), 1, 1 + 3 * rates.z,
    1 + rates.p * (1 - loss) / (1 - rates.p)]

def lowC (loss : ℝ) (rates : Rates) : Payoff Player :=
  ![2 * rates.w + (1 - rates.w) * (1 - loss * rates.y), 1, 1,
    1 + 3 * rates.w - loss * rates.p * (1 - rates.w)]

def lowValue (loss : ℝ) (rates : Rates) : Fin 3 → Payoff Player :=
  ![lowA loss rates, lowB loss rates, lowC loss rates]

def highRates : Rates where
  p := 0
  y := 2 / 3
  z := 2 / 3
  w := 2 / 3
  p_mem := by constructor <;> norm_num
  y_mem := by constructor <;> norm_num
  z_mem := by constructor <;> norm_num
  w_mem := by constructor <;> norm_num

def highValue : Fin 3 → Payoff Player :=
  ![![8 / 13, 3, 1, 1], ![24 / 13, 1, 3, 1], ![20 / 13, 1, 1, 3]]

theorem joint_quit_zero (loss : ℝ) (reward : Reward) (table : RawTable loss reward)
    (rates : Rates) (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail (jointRoot rates) 0 = 1 - loss * rates.y := by
  rw [jointRoot, PairedCycle.rootQuit_first reward tail (by decide),
    quittingHazardCoin_true_toReal, table.singleton_zero, table.joint]
  simp [Math.PairedAffine.activeValue]
  ring

theorem joint_quit_three (loss : ℝ) (reward : Reward) (table : RawTable loss reward)
    (rates : Rates) (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail (jointRoot rates) 3 = 1 - loss * rates.p := by
  rw [jointRoot, PairedCycle.rootQuit_second reward tail (by decide),
    quittingHazardCoin_true_toReal, table.singleton_three, table.joint]
  simp [Math.PairedAffine.activeValue]
  ring

theorem cycle_contracts (rates : Rates) (who : Player) :
    (∏ phase : Fin 3,
      quittingStationaryFixedOpponentsContinueMass (cycle rates phase) who) < 1 := by
  let survival := fun phase : Fin 3 =>
    quittingStationaryFixedOpponentsContinueMass (cycle rates phase) who
  have hsmall : ∃ phase : Fin 3, survival phase < 1 := by
    by_cases hwho : who = 1
    · subst who
      refine ⟨2, ?_⟩
      change quittingStationaryFixedOpponentsContinueMass (soloTwo rates) 1 < 1
      rw [soloTwo, quittingStationaryFixedOpponentsContinueMass_solo_other
        (by decide : (1 : Player) ≠ 2), quittingHazardCoin_false_toReal]
      linarith only [rates.w_mem.1]
    · refine ⟨1, ?_⟩
      change quittingStationaryFixedOpponentsContinueMass (soloOne rates) who < 1
      rw [soloOne, quittingStationaryFixedOpponentsContinueMass_solo_other hwho,
        quittingHazardCoin_false_toReal]
      linarith only [rates.z_mem.1]
  obtain ⟨phase, hphase⟩ := hsmall
  have hprod := Finset.prod_le_prod_of_subset_of_le_one₀
    (Finset.singleton_subset_iff.mpr (Finset.mem_univ phase))
    (fun index _ => quittingStationaryFixedOpponentsContinueMass_nonneg
      (cycle rates index) who)
    (fun index _ _ => quittingStationaryFixedOpponentsContinueMass_le_one
      (cycle rates index) who)
  exact lt_of_le_of_lt (by simpa [survival] using hprod) hphase

theorem low_continue (loss : ℝ) (reward : Reward) (table : RawTable loss reward)
    (rates : Rates) (hp : rates.p < 1)
    (hz : rates.z = second rates.p rates.y) (hw : rates.w = third rates.p rates.y)
    (hchild : childBalance loss rates.p rates.y = 0)
    (hpivot : pivotBalance loss rates.p rates.y = 0)
    (phase : Fin 3) (who : Player) :
    quittingRootContinuePayoff reward (lowValue loss rates (finRotate 3 phase))
      (cycle rates phase) who = lowValue loss rates phase who := by
  have hsoloOne : quittingSoloReward reward 1 = ![2, 1, 4, 0] := table.singleton_one
  have hsoloTwo : quittingSoloReward reward 2 = ![2, 0, 1, 4] := table.singleton_two
  have hpne : 1 - rates.p ≠ 0 := (sub_pos.mpr hp).ne'
  have hyne : 1 - rates.y ≠ 0 := (sub_pos.mpr rates.y_mem.2).ne'
  have hd : denominator rates.p rates.y ≠ 0 := by
    unfold denominator
    linarith [rates.y_mem.1]
  have hzm : rates.z * (3 * (1 - rates.p) * (1 - rates.y)) =
      rates.p + rates.y := by rw [hz, second]; field_simp
  have hwm : rates.w * denominator rates.p rates.y = 3 * rates.y - rates.p := by
    rw [hw, third]; exact div_mul_cancel₀ _ hd
  have hrest : (1 - rates.w) * denominator rates.p rates.y = 1 := by
    unfold denominator at *
    nlinarith only [hwm]
  have hchild' : rates.p * (1 - loss) / (1 - rates.p) + rates.z =
      (1 - rates.z) * (3 * rates.w - loss * rates.p * (1 - rates.w)) := by
    unfold childBalance at hchild
    rw [← hz, ← hw] at hchild
    linarith only [hchild]
  have hpivot' : (1 - loss * rates.y) / (1 - rates.y) =
      2 - (1 - rates.z) * (1 + loss * rates.y) / denominator rates.p rates.y := by
    unfold pivotBalance at hpivot
    rw [← hz] at hpivot
    linarith only [hpivot]
  fin_cases phase
  · change quittingRootContinuePayoff reward (lowB loss rates) (jointRoot rates) who =
      lowA loss rates who
    fin_cases who <;> dsimp only
    · change quittingRootContinuePayoff reward (lowB loss rates) (jointRoot rates) 0 = _
      rw [jointRoot, PairedCycle.rootContinue_first reward (lowB loss rates)
        (by decide : (0 : Player) ≠ 3),
        quittingHazardCoin_true_toReal, table.singleton_three]
      simp [lowA, lowB]
      field_simp
    · change quittingRootContinuePayoff reward (lowB loss rates) (jointRoot rates) 1 = _
      rw [jointRoot, PairedCycle.rootContinue_outside reward (lowB loss rates)
        (by decide : (0 : Player) ≠ 3)
        (by decide : (1 : Player) ≠ 0) (by decide : (1 : Player) ≠ 3),
        quittingHazardCoin_true_toReal, quittingHazardCoin_true_toReal,
        table.singleton_zero, table.singleton_three, table.joint]
      simp [lowA, lowB, Math.PairedAffine.bellman, Math.PairedAffine.contribution]
      ring
    · change quittingRootContinuePayoff reward (lowB loss rates) (jointRoot rates) 2 = _
      rw [jointRoot, PairedCycle.rootContinue_outside reward (lowB loss rates)
        (by decide : (0 : Player) ≠ 3)
        (by decide : (2 : Player) ≠ 0) (by decide : (2 : Player) ≠ 3),
        quittingHazardCoin_true_toReal, quittingHazardCoin_true_toReal,
        table.singleton_zero, table.singleton_three, table.joint]
      simp [lowA, lowB, Math.PairedAffine.bellman, Math.PairedAffine.contribution]
      nlinarith only [hzm]
    · change quittingRootContinuePayoff reward (lowB loss rates) (jointRoot rates) 3 = _
      rw [jointRoot, PairedCycle.rootContinue_second reward (lowB loss rates)
        (by decide : (0 : Player) ≠ 3),
        quittingHazardCoin_true_toReal, table.singleton_zero]
      simp [lowA, lowB]
      field_simp
      ring
  · change quittingRootContinuePayoff reward (lowC loss rates) (soloOne rates) who =
      lowB loss rates who
    fin_cases who <;> dsimp only
    · change quittingRootContinuePayoff reward (lowC loss rates) (soloOne rates) 0 = _
      rw [soloOne, quittingRootContinuePayoff_soloStationaryRoot_other reward
        (by decide : (0 : Player) ≠ 1),
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
      simp [hsoloOne, lowB, lowC]
      rw [hpivot']
      field_simp [hd]
      unfold denominator at hrest ⊢
      have hscaled := congrArg (fun t => (1 - rates.z) * (1 + loss * rates.y) * t) hrest
      nlinarith only [hscaled]
    · change quittingRootContinuePayoff reward (lowC loss rates) (soloOne rates) 1 = _
      rw [soloOne, quittingRootContinuePayoff_soloStationaryRoot_owner]
      rfl
    · change quittingRootContinuePayoff reward (lowC loss rates) (soloOne rates) 2 = _
      rw [soloOne, quittingRootContinuePayoff_soloStationaryRoot_other reward
        (by decide : (2 : Player) ≠ 1),
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
      simp [hsoloOne, lowB, lowC]
      ring
    · change quittingRootContinuePayoff reward (lowC loss rates) (soloOne rates) 3 = _
      rw [soloOne, quittingRootContinuePayoff_soloStationaryRoot_other reward
        (by decide : (3 : Player) ≠ 1),
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
      simp [hsoloOne, lowB, lowC]
      nlinarith only [hchild']
  · change quittingRootContinuePayoff reward (lowA loss rates) (soloTwo rates) who =
      lowC loss rates who
    fin_cases who <;> dsimp only
    · change quittingRootContinuePayoff reward (lowA loss rates) (soloTwo rates) 0 = _
      rw [soloTwo, quittingRootContinuePayoff_soloStationaryRoot_other reward
        (by decide : (0 : Player) ≠ 2),
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
      simp [hsoloTwo, lowA, lowC]
      ring
    · change quittingRootContinuePayoff reward (lowA loss rates) (soloTwo rates) 1 = _
      rw [soloTwo, quittingRootContinuePayoff_soloStationaryRoot_other reward
        (by decide : (1 : Player) ≠ 2),
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
      simp [hsoloTwo, lowA, lowC]
      unfold denominator at hwm
      nlinarith only [hwm]
    · change quittingRootContinuePayoff reward (lowA loss rates) (soloTwo rates) 2 = _
      rw [soloTwo, quittingRootContinuePayoff_soloStationaryRoot_owner]
      rfl
    · change quittingRootContinuePayoff reward (lowA loss rates) (soloTwo rates) 3 = _
      rw [soloTwo, quittingRootContinuePayoff_soloStationaryRoot_other reward
        (by decide : (3 : Player) ≠ 2),
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
      simp [hsoloTwo, lowA, lowC]
      ring

private theorem solo_quit_cap (reward : Reward) {owner other : Player}
    (hne : other ≠ owner) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (tail : Payoff Player) (bound : ℝ) (hown : quittingSoloReward reward other other = 1)
    (hcollision : quittingSingletonCollisionReward reward owner other ≤ bound) :
    quittingRootQuitPayoff reward tail
      (quittingSoloStationaryRoot owner (quittingHazardCoin q hq.1 hq.2)) other ≤
        1 + q * (bound - 1) := by
  rw [quittingRootQuitPayoff_soloStationaryRoot_other reward hne,
    quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal, hown]
  nlinarith only [mul_le_mul_of_nonneg_left hcollision hq.1]

theorem joint_quit_one_le (loss : ℝ) (reward : Reward) (table : RawTable loss reward)
    (rates : Rates) (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail (jointRoot rates) 1 ≤ 1 + loss * (rates.y - rates.p) := by
  rw [jointRoot, PairedCycle.rootQuit_eq_bellman reward tail
    (by decide : (0 : Player) ≠ 3), quittingHazardCoin_true_toReal,
    quittingHazardCoin_true_toReal, table.singleton_one]
  have hl := mul_le_mul_of_nonneg_left table.one_zero
    (mul_nonneg rates.p_mem.1 (sub_nonneg.mpr rates.y_mem.2.le))
  have hr := mul_le_mul_of_nonneg_left table.one_three
    (mul_nonneg (sub_nonneg.mpr rates.p_mem.2) rates.y_mem.1.le)
  have ht := mul_le_mul_of_nonneg_left table.one_both
    (mul_nonneg rates.p_mem.1 rates.y_mem.1.le)
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero,
    Math.PairedAffine.bellman, Math.PairedAffine.contribution]
  nlinarith only [hl, hr, ht]

theorem joint_quit_two_le (loss : ℝ) (reward : Reward) (table : RawTable loss reward)
    (rates : Rates) (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail (jointRoot rates) 2 ≤ 1 - loss * rates.p := by
  rw [jointRoot, PairedCycle.rootQuit_eq_bellman reward tail
    (by decide : (0 : Player) ≠ 3), quittingHazardCoin_true_toReal,
    quittingHazardCoin_true_toReal, table.singleton_two]
  have hl := mul_le_mul_of_nonneg_left table.two_zero
    (mul_nonneg rates.p_mem.1 (sub_nonneg.mpr rates.y_mem.2.le))
  have hr := mul_le_mul_of_nonneg_left table.two_three
    (mul_nonneg (sub_nonneg.mpr rates.p_mem.2) rates.y_mem.1.le)
  have ht := mul_le_mul_of_nonneg_left table.two_both
    (mul_nonneg rates.p_mem.1 rates.y_mem.1.le)
  simp [Math.PairedAffine.bellman, Math.PairedAffine.contribution]
  nlinarith only [hl, hr, ht]

def quitUpper (loss : ℝ) (rates : Rates) : Fin 3 → Payoff Player :=
  ![![1 - loss * rates.y, 1 + loss * (rates.y - rates.p),
      1 - loss * rates.p, 1 - loss * rates.p],
    ![1 + loss * rates.z, 1, 1 + loss * rates.z, 1],
    ![1, 1, 1, 1 + loss * rates.w]]

theorem quit_le (loss : ℝ) (reward : Reward) (table : RawTable loss reward)
    (rates : Rates) (tail : Payoff Player) (phase : Fin 3) (who : Player) :
    quittingRootQuitPayoff reward tail (cycle rates phase) who ≤
      quitUpper loss rates phase who := by
  have hown (player : Player) : quittingSoloReward reward player player = 1 := by
    fin_cases player
    · exact congrFun table.singleton_zero 0
    · exact congrFun table.singleton_one 1
    · exact congrFun table.singleton_two 2
    · exact congrFun table.singleton_three 3
  fin_cases phase
  · fin_cases who
    · exact (joint_quit_zero loss reward table rates tail).le
    · exact joint_quit_one_le loss reward table rates tail
    · exact joint_quit_two_le loss reward table rates tail
    · exact (joint_quit_three loss reward table rates tail).le
  · fin_cases who
    · have hc : quittingSingletonCollisionReward reward 1 0 ≤ 1 + loss := by
        simpa only [quittingSingletonCollisionReward, Finset.pair_comm] using table.zero_one
      simpa [cycle, soloOne, quitUpper, mul_comm] using
        solo_quit_cap reward (by decide : (0 : Player) ≠ 1) rates.z
          ⟨rates.z_mem.1.le, rates.z_mem.2.le⟩ tail (1 + loss) (hown 0) hc
    · change quittingRootQuitPayoff reward tail (soloOne rates) 1 ≤ 1
      rw [soloOne, quittingRootQuitPayoff_soloStationaryRoot_owner, hown]
    · have hc : quittingSingletonCollisionReward reward 1 2 ≤ 1 + loss := by
        simpa only [quittingSingletonCollisionReward, Finset.pair_comm] using table.two_one
      simpa [cycle, soloOne, quitUpper, mul_comm] using
        solo_quit_cap reward (by decide : (2 : Player) ≠ 1) rates.z
          ⟨rates.z_mem.1.le, rates.z_mem.2.le⟩ tail (1 + loss) (hown 2) hc
    · have hc : quittingSingletonCollisionReward reward 1 3 ≤ 1 := by
        simpa only [quittingSingletonCollisionReward, Finset.pair_comm] using table.three_one
      simpa [cycle, soloOne, quitUpper] using
        solo_quit_cap reward (by decide : (3 : Player) ≠ 1) rates.z
          ⟨rates.z_mem.1.le, rates.z_mem.2.le⟩ tail 1 (hown 3) hc
  · fin_cases who
    · have hc : quittingSingletonCollisionReward reward 2 0 ≤ 1 := by
        simpa only [quittingSingletonCollisionReward, Finset.pair_comm] using table.zero_two
      simpa [cycle, soloTwo, quitUpper] using
        solo_quit_cap reward (by decide : (0 : Player) ≠ 2) rates.w
          ⟨rates.w_mem.1.le, rates.w_mem.2.le⟩ tail 1 (hown 0) hc
    · have hc : quittingSingletonCollisionReward reward 2 1 ≤ 1 := by
        simpa only [quittingSingletonCollisionReward, Finset.pair_comm] using table.one_two
      simpa [cycle, soloTwo, quitUpper] using
        solo_quit_cap reward (by decide : (1 : Player) ≠ 2) rates.w
          ⟨rates.w_mem.1.le, rates.w_mem.2.le⟩ tail 1 (hown 1) hc
    · change quittingRootQuitPayoff reward tail (soloTwo rates) 2 ≤ 1
      rw [soloTwo, quittingRootQuitPayoff_soloStationaryRoot_owner, hown]
    · have hc : quittingSingletonCollisionReward reward 2 3 ≤ 1 + loss := by
        simpa only [quittingSingletonCollisionReward, Finset.pair_comm] using table.three_two
      simpa [cycle, soloTwo, quitUpper, mul_comm] using
        solo_quit_cap reward (by decide : (3 : Player) ≠ 2) rates.w
          ⟨rates.w_mem.1.le, rates.w_mem.2.le⟩ tail (1 + loss) (hown 3) hc

theorem low_upper_le (loss : ℝ) (reward : Reward) (table : RawTable loss reward)
    (rates : Rates) (hp : rates.p < 1 / 2) (hy : 2 / 5 < rates.y)
    (hz : rates.z = second rates.p rates.y) (hw : rates.w = third rates.p rates.y)
    (hchild : childBalance loss rates.p rates.y = 0)
    (hpivot : pivotBalance loss rates.p rates.y = 0)
    (phase : Fin 3) (who : Player) :
    quitUpper loss rates phase who ≤ lowValue loss rates phase who := by
  have hp1 : rates.p < 1 := by linarith
  have hd : 0 < denominator rates.p rates.y := by
    unfold denominator
    linarith [rates.y_mem.1]
  have hwm : rates.w * denominator rates.p rates.y = 3 * rates.y - rates.p := by
    rw [hw, third]; exact div_mul_cancel₀ _ hd.ne'
  have hrest : (1 - rates.w) * denominator rates.p rates.y = 1 := by
    unfold denominator at *
    nlinarith only [hwm]
  have hH : 0 < (3 - loss) * rates.y - rates.p := by
    nlinarith [mul_nonneg (sub_nonneg.mpr table.loss_mem.2) rates.y_mem.1.le]
  have hC0 : 1 ≤ lowC loss rates 0 := by
    have hs := congrArg (fun t => loss * rates.y * t) hrest
    have hid : (lowC loss rates 0 - 1) * denominator rates.p rates.y =
        (3 - loss) * rates.y - rates.p := by
      simp only [lowC, Matrix.cons_val_zero]
      nlinarith only [hwm, hs]
    exact le_of_lt (by nlinarith only [hid, hH, hd])
  have hC3 : 1 + loss * rates.w ≤ lowC loss rates 3 := by
    have hs := congrArg (fun t => loss * rates.p * t) hrest
    have ht := congrArg (fun t => (3 - loss) * t) hwm
    have hid : (lowC loss rates 3 - (1 + loss * rates.w)) *
        denominator rates.p rates.y = 3 * ((3 - loss) * rates.y - rates.p) := by
      simp [lowC]
      nlinarith only [hs, ht]
    exact le_of_lt (by nlinarith only [hid, hH, hd])
  have hB0 : 1 + loss * rates.z ≤ lowB loss rates 0 := by
    have heq := low_continue loss reward table rates hp1 hz hw hchild hpivot 1 0
    change quittingRootContinuePayoff reward (lowC loss rates) (soloOne rates) 0 = _ at heq
    rw [soloOne, quittingRootContinuePayoff_soloStationaryRoot_other reward
      (by decide : (0 : Player) ≠ 1), quittingHazardCoin_true_toReal,
      quittingHazardCoin_false_toReal] at heq
    have hsolo : quittingSoloReward reward 1 = ![2, 1, 4, 0] := table.singleton_one
    simp only [hsolo, Matrix.cons_val_zero] at heq
    change rates.z * 2 + (1 - rates.z) * lowC loss rates 0 = lowB loss rates 0 at heq
    have hm := mul_le_mul_of_nonneg_left hC0 (sub_nonneg.mpr rates.z_mem.2.le)
    have hl := mul_le_mul_of_nonneg_left table.loss_mem.2 rates.z_mem.1.le
    nlinarith only [heq, hm, hl]
  have hB3 : 1 ≤ lowB loss rates 3 := by
    have hnonneg : 0 ≤ rates.p * (1 - loss) / (1 - rates.p) :=
      div_nonneg (mul_nonneg rates.p_mem.1 (sub_nonneg.mpr table.loss_mem.2))
        (sub_pos.mpr hp1).le
    simp [lowB]
    exact hnonneg
  fin_cases phase <;> fin_cases who <;>
    simp [quitUpper, lowValue, lowA, lowB, lowC] at *
  all_goals first
    | exact hB0
    | exact hB3
    | exact hC0
    | exact hC3
    | nlinarith [mul_nonneg table.loss_mem.1.le rates.p_mem.1,
        mul_nonneg (show 0 ≤ 3 - loss by linarith [table.loss_mem.2]) rates.z_mem.1.le]

private theorem certificate_of_endpoints (reward : Reward) (rates : Rates)
    (value : Fin 3 → Payoff Player)
    (hcontinue : ∀ phase who, quittingRootContinuePayoff reward (value (finRotate 3 phase))
      (cycle rates phase) who = value phase who)
    (hquit : ∀ phase who, quittingRootQuitPayoff reward (value (finRotate 3 phase))
      (cycle rates phase) who ≤ value phase who)
    (hweighted : ∀ phase who, ((cycle rates phase) who true).toReal *
      (quittingRootQuitPayoff reward (value (finRotate 3 phase))
        (cycle rates phase) who - value phase who) = 0) :
    (∀ phase, value phase = quittingRootSuccessorPayoff reward
      (value (finRotate 3 phase)) (cycle rates phase)) ∧
    (∀ phase, IsεQuittingRootNash reward (value (finRotate 3 phase)) 0 (cycle rates phase)) := by
  have hpolicy (phase : Fin 3) : value phase = quittingRootSuccessorPayoff reward
      (value (finRotate 3 phase)) (cycle rates phase) := by
    funext who
    rw [quittingRootSuccessorPayoff_eq_endpointMix, hcontinue]
    have hsum := quittingRoot_continueProbability_add_quitProbability (cycle rates phase) who
    have hscaled := congrArg (fun t => t * value phase who) hsum
    nlinarith only [hscaled, hweighted phase who]
  refine ⟨hpolicy, fun phase => ?_⟩
  apply (isεQuittingRootEndpointNash_iff_isεQuittingRootNash _ _ _ _).mp
  apply (isεQuittingRootEndpointNash_iff_purePayoff_le _ _ _ _).mpr
  intro who
  rw [← hpolicy, add_zero]
  exact ⟨hquit phase who, (hcontinue phase who).le⟩

theorem low_certificate (loss : ℝ) (reward : Reward) (table : RawTable loss reward)
    (rates : Rates) (hp : rates.p < 1 / 2) (hy : 2 / 5 < rates.y)
    (hz : rates.z = second rates.p rates.y) (hw : rates.w = third rates.p rates.y)
    (hchild : childBalance loss rates.p rates.y = 0)
    (hpivot : pivotBalance loss rates.p rates.y = 0) :
    (∀ phase, lowValue loss rates phase = quittingRootSuccessorPayoff reward
      (lowValue loss rates (finRotate 3 phase)) (cycle rates phase)) ∧
    (∀ phase, IsεQuittingRootNash reward (lowValue loss rates (finRotate 3 phase))
      0 (cycle rates phase)) := by
  apply certificate_of_endpoints reward rates (lowValue loss rates)
  · exact low_continue loss reward table rates (by linarith) hz hw hchild hpivot
  · intro phase who
    exact (quit_le loss reward table rates _ phase who).trans
      (low_upper_le loss reward table rates hp hy hz hw hchild hpivot phase who)
  · intro phase who
    have hzero := joint_quit_zero loss reward table rates
    have hthree := joint_quit_three loss reward table rates
    have hone (tail : Payoff Player) :
        quittingRootQuitPayoff reward tail (soloOne rates) 1 = 1 := by
      rw [soloOne, quittingRootQuitPayoff_soloStationaryRoot_owner]
      exact congrFun table.singleton_one 1
    have htwo (tail : Payoff Player) :
        quittingRootQuitPayoff reward tail (soloTwo rates) 2 = 1 := by
      rw [soloTwo, quittingRootQuitPayoff_soloStationaryRoot_owner]
      exact congrFun table.singleton_two 2
    fin_cases phase <;> fin_cases who
    case «0».«0» => exact mul_eq_zero_of_right _ (sub_eq_zero.mpr (hzero _))
    case «0».«3» => exact mul_eq_zero_of_right _ (sub_eq_zero.mpr (hthree _))
    case «1».«1» => exact mul_eq_zero_of_right _ (sub_eq_zero.mpr (hone _))
    case «2».«2» => exact mul_eq_zero_of_right _ (sub_eq_zero.mpr (htwo _))
    all_goals simp [cycle, jointRoot, PairedCycle.root, soloOne, soloTwo,
      quittingSoloStationaryRoot]

theorem high_joint_eq_solo : jointRoot highRates =
    quittingSoloStationaryRoot (3 : Player)
      (quittingHazardCoin (2 / 3) (by norm_num) (by norm_num)) := by
  funext who
  fin_cases who <;>
    simp [jointRoot, highRates, PairedCycle.root, quittingSoloStationaryRoot,
      quittingHazardCoin_zero]

theorem high_continue (loss : ℝ) (reward : Reward) (table : RawTable loss reward)
    (phase : Fin 3) (who : Player) :
    quittingRootContinuePayoff reward (highValue (finRotate 3 phase))
      (cycle highRates phase) who = highValue phase who := by
  have hsoloOne : quittingSoloReward reward 1 = ![2, 1, 4, 0] := table.singleton_one
  have hsoloTwo : quittingSoloReward reward 2 = ![2, 0, 1, 4] := table.singleton_two
  have hsoloThree : quittingSoloReward reward 3 = ![0, 4, 0, 1] := table.singleton_three
  fin_cases phase
  · change quittingRootContinuePayoff reward (highValue 1) (jointRoot highRates) who =
      highValue 0 who
    rw [high_joint_eq_solo]
    by_cases hwho : who = 3
    · subst who
      rw [quittingRootContinuePayoff_soloStationaryRoot_owner]
      norm_num [highValue]
    · rw [quittingRootContinuePayoff_soloStationaryRoot_other reward hwho,
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal, hsoloThree]
      fin_cases who <;> norm_num [highValue]
  · change quittingRootContinuePayoff reward (highValue 2) (soloOne highRates) who =
      highValue 1 who
    by_cases hwho : who = 1
    · subst who
      rw [soloOne, quittingRootContinuePayoff_soloStationaryRoot_owner]
      norm_num [highValue]
    · rw [soloOne, quittingRootContinuePayoff_soloStationaryRoot_other reward hwho,
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal, hsoloOne]
      fin_cases who <;> norm_num [highValue, highRates]
  · change quittingRootContinuePayoff reward (highValue 0) (soloTwo highRates) who =
      highValue 2 who
    by_cases hwho : who = 2
    · subst who
      rw [soloTwo, quittingRootContinuePayoff_soloStationaryRoot_owner]
      norm_num [highValue]
    · rw [soloTwo, quittingRootContinuePayoff_soloStationaryRoot_other reward hwho,
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal, hsoloTwo]
      fin_cases who <;> norm_num [highValue, highRates]

theorem high_upper_le (loss : ℝ) (reward : Reward) (table : RawTable loss reward)
    (hloss : 15 / 26 ≤ loss) (phase : Fin 3) (who : Player) :
    quitUpper loss highRates phase who ≤ highValue phase who := by
  fin_cases phase <;> fin_cases who <;>
    norm_num [quitUpper, highRates, highValue] <;> linarith [table.loss_mem.2]

theorem high_certificate (loss : ℝ) (reward : Reward) (table : RawTable loss reward)
    (hloss : 15 / 26 ≤ loss) :
    (∀ phase, highValue phase = quittingRootSuccessorPayoff reward
      (highValue (finRotate 3 phase)) (cycle highRates phase)) ∧
    (∀ phase, IsεQuittingRootNash reward (highValue (finRotate 3 phase))
      0 (cycle highRates phase)) := by
  apply certificate_of_endpoints reward highRates highValue
  · exact high_continue loss reward table
  · intro phase who
    exact (quit_le loss reward table highRates _ phase who).trans
      (high_upper_le loss reward table hloss phase who)
  · intro phase who
    have hthree (tail : Payoff Player) :
        quittingRootQuitPayoff reward tail (jointRoot highRates) 3 = 1 := by
      simpa only [highRates, mul_zero, sub_zero] using
        joint_quit_three loss reward table highRates tail
    have hone (tail : Payoff Player) :
        quittingRootQuitPayoff reward tail (soloOne highRates) 1 = 1 := by
      rw [soloOne, quittingRootQuitPayoff_soloStationaryRoot_owner]
      exact congrFun table.singleton_one 1
    have htwo (tail : Payoff Player) :
        quittingRootQuitPayoff reward tail (soloTwo highRates) 2 = 1 := by
      rw [soloTwo, quittingRootQuitPayoff_soloStationaryRoot_owner]
      exact congrFun table.singleton_two 2
    fin_cases phase <;> fin_cases who
    case «0».«3» => exact mul_eq_zero_of_right _ (sub_eq_zero.mpr (hthree _))
    case «1».«1» => exact mul_eq_zero_of_right _ (sub_eq_zero.mpr (hone _))
    case «2».«2» => exact mul_eq_zero_of_right _ (sub_eq_zero.mpr (htwo _))
    all_goals simp [cycle, jointRoot, PairedCycle.root, soloOne, soloTwo,
      quittingSoloStationaryRoot, highRates, quittingHazardCoin_true_toReal]

def opponentProduct (rates : Rates) : Payoff Player :=
  ![(1 - rates.y) * (1 - rates.z) * (1 - rates.w),
    (1 - rates.p) * (1 - rates.y) * (1 - rates.w),
    (1 - rates.p) * (1 - rates.y) * (1 - rates.z),
    (1 - rates.p) * (1 - rates.z) * (1 - rates.w)]

/-- The four actual opponent-cycle factors, including the zero-pivot branch. -/
theorem cycle_opponentProduct (rates : Rates) (who : Player) :
    (∏ phase : Fin 3,
      quittingStationaryFixedOpponentsContinueMass (cycle rates phase) who) =
        opponentProduct rates who := by
  fin_cases who <;>
    simp [Fin.prod_univ_succ, cycle, quittingStationaryFixedOpponentsContinueMass,
      quittingFixedOpponentsContinueMass,
      quittingStationaryContinueMass_eq_prod_continueProbability,
      jointRoot, PairedCycle.root, soloOne, soloTwo, quittingSoloStationaryRoot,
      quittingHazardCoin_false_toReal, opponentProduct] <;> ring

end GameTheory.NegativePremiumCyclicChild
