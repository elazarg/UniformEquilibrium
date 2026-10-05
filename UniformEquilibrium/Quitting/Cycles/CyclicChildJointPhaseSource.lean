import MathUE.CyclicChildJointPhasePivot
import UniformEquilibrium.Quitting.Cycles.MixedCycleUniformPayoff
import UniformEquilibrium.Quitting.Root.PairedProductRoot
import UniformEquilibrium.Quitting.Root.SingletonRootEndpoints
import UniformEquilibrium.Quitting.Stationary.MinMax

/-! # Actual cyclic-child joint-phase source

The scalar parameters and literal reward rows are raw table data. The proper
hazards and continuation vectors are computed from the selected balance root.
Unspecified coalition rewards are retained, not replaced by singleton data.
-/

noncomputable section

namespace GameTheory.CyclicChildJointPhase

open _root_.Math.CyclicChildJointPhase _root_.Math.Probability

abbrev Player := Fin 4
abbrev Reward := {S : Finset Player // S.Nonempty} → Payoff Player

/-- The five specified reward rows and the retained-row outsider caps.
No favorable root, weight, profile or continuation is a field. -/
structure RawTable (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward) : Prop where
  singleton_zero : reward (quittingSingletonTerminal 0) = ![1, -data.h₁, -data.h₂, -data.h₃]
  singleton_one : reward (quittingSingletonTerminal 1) = ![u, 0, data.b, -1]
  singleton_two : reward (quittingSingletonTerminal 2) = ![v, -1, 0, data.c]
  singleton_three : reward (quittingSingletonTerminal 3) = ![R, data.a, -1, 0]
  joint : reward ⟨{0, 1}, by simp⟩ = ![1 + ξ, data.η, data.q₂, data.q₃]
  outsider_two : reward ⟨{2, 0}, by simp⟩ 2 ≤ 0 ∧
    reward ⟨{2, 1}, by simp⟩ 2 ≤ 0 ∧ reward ⟨{2, 0, 1}, by simp⟩ 2 ≤ 0
  outsider_three : reward ⟨{3, 0}, by simp⟩ 3 ≤ 0 ∧
    reward ⟨{3, 1}, by simp⟩ 3 ≤ 0 ∧ reward ⟨{3, 0, 1}, by simp⟩ 3 ≤ 0

def first (data : JointPhaseData) (y : ℝ) : ℝ := data.root y / (1 + data.root y)

def valueA (data : JointPhaseData) (ξ y : ℝ) : Payoff Player :=
  ![1 + ξ * y, data.η * first data y, data.third y / (1 - data.third y), 0]

def valueC (data : JointPhaseData) (ξ R y : ℝ) : Payoff Player :=
  ![(1 - data.third y) * (1 + ξ * y) + R * data.third y,
    (1 - data.third y) * (data.η * first data y) + data.a * data.third y, 0, 0]

def valueB (data : JointPhaseData) (v ξ R y : ℝ) : Payoff Player :=
  ![v * data.second y + (1 - data.second y) * valueC data ξ R y 0,
    (1 - data.second y) * valueC data ξ R y 1 - data.second y, 0,
    data.c * data.second y]

theorem rates_spec (data : JointPhaseData) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper) :
    0 < data.root y ∧ first data y ∈ Set.Ioo 0 1 ∧
      data.second y ∈ Set.Ioo 0 1 ∧ data.third y ∈ Set.Ioo 0 1 ∧
      balanceValue data.a data.b data.c data.h₁ data.η
        (jointLoss data.h₂ data.q₂ y) (jointLoss data.h₃ data.q₃ y) (data.root y) y = 0 := by
  have hs := selectedBalanceRoot_spec data.a_pos data.b_pos data.c_pos data.h₁_pos
    data.h₂_pos data.h₃_pos data.eta_nonneg data.q₂_nonpos data.q₃_nonpos data.gap_pos hy
  refine ⟨hs.1.1, ?_, hs.2⟩
  unfold first
  have hden : 0 < 1 + data.root y := add_pos zero_lt_one hs.1.1
  exact ⟨div_pos hs.1.1 hden, (div_lt_one hden).mpr (lt_add_of_pos_left _ zero_lt_one)⟩

theorem valueB_one (data : JointPhaseData) (v ξ R : ℝ) {y : ℝ}
    (hy : y ∈ Set.Ioo 0 data.upper) :
    valueB data v ξ R y 1 = data.root y * (data.h₁ + data.η) := by
  have hbalance := (rates_spec data hy).2.2.2.2
  have hid : valueB data v ξ R y 1 - data.root y * (data.h₁ + data.η) =
      -balanceValue data.a data.b data.c data.h₁ data.η
        (jointLoss data.h₂ data.q₂ y) (jointLoss data.h₃ data.q₃ y) (data.root y) y := by
    change valueB data v ξ R y 1 - data.root y * (data.h₁ + data.η) =
      -(data.h₁ * data.root y + data.second y -
        data.a * data.third y * (1 - data.second y) + data.η * data.root y *
          (1 - (1 - data.second y) * (1 - data.third y) / (1 + data.root y)))
    simp only [valueB, valueC, Matrix.cons_val_one, Matrix.cons_val_zero, first]
    ring
  rw [hbalance] at hid
  linarith only [hid]

theorem valueB_zero (data : JointPhaseData) (u v ξ R : ℝ) {y : ℝ}
    (hy : y ∈ Set.Ioo 0 data.upper) (hpivot : data.pivot u v ξ y = R) :
    valueB data v ξ R y 0 = (1 + ξ * y - u * y) / (1 - y) := by
  have hrate := rates_spec data hy
  have hy1 : y < 1 := hy.2.trans data.upper_bounds.2.2
  rw [data.pivot_eq_uncanceled u v ξ hy.1.ne'] at hpivot
  have hden : (1 - data.second y) * data.third y ≠ 0 :=
    (mul_pos (sub_pos.mpr hrate.2.2.1.2) hrate.2.2.2.1.1).ne'
  have hrelation := (div_eq_iff hden).mp
    (show ((1 + ξ * y - u) * y / (1 - y) +
        (1 + ξ * y - v) * data.second y) /
        ((1 - data.second y) * data.third y) = R - (1 + ξ * y) by
      linarith only [hpivot])
  apply (eq_div_iff (sub_pos.mpr hy1).ne').mpr
  simp only [valueB, valueC, Matrix.cons_val_zero]
  have hrelation' := congrArg (fun t => t * (1 - y)) hrelation
  rw [add_mul, div_mul_cancel₀ _ (sub_pos.mpr hy1).ne'] at hrelation'
  nlinarith only [hrelation']

theorem third_odds (data : JointPhaseData) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper) :
    data.third y / (1 - data.third y) =
      (data.b * y - jointLoss data.h₂ data.q₂ y * data.root y) / (1 + data.root y) := by
  have hrate := rates_spec data hy
  have hD := data.selected_denominator_pos (Set.Ioo_subset_Icc_self hy)
  have hw : data.third y *
      balanceDenominator data.b (jointLoss data.h₂ data.q₂ y) (data.root y) y =
      data.b * y - jointLoss data.h₂ data.q₂ y * data.root y := by
    unfold JointPhaseData.third soloThirdHazard
    exact div_mul_cancel₀ _ hD.ne'
  have hrest : (1 - data.third y) *
      balanceDenominator data.b (jointLoss data.h₂ data.q₂ y) (data.root y) y =
      1 + data.root y := by
    unfold balanceDenominator at *
    nlinarith only [hw]
  apply (div_eq_div_iff (sub_pos.mpr hrate.2.2.2.1.2).ne'
    (add_pos zero_lt_one hrate.1).ne').mpr
  rw [← hrest, ← hw]
  ring

theorem solo_three_policy (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper) :
    valueC data ξ R y = quittingRootSuccessorPayoff reward (valueA data ξ y)
      (quittingSoloStationaryRoot 3 (quittingHazardCoin (data.third y)
        (rates_spec data hy).2.2.2.1.1.le (rates_spec data hy).2.2.2.1.2.le)) := by
  rw [quittingRootSuccessorPayoff_solo]
  funext who
  rw [quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
  change valueC data ξ R y who = data.third y *
    reward (quittingSingletonTerminal 3) who + (1 - data.third y) * valueA data ξ y who
  rw [table.singleton_three]
  fin_cases who
  · simp [valueA, valueC, mul_comm, add_comm]
  · simp [valueA, valueC, mul_comm, add_comm]
  · change (0 : ℝ) = data.third y * (-1) +
      (1 - data.third y) * (data.third y / (1 - data.third y))
    field_simp [(sub_pos.mpr (rates_spec data hy).2.2.2.1.2).ne']
    ring
  · simp [valueA, valueC]

theorem solo_two_policy (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper) :
    valueB data v ξ R y = quittingRootSuccessorPayoff reward (valueC data ξ R y)
      (quittingSoloStationaryRoot 2 (quittingHazardCoin (data.second y)
        (rates_spec data hy).2.2.1.1.le (rates_spec data hy).2.2.1.2.le)) := by
  rw [quittingRootSuccessorPayoff_solo]
  funext who
  rw [quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
  change valueB data v ξ R y who = data.second y *
    reward (quittingSingletonTerminal 2) who + (1 - data.second y) * valueC data ξ R y who
  rw [table.singleton_two]
  fin_cases who <;> simp [valueB, valueC] <;> ring

def jointRoot (data : JointPhaseData) (y : ℝ) (hy : y ∈ Set.Ioo 0 data.upper) :
    Player → PMF Bool :=
  PairedCycle.root 0 1
    (quittingHazardCoin (first data y) (rates_spec data hy).2.1.1.le
      (rates_spec data hy).2.1.2.le)
    (quittingHazardCoin y hy.1.le (hy.2.trans data.upper_bounds.2.2).le)

theorem joint_quit_zero (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper) :
    quittingRootQuitPayoff reward (valueB data v ξ R y) (jointRoot data y hy) 0 =
      valueA data ξ y 0 := by
  unfold jointRoot
  rw [PairedCycle.rootQuit_first reward _ (by decide : (0 : Player) ≠ 1),
    quittingHazardCoin_true_toReal, table.singleton_zero, table.joint]
  simp [Math.PairedAffine.activeValue, valueA]
  ring

theorem joint_quit_one (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper) :
    quittingRootQuitPayoff reward (valueB data v ξ R y) (jointRoot data y hy) 1 =
      valueA data ξ y 1 := by
  unfold jointRoot
  rw [PairedCycle.rootQuit_second reward _ (by decide : (0 : Player) ≠ 1),
    quittingHazardCoin_true_toReal, table.singleton_one, table.joint]
  simp [Math.PairedAffine.activeValue, valueA]
  ring

theorem joint_continue_zero (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper)
    (hpivot : data.pivot u v ξ y = R) :
    quittingRootContinuePayoff reward (valueB data v ξ R y) (jointRoot data y hy) 0 =
      valueA data ξ y 0 := by
  unfold jointRoot
  rw [PairedCycle.rootContinue_first reward _ (by decide : (0 : Player) ≠ 1),
    quittingHazardCoin_true_toReal, table.singleton_one, valueB_zero data u v ξ R hy hpivot]
  simp only [Matrix.cons_val_zero, valueA]
  field_simp [(sub_pos.mpr (hy.2.trans data.upper_bounds.2.2)).ne']
  ring

theorem joint_continue_one (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper) :
    quittingRootContinuePayoff reward (valueB data v ξ R y) (jointRoot data y hy) 1 =
      valueA data ξ y 1 := by
  unfold jointRoot
  rw [PairedCycle.rootContinue_second reward _ (by decide : (0 : Player) ≠ 1),
    quittingHazardCoin_true_toReal, table.singleton_zero, valueB_one data v ξ R hy]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, valueA, first]
  have hk := (rates_spec data hy).1
  field_simp [(add_pos zero_lt_one hk).ne']
  ring

theorem joint_continue_two (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper) :
    quittingRootContinuePayoff reward (valueB data v ξ R y) (jointRoot data y hy) 2 =
      valueA data ξ y 2 := by
  unfold jointRoot
  rw [PairedCycle.rootContinue_outside reward _ (by decide : (0 : Player) ≠ 1)
    (by decide : (2 : Player) ≠ 0) (by decide : (2 : Player) ≠ 1),
    quittingHazardCoin_true_toReal, quittingHazardCoin_true_toReal,
    table.singleton_zero, table.singleton_one, table.joint]
  change Math.PairedAffine.bellman (-data.h₂) data.b data.q₂ (first data y) y 0 =
    data.third y / (1 - data.third y)
  rw [third_odds data hy]
  unfold Math.PairedAffine.bellman Math.PairedAffine.contribution first jointLoss
  field_simp [(add_pos zero_lt_one (rates_spec data hy).1).ne']
  ring

theorem joint_continue_three (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper) :
    quittingRootContinuePayoff reward (valueB data v ξ R y) (jointRoot data y hy) 3 =
      valueA data ξ y 3 := by
  unfold jointRoot
  rw [PairedCycle.rootContinue_outside reward _ (by decide : (0 : Player) ≠ 1)
    (by decide : (3 : Player) ≠ 0) (by decide : (3 : Player) ≠ 1),
    quittingHazardCoin_true_toReal, quittingHazardCoin_true_toReal,
    table.singleton_zero, table.singleton_one, table.joint]
  have hz : data.second y * (data.c * (1 - y)) =
      jointLoss data.h₃ data.q₃ y * data.root y + y := by
    unfold JointPhaseData.second soloSecondHazard
    exact div_mul_cancel₀ _ (mul_pos data.c_pos
      (sub_pos.mpr (hy.2.trans data.upper_bounds.2.2))).ne'
  change Math.PairedAffine.bellman (-data.h₃) (-1) data.q₃ (first data y) y
    (data.c * data.second y) = 0
  unfold Math.PairedAffine.bellman Math.PairedAffine.contribution first
  field_simp [(add_pos zero_lt_one (rates_spec data hy).1).ne']
  unfold jointLoss at hz
  nlinarith only [hz]

theorem joint_continue (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper)
    (hpivot : data.pivot u v ξ y = R) (who : Player) :
    quittingRootContinuePayoff reward (valueB data v ξ R y) (jointRoot data y hy) who =
      valueA data ξ y who := by
  fin_cases who
  · exact joint_continue_zero data u v ξ R reward table hy hpivot
  · exact joint_continue_one data u v ξ R reward table hy
  · exact joint_continue_two data u v ξ R reward table hy
  · exact joint_continue_three data u v ξ R reward table hy

theorem joint_policy (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper)
    (hpivot : data.pivot u v ξ y = R) :
    valueA data ξ y = quittingRootSuccessorPayoff reward (valueB data v ξ R y)
      (jointRoot data y hy) := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    joint_continue data u v ξ R reward table hy hpivot]
  by_cases hzero : who = 0
  · subst who
    rw [joint_quit_zero data u v ξ R reward table hy,
      Math.PMFProduct.pmfBool_false_toReal]
    ring
  by_cases hone : who = 1
  · subst who
    rw [joint_quit_one data u v ξ R reward table hy,
      Math.PMFProduct.pmfBool_false_toReal]
    ring
  · have hquiet : jointRoot data y hy who = PMF.pure false :=
      PairedCycle.root_outside hzero hone _ _
    rw [hquiet]
    simp

theorem joint_quit_outsider_le_zero (data : JointPhaseData) (u v ξ R : ℝ)
    (reward : Reward) (table : RawTable data u v ξ R reward) {y : ℝ}
    (hy : y ∈ Set.Ioo 0 data.upper) (who : Player) (hwho : who = 2 ∨ who = 3) :
    quittingRootQuitPayoff reward (valueB data v ξ R y) (jointRoot data y hy) who ≤ 0 := by
  unfold jointRoot
  rw [PairedCycle.rootQuit_eq_bellman reward _ (by decide : (0 : Player) ≠ 1),
    quittingHazardCoin_true_toReal, quittingHazardCoin_true_toReal]
  apply Math.PairedAffine.bellman_le (Set.Ioo_subset_Icc_self (rates_spec data hy).2.1)
    ⟨hy.1.le, (hy.2.trans data.upper_bounds.2.2).le⟩
  · rcases hwho with rfl | rfl
    · exact table.outsider_two.1
    · exact table.outsider_three.1
  · rcases hwho with rfl | rfl
    · exact table.outsider_two.2.1
    · exact table.outsider_three.2.1
  · rcases hwho with rfl | rfl
    · exact table.outsider_two.2.2
    · exact table.outsider_three.2.2
  · rcases hwho with rfl | rfl
    · rw [table.singleton_two]
      simp
    · rw [table.singleton_three]
      simp

def coarseValue (data : JointPhaseData) (v ξ R y : ℝ) : Fin 3 → Payoff Player :=
  ![valueA data ξ y, valueB data v ξ R y, valueC data ξ R y]

theorem singleton_floors (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) (hξ : 0 < ξ) (hv : v < 1)
    (hu : u ≤ 1 + ξ) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper)
    (hpivot : data.pivot u v ξ y = R) (block : Fin 3) (who : Player) :
    quittingSoloReward reward who who ≤ coarseValue data v ξ R y block who := by
  have hr := rates_spec data hy
  have hη := data.eta_nonneg
  have ha := data.a_pos
  have hc := data.c_pos
  have hx := hr.2.1.1
  have hz := hr.2.2.1.1
  have hw := hr.2.2.2.1.1
  have hsw : 0 < 1 - data.third y := sub_pos.mpr hr.2.2.2.1.2
  have hsy : 0 < 1 - y := sub_pos.mpr (hy.2.trans data.upper_bounds.2.2)
  have hA : 1 ≤ valueA data ξ y 0 := by
    change 1 ≤ 1 + ξ * y
    exact le_add_of_nonneg_right (mul_pos hξ hy.1).le
  have hB : 1 ≤ valueB data v ξ R y 0 := by
    rw [valueB_zero data u v ξ R hy hpivot]
    apply (le_div_iff₀ hsy).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hu) hy.1.le]
  have hC : 1 ≤ valueC data ξ R y 0 := by
    have hBdef : valueB data v ξ R y 0 =
        v * data.second y + (1 - data.second y) * valueC data ξ R y 0 := rfl
    have hstrict := mul_pos (sub_pos.mpr hv) hz
    by_contra hnot
    have hbound := mul_le_mul_of_nonneg_left (lt_of_not_ge hnot).le
      (sub_pos.mpr hr.2.2.1.2).le
    nlinarith only [hB, hBdef, hstrict, hbound]
  have hB1 : 0 ≤ valueB data v ξ R y 1 := by
    rw [valueB_one data v ξ R hy]
    exact (mul_pos hr.1 (add_pos_of_pos_of_nonneg data.h₁_pos hη)).le
  have hsolo : quittingSoloReward reward who who = if who = 0 then 1 else 0 := by
    fin_cases who
    · change reward (quittingSingletonTerminal 0) 0 = _
      rw [table.singleton_zero]
      norm_num
    · change reward (quittingSingletonTerminal 1) 1 = _
      rw [table.singleton_one]
      norm_num
    · change reward (quittingSingletonTerminal 2) 2 = _
      rw [table.singleton_two]
      norm_num
    · change reward (quittingSingletonTerminal 3) 3 = _
      rw [table.singleton_three]
      norm_num
  rw [hsolo]
  fin_cases block
  · change (if who = 0 then 1 else 0) ≤ valueA data ξ y who
    fin_cases who
    · exact hA
    · change 0 ≤ data.η * first data y
      exact mul_nonneg hη hx.le
    · change 0 ≤ data.third y / (1 - data.third y)
      exact (div_pos hw hsw).le
    · exact le_rfl
  · change (if who = 0 then 1 else 0) ≤ valueB data v ξ R y who
    fin_cases who
    · exact hB
    · exact hB1
    · exact le_rfl
    · change 0 ≤ data.c * data.second y
      exact (mul_pos hc hz).le
  · change (if who = 0 then 1 else 0) ≤ valueC data ξ R y who
    fin_cases who
    · exact hC
    · change 0 ≤ (1 - data.third y) * (data.η * first data y) + data.a * data.third y
      exact add_nonneg (mul_nonneg hsw.le (mul_nonneg hη hx.le)) (mul_pos ha hw).le
    · exact le_rfl
    · exact le_rfl

def coarseSolo : Fin 3 → Bool := ![false, true, true]
def coarseOwner : Fin 3 → Player := ![0, 2, 3]
def coarseMass (data : JointPhaseData) (y : ℝ) : Fin 3 → ℝ := ![0, data.second y, data.third y]

def coarseRoot (data : JointPhaseData) (y : ℝ) (hy : y ∈ Set.Ioo 0 data.upper) :
    Fin 3 → Player → PMF Bool :=
  ![jointRoot data y hy,
    quittingSoloStationaryRoot 2 (quittingHazardCoin (data.second y)
      (rates_spec data hy).2.2.1.1.le (rates_spec data hy).2.2.1.2.le),
    quittingSoloStationaryRoot 3 (quittingHazardCoin (data.third y)
      (rates_spec data hy).2.2.2.1.1.le (rates_spec data hy).2.2.2.1.2.le)]

theorem coarse_policy (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper)
    (hpivot : data.pivot u v ξ y = R) (block : Fin 3) :
    coarseValue data v ξ R y block = quittingRootSuccessorPayoff reward
      (coarseValue data v ξ R y (finRotate 3 block)) (coarseRoot data y hy block) := by
  fin_cases block
  · exact joint_policy data u v ξ R reward table hy hpivot
  · exact solo_two_policy data u v ξ R reward table hy
  · exact solo_three_policy data u v ξ R reward table hy

theorem coarse_continue (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper)
    (hpivot : data.pivot u v ξ y = R) (block : Fin 3) (who : Player) :
    quittingRootContinuePayoff reward (coarseValue data v ξ R y (finRotate 3 block))
      (coarseRoot data y hy block) who = coarseValue data v ξ R y block who := by
  fin_cases block
  · exact joint_continue data u v ξ R reward table hy hpivot who
  · change quittingRootContinuePayoff reward (valueC data ξ R y)
      (quittingSoloStationaryRoot 2 (quittingHazardCoin (data.second y)
        (rates_spec data hy).2.2.1.1.le (rates_spec data hy).2.2.1.2.le)) who =
      valueB data v ξ R y who
    by_cases hwho : who = 2
    · subst who
      rw [quittingRootContinuePayoff_soloStationaryRoot_owner]
      rfl
    · rw [quittingRootContinuePayoff_soloStationaryRoot_other reward hwho,
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
      have hpolicy := congrFun (solo_two_policy data u v ξ R reward table hy) who
      rw [quittingRootSuccessorPayoff_solo, quittingHazardCoin_true_toReal,
        quittingHazardCoin_false_toReal] at hpolicy
      exact hpolicy.symm
  · change quittingRootContinuePayoff reward (valueA data ξ y)
      (quittingSoloStationaryRoot 3 (quittingHazardCoin (data.third y)
        (rates_spec data hy).2.2.2.1.1.le (rates_spec data hy).2.2.2.1.2.le)) who =
      valueC data ξ R y who
    by_cases hwho : who = 3
    · subst who
      rw [quittingRootContinuePayoff_soloStationaryRoot_owner]
      rfl
    · rw [quittingRootContinuePayoff_soloStationaryRoot_other reward hwho,
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
      have hpolicy := congrFun (solo_three_policy data u v ξ R reward table hy) who
      rw [quittingRootSuccessorPayoff_solo, quittingHazardCoin_true_toReal,
        quittingHazardCoin_false_toReal] at hpolicy
      exact hpolicy.symm

theorem coarse_contracts (data : JointPhaseData) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper)
    (who : Player) :
    (∏ block : Fin 3,
      quittingStationaryFixedOpponentsContinueMass (coarseRoot data y hy block) who) < 1 := by
  let survival := fun block : Fin 3 =>
    quittingStationaryFixedOpponentsContinueMass (coarseRoot data y hy block) who
  have hsmall : ∃ block : Fin 3, survival block < 1 := by
    by_cases hwho : who = 2
    · subst who
      refine ⟨2, ?_⟩
      change quittingStationaryFixedOpponentsContinueMass
        (quittingSoloStationaryRoot 3 (quittingHazardCoin (data.third y)
          (rates_spec data hy).2.2.2.1.1.le (rates_spec data hy).2.2.2.1.2.le)) 2 < 1
      rw [quittingStationaryFixedOpponentsContinueMass_solo_other
        (by decide : (2 : Player) ≠ 3), quittingHazardCoin_false_toReal]
      linarith only [(rates_spec data hy).2.2.2.1.1]
    · refine ⟨1, ?_⟩
      change quittingStationaryFixedOpponentsContinueMass
        (quittingSoloStationaryRoot 2 (quittingHazardCoin (data.second y)
          (rates_spec data hy).2.2.1.1.le (rates_spec data hy).2.2.1.2.le)) who < 1
      rw [quittingStationaryFixedOpponentsContinueMass_solo_other hwho,
        quittingHazardCoin_false_toReal]
      linarith only [(rates_spec data hy).2.2.1.1]
  obtain ⟨block, hblock⟩ := hsmall
  have hprod := Finset.prod_le_prod_of_subset_of_le_one₀
    (Finset.singleton_subset_iff.mpr (Finset.mem_univ block))
    (fun index _ => quittingStationaryFixedOpponentsContinueMass_nonneg
      (coarseRoot data y hy index) who)
    (fun index _ _ => quittingStationaryFixedOpponentsContinueMass_le_one
      (coarseRoot data y hy index) who)
  simp only [Finset.prod_singleton] at hprod
  exact hprod.trans_lt hblock

/-- Every coarse compiler field is discharged from the literal raw table.
Only the selected scalar pivot equality enters this intermediate adapter. -/
theorem sourceCertificate (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) (hξ : 0 < ξ) (hv : v < 1)
    (hu : u ≤ 1 + ξ) {y : ℝ} (hy : y ∈ Set.Ioo 0 data.upper)
    (hpivot : data.pivot u v ξ y = R) :
    MixedCycleSoloMesh.SourceCertificate reward coarseSolo coarseOwner
      (coarseMass data y) (coarseRoot data y hy) (coarseValue data v ξ R y) := by
  refine ⟨?_, ?_, ?_, coarse_policy data u v ξ R reward table hy hpivot,
    coarse_continue data u v ξ R reward table hy hpivot,
    singleton_floors data u v ξ R reward table hξ hv hu hy hpivot, ?_,
    coarse_contracts data hy⟩
  · intro block hsolo
    fin_cases block
    · norm_num [coarseSolo] at hsolo
    · exact (rates_spec data hy).2.2.1.1.le
    · exact (rates_spec data hy).2.2.2.1.1.le
  · intro block hsolo
    fin_cases block
    · norm_num [coarseSolo] at hsolo
    · exact (rates_spec data hy).2.2.1.2
    · exact (rates_spec data hy).2.2.2.1.2
  · intro block hsolo
    fin_cases block
    · norm_num [coarseSolo] at hsolo
    · rfl
    · rfl
  · intro block hretained who
    fin_cases block
    · change quittingRootQuitPayoff reward (valueB data v ξ R y)
        (jointRoot data y hy) who ≤ valueA data ξ y who
      by_cases hzero : who = 0
      · subst who
        exact (joint_quit_zero data u v ξ R reward table hy).le
      by_cases hone : who = 1
      · subst who
        exact (joint_quit_one data u v ξ R reward table hy).le
      have hwho : who = 2 ∨ who = 3 := by
        fin_cases who <;> simp_all
      have hcap := joint_quit_outsider_le_zero data u v ξ R reward table hy who hwho
      have hfloor := singleton_floors data u v ξ R reward table hξ hv hu hy hpivot 0 who
      have hsolo : quittingSoloReward reward who who = 0 := by
        rcases hwho with rfl | rfl
        · change reward (quittingSingletonTerminal 2) 2 = 0
          rw [table.singleton_two]
          rfl
        · change reward (quittingSingletonTerminal 3) 3 = 0
          rw [table.singleton_three]
          rfl
      rw [hsolo] at hfloor
      exact hcap.trans hfloor
    · norm_num [coarseSolo] at hretained
    · norm_num [coarseSolo] at hretained

/-- Raw table data internally selects one proper cycle and one exact target,
before any accuracy requested by the shared full-behavior compiler. -/
theorem exists_uniformPayoff (data : JointPhaseData) (u v ξ R : ℝ) (reward : Reward)
    (table : RawTable data u v ξ R reward) (hξ : 0 < ξ) (hv : v < 1)
    (hu : u ≤ 1 + ξ)
    (hR : R ∈ Set.Ioo (data.pivotLower u v) (data.pivotUpper u v ξ)) :
    ∃ y ∈ Set.Ioo 0 data.upper,
      (quittingGame reward).IsUniformEquilibriumPayoff none (valueA data ξ y) := by
  obtain ⟨y, hy, hpivot⟩ := data.exists_pivot u v ξ R hR
  exact ⟨y, hy, MixedCycleSoloMesh.isUniformEquilibriumPayoff reward coarseSolo coarseOwner
    (coarseMass data y) (coarseRoot data y hy) (coarseValue data v ξ R y)
    (sourceCertificate data u v ξ R reward table hξ hv hu hy hpivot) 0⟩

end GameTheory.CyclicChildJointPhase
