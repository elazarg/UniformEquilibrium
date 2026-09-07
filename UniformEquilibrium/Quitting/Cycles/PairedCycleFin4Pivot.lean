import UniformEquilibrium.Quitting.Cycles.PairedCycleEquilibrium
import UniformEquilibrium.Quitting.Terminal.SinglePivotFiniteMenuSource

/-! # The literal Fin4 paired-cycle single-pivot normalization -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine

/-- Ordered pairs `{0,2}`, `{1,3}`. Phase zero is the pivot's active pair. -/
def fin4Schedule : Schedule (Fin 4) 2 where
  label := Equiv.ofBijective
    (fun point : Fin 2 × Bool =>
      (⟨point.1.val + if point.2 then 2 else 0, by split <;> omega⟩ : Fin 4))
    (by decide)

@[simp] theorem fin4Schedule_first_zero : fin4Schedule.first 0 = 0 := rfl
@[simp] theorem fin4Schedule_second_zero : fin4Schedule.second 0 = 2 := rfl
@[simp] theorem fin4Schedule_first_one : fin4Schedule.first 1 = 1 := rfl
@[simp] theorem fin4Schedule_second_one : fin4Schedule.second 1 = 3 := rfl
@[simp] theorem fin4Schedule_phase_zero : fin4Schedule.phase 0 = 0 := by
  exact fin4Schedule.phase_first 0

def fin4PivotScale (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    Payoff (Fin 4) := fun player => if player = 0 then (singleton reward 0)⁻¹ else 1

def fin4PivotShift (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    Payoff (Fin 4) := fun player => if player = 0 then 0 else -singleton reward player

/-- Only the pivot column is divided; the other columns are shifted without rescaling. -/
def fin4PivotReward (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  quittingPlayerwiseAffineReward reward (fin4PivotScale reward) (fin4PivotShift reward)

theorem fin4PivotReward_apply
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : {S : Finset (Fin 4) // S.Nonempty}) (player : Fin 4) :
    fin4PivotReward reward coalition player =
      if player = 0 then reward coalition player / singleton reward 0
      else reward coalition player - singleton reward player := by
  unfold fin4PivotReward quittingPlayerwiseAffineReward fin4PivotScale fin4PivotShift
  split_ifs <;> simp [div_eq_mul_inv, mul_comm, sub_eq_add_neg]

theorem fin4PivotScale_pos
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hregion : RawRegion reward fin4Schedule) (player : Fin 4) :
    0 < fin4PivotScale reward player := by
  unfold fin4PivotScale
  split_ifs
  · apply inv_pos.mpr
    linarith [(hregion.own 0).singleton_lower]
  · norm_num

theorem fin4PivotReward_isSinglePivotSingletonTable
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hregion : RawRegion reward fin4Schedule) :
    IsSinglePivotSingletonTable (fin4PivotReward reward) 0 := by
  intro player
  rw [fin4PivotReward_apply]
  split_ifs with hplayer
  · subst player
    change singleton reward 0 / singleton reward 0 = 1
    exact div_self (by linarith [(hregion.own 0).singleton_lower])
  · exact sub_self _

theorem fin4PivotSingleton_nonneg
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hregion : RawRegion reward fin4Schedule) (player : Fin 4) :
    0 ≤ fin4PivotScale reward player * singleton reward player + fin4PivotShift reward player := by
  have h := fin4PivotReward_isSinglePivotSingletonTable reward hregion player
  change _ = _ at h
  change 0 ≤ fin4PivotReward reward (quittingSingletonTerminal player) player
  rw [h]
  split_ifs <;> norm_num

/-- At the initial active pivot phase the sharper bound is `5/3`, not the
coarse all-phase reward bound divided by the smallest singleton. -/
theorem fin4PivotValue_bounds
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hregion : RawRegion reward fin4Schedule) (q : Fin 4 → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap fin4Schedule.partner (singleton reward)
      (partnerReward reward fin4Schedule) (jointReward reward fin4Schedule)
      (quietRows reward fin4Schedule) q player = 0) (player : Fin 4) :
    0 ≤ fin4PivotScale reward player * value reward fin4Schedule q hq 0 player +
      fin4PivotShift reward player ∧
    fin4PivotScale reward player * value reward fin4Schedule q hq 0 player +
      fin4PivotShift reward player ≤ if player = 0 then 5 / 3 else 6 / 5 := by
  have hv := value_bounds_of_selected reward fin4Schedule hregion q hq hinterior hzero 0 player
  have hs := (hregion.own player).singleton_lower
  by_cases hplayer : player = 0
  · subst player
    simp only [fin4PivotScale, fin4PivotShift, ite_true, add_zero]
    have hspos : 0 < singleton reward 0 := by linarith
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hspos.le) (by linarith)
    · rw [← div_eq_inv_mul, div_le_iff₀ hspos]
      have hactive := value_active_eq_selected reward fin4Schedule hregion q hq
        hinterior hzero 0
      rw [fin4Schedule_phase_zero] at hactive
      rw [hactive]
      have hown := hregion.own 0
      have hgap : 0 ≤ jointReward reward fin4Schedule 0 - singleton reward 0 := by
        linarith [hown.joint_lower, hown.singleton_upper]
      have hmul := mul_le_mul_of_nonneg_right
        (hinterior (fin4Schedule.partner 0)).2.le hgap
      unfold activeValue
      nlinarith [hown.joint_upper]
  · simp only [fin4PivotScale, fin4PivotShift, if_neg hplayer, one_mul]
    constructor <;> linarith

end GameTheory.PairedCycle
