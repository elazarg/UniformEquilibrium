import UniformEquilibrium.Quitting.Root.PlayerwiseAffineReward

/-! # Single-pivot terminal normalization with zero Never payoff -/

noncomputable section

namespace GameTheory

variable {ι : Type} [DecidableEq ι]

/-- Remove the own singleton from every column except the selected pivot. -/
def quittingSinglePivotOffset
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) : Payoff ι :=
  fun who ↦ if who = pivot then 0 else (reward (quittingSingletonTerminal who) who)

/-- Normalize only absorbing rewards; the quitting game's Never payoff stays zero. -/
def quittingSinglePivotNormalizedReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun terminal who ↦ (reward terminal who - quittingSinglePivotOffset reward pivot who) /
    (reward (quittingSingletonTerminal pivot) pivot)

@[simp] theorem quittingSinglePivotOffset_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) :
    quittingSinglePivotOffset reward pivot pivot = 0 := by
  simp [quittingSinglePivotOffset]

theorem quittingSinglePivotOffset_of_ne
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {pivot who : ι}
    (hne : who ≠ pivot) :
    quittingSinglePivotOffset reward pivot who = (reward (quittingSingletonTerminal who) who) := by
  simp [quittingSinglePivotOffset, hne]

/-- The new own-singleton vector is exactly the pivot unit vector. -/
theorem quittingSoloReward_singlePivotNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot who : ι)
    (hpivot : (reward (quittingSingletonTerminal pivot) pivot) ≠ 0) :
    quittingSinglePivotNormalizedReward reward pivot (quittingSingletonTerminal who) who =
      if who = pivot then 1 else 0 := by
  change (reward (quittingSingletonTerminal who) who -
    quittingSinglePivotOffset reward pivot who) /
    (reward (quittingSingletonTerminal pivot) pivot) = _
  by_cases hwho : who = pivot
  · subst who
    simp [hpivot]
  · simp [quittingSinglePivotOffset_of_ne reward hwho, hwho]

theorem abs_quittingSinglePivotOffset_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot who : ι) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingSinglePivotOffset reward pivot who| ≤ bound := by
  have hsolo : |(reward (quittingSingletonTerminal who) who)| ≤ bound :=
    hreward (quittingSingletonTerminal who) who
  by_cases hwho : who = pivot
  · simpa [quittingSinglePivotOffset, hwho] using (abs_nonneg _).trans hsolo
  · simpa [quittingSinglePivotOffset, hwho] using hsolo

/-- Normalization need not preserve a unit reward box: its direct bound is
twice the original bound divided by the positive pivot singleton. -/
theorem abs_quittingSinglePivotNormalizedReward_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpivot : 0 < (reward (quittingSingletonTerminal pivot) pivot))
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) :
    |quittingSinglePivotNormalizedReward reward pivot terminal who| ≤
      2 * bound / (reward (quittingSingletonTerminal pivot) pivot) := by
  unfold quittingSinglePivotNormalizedReward
  rw [abs_div, abs_of_pos hpivot]
  apply div_le_div_of_nonneg_right _ hpivot.le
  exact (abs_sub _ _).trans (by
    have h := abs_quittingSinglePivotOffset_le reward pivot who hreward
    linarith [hreward terminal who])

/-- The terminal table uses the existing playerwise affine chart, without
changing its zero Never payoff. -/
theorem quittingSinglePivotNormalizedReward_eq_playerwiseAffine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) :
    quittingSinglePivotNormalizedReward reward pivot =
      quittingPlayerwiseAffineReward reward
        (fun _ ↦ 1 / (reward (quittingSingletonTerminal pivot) pivot))
        (fun who ↦ -quittingSinglePivotOffset reward pivot who /
          (reward (quittingSingletonTerminal pivot) pivot)) := by
  funext terminal who
  unfold quittingSinglePivotNormalizedReward quittingPlayerwiseAffineReward
  ring

end GameTheory
