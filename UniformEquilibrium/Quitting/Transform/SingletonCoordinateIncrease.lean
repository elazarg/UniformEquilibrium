import UniformEquilibrium.Quitting.Terminal.TerminalPayoffRewardOrder

/-! # Increasing one own-singleton payoff coordinate -/

noncomputable section

namespace GameTheory

variable {ι : Type} [DecidableEq ι]

/-- Increase only the selected player's own singleton payoff. -/
def quittingSingletonCoordinateIncrease
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pivot : ι) (delta : ℝ) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun terminal who => reward terminal who +
    if terminal = quittingSingletonTerminal pivot ∧ who = pivot then delta else 0

@[simp] theorem quittingSingletonCoordinateIncrease_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) (delta : ℝ) :
    quittingSingletonCoordinateIncrease reward pivot delta
      (quittingSingletonTerminal pivot) pivot =
        reward (quittingSingletonTerminal pivot) pivot + delta := by
  simp [quittingSingletonCoordinateIncrease]

/-- The perturbation is nonnegative and uniformly at most its amplitude. -/
theorem quittingSingletonCoordinateIncrease_le_and_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pivot : ι) {delta : ℝ} (hdelta : 0 ≤ delta) :
    (∀ terminal who, reward terminal who ≤
      quittingSingletonCoordinateIncrease reward pivot delta terminal who) ∧
    (∀ terminal who,
      |quittingSingletonCoordinateIncrease reward pivot delta terminal who -
        reward terminal who| ≤ delta) := by
  constructor
  · intro terminal who
    unfold quittingSingletonCoordinateIncrease
    split_ifs <;> linarith
  · intro terminal who
    unfold quittingSingletonCoordinateIncrease
    split_ifs
    · simp only [add_sub_cancel_left, abs_of_nonneg hdelta, le_refl]
    · simpa using hdelta

end GameTheory
