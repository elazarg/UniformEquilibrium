import UniformEquilibrium.Quitting.Root.PlayerwiseAffineReward

/-! # Playerwise unit normalization of a quitting reward table -/

noncomputable section

namespace GameTheory

variable {ι : Type}

/-- Add a common absorption bonus and normalize each coordinate by its
shifted own singleton reward. -/
def quittingPlayerwiseUnitNormalization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (shift : ℝ) : {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun terminal player =>
    (reward terminal player + shift) /
      (reward (quittingSingletonTerminal player) player + shift)

/-- Positive shift and nonnegative singleton rewards make every normalized
own singleton reward equal to one. -/
theorem quittingPlayerwiseUnitNormalization_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {shift : ℝ} (hshift : 0 < shift)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (player : ι) :
    quittingPlayerwiseUnitNormalization reward shift
      (quittingSingletonTerminal player) player = 1 := by
  unfold quittingPlayerwiseUnitNormalization
  exact div_self (ne_of_gt (add_pos_of_nonneg_of_pos
    (hsingleton player) hshift))

end GameTheory
