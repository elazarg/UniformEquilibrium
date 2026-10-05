import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness
import Mathlib.Tactic.Linarith

/-! # A common positive reward scale puts every literal entry strictly inside the unit cube -/

namespace GameTheory

variable {ι : Type} [Fintype ι]

/-- The scale is constructed from the canonical finite reward bound.
This only bounds the table; all payoff/eta scaling semantics remain owned by
TerminalExploitabilityRewardRobustness. No affine payoff shift is used. -/
theorem exists_strictUnit_scaleQuittingReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ scale : ℝ, 0 < scale ∧
      ∀ terminal player, |scaleQuittingReward scale reward terminal player| < 1 := by
  let denominator := quittingRewardBound reward + 1
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    linarith [quittingRewardBound_nonneg reward]
  have hscale : 0 < 1 / denominator := one_div_pos.mpr hdenominator
  refine ⟨1 / denominator, hscale, ?_⟩
  intro terminal player
  rw [scaleQuittingReward_apply, abs_mul, abs_of_pos hscale]
  rw [div_mul_eq_mul_div₀, one_mul]
  apply (div_lt_one hdenominator).mpr
  dsimp [denominator]
  linarith [abs_reward_le_quittingRewardBound reward terminal player]

end GameTheory
