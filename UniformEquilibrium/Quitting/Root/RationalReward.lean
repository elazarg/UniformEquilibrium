import UniformEquilibrium.ProofView.Basic
import Mathlib.Data.Finset.Basic

/-! # Rational terminal reward tables for finite quitting games -/

namespace GameTheory

variable {players : ℕ}

/-- A rational terminal reward table for a finite quitting game. -/
abbrev RationalQuittingReward (players : ℕ) :=
  {S : Finset (Fin players) // S.Nonempty} → Fin players → ℚ

/-- Compile a rational terminal table to the real quitting-game semantics. -/
def rationalQuittingRewardToReal
    (reward : RationalQuittingReward players) :
    {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players) :=
  fun terminal who => (reward terminal who : ℝ)

end GameTheory
