/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.PassivePlayerPaddingCanonical

/-!
# Existence consequence of passive-player padding

The quantitative gap theorem immediately propagates nonexistence of a
uniform-equilibrium payoff through every nonempty finite padding block.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {I J : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

/-- Failure of uniform-equilibrium-payoff existence propagates through a
passive padding block under the same interval hypotheses as the quantitative
theorem. -/
theorem not_exists_uniformEquilibriumPayoff_passivePlayerPadding
    [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (lower upper : I → ℝ) {penalty width : ℝ}
    (hpenalty : 0 < penalty) (hwidth : 0 ≤ width)
    (hlower : ∀ who, lower who ≤ 0)
    (hupper : ∀ who, 0 ≤ upper who)
    (hreward : ∀ terminal who,
      reward terminal who ∈ Set.Icc (lower who) (upper who))
    (hoscillation : ∀ who, upper who - lower who ≤ width)
    (hno : ¬ ∃ payoff : Payoff I,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ¬ ∃ payoff : Payoff (I ⊕ J),
      (quittingGame (quittingPassivePaddingReward
        (J := J) reward upper penalty)).IsUniformEquilibriumPayoff
          none payoff := by
  obtain ⟨gap, hgap, hexploit⟩ :=
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).mp hno
  have hpadded := @HasTerminalExploitabilityGap.passivePlayerPadding
    I J _ _ _ _ _ reward lower upper penalty width gap
    hpenalty hwidth hlower hupper hreward hoscillation hexploit
  have hplayers : 0 < (Fintype.card J : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J)
  have hdenom : 0 < penalty + (Fintype.card J : ℝ) * width := by
    positivity
  have htransported :
      0 < penalty / (penalty + (Fintype.card J : ℝ) * width) * gap := by
    positivity
  exact quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
    _ htransported hpadded

/-- Canonical-extrema form of upward nonexistence under passive padding. -/
theorem not_exists_uniformEquilibriumPayoff_passivePlayerPadding_canonical
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty : ℝ} (hpenalty : 0 < penalty)
    (hno : ¬ ∃ payoff : Payoff I,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ¬ ∃ payoff : Payoff (I ⊕ J),
      (quittingGame (quittingPassivePaddingReward
        (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty))
        |>.IsUniformEquilibriumPayoff none payoff := by
  exact @not_exists_uniformEquilibriumPayoff_passivePlayerPadding
    I J _ _ _ _ _ reward
    (quittingPassivePaddingLowerEndpoint reward)
    (quittingPassivePaddingUpperEndpoint reward)
    penalty (quittingPassivePaddingWidth reward)
    hpenalty (quittingPassivePaddingWidth_nonneg reward)
    (quittingPassivePaddingLowerEndpoint_nonpos reward)
    (quittingPassivePaddingUpperEndpoint_nonneg reward)
    (quittingPassivePaddingReward_mem_canonicalInterval reward)
    (quittingPassivePaddingCoordinateWidth_le_width reward) hno

end GameTheory
