/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportProjectiveQBarResidual
import UniformEquilibrium.Quitting.Classification.Existence.NormalUniquePersistentNashBellmanSpine

/-!
# Nash--Bellman clocks in the four-player full-support hard residual

The hard residual carries all-player punishment normality and a terminal
exploitability witness.  The normal unique-persistent compiler therefore
excludes every nonsummable marginal of a supplied exact Nash--Bellman spine:
one persistent label gives a singleton uniform payoff, while two persistent
labels force the existing opponent-clock alternative into its uniform-payoff
branch.

This theorem constrains supplied exact spines.  It does not construct a spine
with any prescribed clock behavior and does not resolve the hard residual.
-/

noncomputable section

namespace GameTheory

/-- Every marginal Quit-hazard stream of a supplied exact Nash--Bellman spine
is summable in the four-player full-support hard residual. -/
theorem
    FinFourQuantitativeFullSupportHardResidual.all_marginalQuitHazards_summable
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (value : ℕ → Payoff (Fin 4))
    (roots : ℕ → Fin 4 → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots) :
    ∀ owner, Summable (quittingMarginalQuitHazard roots owner) := by
  intro owner
  by_contra howner
  have hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
    quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
      reward residual.witness.terminalGap_pos
        residual.witness.terminalExploitability
  by_cases hothers : ∀ other, other ≠ owner →
      Summable (quittingMarginalQuitHazard roots other)
  · apply hno
    exact ⟨quittingSoloReward reward owner,
      hspine.isUniformEquilibriumPayoff_soloReward_of_uniquePersistent
        reward value roots owner howner hothers
          (residual.all_punishmentNormal owner)⟩
  · push Not at hothers
    obtain ⟨other, hne, hother⟩ := hothers
    have hpersistent : HasTwoPersistentQuittingMarginals roots :=
      ⟨owner, other, hne.symm, howner, hother⟩
    have hall : ∀ who,
        ¬ Summable (quittingOpponentClockCharge roots who) :=
      (hasTwoPersistentQuittingMarginals_iff_all_opponentClocks roots
        (by norm_num)).1 hpersistent
    rcases uniformEquilibriumPayoff_or_summableClock_of_exactNashBellmanSpine
      reward value roots hspine with hue | ⟨who, hsummable, -⟩
    · exact hno ⟨value 0, hue⟩
    · exact (hall who hsummable).elim

/-- If a bounded four-player table has no uniform-equilibrium payoff, every
marginal Quit-hazard stream of every supplied exact Nash--Bellman spine is
summable. -/
theorem all_marginalQuitHazards_summable_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ S who, |reward S who| ≤ bound)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (value : ℕ → Payoff (Fin 4))
    (roots : ℕ → Fin 4 → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots) :
    ∀ owner, Summable (quittingMarginalQuitHazard roots owner) := by
  obtain ⟨residual⟩ :=
    nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff
      reward hreward hnot
  exact residual.all_marginalQuitHazards_summable value roots hspine

end GameTheory
