/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.Leaves

/-!
# Exhaustive coverage theorem for the Fin4 producer atlas

A four-player hard residual produces one of six source-distinct tagged leaves.
The proof performs the high-tail/low-tail split on one fixed selected-row
family and never reselects the table, minimum point, law, or chronology.
-/

noncomputable section

namespace GameTheory

/-- A hard residual produces one of the six source-distinct tagged leaves.
No completion theorem for any returned leaf is asserted. -/
theorem nonempty_finFourProducerResidual_of_hardResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    Nonempty (FinFourProducerResidual reward bound) := by
  obtain ⟨source⟩ := FinFourMinimumAtomProducer.nonempty_of_hardResidual
    reward bound residual
  by_cases hsingleton : source.atom.terminal.val.card = 1
  · exact ⟨.minimumSingleton source hsingleton⟩
  have hcollision : 1 < source.atom.terminal.val.card := by
    have hpositive : 0 < source.atom.terminal.val.card :=
      Finset.card_pos.mpr source.atom.terminal.property
    omega
  rcases source.nonempty_tailEscape_or_lowTailRow hcollision with hescape | hlow
  · obtain ⟨escape⟩ := hescape
    exact ⟨.tailEscape source escape⟩
  · obtain ⟨low⟩ := hlow
    rcases low.nonempty_leaf with hpurified | hterminal | hcommonHost |
        hcomplementaryPair
    · obtain ⟨purified⟩ := hpurified
      exact ⟨.purifiedSingleton source purified⟩
    · obtain ⟨terminal⟩ := hterminal
      exact ⟨.terminalSingleton source terminal⟩
    · obtain ⟨commonHost⟩ := hcommonHost
      exact ⟨.commonHostMonodromy source commonHost⟩
    · obtain ⟨complementaryPair⟩ := hcomplementaryPair
      exact ⟨.complementaryPairMonodromy source complementaryPair⟩

/-- Global four-player coverage: either a uniform-equilibrium payoff already
exists, or the same reward table produces one of the six tagged leaves. -/
theorem uniformPayoff_or_nonempty_finFourProducerResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      Nonempty (FinFourProducerResidual reward bound) := by
  rcases uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual
      reward hreward with hpayoff | hresidual
  · exact Or.inl hpayoff
  · obtain ⟨residual⟩ := hresidual
    exact Or.inr
      (nonempty_finFourProducerResidual_of_hardResidual reward bound residual)

end GameTheory
