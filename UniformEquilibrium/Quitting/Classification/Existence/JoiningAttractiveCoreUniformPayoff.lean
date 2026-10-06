import UniformEquilibrium.Quitting.Classification.JoiningAttractiveCoreSelectedReturn
import UniformEquilibrium.Quitting.Classification.Existence.SelectedSingletonSublevelReturnUniformPayoff

/-! # Actual uniform payoffs from a joining-attractive greatest triple core

The literal reward-only insertion tests supply selected return internally.
A pure-core exact root instead supplies its canonical sure-exit payoff.
Only own singleton rewards are nonnegative; participant premiums may be signed.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

theorem exists_uniformEquilibriumPayoff_of_joiningAttractive_core
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (hcard : (quittingPremiumCore reward).card = 3)
    (hattractive : HasStrictJoiningAttractivePremiumCore reward) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  classical
  by_cases hpure : ∃ tail : Payoff (Fin 4), IsεQuittingRootNash reward tail 0
      (quittingPureSetRoot (quittingPremiumCore reward))
  · obtain ⟨tail, hnash⟩ := hpure
    exact ⟨_, isUniformEquilibriumPayoff_setReward_of_pureSetNash reward tail
      (quittingPremiumCore reward) (by omega) hnash⟩
  · apply exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn reward hsingleton
    apply hasBoxedSelectedSingletonSublevelReturn_of_joiningAttractive_core
      reward hattractive hcard
    intro tail hnash
    exact hpure ⟨tail, hnash⟩

end GameTheory
