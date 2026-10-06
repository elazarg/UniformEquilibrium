import UniformEquilibrium.Quitting.Classification.Existence.MixedSignTripleCoreUniformPayoff
import UniformEquilibrium.Quitting.Classification.MixedSignTripleCorePassivePerturbation
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-! # Original-game weak mixed-sign triple reward closure

Seven passive entries strictify all weak signed gaps simultaneously. The two
equalities remain equalities and the actual computed triple core is unchanged.
Only the strategic weak conclusion is asserted; no weak index claim is made.
-/

noncomputable section

namespace GameTheory

theorem exists_uniformEquilibriumPayoff_of_weakMixedSignTriple_core
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    {first second third : Fin 4}
    (hcore : quittingPremiumCore reward = {first, second, third})
    (hcard : (quittingPremiumCore reward).card = 3)
    (hjoining : HasWeakMixedSignTripleJoining reward first second third) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have htripleCard : ({first, second, third} : Finset (Fin 4)).card = 3 := hcore ▸ hcard
  obtain ⟨hfirstSecond, hfirstThird, hsecondThird⟩ :=
    Finset.card_triple_eq_three_iff.mp htripleCard
  apply exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables
  intro delta hdelta
  let nearby := mixedSignTriplePassivePerturbation reward first second third delta
  refine ⟨nearby, ?_, ?_⟩
  · intro terminal player
    exact (abs_mixedSignTriplePassivePerturbation_sub_le
      reward first second third delta terminal player).trans (by rw [abs_of_pos hdelta])
  · apply exists_uniformEquilibriumPayoff_of_mixedSignTriple_core nearby
    · intro player
      change 0 ≤ mixedSignTriplePassivePerturbation reward first second third delta
        (quittingSingletonTerminal player) player
      rw [mixedSignTriplePassivePerturbation_singleton]
      exact hsingleton player
    · change quittingPremiumCore
        (mixedSignTriplePassivePerturbation reward first second third delta) = _
      rw [mixedSignTriplePassivePerturbation_core]
      exact hcore
    · exact mixedSignTriplePassivePerturbation_strict_of_weak reward
        hfirstSecond hfirstThird hsecondThird hjoining delta hdelta

end GameTheory
