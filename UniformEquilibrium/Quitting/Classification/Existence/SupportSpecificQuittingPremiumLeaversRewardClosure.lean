import UniformEquilibrium.Quitting.Classification.Existence.SupportSpecificQuittingPremiumLeaversUniformPayoff
import UniformEquilibrium.Quitting.Classification.PassiveQuittingRewardPerturbation
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-! # Weak support-specific raw comparisons by all-passive reward closure

Every positive all-passive perturbation is a strict table with the same
participant data, traps, and maximal protected set. The canonical actual-game
reward-closure theorem supplies one fixed original target. No weak analytic
potential exclusion or supplied strategic witness is asserted.
-/

noncomputable section

namespace GameTheory

theorem exists_uniformEquilibriumPayoff_of_supportSpecific_weakLeave
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (protectedPlayers : Finset (Fin 4))
    (hpremiums : HasProtectedParticipantPremiums reward protectedPlayers)
    (hleavers : HasSupportSpecificQuittingLeavers reward protectedPlayers (· ≤ ·)) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables
  intro delta hdelta
  let nearby := passiveQuittingRewardPerturbation reward delta
  refine ⟨nearby, ?_, ?_⟩
  · intro terminal player
    exact (abs_passiveQuittingRewardPerturbation_sub_le reward delta terminal player).trans
      (by rw [abs_of_pos hdelta])
  · apply exists_uniformEquilibriumPayoff_of_supportSpecific_strictLeave nearby
      (fun player => by
        change 0 ≤ passiveQuittingRewardPerturbation reward delta
          (quittingSingletonTerminal player) player
        rw [passiveQuittingRewardPerturbation_singleton]
        exact hsingleton player) protectedPlayers
    · exact (passiveQuittingRewardPerturbation_protectedPremiums_iff
        reward delta protectedPlayers).2 hpremiums
    · exact passiveQuittingRewardPerturbation_strictLeavers_of_weakLeavers
        reward protectedPlayers hleavers delta hdelta

theorem exists_uniformEquilibriumPayoff_of_maximalProtectedPlayers_weakLeave
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (hleavers : HasSupportSpecificQuittingLeavers reward
      (quittingMaximalProtectedPlayers reward) (· ≤ ·)) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_supportSpecific_weakLeave reward hsingleton
    (quittingMaximalProtectedPlayers reward)
    ((hasProtectedParticipantPremiums_iff_subset_maximalProtectedPlayers reward
      (quittingMaximalProtectedPlayers reward)).2 Finset.Subset.rfl) hleavers

end GameTheory
