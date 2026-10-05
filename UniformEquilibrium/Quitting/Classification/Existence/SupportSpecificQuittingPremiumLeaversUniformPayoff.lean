import UniformEquilibrium.Quitting.Classification.SupportSpecificQuittingPremiumLeaversSmoothDrift
import UniformEquilibrium.Quitting.Classification.Existence.BoundaryDifferentiablePotentialUniformPayoff

/-! # Four-player uniform payoffs from strict support-specific raw leavers

The input is only the original reward table and finite protected/leaver tests.
The polynomial obstruction and all-zero-singleton branch are supplied by the
canonical actual-game consumer. No strategy or favorable potential is an input.
-/

noncomputable section

namespace GameTheory

theorem exists_uniformEquilibriumPayoff_of_supportSpecific_strictLeave
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (protectedPlayers : Finset (Fin 4))
    (hpremiums : HasProtectedParticipantPremiums reward protectedPlayers)
    (hleavers : HasSupportSpecificQuittingLeavers reward protectedPlayers (· < ·)) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_continuous_boundaryDifferentiable_potential_exclusion
    reward hsingleton
  intro potential hcontinuous hdiff
  exact not_isQuittingFullExactRootPotential_of_supportSpecific_strictLeave reward
    protectedPlayers hpremiums hleavers (M := quittingRewardBound reward)
    (bound := quittingRewardBound reward + 2) (abs_reward_le_quittingRewardBound reward)
    (by linarith) potential hcontinuous.continuousOn hdiff

/-- The maximal-protected-set test supplies its participant floor internally.
Its separately proved nonempty-admissible-set equivalence retains the packet's
explicit nonempty quantifier; this stronger consumer also allows a trap-free empty set. -/
theorem exists_uniformEquilibriumPayoff_of_maximalProtectedPlayers_strictLeave
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (hleavers : HasSupportSpecificQuittingLeavers reward
      (quittingMaximalProtectedPlayers reward) (· < ·)) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_supportSpecific_strictLeave reward hsingleton
    (quittingMaximalProtectedPlayers reward)
    ((hasProtectedParticipantPremiums_iff_subset_maximalProtectedPlayers reward
      (quittingMaximalProtectedPlayers reward)).2 Finset.Subset.rfl) hleavers

end GameTheory
