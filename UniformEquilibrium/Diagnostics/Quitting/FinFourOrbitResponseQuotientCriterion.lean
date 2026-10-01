import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientPlayerOrbits
import UniformEquilibrium.Diagnostics.Quitting.FinFourResponseQuotientCriterion

/-!
# Every reward-automorphism subgroup under original Fin4 no UE

The same original-game contrary hypothesis produces the R0 certificate and
degree +1 for every canonical subgroup-orbit quotient. Blocks and representatives
are constructed by the production orbit adapter, not supplied as favorable data.
-/

noncomputable section

open scoped Classical

namespace GameTheory

open Math.LinearProgramming

/-- Original no UE forces R0 for the orbit quotient of every actual reward symmetry subgroup. -/
theorem finFour_orbitResponseQuotient_isR0_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (group : Subgroup (Equiv.Perm (Fin 4)))
    (hcovariance : ∀ (element : group) terminal who,
      reward (quittingCoalitionEquiv (element : Equiv.Perm (Fin 4)) terminal)
        ((element : Equiv.Perm (Fin 4)) who) = reward terminal who)
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    IsR0Matrix (quittingResponseQuotientMatrix reward
      (quittingPlayerOrbitBlock group) (quittingPlayerOrbitRepresentative group)) :=
  finFour_isR0Matrix_quittingResponseQuotientMatrix_of_no_uniformPayoff reward
    (quittingPlayerOrbitBlock group) (quittingPlayerOrbitRepresentative group)
    (quittingPlayerOrbitBlock_representative group)
    (responseInvariant_of_reward_subgroup_automorphisms reward group hcovariance) hno

/-- The R0 proof and degree-one integer are outputs of the same original no-UE premise. -/
theorem finFour_orbitResponseQuotient_degree_eq_one_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (group : Subgroup (Equiv.Perm (Fin 4)))
    (hcovariance : ∀ (element : group) terminal who,
      reward (quittingCoalitionEquiv (element : Equiv.Perm (Fin 4)) terminal)
        ((element : Equiv.Perm (Fin 4)) who) = reward terminal who)
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ hR0 : IsR0Matrix (quittingResponseQuotientMatrix reward
        (quittingPlayerOrbitBlock group) (quittingPlayerOrbitRepresentative group)),
      r0Degree (quittingResponseQuotientMatrix reward
        (quittingPlayerOrbitBlock group) (quittingPlayerOrbitRepresentative group)) hR0 = 1 :=
  finFour_responseQuotient_r0Degree_eq_one_of_no_uniformPayoff reward
    (quittingPlayerOrbitBlock group) (quittingPlayerOrbitRepresentative group)
    (quittingPlayerOrbitBlock_representative group)
    (responseInvariant_of_reward_subgroup_automorphisms reward group hcovariance) hno

end GameTheory
