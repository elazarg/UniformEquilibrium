import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterRewardNeighborhood
import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterNearbyOneDate
import UniformEquilibrium.Quitting.Paths.StoppingLawExploitabilityCongruence

/-! # A solved open neighborhood obstructing unchanged-child equilibrium extension

This is a paired floor for actual parent and literal restricted child errors,
together with an internally produced one-date exact terminal equilibrium.
It does not assert a positive parent-only floor or a UE counterexample.
-/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

theorem exists_solved_open_neighborhood_unchanged_child_floor :
    ∃ constant radius : ℝ, 0 < constant ∧ 0 < radius ∧
      ∀ table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      (∀ terminal player, |table terminal player - reward terminal player| < radius) →
      (∀ parent : (quittingGame table).BehaviorProfile, ∀ deleted : Fin 4,
        constant ≤ quittingTerminalExploitability table parent +
          quittingTerminalExploitability (nearbyChildReward table deleted)
            (nearbyRestrictedProfile table deleted parent)) ∧
      ∃ probability : Fin 3 → ℝ,
        (∀ active, 1 / 4 < probability active ∧ probability active < 3 / 4) ∧
        (quittingGame table).IsεAsymptoticNash (quittingTerminalPayoff table) 0
          (nearbyProfile table probability) ∧
        (quittingGame table).IsUniformEquilibriumPayoff none
          (quittingTerminalPayoff table (nearbyProfile table probability)) := by
  obtain ⟨constant, radius, hc, hr, hsmall, hfloor⟩ :=
    exists_open_reward_neighborhood_paired_floor
  refine ⟨constant, radius, hc, hr, ?_⟩
  intro table hclose
  refine ⟨hfloor table hclose, ?_⟩
  obtain ⟨delta, hdelta, hlt, hbound⟩ := exists_reward_distance_lt table hclose
  exact exists_nearby_oneDate_exactTerminalNash_and_uniformPayoff table hdelta
    (hlt.trans_le hsmall) hbound

/-- This corollary applies only when the survivor laws are literally unchanged. -/
theorem parent_floor_of_literal_child_error
    {constant : ℝ}
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hfloor : ∀ parent : (quittingGame table).BehaviorProfile, ∀ deleted : Fin 4,
      constant ≤ quittingTerminalExploitability table parent +
        quittingTerminalExploitability (nearbyChildReward table deleted)
          (nearbyRestrictedProfile table deleted parent))
    (parent : (quittingGame table).BehaviorProfile) (deleted : Fin 4) {epsilon : ℝ}
    (hchild : quittingTerminalExploitability (nearbyChildReward table deleted)
      (nearbyRestrictedProfile table deleted parent) ≤ epsilon) :
    constant - epsilon ≤ quittingTerminalExploitability table parent := by
  linarith [hfloor parent deleted]

/-- ANY supplied child law tuple may be used; the parent must retain that tuple literally. -/
theorem parent_floor_of_unchanged_survivor_laws
    {constant : ℝ}
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hfloor : ∀ parent : (quittingGame table).BehaviorProfile, ∀ deleted : Fin 4,
      constant ≤ quittingTerminalExploitability table parent +
        quittingTerminalExploitability (nearbyChildReward table deleted)
          (nearbyRestrictedProfile table deleted parent))
    (parent : (quittingGame table).BehaviorProfile) (deleted : Fin 4)
    (child : (quittingGame (nearbyChildReward table deleted)).BehaviorProfile) {epsilon : ℝ}
    (hlaws : ∀ who : Fin 3,
      quittingBehaviorStoppingLaw (nearbyChildReward table deleted) (child who) =
        quittingBehaviorStoppingLaw table (parent (deletedEquiv deleted who).1))
    (hchild : quittingTerminalExploitability (nearbyChildReward table deleted) child ≤ epsilon) :
    constant - epsilon ≤ quittingTerminalExploitability table parent := by
  have htuple : quittingBehaviorStoppingLaws (nearbyChildReward table deleted) child =
      quittingBehaviorStoppingLaws (nearbyChildReward table deleted)
        (nearbyRestrictedProfile table deleted parent) := by
    funext who
    simpa [quittingBehaviorStoppingLaws] using hlaws who
  have herror := quittingTerminalExploitability_eq_of_behaviorStoppingLaws_eq
    (nearbyChildReward table deleted) child (nearbyRestrictedProfile table deleted parent) htuple
  rw [herror] at hchild
  exact parent_floor_of_literal_child_error table hfloor parent deleted hchild

end GameTheory.AdaptiveChildCenter
