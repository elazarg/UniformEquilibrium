import UniformEquilibrium.Quitting.Examples.AdaptiveChildEquilibriumExtensionNoGo

/-! # Internally produced nearby floors for arbitrary unchanged child equilibria -/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

/-- No floor, radius, child payoff target, calendar, or favorable face is an input. -/
theorem exists_nearby_parent_floor_of_unchanged_child_terminalNash :
    ∃ constant radius : ℝ, 0 < constant ∧ 0 < radius ∧
      ∀ table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      (∀ terminal player, |table terminal player - reward terminal player| < radius) →
      ∀ parent : (quittingGame table).BehaviorProfile, ∀ deleted : Fin 4,
      ∀ child : (quittingGame (nearbyChildReward table deleted)).BehaviorProfile,
      ∀ epsilon : ℝ, 0 ≤ epsilon →
      (quittingGame (nearbyChildReward table deleted)).IsεAsymptoticNash
        (quittingTerminalPayoff (nearbyChildReward table deleted)) epsilon child →
      (∀ who : Fin 3,
        quittingBehaviorStoppingLaw (nearbyChildReward table deleted) (child who) =
          quittingBehaviorStoppingLaw table (parent (deletedEquiv deleted who).1)) →
      constant - epsilon ≤ quittingTerminalExploitability table parent ∧
        (epsilon ≤ constant / 2 →
          constant / 2 ≤ quittingTerminalExploitability table parent) := by
  obtain ⟨constant, radius, hc, hr, hsource⟩ :=
    exists_solved_open_neighborhood_unchanged_child_floor
  refine ⟨constant, radius, hc, hr, ?_⟩
  intro table hclose parent deleted child epsilon hepsilon hnash hlaws
  have hchild := quittingTerminalExploitability_le_of_isεAsymptoticNash
    (nearbyChildReward table deleted) child hepsilon hnash
  have hparent := parent_floor_of_unchanged_survivor_laws table
    (hsource table hclose).1 parent deleted child hlaws hchild
  exact ⟨hparent, fun hsmall => by linarith⟩

/-- The printed fixed half-floor, for every nearby table and every unchanged child. -/
theorem exists_nearby_half_parent_floor_of_unchanged_child_terminalNash :
    ∃ constant radius : ℝ, 0 < constant ∧ 0 < radius ∧
      ∀ table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      (∀ terminal player, |table terminal player - reward terminal player| < radius) →
      ∀ parent : (quittingGame table).BehaviorProfile, ∀ deleted : Fin 4,
      ∀ child : (quittingGame (nearbyChildReward table deleted)).BehaviorProfile,
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ constant / 2 →
      (quittingGame (nearbyChildReward table deleted)).IsεAsymptoticNash
        (quittingTerminalPayoff (nearbyChildReward table deleted)) epsilon child →
      (∀ who : Fin 3,
        quittingBehaviorStoppingLaw (nearbyChildReward table deleted) (child who) =
          quittingBehaviorStoppingLaw table (parent (deletedEquiv deleted who).1)) →
      constant / 2 ≤ quittingTerminalExploitability table parent := by
  obtain ⟨constant, radius, hc, hr, hsource⟩ :=
    exists_nearby_parent_floor_of_unchanged_child_terminalNash
  exact ⟨constant, radius, hc, hr, fun table hclose parent deleted child epsilon
    hepsilon hsmall hnash hlaws =>
      (hsource table hclose parent deleted child epsilon hepsilon hnash hlaws).2 hsmall⟩

end GameTheory.AdaptiveChildCenter
