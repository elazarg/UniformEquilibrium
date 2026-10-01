import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseExactRoots

/-!
# The literal half-ceiling payoff exceeds every singleton benchmark

These are consequences of the actual terminal Nash profile and its fixed
uniform-equilibrium target, not claims about all profiles or all payoffs.
-/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

/-- Every coordinate of the literal fixed target strictly exceeds its own singleton. -/
theorem halfCeilingValue_strictly_above_singleton (who : Fin 4) :
    halfCeilingReward ⟨{who}, Finset.singleton_nonempty who⟩ who <
      halfCeilingValue who := by
  fin_cases who <;> norm_num +decide [halfCeilingReward, coalitionCode, halfCeilingValue]

/-- The strict inequalities hold for the actual stationary terminal payoff. -/
theorem halfCeilingRoot_terminalPayoff_strictly_above_singleton (who : Fin 4) :
    halfCeilingReward ⟨{who}, Finset.singleton_nonempty who⟩ who <
      quittingTerminalPayoff halfCeilingReward
        (quittingStationaryProfile halfCeilingReward halfCeilingRoot) who := by
  rw [halfCeilingRoot_terminalPayoff]
  exact halfCeilingValue_strictly_above_singleton who

/-- Every nonzero nonnegative weighting has a strictly positive singleton surplus. -/
theorem halfCeilingValue_weighted_strictly_above_singleton
    (weights : Fin 4 → ℝ) (hnonnegative : ∀ who, 0 ≤ weights who)
    (hnonzero : weights ≠ 0) :
    (∑ who, weights who * halfCeilingReward ⟨{who}, Finset.singleton_nonempty who⟩ who) <
      ∑ who, weights who * halfCeilingValue who := by
  have hpositive : ∃ who, 0 < weights who := by
    by_contra hnone
    apply hnonzero
    funext who
    exact le_antisymm (le_of_not_gt (fun h => hnone ⟨who, h⟩)) (hnonnegative who)
  obtain ⟨who, hwho⟩ := hpositive
  apply Finset.sum_lt_sum
  · intro player _
    exact mul_le_mul_of_nonneg_left
      (halfCeilingValue_strictly_above_singleton player).le (hnonnegative player)
  · exact ⟨who, Finset.mem_univ who,
      mul_lt_mul_of_pos_left (halfCeilingValue_strictly_above_singleton who) hwho⟩

/-- The same nonzero weighted surplus is attained by the actual terminal Nash root. -/
theorem halfCeilingRoot_terminalPayoff_weighted_strictly_above_singleton
    (weights : Fin 4 → ℝ) (hnonnegative : ∀ who, 0 ≤ weights who)
    (hnonzero : weights ≠ 0) :
    (∑ who, weights who * halfCeilingReward ⟨{who}, Finset.singleton_nonempty who⟩ who) <
      ∑ who, weights who * quittingTerminalPayoff halfCeilingReward
        (quittingStationaryProfile halfCeilingReward halfCeilingRoot) who := by
  rw [halfCeilingRoot_terminalPayoff]
  exact halfCeilingValue_weighted_strictly_above_singleton weights hnonnegative hnonzero

/-- A universal singleton-coordinate exclusion cannot hold even for exact terminal Nash. -/
theorem halfCeiling_not_terminalNash_singleton_exclusion :
    ¬∀ profile, (quittingGame halfCeilingReward).IsεAsymptoticNash
        (quittingTerminalPayoff halfCeilingReward) 0 profile →
      ∃ who, quittingTerminalPayoff halfCeilingReward profile who ≤
        halfCeilingReward ⟨{who}, Finset.singleton_nonempty who⟩ who := by
  intro hexclusion
  obtain ⟨who, hwho⟩ := hexclusion
    (quittingStationaryProfile halfCeilingReward halfCeilingRoot) halfCeilingRoot_terminalNash
  exact (not_le_of_gt (halfCeilingRoot_terminalPayoff_strictly_above_singleton who)) hwho

/-- For any specified nonzero nonnegative weights, the analogous terminal exclusion fails. -/
theorem halfCeiling_not_terminalNash_weighted_singleton_exclusion
    (weights : Fin 4 → ℝ) (hnonnegative : ∀ who, 0 ≤ weights who)
    (hnonzero : weights ≠ 0) :
    ¬∀ profile, (quittingGame halfCeilingReward).IsεAsymptoticNash
        (quittingTerminalPayoff halfCeilingReward) 0 profile →
      (∑ who, weights who * quittingTerminalPayoff halfCeilingReward profile who) ≤
        ∑ who, weights who * halfCeilingReward ⟨{who}, Finset.singleton_nonempty who⟩ who := by
  intro hexclusion
  exact (not_le_of_gt
    (halfCeilingRoot_terminalPayoff_weighted_strictly_above_singleton
      weights hnonnegative hnonzero))
    (hexclusion (quittingStationaryProfile halfCeilingReward halfCeilingRoot)
      halfCeilingRoot_terminalNash)

/-- The counterexample also supplies one fixed uniform-equilibrium target with all surpluses. -/
theorem halfCeiling_exists_uniformPayoff_strictly_above_singletons :
    ∃ value : Payoff (Fin 4),
      (quittingGame halfCeilingReward).IsUniformEquilibriumPayoff none value ∧
      (∀ who, halfCeilingReward ⟨{who}, Finset.singleton_nonempty who⟩ who < value who) ∧
      ∀ weights : Fin 4 → ℝ, (∀ who, 0 ≤ weights who) → weights ≠ 0 →
        (∑ who, weights who * halfCeilingReward ⟨{who}, Finset.singleton_nonempty who⟩ who) <
          ∑ who, weights who * value who :=
  ⟨halfCeilingValue, halfCeilingValue_uniformPayoff, halfCeilingValue_strictly_above_singleton,
    halfCeilingValue_weighted_strictly_above_singleton⟩

end GameTheory.GuardedCrossedResponseExamples
