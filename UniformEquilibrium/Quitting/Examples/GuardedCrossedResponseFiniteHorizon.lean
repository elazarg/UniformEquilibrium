import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseExactRoots
import UniformEquilibrium.Quitting.Stationary.FiniteHorizonRate

/-! # Explicit horizon regret at the half-ceiling table's displayed root -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

theorem halfCeiling_abs_reward_le
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    |halfCeilingReward terminal who| ≤ 199 / 7 := by
  fin_cases terminal <;> fin_cases who <;>
    norm_num +decide [halfCeilingReward, coalitionCode]

/-- The same exact stationary profile, with no horizon-dependent adjustment,
has regret at most the packet's displayed `4776/(35H)`. -/
theorem halfCeilingRoot_isHorizonNash (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame halfCeilingReward).IsεHorizonNash none horizon
      (4776 / (35 * (horizon : ℝ)))
      (quittingStationaryProfile halfCeilingReward halfCeilingRoot) := by
  have hopponents : ∀ who,
      quittingStationaryFixedOpponentsContinueMass halfCeilingRoot who ≤ 1 - 5 / 12 := by
    intro who
    rw [halfCeilingRoot_deletedSurvival]
    fin_cases who <;> norm_num
  have hnash := isHorizonNash_stationary_of_terminalNash_and_opponentGap
    halfCeilingReward halfCeilingRoot (199 / 7) (5 / 12) (by norm_num) (by norm_num)
      halfCeiling_abs_reward_le hopponents halfCeilingRoot_terminalNash horizon hhorizon
  have hH : (horizon : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hhorizon
  have hconstant :
      2 * (199 / 7 : ℝ) / ((5 / 12) * (horizon : ℝ)) =
        4776 / (35 * (horizon : ℝ)) := by
    field_simp [hH]; ring
  rw [hconstant] at hnash
  exact hnash

end GameTheory.GuardedCrossedResponseExamples
