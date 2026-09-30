import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseChildLP

/-!
# Exact raw-table robustness of the four unit-table child-LP duals

The actual source reward coordinates may vary freely. For a coordinate error
δ, the four sampled dual columns and objectives change by at most
`36δ`, `4δ`, `254δ`, and `28δ`. Thus every three-player child still fails
the full and positive-singleton-relaxed raw tests throughout the literal
reward ball of radius `1/1000`. No robustness of the half table's zero-column
dual certificates is asserted here.
-/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open scoped BigOperators

theorem unitDualErrorFactor_eq_two_weightSum (outside : Fin 4) :
    unitDualErrorFactor outside = 2 * unitDualWeightSum outside := by
  fin_cases outside <;> norm_num [unitDualErrorFactor, unitDualWeightSum]

/-- The exact printed column error factors come from the actual reward-row bound. -/
theorem abs_unitDual_column_sub_le
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - unitCeilingReward terminal who| ≤ error)
    (outside : Fin 4) (who : RawChild (unitDualChild outside)) :
    |(∑ row, unitDualCoefficient outside row *
        cappedClockExactLPDelta
          (rawChildReward other (unitDualChild outside) ⟨outside, by simp [unitDualChild]⟩)
          (unitDualSample outside row) who) - unitDualColumn outside who.1| ≤
      unitDualErrorFactor outside * error := by
  have hclose' := abs_quittingChildWithOutsiderReward_sub_le
    unitCeilingReward other (· ∉ unitDualChild outside)
    ⟨outside, by simp [unitDualChild]⟩ error hclose
  rw [← unitDual_column_eq outside who]
  calc
    _ ≤ (2 * error) * unitDualWeightSum outside := by
      simpa only [unitDual_weightSum_eq] using
        Maths.FiniteInequality.abs_weightedSum_sub_le (unitDualCoefficient outside)
          (fun row => cappedClockExactLPDelta
            (rawChildReward unitCeilingReward (unitDualChild outside)
              ⟨outside, by simp [unitDualChild]⟩) (unitDualSample outside row) who)
          (fun row => cappedClockExactLPDelta
            (rawChildReward other (unitDualChild outside)
              ⟨outside, by simp [unitDualChild]⟩) (unitDualSample outside row) who)
          (2 * error) (by intro row; fin_cases outside <;> fin_cases row <;>
            norm_num [unitDualCoefficient])
          (fun row => abs_cappedClockExactLPDelta_sub_le _ _ error hclose'
            (unitDualSample outside row) who)
    _ = unitDualErrorFactor outside * error := by
      rw [unitDualErrorFactor_eq_two_weightSum]
      ring

/-- The objective has precisely the same four printed error bounds. -/
theorem abs_unitDual_objective_sub_le
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - unitCeilingReward terminal who| ≤ error)
    (outside : Fin 4) :
    |(∑ row, unitDualCoefficient outside row *
        cappedClockExactLPBase
          (rawChildReward other (unitDualChild outside) ⟨outside, by simp [unitDualChild]⟩)
          (unitDualSample outside row)) - unitDualObjective outside| ≤
      unitDualErrorFactor outside * error := by
  have hclose' := abs_quittingChildWithOutsiderReward_sub_le
    unitCeilingReward other (· ∉ unitDualChild outside)
    ⟨outside, by simp [unitDualChild]⟩ error hclose
  rw [← unitDual_objective_eq outside]
  calc
    _ ≤ (2 * error) * unitDualWeightSum outside := by
      simpa only [unitDual_weightSum_eq] using
        Maths.FiniteInequality.abs_weightedSum_sub_le (unitDualCoefficient outside)
          (fun row => cappedClockExactLPBase
            (rawChildReward unitCeilingReward (unitDualChild outside)
              ⟨outside, by simp [unitDualChild]⟩) (unitDualSample outside row))
          (fun row => cappedClockExactLPBase
            (rawChildReward other (unitDualChild outside)
              ⟨outside, by simp [unitDualChild]⟩) (unitDualSample outside row))
          (2 * error) (by intro row; fin_cases outside <;> fin_cases row <;>
            norm_num [unitDualCoefficient])
          (fun row => abs_cappedClockExactLPBase_sub_le _ _ error hclose'
            (unitDualSample outside row))
    _ = unitDualErrorFactor outside * error := by
      rw [unitDualErrorFactor_eq_two_weightSum]
      ring

/-- The actual raw-table perturbation excludes each permitted relaxed child criterion. -/
theorem unitCeiling_three_player_child_no_certificates_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (herror : error < 1 / 1000)
    (hclose : ∀ terminal who, |other terminal who - unitCeilingReward terminal who| ≤ error)
    (outside : Fin 4) :
    let reward := rawChildReward other (unitDualChild outside)
      ⟨outside, by simp [unitDualChild]⟩
    ¬Nonempty (CappedClockParentRewardCertificate reward) ∧
      ¬Nonempty (CappedClockParentFutureJoinCertificate reward) := by
  have hclose' := abs_quittingChildWithOutsiderReward_sub_le
    unitCeilingReward other (· ∉ unitDualChild outside)
    ⟨outside, by simp [unitDualChild]⟩ error hclose
  have hrelaxed : ¬Nonempty (CappedClockParentFutureJoinCertificate
      (rawChildReward other (unitDualChild outside) ⟨outside, by simp [unitDualChild]⟩)) := by
    apply not_nonempty_cappedClockParentFutureJoinCertificate_of_sampledDual_perturbation
      (rawChildReward unitCeilingReward (unitDualChild outside)
        ⟨outside, by simp [unitDualChild]⟩)
      _ (unitDualSample outside) (by intro row; unfold unitDualSample; split_ifs <;> simp)
      (unitDualCoefficient outside)
      (by intro row; fin_cases outside <;> fin_cases row <;> norm_num [unitDualCoefficient])
      error hclose'
    · intro who
      rw [unitDual_column_eq, unitDual_weightSum_eq]
      fin_cases outside
      all_goals rcases who with ⟨who, hwho⟩
      all_goals fin_cases who
      all_goals norm_num [unitDualChild] at hwho
      all_goals norm_num [unitDualColumn, unitDualWeightSum]
      all_goals linarith
    · rw [unitDual_weightSum_eq, unitDual_objective_eq]
      fin_cases outside <;> norm_num [unitDualWeightSum, unitDualObjective] <;> linarith
  refine ⟨?_, hrelaxed⟩
  rintro ⟨certificate⟩
  exact hrelaxed ⟨{
    weight := certificate.weight
    weight_nonneg := certificate.weight_nonneg
    future_row := certificate.future_row
    join_row := certificate.join_row
  }⟩

/-- Every reward coordinate varies independently throughout the literal full-dimensional ball. -/
theorem unitCeiling_three_player_child_no_certificates_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other unitCeilingReward < 1 / 1000) (outside : Fin 4) :
    let reward := rawChildReward other (unitDualChild outside)
      ⟨outside, by simp [unitDualChild]⟩
    ¬Nonempty (CappedClockParentRewardCertificate reward) ∧
      ¬Nonempty (CappedClockParentFutureJoinCertificate reward) := by
  apply unitCeiling_three_player_child_no_certificates_of_coordinate_error
    other (dist other unitCeilingReward) hclose
  intro terminal who
  simpa only [Real.dist_eq] using
    (dist_le_pi_dist (other terminal) (unitCeilingReward terminal) who).trans
      (dist_le_pi_dist other unitCeilingReward terminal)

end GameTheory.GuardedCrossedResponseExamples
