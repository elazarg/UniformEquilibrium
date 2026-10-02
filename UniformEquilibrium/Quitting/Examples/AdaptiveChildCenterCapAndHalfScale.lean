import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterRewardNeighborhood

/-! # Literal center caps and a bounded common scaling of the paired floor

The center has zero parent-only exploitability. Its positive obstruction is
the paired parent/unchanged-child floor, which survives common scaling.
-/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

theorem profile_exploitability_zero :
    quittingTerminalExploitability reward profile = 0 := by
  apply le_antisymm
  · exact quittingTerminalExploitability_le_of_isεAsymptoticNash reward profile
      (le_refl 0) profile_exactTerminalNash
  · exact quittingTerminalExploitability_nonneg reward profile

/-- The cap ranges over ALL unilateral behavioral replacements. -/
theorem profile_fullCap_eq_target :
    quittingContinuationBestResponse reward profile = target := by
  funext who
  have hlower := quittingTerminalDeviationDebt_nonneg reward profile who
  have hupper := quittingTerminalDeviationDebt_le_exploitability reward profile who
  rw [profile_exploitability_zero] at hupper
  unfold quittingTerminalDeviationDebt at hlower hupper
  rw [profile_terminalPayoff] at hlower hupper
  change quittingContinuationBestResponseValue reward profile who = target who
  linarith

/-- No positive global parent gap is asserted by the paired-floor theorem. -/
theorem center_exploitabilityInf_zero :
    quittingTerminalExploitabilityInf reward = 0 := by
  apply le_antisymm
  · exact (quittingTerminalExploitabilityInf_le reward profile).trans
      (le_of_eq profile_exploitability_zero)
  · unfold quittingTerminalExploitabilityInf
    apply le_csInf (Set.range_nonempty _)
    rintro value ⟨parent, rfl⟩
    exact quittingTerminalExploitability_nonneg reward parent

def halfReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  scaleQuittingReward (1 / 2) reward

theorem halfReward_abs_le_one
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    |halfReward terminal who| ≤ 1 := by
  change |(1 / 2 : ℝ) * reward terminal who| ≤ 1
  rw [abs_mul]
  norm_num
  linarith [reward_abs_le_two terminal who]

theorem halfReward_mem_Icc
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    halfReward terminal who ∈ Set.Icc (-1) 1 :=
  abs_le.mp (halfReward_abs_le_one terminal who)

theorem halfReward_never_payoff_zero (who : Fin 4) :
    quittingTerminalPayoff halfReward (quittingAlwaysContinueProfile halfReward) who = 0 :=
  quittingTerminalPayoff_quittingAlwaysContinue halfReward who

theorem halfReward_profile_terminalPayoff :
    quittingTerminalPayoff halfReward profile = fun who => (1 / 2 : ℝ) * target who := by
  funext who
  exact (quittingTerminalPayoff_scaleQuittingReward (1 / 2) reward profile who).trans
    (congrArg (fun value : ℝ => (1 / 2 : ℝ) * value)
      (congrFun profile_terminalPayoff who))

theorem halfReward_profile_exploitability_zero :
    quittingTerminalExploitability halfReward profile = 0 := by
  change quittingTerminalExploitability (scaleQuittingReward (1 / 2) reward) profile = 0
  rw [quittingTerminalExploitability_scaleQuittingReward (by norm_num : (0 : ℝ) ≤ 1 / 2),
    profile_exploitability_zero, mul_zero]

theorem halfReward_exploitabilityInf_zero :
    quittingTerminalExploitabilityInf halfReward = 0 := by
  change quittingTerminalExploitabilityInf (scaleQuittingReward (1 / 2) reward) = 0
  rw [quittingTerminalExploitabilityInf_scaleQuittingReward
    (by norm_num : (0 : ℝ) ≤ 1 / 2), center_exploitabilityInf_zero, mul_zero]

theorem halfReward_target_isUniformEquilibriumPayoff :
    (quittingGame halfReward).IsUniformEquilibriumPayoff none
      (fun who => (1 / 2 : ℝ) * target who) := by
  rw [← halfReward_profile_terminalPayoff]
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact halfReward profile
  exact isεAsymptoticNash_of_quittingTerminalExploitability_le (reward := halfReward) profile
    (le_of_eq halfReward_profile_exploitability_zero)

/-- The scalar is fixed before EVERY actual parent and EVERY omitted player. -/
theorem exists_halfReward_parent_child_exploitability_floor :
    ∃ floor : ℝ, 0 < floor ∧
      ∀ parent : (quittingGame halfReward).BehaviorProfile, ∀ deleted : Fin 4,
        floor ≤ quittingTerminalExploitability halfReward parent +
          quittingTerminalExploitability (nearbyChildReward halfReward deleted)
            (nearbyRestrictedProfile halfReward deleted parent) := by
  obtain ⟨floor, hpositive, hfloor⟩ := exists_center_parent_child_exploitability_floor
  refine ⟨floor / 2, by positivity, ?_⟩
  intro parent deleted
  have hchild : nearbyChildReward halfReward deleted =
      scaleQuittingReward (1 / 2) (childReward deleted) := rfl
  have hparent := quittingTerminalExploitability_scaleQuittingReward
    (by norm_num : (0 : ℝ) ≤ 1 / 2) reward parent
  change quittingTerminalExploitability halfReward parent =
    (1 / 2 : ℝ) * quittingTerminalExploitability reward parent at hparent
  rw [hchild, nearbyRestrictedProfile_eq_center, hparent,
    quittingTerminalExploitability_scaleQuittingReward (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  linarith [hfloor parent deleted]

end GameTheory.AdaptiveChildCenter
