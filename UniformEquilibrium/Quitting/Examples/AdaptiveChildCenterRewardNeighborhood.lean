import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterPairedFloor
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-! # Reward stability of the same-parent literal-child obstruction -/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

/-- The literal deleted table of an arbitrary nearby parent table. -/
def nearbyChildReward
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (deleted : Fin 4) : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3) :=
  quittingRewardReindex (deletedEquiv deleted).symm
    (quittingDeletePlayerReward table deleted)

/-- Reconstruction uses precisely the surviving laws of the supplied parent. -/
def nearbyRestrictedProfile
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (deleted : Fin 4) (parent : (quittingGame table).BehaviorProfile) :
    (quittingGame (nearbyChildReward table deleted)).BehaviorProfile :=
  quittingStoppingLawProfile (nearbyChildReward table deleted)
    (restrictLaws deleted (quittingBehaviorStoppingLaws table parent))

@[simp] theorem nearbyRestrictedProfile_stoppingLaw
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (deleted : Fin 4) (parent : (quittingGame table).BehaviorProfile) (who : Fin 3) :
    quittingBehaviorStoppingLaw (nearbyChildReward table deleted)
        (nearbyRestrictedProfile table deleted parent who) =
      quittingBehaviorStoppingLaw table (parent (deletedEquiv deleted who).1) := by
  simp [nearbyRestrictedProfile, restrictLaws, quittingBehaviorStoppingLaws]

/-- Numerical rewards do not change the literal reconstructed behavior strategies. -/
theorem nearbyRestrictedProfile_eq_center
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (deleted : Fin 4) (parent : (quittingGame table).BehaviorProfile) :
    nearbyRestrictedProfile table deleted parent = restrictedProfileOfParent deleted parent := by
  rfl

theorem nearbyChildReward_close
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {delta : ℝ}
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta)
    (deleted : Fin 4) (terminal : {S : Finset (Fin 3) // S.Nonempty}) (who : Fin 3) :
    |nearbyChildReward table deleted terminal who - childReward deleted terminal who| ≤ delta := by
  exact hclose _ _

/-- Both terms refer to the SAME parent and its literal restriction. -/
theorem nearby_parent_child_floor_of_center_floor
    {floor delta : ℝ}
    (hfloor : ∀ parent : (quittingGame reward).BehaviorProfile, ∀ deleted : Fin 4,
      floor ≤ quittingTerminalExploitability reward parent +
        quittingTerminalExploitability (childReward deleted)
          (restrictedProfileOfParent deleted parent))
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hdelta : 0 ≤ delta)
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta)
    (parent : (quittingGame table).BehaviorProfile) (deleted : Fin 4) :
    floor - 4 * delta ≤ quittingTerminalExploitability table parent +
      quittingTerminalExploitability (nearbyChildReward table deleted)
        (nearbyRestrictedProfile table deleted parent) := by
  have hparent := abs_quittingTerminalExploitability_sub_le_of_reward_close
    table reward parent hdelta hclose
  have hchild := abs_quittingTerminalExploitability_sub_le_of_reward_close
    (nearbyChildReward table deleted) (childReward deleted)
    (nearbyRestrictedProfile table deleted parent) hdelta
    (nearbyChildReward_close table hclose deleted)
  rw [nearbyRestrictedProfile_eq_center] at hchild
  have hsource := hfloor parent deleted
  rw [nearbyRestrictedProfile_eq_center]
  linarith [abs_le.mp hparent, abs_le.mp hchild]

/-- The positive constant and radius precede every nearby table, parent, and deletion. -/
theorem exists_nearby_parent_child_exploitability_floor :
    ∃ constant radius : ℝ, 0 < constant ∧ 0 < radius ∧ radius ≤ 1 / 8 ∧
      ∀ table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      ∀ delta : ℝ, 0 ≤ delta → delta < radius →
      (∀ terminal player, |table terminal player - reward terminal player| ≤ delta) →
      ∀ parent : (quittingGame table).BehaviorProfile, ∀ deleted : Fin 4,
        constant ≤ quittingTerminalExploitability table parent +
          quittingTerminalExploitability (nearbyChildReward table deleted)
            (nearbyRestrictedProfile table deleted parent) := by
  obtain ⟨floor, hpositive, hfloor⟩ := exists_center_parent_child_exploitability_floor
  refine ⟨floor / 2, min (floor / 8) (1 / 8), by positivity,
    lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  intro table delta hdelta hsmall hclose parent deleted
  have hscale : delta < floor / 8 := hsmall.trans_le (min_le_left _ _)
  have hbound := nearby_parent_child_floor_of_center_floor hfloor table hdelta hclose parent deleted
  linarith

/-- Strict coordinate closeness has a single finite nonnegative distance below the radius. -/
theorem exists_reward_distance_lt
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {radius : ℝ}
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| < radius) :
    ∃ delta : ℝ, 0 ≤ delta ∧ delta < radius ∧
      ∀ terminal player, |table terminal player - reward terminal player| ≤ delta := by
  classical
  let distance := fun point : {S : Finset (Fin 4) // S.Nonempty} × Fin 4 =>
    |table point.1 point.2 - reward point.1 point.2|
  obtain ⟨point, _, hmax⟩ := Finset.exists_max_image Finset.univ distance
    ⟨(quittingSingletonTerminal (0 : Fin 4), (0 : Fin 4)), Finset.mem_univ _⟩
  refine ⟨distance point, abs_nonneg _, hclose point.1 point.2, ?_⟩
  intro terminal player
  exact hmax (terminal, player) (Finset.mem_univ _)

theorem exists_open_reward_neighborhood_paired_floor :
    ∃ constant radius : ℝ, 0 < constant ∧ 0 < radius ∧ radius ≤ 1 / 8 ∧
      ∀ table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      (∀ terminal player, |table terminal player - reward terminal player| < radius) →
      ∀ parent : (quittingGame table).BehaviorProfile, ∀ deleted : Fin 4,
        constant ≤ quittingTerminalExploitability table parent +
          quittingTerminalExploitability (nearbyChildReward table deleted)
            (nearbyRestrictedProfile table deleted parent) := by
  obtain ⟨constant, radius, hc, hr, hsmall, hfloor⟩ :=
    exists_nearby_parent_child_exploitability_floor
  refine ⟨constant, radius, hc, hr, hsmall, ?_⟩
  intro table hclose parent deleted
  obtain ⟨delta, hdelta, hlt, hbound⟩ := exists_reward_distance_lt table hclose
  exact hfloor table delta hdelta hlt hbound parent deleted

end GameTheory.AdaptiveChildCenter
