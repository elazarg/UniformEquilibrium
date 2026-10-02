import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterCapAndHalfScale
import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterNearbyOneDate
import MathUE.PMFProduct.TotalVariation

/-! # Literal center restrictions: pure replies and the distinct half-atom move

Pure Quit1 pays 5/4. Moving only the existing half-mass Quit0 atom pays 9/8.
The three anchor-retaining restrictions have their respective half-unit debts.
-/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open Filter Topology
open _root_.Math.Probability _root_.Math.ProbabilityMassFunction Math.PMFProduct
open _root_.Math.Probability.DiscreteHazard.StoppingLaw

theorem root_all_quit_probabilities_pos (who : Fin 4) : 0 < (root who true).toReal := by
  fin_cases who <;> norm_num [root]

private theorem nearby_halfRoot_eq_root : nearbyRoot (fun _ => 1 / 2) = root := by
  have hactive (active : Fin 3) :
      nearbyRoot (fun _ => 1 / 2) active.castSucc = halfCoin := by
    apply PMF.ext
    intro action
    apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    cases action
    · rw [nearbyRoot_active_false, halfCoin_false]
      norm_num [unitIntervalClip]
    · rw [nearbyRoot_active_true, halfCoin_true]
      norm_num [unitIntervalClip]
  funext who
  fin_cases who
  · exact hactive 0
  · exact hactive 1
  · exact hactive 2
  · exact nearbyRoot_anchor (fun _ => 1 / 2)

private theorem profile_eq_nearby_half :
    profile = nearbyProfile reward (fun _ => 1 / 2) := by
  unfold profile nearbyProfile
  rw [nearby_halfRoot_eq_root]

theorem profile_stoppingLaw_eq_map (who : Fin 4) :
    quittingBehaviorStoppingLaw reward (profile who) =
      (root who).map (fun action => if action then some 0 else none) := by
  rw [profile_eq_nearby_half, nearbyProfile_stoppingLaw_eq_map, nearby_halfRoot_eq_root]

theorem profile_active_finiteMass_zero (active : Fin 3) :
    finiteMass (quittingBehaviorStoppingLaws reward profile active.castSucc) 0 = 1 / 2 := by
  change (quittingBehaviorStoppingLaw reward (profile active.castSucc) (some 0)).toReal = _
  rw [profile_eq_nearby_half, nearbyProfile_stoppingLaw_zero, nearbyRoot_active_true]
  norm_num [unitIntervalClip]

private theorem anchorDeleted_center_laws :
    quittingBehaviorStoppingLaws (childReward 3) (restrictedProfileOfParent 3 profile) =
      fun _ => halfCoin.map (fun action => if action then some 0 else none) := by
  funext who
  change quittingBehaviorStoppingLaw (childReward 3)
    (restrictedProfileOfParent 3 profile who) = _
  rw [restrictedProfileOfParent_stoppingLaw, profile_stoppingLaw_eq_map]
  fin_cases who <;> simp [deletedEquiv, finSuccAboveEquiv_apply, root] <;> rfl

private theorem anchorDeleted_center_expect (observable : (Fin 3 → Option ℕ) → ℝ) :
    expect (pmfPi (quittingBehaviorStoppingLaws (childReward 3)
        (restrictedProfileOfParent 3 profile))) observable =
      expect (pmfPi (fun _ : Fin 3 => halfCoin)) (fun action =>
        observable (fun who => if action who then some 0 else none)) := by
  have hmap := expect_pmfPi_coordwise_eq_of_maps_eq
    (fun _ : Fin 3 => halfCoin)
    (quittingBehaviorStoppingLaws (childReward 3) (restrictedProfileOfParent 3 profile))
    (fun _ action => if action then some 0 else none) (fun _ choice => choice)
    observable (fun who => by
      change halfCoin.map (fun action => if action then some 0 else none) =
        PMF.map id (quittingBehaviorStoppingLaws (childReward 3)
          (restrictedProfileOfParent 3 profile) who)
      rw [PMF.map_id, anchorDeleted_center_laws])
  exact hmap.symm

private theorem center_clockMap_eq_tuple (action : Fin 3 → Bool) :
    (fun who => if action who then some 0 else none) =
      ![if action 0 then some 0 else none, if action 1 then some 0 else none,
        if action 2 then some 0 else none] := by
  funext who
  fin_cases who <;> rfl

private theorem childClockPayoff_center_row (first second third : Bool) :
    childClockPayoff 3
        ![if first then some 0 else none, if second then some 0 else none,
          if third then some 0 else none] 0 =
      if first then 1 else 2 * if third then 1 else 0 := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  cases first <;> cases second <;> cases third <;>
    norm_num [childClockPayoff, quittingFirstStoppingOutcome, quittingEarliestStoppingValue,
      quittingEarliestStoppingCoalition, quittingStoppingTimeValue, huniv,
      quittingTerminalOutcomeReward, childReward_three_zero]

private theorem childClockPayoff_center_late_reply (first second third : Bool) :
    childClockPayoff 3
        (Function.update ![if first then some 0 else none, if second then some 0 else none,
          if third then some 0 else none] 0 (some 1)) 0 =
      if third then 2 else if second then 0 else 1 := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  cases first <;> cases second <;> cases third <;>
    norm_num [childClockPayoff, quittingFirstStoppingOutcome, quittingEarliestStoppingValue,
      quittingEarliestStoppingCoalition, quittingStoppingTimeValue, huniv,
      quittingTerminalOutcomeReward, childReward_three_zero]

theorem center_anchorDeleted_prescribed_payoff :
    quittingTerminalPayoff (childReward 3) (restrictedProfileOfParent 3 profile) 0 = 1 := by
  rw [← quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff,
    quittingStoppingLawExpectedPayoff, quittingIndependentTerminalOutcomeLaw, expect_map]
  change expect _ (fun times => childClockPayoff 3 times 0) = 1
  rw [anchorDeleted_center_expect]
  simp_rw [center_clockMap_eq_tuple, childClockPayoff_center_row]
  rw [expect_pmfPi_fin3]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [halfCoin]

/-- The pure replacement changes ALL of player zero's clock to date one. -/
theorem center_anchorDeleted_pureQuitOne_payoff :
    quittingBehaviorPureTimePayoff (childReward 3) (restrictedProfileOfParent 3 profile)
      0 (some 1) = 5 / 4 := by
  rw [quittingBehaviorPureTimePayoff_eq_expect_overwrite]
  change expect _ (fun times =>
    childClockPayoff 3 (Function.update times 0 (some 1)) 0) = 5 / 4
  rw [anchorDeleted_center_expect]
  simp_rw [center_clockMap_eq_tuple, childClockPayoff_center_late_reply]
  rw [expect_pmfPi_fin3]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [halfCoin]

theorem center_anchorDeleted_pureQuitOne_gain :
    quittingBehaviorPureTimePayoff (childReward 3) (restrictedProfileOfParent 3 profile)
        0 (some 1) -
      quittingTerminalPayoff (childReward 3) (restrictedProfileOfParent 3 profile) 0 =
        1 / 4 := by
  rw [center_anchorDeleted_pureQuitOne_payoff, center_anchorDeleted_prescribed_payoff]
  norm_num

/-- Only the existing half-mass date-zero atom moves; Never stays unchanged. -/
theorem center_anchorDeleted_halfAtom_move_gain : anchorDeletedMoveGain profile 0 = 1 / 8 := by
  have hzero := profile_active_finiteMass_zero 0
  have hone := profile_active_finiteMass_zero 1
  have htwo := profile_active_finiteMass_zero 2
  change finiteMass (quittingBehaviorStoppingLaws reward profile 0) 0 = 1 / 2 at hzero
  change finiteMass (quittingBehaviorStoppingLaws reward profile 1) 0 = 1 / 2 at hone
  change finiteMass (quittingBehaviorStoppingLaws reward profile 2) 0 = 1 / 2 at htwo
  rw [actual_anchor_deleted_atom_move_gain, hzero, hone, htwo]
  norm_num

theorem center_anchorDeleted_halfAtom_move_payoff :
    quittingTerminalPayoff (childReward 3)
      (Function.update (restrictedProfileOfParent 3 profile) 0
        (anchorDeletedMoveStrategy profile 0)) 0 = 9 / 8 := by
  have hgain := center_anchorDeleted_halfAtom_move_gain
  unfold anchorDeletedMoveGain at hgain
  rw [center_anchorDeleted_prescribed_payoff] at hgain
  linarith

theorem center_anchored_child_prescribed_payoff (deleted : Fin 3) :
    quittingTerminalPayoff (childReward deleted.castSucc)
      (restrictedProfileOfParent deleted.castSucc profile) (anchoredChildObserver deleted) =
        anchoredChildSign deleted * (1 / 2) := by
  have herror : Tendsto (fun _ : ℕ => quittingTerminalExploitability reward profile)
      atTop (nhds 0) := by
    simp only [profile_exploitability_zero]
    exact tendsto_const_nhds
  have hlimit := tendsto_actual_anchored_child_payoff (fun _ => profile) herror deleted
  exact tendsto_nhds_unique tendsto_const_nhds hlimit

theorem center_anchored_child_exploitability_half_le (deleted : Fin 3) :
    1 / 2 ≤ quittingTerminalExploitability (childReward deleted.castSucc)
      (restrictedProfileOfParent deleted.castSucc profile) := by
  let child := restrictedProfileOfParent deleted.castSucc profile
  have hnash := isεAsymptoticNash_of_quittingTerminalExploitability_le child (le_refl _)
  have hreply := hnash (anchoredChildObserver deleted)
    (quittingPureTimeBehaviorStrategy (childReward deleted.castSucc)
      (anchoredChildObserver deleted) (anchoredChildReplyChoice deleted))
  change quittingBehaviorPureTimePayoff (childReward deleted.castSucc) child
      (anchoredChildObserver deleted) (anchoredChildReplyChoice deleted) ≤
    quittingTerminalPayoff (childReward deleted.castSucc) child (anchoredChildObserver deleted) +
      quittingTerminalExploitability (childReward deleted.castSucc) child at hreply
  rw [anchored_child_reply_payoff] at hreply
  dsimp only [child] at hreply
  rw [center_anchored_child_prescribed_payoff] at hreply
  fin_cases deleted <;>
    norm_num [anchoredChildReplyValue, anchoredChildSign] at hreply <;> linarith

theorem center_anchorDeleted_exploitability_quarter_le :
    1 / 4 ≤ quittingTerminalExploitability (childReward 3)
      (restrictedProfileOfParent 3 profile) := by
  have hnash := isεAsymptoticNash_of_quittingTerminalExploitability_le
    (restrictedProfileOfParent 3 profile) (le_refl _)
  have hreply := hnash 0 (quittingPureTimeBehaviorStrategy (childReward 3) 0 (some 1))
  change quittingBehaviorPureTimePayoff (childReward 3) (restrictedProfileOfParent 3 profile)
      0 (some 1) ≤
    quittingTerminalPayoff (childReward 3) (restrictedProfileOfParent 3 profile) 0 +
      quittingTerminalExploitability (childReward 3) (restrictedProfileOfParent 3 profile)
        at hreply
  rw [center_anchorDeleted_pureQuitOne_payoff, center_anchorDeleted_prescribed_payoff] at hreply
  linarith

/-- The exact center fails on EVERY literal child, with the displayed actual replies. -/
theorem center_all_child_exploitability_lower (deleted : Fin 4) :
    (if deleted = 3 then 1 / 4 else 1 / 2) ≤
      quittingTerminalExploitability (childReward deleted)
        (restrictedProfileOfParent deleted profile) := by
  by_cases hanchor : deleted = 3
  · subst deleted
    simpa using center_anchorDeleted_exploitability_quarter_le
  · obtain ⟨active, hactive⟩ := Fin.exists_castSucc_eq.2 hanchor
    subst deleted
    rw [ite_eq_right (active_ne_anchor active)]
    exact center_anchored_child_exploitability_half_le active

theorem center_all_child_exploitability_pos (deleted : Fin 4) :
    0 < quittingTerminalExploitability (childReward deleted)
      (restrictedProfileOfParent deleted profile) := by
  have hpositive : (0 : ℝ) < (if deleted = 3 then 1 / 4 else 1 / 2) := by
    split_ifs <;> norm_num
  exact hpositive.trans_le (center_all_child_exploitability_lower deleted)

end GameTheory.AdaptiveChildCenter
