import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterNearbyInteriorRoot
import UniformEquilibrium.Quitting.Root.AlwaysContinuePureTimeReplies

/-! # Actual nearby one-date equilibrium, with the anchor's full cap checked -/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open _root_.Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

def nearbyProfile
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ) : (quittingGame table).BehaviorProfile :=
  quittingOneDateThenNeverProfile table (nearbyRoot probability)

@[simp] theorem nearbyProfile_liveHazard_zero
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ) (who : Fin 4) :
    quittingBehaviorLiveHazard table (nearbyProfile table probability who) 0 =
      nearbyRoot probability who := rfl

@[simp] theorem nearbyProfile_liveHazard_succ
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ) (who : Fin 4) (date : ℕ) :
    quittingBehaviorLiveHazard table (nearbyProfile table probability who) (date + 1) =
      PMF.pure false := rfl

@[simp] theorem nearbyProfile_stoppingLaw_zero
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ) (who : Fin 4) :
    (quittingBehaviorStoppingLaw table (nearbyProfile table probability who) (some 0)).toReal =
      (nearbyRoot probability who true).toReal := by
  rw [quittingBehaviorStoppingLaw_some_toReal, quittingHazardStopMass_eq_survival_mul_stop,
    quittingHazardSurvival_zero, nearbyProfile_liveHazard_zero, one_mul]

@[simp] theorem nearbyProfile_stoppingLaw_succ
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ) (who : Fin 4) (date : ℕ) :
    (quittingBehaviorStoppingLaw table
      (nearbyProfile table probability who) (some (date + 1))).toReal = 0 := by
  rw [quittingBehaviorStoppingLaw_some_toReal, quittingHazardStopMass_eq_survival_mul_stop,
    nearbyProfile_liveHazard_succ]
  simp

@[simp] theorem nearbyProfile_stoppingLaw_none
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ) (who : Fin 4) :
    (quittingBehaviorStoppingLaw table (nearbyProfile table probability who) none).toReal =
      (nearbyRoot probability who false).toReal := by
  let law := quittingBehaviorStoppingLaw table (nearbyProfile table probability who)
  have hsum : ∑' date : ℕ, (law (some date)).toReal =
      (nearbyRoot probability who true).toReal := by
    rw [tsum_eq_single 0]
    · exact nearbyProfile_stoppingLaw_zero table probability who
    · intro date hdate
      obtain ⟨date, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hdate
      exact nearbyProfile_stoppingLaw_succ table probability who date
  have htotal := _root_.Math.Probability.DiscreteHazard.StoppingLaw.none_add_tsum_finiteMass law
  change (law none).toReal + (∑' date : ℕ, (law (some date)).toReal) = 1 at htotal
  rw [hsum] at htotal
  have hroot := quittingRoot_continueProbability_add_quitProbability (nearbyRoot probability) who
  change (law none).toReal = _
  linarith

/-- The displayed profile has the actual common Quit0/Never laws, not just matching payoffs. -/
theorem nearbyProfile_stoppingLaw_eq_map
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ) (who : Fin 4) :
    quittingBehaviorStoppingLaw table (nearbyProfile table probability who) =
      (nearbyRoot probability who).map (fun action => if action then some 0 else none) := by
  apply PMF.ext
  intro choice
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  cases choice with
  | none =>
      rw [nearbyProfile_stoppingLaw_none]
      simp [PMF.map_apply, tsum_fintype]
  | some date =>
      cases date with
      | zero =>
          rw [nearbyProfile_stoppingLaw_zero]
          simp [PMF.map_apply, tsum_fintype]
      | succ date =>
          rw [nearbyProfile_stoppingLaw_succ]
          simp [PMF.map_apply, tsum_fintype]

@[simp] theorem nearbyProfile_anchor_stoppingLaw
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ) :
    quittingBehaviorStoppingLaw table (nearbyProfile table probability 3) = PMF.pure (some 0) := by
  rw [nearbyProfile_stoppingLaw_eq_map, nearbyRoot_anchor]
  exact PMF.pure_map (fun action => if action then some 0 else none) true

theorem nearbyProfile_active_stoppingLaw_masses
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ)
    (hbox : ∀ active, 1 / 4 < probability active ∧ probability active < 3 / 4)
    (active : Fin 3) :
    (quittingBehaviorStoppingLaw table
        (nearbyProfile table probability active.castSucc) (some 0)).toReal = probability active ∧
      (quittingBehaviorStoppingLaw table
        (nearbyProfile table probability active.castSucc) none).toReal =
          1 - probability active := by
  have hclip : unitIntervalClip (probability active) = probability active :=
    unitIntervalClip_eq_self (by linarith [(hbox active).1]) (by linarith [(hbox active).2])
  rw [nearbyProfile_stoppingLaw_zero, nearbyProfile_stoppingLaw_none,
    nearbyRoot_active_true, nearbyRoot_active_false, hclip]
  exact ⟨rfl, rfl⟩

private theorem center_anchor_rootPayoff_zero (action : Fin 4 → Bool) :
    quittingRootPayoff reward (0 : Payoff (Fin 4)) action 3 =
      if action 3 then 1 else 0 := by
  cases haction : action 3
  · by_cases hquit : (quittingQuitters action).Nonempty
    · unfold quittingRootPayoff
      rw [dite_eq_left hquit]
      simp [reward, quittingQuitters, haction]
    · unfold quittingRootPayoff
      rw [dite_eq_right hquit]
      rfl
  · have hquit := (quittingQuitters_nonempty_iff action).mpr ⟨3, haction⟩
    unfold quittingRootPayoff
    rw [dite_eq_left hquit]
    simp [reward, quittingQuitters, haction]

theorem center_anchor_quitPayoff (probability : Fin 3 → ℝ) :
    quittingRootQuitPayoff reward 0 (nearbyRoot probability) 3 = 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  simp_rw [center_anchor_rootPayoff_zero]
  rw [expect_pmfPi_fin4]
  simp

theorem center_anchor_continuePayoff_zero (probability : Fin 3 → ℝ) :
    quittingRootContinuePayoff reward 0 (nearbyRoot probability) 3 = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  simp_rw [center_anchor_rootPayoff_zero]
  rw [expect_pmfPi_fin4]
  simp

theorem nearby_anchor_continueMass (probability : Fin 3 → ℝ) :
    quittingRootOpponentContinueMass (nearbyRoot probability) 3 =
      (1 - unitIntervalClip (probability 0)) *
        (1 - unitIntervalClip (probability 1)) * (1 - unitIntervalClip (probability 2)) := by
  unfold quittingRootOpponentContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability, Fin.prod_univ_four]
  simp [nearbyRoot, nearbySimplex]

theorem nearby_anchor_continueMass_le
    (probability : Fin 3 → ℝ)
    (hbox : ∀ active, 1 / 4 < probability active ∧ probability active < 3 / 4) :
    quittingRootOpponentContinueMass (nearbyRoot probability) 3 ≤ 27 / 64 := by
  have hclip : ∀ active, unitIntervalClip (probability active) = probability active := by
    intro active
    apply unitIntervalClip_eq_self <;> linarith [(hbox active).1, (hbox active).2]
  rw [nearby_anchor_continueMass]
  simp_rw [hclip]
  have hfactor : ∀ active, 0 ≤ 1 - probability active ∧ 1 - probability active ≤ 3 / 4 := by
    intro active
    constructor <;> linarith [(hbox active).1, (hbox active).2]
  have hpair := mul_le_mul (hfactor 0).2 (hfactor 1).2
    (hfactor 1).1 (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have htriple := mul_le_mul hpair (hfactor 2).2 (hfactor 2).1
    (by norm_num : (0 : ℝ) ≤ (3 / 4) * (3 / 4))
  norm_num at htriple ⊢
  exact htriple

theorem center_anchor_continuePayoff_best (probability : Fin 3 → ℝ) :
    quittingRootContinuePayoff reward continuationBest (nearbyRoot probability) 3 =
      quittingRootOpponentContinueMass (nearbyRoot probability) 3 := by
  unfold quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  change quittingRootContinuePayoff reward 0 (nearbyRoot probability) 3 +
    quittingRootOpponentContinueMass (nearbyRoot probability) 3 * continuationBest 3 = _
  rw [center_anchor_continuePayoff_zero]
  simp [continuationBest]

/-- This is the actual BEST-response vector of the all-Continue tail. -/
theorem nearby_alwaysContinue_best_close
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta)
    (who : Fin 4) :
    |quittingContinuationBestResponse table (quittingAlwaysContinueProfile table) who -
      continuationBest who| ≤ delta := by
  have hsingleton := hclose (quittingSingletonTerminal who) who
  have hcenter : max 0 (reward (quittingSingletonTerminal who) who) =
      continuationBest who := by
    rw [singleton_reward]
    fin_cases who <;> norm_num [continuationBest]
  unfold quittingContinuationBestResponse
  rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
  rw [← hcenter]
  exact (abs_max_sub_max_le_max 0 _ 0 _).trans
    (max_le (by simpa using hdelta) hsingleton)

/-- Quit dominates the complete Continue arm, including every later finite date and Never. -/
theorem nearby_anchor_endpoints
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta)
    (probability : Fin 3 → ℝ)
    (hbox : ∀ active, 1 / 4 < probability active ∧ probability active < 3 / 4) :
    1 - delta ≤ quittingRootQuitPayoff table 0 (nearbyRoot probability) 3 ∧
      quittingRootContinuePayoff table
          (quittingContinuationBestResponse table (quittingAlwaysContinueProfile table))
          (nearbyRoot probability) 3 ≤ 27 / 64 + delta := by
  have hquit := abs_quittingRootExpectedPayoff_sub_of_reward_and_tail_close
    table reward 0 0 (Function.update (nearbyRoot probability) 3 (PMF.pure true)) 3
    (fun terminal => hclose terminal 3) (by simpa using hdelta)
  change |quittingRootQuitPayoff table 0 (nearbyRoot probability) 3 -
    quittingRootQuitPayoff reward 0 (nearbyRoot probability) 3| ≤ delta at hquit
  rw [center_anchor_quitPayoff] at hquit
  have hcontinue := abs_quittingRootExpectedPayoff_sub_of_reward_and_tail_close
    table reward
    (quittingContinuationBestResponse table (quittingAlwaysContinueProfile table))
    continuationBest (Function.update (nearbyRoot probability) 3 (PMF.pure false)) 3
    (fun terminal => hclose terminal 3) (nearby_alwaysContinue_best_close table hdelta hclose 3)
  change |quittingRootContinuePayoff table
      (quittingContinuationBestResponse table (quittingAlwaysContinueProfile table))
      (nearbyRoot probability) 3 -
    quittingRootContinuePayoff reward continuationBest (nearbyRoot probability) 3| ≤ delta
    at hcontinue
  rw [center_anchor_continuePayoff_best] at hcontinue
  have hmass := nearby_anchor_continueMass_le probability hbox
  constructor <;> linarith [abs_le.mp hquit, abs_le.mp hcontinue]

/-- The Never endpoint keeps the zero prescribed tail. -/
theorem nearby_anchor_neverPayoff_eq
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ) :
    quittingTerminalPayoff table (Function.update (nearbyProfile table probability) 3
      (quittingPureTimeBehaviorStrategy table 3 none)) 3 =
      quittingRootContinuePayoff table 0 (nearbyRoot probability) 3 := by
  have hmenu := quittingTerminalPayoff_rootThen_pureTime_map_succ_eq_continuePayoff
    table (nearbyRoot probability) (quittingAlwaysContinueProfile table) 3 none
  simp only [Option.map_none,
    quittingTerminalPayoff_alwaysContinueProfile_update_pureTime_none,
    quittingTerminalPayoff_quittingAlwaysContinue] at hmenu
  have htailZero : Function.update (fun _ : Fin 4 => (0 : ℝ)) 3 0 =
      (0 : Payoff (Fin 4)) := by
    funext who
    by_cases hwho : who = 3 <;> simp [hwho]
  rw [htailZero] at hmenu
  simpa only [nearbyProfile, quittingOneDateThenNeverProfile] using hmenu

theorem nearby_anchor_latePayoff_eq
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ) (date : ℕ) :
    quittingTerminalPayoff table (Function.update (nearbyProfile table probability) 3
      (quittingPureTimeBehaviorStrategy table 3 (some (date + 1)))) 3 =
      quittingRootContinuePayoff table 0 (nearbyRoot probability) 3 +
        quittingRootOpponentContinueMass (nearbyRoot probability) 3 *
          table (quittingSingletonTerminal 3) 3 := by
  have hmenu := quittingTerminalPayoff_rootThen_pureTime_map_succ_eq_continuePayoff
    table (nearbyRoot probability) (quittingAlwaysContinueProfile table) 3 (some date)
  simp only [Option.map_some, Nat.succ_eq_add_one,
    quittingTerminalPayoff_alwaysContinueProfile_update_pureTime_some,
    quittingTerminalPayoff_quittingAlwaysContinue] at hmenu
  have htail := quittingRootExpectedPayoff_continuation_congr table
    (Function.update (0 : Payoff (Fin 4)) 3 (table (quittingSingletonTerminal 3) 3))
    (fun _ => table (quittingSingletonTerminal 3) 3)
    (Function.update (nearbyRoot probability) 3 (PMF.pure false)) 3 (by simp)
  change quittingRootContinuePayoff table _ (nearbyRoot probability) 3 =
    quittingRootContinuePayoff table _ (nearbyRoot probability) 3 at htail
  exact hmenu.trans (htail.trans
    (quittingRootContinuePayoff_const_singleton_eq table (nearbyRoot probability) 3))

/-- Never and EVERY positive finite date retain their own exact, separately bounded arms. -/
theorem nearby_anchor_never_and_late_bounds
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta)
    (probability : Fin 3 → ℝ) :
    quittingTerminalPayoff table (Function.update (nearbyProfile table probability) 3
        (quittingPureTimeBehaviorStrategy table 3 none)) 3 ≤ delta ∧
      ∀ date : ℕ, quittingTerminalPayoff table (Function.update (nearbyProfile table probability) 3
          (quittingPureTimeBehaviorStrategy table 3 (some (date + 1)))) 3 ≤
        quittingRootOpponentContinueMass (nearbyRoot probability) 3 + delta := by
  have hzero := abs_quittingRootExpectedPayoff_sub_of_reward_and_tail_close
    table reward 0 0 (Function.update (nearbyRoot probability) 3 (PMF.pure false)) 3
    (fun terminal => hclose terminal 3) (by simpa using hdelta)
  change |quittingRootContinuePayoff table 0 (nearbyRoot probability) 3 -
    quittingRootContinuePayoff reward 0 (nearbyRoot probability) 3| ≤ delta at hzero
  rw [center_anchor_continuePayoff_zero] at hzero
  refine ⟨?_, ?_⟩
  · rw [nearby_anchor_neverPayoff_eq]
    linarith [abs_le.mp hzero]
  · intro date
    have hsolo := hclose (quittingSingletonTerminal 3) 3
    have hcenter : reward (quittingSingletonTerminal 3) 3 = 1 := by
      rw [singleton_reward]
      rfl
    rw [hcenter] at hsolo
    have hlate := abs_quittingRootExpectedPayoff_sub_of_reward_and_tail_close table reward
      (fun _ => table (quittingSingletonTerminal 3) 3) continuationBest
      (Function.update (nearbyRoot probability) 3 (PMF.pure false)) 3
      (fun terminal => hclose terminal 3) (by simpa [continuationBest] using hsolo)
    change |quittingRootContinuePayoff table _ (nearbyRoot probability) 3 -
      quittingRootContinuePayoff reward continuationBest (nearbyRoot probability) 3| ≤ delta
      at hlate
    rw [center_anchor_continuePayoff_best, quittingRootContinuePayoff_const_singleton_eq]
      at hlate
    rw [nearby_anchor_latePayoff_eq]
    linarith [abs_le.mp hlate]

/-- The active gap zero and separate anchor bound give Nash against the true tail cap. -/
theorem nearbyRoot_exactNash_best_tail
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hsmall : delta < 1 / 8)
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta)
    (probability : Fin 3 → ℝ)
    (hbox : ∀ active, 1 / 4 < probability active ∧ probability active < 3 / 4)
    (hzero : ∀ active, nearbyGap table probability active = 0) :
    IsεQuittingRootNash table
      (quittingContinuationBestResponse table (quittingAlwaysContinueProfile table)) 0
      (nearbyRoot probability) := by
  apply (isεQuittingRootEndpointNash_iff_isεQuittingRootNash _ _ _ _).mp
  intro who
  simp only [neg_zero]
  by_cases hanchor : who = 3
  · subst who
    obtain ⟨hquit, hcontinue⟩ := nearby_anchor_endpoints
      table hdelta hclose probability hbox
    have hquitTail := quittingRootQuitPayoff_continuation_invariant table 0
      (quittingContinuationBestResponse table (quittingAlwaysContinueProfile table))
      (nearbyRoot probability) 3
    change (nearbyRoot probability 3 false).toReal *
        quittingRootEndpointDifference table _ (nearbyRoot probability) 3 ≤ 0 ∧
      0 ≤ (nearbyRoot probability 3 true).toReal *
        quittingRootEndpointDifference table _ (nearbyRoot probability) 3
    simp only [nearbyRoot_anchor]
    have hfalse : ((PMF.pure true) false).toReal = 0 := by simp
    have htrue : ((PMF.pure true) true).toReal = 1 := by simp
    rw [hfalse, htrue]
    change 0 * (_ - _) ≤ 0 ∧ 0 ≤ 1 * (_ - _)
    constructor
    · simp
    · rw [one_mul, ← hquitTail]
      linarith
  · obtain ⟨active, hactive⟩ := Fin.exists_castSucc_eq.2 hanchor
    subst who
    have hgap := (nearbyGap_eq_endpointDifference_tail table
      (quittingContinuationBestResponse table (quittingAlwaysContinueProfile table))
      probability active).symm.trans (hzero active)
    rw [hgap]
    simp

theorem nearbyProfile_exactTerminalNash
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hsmall : delta < 1 / 8)
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta)
    (probability : Fin 3 → ℝ)
    (hbox : ∀ active, 1 / 4 < probability active ∧ probability active < 3 / 4)
    (hzero : ∀ active, nearbyGap table probability active = 0) :
    (quittingGame table).IsεAsymptoticNash (quittingTerminalPayoff table) 0
      (nearbyProfile table probability) := by
  apply isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash
  · exact nearbyRoot_hasSureQuitter probability
  · exact nearbyRoot_exactNash_best_tail table hdelta hsmall hclose probability hbox hzero

theorem nearbyProfile_anchor_payoff_eq_quit
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (probability : Fin 3 → ℝ) :
    quittingTerminalPayoff table (nearbyProfile table probability) 3 =
      quittingRootQuitPayoff table 0 (nearbyRoot probability) 3 := by
  have hupdate : Function.update (nearbyRoot probability) 3 (PMF.pure true) =
      nearbyRoot probability := by
    rw [← nearbyRoot_anchor probability]
    exact Function.update_eq_self 3 _
  unfold nearbyProfile quittingOneDateThenNeverProfile
  rw [quittingTerminalPayoff_rootThenContinuation_eq]
  simp_rw [quittingTerminalPayoff_quittingAlwaysContinue]
  unfold quittingRootQuitPayoff
  rw [hupdate]
  rfl

theorem nearbyProfile_anchor_fullCap_eq_quit
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hsmall : delta < 1 / 8)
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta)
    (probability : Fin 3 → ℝ)
    (hbox : ∀ active, 1 / 4 < probability active ∧ probability active < 3 / 4) :
    quittingContinuationBestResponseValue table (nearbyProfile table probability) 3 =
      quittingRootQuitPayoff table 0 (nearbyRoot probability) 3 := by
  let best := quittingContinuationBestResponse table (quittingAlwaysContinueProfile table)
  have htail := quittingRootExpectedPayoff_continuation_congr table
    (Function.update (0 : Payoff (Fin 4)) 3 (best 3)) best
    (Function.update (nearbyRoot probability) 3 (PMF.pure false)) 3 (by simp)
  change quittingRootContinuePayoff table _ (nearbyRoot probability) 3 =
    quittingRootContinuePayoff table best (nearbyRoot probability) 3 at htail
  have hformula := quittingContinuationBestResponseValue_rootThenContinuation_eq_max
    table (nearbyRoot probability) (quittingAlwaysContinueProfile table) 3
  simp only [quittingTerminalPayoff_quittingAlwaysContinue] at hformula
  change quittingContinuationBestResponseValue table (nearbyProfile table probability) 3 =
    max (quittingRootQuitPayoff table 0 (nearbyRoot probability) 3)
      (quittingRootContinuePayoff table (Function.update 0 3 (best 3))
        (nearbyRoot probability) 3) at hformula
  rw [htail] at hformula
  obtain ⟨hquit, hcontinue⟩ := nearby_anchor_endpoints table hdelta hclose probability hbox
  change quittingRootContinuePayoff table best (nearbyRoot probability) 3 ≤
    27 / 64 + delta at hcontinue
  rw [hformula, max_eq_left (by linarith)]

theorem exists_nearby_oneDate_exactTerminalNash_and_uniformPayoff
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hsmall : delta < 1 / 8)
    (hclose : ∀ terminal player, |table terminal player - reward terminal player| ≤ delta) :
    ∃ probability : Fin 3 → ℝ,
      (∀ active, 1 / 4 < probability active ∧ probability active < 3 / 4) ∧
      (quittingGame table).IsεAsymptoticNash (quittingTerminalPayoff table) 0
        (nearbyProfile table probability) ∧
      (quittingGame table).IsUniformEquilibriumPayoff none
        (quittingTerminalPayoff table (nearbyProfile table probability)) := by
  obtain ⟨probability, hbox, hzero⟩ :=
    exists_nearby_interior_active_root table hdelta hsmall hclose
  have hnash := nearbyProfile_exactTerminalNash table hdelta hsmall hclose probability hbox hzero
  exact ⟨probability, hbox, hnash,
    quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact table _ hnash⟩

end GameTheory.AdaptiveChildCenter
