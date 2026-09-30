/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCollisionRewardTable
import UniformEquilibrium.Quitting.Paths.PureTimeMembershipToggleObstruction
import UniformEquilibrium.Quitting.Classification.Existence.PerfectAbsorbingRow
import UniformEquilibrium.Quitting.Cycles.PairedCycleSchedule
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Circulation.DirectionBarycenter
import MathUE.Topology.FiniteLimitDecomposition

/-!
# Boundary and class comparisons for the literal paired collision family

The pure-clock obstruction covers complete deterministic clocks, including
delayed exits and Never. The class exclusions are exclusions of the named
source hypotheses, not exclusions of uniform-equilibrium payoffs.
-/

noncomputable section

namespace GameTheory.PairedCollisionReward

open Filter
open QuittingSureSetOwnerRepair
open scoped Topology

/-- The packet's toggles have the positive common gap `min 1 (4 - c)`. -/
theorem membershipToggleGap {c : ℝ} (hc : 1 ≤ c) :
    HasQuittingPureTimeMembershipToggleGap (reward c) (min 1 (4 - c)) := by
  have hgapOne : min 1 (4 - c) ≤ 1 := min_le_left _ _
  have hgapPair : min 1 (4 - c) ≤ 4 - c := min_le_right _ _
  refine ⟨?_, ?_⟩
  · refine ⟨0, ?_⟩
    change min 1 (4 - c) ≤ 1
    exact hgapOne
  · intro coalition
    by_cases hsingleton : coalition.1.card = 1
    · obtain ⟨owner, howner⟩ := Finset.card_eq_one.mp hsingleton
      have heq : coalition = quittingSingletonTerminal owner := Subtype.ext howner
      rw [heq]
      fin_cases owner
      · refine Or.inl ⟨2, by decide, ?_⟩
        change 0 + min 1 (4 - c) ≤ c
        linarith
      · refine Or.inl ⟨2, by decide, ?_⟩
        change 0 + min 1 (4 - c) ≤ c
        linarith
      · refine Or.inl ⟨0, by decide, ?_⟩
        change 0 + min 1 (4 - c) ≤ c
        linarith
      · refine Or.inl ⟨0, by decide, ?_⟩
        change 0 + min 1 (4 - c) ≤ c
        linarith
    · fin_cases coalition <;>
        first
        | exact (hsingleton (by decide)).elim
        | solve
          | (refine Or.inl ⟨0, ?_, ?_⟩
             · decide
             · norm_num +decide [reward])
          | (refine Or.inl ⟨1, ?_, ?_⟩
             · decide
             · norm_num +decide [reward])
          | (refine Or.inl ⟨2, ?_, ?_⟩
             · decide
             · norm_num +decide [reward])
          | (refine Or.inl ⟨3, ?_, ?_⟩
             · decide
             · norm_num +decide [reward])
          | (refine Or.inr ⟨0, ?_, ?_, ?_⟩
             · decide
             · decide
             · norm_num +decide [reward] <;> linarith)
          | (refine Or.inr ⟨1, ?_, ?_, ?_⟩
             · decide
             · decide
             · norm_num +decide [reward])
          | (refine Or.inr ⟨2, ?_, ?_, ?_⟩
             · decide
             · decide
             · norm_num +decide [reward]
               linarith)

/-- Every complete pure clock has an actual full behavioral improving reply. -/
theorem exists_behaviorDeviation_pureClock {c : ℝ} (hc : 1 ≤ c) (_hupper : c < 4)
    (times : QuittingPureTimeProfile Player) :
    ∃ (who : Player) (deviation : (quittingGame (reward c)).BehaviorStrategy who),
      quittingTerminalPayoff (reward c)
          (quittingPureTimeProfileBehavior (reward c) times) who + min 1 (4 - c) ≤
        quittingTerminalPayoff (reward c)
          (Function.update (quittingPureTimeProfileBehavior (reward c) times)
            who deviation) who :=
  (membershipToggleGap hc).exists_behaviorDeviation times

/-- Earliest-coalition toggles and the all-Never escape exclude every pure clock. -/
theorem not_exactTerminalNash_pureClock {c : ℝ} (hc : 1 ≤ c) (hupper : c < 4)
    (times : QuittingPureTimeProfile Player) :
    ¬ (quittingGame (reward c)).IsεAsymptoticNash
        (quittingTerminalPayoff (reward c)) 0
        (quittingPureTimeProfileBehavior (reward c) times) := by
  exact (membershipToggleGap hc).not_isεAsymptoticNash_zero
    (lt_min (by norm_num) (by linarith)) times

/-- All-Never opponents cap every full behavioral reply at the solo level. -/
theorem bestReplyValue_allNever (c : ℝ) (who : Player) :
    quittingBestReplyValue (reward c) (quittingAlwaysContinueProfile (reward c)) who =
      1 := by
  rw [← quittingStationaryProfile_pureSetRoot_empty,
    quittingBestReplyValue_stationary, quittingStationaryUnilateralCap_pureSetRoot]
  simp only [Finset.insert_empty, Finset.erase_empty, quittingSetReward_empty,
    quittingSetReward_singleton_eq_soloReward]
  simp

/-- Punishment normality holds at every real parameter, via the actual Never plan. -/
theorem punishmentValue_le_one (c : ℝ) (who : Player) :
    quittingPunishmentValue (reward c) who ≤ 1 := by
  rw [← bestReplyValue_allNever c who]
  exact quittingPunishmentValue_le (reward c) who _

/-- A literal pair member disproves capped joint exit as soon as `c > 1`. -/
theorem not_cappedJointExit {c : ℝ} (hc : 1 < c) :
    ¬ QuittingCappedJointExit (reward c) := by
  intro hcap
  have h := hcap ⟨{0, 1}, by decide⟩ 0 (by decide)
  norm_num [reward] at h
  linarith

/-- A sure two-player root has endpoint `c > 1` at both active players;
the other players have zero hazard and cannot be low-active witnesses. -/
theorem not_lowActiveQuittingRootQuitPayoff {c : ℝ} (hc : 1 < c) :
    ¬ HasLowActiveQuittingRootQuitPayoff (reward c) := by
  intro hlow
  have habs : 0 < quittingRootAbsorptionMass (quittingPureSetRoot ({0, 1} :
      Finset Player)) := by
    rw [quittingRootAbsorptionMass_pureSetRoot_of_nonempty (by decide)]
    norm_num
  obtain ⟨who, hactive, hlowWho⟩ := hlow _ habs
  rw [quittingRootQuitPayoff_pureSetRoot_eq_insert] at hlowWho
  fin_cases who <;> norm_num [quittingPureSetRoot, quittingSetAction] at hactive
  all_goals norm_num [quittingSetReward, reward] at hlowWho
  all_goals linarith

/-- Every owner has a cross recipient whose immediate joining payoff is at
least one at every positive solo rate, while its passive solo payoff is zero. -/
theorem soloJoiningObstruction_allRates {c : ℝ} (hc : 1 ≤ c) (owner : Player)
    {h : ℝ} (hh : 0 < h) (_hupper : h ≤ 1) :
    QuittingSoloJoiningObstruction (reward c) owner h := by
  have hgain : 1 ≤ (1 - h) + h * c := by
    nlinarith
  fin_cases owner
  · refine ⟨2, by decide, ?_⟩
    norm_num [quittingSoloReward, quittingSingletonCollisionReward, reward]
    linarith
  · refine ⟨2, by decide, ?_⟩
    norm_num [quittingSoloReward, quittingSingletonCollisionReward, reward]
    linarith
  · refine ⟨0, by decide, ?_⟩
    norm_num [quittingSoloReward, quittingSingletonCollisionReward, reward]
    linarith
  · refine ⟨0, by decide, ?_⟩
    norm_num [quittingSoloReward, quittingSingletonCollisionReward, reward]
    linarith

/-- Two distinct zero singleton comparisons cannot both be the one partner
allowed by the exact paired raw-region hypotheses. This covers every schedule. -/
theorem not_pairedCycleRawRegion (c : ℝ) {period : ℕ}
    (schedule : PairedCycle.Schedule Player period) :
    ¬ PairedCycle.RawRegion (reward c) schedule := by
  intro hregion
  have htwo : (2 : Player) = schedule.partner 0 :=
    hregion.eq_partner_of_singleton_lt (by
      norm_num [PairedCycle.singleton, quittingSingletonTerminal, reward])
  have hthree : (3 : Player) = schedule.partner 0 :=
    hregion.eq_partner_of_singleton_lt (by
      norm_num [PairedCycle.singleton, quittingSingletonTerminal, reward])
  have hfalse : (2 : Player) = 3 := htwo.trans hthree.symm
  exact (by decide : (2 : Player) ≠ 3) hfalse

/-- Relabel both coalition members and payoff recipients by the same permutation. -/
def relabelReward (c : ℝ) (order : Equiv.Perm Player)
    (coalition : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who => reward c
    ⟨coalition.1.map order.toEmbedding, Finset.map_nonempty.mpr coalition.2⟩ (order who)

@[simp] theorem relabelReward_singleton (c : ℝ) (order : Equiv.Perm Player)
    (owner who : Player) :
    relabelReward c order (quittingSingletonTerminal owner) who =
      quittingSoloReward (reward c) (order owner) (order who) := by
  simp [relabelReward, quittingSingletonTerminal, quittingSoloReward]

/-- No permutation of the literal table supplies the exact raw paired source. -/
theorem not_pairedCycleRawRegion_relabel (c : ℝ) (order : Equiv.Perm Player)
    {period : ℕ} (schedule : PairedCycle.Schedule Player period) :
    ¬ PairedCycle.RawRegion (relabelReward c order) schedule := by
  intro hregion
  have htwo : order.symm 2 = schedule.partner (order.symm 0) :=
    hregion.eq_partner_of_singleton_lt (by
      simp [PairedCycle.singleton])
  have hthree : order.symm 3 = schedule.partner (order.symm 0) :=
    hregion.eq_partner_of_singleton_lt (by
      simp [PairedCycle.singleton])
  have hfalse : (2 : Player) = 3 := order.symm.injective (htwo.trans hthree.symm)
  exact (by decide : (2 : Player) ≠ 3) hfalse

/-- A concrete common hazard tending to zero, with independent draws per player. -/
def smallHazard (index : ℕ) : ℝ := 1 / (index + 2 : ℝ)

theorem smallHazard_pos (index : ℕ) : 0 < smallHazard index := by
  unfold smallHazard
  positivity

theorem smallHazard_le_one (index : ℕ) : smallHazard index ≤ 1 := by
  unfold smallHazard
  rw [div_le_one (by positivity)]
  have hindex : (0 : ℝ) ≤ index := Nat.cast_nonneg index
  linarith

theorem smallHazard_tendsto_zero : Tendsto smallHazard atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)
  convert h using 1
  funext index
  simp [smallHazard, Function.comp_apply, Nat.cast_add]
  ring

def smallHazardRoot (index : ℕ) : Player → PMF Bool := fun _ =>
  Math.ProbabilityMassFunction.bernoulliBool (smallHazard index)
    (smallHazard_pos index).le (smallHazard_le_one index)

@[simp] theorem smallHazardRoot_total (index : ℕ) :
    quittingStationaryTotalHazard (smallHazardRoot index) = 4 * smallHazard index := by
  simp [quittingStationaryTotalHazard, smallHazardRoot]

/-- Each recipient has singleton average `5/4`, independently of `c`. -/
theorem smallHazardRoot_singletonBarycenter (c : ℝ) (index : ℕ) (who : Player) :
    quittingStationarySingletonDirectionBarycenter (reward c)
      (smallHazardRoot index) who = 5 / 4 := by
  have hne : smallHazard index ≠ 0 := (smallHazard_pos index).ne'
  unfold quittingStationarySingletonDirectionBarycenter
  simp only [smallHazardRoot_total]
  fin_cases who
  all_goals
    simp [smallHazardRoot, Fin.sum_univ_four, soloReward_eval]
    field_simp [hne]
    ring

/-- The actual stationary payoff, rather than only its formal singleton
linearization, tends to `5/4` for every player and every fixed real `c`. -/
theorem smallHazard_actualPayoff_tendsto (c : ℝ) (who : Player) :
    Tendsto (fun index => quittingTerminalPayoff (reward c)
      (quittingStationaryProfile (reward c) (smallHazardRoot index)) who)
      atTop (𝓝 (5 / 4)) := by
  have htotal : Tendsto (fun index => quittingStationaryTotalHazard
      (smallHazardRoot index)) atTop (𝓝 0) := by
    simpa using smallHazard_tendsto_zero.const_mul 4
  have hhalf : ∀ᶠ index in atTop,
      quittingStationaryTotalHazard (smallHazardRoot index) ≤ 1 / 2 :=
    (htotal.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ h => h.le
  have hdiff := Math.tendsto_zero_of_abs_le_of_tendsto_zero _ _
    (by simpa using htotal.const_mul (6 * quittingRewardBound (reward c)))
    (hhalf.mono fun index h =>
      abs_stationaryPayoff_sub_singletonDirectionBarycenter_le (reward c)
        (abs_reward_le_quittingRewardBound (reward c)) (smallHazardRoot index) who
        (by
          rw [smallHazardRoot_total]
          exact mul_pos (by norm_num) (smallHazard_pos index)) h)
  simp_rw [smallHazardRoot_singletonBarycenter] at hdiff
  simpa using hdiff.add_const (5 / 4 : ℝ)

/-- One actual stationary profile pays all four players strictly above their
own singleton rewards. Its equilibrium status is not asserted. -/
theorem exists_stationaryProfile_all_payoffs_gt_singleton (c : ℝ) :
    ∃ index : ℕ, ∀ who : Player,
      quittingSoloReward (reward c) who who <
        quittingTerminalPayoff (reward c)
          (quittingStationaryProfile (reward c) (smallHazardRoot index)) who := by
  have hevent (who : Player) : ∀ᶠ index in atTop,
      quittingSoloReward (reward c) who who <
        quittingTerminalPayoff (reward c)
          (quittingStationaryProfile (reward c) (smallHazardRoot index)) who := by
    simpa using (smallHazard_actualPayoff_tendsto c who).eventually
      (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 5 / 4))
  exact (eventually_all.mpr hevent).exists

/-- Weak singleton payoff exclusion over all actual behavioral profiles fails.
This does not assert that the witnessing stationary profile is an equilibrium. -/
theorem not_weakSingletonPayoffExclusion (c : ℝ) :
    ¬ (∀ profile : (quittingGame (reward c)).BehaviorProfile, ∃ who : Player,
      quittingTerminalPayoff (reward c) profile who ≤
        quittingSoloReward (reward c) who who) := by
  intro hexclusion
  obtain ⟨index, hstrict⟩ := exists_stationaryProfile_all_payoffs_gt_singleton c
  obtain ⟨who, hweak⟩ := hexclusion
    (quittingStationaryProfile (reward c) (smallHazardRoot index))
  exact (not_le_of_gt (hstrict who)) hweak

end GameTheory.PairedCollisionReward
