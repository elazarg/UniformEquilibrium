/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.DiffuseStationaryPrefixSourceAttachments
import UniformEquilibrium.Quitting.Classification.Existence.PositiveAbsorptionStationarySplice
import UniformEquilibrium.Quitting.Cycles.PeriodOneTangentAtlas

/-!
# A fixed-horizon exceptional-owner source need not isolate its owner

Positive owner-deleted survival and vanishing joint survival do not by
themselves imply that absorption concentrates on the exceptional owner's
singleton.  The exact zero-payoff two-player family below is a genuine
`QuittingDiffuseStationaryPrefixFamily`: the owner becomes almost sure to Quit,
the spectator independently Quits with probability one half, and the repeated
prefix has fixed length three.  Every profile is exact Nash because every
terminal reward is zero.

The resulting source has vanishing joint survival, owner-deleted survival
identically `1/8`, and every other deleted survival tending to zero.  Yet the
first-row singleton-owner mass tends to `1/2`, not one.  Thus an exceptional
source needs an additional temporal-diffusion or owner-isolation field before
the singleton endpoint and normal/no-harm adapter can be invoked.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

namespace ExceptionalOwnerSourceRegression

/-- The zero terminal table. -/
def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun _ _ ↦ 0

/-- A positive scale strictly below one. -/
def rate (n : ℕ) : ℝ := 1 / (n + 2)

theorem rate_pos (n : ℕ) : 0 < rate n := by
  unfold rate
  positivity

theorem rate_lt_one (n : ℕ) : rate n < 1 := by
  unfold rate
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)).2
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem rate_tendsto_zero : Tendsto rate atTop (nhds 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hshift := h.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 2)) atTop (nhds 0)
  convert hshift using 1
  funext n
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

/-- The exceptional owner continues with probability `rate n`. -/
def ownerHazard (n : ℕ) : PMF Bool :=
  quittingHazardCoin (1 - rate n) (sub_nonneg.mpr (rate_lt_one n).le)
    (by linarith [rate_pos n])

/-- The spectator independently Quits with probability one half. -/
def spectatorHazard : PMF Bool :=
  quittingHazardCoin (1 / 2) (by norm_num) (by norm_num)

/-- Player `true` is the exceptional owner. -/
def root (n : ℕ) : Bool → PMF Bool
  | true => ownerHazard n
  | false => spectatorHazard

@[simp] theorem ownerHazard_continue (n : ℕ) :
    (ownerHazard n false).toReal = rate n := by
  simp [ownerHazard]

@[simp] theorem spectatorHazard_continue :
    (spectatorHazard false).toReal = 1 / 2 := by
  simp [spectatorHazard]
  norm_num

theorem stationaryContinueMass_root (n : ℕ) :
    quittingStationaryContinueMass (root n) = rate n / 2 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [root]
  ring

theorem deletedContinueMass_owner (n : ℕ) :
    quittingRootDeletedContinueMass (root n) true = 1 / 2 := by
  have h := quittingStationaryContinueMass_eq_deletedContinueMass_mul_own
    (root n) true
  rw [stationaryContinueMass_root] at h
  simp [root] at h
  nlinarith [rate_pos n]

theorem deletedContinueMass_spectator (n : ℕ) :
    quittingRootDeletedContinueMass (root n) false = rate n := by
  have h := quittingStationaryContinueMass_eq_deletedContinueMass_mul_own
    (root n) false
  rw [stationaryContinueMass_root] at h
  simp [root] at h
  linarith

theorem rewardBound_eq_zero : quittingRewardBound reward = 0 := by
  unfold quittingRewardBound
  simp [reward]

theorem rootSequenceTerminalValue_eq_zero
    (roots : ℕ → Bool → PMF Bool) (who : Bool) (start : ℕ) :
    quittingRootSequenceTerminalValue reward roots who start = 0 := by
  have hbound := abs_quittingRootSequenceTerminalValue_le reward roots who start
    (bound := 0) (by norm_num) (by intro terminal player; simp [reward])
  exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))

theorem rootSequenceHazardTerminalValue_eq_zero
    (roots : ℕ → Bool → PMF Bool) (who : Bool)
    (hazard : ℕ → PMF Bool) (start : ℕ) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard start = 0 := by
  unfold quittingRootSequenceHazardTerminalValue
  exact rootSequenceTerminalValue_eq_zero
    (quittingRootSequenceUpdate roots who hazard) who start

theorem punishmentValue_eq_zero (who : Bool) :
    quittingPunishmentValue reward who = 0 := by
  have hbound := abs_quittingPunishmentValue_le_quittingRewardBound reward who
  rw [rewardBound_eq_zero] at hbound
  exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))

/-- Every player continues in the punishment suffix. -/
def punishment : ℕ → Bool → PMF Bool :=
  fun _ _ ↦ PMF.pure false

/-- The actual diffuse family underlying the regression. -/
def family : QuittingDiffuseStationaryPrefixFamily reward where
  error := rate
  root := root
  horizon := fun _ ↦ 2
  punished := fun _ ↦ true
  punishment := fun _ ↦ punishment
  error_pos := rate_pos
  error_tendsto_zero := rate_tendsto_zero
  horizon_gt_one := by simp
  punishmentWithin := by
    intro n hazard
    rw [rootSequenceHazardTerminalValue_eq_zero, punishmentValue_eq_zero]
    simpa using (rate_pos n).le
  nash := by
    intro n who hazard
    rw [rootSequenceHazardTerminalValue_eq_zero,
      rootSequenceTerminalValue_eq_zero]
    nlinarith [rate_pos n]
  live_pos := by
    intro n
    rw [stationaryContinueMass_root]
    exact div_pos (rate_pos n) (by norm_num)

theorem family_prefixJointSurvival (n : ℕ) :
    family.prefixJointSurvival n = (rate n / 2) ^ 3 := by
  unfold QuittingDiffuseStationaryPrefixFamily.prefixJointSurvival family
  rw [quittingJointSurvivalWeight_const, stationaryContinueMass_root]

theorem family_prefixDeletedSurvival_owner (n : ℕ) :
    family.prefixDeletedSurvival n true = 1 / 8 := by
  unfold QuittingDiffuseStationaryPrefixFamily.prefixDeletedSurvival family
    quittingOpponentSurvivalWeight
  have hmass : ∀ time,
      quittingFixedOpponentsContinueMass (fun _ ↦ root n) true time = 1 / 2 := by
    intro time
    exact deletedContinueMass_owner n
  simp_rw [hmass]
  norm_num

theorem family_prefixDeletedSurvival_spectator (n : ℕ) :
    family.prefixDeletedSurvival n false = (rate n) ^ 3 := by
  unfold QuittingDiffuseStationaryPrefixFamily.prefixDeletedSurvival family
    quittingOpponentSurvivalWeight
  have hmass : ∀ time,
      quittingFixedOpponentsContinueMass (fun _ ↦ root n) false time = rate n := by
    intro time
    exact deletedContinueMass_spectator n
  simp_rw [hmass]
  simp

theorem tendsto_family_prefixJointSurvival_zero :
    Tendsto family.prefixJointSurvival atTop (nhds 0) := by
  simpa using ((rate_tendsto_zero.div_const 2 |>.pow 3).congr'
    (Filter.Eventually.of_forall fun n ↦
      (family_prefixJointSurvival n).symm))

theorem tendsto_family_prefixDeletedSurvival_spectator_zero :
    Tendsto (fun n ↦ family.prefixDeletedSurvival n false) atTop (nhds 0) := by
  simpa using ((rate_tendsto_zero.pow 3).congr'
    (Filter.Eventually.of_forall fun n ↦
      (family_prefixDeletedSurvival_spectator n).symm))

/-- The regression is a literal unique-exceptional-owner source. -/
def source : QuittingUniqueExceptionalOwnerSource reward where
  family := family
  owner := true
  selected := id
  deletedLimit := 1 / 8
  selected_strictMono := strictMono_id
  deletedLimit_pos := by norm_num
  joint_tendsto_zero := by simpa using tendsto_family_prefixJointSurvival_zero
  ownerDeleted_tendsto := by
    have heq : (fun n ↦ family.prefixDeletedSurvival n true) =
        fun _ ↦ (1 / 8 : ℝ) := by
      funext n
      exact family_prefixDeletedSurvival_owner n
    simp [heq]
  otherDeleted_tendsto_zero := by
    intro other hother
    cases other with
    | false =>
        simpa using tendsto_family_prefixDeletedSurvival_spectator_zero
    | true => exact False.elim (hother rfl)

/-- Exact first-row mass of the exceptional owner's singleton coalition. -/
theorem rootCoalitionMass_owner (n : ℕ) :
    quittingRootCoalitionMass (root n) {true} = (1 - rate n) / 2 := by
  rw [quittingRootCoalitionMass_singleton_eq_opponentContinue_mul_quit]
  rw [show quittingStationaryContinueMass
      (Function.update (root n) true (PMF.pure false)) = 1 / 2 by
    exact deletedContinueMass_owner n]
  simp [root, ownerHazard]
  ring

theorem rootAbsorptionMass (n : ℕ) :
    quittingRootAbsorptionMass (root n) = 1 - rate n / 2 := by
  unfold quittingRootAbsorptionMass
  rw [stationaryContinueMass_root]

theorem normalizedSingletonMass_owner (n : ℕ) :
    quittingRootNormalizedSingletonMass (root n) true =
      ((1 - rate n) / 2) / (1 - rate n / 2) := by
  unfold quittingRootNormalizedSingletonMass
  rw [rootCoalitionMass_owner, rootAbsorptionMass]

theorem normalizedSingletonMass_owner_tendsto_half :
    Tendsto (fun n ↦ quittingRootNormalizedSingletonMass (root n) true)
      atTop (nhds (1 / 2)) := by
  have hnum : Tendsto (fun n ↦ (1 - rate n) / 2)
      atTop (nhds ((1 - 0) / 2)) :=
    (tendsto_const_nhds.sub rate_tendsto_zero).div_const 2
  have hden : Tendsto (fun n ↦ 1 - rate n / 2)
      atTop (nhds (1 - 0 / 2)) :=
    tendsto_const_nhds.sub (rate_tendsto_zero.div_const 2)
  have hquotient := hnum.div hden (by norm_num : (1 - 0 / 2 : ℝ) ≠ 0)
  simpa using (hquotient.congr'
    (Filter.Eventually.of_forall fun n ↦
      (normalizedSingletonMass_owner n).symm))

/-- The minimal one-row isolation field that turns repeated-prefix absorption
into the exceptional owner's singleton law. -/
def HasOwnerSingletonIsolation
    {κ : Type} [Fintype κ] [DecidableEq κ]
    {reward : {S : Finset κ // S.Nonempty} → Payoff κ}
    (source : QuittingUniqueExceptionalOwnerSource reward) : Prop :=
  Tendsto (fun n ↦ quittingRootNormalizedSingletonMass
    (source.family.root (source.selected n)) source.owner) atTop (nhds 1)

/-- The current unique-exceptional-owner source fields do not imply owner
isolation, even for an actual diffuse exact-Nash family. -/
theorem source_not_hasOwnerSingletonIsolation :
    ¬HasOwnerSingletonIsolation source := by
  intro hisolated
  have heq := tendsto_nhds_unique normalizedSingletonMass_owner_tendsto_half
    hisolated
  norm_num at heq

end ExceptionalOwnerSourceRegression
end GameTheory
