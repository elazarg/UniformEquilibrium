/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashFixedTailPrefixRay
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn

/-!
# Stopping-clock escape along a fixed-tail cap-Nash prefix ray

This module combines a positive joint-prefix survival limit with one
retained finite tail atom.  It proves exact marginal Never transport,
vanishing fixed finite coordinates, an exact total-variation limit, and a
uniform late-finite mass floor.  It claims no source, Fin4, Nash property of
the fixed tail, or uniform-equilibrium consumer.
-/

noncomputable section

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {terminal : (quittingGame reward).BehaviorProfile}

namespace QuittingFixedTailCapNashPrefixRay

variable (ray : QuittingFixedTailCapNashPrefixRay reward terminal)

/-- A fixed terminal stage atom is shifted by the prefix depth and scaled by
the exact joint Continue product. -/
theorem stageCoalitionMass_shift
    (depth time : ℕ) (coalition : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth)
        (depth + time) coalition =
      ray.continueProduct depth *
        quittingStageCoalitionMass reward terminal time coalition := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [quittingFixedTailCapNashPrefixProfile_succ,
        show depth + 1 + time = (depth + time) + 1 by omega,
        quittingStageCoalitionMass_rootThenContinuation_succ,
        ray.continueProduct_succ, ih]
      ring

/-- Product of one player's own Continue probabilities in the depth-`depth`
prefix. -/
def ownPrefixProduct (who : ι) (depth : ℕ) : ℝ :=
  quittingLiteralRootStackOwnSurvival (ray.rootStack depth) who

@[simp]
theorem ownPrefixProduct_zero (who : ι) : ray.ownPrefixProduct who 0 = 1 := rfl

@[simp]
theorem ownPrefixProduct_succ (who : ι) (depth : ℕ) :
    ray.ownPrefixProduct who (depth + 1) =
      (ray.roots depth who false).toReal * ray.ownPrefixProduct who depth := rfl

theorem ownPrefixProduct_nonneg (who : ι) (depth : ℕ) :
    0 ≤ ray.ownPrefixProduct who depth :=
  quittingLiteralRootStackOwnSurvival_nonneg (ray.rootStack depth) who

theorem ownPrefixProduct_le_one (who : ι) (depth : ℕ) :
    ray.ownPrefixProduct who depth ≤ 1 :=
  quittingLiteralRootStackOwnSurvival_le_one (ray.rootStack depth) who

theorem ownPrefixProduct_antitone (who : ι) :
    Antitone (ray.ownPrefixProduct who) := by
  apply antitone_nat_of_succ_le
  intro depth
  rw [ray.ownPrefixProduct_succ]
  have hroot : (ray.roots depth who false).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top
      ((ray.roots depth who).coe_le_one false)
  exact mul_le_of_le_one_left (ray.ownPrefixProduct_nonneg who depth) hroot

/-- Limit of one player's decreasing own-prefix Continue products. -/
def ownPrefixProductLimit (who : ι) : ℝ :=
  ⨅ depth, ray.ownPrefixProduct who depth

theorem ownPrefixProduct_tendsto_limit (who : ι) :
    Tendsto (ray.ownPrefixProduct who) atTop
      (nhds (ray.ownPrefixProductLimit who)) := by
  apply tendsto_atTop_ciInf (ray.ownPrefixProduct_antitone who)
  refine ⟨0, ?_⟩
  rintro _ ⟨depth, rfl⟩
  exact ray.ownPrefixProduct_nonneg who depth

theorem ownPrefixProductLimit_nonneg (who : ι) :
    0 ≤ ray.ownPrefixProductLimit who := by
  apply le_ciInf
  exact ray.ownPrefixProduct_nonneg who

theorem ownPrefixProductLimit_le_one (who : ι) :
    ray.ownPrefixProductLimit who ≤ 1 := by
  exact le_of_tendsto' (ray.ownPrefixProduct_tendsto_limit who)
    (ray.ownPrefixProduct_le_one who)

/-- Joint survival never exceeds one selected player's own survival. -/
theorem continueProduct_le_ownPrefixProduct (who : ι) (depth : ℕ) :
    ray.continueProduct depth ≤ ray.ownPrefixProduct who depth := by
  change quittingLiteralRootStackJointSurvival (ray.rootStack depth) ≤
    quittingLiteralRootStackOwnSurvival (ray.rootStack depth) who
  rw [quittingLiteralRootStackJointSurvival_eq_opponent_mul_own]
  exact mul_le_of_le_one_left
    (quittingLiteralRootStackOwnSurvival_nonneg (ray.rootStack depth) who)
    (quittingLiteralRootStackOpponentSurvival_le_one
      (ray.rootStack depth) who)

theorem continueProductLimit_le_ownPrefixProductLimit (who : ι) :
    ray.continueProductLimit ≤ ray.ownPrefixProductLimit who := by
  apply le_ciInf
  intro depth
  exact (ray.continueProductLimit_le depth).trans
    (ray.continueProduct_le_ownPrefixProduct who depth)

/-- Exact Never transport through every fixed-tail prefix. -/
theorem stoppingLaw_none_eq_ownPrefixProduct_mul (who : ι) (depth : ℕ) :
    (quittingBehaviorStoppingLaw reward
        ((quittingFixedTailCapNashPrefixProfile
          reward terminal ray.roots depth) who) none).toReal =
      ray.ownPrefixProduct who depth *
        (quittingBehaviorStoppingLaw reward (terminal who) none).toReal := by
  simpa [quittingFixedTailCapNashPrefixProfile,
    quittingReversePrefixProfile, ownPrefixProduct, rootStack] using
    (quittingBehaviorStoppingLaw_none_literalRootStackProfile_eq
      reward (ray.rootStack depth) terminal who)

/-- Limiting Never mass of the selected player's prefixed stopping laws. -/
def stoppingLawNeverLimit (who : ι) : ℝ :=
  ray.ownPrefixProductLimit who *
    (quittingBehaviorStoppingLaw reward (terminal who) none).toReal

theorem stoppingLaw_none_tendsto_limit (who : ι) :
    Tendsto
      (fun depth =>
        (quittingBehaviorStoppingLaw reward
          ((quittingFixedTailCapNashPrefixProfile
            reward terminal ray.roots depth) who) none).toReal)
      atTop (nhds (ray.stoppingLawNeverLimit who)) := by
  rw [show (fun depth =>
      (quittingBehaviorStoppingLaw reward
        ((quittingFixedTailCapNashPrefixProfile
          reward terminal ray.roots depth) who) none).toReal) =
      fun depth => ray.ownPrefixProduct who depth *
        (quittingBehaviorStoppingLaw reward (terminal who) none).toReal by
    funext depth
    exact ray.stoppingLaw_none_eq_ownPrefixProduct_mul who depth]
  exact (ray.ownPrefixProduct_tendsto_limit who).mul_const _

/-- Every fixed finite stopping coordinate vanishes under the positive debt
floor. -/
theorem stoppingLaw_finiteCoordinate_tendsto_zero
    (who : ι) {Dstar : ℝ} (hDstar : 0 < Dstar)
    (hfloor : ∀ depth, Dstar ≤ quittingTerminalDebtSum reward
      (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth))
    (time : ℕ) :
    Tendsto
      (fun depth =>
        (quittingBehaviorStoppingLaw reward
          ((quittingFixedTailCapNashPrefixProfile
            reward terminal ray.roots depth) who) (some time)).toReal)
      atTop (nhds 0) := by
  simpa [quittingFixedTailCapNashPrefixProfile] using
    (quittingReversePrefix_finiteCoordinate_tendsto_zero
      reward ray.roots (fun _ => terminal) who
      (ray.rootAbsorptionMass_tendsto_zero hDstar hfloor) time)

/-- Exact total-variation limit from every fixed stopping law. -/
theorem pmfGeneralTV_tendsto_one_sub_min
    (who : ι) {Dstar : ℝ} (hDstar : 0 < Dstar)
    (hfloor : ∀ depth, Dstar ≤ quittingTerminalDebtSum reward
      (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth))
    (fixed : PMF (Option ℕ)) :
    Tendsto
      (fun depth => pmfGeneralTV
        (quittingBehaviorStoppingLaw reward
          ((quittingFixedTailCapNashPrefixProfile
            reward terminal ray.roots depth) who)) fixed)
      atTop
      (nhds (1 - min (ray.stoppingLawNeverLimit who)
        (fixed none).toReal)) := by
  exact pmfGeneralTV_tendsto_one_sub_min_of_finiteCoordinates_tendsto_zero
    (fun depth => quittingBehaviorStoppingLaw reward
      ((quittingFixedTailCapNashPrefixProfile
        reward terminal ray.roots depth) who))
    fixed (ray.stoppingLawNeverLimit who)
    (ray.stoppingLaw_finiteCoordinate_tendsto_zero who hDstar hfloor)
    (ray.stoppingLaw_none_tendsto_limit who)

/-- Data of one positive coalition atom retained in the fixed behavioral
tail, together with one member whose stopping clock it forces. -/
structure RetainedStageAtom (who : ι) where
  time : ℕ
  coalition : {S : Finset ι // S.Nonempty}
  mass : ℝ
  mass_pos : 0 < mass
  mass_le : mass ≤
    quittingStageCoalitionMass reward terminal time coalition
  who_mem : who ∈ coalition.val

variable {ray}

theorem RetainedStageAtom.tailNever_le_one_sub_mass
    {who : ι}
    (atom : RetainedStageAtom (reward := reward) (terminal := terminal) who) :
    (quittingBehaviorStoppingLaw reward (terminal who) none).toReal ≤
      1 - atom.mass := by
  have hstageLe := quittingStageCoalitionMass_le_member_stoppingLaw
    terminal atom.time atom.coalition who atom.who_mem
  have hmassLe : atom.mass ≤
      (quittingBehaviorStoppingLaw reward
        (terminal who) (some atom.time)).toReal :=
    atom.mass_le.trans hstageLe
  let law := quittingBehaviorStoppingLaw reward (terminal who)
  have hne : (none : Option ℕ) ≠ some atom.time := by simp
  have hsum := (pmf_toReal_summable law).sum_le_tsum
    ({none, some atom.time} : Finset (Option ℕ))
    (fun _ _ => ENNReal.toReal_nonneg)
  rw [pmf_toReal_tsum_one law] at hsum
  simp only [Finset.sum_pair hne] at hsum
  dsimp only [law] at hsum
  linarith

theorem RetainedStageAtom.missingNeverMass_ge
    {who : ι}
    (atom : RetainedStageAtom (reward := reward) (terminal := terminal) who) :
    ray.continueProductLimit * atom.mass ≤
      1 - ray.stoppingLawNeverLimit who := by
  have htail := atom.tailNever_le_one_sub_mass
  have hp0 := ray.ownPrefixProductLimit_nonneg who
  have hp1 := ray.ownPrefixProductLimit_le_one who
  have hjoint := ray.continueProductLimit_le_ownPrefixProductLimit who
  have hmass0 := atom.mass_pos.le
  dsimp only [stoppingLawNeverLimit]
  nlinarith [mul_nonneg hp0 (sub_nonneg.mpr htail),
    mul_nonneg (sub_nonneg.mpr hp1) hmass0,
    mul_nonneg (sub_nonneg.mpr hjoint) hmass0]

theorem RetainedStageAtom.debtRatio_mul_mass_le_missingNeverMass
    {who : ι}
    (atom : RetainedStageAtom (reward := reward) (terminal := terminal) who)
    {Dstar : ℝ} (hDstar : 0 < Dstar)
    (hfloor : ∀ depth, Dstar ≤ quittingTerminalDebtSum reward
      (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth)) :
    Dstar / quittingTerminalDebtSum reward terminal * atom.mass ≤
      1 - ray.stoppingLawNeverLimit who :=
  (mul_le_mul_of_nonneg_right
      (ray.debtFloor_div_tailDebt_le_continueProductLimit hDstar hfloor)
      atom.mass_pos.le).trans atom.missingNeverMass_ge

theorem RetainedStageAtom.tvLimit_lower_chain
    {who : ι}
    (atom : RetainedStageAtom (reward := reward) (terminal := terminal) who)
    {Dstar : ℝ} (hDstar : 0 < Dstar)
    (hfloor : ∀ depth, Dstar ≤ quittingTerminalDebtSum reward
      (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth))
    (fixed : PMF (Option ℕ)) :
    Dstar / quittingTerminalDebtSum reward terminal * atom.mass ≤
      ray.continueProductLimit * atom.mass ∧
    ray.continueProductLimit * atom.mass ≤
      1 - ray.stoppingLawNeverLimit who ∧
    1 - ray.stoppingLawNeverLimit who ≤
      1 - min (ray.stoppingLawNeverLimit who) (fixed none).toReal := by
  exact ⟨mul_le_mul_of_nonneg_right
      (ray.debtFloor_div_tailDebt_le_continueProductLimit hDstar hfloor)
      atom.mass_pos.le,
    atom.missingNeverMass_ge,
    sub_le_sub_left (min_le_left _ _) 1⟩

/-- The retained tail atom yields a uniform late-finite stopping-mass floor
beyond every fixed horizon. -/
theorem RetainedStageAtom.eventually_debtRatio_mul_mass_le_lateFiniteMass
    {who : ι}
    (atom : RetainedStageAtom (reward := reward) (terminal := terminal) who)
    {Dstar : ℝ} (hDstar : 0 < Dstar)
    (hfloor : ∀ depth, Dstar ≤ quittingTerminalDebtSum reward
      (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth))
    (horizon : ℕ) :
    ∀ᶠ depth in atTop,
      Dstar / quittingTerminalDebtSum reward terminal * atom.mass ≤
        stoppingLawLateFiniteMass
          (quittingBehaviorStoppingLaw reward
            ((quittingFixedTailCapNashPrefixProfile
              reward terminal ray.roots depth) who)) horizon := by
  filter_upwards [eventually_gt_atTop horizon] with depth hdepth
  have hshift := ray.stageCoalitionMass_shift
    depth atom.time atom.coalition
  have hstageLe := quittingStageCoalitionMass_le_member_stoppingLaw
    (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth)
    (depth + atom.time) atom.coalition who atom.who_mem
  have hatomLe := stoppingLaw_atom_le_lateFiniteMass
    (quittingBehaviorStoppingLaw reward
      ((quittingFixedTailCapNashPrefixProfile
        reward terminal ray.roots depth) who))
    horizon (depth + atom.time) (by omega)
  have hproduct := ray.debtFloor_div_tailDebt_le_continueProduct
    hDstar hfloor depth
  calc
    Dstar / quittingTerminalDebtSum reward terminal * atom.mass ≤
        ray.continueProduct depth * atom.mass :=
      mul_le_mul_of_nonneg_right hproduct atom.mass_pos.le
    _ ≤ ray.continueProduct depth *
        quittingStageCoalitionMass reward terminal atom.time atom.coalition :=
      mul_le_mul_of_nonneg_left atom.mass_le
        (ray.continueProduct_nonneg depth)
    _ = quittingStageCoalitionMass reward
        (quittingFixedTailCapNashPrefixProfile
          reward terminal ray.roots depth)
        (depth + atom.time) atom.coalition := hshift.symm
    _ ≤ (quittingBehaviorStoppingLaw reward
          ((quittingFixedTailCapNashPrefixProfile
            reward terminal ray.roots depth) who)
          (some (depth + atom.time))).toReal := hstageLe
    _ ≤ stoppingLawLateFiniteMass
        (quittingBehaviorStoppingLaw reward
          ((quittingFixedTailCapNashPrefixProfile
            reward terminal ray.roots depth) who)) horizon := hatomLe

/-- No cofinal subsequence can converge in total variation to a fixed actual
stopping law. -/
theorem RetainedStageAtom.no_cofinal_pmfGeneralTV_convergent_subsequence
    {who : ι}
    (atom : RetainedStageAtom (reward := reward) (terminal := terminal) who)
    {Dstar : ℝ} (hDstar : 0 < Dstar)
    (hfloor : ∀ depth, Dstar ≤ quittingTerminalDebtSum reward
      (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth)) :
    ¬ ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      ∃ fixed : PMF (Option ℕ),
        Tendsto
          (fun index => pmfGeneralTV
            (quittingBehaviorStoppingLaw reward
              ((quittingFixedTailCapNashPrefixProfile reward terminal ray.roots
                (subsequence index)) who)) fixed)
          atTop (nhds 0) := by
  rintro ⟨subsequence, hmono, fixed, hzero⟩
  have hlimit := (ray.pmfGeneralTV_tendsto_one_sub_min
    who hDstar hfloor fixed).comp hmono.tendsto_atTop
  have heq : 1 - min (ray.stoppingLawNeverLimit who) (fixed none).toReal = 0 :=
    tendsto_nhds_unique hlimit hzero
  have hlower := atom.tvLimit_lower_chain hDstar hfloor fixed
  have htailPos : 0 < quittingTerminalDebtSum reward terminal := by
    simpa using hDstar.trans_le (hfloor 0)
  have hpositive :
      0 < Dstar / quittingTerminalDebtSum reward terminal * atom.mass :=
    mul_pos (div_pos hDstar htailPos) atom.mass_pos
  rw [heq] at hlower
  linarith [hlower.1, hlower.2.1, hlower.2.2]

end QuittingFixedTailCapNashPrefixRay

end GameTheory
