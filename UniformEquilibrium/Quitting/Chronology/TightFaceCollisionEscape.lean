/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorAdmissibleChargedRelation
import UniformEquilibrium.Quitting.Chronology.StrictCovectorRootStep
import UniformEquilibrium.Quitting.Cycles.CollisionAwareFiniteReturn

/-!
# Tight-face collision escape on finite exact quitting paths

A singleton-row separator is strictly monotone on every local exact Bellman
edge whose active Quit owners stay in its face, up to the literal mass of
simultaneous quitting.  The estimate retains the exact product-law collision
term and telescopes over arbitrary finite punishment-floor paths.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A nonempty singleton face and one strict covector separator on all of its
literal singleton reward columns. -/
structure TightFaceSeparatorData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  boundary : Payoff ι
  owners : Finset ι
  owners_nonempty : owners.Nonempty
  covector : Payoff ι
  margin : ℝ
  margin_pos : 0 < margin
  separated : ∀ owner ∈ owners,
    margin ≤ quittingCovectorPairing covector (fun who ↦
      boundary who - reward (quittingSingletonTerminal owner) who)

namespace TightFaceSeparatorData

variable (data : TightFaceSeparatorData reward)

/-- The `ℓ¹` size of the separator. -/
def covectorL1 : ℝ := ∑ who, |data.covector who|

/-- A reward ceiling bounded below by one. -/
def rewardCeiling (_data : TightFaceSeparatorData reward) : ℝ :=
  max 1 (quittingRewardBound reward)

/-- Local payoff radius used by the collision escape theorem. -/
def localRadius : ℝ := data.margin / (4 * data.covectorL1)

/-- Conditional-collision ceiling used by the collision-light corollary. -/
def collisionFractionCeiling : ℝ :=
  min (1 / 2) (data.margin / (8 * data.rewardCeiling * data.covectorL1))

/-- Conditional collision share, defined as zero on a zero-absorption root. -/
def collisionFraction (root : ι → PMF Bool) : ℝ :=
  if quittingRootAbsorptionMass root = 0 then 0
  else quittingRootCollisionMass root / quittingRootAbsorptionMass root

omit [Nonempty ι] [DecidableEq ι] in
theorem covectorL1_pos : 0 < data.covectorL1 := by
  obtain ⟨owner, howner⟩ := data.owners_nonempty
  have hseparator := data.separated owner howner
  by_contra hnot
  have hzero : data.covectorL1 = 0 :=
    le_antisymm (le_of_not_gt hnot) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
  have hcoordinate : ∀ who, data.covector who = 0 := by
    intro who
    have hle : |data.covector who| ≤ data.covectorL1 := by
      exact Finset.single_le_sum (fun other _ ↦ abs_nonneg (data.covector other))
        (Finset.mem_univ who)
    have habs : |data.covector who| = 0 :=
      le_antisymm (hle.trans_eq hzero) (abs_nonneg _)
    exact abs_eq_zero.mp habs
  unfold quittingCovectorPairing at hseparator
  simp_rw [hcoordinate, zero_mul] at hseparator
  simp at hseparator
  exact (not_lt_of_ge hseparator) data.margin_pos

omit [Nonempty ι] [DecidableEq ι] in
theorem rewardCeiling_pos : 0 < data.rewardCeiling := by
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

omit [Nonempty ι] [DecidableEq ι] in
theorem reward_abs_le_ceiling (terminal player) :
    |reward terminal player| ≤ data.rewardCeiling :=
  (abs_reward_le_quittingRewardBound reward terminal player).trans
    (le_max_right _ _)

/-- Total probability of singleton absorption at one product root. -/
def singletonMass (_data : TightFaceSeparatorData reward)
    (root : ι → PMF Bool) : ℝ :=
  ∑ owner, quittingRootCoalitionMass root {owner}

/-- Canonical singleton weights, with a fixed face owner used only when the
root has no singleton mass. -/
def singletonWeight (root : ι → PMF Bool) (owner : ι) : ℝ :=
  if _h : 0 < data.singletonMass root then
    quittingRootCoalitionMass root {owner} / data.singletonMass root
  else if owner = data.owners_nonempty.choose then 1 else 0

omit [Nonempty ι] in
theorem singletonMass_nonneg (root : ι → PMF Bool) :
    0 ≤ data.singletonMass root :=
  Finset.sum_nonneg fun owner _ ↦
    MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {owner}

omit [Nonempty ι] in
theorem singletonWeight_nonneg (root : ι → PMF Bool) (owner : ι) :
    0 ≤ data.singletonWeight root owner := by
  unfold singletonWeight
  split_ifs with hpos heq
  · exact div_nonneg
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {owner})
      hpos.le
  · norm_num
  · norm_num

omit [Nonempty ι] in
theorem sum_singletonWeight (root : ι → PMF Bool) :
    ∑ owner, data.singletonWeight root owner = 1 := by
  unfold singletonWeight
  split_ifs with hpos
  · rw [← Finset.sum_div]
    exact div_self hpos.ne'
  · simp

omit [Nonempty ι] in
theorem singletonWeight_support
    (root : ι → PMF Bool)
    (hsupport : ∀ owner,
      0 < (root owner true).toReal → owner ∈ data.owners)
    (owner : ι) (hweight : 0 < data.singletonWeight root owner) :
    owner ∈ data.owners := by
  unfold singletonWeight at hweight
  split_ifs at hweight with hmass heq
  · apply hsupport owner
    apply QuittingFiniteRootWindow.quitProbability_pos_of_singletonCoalitionMass_pos
    have hdenom : 0 < data.singletonMass root := hmass
    rcases (div_pos_iff.mp hweight) with hpositive | hnegative
    · exact hpositive.1
    · exact (not_lt_of_ge hdenom.le hnegative.2).elim
  · simpa [heq] using data.owners_nonempty.choose_spec
  · norm_num at hweight

/-- Singleton reward mixture selected by the canonical weights. -/
def singletonRewardMixture (root : ι → PMF Bool) : Payoff ι := fun who ↦
  ∑ owner, data.singletonWeight root owner *
    reward (quittingSingletonTerminal owner) who

omit [Nonempty ι] in
theorem abs_singletonRewardMixture_le (root : ι → PMF Bool) (who : ι) :
    |data.singletonRewardMixture root who| ≤ data.rewardCeiling := by
  calc
    |data.singletonRewardMixture root who| ≤
        ∑ owner, |data.singletonWeight root owner *
          reward (quittingSingletonTerminal owner) who| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ owner, data.singletonWeight root owner *
        |reward (quittingSingletonTerminal owner) who| := by
      apply Finset.sum_congr rfl
      intro owner _
      rw [abs_mul, abs_of_nonneg (data.singletonWeight_nonneg root owner)]
    _ ≤ ∑ owner, data.singletonWeight root owner * data.rewardCeiling := by
      apply Finset.sum_le_sum
      intro owner _
      exact mul_le_mul_of_nonneg_left (data.reward_abs_le_ceiling _ _)
        (data.singletonWeight_nonneg root owner)
    _ = data.rewardCeiling := by
      rw [← Finset.sum_mul, data.sum_singletonWeight, one_mul]

omit [Nonempty ι] in
/-- The raw singleton reward contribution factors through the selected
singleton mixture, including the zero-singleton-mass branch. -/
theorem singletonContribution_eq_mass_mul_mixture
    (root : ι → PMF Bool) (who : ι) :
    (∑ owner, quittingRootCoalitionMass root {owner} *
        reward (quittingSingletonTerminal owner) who) =
      data.singletonMass root * data.singletonRewardMixture root who := by
  by_cases hmass : 0 < data.singletonMass root
  · unfold singletonRewardMixture singletonWeight
    simp only [dif_pos hmass]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro owner _
    field_simp [hmass.ne']
  · have hzero : data.singletonMass root = 0 :=
      le_antisymm (le_of_not_gt hmass) (data.singletonMass_nonneg root)
    have hcoordinate : ∀ owner, quittingRootCoalitionMass root {owner} = 0 := by
      intro owner
      have hle : quittingRootCoalitionMass root {owner} ≤ data.singletonMass root :=
        Finset.single_le_sum
          (fun other _ ↦
            MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {other})
          (Finset.mem_univ owner)
      exact le_antisymm (hle.trans_eq hzero)
        (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {owner})
    rw [hzero, zero_mul]
    simp_rw [hcoordinate, zero_mul]
    simp

omit [Nonempty ι] in
/-- Exact absorption split in the notation of this module. -/
theorem absorptionMass_eq_singletonMass_add_collisionMass
    (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root =
      data.singletonMass root + quittingRootCollisionMass root := by
  simpa only [singletonMass] using
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root

omit [Nonempty ι] in
theorem absorptionMass_mul_collisionFraction (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root * collisionFraction root =
      quittingRootCollisionMass root := by
  unfold collisionFraction
  split_ifs with hzero
  · rw [hzero, zero_mul]
    exact le_antisymm
      (quittingRootCollisionMass_nonneg root)
      (quittingRootCollisionMass_le_absorptionMass root |>.trans_eq hzero)
  · exact mul_div_cancel₀ _ hzero

omit [Nonempty ι] in
theorem collisionFraction_nonneg (root : ι → PMF Bool) :
    0 ≤ collisionFraction root := by
  unfold collisionFraction
  split_ifs
  · norm_num
  · exact div_nonneg (quittingRootCollisionMass_nonneg root)
      (quittingRootAbsorptionMass_nonneg root)

omit [Nonempty ι] in
/-- Exact collision-aware decomposition of one Bellman drift around the
selected singleton mixture. -/
theorem bellmanDrift_eq_singletonDrift_sub_collisionError
    (tail current : Payoff ι) (root : ι → PMF Bool)
    (hbellman : current = quittingRootSuccessorPayoff reward tail root) :
    tail - current = fun who ↦
      quittingRootAbsorptionMass root *
          (tail who - data.singletonRewardMixture root who) -
        (QuittingFiniteRootWindow.rootCollisionRewardContribution
            reward root who - quittingRootCollisionMass root *
              data.singletonRewardMixture root who) := by
  funext who
  have hsuccessor :=
    quittingRootExpectedPayoff_eq_absorbingContribution_add reward tail root who
  change quittingRootSuccessorPayoff reward tail root who = _ at hsuccessor
  rw [← congrFun hbellman who] at hsuccessor
  have habsorbing :=
    QuittingFiniteRootWindow.quittingRootAbsorbingContribution_eq_singleton_add_collision
      reward root who
  have hsingleton := data.singletonContribution_eq_mass_mul_mixture root who
  have hsplit := data.absorptionMass_eq_singletonMass_add_collisionMass root
  simp only [Pi.sub_apply]
  calc
    tail who - current who =
        tail who - (data.singletonMass root *
            data.singletonRewardMixture root who +
          QuittingFiniteRootWindow.rootCollisionRewardContribution
            reward root who +
          quittingStationaryContinueMass root * tail who) := by
      rw [hsuccessor, habsorbing, hsingleton]
    _ = (1 - quittingStationaryContinueMass root) * tail who -
        data.singletonMass root * data.singletonRewardMixture root who -
        QuittingFiniteRootWindow.rootCollisionRewardContribution
          reward root who := by ring
    _ = quittingRootAbsorptionMass root *
          (tail who - data.singletonRewardMixture root who) -
        (QuittingFiniteRootWindow.rootCollisionRewardContribution
            reward root who - quittingRootCollisionMass root *
              data.singletonRewardMixture root who) := by
      unfold quittingRootAbsorptionMass at hsplit ⊢
      rw [hsplit]
      ring

omit [Nonempty ι] in
/-- Collision reward minus collision mass times any bounded singleton mixture
has coordinate size at most twice the reward ceiling times collision mass. -/
theorem abs_collisionError_le (root : ι → PMF Bool) (who : ι) :
    |QuittingFiniteRootWindow.rootCollisionRewardContribution reward root who -
        quittingRootCollisionMass root * data.singletonRewardMixture root who| ≤
      2 * data.rewardCeiling * quittingRootCollisionMass root := by
  have hcollision :=
    QuittingFiniteRootWindow.abs_rootCollisionRewardContribution_le
      reward root who data.reward_abs_le_ceiling
  have hmass := quittingRootCollisionMass_nonneg root
  calc
    |_ - _| ≤
        |QuittingFiniteRootWindow.rootCollisionRewardContribution reward root who| +
          |quittingRootCollisionMass root * data.singletonRewardMixture root who| :=
      abs_sub _ _
    _ ≤ data.rewardCeiling * quittingRootCollisionMass root +
        quittingRootCollisionMass root * data.rewardCeiling := by
      gcongr
      rw [abs_mul, abs_of_nonneg hmass]
      exact mul_le_mul_of_nonneg_left
        (data.abs_singletonRewardMixture_le root who) hmass
    _ = 2 * data.rewardCeiling * quittingRootCollisionMass root := by ring

omit [Nonempty ι] in
/-- One local exact Bellman edge pays the strict singleton separator, up to
its literal simultaneous-quitter mass. -/
theorem local_bellmanDrift_pairing_le
    (tail current : Payoff ι) (root : ι → PMF Bool)
    (hbellman : current = quittingRootSuccessorPayoff reward tail root)
    (hsupport : ∀ owner,
      0 < (root owner true).toReal → owner ∈ data.owners)
    (hlocal : ∀ who,
      |tail who - data.boundary who| ≤ data.localRadius) :
    3 * data.margin / 4 * quittingRootAbsorptionMass root -
        2 * data.rewardCeiling * data.covectorL1 *
          quittingRootCollisionMass root ≤
      quittingCovectorPairing data.covector (tail - current) := by
  let weight := data.singletonWeight root
  have hweight0 : ∀ owner, 0 ≤ weight owner :=
    data.singletonWeight_nonneg root
  have hweightSum : (∑ owner, weight owner) = 1 := data.sum_singletonWeight root
  have hseparator : data.margin ≤ quittingCovectorPairing data.covector
      (fun who ↦ data.boundary who - data.singletonRewardMixture root who) := by
    apply strictSeparator_le_singletonMixturePairing reward data.boundary
      data.covector weight hweight0 hweightSum
    intro owner howner
    exact data.separated owner
      (data.singletonWeight_support root hsupport owner howner)
  change data.margin ≤ quittingCovectorPairing data.covector
    (data.boundary - data.singletonRewardMixture root) at hseparator
  have hboundaryError :
      |quittingCovectorPairing data.covector (tail - data.boundary)| ≤
        data.covectorL1 * data.localRadius := by
    apply abs_quittingCovectorPairing_le
    intro who
    simpa only [Pi.sub_apply] using hlocal who
  have hmain : 3 * data.margin / 4 ≤
      quittingCovectorPairing data.covector
        (tail - data.singletonRewardMixture root) := by
    have hdecompose : quittingCovectorPairing data.covector
        (tail - data.singletonRewardMixture root) =
      quittingCovectorPairing data.covector
          (data.boundary - data.singletonRewardMixture root) +
        quittingCovectorPairing data.covector (tail - data.boundary) := by
      unfold quittingCovectorPairing
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro who _
      simp only [Pi.sub_apply]
      ring
    have herrorLower := neg_le_of_abs_le hboundaryError
    rw [hdecompose]
    have hLpos := data.covectorL1_pos
    have hproduct : data.covectorL1 * data.localRadius = data.margin / 4 := by
      unfold localRadius
      field_simp [hLpos.ne']
    linarith
  let error : Payoff ι := fun who ↦
    QuittingFiniteRootWindow.rootCollisionRewardContribution reward root who -
      quittingRootCollisionMass root * data.singletonRewardMixture root who
  have herrorPairing :
      |quittingCovectorPairing data.covector error| ≤
        data.covectorL1 *
          (2 * data.rewardCeiling * quittingRootCollisionMass root) := by
    apply abs_quittingCovectorPairing_le
    exact data.abs_collisionError_le root
  have hidentity := data.bellmanDrift_eq_singletonDrift_sub_collisionError
    tail current root hbellman
  have hpairIdentity : quittingCovectorPairing data.covector (tail - current) =
      quittingRootAbsorptionMass root *
          quittingCovectorPairing data.covector
            (tail - data.singletonRewardMixture root) -
        quittingCovectorPairing data.covector error := by
    rw [hidentity]
    unfold quittingCovectorPairing error
    simp only [Pi.sub_apply]
    simp_rw [mul_sub]
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro who _
    ring
  have hQ := quittingRootAbsorptionMass_nonneg root
  have hscaled := mul_le_mul_of_nonneg_left hmain hQ
  have herrorUpper := (le_abs_self _).trans herrorPairing
  rw [hpairIdentity]
  nlinarith

/-- Total literal collision mass of a finite exact prefix. -/
def pathCollisionMass (_data : TightFaceSeparatorData reward)
    (path : QuittingPunishmentFloorFinitePrefix reward) : ℝ :=
  ∑ time ∈ Finset.range path.horizon,
    quittingRootCollisionMass (path.roots time)

omit [Nonempty ι] in
theorem pathCollisionMass_nonneg
    (path : QuittingPunishmentFloorFinitePrefix reward) :
    0 ≤ data.pathCollisionMass path :=
  Finset.sum_nonneg fun _time _ ↦ quittingRootCollisionMass_nonneg _

omit [Nonempty ι] in
private theorem sum_pairing_consecutive
    (path : QuittingPunishmentFloorFinitePrefix reward) :
    (∑ time ∈ Finset.range path.horizon,
      quittingCovectorPairing data.covector
        (path.value time - path.value (time + 1))) =
      quittingCovectorPairing data.covector
        (path.value 0 - path.value path.horizon) := by
  have htelescope : ∀ length,
      (∑ time ∈ Finset.range length,
        quittingCovectorPairing data.covector
          (path.value time - path.value (time + 1))) =
        quittingCovectorPairing data.covector
          (path.value 0 - path.value length) := by
    intro length
    induction length with
    | zero => simp [quittingCovectorPairing]
    | succ length ih =>
        rw [Finset.sum_range_succ, ih]
        unfold quittingCovectorPairing
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro who _
        simp only [Pi.sub_apply]
        ring
  exact htelescope path.horizon

omit [Nonempty ι] in
/-- **Finite-path tight-face collision estimate.**  This is the exact
arbitrary-horizon telescope with literal product-law collision mass. -/
theorem path_pairing_lowerBound
    (path : QuittingPunishmentFloorFinitePrefix reward)
    (hsupport : ∀ time, time < path.horizon → ∀ owner,
      0 < (path.roots time owner true).toReal → owner ∈ data.owners)
    (hlocal : ∀ time, time ≤ path.horizon → ∀ who,
      |path.value time who - data.boundary who| ≤ data.localRadius) :
    3 * data.margin / 4 * path.charge -
        2 * data.rewardCeiling * data.covectorL1 *
          data.pathCollisionMass path ≤
      quittingCovectorPairing data.covector
        (path.value 0 - path.value path.horizon) := by
  have hsum := Finset.sum_le_sum fun time (htime : time ∈
      Finset.range path.horizon) ↦
    data.local_bellmanDrift_pairing_le
      (path.value time) (path.value (time + 1)) (path.roots time)
      (path.policy time (Finset.mem_range.1 htime))
      (hsupport time (Finset.mem_range.1 htime))
      (hlocal time (Nat.le_of_lt (Finset.mem_range.1 htime)))
  rw [data.sum_pairing_consecutive path] at hsum
  unfold QuittingPunishmentFloorFinitePrefix.charge pathCollisionMass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact hsum

omit [Nonempty ι] in
/-- Collision-light rows leave a strict half-margin charge telescope.  The
input is the division-free form of the conditional collision cap. -/
theorem path_halfMargin_lowerBound
    (path : QuittingPunishmentFloorFinitePrefix reward)
    (hsupport : ∀ time, time < path.horizon → ∀ owner,
      0 < (path.roots time owner true).toReal → owner ∈ data.owners)
    (hlocal : ∀ time, time ≤ path.horizon → ∀ who,
      |path.value time who - data.boundary who| ≤ data.localRadius)
    (hcollision : ∀ time, time < path.horizon →
      2 * data.rewardCeiling * data.covectorL1 *
          quittingRootCollisionMass (path.roots time) ≤
        data.margin / 4 *
          quittingRootAbsorptionMass (path.roots time)) :
    data.margin / 2 * path.charge ≤
      quittingCovectorPairing data.covector
        (path.value 0 - path.value path.horizon) := by
  have hpath := data.path_pairing_lowerBound path hsupport hlocal
  have hcollisionSum := Finset.sum_le_sum fun time (htime : time ∈
      Finset.range path.horizon) ↦
    hcollision time (Finset.mem_range.1 htime)
  unfold QuittingPunishmentFloorFinitePrefix.charge at hpath ⊢
  unfold pathCollisionMass at hpath
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hcollisionSum
  linarith

omit [Nonempty ι] in
/-- The packet's explicit conditional-collision ceiling implies the
division-free hypothesis of `path_halfMargin_lowerBound`. -/
theorem path_halfMargin_lowerBound_of_collisionFraction_le
    (path : QuittingPunishmentFloorFinitePrefix reward)
    (hsupport : ∀ time, time < path.horizon → ∀ owner,
      0 < (path.roots time owner true).toReal → owner ∈ data.owners)
    (hlocal : ∀ time, time ≤ path.horizon → ∀ who,
      |path.value time who - data.boundary who| ≤ data.localRadius)
    (hcollision : ∀ time, time < path.horizon →
      collisionFraction (path.roots time) ≤
        data.collisionFractionCeiling) :
    data.margin / 2 * path.charge ≤
      quittingCovectorPairing data.covector
        (path.value 0 - path.value path.horizon) := by
  apply data.path_halfMargin_lowerBound path hsupport hlocal
  intro time htime
  let root := path.roots time
  have hfraction := hcollision time htime
  have hceiling : data.collisionFractionCeiling ≤
      data.margin / (8 * data.rewardCeiling * data.covectorL1) :=
    min_le_right _ _
  have hfractionBound := hfraction.trans hceiling
  have hQ := quittingRootAbsorptionMass_nonneg root
  have hB := data.rewardCeiling_pos
  have hL := data.covectorL1_pos
  have hCQ := mul_le_mul_of_nonneg_left hfractionBound hQ
  change collisionFraction root ≤ _ at hfractionBound
  rw [absorptionMass_mul_collisionFraction] at hCQ
  have hfactor : 0 ≤ 2 * data.rewardCeiling * data.covectorL1 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hCQ hfactor
  have heq :
      (2 * data.rewardCeiling * data.covectorL1) *
          (quittingRootAbsorptionMass root *
            (data.margin / (8 * data.rewardCeiling * data.covectorL1))) =
        data.margin / 4 * quittingRootAbsorptionMass root := by
    field_simp [hB.ne', hL.ne']
    ring
  rw [heq] at hscaled
  simpa only [mul_assoc] using hscaled

omit [Nonempty ι] in
/-- A high-absorption edge on a collision-light local path forces a fixed
endpoint displacement in some coordinate. -/
theorem exists_endpointDisplacement_ge_of_highAbsorption
    (path : QuittingPunishmentFloorFinitePrefix reward)
    (hsupport : ∀ time, time < path.horizon → ∀ owner,
      0 < (path.roots time owner true).toReal → owner ∈ data.owners)
    (hlocal : ∀ time, time ≤ path.horizon → ∀ who,
      |path.value time who - data.boundary who| ≤ data.localRadius)
    (hcollision : ∀ time, time < path.horizon →
      2 * data.rewardCeiling * data.covectorL1 *
          quittingRootCollisionMass (path.roots time) ≤
        data.margin / 4 *
          quittingRootAbsorptionMass (path.roots time))
    {a : ℝ} (ha : 0 < a)
    (hhigh : ∃ time, time < path.horizon ∧
      a ≤ quittingRootAbsorptionMass (path.roots time)) :
    ∃ who, data.margin * a / (2 * data.covectorL1) ≤
      |path.value 0 who - path.value path.horizon who| := by
  have hcharge : a ≤ path.charge := by
    obtain ⟨time, htime, hmass⟩ := hhigh
    unfold QuittingPunishmentFloorFinitePrefix.charge
    exact hmass.trans <| Finset.single_le_sum
      (fun stage _ ↦ quittingRootAbsorptionMass_nonneg (path.roots stage))
      (Finset.mem_range.2 htime)
  have hpair := data.path_halfMargin_lowerBound path hsupport hlocal hcollision
  by_contra hnone
  push Not at hnone
  have hL := data.covectorL1_pos
  have hmargin := data.margin_pos
  have hcoordinate : ∃ who, 0 < |data.covector who| := by
    by_contra hzero
    push Not at hzero
    have : data.covectorL1 = 0 := by
      unfold covectorL1
      apply Finset.sum_eq_zero
      intro who _
      exact le_antisymm (hzero who) (abs_nonneg _)
    linarith
  obtain ⟨marked, hmarked⟩ := hcoordinate
  have habsStrict :
      |quittingCovectorPairing data.covector
        (path.value 0 - path.value path.horizon)| <
        data.covectorL1 *
          (data.margin * a / (2 * data.covectorL1)) := by
    calc
      |quittingCovectorPairing data.covector
          (path.value 0 - path.value path.horizon)| ≤
          ∑ who, |data.covector who *
          (path.value 0 who - path.value path.horizon who)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ < ∑ who, |data.covector who| *
          (data.margin * a / (2 * data.covectorL1)) := by
        apply Finset.sum_lt_sum
        · intro who _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hnone who).le (abs_nonneg _)
        · exact ⟨marked, Finset.mem_univ marked, by
            rw [abs_mul]
            exact mul_lt_mul_of_pos_left (hnone marked) hmarked⟩
      _ = _ := by
        unfold covectorL1
        rw [Finset.sum_mul]
  have hpairUpper := (le_abs_self _).trans_lt habsStrict
  have hchargeScaled : data.margin / 2 * a ≤
      data.margin / 2 * path.charge :=
    mul_le_mul_of_nonneg_left hcharge (by linarith [data.margin_pos])
  have hscaled : data.margin / 2 * a ≤
      quittingCovectorPairing data.covector
        (path.value 0 - path.value path.horizon) := by
    exact hchargeScaled.trans hpair
  have hsimplify : data.covectorL1 *
      (data.margin * a / (2 * data.covectorL1)) = data.margin * a / 2 := by
    field_simp [hL.ne']
  rw [hsimplify] at hpairUpper
  linarith

omit [Nonempty ι] in
/-- Endpoint proximity plus one high edge forces a fixed aggregate collision
budget, without any rowwise collision assumption. -/
theorem collisionMass_lowerBound_of_highAbsorption_nearReturn
    (path : QuittingPunishmentFloorFinitePrefix reward)
    (hsupport : ∀ time, time < path.horizon → ∀ owner,
      0 < (path.roots time owner true).toReal → owner ∈ data.owners)
    (hlocal : ∀ time, time ≤ path.horizon → ∀ who,
      |path.value time who - data.boundary who| ≤ data.localRadius)
    {a : ℝ} (ha : 0 < a)
    (hhigh : ∃ time, time < path.horizon ∧
      a ≤ quittingRootAbsorptionMass (path.roots time))
    (hnear : ∀ who,
      |path.value 0 who - path.value path.horizon who| ≤
        data.margin * a / (4 * data.covectorL1)) :
    data.margin * a /
        (4 * data.rewardCeiling * data.covectorL1) ≤
      data.pathCollisionMass path := by
  have hpath := data.path_pairing_lowerBound path hsupport hlocal
  have hcharge : a ≤ path.charge := by
    obtain ⟨time, htime, hmass⟩ := hhigh
    unfold QuittingPunishmentFloorFinitePrefix.charge
    exact hmass.trans <| Finset.single_le_sum
      (fun stage _ ↦ quittingRootAbsorptionMass_nonneg (path.roots stage))
      (Finset.mem_range.2 htime)
  have habs := abs_quittingCovectorPairing_le data.covector
    (path.value 0 - path.value path.horizon)
    (bound := data.margin * a / (4 * data.covectorL1)) (fun who ↦ by
      simpa only [Pi.sub_apply] using hnear who)
  have hupperRaw := (le_abs_self _).trans habs
  have hL := data.covectorL1_pos
  have hB := data.rewardCeiling_pos
  have hupper : quittingCovectorPairing data.covector
      (path.value 0 - path.value path.horizon) ≤ data.margin * a / 4 := by
    calc
      _ ≤ data.covectorL1 *
          (data.margin * a / (4 * data.covectorL1)) := by
        simpa only [covectorL1] using hupperRaw
      _ = data.margin * a / 4 := by
        field_simp [hL.ne']
  have hchargeScaled : 3 * data.margin / 4 * a ≤
      3 * data.margin / 4 * path.charge :=
    mul_le_mul_of_nonneg_left hcharge (by linarith [data.margin_pos])
  have hcollisionScaled : data.margin * a ≤
      4 * data.rewardCeiling * data.covectorL1 *
        data.pathCollisionMass path := by
    nlinarith
  rw [div_le_iff₀ (mul_pos (mul_pos (by norm_num) hB) hL)]
  nlinarith

omit [Nonempty ι] in
/-- A positive aggregate collision budget localized under a finite charge
ceiling yields one edge with macroscopic conditional collision, absorption,
and literal collision mass.  This is the packet's pigeonhole step (10). -/
theorem exists_macroscopicCollision_of_collisionMass_lowerBound_charge_le
    (path : QuittingPunishmentFloorFinitePrefix reward)
    {δ P : ℝ} (hδ : 0 < δ)
    (hlower : δ ≤ data.pathCollisionMass path)
    (hP : 0 < P) (hcharge : path.charge ≤ P) :
    ∃ time, time < path.horizon ∧
      δ / P ≤ collisionFraction (path.roots time) ∧
      δ / P / ((Fintype.card ι).choose 2 : ℝ) ≤
        quittingRootAbsorptionMass (path.roots time) ∧
      (δ / P) ^ 2 / ((Fintype.card ι).choose 2 : ℝ) ≤
        quittingRootCollisionMass (path.roots time) := by
  let γ := δ / P
  have hγ : 0 < γ := div_pos hδ hP
  have hcollisionPos : 0 < data.pathCollisionMass path := hδ.trans_le hlower
  have hmarked : ∃ time ∈ Finset.range path.horizon,
      0 < quittingRootCollisionMass (path.roots time) := by
    rw [pathCollisionMass, Finset.sum_pos_iff_of_nonneg] at hcollisionPos
    · exact hcollisionPos
    · exact fun time _ ↦ quittingRootCollisionMass_nonneg (path.roots time)
  have hratio : ∃ time, time < path.horizon ∧
      γ ≤ collisionFraction (path.roots time) := by
    by_contra hnone
    push Not at hnone
    obtain ⟨marked, hmarkedMem, hmarkedPos⟩ := hmarked
    have hsumStrict : data.pathCollisionMass path < γ * path.charge := by
      unfold pathCollisionMass QuittingPunishmentFloorFinitePrefix.charge
      calc
        (∑ time ∈ Finset.range path.horizon,
            quittingRootCollisionMass (path.roots time)) <
            ∑ time ∈ Finset.range path.horizon,
              γ * quittingRootAbsorptionMass (path.roots time) := by
          apply Finset.sum_lt_sum
          · intro time htime
            have hQ := quittingRootAbsorptionMass_nonneg (path.roots time)
            have hfrac := (hnone time (Finset.mem_range.1 htime)).le
            calc
              quittingRootCollisionMass (path.roots time) =
                  quittingRootAbsorptionMass (path.roots time) *
                    collisionFraction (path.roots time) :=
                (absorptionMass_mul_collisionFraction _).symm
              _ ≤ quittingRootAbsorptionMass (path.roots time) * γ :=
                mul_le_mul_of_nonneg_left hfrac hQ
              _ = _ := mul_comm _ _
          · refine ⟨marked, hmarkedMem, ?_⟩
            have hQ : 0 < quittingRootAbsorptionMass (path.roots marked) :=
              hmarkedPos.trans_le
                (quittingRootCollisionMass_le_absorptionMass _)
            calc
              quittingRootCollisionMass (path.roots marked) =
                  quittingRootAbsorptionMass (path.roots marked) *
                    collisionFraction (path.roots marked) :=
                (absorptionMass_mul_collisionFraction _).symm
              _ < quittingRootAbsorptionMass (path.roots marked) * γ :=
                mul_lt_mul_of_pos_left
                  (hnone marked (Finset.mem_range.1 hmarkedMem)) hQ
              _ = _ := mul_comm _ _
        _ = γ * ∑ time ∈ Finset.range path.horizon,
            quittingRootAbsorptionMass (path.roots time) := by
          rw [Finset.mul_sum]
        _ = _ := rfl
    have hupper : γ * path.charge ≤ δ := by
      calc
        γ * path.charge ≤ γ * P :=
          mul_le_mul_of_nonneg_left hcharge hγ.le
        _ = δ := by
          dsimp [γ]
          field_simp [hP.ne']
    linarith
  obtain ⟨time, htime, hfraction⟩ := hratio
  let root := path.roots time
  let pairs : ℝ := ((Fintype.card ι).choose 2 : ℝ)
  have hQnonneg := quittingRootAbsorptionMass_nonneg root
  have hQpos : 0 < quittingRootAbsorptionMass root := by
    by_contra hzero
    have hQzero : quittingRootAbsorptionMass root = 0 :=
      le_antisymm (le_of_not_gt hzero) hQnonneg
    have hfzero : collisionFraction root = 0 := by simp [collisionFraction, hQzero]
    rw [hfzero] at hfraction
    linarith
  have hγQ : γ * quittingRootAbsorptionMass root ≤
      quittingRootCollisionMass root := by
    rw [← absorptionMass_mul_collisionFraction root]
    nlinarith
  have hCpos : 0 < quittingRootCollisionMass root :=
    (mul_pos hγ hQpos).trans_le hγQ
  have hpairBound : quittingRootCollisionMass root ≤
      pairs * quittingRootAbsorptionMass root ^ 2 := by
    simpa only [pairs, Nat.cast_ofNat] using
      quittingRootCollisionMass_le_choose_card_mul_absorption_sq root
  have hpairs : 0 < pairs := by
    by_contra hpairsNonpos
    have hpairsLe : pairs ≤ 0 := le_of_not_gt hpairsNonpos
    have : quittingRootCollisionMass root ≤ 0 :=
      hpairBound.trans (mul_nonpos_of_nonpos_of_nonneg hpairsLe (sq_nonneg _))
    linarith
  have hQlower : γ / pairs ≤ quittingRootAbsorptionMass root := by
    rw [div_le_iff₀ hpairs]
    nlinarith
  have hClower : γ ^ 2 / pairs ≤ quittingRootCollisionMass root := by
    rw [div_le_iff₀ hpairs]
    have hchain : γ * (γ / pairs) ≤ quittingRootCollisionMass root :=
      (mul_le_mul_of_nonneg_left hQlower hγ.le).trans hγQ
    have hscaled := mul_le_mul_of_nonneg_right hchain hpairs.le
    field_simp [hpairs.ne'] at hscaled
    nlinarith
  exact ⟨time, htime, hfraction, hQlower, hClower⟩

omit [Nonempty ι] in
/-- Combining the tight-face collision lower bound with a finite charge
ceiling gives the explicit localized collision edge stated in (10). -/
theorem exists_macroscopicCollision_of_highAbsorption_nearReturn
    (path : QuittingPunishmentFloorFinitePrefix reward)
    (hsupport : ∀ time, time < path.horizon → ∀ owner,
      0 < (path.roots time owner true).toReal → owner ∈ data.owners)
    (hlocal : ∀ time, time ≤ path.horizon → ∀ who,
      |path.value time who - data.boundary who| ≤ data.localRadius)
    {a P : ℝ} (ha : 0 < a)
    (hhigh : ∃ time, time < path.horizon ∧
      a ≤ quittingRootAbsorptionMass (path.roots time))
    (hnear : ∀ who,
      |path.value 0 who - path.value path.horizon who| ≤
        data.margin * a / (4 * data.covectorL1))
    (hP : 0 < P) (hcharge : path.charge ≤ P) :
    ∃ time, time < path.horizon ∧
      (data.margin * a / (4 * data.rewardCeiling * data.covectorL1)) / P ≤
        collisionFraction (path.roots time) ∧
      (data.margin * a / (4 * data.rewardCeiling * data.covectorL1)) / P /
          ((Fintype.card ι).choose 2 : ℝ) ≤
        quittingRootAbsorptionMass (path.roots time) ∧
      ((data.margin * a / (4 * data.rewardCeiling * data.covectorL1)) / P) ^ 2 /
          ((Fintype.card ι).choose 2 : ℝ) ≤
        quittingRootCollisionMass (path.roots time) := by
  have hlower := data.collisionMass_lowerBound_of_highAbsorption_nearReturn
    path hsupport hlocal ha hhigh hnear
  have hδ : 0 < data.margin * a /
      (4 * data.rewardCeiling * data.covectorL1) := by
    exact div_pos (mul_pos data.margin_pos ha)
      (mul_pos (mul_pos (by norm_num) data.rewardCeiling_pos)
        data.covectorL1_pos)
  exact data.exists_macroscopicCollision_of_collisionMass_lowerBound_charge_le
    path hδ hlower hP hcharge

end TightFaceSeparatorData

end GameTheory
