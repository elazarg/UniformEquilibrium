/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.NormalTerminalGapFullSupportLift
import UniformEquilibrium.Quitting.Classification.LCP.HomogeneousProducer
import UniformEquilibrium.Quitting.Stationary.ApproximabilityCompactification

/-!
# Compact limit in the normal terminal-gap full-support lift

This module closes the compactness and first-order product-law part of the
normal terminal-gap lift.  Its input is a literal family of stationary product
roots.  The endpoint sign is the exact consequence needed from the constrained
stationary Nash construction once no hazard is equal to one.

The proof uses the checked `10 M H` comparison between endpoint differences
and normalized singleton-LCP residuals.  Thus all simultaneous-quitting terms
are retained at finite scale and disappear only through the proved finite
product estimate as total hazard tends to zero.
-/

noncomputable section

namespace GameTheory

open Filter Math.LinearProgramming Math.Probability Math.Topology
open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- A singleton-LCP residual is continuous in its simplex argument. -/
theorem continuous_singletonLCPResidual_simplex
    (matrix : ι → ι → ℝ) (who : ι) :
    Continuous (fun mass : stdSimplex ℝ ι =>
      singletonLCPResidual matrix mass who) := by
  unfold singletonLCPResidual wsum dotProduct
  apply continuous_finsetSum
  intro owner _
  exact ((continuous_apply owner).comp continuous_subtype_val).mul continuous_const

omit [Nonempty ι] in
/-- For the normalized solo matrix, a nonnegative residual is exactly the
singleton-mixture floor at the corresponding player. -/
theorem solo_le_singletonMixture_of_normalizedSoloResidual_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : stdSimplex ℝ ι) (who : ι)
    (hresidual : 0 ≤ singletonLCPResidual
      (normalizedSoloMatrix reward) mass who) :
    reward (quittingSingletonTerminal who) who ≤
      quittingSingletonMixture reward mass.val who := by
  let root := homogeneousScaledRoot mass (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have htotal : quittingStationaryTotalHazard root = 1 / 2 := by
    exact quittingStationaryTotalHazard_homogeneousScaledRoot
      mass (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have htotalPos : 0 < quittingStationaryTotalHazard root := by
    rw [htotal]
    norm_num
  have hdirection :
      quittingStationaryHazardDirection root htotalPos = mass := by
    ext owner
    change (quittingStationaryHazardDirection root htotalPos).val owner =
      mass.val owner
    rw [quittingStationaryHazardDirection_apply, htotal]
    dsimp only [root]
    rw [homogeneousScaledRoot_true_toReal]
    norm_num
  have hidentity :=
    singletonLCPResidual_normalizedSoloMatrix_hazardDirection
      reward root htotalPos who
  rw [hdirection] at hidentity
  have hbarycenter :=
    quittingStationarySingletonDirectionBarycenter_homogeneousScaledRoot
      reward mass (scale := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num) who
  change quittingStationarySingletonDirectionBarycenter reward root who =
    quittingSingletonMixture reward mass.val who at hbarycenter
  rw [hbarycenter] at hidentity
  rw [quittingSoloReward_eq_singletonTerminal] at hidentity
  linarith

/-- **Source-native compact-limit bridge.**  Suppose literal stationary
product roots approach the all-Continue apex.  Assume every normalized hazard
coordinate stays above one fixed positive floor, and every player's exact
Quit-versus-Continue endpoint difference is nonpositive.  Then the normalized
hazard directions have a compact limit which gives a literal full-support
normalized singleton source packet.

The endpoint sign is deliberately stated on the actual stationary terminal
payoff, rather than packaged as a supplied packet or an artificial candidate.
It is the remaining output of the constrained stationary Nash producer after
the terminal gap makes all hazards small. -/
theorem exists_fullSupport_normalizedSingletonSourcePacket_of_vanishingRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {floor : ℝ}
    (hfloor : 0 < floor)
    (hpositive : ∀ n, 0 < quittingStationaryTotalHazard (roots n))
    (hhalf : ∀ n, quittingStationaryTotalHazard (roots n) ≤ 1 / 2)
    (hvanish : Tendsto
      (fun n => quittingStationaryTotalHazard (roots n)) atTop (nhds 0))
    (hdirectionFloor : ∀ n who, floor ≤
      (quittingStationaryHazardDirection (roots n) (hpositive n)).val who)
    (hendpoint : ∀ n who,
      quittingRootEndpointDifference reward
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward (roots n)) player)
          (roots n) who ≤ 0)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who) :
    ∃ packet : QuittingNormalizedSingletonSourcePacket reward,
      packet.support = Finset.univ ∧
      ∀ who, floor ≤ packet.mass who := by
  let direction : ℕ → stdSimplex ℝ ι := fun n =>
    quittingStationaryHazardDirection (roots n) (hpositive n)
  obtain ⟨mass, subsequence, hsubsequence, hmassLimit⟩ :=
    CompactSpace.tendsto_subseq direction
  have hsubsequenceAtTop : Tendsto subsequence atTop atTop :=
    hsubsequence.tendsto_atTop
  have hhazardLimit : Tendsto
      (fun n => quittingStationaryTotalHazard (roots (subsequence n)))
      atTop (nhds 0) :=
    hvanish.comp hsubsequenceAtTop
  have hmassFloor : ∀ who, floor ≤ mass.val who := by
    intro who
    have hcoordinate : Tendsto
        (fun n => (direction (subsequence n)).val who)
        atTop (nhds (mass.val who)) :=
      (((continuous_apply who).comp continuous_subtype_val).tendsto mass).comp
        hmassLimit
    exact ge_of_tendsto' hcoordinate fun n =>
      hdirectionFloor (subsequence n) who
  have hresidual : ∀ who, 0 ≤ singletonLCPResidual
      (normalizedSoloMatrix reward) mass who := by
    intro who
    let residual : stdSimplex ℝ ι → ℝ := fun candidate =>
      singletonLCPResidual (normalizedSoloMatrix reward) candidate who
    have hresidualLimit : Tendsto
        (fun n => residual (direction (subsequence n))) atTop
        (nhds (residual mass)) :=
      ((continuous_singletonLCPResidual_simplex
        (normalizedSoloMatrix reward) who).tendsto mass).comp hmassLimit
    have hlower : ∀ n,
        -(10 * quittingRewardBound reward *
            quittingStationaryTotalHazard (roots (subsequence n))) ≤
          residual (direction (subsequence n)) := by
      intro n
      have hclose :=
        abs_quittingRootEndpointDifference_add_singletonLCPResidual_le
          reward (abs_reward_le_quittingRewardBound reward)
          (roots (subsequence n)) who (hpositive (subsequence n))
          (hhalf (subsequence n))
      have hlowerClose := (abs_le.mp hclose).1
      have hsign := hendpoint (subsequence n) who
      dsimp only [residual, direction]
      linarith
    have hlowerLimit : Tendsto
        (fun n => -(10 * quittingRewardBound reward *
          quittingStationaryTotalHazard (roots (subsequence n))))
        atTop (nhds 0) := by
      convert hhazardLimit.const_mul (-(10 * quittingRewardBound reward)) using 1
      · funext n
        ring
      · ring_nf
    exact le_of_tendsto_of_tendsto hlowerLimit hresidualLimit
      (Filter.Eventually.of_forall hlower)
  have hmixture : ∀ who,
      reward (quittingSingletonTerminal who) who ≤
        quittingSingletonMixture reward mass.val who := fun who =>
    solo_le_singletonMixture_of_normalizedSoloResidual_nonneg
      reward mass who (hresidual who)
  let packet := normalFullSupportSingletonPacket reward mass.val
    mass.property.1 mass.property.2 hnormal hmixture
  refine ⟨packet, ?_, ?_⟩
  · dsimp only [packet]
    exact normalFullSupportSingletonPacket_support_eq_univ reward mass.val
      mass.property.1 mass.property.2 (fun who => hfloor.trans_le (hmassFloor who))
      hnormal hmixture
  · intro who
    exact hmassFloor who

end GameTheory
