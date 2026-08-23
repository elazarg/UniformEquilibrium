/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Chronology.TightFaceCollisionEscapeAdapters
import UniformEquilibrium.Diagnostics.Quitting.PaidFirstDisagreementPayoffNearReturn

/-!
# Tight-face restriction on paid payoff near-return families

This is a necessary-condition adapter, not a producer.  Every supplied
positive-charge payoff near-return family has a decoded path which either
leaves the local payoff ball, activates a Quit owner outside the separated
face, or contains a nonperturbative collision row.
-/

noncomputable section

namespace GameTheory

open Math.Probability
open QuittingPunishmentFloorAdmissibleChargedRelation

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingPositiveAdmissiblePayoffNearReturnFamily

omit [Nonempty ι] in
/-- Every positive-charge admissible payoff near-return family crosses one
of the three tight-face escape arms.  The source, path, and arm may depend on
the family, exactly as allowed by the checked near-return consumer. -/
theorem exists_tightFace_escape
    (family : QuittingPositiveAdmissiblePayoffNearReturnFamily reward)
    (data : TightFaceSeparatorData reward) :
    ∃ (source target : QuittingPunishmentFloorAdmissibleState reward)
      (relationPath :
        (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
          source target),
      (∀ who, |source.1.1.1 who - target.1.1.1 who| ≤
        data.margin * family.chargeThreshold / (4 * data.covectorL1)) ∧
      (0 < relationPath.highChargeCount family.chargeThreshold) ∧
      ((∃ time, time ≤ (QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
            relationPath).horizon ∧
          ∃ who, data.localRadius <
            |(QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
              relationPath).value time who -
                data.boundary who|) ∨
       (∃ time, time < (QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
            relationPath).horizon ∧
          ∃ owner, 0 < ((QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
              relationPath).roots time owner true).toReal ∧
            owner ∉ data.owners) ∨
       (∃ time, time < (QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
            relationPath).horizon ∧
          data.collisionFractionCeiling <
            TightFaceSeparatorData.collisionFraction
              ((QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
                relationPath).roots time))) := by
  have herror : 0 < data.margin * family.chargeThreshold /
      (4 * data.covectorL1) := by
    exact div_pos (mul_pos data.margin_pos family.charge_pos)
      (mul_pos (by norm_num) data.covectorL1_pos)
  obtain ⟨source, target, relationPath, hnear, hhighCount⟩ :=
    family.nearReturn _ herror
  refine ⟨source, target, relationPath, hnear, hhighCount, ?_⟩
  let path :=
    QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
      relationPath
  by_contra hnone
  push Not at hnone
  have hlocal : ∀ time, time ≤ path.horizon → ∀ who,
      |path.value time who - data.boundary who| ≤ data.localRadius := by
    intro time htime who
    simpa only [path] using hnone.1 time htime who
  have hsupport : ∀ time, time < path.horizon → ∀ owner,
      0 < (path.roots time owner true).toReal → owner ∈ data.owners := by
    intro time htime owner howner
    simpa only [path] using hnone.2.1 time htime owner howner
  have hcollision : ∀ time, time < path.horizon →
      TightFaceSeparatorData.collisionFraction (path.roots time) ≤
        data.collisionFractionCeiling := by
    intro time htime
    simpa only [path] using hnone.2.2 time htime
  have hhigh :=
    decodedPathHasChargeAtLeast_of_highChargeCount_pos
      relationPath family.chargeThreshold hhighCount
  have hpair := data.path_halfMargin_lowerBound_of_collisionFraction_le
    path hsupport hlocal hcollision
  have hcharge : family.chargeThreshold ≤ path.charge := by
    obtain ⟨time, htime, hmass⟩ := hhigh
    unfold QuittingPunishmentFloorFinitePrefix.charge
    exact hmass.trans <| Finset.single_le_sum
      (fun stage _ ↦ quittingRootAbsorptionMass_nonneg (path.roots stage))
      (Finset.mem_range.2 htime)
  have hzero : path.value 0 = source.1.1.1 :=
    QuittingPunishmentFloorBoxPath.value_zero
      (QuittingPunishmentFloorAdmissibleChargedRelation.pathToBoxPath
        relationPath)
  have hend : path.value path.horizon = target.1.1.1 := by
    exact
      QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_value_horizon
        relationPath
  have hcoordinate : ∀ who,
      |path.value 0 who - path.value path.horizon who| ≤
        data.margin * family.chargeThreshold / (4 * data.covectorL1) := by
    intro who
    rw [hzero, hend]
    exact hnear who
  have habs := abs_quittingCovectorPairing_le data.covector
    (path.value 0 - path.value path.horizon)
    hcoordinate
  have hupper := (le_abs_self _).trans habs
  have hL := data.covectorL1_pos
  have hsimplify : data.covectorL1 *
      (data.margin * family.chargeThreshold / (4 * data.covectorL1)) =
        data.margin * family.chargeThreshold / 4 := by
    field_simp [hL.ne']
  change quittingCovectorPairing data.covector
      (path.value 0 - path.value path.horizon) ≤ data.covectorL1 *
        (data.margin * family.chargeThreshold / (4 * data.covectorL1)) at hupper
  rw [hsimplify] at hupper
  have hlower : data.margin / 2 * family.chargeThreshold ≤
      quittingCovectorPairing data.covector
        (path.value 0 - path.value path.horizon) :=
    (mul_le_mul_of_nonneg_left hcharge (by linarith [data.margin_pos])).trans
      hpair
  nlinarith [data.margin_pos, family.charge_pos]

end QuittingPositiveAdmissiblePayoffNearReturnFamily

end GameTheory
