/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Chronology.StrictCovectorDynamicTail
import UniformEquilibrium.Diagnostics.Quitting.TightFaceCollisionSemanticDebt
import UniformEquilibrium.Quitting.Projective.PunishmentFloorNearReturn
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness

/-!
# Source adapters for tight-face collision escape

The strict separator on a canonical nonplateau tail supplies the finite
tight-face datum.  Separately, canonical prefix capacity supplies the finite
charge ceiling used to localize aggregate collision mass.  The final theorem
states the semantic debt excursion directly for an admissible relation path.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingPositiveDebtDynamicTailWitness

variable {witness : QuittingTerminalExploitabilityWitness reward}
variable (seam : QuittingPositiveDebtDynamicTailWitness witness)

omit [Nonempty ι] in
/-- The canonical nonplateau strict separator, packaged as the exact datum
consumed by finite tight-face collision escape. -/
theorem exists_tightFaceSeparatorData_of_no_uniformPayoff
    (hpositive : ∀ cutoff, ∃ time, cutoff ≤ time ∧
      0 < quittingRootAbsorptionMass
        (quittingDynamicDebtTailRoots seam.tail time))
    (hnoUE : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ data : TightFaceSeparatorData reward,
      data.boundary = seam.limit.value ∧
      data.owners = seam.tightOwnerFinset := by
  obtain ⟨covector, margin, hmargin, _hunit, hseparated⟩ :=
    seam.exists_strictCovector_on_tightOwners_of_no_uniformPayoff hnoUE
  have howners : seam.tightOwnerFinset.Nonempty := by
    letI := seam.tightOwner_nonempty_of_arbitrarilyLateAbsorption hpositive
    let owner : seam.TightOwner := Classical.choice inferInstance
    exact ⟨owner.1, owner.2⟩
  let data : TightFaceSeparatorData reward :=
    { boundary := seam.limit.value
      owners := seam.tightOwnerFinset
      owners_nonempty := howners
      covector := covector
      margin := margin
      margin_pos := hmargin
      separated := fun owner howner ↦ hseparated ⟨owner, howner⟩ }
  exact ⟨data, rfl, rfl⟩

end QuittingPositiveDebtDynamicTailWitness

namespace TightFaceSeparatorData

variable (data : TightFaceSeparatorData reward)

omit [Nonempty ι] in
/-- Canonical prefix capacity turns any positive aggregate collision lower
bound into the literal macroscopic collision edge of (10). -/
theorem exists_macroscopicCollision_of_collisionMass_lowerBound_canonical
    (witness : QuittingTerminalExploitabilityWitness reward)
    (path : QuittingPunishmentFloorFinitePrefix reward)
    {δ : ℝ} (hδ : 0 < δ) (hlower : δ ≤ data.pathCollisionMass path) :
    ∃ time, time < path.horizon ∧
      δ / quittingPunishmentFloorPrefixChargeBound reward ≤
        collisionFraction (path.roots time) ∧
      δ / quittingPunishmentFloorPrefixChargeBound reward /
          ((Fintype.card ι).choose 2 : ℝ) ≤
        quittingRootAbsorptionMass (path.roots time) ∧
      (δ / quittingPunishmentFloorPrefixChargeBound reward) ^ 2 /
          ((Fintype.card ι).choose 2 : ℝ) ≤
        quittingRootCollisionMass (path.roots time) := by
  have hcollisionCharge : data.pathCollisionMass path ≤ path.charge := by
    unfold pathCollisionMass QuittingPunishmentFloorFinitePrefix.charge
    exact Finset.sum_le_sum fun time _ ↦
      quittingRootCollisionMass_le_absorptionMass (path.roots time)
  have hbound := witness.prefixCharge_le path
  have hP : 0 < quittingPunishmentFloorPrefixChargeBound reward :=
    lt_of_lt_of_le hδ (hlower.trans (hcollisionCharge.trans hbound))
  exact data.exists_macroscopicCollision_of_collisionMass_lowerBound_charge_le
    path hδ hlower hP hbound

omit [Nonempty ι] in
/-- The canonical localization theorem applied directly to a decoded exact
punishment-floor admissible relation path. -/
theorem exists_macroscopicCollision_of_admissiblePath_collisionMassLowerBound
    (witness : QuittingTerminalExploitabilityWitness reward)
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      source target)
    {δ : ℝ} (hδ : 0 < δ)
    (hlower : δ ≤ data.pathCollisionMass
      (QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix path)) :
    ∃ time,
      time < (QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
        path).horizon ∧
      δ / quittingPunishmentFloorPrefixChargeBound reward ≤
        collisionFraction
          ((QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
            path).roots time) ∧
      δ / quittingPunishmentFloorPrefixChargeBound reward /
          ((Fintype.card ι).choose 2 : ℝ) ≤
        quittingRootAbsorptionMass
          ((QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
            path).roots time) ∧
      (δ / quittingPunishmentFloorPrefixChargeBound reward) ^ 2 /
          ((Fintype.card ι).choose 2 : ℝ) ≤
        quittingRootCollisionMass
          ((QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
            path).roots time) := by
  exact data.exists_macroscopicCollision_of_collisionMass_lowerBound_canonical
    witness _ hδ hlower

end TightFaceSeparatorData

namespace QuittingPunishmentFloorAdmissibleChargedRelation

/-- The semantic debt excursion (13), with the relation-path endpoint
coordinates and decoder identities discharged.  The semantic source lift is
still an explicit hypothesis: admissible relation data alone need not supply
one. -/
theorem minimumDebt_mul_tightFaceGap_le_sourceExcess
    (data : TightFaceSeparatorData reward)
    {sourceState targetState : QuittingPunishmentFloorAdmissibleState reward}
    (relationPath :
      (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
        sourceState targetState)
    (source minimum : QuittingTerminalSemanticPair ι)
    (hsourceCarrier : source ∈ quittingTerminalSemanticCarrier reward)
    (hsourceFst : source.1 = sourceState.1.1.1)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsupport : ∀ time,
      time < (pathToFinitePrefix relationPath).horizon → ∀ owner,
      0 < ((pathToFinitePrefix relationPath).roots time owner true).toReal →
        owner ∈ data.owners)
    (hlocal : ∀ time, time ≤ (pathToFinitePrefix relationPath).horizon →
      ∀ who, |(pathToFinitePrefix relationPath).value time who -
        data.boundary who| ≤ data.localRadius)
    {a : ℝ} (ha : 0 < a)
    (hhigh : ∃ time, time < (pathToFinitePrefix relationPath).horizon ∧
      a ≤ quittingRootAbsorptionMass
        ((pathToFinitePrefix relationPath).roots time))
    (hnear : ∀ who,
      |sourceState.1.1.1 who - targetState.1.1.1 who| ≤
        data.margin * a / (4 * data.covectorL1)) :
    quittingTerminalSemanticDebtSum minimum *
        (data.margin * a /
          (4 * data.rewardCeiling * data.covectorL1)) ≤
      quittingTerminalSemanticDebtSum source -
        quittingTerminalSemanticDebtSum minimum := by
  let path := pathToFinitePrefix relationPath
  have hzero : path.value 0 = sourceState.1.1.1 :=
    QuittingPunishmentFloorBoxPath.value_zero (pathToBoxPath relationPath)
  have hend : path.value path.horizon = targetState.1.1.1 := by
    exact pathToFinitePrefix_value_horizon relationPath
  apply path.minimumDebt_mul_tightFaceGap_le_sourceExcess data source minimum
    hsourceCarrier (hsourceFst.trans hzero.symm) hminimumCarrier hminimum
    hminimumPositive hsupport hlocal ha hhigh
  intro who
  rw [hzero, hend]
  exact hnear who

end QuittingPunishmentFloorAdmissibleChargedRelation

end GameTheory
