/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.SingletonBaseSameLawResetProducer
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargeBaseStationarySemanticHandoff

/-!
# Same-point singleton reset and repair paid chain on four players

The singleton-base same-law producer and the stationary owner-repair handoff
can use the same induced Nash point.  Thus one actual stationary source carries
the original paid row and fixed-law reset dispatch.  Replacing its sure-Quit
owner by Always Continue gives a second actual profile with a full-gap paid row
at a distinct free player.

This is a two-profile chain, not a fixed-law or chronological edge.  The
repaired profile is a literal unilateral replacement, but no declaration here
identifies its outcome law, semantic pair, or reset dispatch with the original
source data.  The handoff also records only a floor-admissible/free-underfloor
alternative for the repaired profile; it does not preserve every free-player
floor inequality.
-/

noncomputable section

namespace GameTheory

open Finset

/-- The `Fin 4` source profile is definitionally the generic singleton-base
profile at the same induced Nash point. -/
theorem finFourSingletonBaseProfile_eq_singletonBaseStationaryProfile
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4)
    (point : mixedPolytope
      (quittingBinaryForm (finFourSingletonBaseFree owner)).sig) :
    finFourSingletonBaseProfile reward owner point =
      quittingSingletonBaseStationaryProfile reward owner
        (finFourSingletonBaseFree owner) point := by
  rfl

/-- A source-native packet retaining the original same-law paid/reset data and
the paid row produced by the literal owner repair at the same Nash point.

The type deliberately keeps the repaired handoff separate from `producer`'s
`target_joint` and `dispatch`: no repaired-law or chronological alignment is
part of the packet. -/
structure FinFourSingletonBaseResetRepairPaidChain
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (owner : Fin 4) where
  producer : FinFourSingletonBaseSameLawResetProducer reward bound residual
    owner
  delta : ℝ
  delta_pos : 0 < delta
  owner_floor_excess : delta ≤
    quittingSingletonBaseOwnerFloorExcess reward owner
      (quittingPersistentBaseRoot {owner}
        (finFourSingletonBaseFree owner) producer.point)
  repair : QuittingSingletonBaseStationaryHandoff reward owner
    (finFourSingletonBaseFree owner) producer.point delta
      residual.witness.terminalGap

namespace FinFourSingletonBaseResetRepairPaidChain

/-- The second paid observer is a free player distinct from the original
singleton owner. -/
theorem repairedObserver_mem_free_ne_owner
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
    {owner : Fin 4}
    (chain : FinFourSingletonBaseResetRepairPaidChain reward bound residual
      owner) :
    chain.repair.outsideDebtor ∈ finFourSingletonBaseFree owner ∧
      chain.repair.outsideDebtor ≠ owner :=
  ⟨chain.repair.outsideDebtor_mem_free,
    chain.repair.outsideDebtor_ne_owner⟩

/-- The repair profile is exactly the unilateral Always-Continue replacement
of the original source owner. -/
theorem repairedProfile_eq_ownerAlwaysContinueUpdate
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
    {owner : Fin 4}
    (chain : FinFourSingletonBaseResetRepairPaidChain reward bound residual
      owner) :
    quittingSingletonBaseRepairedProfile reward owner
        (finFourSingletonBaseFree owner) chain.producer.point =
      Function.update
        (finFourSingletonBaseProfile reward owner chain.producer.point)
        owner (quittingAlwaysContinueStrategy reward owner) := by
  rw [finFourSingletonBaseProfile_eq_singletonBaseStationaryProfile]
  exact (update_quittingSingletonBaseStationaryProfile_owner_alwaysContinue
    reward owner (finFourSingletonBaseFree owner)
      chain.producer.point).symm

/-- The packet exposes a full-gap paid row both before and after the owner
repair, with distinct observers.  The profiles in the two rows are not claimed
to have the same law. -/
theorem paidRows_before_and_after
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
    {owner : Fin 4}
    (chain : FinFourSingletonBaseResetRepairPaidChain reward bound residual
      owner) :
    Nonempty (QuittingPaidFirstDisagreementRow reward
        (finFourSingletonBaseProfile reward owner chain.producer.point)
        owner residual.witness.terminalGap) ∧
      Nonempty (QuittingPaidFirstDisagreementRow reward
        (quittingSingletonBaseRepairedProfile reward owner
          (finFourSingletonBaseFree owner) chain.producer.point)
        chain.repair.outsideDebtor residual.witness.terminalGap) :=
  ⟨chain.producer.paid_row, chain.repair.paid_row⟩

end FinFourSingletonBaseResetRepairPaidChain

/-- Every existing same-law singleton producer extends, at its already chosen
Nash point, to the literal repair paid chain. -/
theorem FinFourSingletonBaseSameLawResetProducer.nonempty_resetRepairPaidChain
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
    {owner : Fin 4}
    (producer : FinFourSingletonBaseSameLawResetProducer reward bound residual
      owner) :
    Nonempty (FinFourSingletonBaseResetRepairPaidChain reward bound residual
      owner) := by
  obtain ⟨delta, hdeltaPos, hdelta⟩ :=
    residual.witness.exists_pos_ownerFloorExcess_gap owner
      (finFourSingletonBaseFree owner) rfl
  have hpointLower := hdelta producer.point producer.point_mem
  have hrepair := exists_singletonBaseStationaryHandoff reward owner
    (finFourSingletonBaseFree owner) rfl producer.point producer.point_mem
      residual.witness hdeltaPos hpointLower
  obtain ⟨repair⟩ := hrepair
  exact ⟨{
    producer := producer
    delta := delta
    delta_pos := hdeltaPos
    owner_floor_excess := hpointLower
    repair := repair }⟩

/-- Source-free existence form: the quantitative hard residual selects one
actual singleton source carrying both the same-law reset data and its literal
repair paid chain. -/
theorem FinFourQuantitativeFullSupportHardResidual.nonempty_resetRepairPaidChain
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (owner : Fin 4) :
    Nonempty (FinFourSingletonBaseResetRepairPaidChain reward bound residual
      owner) := by
  obtain ⟨producer⟩ := residual.nonempty_singletonBaseSameLawResetProducer
    hreward owner
  exact producer.nonempty_resetRepairPaidChain

end GameTheory
