/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.StrictRayBindingCardinality
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSupportEntry

/-!
# Eliminate a singleton binding face on the strict Fin4 ray

If all Continue is the unique exact root at the limiting cap, the binding
singleton face cannot consist of one player.  A singleton binding coordinate
can be given an arbitrarily small positive solo Quit hazard.  Its endpoint
gain remains exactly zero because its cap is pinned to its singleton payoff,
while every nonbinding coordinate has a strict negative gain at hazard zero
and therefore remains negative for a sufficiently small positive hazard.
This produces a positive-absorption exact root at the limiting cap, contrary
to uniqueness.
-/

noncomputable section

namespace GameTheory

open Filter Math Math.Probability Set
open scoped Topology

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {returnSource : FinFourOwnerCompressedMinimumReturnForcedPairSource source}
variable {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}

/-- Under uniqueness of all Continue at the strict-ray limiting cap, the
binding singleton face cannot have cardinality one. -/
theorem bindingFinset_card_ne_one_of_unique_allContinue
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (hunique : HasUniqueAllContinueAtCapLimit flow) :
    flow.forward.bindingFinset.card ≠ 1 := by
  intro hcard
  obtain ⟨owner, hbinding⟩ := Finset.card_eq_one.mp hcard
  obtain ⟨anchor, hanchor⟩ :=
    Fintype.exists_ne_of_one_lt_card (by decide) owner
  have hne : owner ≠ anchor := hanchor.symm

  let gain : ℝ → Fin 4 → ℝ := fun rate who =>
    gainValue (weightOfReward reward)
      (quittingTwoOwnerHazard owner anchor rate 0)
      who (flow.forward.capLimit who)

  have hgainContinuous : ∀ who, Continuous (fun rate => gain rate who) := by
    intro who
    exact continuous_gainValue_twoOwner_firstHazard
      (reward := reward) flow.forward.capLimit owner anchor who hne

  have hzeroHazard :
      quittingTwoOwnerHazard owner anchor 0 0 =
        hazardOfRoot
          (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
    funext who
    simp [quittingTwoOwnerHazard, quittingTwoOwnerLeadingVariation,
      hazardOfRoot, quittingAllContinueRoot]

  have hgainZero : ∀ who,
      gain 0 who =
        reward (quittingSingletonTerminal who) who -
          flow.forward.capLimit who := by
    intro who
    dsimp only [gain]
    rw [hzeroHazard]
    rw [← quittingRootEndpointDifference_eq_gainValue
      reward flow.forward.capLimit
      (quittingAllContinueRoot : Fin 4 → PMF Bool) who]
    exact quittingRootEndpointDifference_allContinueRoot
      reward flow.forward.capLimit who

  have hownerMem : owner ∈ flow.forward.bindingFinset := by
    rw [hbinding]
    simp
  have hownerPin :
      flow.forward.capLimit owner =
        reward (quittingSingletonTerminal owner) owner := by
    simpa [QuittingForwardExactCapTail.bindingFinset] using hownerMem

  have hstrictAtZero : ∀ who, who ≠ owner → gain 0 who < 0 := by
    intro who hwho
    have hnotmem : who ∉ flow.forward.bindingFinset := by
      rw [hbinding]
      simpa [hwho]
    have hnotEq :
        flow.forward.capLimit who ≠
          reward (quittingSingletonTerminal who) who := by
      intro heq
      apply hnotmem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ who, heq⟩
    have hstrict :
        reward (quittingSingletonTerminal who) who <
          flow.forward.capLimit who :=
      lt_of_le_of_ne (flow.forward.singleton_le_capLimit who)
        (Ne.symm hnotEq)
    rw [hgainZero who]
    linarith

  have hstrictEventually : ∀ᶠ rate in 𝓝 (0 : ℝ),
      ∀ who, who ≠ owner → gain rate who < 0 := by
    rw [Filter.eventually_all]
    intro who
    by_cases hwho : who = owner
    · exact Filter.Eventually.of_forall fun _ hneWho =>
        (hneWho hwho).elim
    · exact ((hgainContinuous who).continuousAt.eventually_lt
        continuousAt_const (hstrictAtZero who hwho)).mono
          (fun _ hlt _ => hlt)
  have hltOne : ∀ᶠ rate in 𝓝 (0 : ℝ), rate < 1 :=
    continuousAt_id.eventually_lt continuousAt_const zero_lt_one
  have hpositiveEvent : ∀ᶠ rate : ℝ in 𝓝[>] (0 : ℝ),
      0 < rate := self_mem_nhdsWithin
  obtain ⟨rate, hproperties, hratePos⟩ :=
    ((((hstrictEventually.and hltOne).filter_mono
      nhdsWithin_le_nhds).and hpositiveEvent).exists)
  have hrateLt : rate < 1 := hproperties.2

  let hazard := quittingTwoOwnerHazard owner anchor rate 0
  have hhazardNonneg : ∀ who, 0 ≤ hazard who := by
    intro who
    by_cases hwho : who = owner
    · subst who
      simp [hazard, hratePos.le]
    · simp [hazard, quittingTwoOwnerHazard,
        quittingTwoOwnerLeadingVariation, hwho]
  have hhazardLeOne : ∀ who, hazard who ≤ 1 := by
    intro who
    by_cases hwho : who = owner
    · subst who
      simp [hazard, hrateLt.le]
    · simp [hazard, quittingTwoOwnerHazard,
        quittingTwoOwnerLeadingVariation, hwho]
  let root := rootOfHazard hazard hhazardNonneg hhazardLeOne

  have hownerGain :
      gainValue (weightOfReward reward) hazard owner
          (flow.forward.capLimit owner) = 0 := by
    rw [show hazard =
      quittingTwoOwnerHazard owner anchor rate 0 by rfl]
    rw [gainValue_twoOwner_first_fixedTail flow.forward.capLimit
      owner anchor rate 0 hne, hownerPin]
    ring

  have hcomplementary : IsExactRowComplementary hazard
      (fun who => gainValue (weightOfReward reward) hazard who
        (flow.forward.capLimit who)) := by
    intro who
    by_cases hwho : who = owner
    · subst who
      have hownerHazard : hazard owner = rate := by
        simp [hazard]
      rw [hownerHazard, hownerGain]
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
    · have hzero : hazard who = 0 := by
        simp [hazard, quittingTwoOwnerHazard,
          quittingTwoOwnerLeadingVariation, hwho]
      have hstrict :
          gainValue (weightOfReward reward) hazard who
              (flow.forward.capLimit who) < 0 := by
        simpa [gain, hazard] using hproperties.1 who hwho
      rw [hzero]
      exact ⟨fun hpos => (lt_irrefl 0 hpos).elim,
        fun _ => hstrict.le⟩

  have hnash :
      IsεQuittingRootNash reward flow.forward.capLimit 0 root := by
    apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward flow.forward.capLimit root).mp
    apply (isExactRowComplementary_hazardOfRoot_iff
      reward flow.forward.capLimit root).mp
    simpa [root, hazardOfRoot_rootOfHazard] using hcomplementary

  have hrootHazard : hazardOfRoot root = hazard :=
    hazardOfRoot_rootOfHazard hazard hhazardNonneg hhazardLeOne
  have hownerQuit : (root owner true).toReal = rate := by
    change hazardOfRoot root owner = rate
    rw [hrootHazard]
    simp [hazard]
  have hrootNe :
      root ≠ (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
    intro hroot
    have hzero : (root owner true).toReal = 0 := by
      rw [hroot]
      simp [quittingAllContinueRoot]
    linarith
  exact hrootNe (hunique root hnash)

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
