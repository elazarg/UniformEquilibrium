/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.SupportThreeFourSignGraph
import UniformEquilibrium.Quitting.Classification.AbnormalSingletonConsequences

/-!
# Normality dispatch for support-three packets

On four players, a support-three terminal packet has a precise dichotomy.
Either every player is punishment-normal, or the unique unsupported player is
abnormal.  In the latter case the abnormal singleton floor forbids a crossed
row through that outsider, so the checked support-three sign dispatch must
enter its internal cyclic branch.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A four-player support-three terminal packet is either all-normal or has
the checked internal cyclic sign screen.  This is the strongest conclusion
available from singleton crossed rows and abnormal floors alone. -/
theorem QuittingTerminalExploitabilityWitness.supportThree_allNormal_or_cyclicSignScreen
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hplayers : Fintype.card ι = 4)
    (hsupport : packet.support.card = 3) :
    (∀ who, IsQuittingNormalPlayer reward who) ∨
      Nonempty (QuittingSupportThreeCyclicSignScreen packet) := by
  by_cases hallNormal : ∀ who, IsQuittingNormalPlayer reward who
  · exact Or.inl hallNormal
  · right
    push Not at hallNormal
    obtain ⟨abnormal, habnormalNot⟩ := hallNormal
    have habnormal : IsQuittingAbnormalPlayer reward abnormal :=
      lt_of_not_ge habnormalNot
    have habnormalOutside : abnormal ∉ packet.support := by
      intro habnormalMem
      exact habnormalNot
        (packet.isQuittingNormalPlayer_of_mass_pos abnormal
          ((packet.mem_support_iff abnormal).mp habnormalMem))
    obtain ⟨outsider, houtside, hcyclic | hcrossing⟩ :=
      witness.supportThree_cyclicSignScreen_or_outsiderCrossing
        packet hplayers hsupport
    · exact hcyclic
    · obtain ⟨owner, row, hharmed⟩ := hcrossing
      have habnormalCompl : abnormal ∈ packet.supportᶜ :=
        Finset.mem_compl.mpr habnormalOutside
      rw [houtside] at habnormalCompl
      have habnormalEq : abnormal = outsider := by simpa using habnormalCompl
      have hharmedAbnormal : row.harmed = abnormal :=
        hharmed.trans habnormalEq.symm
      have hownerNe : abnormal ≠ owner := by
        rw [← hharmedAbnormal]
        exact row.harmed_ne_owner
      obtain ⟨hsoloFloor, hownerFloor⟩ :=
        abnormal_singletonFloor_chain reward habnormal hownerNe
      have hcrossing' : quittingSoloReward reward owner abnormal <
          quittingSoloReward reward abnormal abnormal := by
        rw [← hharmedAbnormal]
        simpa only [quittingSoloReward, quittingSingletonTerminal] using
          row.singleton_crossing.1
      exfalso
      linarith

end GameTheory
