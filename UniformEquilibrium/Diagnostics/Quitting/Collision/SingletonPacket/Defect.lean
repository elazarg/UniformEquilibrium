/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.Surplus
import UniformEquilibrium.Quitting.Classification.SingletonPacketDefect

/-!
# Uniform packet defect in a terminal exploitability witness

The generic compact coordinate model and continuous defect live in
`Quitting.Classification.SingletonPacketDefect`.  This adapter proves that a
terminal exploitability witness makes the defect pointwise positive, obtains one
positive margin over every normalized packet, and converts that margin into
a uniform refusal advantage.

These are finite packet restrictions.  They do not identify packet mass with
the occupation law of a late dynamic-debt window.
-/

noncomputable section

namespace GameTheory

open Finset Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- In a terminal exploitability witness, the defect is positive at every raw packet. -/
theorem quittingNormalizedSingletonPacketDefect_pos
    (witness : QuittingTerminalExploitabilityWitness reward)
    (data : QuittingNormalizedSingletonPacketData ι)
    (hdata : data ∈ quittingNormalizedSingletonPacketDataSet reward) :
    0 < @quittingNormalizedSingletonPacketDefect ι _
      witness.nonempty_players reward data := by
  letI : Nonempty ι := witness.nonempty_players
  let packet := quittingNormalizedSingletonSourcePacketOfData data hdata
  obtain ⟨owner, hmass, hsurplus⟩ :=
    witness.exists_active_strictSingletonSurplus packet
  have hterm : 0 < data.1 owner *
      (quittingSingletonMixture reward data.1 owner - data.2 owner) :=
    mul_pos hmass (sub_pos.mpr hsurplus)
  exact hterm.trans_le (Finset.le_sup'
    (f := fun who ↦ data.1 who *
      (quittingSingletonMixture reward data.1 who - data.2 who))
    (Finset.mem_univ owner))

namespace QuittingTerminalExploitabilityWitness

/-- **Uniform packet-defect margin.** One positive number works for every
normalized singleton packet of the fixed counterexample reward table. -/
theorem exists_pos_uniform_normalizedSingletonPacketDefect
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ packet : QuittingNormalizedSingletonSourcePacket reward,
        δ ≤ @quittingNormalizedSingletonPacketDefect ι _
          witness.nonempty_players reward (packet.mass, packet.target) := by
  letI : Nonempty ι := witness.nonempty_players
  obtain ⟨packet⟩ := witness.nonempty_normalizedSingletonSourcePacket
  have hnonempty :
      (quittingNormalizedSingletonPacketDataSet reward).Nonempty :=
    ⟨(packet.mass, packet.target), packet.data_mem⟩
  obtain ⟨data, hdata, hmin⟩ :=
    quittingNormalizedSingletonPacketDataSet_isCompact.exists_isMinOn
      hnonempty
      continuous_quittingNormalizedSingletonPacketDefect.continuousOn
  exact ⟨quittingNormalizedSingletonPacketDefect reward data,
    quittingNormalizedSingletonPacketDefect_pos witness data hdata,
    fun candidate ↦ hmin candidate.data_mem⟩

/-- The uniform defect is a uniform refusal advantage on one active atom of
every normalized packet. -/
theorem exists_pos_uniform_normalizedSingletonPacketRefusal
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ packet : QuittingNormalizedSingletonSourcePacket reward,
        ∃ owner,
          0 < packet.mass owner ∧ packet.mass owner < 1 ∧
          packet.target owner <
            quittingSingletonMixture reward packet.mass owner ∧
          quittingSingletonMixture reward packet.mass owner + δ ≤
            quittingSingletonRefusalValue reward packet.mass owner owner := by
  letI : Nonempty ι := witness.nonempty_players
  obtain ⟨δ, hδ, hdefect⟩ :=
    witness.exists_pos_uniform_normalizedSingletonPacketDefect
  refine ⟨δ, hδ, fun packet ↦ ?_⟩
  obtain ⟨owner, _, howner⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty
    (fun who ↦ packet.mass who *
      (quittingSingletonMixture reward packet.mass who - packet.target who))
  have hproduct : δ ≤ packet.mass owner *
      (quittingSingletonMixture reward packet.mass owner -
        packet.target owner) := by
    rw [← howner]
    exact hdefect packet
  have hproductPos : 0 < packet.mass owner *
      (quittingSingletonMixture reward packet.mass owner -
        packet.target owner) := hδ.trans_le hproduct
  have hmass : 0 < packet.mass owner := by
    by_contra hnot
    have hle : packet.mass owner ≤ 0 := le_of_not_gt hnot
    have hsurplusNonneg := sub_nonneg.mpr (packet.mix_ge_target owner)
    have : packet.mass owner *
        (quittingSingletonMixture reward packet.mass owner -
          packet.target owner) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hsurplusNonneg
    linarith
  have hsurplus : packet.target owner <
      quittingSingletonMixture reward packet.mass owner := by
    have hmassNonneg := hmass.le
    by_contra hnot
    have hle : quittingSingletonMixture reward packet.mass owner -
        packet.target owner ≤ 0 := by linarith
    have : packet.mass owner *
        (quittingSingletonMixture reward packet.mass owner -
          packet.target owner) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hmassNonneg hle
    linarith
  have hmassLt : packet.mass owner < 1 := by
    apply lt_of_le_of_ne (packet.mass_le_one owner)
    intro hone
    rw [packet.singletonMixture_eq_singleton_of_mass_eq_one hone owner,
      ← packet.positive_mass_pins_target owner hmass] at hsurplus
    exact (lt_irrefl _ hsurplus)
  have hodds : packet.mass owner ≤
      packet.mass owner / (1 - packet.mass owner) := by
    apply (le_div_iff₀ (sub_pos.mpr hmassLt)).2
    nlinarith [packet.mass_nonneg owner]
  have hgain := packet.refusal_sub_mixture_eq_mass_div_mul_surplus
    hmass hmassLt
  have hscaled := mul_le_mul_of_nonneg_right hodds (sub_pos.mpr hsurplus).le
  refine ⟨owner, hmass, hmassLt, hsurplus, ?_⟩
  linarith

end QuittingTerminalExploitabilityWitness

end GameTheory
