/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FiniteFaceSideClaims
import UniformEquilibrium.Quitting.Classification.LCP.Normalization

/-!
# Three- and four-point singleton-packet support

A supported singleton owner in a terminal counterexample cannot be pointwise
safe: packet normality and the no-harm singleton compiler would solve the
game.  If its singleton row harms one coordinate, packet averaging forces a
different supported singleton row to help that same coordinate strictly.

Thus every supported owner column participates in a crossed row of the
normalized singleton matrix.  On four players, support three gives either an
internal crossing exhausting the support or a crossing through the unique
outsider.  Full support leaves only the internal alternative.

These are singleton-table consequences.  They supply no coalition-collision
payoff, source matching, or executable chronology.
-/

noncomputable section

namespace GameTheory

open Finset QuittingLCPClassification

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

namespace QuittingNormalizedSingletonSourcePacket

/-- A strict loss in one positive-mass singleton atom must be offset by a
strict gain in another positive-mass singleton atom. -/
theorem exists_supported_helper_of_singleton_lt_solo
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {owner who : iota} (howner : owner ∈ packet.support)
    (hharm : reward (quittingSingletonTerminal owner) who <
      reward (quittingSingletonTerminal who) who) :
    ∃ helper ∈ packet.support, helper ≠ owner ∧
      reward (quittingSingletonTerminal who) who <
        reward (quittingSingletonTerminal helper) who := by
  have hownerMass : 0 < packet.mass owner :=
    (packet.mem_support_iff owner).mp howner
  have hsoloMix : reward (quittingSingletonTerminal who) who ≤
      quittingSingletonMixture reward packet.mass who :=
    (packet.solo_le_target who).trans (packet.mix_ge_target who)
  by_contra hnone
  push Not at hnone
  have hotherLe : ∀ helper ∈ packet.support.erase owner,
      reward (quittingSingletonTerminal helper) who ≤
        reward (quittingSingletonTerminal who) who := by
    intro helper hhelper
    exact hnone helper (Finset.mem_of_mem_erase hhelper)
      (Finset.ne_of_mem_erase hhelper)
  have hweightedLe :
      ∑ helper ∈ packet.support.erase owner,
          packet.mass helper * reward (quittingSingletonTerminal helper) who ≤
        ∑ helper ∈ packet.support.erase owner,
          packet.mass helper * reward (quittingSingletonTerminal who) who := by
    apply Finset.sum_le_sum
    intro helper hhelper
    exact mul_le_mul_of_nonneg_left (hotherLe helper hhelper)
      (packet.mass_nonneg helper)
  have hmassSplit := Finset.sum_erase_add
    (s := packet.support) (f := packet.mass) howner
  rw [packet.sum_support_mass] at hmassSplit
  have hrewardSplit := Finset.sum_erase_add
    (s := packet.support)
    (f := fun helper => packet.mass helper *
      reward (quittingSingletonTerminal helper) who) howner
  have hownerStrict : packet.mass owner *
      reward (quittingSingletonTerminal owner) who <
        packet.mass owner * reward (quittingSingletonTerminal who) who :=
    mul_lt_mul_of_pos_left hharm hownerMass
  have hmixStrict : quittingSingletonMixture reward packet.mass who <
      reward (quittingSingletonTerminal who) who := by
    rw [← packet.sum_support_mul_singletonReward who, ← hrewardSplit]
    calc
      ∑ helper ∈ packet.support.erase owner,
              packet.mass helper * reward (quittingSingletonTerminal helper) who +
            packet.mass owner * reward (quittingSingletonTerminal owner) who <
          ∑ helper ∈ packet.support.erase owner,
              packet.mass helper * reward (quittingSingletonTerminal who) who +
            packet.mass owner * reward (quittingSingletonTerminal who) who :=
        add_lt_add_of_le_of_lt hweightedLe hownerStrict
      _ = reward (quittingSingletonTerminal who) who := by
        rw [← Finset.sum_mul, ← add_mul, hmassSplit, one_mul]
  exact (not_lt_of_ge hsoloMix) hmixStrict

end QuittingNormalizedSingletonSourcePacket

/-- A packet-supported owner harms one coordinate, while another supported
owner strictly overpays that same coordinate.  Equivalently, one row of the
normalized singleton matrix has a negative entry in the first owner column
and a positive entry in the helper column. -/
structure QuittingPacketCrossedRow
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (owner : iota) where
  harmed : iota
  helper : iota
  owner_mem : owner ∈ packet.support
  helper_mem : helper ∈ packet.support
  harmed_ne_owner : harmed ≠ owner
  helper_ne_owner : helper ≠ owner
  helper_ne_harmed : helper ≠ harmed
  singleton_crossing :
    reward (quittingSingletonTerminal owner) harmed <
        reward (quittingSingletonTerminal harmed) harmed ∧
      reward (quittingSingletonTerminal harmed) harmed <
        reward (quittingSingletonTerminal helper) harmed
  matrix_crossing :
    normalizedSoloMatrix reward harmed owner < 0 ∧
      0 < normalizedSoloMatrix reward harmed helper

namespace QuittingTerminalExploitabilityWitness

/-- Every supported owner of a terminal counterexample participates in a
strict crossed singleton row. -/
theorem nonempty_packetCrossedRow
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {owner : iota} (howner : owner ∈ packet.support) :
    Nonempty (QuittingPacketCrossedRow packet owner) := by
  have hnormal : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner := by
    change quittingPunishmentValue reward owner ≤
      reward (quittingSingletonTerminal owner) owner
    calc
      quittingPunishmentValue reward owner ≤ packet.target owner :=
        packet.punishment_le_target owner
      _ = reward (quittingSingletonTerminal owner) owner :=
        packet.positive_mass_pins_target owner
          ((packet.mem_support_iff owner).mp howner)
  have hharmed : ∃ harmed, harmed ≠ owner ∧
      reward (quittingSingletonTerminal owner) harmed <
        reward (quittingSingletonTerminal harmed) harmed := by
    by_contra hnone
    push Not at hnone
    have hgenerated :=
      quittingStationarilyGeneratedApproximateEquilibria_of_normal_noHarmSingleton
        reward owner hnone hnormal
    have hexists :=
      quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence
        reward
        (quittingApproximateEquilibriumExistence_of_stationarilyGenerated
          hgenerated)
    exact witness.not_exists_uniformEquilibriumPayoff hexists
  obtain ⟨harmed, hharmedNe, hharm⟩ := hharmed
  obtain ⟨helper, hhelper, hhelperNe, hhelp⟩ :=
    packet.exists_supported_helper_of_singleton_lt_solo howner hharm
  have hhelperHarmed : helper ≠ harmed := by
    intro heq
    subst helper
    exact (lt_irrefl _ hhelp)
  have hharm' : quittingSoloReward reward owner harmed <
      quittingSoloReward reward harmed harmed := by
    simpa only [quittingSoloReward, quittingSingletonTerminal] using hharm
  have hhelp' : quittingSoloReward reward harmed harmed <
      quittingSoloReward reward helper harmed := by
    simpa only [quittingSoloReward, quittingSingletonTerminal] using hhelp
  refine ⟨{
    harmed := harmed
    helper := helper
    owner_mem := howner
    helper_mem := hhelper
    harmed_ne_owner := hharmedNe
    helper_ne_owner := hhelperNe
    helper_ne_harmed := hhelperHarmed
    singleton_crossing := ⟨hharm, hhelp⟩
    matrix_crossing := ?_ }⟩
  constructor
  · rw [normalizedSoloMatrix_eq_soloReward_sub]
    exact sub_neg.mpr hharm'
  · rw [normalizedSoloMatrix_eq_soloReward_sub]
    exact sub_pos.mpr hhelp'

/-- In a four-player support-three packet, the complement is one player and
each supported owner has either an internal crossed row exhausting the
support, or a crossed row at that unique outsider. -/
theorem exists_supportThree_crossedRow_dispatch
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hplayers : Fintype.card iota = 4)
    (hsupport : packet.support.card = 3) :
    ∃ outsider,
      packet.supportᶜ = {outsider} ∧
      ∀ owner, owner ∈ packet.support →
        ∃ row : QuittingPacketCrossedRow packet owner,
          row.harmed = outsider ∨
            packet.support = {owner, row.harmed, row.helper} := by
  have hcomplCard : packet.supportᶜ.card = 1 := by
    rw [Finset.card_compl, hplayers, hsupport]
  obtain ⟨outsider, houtside⟩ := Finset.card_eq_one.mp hcomplCard
  refine ⟨outsider, houtside, ?_⟩
  intro owner howner
  obtain ⟨row⟩ := witness.nonempty_packetCrossedRow packet howner
  refine ⟨row, ?_⟩
  by_cases hharmed : row.harmed ∈ packet.support
  · right
    have hsubset : ({owner, row.harmed, row.helper} : Finset iota) ⊆
        packet.support := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨row.owner_mem, hharmed, row.helper_mem⟩
    have htripleCard : ({owner, row.harmed, row.helper} : Finset iota).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨row.harmed_ne_owner.symm, row.helper_ne_owner.symm⟩)]
      · rw [Finset.card_pair row.helper_ne_harmed.symm]
    exact (Finset.eq_of_subset_of_card_le hsubset (by
      rw [htripleCard, hsupport])).symm
  · left
    have hcomplement : row.harmed ∈ packet.supportᶜ := by simp [hharmed]
    rw [houtside] at hcomplement
    simpa using hcomplement

/-- A full-support four-player packet forces a crossed normalized-matrix row
through three pairwise distinct supported labels for every owner. -/
theorem supportFour_crossedRows
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hplayers : Fintype.card iota = 4)
    (hsupport : packet.support.card = 4) :
    packet.support = Finset.univ ∧
      ∀ owner, Nonempty (QuittingPacketCrossedRow packet owner) := by
  have hsupportUniv : packet.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [hplayers] using hsupport
  refine ⟨hsupportUniv, ?_⟩
  intro owner
  have howner : owner ∈ packet.support := by rw [hsupportUniv]; simp
  exact witness.nonempty_packetCrossedRow packet howner

end QuittingTerminalExploitabilityWitness

/-! ## Collision-interface boundary -/

namespace QuittingSupportThreeFourCollisionFalsifier

open QuittingCollisionPacketInterfaceFalsifier
open QuittingSureSetOwnerRepair

abbrev table (alpha beta : Real) :=
  QuittingCollisionPacketInterfaceFalsifier.reward alpha beta

/-- Three positive singleton masses, leaving `right` outside the support. -/
def supportThreeMass (who : Player) : Real :=
  if who = first then 1 / 3
  else if who = second then 1 / 3
  else if who = left then 1 / 3
  else 0

/-- Uniform positive singleton mass on all four players. -/
def supportFourMass (_who : Player) : Real := 1 / 4

private theorem supportThreeMass_nonneg (who : Player) :
    0 ≤ supportThreeMass who := by
  fin_cases who <;>
    simp +decide [supportThreeMass]

private theorem supportThreeMass_sum :
    ∑ who, supportThreeMass who = 1 := by
  simp +decide [Fin.sum_univ_succ, supportThreeMass, first, second, left]
  norm_num

private theorem supportFourMass_nonneg (who : Player) :
    0 ≤ supportFourMass who := by
  norm_num [supportFourMass]

private theorem supportFourMass_sum :
    ∑ who, supportFourMass who = 1 := by
  simp [supportFourMass]

private theorem supportThreeMixture_eq_zero
    (alpha beta : Real) (who : Player) :
    quittingSingletonMixture (table alpha beta) supportThreeMass who = 0 := by
  fin_cases who <;>
    simp +decide [quittingSingletonMixture, Fin.sum_univ_succ,
      supportThreeMass, table,
      QuittingCollisionPacketInterfaceFalsifier.reward,
      quittingSingletonTerminal,
      first, second, left, right]

private theorem supportFourMixture_eq_zero
    (alpha beta : Real) (who : Player) :
    quittingSingletonMixture (table alpha beta) supportFourMass who = 0 := by
  fin_cases who <;>
    simp +decide [quittingSingletonMixture, Fin.sum_univ_succ,
      supportFourMass, table,
      QuittingCollisionPacketInterfaceFalsifier.reward,
      quittingSingletonTerminal,
      first, second, left, right]

private theorem table_ownSingleton_eq_zero
    (alpha beta : Real) (who : Player) :
    table alpha beta (quittingSingletonTerminal who) who = 0 := by
  fin_cases who <;>
    simp +decide [table, QuittingCollisionPacketInterfaceFalsifier.reward]

private def packetOfMass
    (alpha beta : Real) (packetMass : Player → Real)
    (hmassNonneg : ∀ who, 0 ≤ packetMass who)
    (hmassSum : ∑ who, packetMass who = 1)
    (hmix : ∀ who,
      quittingSingletonMixture (table alpha beta) packetMass who = 0) :
    QuittingNormalizedSingletonSourcePacket (table alpha beta) where
  mass := packetMass
  target := fun _ ↦ 0
  mass_nonneg := hmassNonneg
  mass_sum := hmassSum
  mix_ge_target := fun who ↦ by rw [hmix who]
  solo_le_target := fun who ↦ by
    rw [table_ownSingleton_eq_zero]
  punishment_le_target := fun who ↦ by
    calc
      quittingPunishmentValue (table alpha beta) who ≤
          max (quittingSetReward (table alpha beta) {who} who) 0 :=
        quittingPunishmentValue_le_max_solo (table alpha beta) who
      _ = 0 := by
        rw [quittingSetReward_singleton_eq_soloReward]
        rw [show quittingSoloReward (table alpha beta) who who = 0 by
          simpa only [quittingSoloReward, quittingSingletonTerminal] using
            table_ownSingleton_eq_zero alpha beta who]
        simp
  positive_mass_pins_target := fun owner _ ↦ by
    rw [table_ownSingleton_eq_zero]

def supportThreePacket (alpha beta : Real) :
    QuittingNormalizedSingletonSourcePacket (table alpha beta) :=
  packetOfMass alpha beta supportThreeMass supportThreeMass_nonneg
    supportThreeMass_sum (supportThreeMixture_eq_zero alpha beta)

def supportFourPacket (alpha beta : Real) :
    QuittingNormalizedSingletonSourcePacket (table alpha beta) :=
  packetOfMass alpha beta supportFourMass supportFourMass_nonneg
    supportFourMass_sum (supportFourMixture_eq_zero alpha beta)

theorem supportThreePacket_support (alpha beta : Real) :
    (supportThreePacket alpha beta).support = {first, second, left} := by
  ext who
  fin_cases who <;>
    simp +decide [QuittingNormalizedSingletonSourcePacket.support,
      supportThreePacket, packetOfMass, supportThreeMass,
      first, second, left]

theorem supportFourPacket_support (alpha beta : Real) :
    (supportFourPacket alpha beta).support = Finset.univ := by
  ext who
  simp [QuittingNormalizedSingletonSourcePacket.support,
    supportFourPacket, packetOfMass, supportFourMass]

/-- A support-three normalized packet does not by itself supply either
ordered collision repair on a chosen support pair. -/
theorem supportThree_packet_does_not_supply_collisionRepair
    (alpha beta : Real) :
    (supportThreePacket alpha beta).support.card = 3 ∧
      (∀ (rate : Real) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1),
        ¬QuittingCollisionRepairWorks
          (table alpha beta) first second rate hrate0 hrate1) ∧
      (∀ (rate : Real) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1),
        ¬QuittingCollisionRepairWorks
          (table alpha beta) second first rate hrate0 hrate1) := by
  refine ⟨?_, not_firstOrientation_repairWorks alpha beta,
    not_secondOrientation_repairWorks alpha beta⟩
  rw [supportThreePacket_support]
  decide

/-- Even full packet support does not supply the missing nonsingleton
collision inequalities. -/
theorem supportFour_packet_does_not_supply_collisionRepair
    (alpha beta : Real) :
    (supportFourPacket alpha beta).support.card = 4 ∧
      (∀ (rate : Real) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1),
        ¬QuittingCollisionRepairWorks
          (table alpha beta) first second rate hrate0 hrate1) ∧
      (∀ (rate : Real) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1),
        ¬QuittingCollisionRepairWorks
          (table alpha beta) second first rate hrate0 hrate1) := by
  refine ⟨?_, not_firstOrientation_repairWorks alpha beta,
    not_secondOrientation_repairWorks alpha beta⟩
  rw [supportFourPacket_support]
  decide

end QuittingSupportThreeFourCollisionFalsifier

end GameTheory
