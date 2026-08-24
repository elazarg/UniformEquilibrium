/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FiniteFaceAggregate

/-!
# Exact side claims for the crossed support-two finite dispatch

This module records two independent finite facts.  First, a concrete
four-player normalized singleton packet can fail both ordered collision
repairs at every legal rate, despite satisfying the packet interface.  Thus
the singleton packet fields alone cannot supply the missing nonsingleton
collision inequalities.  The example is a zero-solo game and hence is not a
counterexample to uniform equilibrium.

Second, if a nonprojective normalized-solo principal in the crossed `Fin 4`
setting has cardinality two, the existing safe-pair exclusions leave exactly
the two harmed owner--spectator pairs and the spectator pair.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair QuittingLCPClassification

namespace QuittingCollisionPacketInterfaceFalsifier

abbrev Player := Fin 4

def first : Player := 0

def second : Player := 1

def left : Player := 2

def right : Player := 3

theorem first_ne_second : first ≠ second := by decide

theorem first_ne_left : first ≠ left := by decide

theorem first_ne_right : first ≠ right := by decide

theorem second_ne_left : second ≠ left := by decide

theorem second_ne_right : second ≠ right := by decide

theorem left_ne_right : left ≠ right := by decide

/-- The parametric reward table from equation (22) of the finite-dispatch
packet.  The parameters affect only the two supported owners' pair rewards. -/
def reward (alpha beta : Real) :
    {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who =>
    if terminal.1 = {first} then
      if who = left then -1 else if who = right then 1 else 0
    else if terminal.1 = {second} then
      if who = left then 1 else if who = right then -1 else 0
    else if terminal.1 = {first, second} then
      if who = first then alpha else if who = second then beta else 0
    else if terminal.1 = {first, second, left} then
      if who = left then 1 else 0
    else if terminal.1 = {first, second, right} then
      if who = right then 1 else 0
    else 0

def mass (who : Player) : Real :=
  if who = first then 1 / 2 else if who = second then 1 / 2 else 0

private theorem mass_nonneg (who : Player) : 0 ≤ mass who := by
  fin_cases who <;> norm_num [mass, first, second]

private theorem mass_sum : ∑ who, mass who = 1 := by
  simp +decide [Fin.sum_univ_succ, mass, first, second]
  norm_num

private theorem singletonMixture_eq_zero (alpha beta : Real) (who : Player) :
    quittingSingletonMixture (reward alpha beta) mass who = 0 := by
  fin_cases who <;>
    simp +decide [quittingSingletonMixture, Fin.sum_univ_succ, mass, reward,
      quittingSingletonTerminal, first, second, left, right]

private theorem ownSingleton_eq_zero (alpha beta : Real) (who : Player) :
    reward alpha beta (quittingSingletonTerminal who) who = 0 := by
  fin_cases who <;>
    simp +decide [reward]

/-- The equation-(22) table satisfies the full normalized singleton packet
interface for every choice of its two nonsingleton parameters. -/
def packet (alpha beta : Real) :
    QuittingNormalizedSingletonSourcePacket (reward alpha beta) where
  mass := mass
  target := fun _ => 0
  mass_nonneg := mass_nonneg
  mass_sum := mass_sum
  mix_ge_target := fun who => by rw [singletonMixture_eq_zero]
  solo_le_target := fun who => by rw [ownSingleton_eq_zero]
  punishment_le_target := fun who => by
    calc
      quittingPunishmentValue (reward alpha beta) who ≤
          max (quittingSetReward (reward alpha beta) {who} who) 0 :=
        quittingPunishmentValue_le_max_solo (reward alpha beta) who
      _ = 0 := by
        rw [quittingSetReward_singleton_eq_soloReward]
        rw [show quittingSoloReward (reward alpha beta) who who = 0 by
          exact ownSingleton_eq_zero alpha beta who]
        simp
  positive_mass_pins_target := fun owner _ => by
    rw [ownSingleton_eq_zero]

theorem packet_support_eq_pair (alpha beta : Real) :
    (packet alpha beta).support = {first, second} := by
  ext who
  fin_cases who <;> norm_num [QuittingNormalizedSingletonSourcePacket.support,
    packet, mass, first, second]

theorem isQuittingZeroSolo_reward (alpha beta : Real) :
    IsQuittingZeroSolo (reward alpha beta) := by
  intro who
  exact le_of_eq (ownSingleton_eq_zero alpha beta who)

/-- The falsifier is already in the solved zero-solo branch; it is not a
terminal counterexample. -/
theorem uniformEquilibriumPayoff_zero (alpha beta : Real) :
    (quittingGame (reward alpha beta)).IsUniformEquilibriumPayoff none 0 :=
  quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo
    (reward alpha beta) (isQuittingZeroSolo_reward alpha beta)

private theorem firstOrientation_spectator_defect
    (alpha beta : Real) (rate : Real) :
    (1 - rate) *
          quittingCollisionConstraintLower (reward alpha beta)
            first second ⟨right, first_ne_right.symm⟩ +
        rate * quittingCollisionConstraintUpper (reward alpha beta)
          first second ⟨right, first_ne_right.symm⟩ = 1 := by
  simp +decide [quittingCollisionConstraintLower,
    quittingCollisionConstraintUpper, quittingSetReward, reward]

private theorem secondOrientation_spectator_defect
    (alpha beta : Real) (rate : Real) :
    (1 - rate) *
          quittingCollisionConstraintLower (reward alpha beta)
            second first ⟨left, second_ne_left.symm⟩ +
        rate * quittingCollisionConstraintUpper (reward alpha beta)
          second first ⟨left, second_ne_left.symm⟩ = 1 := by
  simp +decide [quittingCollisionConstraintLower,
    quittingCollisionConstraintUpper, quittingSetReward, reward]

/-- Every legal rate fails for the ordered support orientation `(first,
second)`, independently of `alpha` and `beta`. -/
theorem not_firstOrientation_repairWorks
    (alpha beta rate : Real) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    ¬QuittingCollisionRepairWorks
      (reward alpha beta) first second rate hrate0 hrate1 := by
  intro hworks
  have hconditions :=
    (quittingCollisionRepairWorks_iff
      (reward alpha beta) first_ne_second hrate0 hrate1).1 hworks
  have hconstraints :=
    (quittingCollisionConstraints_iff
      (reward alpha beta) first_ne_second rate).2 ⟨hconditions.2.1, hconditions.2.2⟩
  have hrow := hconstraints
    (⟨right, first_ne_right.symm⟩ : QuittingCollisionConstraintPlayer first)
  rw [firstOrientation_spectator_defect] at hrow
  linarith

/-- Every legal rate fails for the reversed support orientation `(second,
first)`, independently of `alpha` and `beta`. -/
theorem not_secondOrientation_repairWorks
    (alpha beta rate : Real) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    ¬QuittingCollisionRepairWorks
      (reward alpha beta) second first rate hrate0 hrate1 := by
  intro hworks
  have hconditions :=
    (quittingCollisionRepairWorks_iff
      (reward alpha beta) first_ne_second.symm hrate0 hrate1).1 hworks
  have hconstraints :=
    (quittingCollisionConstraints_iff
      (reward alpha beta) first_ne_second.symm rate).2
        ⟨hconditions.2.1, hconditions.2.2⟩
  have hrow := hconstraints
    (⟨left, second_ne_left.symm⟩ : QuittingCollisionConstraintPlayer second)
  rw [secondOrientation_spectator_defect] at hrow
  linarith

/-- Exact packet-interface boundary: a normalized support-two packet may have
no collision repair in either orientation, at any legal rate. -/
theorem packetInterface_does_not_supply_collisionRepair (alpha beta : Real) :
    Nonempty (QuittingNormalizedSingletonSourcePacket (reward alpha beta)) ∧
      (packet alpha beta).support = {first, second} ∧
      (∀ (rate : Real) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1),
        ¬QuittingCollisionRepairWorks
          (reward alpha beta) first second rate hrate0 hrate1) ∧
      (∀ (rate : Real) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1),
        ¬QuittingCollisionRepairWorks
          (reward alpha beta) second first rate hrate0 hrate1) := by
  exact ⟨⟨packet alpha beta⟩, packet_support_eq_pair alpha beta,
    not_firstOrientation_repairWorks alpha beta,
    not_secondOrientation_repairWorks alpha beta⟩

end QuittingCollisionPacketInterfaceFalsifier

namespace QuittingNormalizedSingletonSourcePacket

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- In the crossed `Fin 4` support-pair setting, a two-element nonprojective
principal is exactly one of the three pairs not eliminated by the checked
safe-pair screen. -/
theorem nonprojectivePrincipal_eq_one_of_three_residualPairs
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {first second left right : iota} (hne : first ≠ second)
    (hsupport : packet.support = {first, second})
    (houtside : packet.supportᶜ = {left, right})
    (hleftHelped : quittingSoloReward reward left left <
      quittingSoloReward reward second left)
    (hrightHelped : quittingSoloReward reward right right <
      quittingSoloReward reward first right)
    {players : Finset iota} (hcard : players.card = 2)
    (hnot : ¬IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) players)) :
    players = {first, left} ∨ players = {second, right} ∨
      players = {left, right} := by
  obtain ⟨hneOwners, hneFirstRight, hneSecondLeft⟩ :=
    packet.nonprojectivePrincipal_ne_safePairs_of_support_eq_pair
      hne hsupport hleftHelped hrightHelped hnot
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  have classify (who : iota) :
      who = first ∨ who = second ∨ who = left ∨ who = right := by
    by_cases hmem : who ∈ packet.support
    · rw [hsupport] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      exact hmem.imp_right Or.inl
    · have hmemComplement : who ∈ packet.supportᶜ := by simp [hmem]
      rw [houtside] at hmemComplement
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmemComplement
      rcases hmemComplement with hleft | hright
      · exact Or.inr (Or.inr (Or.inl hleft))
      · exact Or.inr (Or.inr (Or.inr hright))
  have hfirstMem : first ∈ packet.support := by rw [hsupport]; simp
  have hsecondMem : second ∈ packet.support := by rw [hsupport]; simp
  have hleftOutside : left ∈ packet.supportᶜ := by rw [houtside]; simp
  have hrightOutside : right ∈ packet.supportᶜ := by rw [houtside]; simp
  have hleftNot : left ∉ packet.support := Finset.mem_compl.mp hleftOutside
  have hrightNot : right ∉ packet.support := Finset.mem_compl.mp hrightOutside
  have hfirstLeft : first ≠ left := fun h => hleftNot (h ▸ hfirstMem)
  have hfirstRight : first ≠ right := fun h => hrightNot (h ▸ hfirstMem)
  have hsecondLeft : second ≠ left := fun h => hleftNot (h ▸ hsecondMem)
  have hsecondRight : second ≠ right := fun h => hrightNot (h ▸ hsecondMem)
  rcases classify x with hx | hx | hx | hx <;>
    rcases classify y with hy | hy | hy | hy
  · exact (hxy (hx.trans hy.symm)).elim
  · exact (hneOwners (by simp only [hx, hy])).elim
  · left
    simp only [hx, hy]
  · exact (hneFirstRight (by simp only [hx, hy])).elim
  · exact (hneOwners (by simp only [hx, hy, Finset.pair_comm])).elim
  · exact (hxy (hx.trans hy.symm)).elim
  · exact (hneSecondLeft (by simp only [hx, hy])).elim
  · right
    left
    simp only [hx, hy]
  · left
    simp only [hx, hy, Finset.pair_comm]
  · exact (hneSecondLeft (by
      simp only [hx, hy, Finset.pair_comm])).elim
  · exact (hxy (hx.trans hy.symm)).elim
  · right
    right
    simp only [hx, hy]
  · exact (hneFirstRight (by
      simp only [hx, hy, Finset.pair_comm])).elim
  · right
    left
    simp only [hx, hy, Finset.pair_comm]
  · right
    right
    simp only [hx, hy, Finset.pair_comm]
  · exact (hxy (hx.trans hy.symm)).elim

end QuittingNormalizedSingletonSourcePacket

end GameTheory
