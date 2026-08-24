/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.SupportThreeFour
import UniformEquilibrium.Quitting.Punishment.ContinueFloor

/-!
# Support-three normality barrier

The unique outsider of a support-three packet need not be punishment-normal.
The concrete packet below also carries the complete internal crossed-row
pattern forced by the checked support-three singleton machinery.  Hence the
abnormal singleton floor rules out only an outsider crossing; it does not
rule out the internal cyclic branch.
-/

noncomputable section

namespace GameTheory

open Finset QuittingLCPClassification QuittingSureSetOwnerRepair

namespace QuittingSupportThreeNormalityBarrier

abbrev Player := Fin 4

def outsider : Player := 3

/-- Cyclic singleton matrix on the three supported labels, with an abnormal
fourth coordinate.  Nonsingleton rows are set to zero except that any row
containing the outsider pays that outsider `-1`. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun S who =>
    if who = outsider then
      if outsider ∈ S.1 then -1 else 0
    else if S.1 = {0} then
      if who = 1 then 1 else if who = 2 then -1 else 0
    else if S.1 = {1} then
      if who = 0 then -1 else if who = 2 then 1 else 0
    else if S.1 = {2} then
      if who = 0 then 1 else if who = 1 then -1 else 0
    else 0

/-- Equal mass on the three supported labels. -/
def mass (who : Player) : ℝ := if who = outsider then 0 else 1 / 3

private theorem mass_nonneg (who : Player) : 0 ≤ mass who := by
  unfold mass
  split <;> norm_num

private theorem mass_sum : ∑ who, mass who = 1 := by
  simp +decide [Fin.sum_univ_succ, mass, outsider]
  norm_num

private theorem singletonMixture_eq_zero (who : Player) :
    quittingSingletonMixture reward mass who = 0 := by
  fin_cases who <;>
    simp +decide [quittingSingletonMixture, Fin.sum_univ_succ, mass, reward,
      outsider, quittingSingletonTerminal]

private theorem ownSingleton_le_zero (who : Player) :
    reward (quittingSingletonTerminal who) who ≤ 0 := by
  fin_cases who <;>
    simp +decide [reward]

private theorem supportedOwnSingleton_eq_zero
    {who : Player} (hwho : who ≠ outsider) :
    reward (quittingSingletonTerminal who) who = 0 := by
  fin_cases who <;>
    simp +decide [reward] at hwho ⊢

/-- Literal support-three normalized singleton packet. -/
def packet : QuittingNormalizedSingletonSourcePacket reward where
  mass := mass
  target := fun _ => 0
  mass_nonneg := mass_nonneg
  mass_sum := mass_sum
  mix_ge_target := fun who => by rw [singletonMixture_eq_zero]
  solo_le_target := ownSingleton_le_zero
  punishment_le_target := fun who => by
    calc
      quittingPunishmentValue reward who ≤
          max (quittingSetReward reward {who} who) 0 :=
        quittingPunishmentValue_le_max_solo reward who
      _ = 0 := by
        rw [quittingSetReward_singleton_eq_soloReward]
        have hsolo : quittingSoloReward reward who who ≤ 0 := by
          simpa only [quittingSoloReward, quittingSingletonTerminal] using
            ownSingleton_le_zero who
        exact max_eq_right hsolo
  positive_mass_pins_target := fun owner hmass => by
    have howner : owner ≠ outsider := by
      intro heq
      subst owner
      simp [mass, outsider] at hmass
    exact (supportedOwnSingleton_eq_zero howner).symm

theorem packet_support : packet.support = {0, 1, 2} := by
  ext who
  fin_cases who <;>
    simp +decide [QuittingNormalizedSingletonSourcePacket.support,
      packet, mass, outsider]

/-- The outsider's continue floor is zero because every coalition avoiding
it pays it zero. -/
theorem outsider_continueFloor : quittingContinueFloor reward outsider = 0 := by
  apply le_antisymm
  · exact quittingContinueFloor_nonpos reward outsider
  · unfold quittingContinueFloor
    apply le_quittingBlockContinueFloor reward {outsider} outsider le_rfl
    intro S _hS hdisjoint
    have houtside : outsider ∉ S :=
      Finset.disjoint_singleton_right.mp hdisjoint
    simp [reward, houtside]

/-- The outsider's behavioral punishment value is zero. -/
theorem outsider_punishmentValue :
    quittingPunishmentValue reward outsider = 0 := by
  apply le_antisymm
  · calc
      quittingPunishmentValue reward outsider ≤
          max (quittingSetReward reward {outsider} outsider) 0 :=
        quittingPunishmentValue_le_max_solo reward outsider
      _ = 0 := by
        norm_num [quittingSetReward, reward, outsider]
  · rw [← outsider_continueFloor]
    exact quittingContinueFloor_le_quittingPunishmentValue reward outsider

/-- The unique outsider is strictly punishment-abnormal. -/
theorem outsider_abnormal : IsQuittingAbnormalPlayer reward outsider := by
  unfold IsQuittingAbnormalPlayer quittingSoloSelfPayoff
  rw [outsider_punishmentValue]
  norm_num [reward, outsider, quittingSingletonTerminal]

/-- Every supported owner has the literal internal crossed row expected in
the unresolved cyclic support-three branch. -/
theorem packet_internalCrossedRows :
    ∀ owner, owner ∈ packet.support →
      Nonempty (QuittingPacketCrossedRow packet owner) := by
  intro owner howner
  rw [packet_support] at howner
  fin_cases owner
  · refine ⟨{
      harmed := 2
      helper := 1
      owner_mem := by rw [packet_support]; simp
      helper_mem := by rw [packet_support]; simp
      harmed_ne_owner := by decide
      helper_ne_owner := by decide
      helper_ne_harmed := by decide
      singleton_crossing := ?_
      matrix_crossing := ?_ }⟩
    · simp +decide [reward]
    · constructor <;>
        rw [normalizedSoloMatrix_eq_soloReward_sub] <;>
        simp +decide [quittingSoloReward, reward]
  · refine ⟨{
      harmed := 0
      helper := 2
      owner_mem := by rw [packet_support]; simp
      helper_mem := by rw [packet_support]; simp
      harmed_ne_owner := by decide
      helper_ne_owner := by decide
      helper_ne_harmed := by decide
      singleton_crossing := ?_
      matrix_crossing := ?_ }⟩
    · simp +decide [reward]
    · constructor <;>
        rw [normalizedSoloMatrix_eq_soloReward_sub] <;>
        simp +decide [quittingSoloReward, reward]
  · refine ⟨{
      harmed := 1
      helper := 0
      owner_mem := by rw [packet_support]; simp
      helper_mem := by rw [packet_support]; simp
      harmed_ne_owner := by decide
      helper_ne_owner := by decide
      helper_ne_harmed := by decide
      singleton_crossing := ?_
      matrix_crossing := ?_ }⟩
    · simp +decide [reward]
    · constructor <;>
        rw [normalizedSoloMatrix_eq_soloReward_sub] <;>
        simp +decide [quittingSoloReward, reward]
  · simp at howner

/-- The checked singleton consequences of the support-three terminal branch
are compatible with a strictly abnormal unique outsider.  Therefore those
consequences alone cannot feed the all-normal full-support lift. -/
theorem supportThree_internalCrossedRows_do_not_force_outsider_normal :
    packet.support.card = 3 ∧
      packet.supportᶜ = {outsider} ∧
      (∀ owner, owner ∈ packet.support →
        Nonempty (QuittingPacketCrossedRow packet owner)) ∧
      IsQuittingAbnormalPlayer reward outsider := by
  refine ⟨?_, ?_, packet_internalCrossedRows, outsider_abnormal⟩
  · rw [packet_support]
    decide
  · rw [packet_support]
    ext who
    fin_cases who <;> simp [outsider]

end QuittingSupportThreeNormalityBarrier

end GameTheory
