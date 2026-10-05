import UniformEquilibrium.Quitting.Classification.Existence.CommonQuittingPremiumLeaverRewardClosure
import UniformEquilibrium.Quitting.Examples.TwoPlayerPremiumCoreStrictLeave

/-! # A literal signed common-leaver fixture with a three-player premium core

This is the table in Section 6 of `COMMON_LEAVER_WITH_SIGNED_PREMIUMS.md`.
It has strict and weak common-leaver uniform-payoff applications, a negative
participant premium, and a product-low obstruction. This does not certify the
Section 5 counterroot, matrix degree/inverse claims, or all response partitions
and quiet children. The older pair fixture supplies only coding and root helpers.
-/

noncomputable section

namespace GameTheory.CommonLeaverSignedPremiumFixture

open TwoPlayerPremiumCoreStrictLeave (coalitionCode halfCoreRoot)

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal => match coalitionCode terminal.val with
    | 1 => ![1, -1, -1, -1]
    | 2 => ![11 / 10, 0, 2, -1]
    | 3 => ![1, 1 / 2, -1, -1]
    | 4 => ![0, -1, 0, 2]
    | 5 => ![1, -1, -1 / 10, -1]
    | 6 => ![0, 0, 0, 1]
    | 7 => ![1, 0, 0, -1]
    | 8 => ![5 / 2, 2, -1, 0]
    | 9 => ![2, -1, -1, 1]
    | 10 => ![5 / 2, 0, 1, 0]
    | 11 => ![1, 0, -1, 0]
    | 12 => ![5 / 2, 1, 0, 0]
    | 13 => ![1, -1, 0, 0]
    | 14 => ![5 / 2, 0, 0, 0]
    | 15 => ![1, 0, 0, 0]
    | _ => 0

@[simp] theorem reward_singleton (player : Fin 4) :
    reward (quittingSingletonTerminal player) player =
      (![1, 0, 0, 0] : Payoff (Fin 4)) player := by
  fin_cases player <;>
    norm_num +decide [reward, coalitionCode, quittingSingletonTerminal]

theorem singleton_nonnegative (player : Fin 4) :
    0 ≤ reward (quittingSingletonTerminal player) player := by
  rw [reward_singleton]
  fin_cases player <;> norm_num

/-- Membership is part of the statement: passive positive rewards are not
participant premiums and are not discarded from the actual reward table. -/
theorem participant_positive_iff (coalition : Finset (Fin 4)) (player : Fin 4) :
    (player ∈ coalition ∧ HasPositiveOwnQuittingPremium reward player coalition) ↔
      (coalition = {0, 3} ∧ (player = 0 ∨ player = 3)) ∨
        (coalition = {0, 1} ∧ player = 1) := by
  by_cases hmember : player ∈ coalition
  · have hnonempty : coalition.Nonempty := ⟨player, hmember⟩
    have hpositive : HasPositiveOwnQuittingPremium reward player coalition ↔
        reward (quittingSingletonTerminal player) player <
          reward ⟨coalition, hnonempty⟩ player := by
      constructor
      · rintro ⟨_, hlt⟩
        exact hlt
      · intro hlt
        exact ⟨hnonempty, hlt⟩
    rw [hpositive, reward_singleton]
    fin_cases coalition <;> fin_cases player <;>
      norm_num +decide [reward, coalitionCode] at *
  · fin_cases coalition <;> fin_cases player <;> norm_num +decide at *

theorem trap_iff (active : Finset (Fin 4)) :
    IsQuittingPremiumTrap reward active ↔ active = {0, 3} ∨ active = {0, 1, 3} := by
  unfold IsQuittingPremiumTrap MathUE.IsFiniteCoalitionPremiumTrap
  simp_rw [participant_positive_iff]
  fin_cases active <;> decide

@[simp] theorem premiumCore_eq : quittingPremiumCore reward = {0, 1, 3} := by
  ext player
  change player ∈ MathUE.finiteCoalitionPremiumCore
    (HasPositiveOwnQuittingPremium reward) ↔ _
  rw [MathUE.mem_finiteCoalitionPremiumCore_iff]
  change (∃ active, IsQuittingPremiumTrap reward active ∧ player ∈ active) ↔ _
  simp only [trap_iff]
  fin_cases player <;> simp

theorem premiumCore_card : (quittingPremiumCore reward).card = 3 := by
  rw [premiumCore_eq]
  decide

theorem premiumCore_nonempty : (quittingPremiumCore reward).Nonempty := by
  rw [premiumCore_eq]
  simp

theorem commonLeaver : IsCommonQuittingPremiumLeaver reward 0 := by
  constructor
  · intro terminal hmember
    rw [reward_singleton]
    fin_cases terminal <;> norm_num +decide [reward, coalitionCode] at *
  · intro active htrap
    rcases (trap_iff active).mp htrap with rfl | rfl <;> simp

theorem strictLeave
    (coalition : Finset (Fin 4)) (hnonempty : coalition.Nonempty)
    (hsubset : coalition ⊆ (quittingPremiumCore reward).erase 0) :
    reward ⟨insert 0 coalition, Finset.insert_nonempty _ _⟩ 0 <
      reward ⟨coalition, hnonempty⟩ 0 := by
  rw [premiumCore_eq] at hsubset
  fin_cases coalition <;> norm_num +decide [reward, coalitionCode] at *
  exact Finset.not_nonempty_empty hnonempty

theorem weakLeave
    (coalition : Finset (Fin 4)) (hnonempty : coalition.Nonempty)
    (hsubset : coalition ⊆ (quittingPremiumCore reward).erase 0) :
    reward ⟨insert 0 coalition, Finset.insert_nonempty _ _⟩ 0 ≤
      reward ⟨coalition, hnonempty⟩ 0 :=
  (strictLeave coalition hnonempty hsubset).le

theorem not_nonnegativePremium : ¬HasNonnegativeOwnQuittingPremium reward := by
  intro hnonnegative
  have h := hnonnegative ⟨{0, 2}, by simp⟩ 2 (by simp)
  norm_num +decide [reward, coalitionCode, quittingSingletonTerminal] at h

theorem exists_uniformEquilibriumPayoff_strict :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_commonLeaver_strictLeave
    reward singleton_nonnegative 0 commonLeaver strictLeave

theorem exists_uniformEquilibriumPayoff_weak :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_commonLeaver_weakLeave
    reward singleton_nonnegative 0 commonLeaver weakLeave

/-- This root is only a product-low witness; no root-Nash assertion is made. -/
theorem halfCoreRoot_quit_first (tail : Payoff (Fin 4)) :
    quittingRootQuitPayoff reward tail halfCoreRoot 0 = 3 / 2 := by
  rw [TwoPlayerPremiumCoreStrictLeave.halfCoreRoot,
    PairedCycle.rootQuit_first reward tail (by decide)]
  norm_num +decide [Math.PairedAffine.activeValue, reward, coalitionCode,
    quittingSingletonTerminal]

theorem halfCoreRoot_quit_second (tail : Payoff (Fin 4)) :
    quittingRootQuitPayoff reward tail halfCoreRoot 3 = 1 / 2 := by
  rw [TwoPlayerPremiumCoreStrictLeave.halfCoreRoot,
    PairedCycle.rootQuit_second reward tail (by decide)]
  norm_num +decide [Math.PairedAffine.activeValue, reward, coalitionCode,
    quittingSingletonTerminal]

theorem not_hasProductLowQuittingPremium : ¬HasProductLowQuittingPremium reward := by
  intro hlow
  obtain ⟨player, hactive, hquit⟩ := hlow halfCoreRoot
    (by rw [TwoPlayerPremiumCoreStrictLeave.halfCoreRoot_absorptionMass]; norm_num)
  by_cases hfirst : player = 0
  · subst player
    rw [halfCoreRoot_quit_first, reward_singleton] at hquit
    norm_num at hquit
  · by_cases hsecond : player = 3
    · subst player
      rw [halfCoreRoot_quit_second, reward_singleton] at hquit
      norm_num at hquit
    · rw [TwoPlayerPremiumCoreStrictLeave.halfCoreRoot_outside_inactive
        player hfirst hsecond] at hactive
      exact (lt_irrefl 0) hactive

end GameTheory.CommonLeaverSignedPremiumFixture
