import UniformEquilibrium.Quitting.Classification.Existence.BoxedQuittingNashChargesUniformPayoff
import MathUE.Finset.CoalitionBinaryCode
import Mathlib.Tactic.NormNum

/-! # The literal proper-triple boxed Nash-charge fixture

This is the complete reward table from Section 6 of the boxed-charge packet.
The first bounded unit checks its raw trap tests and actual payoff consumer.
The unbounded counterroot, all proper-child debt witnesses, neighborhood and
matrix/response separation claims are separate obligations, not asserted here.
-/

noncomputable section

namespace GameTheory.BoxedNashChargeTripleFixture

private abbrev coalitionCode := @Math.FiniteCoalition.binaryCode 4

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal => match coalitionCode terminal.val with
    | 1 => ![1 / 10, 21 / 10, -9 / 10, 2]
    | 2 => ![-9 / 10, 1 / 10, 21 / 10, 2]
    | 3 => ![3 / 5, -9 / 10, 11 / 10, 2]
    | 4 => ![21 / 10, -9 / 10, 1 / 10, 0]
    | 5 => ![-9 / 10, 11 / 10, 3 / 5, 2]
    | 6 => ![11 / 10, 3 / 5, -9 / 10, 2]
    | 7 => ![1 / 5, 1 / 5, 1 / 5, 2]
    | 8 => ![-9 / 10, -9 / 10, -9 / 10, 1]
    | 9 => ![31 / 10, -9 / 10, -9 / 10, 0]
    | 10 => ![-9 / 10, 21 / 10, -9 / 10, 0]
    | 11 => ![21 / 10, 21 / 10, -9 / 10, 0]
    | 12 => ![-9 / 10, -9 / 10, 21 / 10, 0]
    | 13 => ![21 / 10, -9 / 10, 21 / 10, 0]
    | 14 => ![-9 / 10, 21 / 10, 21 / 10, 0]
    | 15 => ![21 / 10, 21 / 10, 21 / 10, 0]
    | _ => 0

@[simp] theorem reward_singleton (player : Fin 4) :
    reward (quittingSingletonTerminal player) player =
      (![1 / 10, 1 / 10, 1 / 10, 1] : Payoff (Fin 4)) player := by
  fin_cases player <;>
    norm_num +decide [reward, coalitionCode, Math.FiniteCoalition.binaryCode_finFour,
      quittingSingletonTerminal]

theorem singleton_nonnegative (player : Fin 4) :
    0 ≤ reward (quittingSingletonTerminal player) player := by
  rw [reward_singleton]
  fin_cases player <;> norm_num

theorem reward_abs_le (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (player : Fin 4) : |reward terminal player| ≤ 31 / 10 := by
  fin_cases terminal <;> fin_cases player <;>
    norm_num +decide [reward, coalitionCode, Math.FiniteCoalition.binaryCode_finFour]

theorem participant_positive_iff (coalition : Finset (Fin 4)) (player : Fin 4) :
    (player ∈ coalition ∧ HasPositiveOwnQuittingPremium reward player coalition) ↔
      player ≠ 3 ∧
        ((coalition = {0, 1} ∧ player = 0) ∨
          (coalition = {0, 2} ∧ player = 2) ∨
          (coalition = {1, 2} ∧ player = 1) ∨
          (player ∈ coalition ∧ (3 ∈ coalition ∨ coalition = {0, 1, 2}))) := by
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
      norm_num +decide [reward, coalitionCode, Math.FiniteCoalition.binaryCode_finFour] at *
  · fin_cases coalition <;> fin_cases player <;> norm_num +decide at *

theorem trap_iff (active : Finset (Fin 4)) :
    IsQuittingPremiumTrap reward active ↔ active = {0, 1, 2} := by
  unfold IsQuittingPremiumTrap MathUE.IsFiniteCoalitionPremiumTrap
  simp_rw [participant_positive_iff]
  fin_cases active <;> decide

@[simp] theorem premiumCore_eq : quittingPremiumCore reward = {0, 1, 2} := by
  ext player
  change player ∈ MathUE.finiteCoalitionPremiumCore
    (HasPositiveOwnQuittingPremium reward) ↔ _
  rw [MathUE.mem_finiteCoalitionPremiumCore_iff]
  change (∃ active, IsQuittingPremiumTrap reward active ∧ player ∈ active) ↔ _
  simp only [trap_iff]
  constructor
  · rintro ⟨active, rfl, hplayer⟩
    exact hplayer
  · intro hplayer
    exact ⟨{0, 1, 2}, rfl, hplayer⟩

theorem singleton_sums (coalition : Finset (Fin 4)) (hnonempty : coalition.Nonempty)
    (hproper : coalition ⊂ {0, 1, 2}) (hcard : coalition.card = 1) :
    quittingTrapInsertedPremiumSum reward {0, 1, 2} coalition = -1 / 2 ∧
      quittingTrapLeaveSum reward {0, 1, 2} ⟨coalition, hnonempty⟩ = -3 / 2 := by
  have hcases : coalition = {0} ∨ coalition = {1} ∨ coalition = {2} := by
    fin_cases coalition <;> norm_num +decide at *
  rcases hcases with rfl | rfl | rfl <;>
    norm_num +decide [quittingTrapInsertedPremiumSum, quittingTrapLeaveSum,
      quittingWeightedLeaveSum, Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, Finset.sum_insert, reward, coalitionCode,
      Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal]

theorem pair_sums (coalition : Finset (Fin 4)) (hnonempty : coalition.Nonempty)
    (hproper : coalition ⊂ {0, 1, 2}) (hcard : coalition.card = 2) :
    quittingTrapInsertedPremiumSum reward {0, 1, 2} coalition = 1 / 10 ∧
      quittingTrapLeaveSum reward {0, 1, 2} ⟨coalition, hnonempty⟩ = -9 / 10 := by
  have hcases : coalition = {0, 1} ∨ coalition = {0, 2} ∨ coalition = {1, 2} := by
    fin_cases coalition <;> norm_num +decide at *
  rcases hcases with rfl | rfl | rfl <;>
    norm_num +decide [quittingTrapInsertedPremiumSum, quittingTrapLeaveSum,
      quittingWeightedLeaveSum, Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, Finset.sum_insert, reward, coalitionCode,
      Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal]

def coefficients : QuittingTrapChargeCoefficients reward {0, 1, 2} where
  delta := 1 / 2
  tau := 1 / 10
  gap := 3 / 2
  loss := 9 / 10
  delta_pos := by norm_num
  tau_pos := by norm_num
  gap_pos := by norm_num
  loss_pos := by norm_num
  card_ge_three := by decide
  singleton := by
    intro coalition hnonempty hproper hcard
    obtain ⟨hpremium, hleave⟩ := singleton_sums coalition hnonempty hproper hcard
    rw [hpremium, hleave]
    norm_num
  middle := by
    intro coalition _ _ hlow hhigh
    have : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
    rw [this] at hhigh
    omega
  penultimate := by
    intro coalition hnonempty hproper hcard
    have hcore : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
    rw [hcore] at hcard
    obtain ⟨hpremium, hleave⟩ := pair_sums coalition hnonempty hproper hcard
    rw [hpremium, hleave]
    norm_num

theorem threshold_eq : coefficients.threshold = 90 := by
  rw [coefficients.threshold_of_cardinality_three (by decide)]
  norm_num [coefficients]

theorem boxed_charges : HasBoxedQuittingNashCharges reward (31 / 10) := by
  intro active htrap
  rw [trap_iff] at htrap
  subst active
  refine ⟨coefficients, ?_⟩
  rw [threshold_eq]
  norm_num +decide [reward, coalitionCode, Math.FiniteCoalition.binaryCode_finFour,
    quittingSingletonTerminal]

theorem exists_uniformEquilibriumPayoff :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_boxedQuittingNashCharges
    reward singleton_nonnegative (31 / 10) reward_abs_le boxed_charges

end GameTheory.BoxedNashChargeTripleFixture
