import UniformEquilibrium.Quitting.Classification.Existence.BoxedQuittingNashChargesUniformPayoff
import MathUE.Finset.CoalitionBinaryCode
import Mathlib.Tactic.NormNum

/-! # The literal full-core boxed Nash-charge fixture

This is the complete table from Section 7 of the boxed-charge packet. The
coefficient tests and actual payoff consumer are supplied from the table.
Neighborhoods, child debt witnesses and matrix/response exclusions are separate
obligations, not asserted by this bounded unit.
-/

noncomputable section

namespace GameTheory.BoxedNashChargeFullCoreFixture

private abbrev coalitionCode := @Math.FiniteCoalition.binaryCode 4

private theorem univ_eq : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal => match coalitionCode terminal.val with
    | 1 => ![1, -1, -1, -1]
    | 2 => ![2, 0, 2, -1]
    | 3 => ![-1, -2, 2, 2]
    | 4 => ![2, -1, 0, 2]
    | 5 => ![-1, 2, -1 / 2, 2]
    | 6 => ![3, -1 / 2, -2, 2]
    | 7 => ![-1, -2, -2, 2]
    | 8 => ![0, 2, -1, 0]
    | 9 => ![1 / 2, 2, 2, -2]
    | 10 => ![3, -2, 2, -1 / 2]
    | 11 => ![-1, -2, 2, -2]
    | 12 => ![3, 2, -2, -2]
    | 13 => ![-1, 2, -2, -2]
    | 14 => ![3, -2, -2, -2]
    | 15 => ![11 / 10, 1 / 10, 1 / 10, 1 / 10]
    | _ => 0

@[simp] theorem reward_singleton (player : Fin 4) :
    reward (quittingSingletonTerminal player) player = (![1, 0, 0, 0] : Payoff (Fin 4))
      player := by
  fin_cases player <;>
    norm_num +decide [reward, coalitionCode, Math.FiniteCoalition.binaryCode_finFour,
      quittingSingletonTerminal]

theorem singleton_nonnegative (player : Fin 4) :
    0 ≤ reward (quittingSingletonTerminal player) player := by
  rw [reward_singleton]
  fin_cases player <;> norm_num

theorem reward_abs_le (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (player : Fin 4) : |reward terminal player| ≤ 3 := by
  fin_cases terminal <;> fin_cases player <;>
    norm_num +decide [reward, coalitionCode, Math.FiniteCoalition.binaryCode_finFour]

theorem participant_positive_iff (coalition : Finset (Fin 4)) (player : Fin 4) :
    (player ∈ coalition ∧ HasPositiveOwnQuittingPremium reward player coalition) ↔
      coalition = Finset.univ := by
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
    IsQuittingPremiumTrap reward active ↔ active = Finset.univ := by
  unfold IsQuittingPremiumTrap MathUE.IsFiniteCoalitionPremiumTrap
  simp_rw [participant_positive_iff]
  fin_cases active <;> decide

@[simp] theorem premiumCore_eq : quittingPremiumCore reward = Finset.univ := by
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
    exact ⟨Finset.univ, rfl, hplayer⟩

theorem singleton_sums (coalition : Finset (Fin 4)) (hnonempty : coalition.Nonempty)
    (hcard : coalition.card = 1) :
    quittingTrapInsertedPremiumSum reward Finset.univ coalition = -9 / 2 ∧
      quittingTrapLeaveSum reward Finset.univ ⟨coalition, hnonempty⟩ ≤ -3 / 2 := by
  have hcases : coalition = {0} ∨ coalition = {1} ∨ coalition = {2} ∨
      coalition = {3} := by
    fin_cases coalition <;> norm_num +decide at *
  rcases hcases with rfl | rfl | rfl | rfl <;>
    norm_num +decide [quittingTrapInsertedPremiumSum, quittingTrapLeaveSum,
      quittingWeightedLeaveSum, univ_eq, Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, Finset.sum_insert, reward, coalitionCode,
      Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal]

theorem pair_sums (coalition : Finset (Fin 4)) (hnonempty : coalition.Nonempty)
    (hcard : coalition.card = 2) :
    quittingTrapInsertedPremiumSum reward Finset.univ coalition = -4 ∧
      quittingTrapLeaveSum reward Finset.univ ⟨coalition, hnonempty⟩ = -8 := by
  have hcases : coalition = {0, 1} ∨ coalition = {0, 2} ∨ coalition = {0, 3} ∨
      coalition = {1, 2} ∨ coalition = {1, 3} ∨ coalition = {2, 3} := by
    fin_cases coalition <;> norm_num +decide at *
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num +decide [quittingTrapInsertedPremiumSum, quittingTrapLeaveSum,
      quittingWeightedLeaveSum, univ_eq, Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, Finset.sum_insert, reward, coalitionCode,
      Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal]

theorem triple_sums (coalition : Finset (Fin 4)) (hnonempty : coalition.Nonempty)
    (hcard : coalition.card = 3) :
    quittingTrapInsertedPremiumSum reward Finset.univ coalition = 1 / 10 ∧
      quittingTrapLeaveSum reward Finset.univ ⟨coalition, hnonempty⟩ = -19 / 10 := by
  have hcases : coalition = {0, 1, 2} ∨ coalition = {0, 1, 3} ∨
      coalition = {0, 2, 3} ∨ coalition = {1, 2, 3} := by
    fin_cases coalition <;> norm_num +decide at *
  rcases hcases with rfl | rfl | rfl | rfl <;>
    norm_num +decide [quittingTrapInsertedPremiumSum, quittingTrapLeaveSum,
      quittingWeightedLeaveSum, univ_eq, Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, Finset.sum_insert, reward, coalitionCode,
      Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal]

def coefficients : QuittingTrapChargeCoefficients reward Finset.univ where
  delta := 9 / 2
  tau := 1 / 10
  gap := 3 / 2
  loss := 19 / 10
  delta_pos := by norm_num
  tau_pos := by norm_num
  gap_pos := by norm_num
  loss_pos := by norm_num
  card_ge_three := by decide
  singleton := by
    intro coalition hnonempty _ hcard
    obtain ⟨hpremium, hleave⟩ := singleton_sums coalition hnonempty hcard
    rw [hpremium]
    constructor
    · norm_num
    · simpa only [neg_div] using hleave
  middle := by
    intro coalition hnonempty _ hlow hhigh
    have hsize : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    rw [hsize] at hhigh
    obtain ⟨hpremium, hleave⟩ := pair_sums coalition hnonempty (by omega)
    rw [hpremium, hleave]
    norm_num
  penultimate := by
    intro coalition hnonempty _ hcard
    have hsize : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    rw [hsize] at hcard
    obtain ⟨hpremium, hleave⟩ := triple_sums coalition hnonempty hcard
    rw [hpremium, hleave]
    norm_num

theorem threshold_eq : coefficients.threshold = 348 * Real.sqrt 45 := by
  rw [coefficients.threshold_of_cardinality_four (by decide)]
  norm_num [coefficients]
  ring

theorem threshold_gt_thirteen : 13 < coefficients.threshold := by
  rw [threshold_eq]
  have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 45)
  have hnonnegative := Real.sqrt_nonneg (45 : ℝ)
  nlinarith

theorem boxed_charges : HasBoxedQuittingNashCharges reward 3 := by
  intro active htrap
  rw [trap_iff] at htrap
  subst active
  refine ⟨coefficients, ?_⟩
  have hsum : ∑ player : Fin 4, reward (quittingSingletonTerminal player) player = 1 := by
    simp only [reward_singleton]
    norm_num [Fin.sum_univ_succ]
  simpa only [hsum, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat,
    show (1 : ℝ) + 4 * 3 = 13 from by norm_num] using threshold_gt_thirteen

theorem exists_uniformEquilibriumPayoff :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_boxedQuittingNashCharges
    reward singleton_nonnegative 3 reward_abs_le boxed_charges

end GameTheory.BoxedNashChargeFullCoreFixture
