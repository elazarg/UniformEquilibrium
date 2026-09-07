import UniformEquilibrium.Quitting.Examples.ProductLowFinFourFamily
import MathUE.PMFProduct.CoalitionMass

/-! # Exact dual boundary identities for product-low premiums -/

noncomputable section

namespace GameTheory.ProductLowPremiumBoundaryIdentities

open Math.PMFProduct

def dualCoefficient (terminal : Finset (Fin 4)) : ℝ :=
  2 * (if terminal = {0, 1} then 1 else 0) +
    (if terminal = {0, 2} then 1 else 0) +
    3 * (if terminal = {1, 2, 3} then 1 else 0) +
    (if terminal = Finset.univ then 1 else 0)

def dualMass (terminal : Finset (Fin 4)) : ℝ := dualCoefficient terminal / 7

/-- The integer dual combination of the four displayed coalition premiums
is the strictly positive coordinate-scale vector. -/
theorem dualPremium_identity (scale : Payoff (Fin 4)) (player : Fin 4) :
    2 * ProductLowFinFourFamily.premium scale {0, 1} player +
        ProductLowFinFourFamily.premium scale {0, 2} player +
        3 * ProductLowFinFourFamily.premium scale {1, 2, 3} player +
        ProductLowFinFourFamily.premium scale Finset.univ player =
      scale player := by
  fin_cases player <;>
    norm_num +decide [ProductLowFinFourFamily.premium] <;> ring

@[simp] theorem dualMass_empty : dualMass (∅ : Finset (Fin 4)) = 0 := by
  norm_num +decide [dualMass, dualCoefficient]

@[simp] theorem dualMass_full : dualMass (Finset.univ : Finset (Fin 4)) = 1 / 7 := by
  norm_num +decide [dualMass, dualCoefficient]

@[simp] theorem dualMass_zeroOne : dualMass ({0, 1} : Finset (Fin 4)) = 2 / 7 := by
  norm_num +decide [dualMass, dualCoefficient]

@[simp] theorem dualMass_zeroTwo : dualMass ({0, 2} : Finset (Fin 4)) = 1 / 7 := by
  norm_num +decide [dualMass, dualCoefficient]

@[simp] theorem dualMass_oneTwoThree :
    dualMass ({1, 2, 3} : Finset (Fin 4)) = 3 / 7 := by
  norm_num +decide [dualMass, dualCoefficient]

theorem dualMass_nonneg (terminal : Finset (Fin 4)) :
    0 ≤ dualMass terminal := by
  unfold dualMass dualCoefficient
  split_ifs <;> norm_num

/-- The four displayed atoms form a normalized correlated coalition law. -/
theorem dualMass_sum_one :
    (∑ terminal : Finset (Fin 4), dualMass terminal) = 1 := by
  classical
  have hsum (terminal : Finset (Fin 4)) (coefficient : ℝ) :
      (∑ other : Finset (Fin 4),
        (if other = terminal then coefficient else 0) / 7) = coefficient / 7 := by
    simp only [ite_div, zero_div]
    exact Fintype.sum_ite_eq' terminal (fun _ => coefficient / 7)
  simp only [dualMass, dualCoefficient, mul_ite, mul_one, mul_zero, add_div,
    Finset.sum_add_distrib]
  rw [hsum, hsum, hsum, hsum]
  norm_num

/-- The positive dual law cannot be the coalition law of independent
Bernoulli coordinates: its positive displayed atoms force every Continue
factor positive, contradicting its zero empty-coalition mass. -/
theorem dualMass_not_independent :
    ¬∃ q : Fin 4 → ℝ, (∀ player, 0 ≤ q player) ∧
      (∀ player, q player ≤ 1) ∧
      ∀ terminal, coalitionMass q terminal = dualMass terminal := by
  rintro ⟨q, hq0, hq1, hmatch⟩
  have h123 : coalitionMass q ({1, 2, 3} : Finset (Fin 4)) = 3 / 7 := by
    rw [hmatch, dualMass_oneTwoThree]
  have h02 : coalitionMass q ({0, 2} : Finset (Fin 4)) = 1 / 7 := by
    rw [hmatch, dualMass_zeroTwo]
  have h01 : coalitionMass q ({0, 1} : Finset (Fin 4)) = 2 / 7 := by
    rw [hmatch, dualMass_zeroOne]
  have hc0 : 0 < 1 - q 0 := lt_of_lt_of_le (by norm_num)
    (h123 ▸ coalitionMass_le_one_sub_coordinate_of_not_mem
      q hq0 hq1 (by decide))
  have hc1 : 0 < 1 - q 1 := lt_of_lt_of_le (by norm_num)
    (h02 ▸ coalitionMass_le_one_sub_coordinate_of_not_mem
      q hq0 hq1 (by decide))
  have hc2 : 0 < 1 - q 2 := lt_of_lt_of_le (by norm_num)
    (h01 ▸ coalitionMass_le_one_sub_coordinate_of_not_mem
      q hq0 hq1 (by decide))
  have hc3 : 0 < 1 - q 3 := lt_of_lt_of_le (by norm_num)
    (h01 ▸ coalitionMass_le_one_sub_coordinate_of_not_mem
      q hq0 hq1 (by decide))
  have hempty : coalitionMass q (∅ : Finset (Fin 4)) = 0 := by
    rw [hmatch, dualMass_empty]
  have hemptyPos : 0 < coalitionMass q (∅ : Finset (Fin 4)) := by
    simp [coalitionMass, Fin.prod_univ_four]
    positivity
  linarith

end GameTheory.ProductLowPremiumBoundaryIdentities
