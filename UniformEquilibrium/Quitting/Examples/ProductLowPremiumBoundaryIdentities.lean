import UniformEquilibrium.Quitting.Examples.ProductLowFinFourFamily
import MathUE.PMFProduct.CoalitionMass
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-! # Exact dual boundary identities for product-low premiums -/

noncomputable section

namespace GameTheory.ProductLowPremiumBoundaryIdentities

open Math.Probability Math.PMFProduct QuittingSureSetOwnerRepair

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

/-- The all-Quit product root. -/
def allQuitRoot : Fin 4 → PMF Bool := fun _ => PMF.pure true

/-- At all-Quit, the normalized four-player family premium vector is exactly
`(0,0,0,1)`. -/
theorem quitPremiumPolynomial_allQuit :
    ProductLowFinFourFamily.quitPremiumPolynomial allQuitRoot = ![0, 0, 0, 1] := by
  funext player
  fin_cases player <;>
    norm_num +decide [ProductLowFinFourFamily.quitPremiumPolynomial, allQuitRoot]

/-- The actual singleton-relative pure-Quit payoff at all-Quit is zero in
the first three coordinates and `scale 3` in the fourth. -/
theorem quitPremium_allQuit_formula
    (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (player : Fin 4) :
    quittingRootQuitPayoff
          (ProductLowFinFourFamily.reward singleton scale passive)
          0 allQuitRoot player - singleton player =
      scale player * ![0, 0, 0, 1] player := by
  rw [ProductLowFinFourFamily.quitPremium_formula]
  rw [congrFun quitPremiumPolynomial_allQuit player]

/-- The root with only player three active. -/
def onlyThreeRoot : Fin 4 → PMF Bool := quittingPureSetRoot {3}

@[simp] theorem onlyThreeRoot_three_active :
    0 < (onlyThreeRoot 3 true).toReal := by
  norm_num [onlyThreeRoot, quittingPureSetRoot, quittingSetAction]

@[simp] theorem onlyThreeRoot_absorptionMass :
    quittingRootAbsorptionMass onlyThreeRoot = 1 := by
  unfold onlyThreeRoot
  exact quittingRootAbsorptionMass_pureSetRoot_of_nonempty (by simp)

/-- When only player three is active, its normalized pure-Quit premium is
zero despite its positive full-coalition premium. -/
theorem quitPremiumPolynomial_onlyThree_active_zero :
    ProductLowFinFourFamily.quitPremiumPolynomial onlyThreeRoot 3 = 0 := by
  norm_num +decide [ProductLowFinFourFamily.quitPremiumPolynomial, onlyThreeRoot,
    quittingPureSetRoot, quittingSetAction]

/-- The actual active pure-Quit payoff at the only-player-three root equals
player three's own singleton reward. -/
theorem quitPayoff_onlyThree_eq_singleton
    (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    quittingRootQuitPayoff
        (ProductLowFinFourFamily.reward singleton scale passive)
        0 onlyThreeRoot 3 =
      ProductLowFinFourFamily.reward singleton scale passive
        (quittingSingletonTerminal 3) 3 := by
  rw [ProductLowFinFourFamily.reward_singleton]
  apply sub_eq_zero.mp
  rw [ProductLowFinFourFamily.quitPremium_formula,
    quitPremiumPolynomial_onlyThree_active_zero, mul_zero]

/-- The normalized correlated coalition law has expected participant premium
`scale player / 7` in every coordinate. -/
theorem sum_dualMass_mul_participantPremium
    (scale : Payoff (Fin 4)) (player : Fin 4) :
    (∑ terminal : Finset (Fin 4),
      dualMass terminal * ProductLowFinFourFamily.premium scale terminal player) =
        scale player / 7 := by
  let premiumAt : Finset (Fin 4) → ℝ := fun terminal =>
    ProductLowFinFourFamily.premium scale terminal player
  have hsingle (terminal : Finset (Fin 4)) (coefficient : ℝ) :
      (∑ other : Finset (Fin 4),
        ((if other = terminal then coefficient else 0) / 7) * premiumAt other) =
          coefficient / 7 * premiumAt terminal := by
    simp only [ite_div, zero_div, ite_mul, zero_mul]
    exact Fintype.sum_ite_eq' terminal (fun other => coefficient / 7 * premiumAt other)
  change (∑ terminal : Finset (Fin 4), dualMass terminal * premiumAt terminal) = _
  simp only [dualMass, dualCoefficient, mul_ite, mul_one, mul_zero, add_div,
    add_mul, Finset.sum_add_distrib]
  rw [hsingle, hsingle, hsingle, hsingle]
  dsimp only [premiumAt]
  have hidentity := ProductLowPremiumBoundaryIdentities.dualPremium_identity scale player
  linarith

private theorem dualMass_mul_premium_eq_participant_mask
    (scale : Payoff (Fin 4)) (terminal : Finset (Fin 4)) (player : Fin 4) :
    dualMass terminal * ProductLowFinFourFamily.premium scale terminal player =
      dualMass terminal *
        (if player ∈ terminal then
          ProductLowFinFourFamily.premium scale terminal player else 0) := by
  by_cases hplayer : player ∈ terminal
  · rw [if_pos hplayer]
  rw [if_neg hplayer, mul_zero]
  by_cases hmass : dualMass terminal = 0
  · rw [hmass, zero_mul]
  have hsupport : terminal = {0, 1} ∨ terminal = {0, 2} ∨
      terminal = {1, 2, 3} ∨ terminal = Finset.univ := by
    by_contra hnot
    push Not at hnot
    apply hmass
    simp [dualMass, dualCoefficient, hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2]
  rcases hsupport with rfl | rfl | rfl | rfl <;>
    fin_cases player <;> simp_all +decide [ProductLowFinFourFamily.premium]

/-- The normalized correlated coalition law has expected actual participant
premium `scale player / 7`, with passive coordinates explicitly excluded. -/
theorem sum_dualMass_mul_actualParticipantPremium
    (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (player : Fin 4) :
    (∑ terminal : {S : Finset (Fin 4) // S.Nonempty},
      dualMass terminal.val *
        (if player ∈ terminal.val then
          ProductLowFinFourFamily.reward singleton scale passive terminal player -
            ProductLowFinFourFamily.reward singleton scale passive
              (quittingSingletonTerminal player) player
        else 0)) = scale player / 7 := by
  calc
    _ = ∑ terminal : {S : Finset (Fin 4) // S.Nonempty},
        dualMass terminal.val * ProductLowFinFourFamily.premium scale terminal.val player := by
      apply Finset.sum_congr rfl
      intro terminal _
      rw [dualMass_mul_premium_eq_participant_mask]
      by_cases hplayer : player ∈ terminal.val
      · rw [if_pos hplayer, if_pos hplayer,
          ProductLowFinFourFamily.reward_sub_singleton singleton scale passive
            terminal player hplayer]
      · rw [if_neg hplayer, if_neg hplayer]
    _ = ∑ terminal : Finset (Fin 4),
        dualMass terminal * ProductLowFinFourFamily.premium scale terminal player := by
      rw [← Finset.sum_subtype
        (Finset.univ.filter (fun terminal : Finset (Fin 4) => terminal.Nonempty))
        (by simp) (fun terminal =>
          dualMass terminal * ProductLowFinFourFamily.premium scale terminal player)]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro terminal _ houtside
      have hempty : terminal = ∅ := by
        simpa using houtside
      simp [hempty]
    _ = scale player / 7 := sum_dualMass_mul_participantPremium scale player

end GameTheory.ProductLowPremiumBoundaryIdentities
