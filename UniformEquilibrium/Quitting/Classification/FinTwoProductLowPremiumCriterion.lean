import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremium
import MathUE.PMFProduct.FiniteFubini

/-!
# Exact two-player product-low premium criterion

For an arbitrary two-player quitting reward table, product-low premiums fail
exactly when both players' full-coalition premiums over their own singleton
rewards are strictly positive.  Passive coordinates play no role.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

/-- The arbitrary-table pair premium of a two-player quitting game. -/
def finTwoPairPremium
    (reward : {S : Finset (Fin 2) // S.Nonempty} → Payoff (Fin 2))
    (player : Fin 2) : ℝ :=
  reward ⟨Finset.univ, Finset.univ_nonempty⟩ player -
    reward (quittingSingletonTerminal player) player

/-- In two players, a pure-Quit premium is the opponent's Quit probability
times the corresponding pair premium. -/
theorem finTwo_quitPremium_formula
    (reward : {S : Finset (Fin 2) // S.Nonempty} → Payoff (Fin 2))
    (root : Fin 2 → PMF Bool) (player : Fin 2) :
    quittingRootQuitPayoff reward 0 root player -
        reward (quittingSingletonTerminal player) player =
      (root (1 - player) true).toReal * finTwoPairPremium reward player := by
  fin_cases player
  · have hfull :
        (⟨({who | ![true, true] who = true} : Finset (Fin 2)), by decide⟩ :
          {S : Finset (Fin 2) // S.Nonempty}) =
            ⟨Finset.univ, Finset.univ_nonempty⟩ := by
      apply Subtype.ext
      decide
    have hsolo :
        (⟨({who | ![true, false] who = true} : Finset (Fin 2)), by decide⟩ :
          {S : Finset (Fin 2) // S.Nonempty}) =
            quittingSingletonTerminal 0 := by
      apply Subtype.ext
      decide
    unfold quittingRootQuitPayoff quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_fin2]
    simp +decide [finTwoPairPremium, quittingRootPayoff, quittingQuitters,
      quittingSingletonTerminal, Math.Probability.expect_eq_sum,
      pmfBool_false_toReal, hfull, hsolo]
    ring
  · have hfull :
        (⟨({who | ![true, true] who = true} : Finset (Fin 2)), by decide⟩ :
          {S : Finset (Fin 2) // S.Nonempty}) =
            ⟨Finset.univ, Finset.univ_nonempty⟩ := by
      apply Subtype.ext
      decide
    have hsolo :
        (⟨({who | ![false, true] who = true} : Finset (Fin 2)), by decide⟩ :
          {S : Finset (Fin 2) // S.Nonempty}) =
            quittingSingletonTerminal 1 := by
      apply Subtype.ext
      decide
    unfold quittingRootQuitPayoff quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_fin2]
    simp +decide [finTwoPairPremium, quittingRootPayoff, quittingQuitters,
      quittingSingletonTerminal, Math.Probability.expect_eq_sum,
      pmfBool_false_toReal, hfull, hsolo]
    ring

/-- For two players, product-low premiums fail exactly when both pair
premiums are strictly positive. -/
theorem finTwo_not_hasProductLowQuittingPremium_iff
    (reward : {S : Finset (Fin 2) // S.Nonempty} → Payoff (Fin 2)) :
    ¬HasProductLowQuittingPremium reward ↔
      0 < finTwoPairPremium reward 0 ∧ 0 < finTwoPairPremium reward 1 := by
  constructor
  · intro hnot
    by_contra hpairs
    push Not at hpairs
    apply hnot
    intro root habsorption
    have hcontinue : quittingStationaryContinueMass root < 1 := by
      unfold quittingRootAbsorptionMass at habsorption
      linarith
    obtain ⟨active, hactive⟩ :=
      exists_quitProbability_pos_of_continueMass_lt_one hcontinue
    by_cases hzero : 0 < (root 0 true).toReal
    · by_cases hpremiumZero : 0 < finTwoPairPremium reward 0
      · have hpremiumOne : finTwoPairPremium reward 1 ≤ 0 :=
          hpairs hpremiumZero
        by_cases hone : 0 < (root 1 true).toReal
        · refine ⟨1, hone, ?_⟩
          apply sub_nonpos.mp
          rw [finTwo_quitPremium_formula]
          exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg hpremiumOne
        · refine ⟨0, hzero, ?_⟩
          have hrootOne : (root 1 true).toReal = 0 :=
            le_antisymm (le_of_not_gt hone) ENNReal.toReal_nonneg
          apply sub_nonpos.mp
          rw [finTwo_quitPremium_formula]
          norm_num at hrootOne ⊢
          rw [hrootOne, zero_mul]
      · refine ⟨0, hzero, ?_⟩
        apply sub_nonpos.mp
        rw [finTwo_quitPremium_formula]
        exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
          (le_of_not_gt hpremiumZero)
    · have hrootZero : (root 0 true).toReal = 0 :=
        le_antisymm (le_of_not_gt hzero) ENNReal.toReal_nonneg
      have hone : 0 < (root 1 true).toReal := by
        fin_cases active <;> simp_all
      refine ⟨1, hone, ?_⟩
      apply sub_nonpos.mp
      rw [finTwo_quitPremium_formula]
      norm_num at hrootZero ⊢
      rw [hrootZero, zero_mul]
  · rintro ⟨hpremiumZero, hpremiumOne⟩ hlow
    let halfRoot : Fin 2 → PMF Bool := fun _ =>
      quittingHazardCoin (1 / 2) (by norm_num) (by norm_num)
    have habsorption : 0 < quittingRootAbsorptionMass halfRoot := by
      unfold quittingRootAbsorptionMass
      rw [quittingStationaryContinueMass_eq_prod_continueProbability,
        Fin.prod_univ_two]
      norm_num [halfRoot, quittingHazardCoin]
    obtain ⟨player, _hactive, hlowPlayer⟩ := hlow halfRoot habsorption
    have hformula := finTwo_quitPremium_formula reward halfRoot player
    have hpremium : 0 < finTwoPairPremium reward player := by
      fin_cases player <;> assumption
    have hopponent : 0 < (halfRoot (1 - player) true).toReal := by
      simp [halfRoot, quittingHazardCoin]
    nlinarith

end GameTheory
