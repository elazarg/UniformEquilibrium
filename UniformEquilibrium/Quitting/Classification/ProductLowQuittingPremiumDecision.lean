import MathUE.RealQuantifierElimination.QuantifierElimination
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumFormula
import UniformEquilibrium.Quitting.Root.RationalReward

/-! # Exact rational decision for product-low quitting premiums -/

namespace GameTheory

open MathUE.RealQuantifierElimination

variable {players : Nat}

/-- The product of hazard variables over a finite player set. -/
def hazardProductExpression (set : Finset (Fin players)) : RingExpression players :=
  hazardProductExpressionWithTerms RingExpression.var set

/-- The product of one-minus-hazard expressions over a finite player set. -/
def continueProductExpression (set : Finset (Fin players)) : RingExpression players :=
  continueProductExpressionWithTerms RingExpression.var set

@[simp]
theorem evalReal_hazardProductExpression
    (set : Finset (Fin players)) (hazard : Fin players → ℝ) :
    (hazardProductExpression set).evalReal hazard =
      ∏ player ∈ set, hazard player := by
  simp [hazardProductExpression]

@[simp]
theorem evalReal_continueProductExpression
    (set : Finset (Fin players)) (hazard : Fin players → ℝ) :
    (continueProductExpression set).evalReal hazard =
      ∏ player ∈ set, (1 - hazard player) := by
  simp [continueProductExpression]

/-- A coalition's contribution to one player's singleton-relative Quit premium. -/
def coalitionPremiumExpression (reward : RationalQuittingReward players)
    (player : Fin players) (coalition : Finset (Fin players)) :
    RingExpression players :=
  coalitionPremiumExpressionWithTerms
    (fun terminal observer => RingExpression.const (reward terminal observer))
    RingExpression.var player coalition

/-- The singleton-relative Quit premium as an explicit rational expression. -/
def quittingHazardQuitPremiumExpression
    (reward : RationalQuittingReward players) (player : Fin players) :
    RingExpression players :=
  quittingHazardQuitPremiumExpressionWithTerms
    (fun terminal observer => RingExpression.const (reward terminal observer))
    RingExpression.var player

@[simp]
theorem evalReal_coalitionPremiumExpression
    (reward : RationalQuittingReward players) (player : Fin players)
    (coalition : Finset (Fin players)) (hazard : Fin players → ℝ) :
    (coalitionPremiumExpression reward player coalition).evalReal hazard =
      ((∏ other ∈ coalition, hazard other) *
        ∏ other ∈ Finset.univ.erase player \ coalition, (1 - hazard other)) *
        (rationalQuittingRewardToReal reward
              ⟨insert player coalition, Finset.insert_nonempty player coalition⟩ player -
          rationalQuittingRewardToReal reward
            (quittingSingletonTerminal player) player) := by
  simp [coalitionPremiumExpression, rationalQuittingRewardToReal]

@[simp]
theorem evalReal_quittingHazardQuitPremiumExpression
    (reward : RationalQuittingReward players) (player : Fin players)
    (hazard : Fin players → ℝ) :
    (quittingHazardQuitPremiumExpression reward player).evalReal hazard =
      quittingHazardQuitPremium (rationalQuittingRewardToReal reward) hazard player := by
  rw [quittingHazardQuitPremiumExpression,
    evalReal_quittingHazardQuitPremiumExpressionWithTerms]
  rfl

/-- The conjunction saying every hazard coordinate belongs to `[0,1]`. -/
def hazardCubeFormula (players : Nat) : QuantifierFreeFormula players :=
  hazardCubeFormulaWithTerms RingExpression.var

/-- Some hazard coordinate is positive. -/
def activeHazardFormula (players : Nat) : QuantifierFreeFormula players :=
  activeHazardFormulaWithTerms RingExpression.var

/-- Some active player has a nonpositive singleton-relative Quit premium. -/
def lowActivePremiumFormula (reward : RationalQuittingReward players) :
    QuantifierFreeFormula players :=
  lowActivePremiumFormulaWithTerms RingExpression.var
    (quittingHazardQuitPremiumExpression reward)

/-- The hazard-space sentence underlying the product-low condition. -/
def productLowHazardFormula (reward : RationalQuittingReward players) :
    QuantifierFreeFormula players :=
  productLowHazardFormulaWithTerms RingExpression.var
    (quittingHazardQuitPremiumExpression reward)

@[simp]
theorem hazardCubeFormula_holdsAt_iff (hazard : Fin players → ℝ) :
    (hazardCubeFormula players).HoldsAt hazard ↔
      (∀ player, 0 ≤ hazard player) ∧ ∀ player, hazard player ≤ 1 := by
  rw [hazardCubeFormula, hazardCubeFormulaWithTerms_holdsAt_iff]
  simp

@[simp]
theorem activeHazardFormula_holdsAt_iff (hazard : Fin players → ℝ) :
    (activeHazardFormula players).HoldsAt hazard ↔
      ∃ player, 0 < hazard player := by
  rw [activeHazardFormula, activeHazardFormulaWithTerms_holdsAt_iff]
  simp

@[simp]
theorem lowActivePremiumFormula_holdsAt_iff
    (reward : RationalQuittingReward players) (hazard : Fin players → ℝ) :
    (lowActivePremiumFormula reward).HoldsAt hazard ↔
      ∃ player, 0 < hazard player ∧
        quittingHazardQuitPremium (rationalQuittingRewardToReal reward)
          hazard player ≤ 0 := by
  rw [lowActivePremiumFormula,
    lowActivePremiumFormulaWithTerms_holdsAt_iff]
  simp only [RingExpression.evalReal_var,
    evalReal_quittingHazardQuitPremiumExpression]

@[simp]
theorem productLowHazardFormula_holdsAt_iff
    (reward : RationalQuittingReward players) (hazard : Fin players → ℝ) :
    (productLowHazardFormula reward).HoldsAt hazard ↔
      (((∀ player, 0 ≤ hazard player) ∧ ∀ player, hazard player ≤ 1) ∧
          (∃ player, 0 < hazard player) →
        ∃ player, 0 < hazard player ∧
          quittingHazardQuitPremium (rationalQuittingRewardToReal reward)
            hazard player ≤ 0) := by
  rw [productLowHazardFormula,
    productLowHazardFormulaWithTerms_holdsAt_iff]
  simp only [RingExpression.evalReal_var,
    evalReal_quittingHazardQuitPremiumExpression]

/-- The closed first-order sentence recognizing product-low rational tables. -/
def productLowQuittingPremiumFormula (reward : RationalQuittingReward players) :
    PolynomialFormula 0 :=
  (PolynomialFormula.ofQuantifierFree
    (productLowHazardFormula reward)).universallyClose

/-- The closed formula has exactly the existing product-low semantics. -/
theorem productLowQuittingPremiumFormula_holdsAt_iff
    (reward : RationalQuittingReward players) :
    (productLowQuittingPremiumFormula reward).HoldsAt Fin.elim0 ↔
      HasProductLowQuittingPremium (rationalQuittingRewardToReal reward) := by
  rw [productLowQuittingPremiumFormula,
    PolynomialFormula.holdsAt_universallyClose_iff]
  simp only [PolynomialFormula.holdsAt_ofQuantifierFree_iff]
  rw [hasProductLowQuittingPremium_iff_hazard]
  constructor
  · intro hformula hazard hzero hone hactive
    exact (productLowHazardFormula_holdsAt_iff reward hazard).mp
      (hformula hazard) ⟨⟨hzero, hone⟩, hactive⟩
  · intro hhazard hazard
    apply (productLowHazardFormula_holdsAt_iff reward hazard).mpr
    rintro ⟨⟨hzero, hone⟩, hactive⟩
    exact hhazard hazard hzero hone hactive

/-- Execute the checked real quantifier eliminator on a rational reward table. -/
def decideHasProductLowQuittingPremium
    (reward : RationalQuittingReward players) : Bool :=
  decideClosedFormula (productLowQuittingPremiumFormula reward)

/-- The executable Boolean result is true exactly for product-low tables. -/
theorem decideHasProductLowQuittingPremium_eq_true_iff
    (reward : RationalQuittingReward players) :
    decideHasProductLowQuittingPremium reward = true ↔
      HasProductLowQuittingPremium (rationalQuittingRewardToReal reward) := by
  rw [decideHasProductLowQuittingPremium, decideClosedFormula_eq_true_iff,
    productLowQuittingPremiumFormula_holdsAt_iff]

/-- With no players, the original product-low condition is vacuously true. -/
theorem decideHasProductLowQuittingPremium_zero_players
    (reward : RationalQuittingReward 0) :
    decideHasProductLowQuittingPremium reward = true := by
  rw [decideHasProductLowQuittingPremium_eq_true_iff]
  intro root habsorption
  obtain ⟨player, _⟩ :=
    (quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos root).mp
      habsorption
  exact Fin.elim0 player

end GameTheory
