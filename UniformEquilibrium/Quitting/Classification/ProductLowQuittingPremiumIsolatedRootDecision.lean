import MathUE.RealQuantifierElimination.QuantifierBlocks
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumFormula
import UniformEquilibrium.Quitting.Root.IsolatedRootRewardParameters

/-! # Product-low decision for isolated-root reward entries -/

namespace GameTheory

open MathUE.RealQuantifierElimination

variable {players : Nat}

/-- A hazard variable in the leading universally quantified block. -/
def isolatedRootProductLowHazardTerm (player : Fin players) :
    RingExpression (quittingRewardParameterCount players + players) :=
  .var (PolynomialFormula.leadingBlockIndex
    (quittingRewardParameterCount players) player)

/-- A reward variable in the trailing isolated-root parameter block. -/
def isolatedRootProductLowRewardTerm
    (terminal : {S : Finset (Fin players) // S.Nonempty}) (observer : Fin players) :
    RingExpression (quittingRewardParameterCount players + players) :=
  .var (PolynomialFormula.trailingBlockIndex
    (quittingRewardParameterCount players) players
      (quittingRewardTableVariableIndex (terminal, observer)))

/-- The parametric singleton-relative premium expression. -/
def isolatedRootProductLowPremiumTerm (player : Fin players) :
    RingExpression (quittingRewardParameterCount players + players) :=
  quittingHazardQuitPremiumExpressionWithTerms
    isolatedRootProductLowRewardTerm isolatedRootProductLowHazardTerm player

@[simp]
theorem evalReal_isolatedRootProductLowHazardTerm
    (hazard : Fin players → ℝ)
    (parameters : Fin (quittingRewardParameterCount players) → ℝ)
    (player : Fin players) :
    (isolatedRootProductLowHazardTerm player).evalReal
      (PolynomialFormula.blockEnvironment hazard parameters) = hazard player := by
  simp [isolatedRootProductLowHazardTerm]

@[simp]
theorem evalReal_isolatedRootProductLowRewardTerm
    (hazard : Fin players → ℝ)
    (parameters : Fin (quittingRewardParameterCount players) → ℝ)
    (terminal : {S : Finset (Fin players) // S.Nonempty}) (observer : Fin players) :
    (isolatedRootProductLowRewardTerm terminal observer).evalReal
        (PolynomialFormula.blockEnvironment hazard parameters) =
      quittingRewardFromParameters parameters terminal observer := by
  simp [isolatedRootProductLowRewardTerm, quittingRewardFromParameters]

@[simp]
theorem evalReal_isolatedRootProductLowPremiumTerm
    (hazard : Fin players → ℝ)
    (parameters : Fin (quittingRewardParameterCount players) → ℝ)
    (player : Fin players) :
    (isolatedRootProductLowPremiumTerm player).evalReal
        (PolynomialFormula.blockEnvironment hazard parameters) =
      quittingHazardQuitPremium (quittingRewardFromParameters parameters)
        hazard player := by
  simp [isolatedRootProductLowPremiumTerm]

/-- Product-low recognition with reward entries left as free parameters. -/
def isolatedRootProductLowParameterFormula :
    PolynomialFormula (quittingRewardParameterCount players) :=
  PolynomialFormula.universallyQuantifyFirst players
    (.ofQuantifierFree
      (productLowHazardFormulaWithTerms isolatedRootProductLowHazardTerm
        isolatedRootProductLowPremiumTerm))

@[simp]
theorem isolatedRootProductLowParameterFormula_holdsAt_iff
    (parameters : Fin (quittingRewardParameterCount players) → ℝ) :
    isolatedRootProductLowParameterFormula.HoldsAt parameters ↔
      HasProductLowQuittingPremium (quittingRewardFromParameters parameters) := by
  rw [isolatedRootProductLowParameterFormula,
    PolynomialFormula.holdsAt_universallyQuantifyFirst_iff,
    hasProductLowQuittingPremium_iff_hazard]
  simp only [PolynomialFormula.holdsAt_ofQuantifierFree_iff]
  constructor
  · intro hformula hazard hzero hone hactive
    have himp := (productLowHazardFormulaWithTerms_holdsAt_iff _ _ _).mp
      (hformula hazard)
    simp only [evalReal_isolatedRootProductLowHazardTerm,
      evalReal_isolatedRootProductLowPremiumTerm] at himp
    exact himp ⟨⟨hzero, hone⟩, hactive⟩
  · intro hhazard hazard
    apply (productLowHazardFormulaWithTerms_holdsAt_iff _ _ _).mpr
    simp only [evalReal_isolatedRootProductLowHazardTerm,
      evalReal_isolatedRootProductLowPremiumTerm]
    rintro ⟨⟨hzero, hone⟩, hactive⟩
    exact hhazard hazard hzero hone hactive

/-- Execute product-low recognition for a table of certified isolated roots. -/
def decideHasProductLowQuittingPremiumAtIsolatedRoots
    (encoded : CertifiedIsolatedRootQuittingReward players) : Bool :=
  decideAtIsolatedRoots (certifiedIsolatedRootRewardParameters encoded)
    isolatedRootProductLowParameterFormula

/-- The Boolean result is correct for every real reward table denoted by the
certified coordinate inputs. -/
theorem decideHasProductLowQuittingPremiumAtIsolatedRoots_eq_true_iff
    (encoded : CertifiedIsolatedRootQuittingReward players)
    (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players))
    (hdenotes : encoded.Denotes reward) :
    decideHasProductLowQuittingPremiumAtIsolatedRoots encoded = true ↔
      HasProductLowQuittingPremium reward := by
  rw [decideHasProductLowQuittingPremiumAtIsolatedRoots,
    decideAtIsolatedRoots_eq_true_iff
      (certifiedIsolatedRootRewardParameters encoded)
      isolatedRootProductLowParameterFormula (quittingRewardParameters reward)]
  · simp
  · intro index
    exact hdenotes ((quittingRewardTableVariableList players).get index).1
      ((quittingRewardTableVariableList players).get index).2

end GameTheory
