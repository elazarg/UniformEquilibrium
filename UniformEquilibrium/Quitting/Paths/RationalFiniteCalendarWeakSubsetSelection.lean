import UniformEquilibrium.Quitting.Paths.RationalFiniteCalendarWeakSubsetSource
import UniformEquilibrium.Quitting.Paths.ExecutableRationalWeakSubsetDyadicSelection

/-! # Actual dyadic selection from literal raw weak-subset exclusion

The raw predicate is an erased source proof for the existing rational algorithm.
The selected word, independent date/Never laws, whole payoff/cap pair and absolute
date bound are retained. No payoff compression is asserted to preserve caps.
-/

namespace GameTheory

variable {players : ℕ}

/-- The canonical dyadic algorithm with its source and singleton signs supplied
by the actual raw-calendar predicate, rather than selected favorable data. -/
def executableRationalFiniteCalendarRawWeakSubsetSelection
    (reward : RationalQuittingReward players) (owners : Finset (Fin players))
    (hraw : HasQuittingFiniteCalendarRawWeakSubsetExclusion
      (rationalQuittingRewardToReal reward) owners)
    (M accuracy : ℚ) (haccuracy : 0 < accuracy) (haccuracyM : accuracy ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    RationalWeakSubsetOutcome players :=
  executableRationalWeakSubsetDyadicSelection reward owners
    (rationalFiniteWordOwnerExclusion_and_signs_of_rawWeakSubsetExclusion
      reward owners hraw).1 M accuracy haccuracy haccuracyM hreward

noncomputable section

/-- The SAME computed word has exact independent marginal laws, full terminal
debt and Nash at the requested accuracy, with the packet's absolute date bound.
The initial equal-debt boundary and empty-word laws remain those of the original
selector. Only designated owners need nonnegative singleton payoffs. -/
theorem executableRationalFiniteCalendarRawWeakSubsetSelection_finiteLaws_and_bound
    (reward : RationalQuittingReward players) (owners : Finset (Fin players))
    (hraw : HasQuittingFiniteCalendarRawWeakSubsetExclusion
      (rationalQuittingRewardToReal reward) owners)
    (M accuracy : ℚ) (haccuracy : 0 < accuracy) (haccuracyM : accuracy ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    let word := (executableRationalFiniteCalendarRawWeakSubsetSelection
      reward owners hraw M accuracy haccuracy haccuracyM hreward).word
    (word.length : ℝ) ≤
        1000000 * ((players : ℝ) + ((M : ℝ) / (accuracy : ℝ)) ^ 2 *
          Real.log (16 * players * (M : ℝ) / (accuracy : ℝ))) ∧
      ∃ mixed : Fin players → PMF (Option (Fin word.length)),
        (∀ who choice, (mixed who choice).toReal =
          (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
            word.length who choice : ℝ)) ∧
        quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
            word.length mixed) =
          (rationalQuittingFiniteWordSemanticPair reward word).toReal ∧
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
            (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
              word.length mixed)) ≤ (accuracy : ℝ) ∧
        (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
          (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) (accuracy : ℝ)
          (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
            word.length mixed) := by
  dsimp only
  let hWE := (rationalFiniteWordOwnerExclusion_and_signs_of_rawWeakSubsetExclusion
    reward owners hraw).1
  have hsign := (rationalFiniteWordOwnerExclusion_and_signs_of_rawWeakSubsetExclusion
    reward owners hraw).2
  let word := (executableRationalWeakSubsetDyadicSelection reward owners hWE
    M accuracy haccuracy haccuracyM hreward).word
  change (word.length : ℝ) ≤ _ ∧ _
  refine ⟨executableRationalWeakSubsetDyadicSelection_length_le_absolute
    reward owners hWE M accuracy haccuracy haccuracyM hreward hsign, ?_⟩
  obtain ⟨mixed, hmass, hpair, hnash⟩ :=
    executableRationalWeakSubsetDyadicSelection_finiteLaws
      reward owners hWE M accuracy haccuracy haccuracyM hreward hsign
  refine ⟨mixed, hmass, hpair, ?_, hnash⟩
  change quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          (executableRationalWeakSubsetDyadicSelection reward owners hWE
            M accuracy haccuracy haccuracyM hreward).word.length mixed)) ≤ (accuracy : ℝ)
  rw [hpair]
  change quittingTerminalSemanticDebtSum
      (rationalQuittingFiniteWordSemanticPair reward word).toReal ≤ (accuracy : ℝ)
  rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
  exact_mod_cast executableRationalWeakSubsetDyadicSelection_debt_le
    reward owners hWE M accuracy haccuracy haccuracyM hreward hsign

end
end GameTheory
