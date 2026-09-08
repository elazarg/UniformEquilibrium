import UniformEquilibrium.Quitting.Paths.ExecutableRationalStrictDeficitRates
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Paths.StrictDeficitFiniteWords

/-! # Real-source adapters for executable rational strict-deficit selection

For a rational reward table, the exact rational semantic fold is the actual
real terminal payoff of the same literal word.  Hence either real finite-word
strict deficit or the stronger actual-profile predicate supplies the rational
selector's source condition without approximation.
-/

namespace GameTheory

variable {players : ℕ}

/-- Real strict deficit on every literal finite word restricts exactly to the
rational finite-word semantic fold. -/
theorem rationalQuittingFiniteWordStrictSingletonDeficit_of_real
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit
      (rationalQuittingRewardToReal reward) (gap : ℝ)) :
    RationalQuittingFiniteWordStrictSingletonDeficit reward gap := by
  intro roots
  obtain ⟨who, hwho⟩ := hdeficit (roots.map RationalQuittingRoot.toPMF)
  refine ⟨who, ?_⟩
  have hpair := quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward roots
  have hcoordinate := congrFun (congrArg Prod.fst hpair) who
  have hcoordinate' : quittingTerminalPayoff
      (rationalQuittingRewardToReal reward)
      (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
        (roots.map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) who =
      ((rationalQuittingFiniteWordSemanticPair reward roots).1 who : ℝ) := by
    simpa only [quittingTerminalSemanticPair] using hcoordinate
  have hreal : ((rationalQuittingFiniteWordSemanticPair reward roots).1 who : ℝ) ≤
      (reward (quittingSingletonTerminal who) who - gap : ℚ) := by
    rw [← hcoordinate']
    simpa only [rationalQuittingRewardToReal, Rat.cast_sub] using hwho
  exact_mod_cast hreal

/-- Actual-profile strict deficit supplies the executable rational finite-word
source condition. -/
theorem rationalQuittingFiniteWordStrictSingletonDeficit_of_actual
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : HasQuittingActualStrictSingletonDeficit
      (rationalQuittingRewardToReal reward) (gap : ℝ)) :
    RationalQuittingFiniteWordStrictSingletonDeficit reward gap :=
  rationalQuittingFiniteWordStrictSingletonDeficit_of_real reward gap <| by
    intro roots
    exact hdeficit (quittingLiteralRootStackProfile
      (rationalQuittingRewardToReal reward) roots
      (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward)))

end GameTheory
