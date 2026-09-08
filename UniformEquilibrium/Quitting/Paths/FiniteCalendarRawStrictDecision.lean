import MathUE.RealQuantifierElimination.QuantifierElimination
import UniformEquilibrium.Quitting.Paths.FiniteCalendarFormulaCoordinates
import UniformEquilibrium.Quitting.Paths.FiniteCalendarPayoffFormula
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Root.RationalReward

/-! # Exact rational decision for strict finite-calendar payoff exclusion -/

namespace GameTheory

open MathUE.RealQuantifierElimination

variable {players : Nat}

/-- The exact finite-calendar deadline used by the raw exclusion predicate. -/
def quittingRawExclusionDeadline (players : Nat) : Nat :=
  Fintype.card (Fin players) * (Fintype.card (Fin players) + 1)

/-- The explicit rational formula for strict raw exclusion on one calendar. -/
def rationalQuittingFiniteCalendarRawStrictFormula
    (reward : RationalQuittingReward players) :
    QuantifierFreeFormula
      (quittingFiniteCalendarParameterCount players
        (quittingRawExclusionDeadline players)) :=
  quittingFiniteCalendarRawStrictFormulaWithTerms
    (players := players) (deadline := quittingRawExclusionDeadline players)
    (fun terminal observer => .const (reward terminal observer))
    quittingFiniteCalendarVariableTerm

/-- The closed sentence recognizing strict raw exclusion for a rational table. -/
def rationalQuittingFiniteCalendarRawStrictSentence
    (reward : RationalQuittingReward players) : PolynomialFormula 0 :=
  (PolynomialFormula.ofQuantifierFree
    (rationalQuittingFiniteCalendarRawStrictFormula reward)).universallyClose

private theorem rationalQuittingFiniteCalendarRawStrictFormula_holdsAt_profile_iff
    (reward : RationalQuittingReward players)
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction
        (quittingRawExclusionDeadline players))) :
    (rationalQuittingFiniteCalendarRawStrictFormula reward).HoldsAt
        (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) ↔
      ∃ observer,
        quittingFiniteCalendarRawPayoff (rationalQuittingRewardToReal reward)
            (quittingRawExclusionDeadline players) profile observer <
          rationalQuittingRewardToReal reward
            (quittingSingletonTerminal observer) observer := by
  rw [rationalQuittingFiniteCalendarRawStrictFormula]
  have hresult :=
    quittingFiniteCalendarRawStrictFormulaWithTerms_holdsAt_profile_iff
      (players := players) (deadline := quittingRawExclusionDeadline players)
      (fun terminal observer => RingExpression.const (reward terminal observer))
      quittingFiniteCalendarVariableTerm
      (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2)
      profile (fun who choice =>
        evalReal_quittingFiniteCalendarVariableTerm_parameters profile (who, choice))
  change _ ↔ ∃ observer,
    quittingFiniteCalendarRawPayoff
        (fun terminal who => (reward terminal who : ℝ))
        (quittingRawExclusionDeadline players) profile observer <
      (reward (quittingSingletonTerminal observer) observer : ℝ)
  exact hresult

private theorem rationalQuittingFiniteCalendarRawStrictFormula_forall_iff
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) :
    (∀ environment,
      (rationalQuittingFiniteCalendarRawStrictFormula reward).HoldsAt environment) ↔
      HasQuittingFiniteCalendarRawStrictExclusion
        (rationalQuittingRewardToReal reward) := by
  unfold HasQuittingFiniteCalendarRawStrictExclusion
  constructor
  · intro hformula profile
    exact (rationalQuittingFiniteCalendarRawStrictFormula_holdsAt_profile_iff
      reward profile).mp
        (hformula (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2))
  · intro hraw environment
    by_cases hsimplex :
        (quittingFiniteCalendarSimplexFormula players
          (quittingRawExclusionDeadline players)).HoldsAt environment
    · let profile := quittingFiniteCalendarProfileOfParameters environment hsimplex
      have hcalendar : ∀ who choice,
          (quittingFiniteCalendarVariableTerm (who, choice)).evalReal environment =
            profile who choice := by
        intro who choice
        rfl
      have hprofile := hraw profile
      have hresult :=
        (quittingFiniteCalendarRawStrictFormulaWithTerms_holdsAt_profile_iff
          (players := players) (deadline := quittingRawExclusionDeadline players)
          (fun terminal observer => RingExpression.const (reward terminal observer))
          quittingFiniteCalendarVariableTerm
          environment profile hcalendar).mpr
      apply hresult
      change ∃ observer,
        quittingFiniteCalendarRawPayoff
            (fun terminal who => (reward terminal who : ℝ))
            (quittingRawExclusionDeadline players) profile observer <
          (reward (quittingSingletonTerminal observer) observer : ℝ) at hprofile
      simpa only [RingExpression.evalReal_const] using hprofile
    · apply
        (quittingFiniteCalendarRawStrictFormulaWithTerms_holdsAt_iff
          (players := players) (deadline := quittingRawExclusionDeadline players)
          (fun terminal observer => RingExpression.const (reward terminal observer))
          quittingFiniteCalendarVariableTerm
          environment).mpr
      exact Or.inl (by
        simpa [quittingFiniteCalendarSimplexFormula] using hsimplex)

/-- The closed sentence has exactly the actual strict raw-exclusion semantics. -/
theorem rationalQuittingFiniteCalendarRawStrictSentence_holdsAt_iff
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) :
    (rationalQuittingFiniteCalendarRawStrictSentence reward).HoldsAt Fin.elim0 ↔
      HasQuittingFiniteCalendarRawStrictExclusion
        (rationalQuittingRewardToReal reward) := by
  rw [rationalQuittingFiniteCalendarRawStrictSentence,
    PolynomialFormula.holdsAt_universallyClose_iff]
  simp only [PolynomialFormula.holdsAt_ofQuantifierFree_iff]
  exact rationalQuittingFiniteCalendarRawStrictFormula_forall_iff reward

/-- Execute real quantifier elimination on strict raw exclusion for a rational table. -/
def decideHasQuittingFiniteCalendarRawStrictExclusion
    (reward : RationalQuittingReward players) : Bool :=
  decideClosedFormula (rationalQuittingFiniteCalendarRawStrictSentence reward)

/-- The executable result is true exactly for actual strict raw exclusion. -/
theorem decideHasQuittingFiniteCalendarRawStrictExclusion_eq_true_iff
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) :
    decideHasQuittingFiniteCalendarRawStrictExclusion reward = true ↔
      HasQuittingFiniteCalendarRawStrictExclusion
        (rationalQuittingRewardToReal reward) := by
  rw [decideHasQuittingFiniteCalendarRawStrictExclusion,
    decideClosedFormula_eq_true_iff,
    rationalQuittingFiniteCalendarRawStrictSentence_holdsAt_iff]

end GameTheory
