import MathUE.RealQuantifierElimination.QuantifierElimination
import UniformEquilibrium.Quitting.Paths.FiniteCalendarExclusionFormula
import UniformEquilibrium.Quitting.Paths.FiniteCalendarFormulaCoordinates
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Root.RationalReward

/-! # Exact rational decision for weak-subset finite-calendar exclusion -/

namespace GameTheory

open MathUE.RealQuantifierElimination

variable {players : Nat}

private abbrev rawDeadline (players : Nat) : Nat :=
  Fintype.card (Fin players) * (Fintype.card (Fin players) + 1)

/-- The explicit rational formula for weak-subset exclusion on one calendar. -/
def rationalQuittingFiniteCalendarRawWeakSubsetFormula
    (reward : RationalQuittingReward players) (owners : Finset (Fin players)) :
    QuantifierFreeFormula
      (quittingFiniteCalendarParameterCount players (rawDeadline players)) :=
  quittingFiniteCalendarRawWeakSubsetFormulaWithTerms
    (players := players) (deadline := rawDeadline players)
    (fun terminal observer => .const (reward terminal observer))
    quittingFiniteCalendarVariableTerm owners

/-- The closed sentence recognizing weak-subset exclusion for a rational table. -/
def rationalQuittingFiniteCalendarRawWeakSubsetSentence
    (reward : RationalQuittingReward players) (owners : Finset (Fin players)) :
    PolynomialFormula 0 :=
  (PolynomialFormula.ofQuantifierFree
    (rationalQuittingFiniteCalendarRawWeakSubsetFormula reward owners)).universallyClose

private theorem rationalRawWeakSubsetFormula_holdsAt_profile_iff
    (reward : RationalQuittingReward players) (owners : Finset (Fin players))
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction (rawDeadline players))) :
    (rationalQuittingFiniteCalendarRawWeakSubsetFormula reward owners).HoldsAt
        (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) ↔
      (∀ observer ∈ owners,
        0 ≤ rationalQuittingRewardToReal reward
          (quittingSingletonTerminal observer) observer) ∧
      ∃ observer ∈ owners,
        quittingFiniteCalendarRawPayoff (rationalQuittingRewardToReal reward)
            (rawDeadline players) profile observer ≤
          rationalQuittingRewardToReal reward
            (quittingSingletonTerminal observer) observer := by
  rw [rationalQuittingFiniteCalendarRawWeakSubsetFormula,
    quittingFiniteCalendarRawWeakSubsetFormulaWithTerms_holdsAt_iff]
  have hsimplex :=
    quittingFiniteCalendarSimplexFormula_holdsAt_parameters profile
  have hsimplexWithTerms :
      (quittingFiniteCalendarSimplexFormulaWithTerms
        (quittingFiniteCalendarVariableTerm (players := players)
          (deadline := rawDeadline players))).HoldsAt
        (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) := by
    simpa [quittingFiniteCalendarSimplexFormula] using hsimplex
  simp only [hsimplexWithTerms, not_true_eq_false, false_or,
    RingExpression.evalReal_const]
  constructor
  · rintro ⟨hsingleton, hexclusion⟩
    constructor
    · simpa only [rationalQuittingRewardToReal] using hsingleton
    · obtain ⟨observer, hobserver, hsurplus⟩ := hexclusion
      refine ⟨observer, hobserver, ?_⟩
      rw [evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms,
        evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
          (fun terminal who => RingExpression.const (reward terminal who))
          quittingFiniteCalendarVariableTerm observer _ profile
          (fun who choice =>
            evalReal_quittingFiniteCalendarVariableTerm_parameters profile (who, choice))]
        at hsurplus
      have hcast :
          quittingFiniteCalendarRawPayoff
              (fun terminal who => (reward terminal who : ℝ))
              (rawDeadline players) profile observer ≤
            (reward (quittingSingletonTerminal observer) observer : ℝ) := by
        simpa only [RingExpression.evalReal_const, sub_nonpos] using hsurplus
      change quittingFiniteCalendarRawPayoff
          (fun terminal who => (reward terminal who : ℝ))
          (rawDeadline players) profile observer ≤
        (reward (quittingSingletonTerminal observer) observer : ℝ)
      exact hcast
  · rintro ⟨hsingleton, observer, hobserver, hexclusion⟩
    constructor
    · simpa only [rationalQuittingRewardToReal] using hsingleton
    · refine ⟨observer, hobserver, ?_⟩
      rw [evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms,
        evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
          (fun terminal who => RingExpression.const (reward terminal who))
          quittingFiniteCalendarVariableTerm observer _ profile
          (fun who choice =>
            evalReal_quittingFiniteCalendarVariableTerm_parameters profile (who, choice))]
      change
        quittingFiniteCalendarRawPayoff
            (fun terminal who => (reward terminal who : ℝ))
            (rawDeadline players) profile observer ≤
          (reward (quittingSingletonTerminal observer) observer : ℝ) at hexclusion
      simpa only [RingExpression.evalReal_const, sub_nonpos] using hexclusion

private theorem rationalRawWeakSubsetFormula_forall_iff
    [Nonempty (Fin players)]
    (reward : RationalQuittingReward players) (owners : Finset (Fin players)) :
    (∀ environment,
      (rationalQuittingFiniteCalendarRawWeakSubsetFormula reward owners).HoldsAt
        environment) ↔
      HasQuittingFiniteCalendarRawWeakSubsetExclusion
        (rationalQuittingRewardToReal reward) owners := by
  unfold HasQuittingFiniteCalendarRawWeakSubsetExclusion
  constructor
  · intro hformula
    have hzero := hformula fun _ => 0
    rw [rationalQuittingFiniteCalendarRawWeakSubsetFormula,
      quittingFiniteCalendarRawWeakSubsetFormulaWithTerms_holdsAt_iff] at hzero
    refine ⟨?_, fun profile => ?_⟩
    · simpa only [RingExpression.evalReal_const, rationalQuittingRewardToReal] using hzero.1
    · exact (rationalRawWeakSubsetFormula_holdsAt_profile_iff reward owners profile).mp
        (hformula (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2)) |>.2
  · rintro ⟨hsingleton, hraw⟩ environment
    rw [rationalQuittingFiniteCalendarRawWeakSubsetFormula,
      quittingFiniteCalendarRawWeakSubsetFormulaWithTerms_holdsAt_iff]
    constructor
    · simpa only [RingExpression.evalReal_const, rationalQuittingRewardToReal] using hsingleton
    · by_cases hsimplex :
          (quittingFiniteCalendarSimplexFormula players (rawDeadline players)).HoldsAt
            environment
      · right
        let profile := quittingFiniteCalendarProfileOfParameters environment hsimplex
        obtain ⟨observer, hobserver, hexclusion⟩ := hraw profile
        refine ⟨observer, hobserver, ?_⟩
        rw [evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms,
          evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
            (fun terminal who => RingExpression.const (reward terminal who))
            quittingFiniteCalendarVariableTerm observer environment profile
            (fun _ _ => rfl)]
        change
          quittingFiniteCalendarRawPayoff
              (fun terminal who => (reward terminal who : ℝ))
              (rawDeadline players) profile observer ≤
            (reward (quittingSingletonTerminal observer) observer : ℝ) at hexclusion
        simpa only [RingExpression.evalReal_const, sub_nonpos] using hexclusion
      · left
        simpa [quittingFiniteCalendarSimplexFormula] using hsimplex

/-- The closed sentence has exactly the actual weak-subset raw semantics. -/
theorem rationalQuittingFiniteCalendarRawWeakSubsetSentence_holdsAt_iff
    [Nonempty (Fin players)]
    (reward : RationalQuittingReward players) (owners : Finset (Fin players)) :
    (rationalQuittingFiniteCalendarRawWeakSubsetSentence reward owners).HoldsAt
        Fin.elim0 ↔
      HasQuittingFiniteCalendarRawWeakSubsetExclusion
        (rationalQuittingRewardToReal reward) owners := by
  rw [rationalQuittingFiniteCalendarRawWeakSubsetSentence,
    PolynomialFormula.holdsAt_universallyClose_iff]
  simp only [PolynomialFormula.holdsAt_ofQuantifierFree_iff]
  exact rationalRawWeakSubsetFormula_forall_iff reward owners

/-- Execute real quantifier elimination on rational weak-subset exclusion. -/
def decideHasQuittingFiniteCalendarRawWeakSubsetExclusion
    (reward : RationalQuittingReward players) (owners : Finset (Fin players)) : Bool :=
  decideClosedFormula
    (rationalQuittingFiniteCalendarRawWeakSubsetSentence reward owners)

/-- The executable result is true exactly for actual weak-subset raw exclusion. -/
theorem decideHasQuittingFiniteCalendarRawWeakSubsetExclusion_eq_true_iff
    [Nonempty (Fin players)]
    (reward : RationalQuittingReward players) (owners : Finset (Fin players)) :
    decideHasQuittingFiniteCalendarRawWeakSubsetExclusion reward owners = true ↔
      HasQuittingFiniteCalendarRawWeakSubsetExclusion
        (rationalQuittingRewardToReal reward) owners := by
  rw [decideHasQuittingFiniteCalendarRawWeakSubsetExclusion,
    decideClosedFormula_eq_true_iff,
    rationalQuittingFiniteCalendarRawWeakSubsetSentence_holdsAt_iff]

end GameTheory
