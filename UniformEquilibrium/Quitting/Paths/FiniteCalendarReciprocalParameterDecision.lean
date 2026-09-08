import MathUE.RealQuantifierElimination.QuantifierElimination
import UniformEquilibrium.Quitting.Paths.FiniteCalendarExclusionFormula
import UniformEquilibrium.Quitting.Paths.FiniteCalendarFormulaCoordinates
import UniformEquilibrium.Quitting.Paths.FiniteCalendarOrderedPairGroupExclusion
import UniformEquilibrium.Quitting.Root.RationalReward

/-! # Exact decisions at fixed rational reciprocal parameters -/

namespace GameTheory

open Math.PolynomialSignCell.SignFormula
open MathUE.RealQuantifierElimination

variable {players deadline arity : Nat}

private abbrev reciprocalDeadline (players : Nat) : Nat :=
  Fintype.card (Fin players) * (Fintype.card (Fin players) + 1)

private abbrev reciprocalCalendarCount (players : Nat) : Nat :=
  quittingFiniteCalendarParameterCount players (reciprocalDeadline players)

/-- Strict singleton deficit at one calendar, guarded by the calendar simplex. -/
def quittingFiniteCalendarRawStrictDeficitFormulaWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (gap : RingExpression arity) : QuantifierFreeFormula arity :=
  .or (.not (quittingFiniteCalendarSimplexFormulaWithTerms calendarTerm))
    (disjunction (List.ofFn fun observer : Fin players =>
      QuantifierFreeFormula.nonpositive
        (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
          rewardTerm calendarTerm observer + gap)))

@[simp]
theorem quittingFiniteCalendarRawStrictDeficitFormulaWithTerms_holdsAt_iff
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (gap : RingExpression arity) (environment : Fin arity → ℝ) :
    (quittingFiniteCalendarRawStrictDeficitFormulaWithTerms
        rewardTerm calendarTerm gap).HoldsAt environment ↔
      (¬(quittingFiniteCalendarSimplexFormulaWithTerms calendarTerm).HoldsAt
          environment) ∨
        ∃ observer,
          (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
              rewardTerm calendarTerm observer).evalReal environment +
            gap.evalReal environment ≤ 0 := by
  change
    (¬(quittingFiniteCalendarSimplexFormulaWithTerms calendarTerm).HoldsAt
        environment) ∨
      (disjunction (List.ofFn fun observer : Fin players =>
        QuantifierFreeFormula.nonpositive
          (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
            rewardTerm calendarTerm observer + gap))).Holds
        (realSignAssignment environment) ↔ _
  rw [holds_disjunction_iff]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨formula, hformula, hholds⟩
    rw [List.mem_ofFn] at hformula
    obtain ⟨observer, rfl⟩ := hformula
    refine ⟨observer, ?_⟩
    have hnonpositive :=
      (QuantifierFreeFormula.holdsAt_nonpositive_iff _ environment).mp hholds
    simpa only [RingExpression.evalReal_add] using hnonpositive
  · rintro ⟨observer, hsurplus⟩
    refine ⟨QuantifierFreeFormula.nonpositive
      (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
        rewardTerm calendarTerm observer + gap), ?_, ?_⟩
    · exact List.mem_ofFn.mpr ⟨observer, rfl⟩
    · apply (QuantifierFreeFormula.holdsAt_nonpositive_iff _ environment).mpr
      simpa only [RingExpression.evalReal_add] using hsurplus

/-- The rational formula for a fixed strict-deficit gap. -/
def rationalQuittingFiniteCalendarRawStrictDeficitFormula
    (reward : RationalQuittingReward players) (gap : ℚ) :
    QuantifierFreeFormula (reciprocalCalendarCount players) :=
  quittingFiniteCalendarRawStrictDeficitFormulaWithTerms
    (players := players) (deadline := reciprocalDeadline players)
    (fun terminal observer => .const (reward terminal observer))
    quittingFiniteCalendarVariableTerm (.const gap)

/-- The closed fixed-gap strict-deficit sentence. -/
def rationalQuittingFiniteCalendarRawStrictDeficitSentence
    (reward : RationalQuittingReward players) (gap : ℚ) : PolynomialFormula 0 :=
  (PolynomialFormula.ofQuantifierFree
    (rationalQuittingFiniteCalendarRawStrictDeficitFormula reward gap)).universallyClose

private theorem rationalRawStrictDeficitFormula_holdsAt_profile_iff
    (reward : RationalQuittingReward players) (gap : ℚ)
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction
        (reciprocalDeadline players))) :
    (rationalQuittingFiniteCalendarRawStrictDeficitFormula reward gap).HoldsAt
        (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) ↔
      ∃ observer,
        quittingFiniteCalendarRawPayoff (rationalQuittingRewardToReal reward)
            (reciprocalDeadline players) profile observer ≤
          rationalQuittingRewardToReal reward
            (quittingSingletonTerminal observer) observer - (gap : ℝ) := by
  rw [rationalQuittingFiniteCalendarRawStrictDeficitFormula,
    quittingFiniteCalendarRawStrictDeficitFormulaWithTerms_holdsAt_iff]
  have hsimplex :
      (quittingFiniteCalendarSimplexFormulaWithTerms
        (quittingFiniteCalendarVariableTerm (players := players)
          (deadline := reciprocalDeadline players))).HoldsAt
        (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) := by
    simpa [quittingFiniteCalendarSimplexFormula] using
      quittingFiniteCalendarSimplexFormula_holdsAt_parameters profile
  simp only [hsimplex, not_true_eq_false, false_or]
  apply exists_congr
  intro observer
  rw [evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms,
    evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
      (fun terminal who => RingExpression.const (reward terminal who))
      quittingFiniteCalendarVariableTerm observer _ profile
      (fun who choice =>
        evalReal_quittingFiniteCalendarVariableTerm_parameters profile (who, choice))]
  simp only [RingExpression.evalReal_const]
  change
    (quittingFiniteCalendarRawPayoff
          (fun terminal who => (reward terminal who : ℝ))
          (reciprocalDeadline players) profile observer -
        (reward (quittingSingletonTerminal observer) observer : ℝ) +
      (gap : ℝ) ≤ 0) ↔
      quittingFiniteCalendarRawPayoff
          (fun terminal who => (reward terminal who : ℝ))
          (reciprocalDeadline players) profile observer ≤
        (reward (quittingSingletonTerminal observer) observer : ℝ) - (gap : ℝ)
  constructor <;> intro h <;> linarith

private theorem rationalRawStrictDeficitFormula_forall_iff
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) (gap : ℚ) :
    (∀ environment,
      (rationalQuittingFiniteCalendarRawStrictDeficitFormula reward gap).HoldsAt
        environment) ↔
      HasQuittingFiniteCalendarRawStrictSingletonDeficit
        (rationalQuittingRewardToReal reward) (gap : ℝ) := by
  unfold HasQuittingFiniteCalendarRawStrictSingletonDeficit
  constructor
  · intro hformula profile
    exact (rationalRawStrictDeficitFormula_holdsAt_profile_iff
      reward gap profile).mp
        (hformula (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2))
  · intro hraw environment
    by_cases hsimplex :
        (quittingFiniteCalendarSimplexFormula players
          (reciprocalDeadline players)).HoldsAt environment
    · let profile := quittingFiniteCalendarProfileOfParameters environment hsimplex
      rw [rationalQuittingFiniteCalendarRawStrictDeficitFormula,
        quittingFiniteCalendarRawStrictDeficitFormulaWithTerms_holdsAt_iff]
      right
      obtain ⟨observer, hobserver⟩ := hraw profile
      refine ⟨observer, ?_⟩
      rw [evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms,
        evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
          (fun terminal who => RingExpression.const (reward terminal who))
          quittingFiniteCalendarVariableTerm observer environment profile
          (fun _ _ => rfl)]
      simp only [RingExpression.evalReal_const]
      change quittingFiniteCalendarRawPayoff
          (fun terminal who => (reward terminal who : ℝ))
          (reciprocalDeadline players) profile observer ≤
        (reward (quittingSingletonTerminal observer) observer : ℝ) - (gap : ℝ)
        at hobserver
      linarith
    · rw [rationalQuittingFiniteCalendarRawStrictDeficitFormula,
        quittingFiniteCalendarRawStrictDeficitFormulaWithTerms_holdsAt_iff]
      exact Or.inl (by
        simpa [quittingFiniteCalendarSimplexFormula] using hsimplex)

/-- The fixed-gap sentence has exactly the raw strict-deficit semantics. -/
theorem rationalQuittingFiniteCalendarRawStrictDeficitSentence_holdsAt_iff
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) (gap : ℚ) :
    (rationalQuittingFiniteCalendarRawStrictDeficitSentence reward gap).HoldsAt
        Fin.elim0 ↔
      HasQuittingFiniteCalendarRawStrictSingletonDeficit
        (rationalQuittingRewardToReal reward) (gap : ℝ) := by
  rw [rationalQuittingFiniteCalendarRawStrictDeficitSentence,
    PolynomialFormula.holdsAt_universallyClose_iff]
  simp only [PolynomialFormula.holdsAt_ofQuantifierFree_iff]
  exact rationalRawStrictDeficitFormula_forall_iff reward gap

/-- Decide strict deficit at one supplied rational gap. -/
def decideHasQuittingFiniteCalendarRawStrictSingletonDeficit
    (reward : RationalQuittingReward players) (gap : ℚ) : Bool :=
  decideClosedFormula
    (rationalQuittingFiniteCalendarRawStrictDeficitSentence reward gap)

/-- The fixed-gap decision has exactly the raw strict-deficit semantics. -/
theorem decideHasQuittingFiniteCalendarRawStrictSingletonDeficit_eq_true_iff
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) (gap : ℚ) :
    decideHasQuittingFiniteCalendarRawStrictSingletonDeficit reward gap = true ↔
      HasQuittingFiniteCalendarRawStrictSingletonDeficit
        (rationalQuittingRewardToReal reward) (gap : ℝ) := by
  rw [decideHasQuittingFiniteCalendarRawStrictSingletonDeficit,
    decideClosedFormula_eq_true_iff,
    rationalQuittingFiniteCalendarRawStrictDeficitSentence_holdsAt_iff]

/-- The rational one-calendar ordered-pair formula at a fixed lambda. -/
def rationalQuittingFiniteCalendarRawOrderedPairAtFormula
    (reward : RationalQuittingReward players) (lambda : ℚ) :
    QuantifierFreeFormula (reciprocalCalendarCount players) :=
  quittingFiniteCalendarRawOrderedPairFormulaWithTerms
    (players := players) (deadline := reciprocalDeadline players)
    (fun terminal observer => .const (reward terminal observer))
    quittingFiniteCalendarVariableTerm (.const lambda)

/-- The closed ordered-pair sentence at a fixed rational lambda. -/
def rationalQuittingFiniteCalendarRawOrderedPairAtSentence
    (reward : RationalQuittingReward players) (lambda : ℚ) : PolynomialFormula 0 :=
  (PolynomialFormula.ofQuantifierFree
    (rationalQuittingFiniteCalendarRawOrderedPairAtFormula reward lambda)).universallyClose

private theorem rationalRawOrderedPairAtFormula_holdsAt_profile_iff
    (reward : RationalQuittingReward players) (lambda : ℚ)
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction
        (reciprocalDeadline players))) :
    (rationalQuittingFiniteCalendarRawOrderedPairAtFormula reward lambda).HoldsAt
        (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) ↔
      ∃ first second, first ≠ second ∧
        (1 - (lambda : ℝ)) *
            (quittingFiniteCalendarRawPayoff
                (rationalQuittingRewardToReal reward)
                (reciprocalDeadline players) profile first -
              rationalQuittingRewardToReal reward
                (quittingSingletonTerminal first) first) +
          (lambda : ℝ) *
            (quittingFiniteCalendarRawPayoff
                (rationalQuittingRewardToReal reward)
                (reciprocalDeadline players) profile second -
              rationalQuittingRewardToReal reward
                (quittingSingletonTerminal second) second) ≤ 0 := by
  rw [rationalQuittingFiniteCalendarRawOrderedPairAtFormula,
    quittingFiniteCalendarRawOrderedPairFormulaWithTerms_holdsAt_iff]
  have hsimplex :
      (quittingFiniteCalendarSimplexFormulaWithTerms
        (quittingFiniteCalendarVariableTerm (players := players)
          (deadline := reciprocalDeadline players))).HoldsAt
        (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) := by
    simpa [quittingFiniteCalendarSimplexFormula] using
      quittingFiniteCalendarSimplexFormula_holdsAt_parameters profile
  simp only [hsimplex, not_true_eq_false, false_or]
  apply exists_congr
  intro first
  apply exists_congr
  intro second
  apply and_congr Iff.rfl
  rw [evalReal_quittingFiniteCalendarOrderedPairSurplusExpressionWithTerms]
  have hterm : ∀ observer,
      (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
        (fun terminal who => RingExpression.const (reward terminal who))
        quittingFiniteCalendarVariableTerm observer).evalReal
          (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) =
        quittingFiniteCalendarRawPayoff
            (fun terminal who => (reward terminal who : ℝ))
            (reciprocalDeadline players) profile observer -
          (reward (quittingSingletonTerminal observer) observer : ℝ) := by
    intro observer
    rw [evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms,
      evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
        (fun terminal who => RingExpression.const (reward terminal who))
        quittingFiniteCalendarVariableTerm observer _ profile
        (fun who choice =>
          evalReal_quittingFiniteCalendarVariableTerm_parameters profile (who, choice))]
    simp only [RingExpression.evalReal_const]
  simp only [RingExpression.evalReal_const, hterm]
  change _ ↔
    (1 - (lambda : ℝ)) *
          (quittingFiniteCalendarRawPayoff
              (fun terminal who => (reward terminal who : ℝ))
              (reciprocalDeadline players) profile first -
            (reward (quittingSingletonTerminal first) first : ℝ)) +
        (lambda : ℝ) *
          (quittingFiniteCalendarRawPayoff
              (fun terminal who => (reward terminal who : ℝ))
              (reciprocalDeadline players) profile second -
            (reward (quittingSingletonTerminal second) second : ℝ)) ≤ 0
  rfl

private theorem rationalRawOrderedPairAtFormula_forall_iff
    [Nonempty (Fin players)]
    (reward : RationalQuittingReward players) (lambda : ℚ) :
    (∀ environment,
      (rationalQuittingFiniteCalendarRawOrderedPairAtFormula reward lambda).HoldsAt
        environment) ↔
      HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
        (rationalQuittingRewardToReal reward) (lambda : ℝ) := by
  unfold HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
  constructor
  · intro hformula profile
    exact (rationalRawOrderedPairAtFormula_holdsAt_profile_iff
      reward lambda profile).mp
        (hformula (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2))
  · intro hraw environment
    by_cases hsimplex :
        (quittingFiniteCalendarSimplexFormula players
          (reciprocalDeadline players)).HoldsAt environment
    · let profile := quittingFiniteCalendarProfileOfParameters environment hsimplex
      rw [rationalQuittingFiniteCalendarRawOrderedPairAtFormula,
        quittingFiniteCalendarRawOrderedPairFormulaWithTerms_holdsAt_iff]
      right
      obtain ⟨first, second, hne, hweighted⟩ := hraw profile
      refine ⟨first, second, hne, ?_⟩
      rw [evalReal_quittingFiniteCalendarOrderedPairSurplusExpressionWithTerms]
      have hterm : ∀ observer,
          (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
            (fun terminal who => RingExpression.const (reward terminal who))
            quittingFiniteCalendarVariableTerm observer).evalReal environment =
              quittingFiniteCalendarRawPayoff
                  (fun terminal who => (reward terminal who : ℝ))
                  (reciprocalDeadline players) profile observer -
                (reward (quittingSingletonTerminal observer) observer : ℝ) := by
        intro observer
        rw [evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms,
          evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
            (fun terminal who => RingExpression.const (reward terminal who))
            quittingFiniteCalendarVariableTerm observer environment profile
            (fun _ _ => rfl)]
        simp only [RingExpression.evalReal_const]
      simp only [RingExpression.evalReal_const, hterm]
      change
        (1 - (lambda : ℝ)) *
              (quittingFiniteCalendarRawPayoff
                  (fun terminal who => (reward terminal who : ℝ))
                  (reciprocalDeadline players) profile first -
                (reward (quittingSingletonTerminal first) first : ℝ)) +
            (lambda : ℝ) *
              (quittingFiniteCalendarRawPayoff
                  (fun terminal who => (reward terminal who : ℝ))
                  (reciprocalDeadline players) profile second -
                (reward (quittingSingletonTerminal second) second : ℝ)) ≤ 0
          at hweighted
      exact hweighted
    · rw [rationalQuittingFiniteCalendarRawOrderedPairAtFormula,
        quittingFiniteCalendarRawOrderedPairFormulaWithTerms_holdsAt_iff]
      exact Or.inl (by
        simpa [quittingFiniteCalendarSimplexFormula] using hsimplex)

/-- The fixed-lambda sentence has exactly the raw ordered-pair semantics. -/
theorem rationalQuittingFiniteCalendarRawOrderedPairAtSentence_holdsAt_iff
    [Nonempty (Fin players)]
    (reward : RationalQuittingReward players) (lambda : ℚ) :
    (rationalQuittingFiniteCalendarRawOrderedPairAtSentence reward lambda).HoldsAt
        Fin.elim0 ↔
      HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
        (rationalQuittingRewardToReal reward) (lambda : ℝ) := by
  rw [rationalQuittingFiniteCalendarRawOrderedPairAtSentence,
    PolynomialFormula.holdsAt_universallyClose_iff]
  simp only [PolynomialFormula.holdsAt_ofQuantifierFree_iff]
  exact rationalRawOrderedPairAtFormula_forall_iff reward lambda

/-- Decide ordered-pair group exclusion at one supplied rational lambda. -/
def decideHasQuittingFiniteCalendarRawOrderedPairGroupExclusion
    (reward : RationalQuittingReward players) (lambda : ℚ) : Bool :=
  decideClosedFormula
    (rationalQuittingFiniteCalendarRawOrderedPairAtSentence reward lambda)

/-- The fixed-lambda decision has exactly the raw ordered-pair semantics. -/
theorem decideHasQuittingFiniteCalendarRawOrderedPairGroupExclusion_eq_true_iff
    [Nonempty (Fin players)]
    (reward : RationalQuittingReward players) (lambda : ℚ) :
    decideHasQuittingFiniteCalendarRawOrderedPairGroupExclusion reward lambda = true ↔
      HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
        (rationalQuittingRewardToReal reward) (lambda : ℝ) := by
  rw [decideHasQuittingFiniteCalendarRawOrderedPairGroupExclusion,
    decideClosedFormula_eq_true_iff,
    rationalQuittingFiniteCalendarRawOrderedPairAtSentence_holdsAt_iff]

end GameTheory
