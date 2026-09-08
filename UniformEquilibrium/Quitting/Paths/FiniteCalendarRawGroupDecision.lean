import MathUE.RealQuantifierElimination.QuantifierBlocks
import MathUE.RealQuantifierElimination.QuantifierElimination
import UniformEquilibrium.Quitting.Paths.FiniteCalendarExclusionFormula
import UniformEquilibrium.Quitting.Paths.FiniteCalendarFormulaCoordinates
import UniformEquilibrium.Quitting.Paths.FiniteCalendarOrderedPairGroupExclusion
import UniformEquilibrium.Quitting.Root.RationalReward

/-! # Exact rational decision for finite-calendar group exclusion -/

namespace GameTheory

open MathUE.RealQuantifierElimination

variable {players : Nat}

private abbrev rawDeadline (players : Nat) : Nat :=
  Fintype.card (Fin players) * (Fintype.card (Fin players) + 1)

private abbrev calendarCount (players : Nat) : Nat :=
  quittingFiniteCalendarParameterCount players (rawDeadline players)

private def groupCalendarTerm
    (entry : QuittingFiniteCalendarVariable (Fin players) (rawDeadline players)) :
    RingExpression (1 + calendarCount players) :=
  .var (PolynomialFormula.leadingBlockIndex 1
    (quittingFiniteCalendarVariableIndex entry))

private def groupLambdaTerm (players : Nat) :
    RingExpression (1 + calendarCount players) :=
  .var (PolynomialFormula.trailingBlockIndex 1 (calendarCount players) 0)

private def groupEnvironment
    (calendar : Fin (calendarCount players) → ℝ) (lambda : ℝ) :
    Fin (1 + calendarCount players) → ℝ :=
  PolynomialFormula.blockEnvironment calendar (fun _ : Fin 1 => lambda)

@[simp]
private theorem evalReal_groupCalendarTerm
    (calendar : Fin (calendarCount players) → ℝ) (lambda : ℝ)
    (entry : QuittingFiniteCalendarVariable (Fin players) (rawDeadline players)) :
    (groupCalendarTerm entry).evalReal (groupEnvironment calendar lambda) =
      quittingFiniteCalendarFromParameters calendar entry := by
  simp [groupCalendarTerm, groupEnvironment, quittingFiniteCalendarFromParameters]

@[simp]
private theorem evalReal_groupLambdaTerm
    (calendar : Fin (calendarCount players) → ℝ) (lambda : ℝ) :
    (groupLambdaTerm players).evalReal (groupEnvironment calendar lambda) = lambda := by
  simp [groupLambdaTerm, groupEnvironment]

/-- The ordered-pair group formula at one raw calendar and one mixture parameter. -/
def rationalQuittingFiniteCalendarRawOrderedPairFormula
    (reward : RationalQuittingReward players) :
    QuantifierFreeFormula (1 + calendarCount players) :=
  quittingFiniteCalendarRawOrderedPairFormulaWithTerms
    (players := players) (deadline := rawDeadline players)
    (fun terminal observer => .const (reward terminal observer))
    groupCalendarTerm (groupLambdaTerm players)

/-- The admissible interval `(0, 1/2]` for the uniform pair parameter. -/
def quittingOrderedPairLambdaRangeFormula : QuantifierFreeFormula 1 :=
  .and (QuantifierFreeFormula.positive (.var 0))
    (QuantifierFreeFormula.nonpositive (.var 0 + -.const (1 / 2)))

@[simp]
theorem quittingOrderedPairLambdaRangeFormula_holdsAt_iff (lambda : ℝ) :
    quittingOrderedPairLambdaRangeFormula.HoldsAt (fun _ => lambda) ↔
      0 < lambda ∧ lambda ≤ (1 : ℝ) / 2 := by
  change
    (QuantifierFreeFormula.positive (.var 0)).HoldsAt (fun _ => lambda) ∧
      (QuantifierFreeFormula.nonpositive
        (.var 0 + -.const (1 / 2))).HoldsAt (fun _ => lambda) ↔ _
  rw [QuantifierFreeFormula.holdsAt_positive_iff,
    QuantifierFreeFormula.holdsAt_nonpositive_iff]
  norm_num

/-- The closed sentence with one uniform parameter outside all calendars. -/
def rationalQuittingFiniteCalendarRawGroupSentence
    (reward : RationalQuittingReward players) : PolynomialFormula 0 :=
  .ex (.and
    (PolynomialFormula.ofQuantifierFree quittingOrderedPairLambdaRangeFormula)
    (PolynomialFormula.universallyQuantifyFirst (calendarCount players)
      (PolynomialFormula.ofQuantifierFree
        (rationalQuittingFiniteCalendarRawOrderedPairFormula reward))))

private theorem rationalRawOrderedPairFormula_holdsAt_profile_iff
    (reward : RationalQuittingReward players) (lambda : ℝ)
    (calendar : Fin (calendarCount players) → ℝ)
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction (rawDeadline players)))
    (hcalendar : ∀ who choice,
      quittingFiniteCalendarFromParameters calendar (who, choice) =
        profile who choice) :
    (rationalQuittingFiniteCalendarRawOrderedPairFormula reward).HoldsAt
        (groupEnvironment calendar lambda) ↔
      ∃ first second, first ≠ second ∧
        (1 - lambda) *
            (quittingFiniteCalendarRawPayoff (rationalQuittingRewardToReal reward)
              (rawDeadline players) profile first -
                rationalQuittingRewardToReal reward
                  (quittingSingletonTerminal first) first) +
          lambda *
            (quittingFiniteCalendarRawPayoff (rationalQuittingRewardToReal reward)
              (rawDeadline players) profile second -
                rationalQuittingRewardToReal reward
                  (quittingSingletonTerminal second) second) ≤ 0 := by
  rw [rationalQuittingFiniteCalendarRawOrderedPairFormula,
    quittingFiniteCalendarRawOrderedPairFormulaWithTerms_holdsAt_iff]
  have hsimplex :
      (quittingFiniteCalendarSimplexFormulaWithTerms
        (groupCalendarTerm (players := players))).HoldsAt
          (groupEnvironment calendar lambda) := by
    apply (quittingFiniteCalendarSimplexFormulaWithTerms_holdsAt_iff _ _).mpr
    constructor
    · intro who choice
      rw [evalReal_groupCalendarTerm, hcalendar]
      exact (profile who).property.1 choice
    · intro who
      simp only [evalReal_groupCalendarTerm, hcalendar]
      have htotal := (profile who).property.2
      rw [Fintype.sum_option] at htotal
      exact htotal
  simp only [hsimplex, not_true_eq_false, false_or]
  apply exists_congr
  intro first
  apply exists_congr
  intro second
  apply and_congr Iff.rfl
  rw [evalReal_quittingFiniteCalendarOrderedPairSurplusExpressionWithTerms,
    evalReal_groupLambdaTerm]
  have hterm : ∀ observer,
      (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
        (fun terminal who => RingExpression.const (reward terminal who))
        groupCalendarTerm observer).evalReal (groupEnvironment calendar lambda) =
      quittingFiniteCalendarRawPayoff
          (fun terminal who => (reward terminal who : ℝ))
          (rawDeadline players) profile observer -
        (reward (quittingSingletonTerminal observer) observer : ℝ) := by
    intro observer
    rw [evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms,
      evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
        (fun terminal who => RingExpression.const (reward terminal who))
        groupCalendarTerm observer (groupEnvironment calendar lambda) profile
        (fun who choice => (evalReal_groupCalendarTerm calendar lambda (who, choice)).trans
          (hcalendar who choice))]
    simp only [RingExpression.evalReal_const]
  rw [hterm first, hterm second]
  rfl

private theorem rationalRawOrderedPairFormula_forall_iff
    [Nonempty (Fin players)]
    (reward : RationalQuittingReward players) (lambda : ℝ) :
    (∀ calendar,
      (rationalQuittingFiniteCalendarRawOrderedPairFormula reward).HoldsAt
        (groupEnvironment calendar lambda)) ↔
      HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
        (rationalQuittingRewardToReal reward) lambda := by
  unfold HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
  constructor
  · intro hformula profile
    have hresult :=
      (rationalRawOrderedPairFormula_holdsAt_profile_iff reward lambda
        (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) profile
        (fun who choice => by
          rw [quittingFiniteCalendarFromParameters_encode])).mp
        (hformula (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2))
    exact hresult
  · intro hraw calendar
    by_cases hsimplex :
        (quittingFiniteCalendarSimplexFormulaWithTerms
          (groupCalendarTerm (players := players))).HoldsAt
            (groupEnvironment calendar lambda)
    · have hconditions :=
        (quittingFiniteCalendarSimplexFormulaWithTerms_holdsAt_iff _ _).mp hsimplex
      have hspecialized :
          (quittingFiniteCalendarSimplexFormula players (rawDeadline players)).HoldsAt
            calendar := by
        apply (quittingFiniteCalendarSimplexFormula_holdsAt_iff calendar).mpr
        simpa only [evalReal_groupCalendarTerm] using hconditions
      let profile := quittingFiniteCalendarProfileOfParameters calendar hspecialized
      apply (rationalRawOrderedPairFormula_holdsAt_profile_iff reward lambda calendar
        profile (fun _ _ => rfl)).mpr
      exact hraw profile
    · rw [rationalQuittingFiniteCalendarRawOrderedPairFormula,
        quittingFiniteCalendarRawOrderedPairFormulaWithTerms_holdsAt_iff]
      exact Or.inl hsimplex

/-- The closed sentence has exactly the existing raw group-exclusion semantics. -/
theorem rationalQuittingFiniteCalendarRawGroupSentence_holdsAt_iff
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) :
    (rationalQuittingFiniteCalendarRawGroupSentence reward).HoldsAt Fin.elim0 ↔
      ∃ beta < 1, HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion
        (rationalQuittingRewardToReal reward) beta := by
  rw [rationalQuittingFiniteCalendarRawGroupSentence]
  change (∃ lambda : ℝ,
    (PolynomialFormula.ofQuantifierFree
      quittingOrderedPairLambdaRangeFormula).HoldsAt
        (Fin.cases lambda Fin.elim0) ∧
      (PolynomialFormula.universallyQuantifyFirst (calendarCount players)
        (PolynomialFormula.ofQuantifierFree
          (rationalQuittingFiniteCalendarRawOrderedPairFormula reward))).HoldsAt
            (Fin.cases lambda Fin.elim0)) ↔ _
  have hsingle (lambda : ℝ) :
      Fin.cases lambda Fin.elim0 = fun _ : Fin 1 => lambda := by
    funext index
    fin_cases index
    rfl
  simp only [PolynomialFormula.holdsAt_ofQuantifierFree_iff, hsingle,
    quittingOrderedPairLambdaRangeFormula_holdsAt_iff,
    PolynomialFormula.holdsAt_universallyQuantifyFirst_iff]
  rw [exists_finiteCalendarRawNonconcentratedGroupExclusion_iff_orderedPair]
  apply exists_congr
  intro lambda
  rw [and_assoc]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  exact rationalRawOrderedPairFormula_forall_iff reward lambda

/-- Execute real quantifier elimination on rational raw group exclusion. -/
def decideExistsQuittingFiniteCalendarRawGroupExclusion
    (reward : RationalQuittingReward players) : Bool :=
  decideClosedFormula (rationalQuittingFiniteCalendarRawGroupSentence reward)

/-- The executable result is true exactly for actual raw group exclusion. -/
theorem decideExistsQuittingFiniteCalendarRawGroupExclusion_eq_true_iff
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) :
    decideExistsQuittingFiniteCalendarRawGroupExclusion reward = true ↔
      ∃ beta < 1, HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion
        (rationalQuittingRewardToReal reward) beta := by
  rw [decideExistsQuittingFiniteCalendarRawGroupExclusion,
    decideClosedFormula_eq_true_iff,
    rationalQuittingFiniteCalendarRawGroupSentence_holdsAt_iff]

end GameTheory
