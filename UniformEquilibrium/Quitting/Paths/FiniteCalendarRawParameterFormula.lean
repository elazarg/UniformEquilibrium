import MathUE.RealQuantifierElimination.QuantifierBlocks
import UniformEquilibrium.Quitting.Paths.FiniteCalendarExclusionFormula
import UniformEquilibrium.Quitting.Paths.FiniteCalendarFormulaCoordinates
import UniformEquilibrium.Quitting.Paths.FiniteCalendarOrderedPairGroupExclusion
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Root.RewardTableParameters

/-! # Reward-parameter formulas for finite-calendar raw exclusion -/

namespace GameTheory

open MathUE.RealQuantifierElimination

variable {players : Nat}

private abbrev rawDeadline (players : Nat) : Nat :=
  Fintype.card (Fin players) * (Fintype.card (Fin players) + 1)

private abbrev rewardCount (players : Nat) : Nat :=
  quittingRewardParameterCount players

private abbrev calendarCount (players : Nat) : Nat :=
  quittingFiniteCalendarParameterCount players (rawDeadline players)

/-- A calendar variable in the leading universally quantified block. -/
def rawExclusionCalendarTerm
    (entry : QuittingFiniteCalendarVariable (Fin players) (rawDeadline players)) :
    RingExpression (rewardCount players + calendarCount players) :=
  .var (PolynomialFormula.leadingBlockIndex (rewardCount players)
    (quittingFiniteCalendarVariableIndex entry))

/-- A reward variable in the trailing free parameter block. -/
def rawExclusionRewardTerm
    (terminal : {S : Finset (Fin players) // S.Nonempty}) (observer : Fin players) :
    RingExpression (rewardCount players + calendarCount players) :=
  .var (PolynomialFormula.trailingBlockIndex (rewardCount players)
    (calendarCount players) (quittingRewardTableVariableIndex (terminal, observer)))

@[simp]
theorem evalReal_rawExclusionCalendarTerm
    (calendar : Fin (calendarCount players) → ℝ)
    (parameters : Fin (rewardCount players) → ℝ)
    (entry : QuittingFiniteCalendarVariable (Fin players) (rawDeadline players)) :
    (rawExclusionCalendarTerm entry).evalReal
        (PolynomialFormula.blockEnvironment calendar parameters) =
      quittingFiniteCalendarFromParameters calendar entry := by
  simp [rawExclusionCalendarTerm, quittingFiniteCalendarFromParameters]

@[simp]
theorem evalReal_rawExclusionRewardTerm
    (calendar : Fin (calendarCount players) → ℝ)
    (parameters : Fin (rewardCount players) → ℝ)
    (terminal : {S : Finset (Fin players) // S.Nonempty}) (observer : Fin players) :
    (rawExclusionRewardTerm terminal observer).evalReal
        (PolynomialFormula.blockEnvironment calendar parameters) =
      quittingRewardFromParameters parameters terminal observer := by
  simp [rawExclusionRewardTerm, quittingRewardFromParameters]

/-- Strict raw exclusion with the reward table left as free parameters. -/
def rawStrictExclusionParameterFormula : PolynomialFormula (rewardCount players) :=
  PolynomialFormula.universallyQuantifyFirst (calendarCount players)
    (.ofQuantifierFree
      (quittingFiniteCalendarRawStrictFormulaWithTerms rawExclusionRewardTerm
        rawExclusionCalendarTerm))

/-- Weak-subset raw exclusion with the reward table left as free parameters. -/
def rawWeakSubsetExclusionParameterFormula (owners : Finset (Fin players)) :
    PolynomialFormula (rewardCount players) :=
  PolynomialFormula.universallyQuantifyFirst (calendarCount players)
    (.ofQuantifierFree
      (quittingFiniteCalendarRawWeakSubsetFormulaWithTerms rawExclusionRewardTerm
        rawExclusionCalendarTerm owners))

/-- A calendar variable when lambda precedes the reward parameter block. -/
def rawGroupCalendarTerm
    (entry : QuittingFiniteCalendarVariable (Fin players) (rawDeadline players)) :
    RingExpression ((rewardCount players + 1) + calendarCount players) :=
  .var (PolynomialFormula.leadingBlockIndex (rewardCount players + 1)
    (quittingFiniteCalendarVariableIndex entry))

/-- The leading free lambda coordinate under the universal calendar block. -/
def rawGroupLambdaTerm :
    RingExpression ((rewardCount players + 1) + calendarCount players) :=
  .var (PolynomialFormula.trailingBlockIndex (rewardCount players + 1)
    (calendarCount players) 0)

/-- A reward variable following lambda under the universal calendar block. -/
def rawGroupRewardTerm
    (terminal : {S : Finset (Fin players) // S.Nonempty}) (observer : Fin players) :
    RingExpression ((rewardCount players + 1) + calendarCount players) :=
  .var (PolynomialFormula.trailingBlockIndex (rewardCount players + 1)
    (calendarCount players)
      (Fin.succ (quittingRewardTableVariableIndex (terminal, observer))))

private def rawGroupFreeEnvironment
    (lambda : ℝ) (parameters : Fin (rewardCount players) → ℝ) :
    Fin (rewardCount players + 1) → ℝ :=
  Fin.cases lambda parameters

private def rawGroupEnvironment
    (calendar : Fin (calendarCount players) → ℝ) (lambda : ℝ)
    (parameters : Fin (rewardCount players) → ℝ) :
    Fin ((rewardCount players + 1) + calendarCount players) → ℝ :=
  PolynomialFormula.blockEnvironment calendar
    (rawGroupFreeEnvironment lambda parameters)

@[simp]
private theorem evalReal_rawGroupCalendarTerm
    (calendar : Fin (calendarCount players) → ℝ) (lambda : ℝ)
    (parameters : Fin (rewardCount players) → ℝ)
    (entry : QuittingFiniteCalendarVariable (Fin players) (rawDeadline players)) :
    (rawGroupCalendarTerm entry).evalReal
        (rawGroupEnvironment calendar lambda parameters) =
      quittingFiniteCalendarFromParameters calendar entry := by
  simp [rawGroupCalendarTerm, rawGroupEnvironment,
    quittingFiniteCalendarFromParameters]

@[simp]
private theorem evalReal_rawGroupLambdaTerm
    (calendar : Fin (calendarCount players) → ℝ) (lambda : ℝ)
    (parameters : Fin (rewardCount players) → ℝ) :
    (rawGroupLambdaTerm (players := players)).evalReal
        (rawGroupEnvironment calendar lambda parameters) = lambda := by
  simp [rawGroupLambdaTerm, rawGroupEnvironment, rawGroupFreeEnvironment]

@[simp]
private theorem evalReal_rawGroupRewardTerm
    (calendar : Fin (calendarCount players) → ℝ) (lambda : ℝ)
    (parameters : Fin (rewardCount players) → ℝ)
    (terminal : {S : Finset (Fin players) // S.Nonempty}) (observer : Fin players) :
    (rawGroupRewardTerm terminal observer).evalReal
        (rawGroupEnvironment calendar lambda parameters) =
      quittingRewardFromParameters parameters terminal observer := by
  simp [rawGroupRewardTerm, rawGroupEnvironment, rawGroupFreeEnvironment,
    quittingRewardFromParameters]

/-- The lambda range formula before lambda is existentially bound. -/
def rawGroupLambdaRangeFormula : QuantifierFreeFormula (rewardCount players + 1) :=
  .and (QuantifierFreeFormula.positive (.var 0))
    (QuantifierFreeFormula.nonpositive (.var 0 + -.const (1 / 2)))

@[simp]
theorem rawGroupLambdaRangeFormula_holdsAt_iff
    (lambda : ℝ) (parameters : Fin (rewardCount players) → ℝ) :
    (rawGroupLambdaRangeFormula (players := players)).HoldsAt
        (rawGroupFreeEnvironment lambda parameters) ↔
      0 < lambda ∧ lambda ≤ (1 : ℝ) / 2 := by
  change
    (QuantifierFreeFormula.positive (.var 0)).HoldsAt
        (rawGroupFreeEnvironment lambda parameters) ∧
      (QuantifierFreeFormula.nonpositive
        (.var 0 + -.const (1 / 2))).HoldsAt
          (rawGroupFreeEnvironment lambda parameters) ↔ _
  rw [QuantifierFreeFormula.holdsAt_positive_iff,
    QuantifierFreeFormula.holdsAt_nonpositive_iff]
  norm_num [rawGroupFreeEnvironment]

/-- Group exclusion with one lambda bound before all calendars and free rewards retained. -/
def rawGroupExclusionParameterFormula : PolynomialFormula (rewardCount players) :=
  .ex (.and
    (.ofQuantifierFree rawGroupLambdaRangeFormula)
    (PolynomialFormula.universallyQuantifyFirst (calendarCount players)
      (.ofQuantifierFree
        (quittingFiniteCalendarRawOrderedPairFormulaWithTerms rawGroupRewardTerm
          rawGroupCalendarTerm rawGroupLambdaTerm))))

private theorem rawStrictFormula_holdsAt_profile_iff
    (parameters : Fin (rewardCount players) → ℝ)
    (calendar : Fin (calendarCount players) → ℝ)
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction (rawDeadline players)))
    (hcalendar : ∀ who choice,
      quittingFiniteCalendarFromParameters calendar (who, choice) =
        profile who choice) :
    (quittingFiniteCalendarRawStrictFormulaWithTerms rawExclusionRewardTerm
      rawExclusionCalendarTerm).HoldsAt
        (PolynomialFormula.blockEnvironment calendar parameters) ↔
      ∃ observer,
        quittingFiniteCalendarRawPayoff (quittingRewardFromParameters parameters)
            (rawDeadline players) profile observer <
          quittingRewardFromParameters parameters
            (quittingSingletonTerminal observer) observer := by
  have hresult :=
    quittingFiniteCalendarRawStrictFormulaWithTerms_holdsAt_profile_iff
      rawExclusionRewardTerm rawExclusionCalendarTerm
      (PolynomialFormula.blockEnvironment calendar parameters) profile
      (fun who choice =>
        (evalReal_rawExclusionCalendarTerm calendar parameters (who, choice)).trans
          (hcalendar who choice))
  simpa only [evalReal_rawExclusionRewardTerm] using hresult

private theorem evalReal_rawExclusionSingletonSurplusTerm_profile
    (parameters : Fin (rewardCount players) → ℝ)
    (calendar : Fin (calendarCount players) → ℝ)
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction (rawDeadline players)))
    (hcalendar : ∀ who choice,
      quittingFiniteCalendarFromParameters calendar (who, choice) =
        profile who choice)
    (observer : Fin players) :
    (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
      rawExclusionRewardTerm rawExclusionCalendarTerm observer).evalReal
        (PolynomialFormula.blockEnvironment calendar parameters) =
      quittingFiniteCalendarRawPayoff (quittingRewardFromParameters parameters)
          (rawDeadline players) profile observer -
        quittingRewardFromParameters parameters
          (quittingSingletonTerminal observer) observer := by
  rw [evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms,
    evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
      rawExclusionRewardTerm rawExclusionCalendarTerm observer
      (PolynomialFormula.blockEnvironment calendar parameters) profile
      (fun who choice =>
        (evalReal_rawExclusionCalendarTerm calendar parameters (who, choice)).trans
          (hcalendar who choice))]
  simp only [evalReal_rawExclusionRewardTerm]

private theorem rawWeakFormula_holdsAt_profile_iff
    (parameters : Fin (rewardCount players) → ℝ)
    (calendar : Fin (calendarCount players) → ℝ)
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction (rawDeadline players)))
    (hcalendar : ∀ who choice,
      quittingFiniteCalendarFromParameters calendar (who, choice) =
        profile who choice)
    (owners : Finset (Fin players)) :
    (quittingFiniteCalendarRawWeakSubsetFormulaWithTerms rawExclusionRewardTerm
      rawExclusionCalendarTerm owners).HoldsAt
        (PolynomialFormula.blockEnvironment calendar parameters) ↔
      (∀ observer ∈ owners,
        0 ≤ quittingRewardFromParameters parameters
          (quittingSingletonTerminal observer) observer) ∧
      ∃ observer ∈ owners,
        quittingFiniteCalendarRawPayoff (quittingRewardFromParameters parameters)
            (rawDeadline players) profile observer ≤
          quittingRewardFromParameters parameters
            (quittingSingletonTerminal observer) observer := by
  rw [quittingFiniteCalendarRawWeakSubsetFormulaWithTerms_holdsAt_iff]
  have hsimplex :
      (quittingFiniteCalendarSimplexFormulaWithTerms rawExclusionCalendarTerm).HoldsAt
        (PolynomialFormula.blockEnvironment calendar parameters) := by
    apply (quittingFiniteCalendarSimplexFormulaWithTerms_holdsAt_iff _ _).mpr
    constructor
    · intro who choice
      rw [evalReal_rawExclusionCalendarTerm, hcalendar]
      exact (profile who).property.1 choice
    · intro who
      simp only [evalReal_rawExclusionCalendarTerm, hcalendar]
      have htotal := (profile who).property.2
      rw [Fintype.sum_option] at htotal
      exact htotal
  simp only [evalReal_rawExclusionRewardTerm, hsimplex, not_true_eq_false, false_or,
    evalReal_rawExclusionSingletonSurplusTerm_profile parameters calendar profile hcalendar,
    sub_nonpos]

@[simp]
theorem rawStrictExclusionParameterFormula_holdsAt_iff
    [Nonempty (Fin players)] (parameters : Fin (rewardCount players) → ℝ) :
    rawStrictExclusionParameterFormula.HoldsAt parameters ↔
      HasQuittingFiniteCalendarRawStrictExclusion
        (quittingRewardFromParameters parameters) := by
  rw [rawStrictExclusionParameterFormula,
    PolynomialFormula.holdsAt_universallyQuantifyFirst_iff]
  simp only [PolynomialFormula.holdsAt_ofQuantifierFree_iff]
  unfold HasQuittingFiniteCalendarRawStrictExclusion
  constructor
  · intro hformula profile
    apply (rawStrictFormula_holdsAt_profile_iff parameters
      (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) profile
      (fun who choice => by rw [quittingFiniteCalendarFromParameters_encode])).mp
    exact hformula _
  · intro hraw calendar
    by_cases hsimplex :
        (quittingFiniteCalendarSimplexFormulaWithTerms rawExclusionCalendarTerm).HoldsAt
          (PolynomialFormula.blockEnvironment calendar parameters)
    · have hconditions :=
        (quittingFiniteCalendarSimplexFormulaWithTerms_holdsAt_iff _ _).mp hsimplex
      have hspecialized :
          (quittingFiniteCalendarSimplexFormula players (rawDeadline players)).HoldsAt
            calendar := by
        apply (quittingFiniteCalendarSimplexFormula_holdsAt_iff calendar).mpr
        simpa only [evalReal_rawExclusionCalendarTerm] using hconditions
      let profile := quittingFiniteCalendarProfileOfParameters calendar hspecialized
      apply (rawStrictFormula_holdsAt_profile_iff parameters calendar profile
        (fun _ _ => rfl)).mpr
      exact hraw profile
    · apply
        (quittingFiniteCalendarRawStrictFormulaWithTerms_holdsAt_iff
          rawExclusionRewardTerm rawExclusionCalendarTerm
          (PolynomialFormula.blockEnvironment calendar parameters)).mpr
      exact Or.inl hsimplex

@[simp]
theorem rawWeakSubsetExclusionParameterFormula_holdsAt_iff
    [Nonempty (Fin players)] (parameters : Fin (rewardCount players) → ℝ)
    (owners : Finset (Fin players)) :
    (rawWeakSubsetExclusionParameterFormula owners).HoldsAt parameters ↔
      HasQuittingFiniteCalendarRawWeakSubsetExclusion
        (quittingRewardFromParameters parameters) owners := by
  rw [rawWeakSubsetExclusionParameterFormula,
    PolynomialFormula.holdsAt_universallyQuantifyFirst_iff]
  simp only [PolynomialFormula.holdsAt_ofQuantifierFree_iff]
  unfold HasQuittingFiniteCalendarRawWeakSubsetExclusion
  constructor
  · intro hformula
    have hzero := hformula fun _ => 0
    rw [quittingFiniteCalendarRawWeakSubsetFormulaWithTerms_holdsAt_iff] at hzero
    refine ⟨?_, fun profile => ?_⟩
    · simpa only [evalReal_rawExclusionRewardTerm] using hzero.1
    · have hresult := (rawWeakFormula_holdsAt_profile_iff parameters
        (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) profile
        (fun who choice => by rw [quittingFiniteCalendarFromParameters_encode])
        owners).mp
        (hformula _)
      exact hresult.2
  · rintro ⟨hsingleton, hraw⟩ calendar
    by_cases hsimplex :
        (quittingFiniteCalendarSimplexFormulaWithTerms rawExclusionCalendarTerm).HoldsAt
          (PolynomialFormula.blockEnvironment calendar parameters)
    · have hconditions :=
        (quittingFiniteCalendarSimplexFormulaWithTerms_holdsAt_iff _ _).mp hsimplex
      have hspecialized :
          (quittingFiniteCalendarSimplexFormula players (rawDeadline players)).HoldsAt
            calendar := by
        apply (quittingFiniteCalendarSimplexFormula_holdsAt_iff calendar).mpr
        simpa only [evalReal_rawExclusionCalendarTerm] using hconditions
      let profile := quittingFiniteCalendarProfileOfParameters calendar hspecialized
      apply (rawWeakFormula_holdsAt_profile_iff parameters calendar profile
        (fun _ _ => rfl) owners).mpr
      exact ⟨hsingleton, hraw profile⟩
    · apply
        (quittingFiniteCalendarRawWeakSubsetFormulaWithTerms_holdsAt_iff
          rawExclusionRewardTerm rawExclusionCalendarTerm owners
          (PolynomialFormula.blockEnvironment calendar parameters)).mpr
      refine ⟨?_, Or.inl hsimplex⟩
      simpa only [evalReal_rawExclusionRewardTerm] using hsingleton

private theorem evalReal_rawGroupSingletonSurplusTerm_profile
    (parameters : Fin (rewardCount players) → ℝ)
    (calendar : Fin (calendarCount players) → ℝ) (lambda : ℝ)
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction (rawDeadline players)))
    (hcalendar : ∀ who choice,
      quittingFiniteCalendarFromParameters calendar (who, choice) =
        profile who choice)
    (observer : Fin players) :
    (quittingFiniteCalendarSingletonSurplusExpressionWithTerms rawGroupRewardTerm
      rawGroupCalendarTerm observer).evalReal
        (rawGroupEnvironment calendar lambda parameters) =
      quittingFiniteCalendarRawPayoff (quittingRewardFromParameters parameters)
          (rawDeadline players) profile observer -
        quittingRewardFromParameters parameters
          (quittingSingletonTerminal observer) observer := by
  rw [evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms,
    evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
      rawGroupRewardTerm rawGroupCalendarTerm observer
      (rawGroupEnvironment calendar lambda parameters) profile
      (fun who choice =>
        (evalReal_rawGroupCalendarTerm calendar lambda parameters (who, choice)).trans
          (hcalendar who choice))]
  simp only [evalReal_rawGroupRewardTerm]

private theorem rawGroupFormula_holdsAt_profile_iff
    (parameters : Fin (rewardCount players) → ℝ)
    (calendar : Fin (calendarCount players) → ℝ) (lambda : ℝ)
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction (rawDeadline players)))
    (hcalendar : ∀ who choice,
      quittingFiniteCalendarFromParameters calendar (who, choice) =
        profile who choice) :
    (quittingFiniteCalendarRawOrderedPairFormulaWithTerms rawGroupRewardTerm
      rawGroupCalendarTerm rawGroupLambdaTerm).HoldsAt
        (rawGroupEnvironment calendar lambda parameters) ↔
      ∃ first second, first ≠ second ∧
        (1 - lambda) *
            (quittingFiniteCalendarRawPayoff (quittingRewardFromParameters parameters)
              (rawDeadline players) profile first -
                quittingRewardFromParameters parameters
                  (quittingSingletonTerminal first) first) +
          lambda *
            (quittingFiniteCalendarRawPayoff (quittingRewardFromParameters parameters)
              (rawDeadline players) profile second -
                quittingRewardFromParameters parameters
                  (quittingSingletonTerminal second) second) ≤ 0 := by
  rw [quittingFiniteCalendarRawOrderedPairFormulaWithTerms_holdsAt_iff]
  have hsimplex :
      (quittingFiniteCalendarSimplexFormulaWithTerms rawGroupCalendarTerm).HoldsAt
        (rawGroupEnvironment calendar lambda parameters) := by
    apply (quittingFiniteCalendarSimplexFormulaWithTerms_holdsAt_iff _ _).mpr
    constructor
    · intro who choice
      rw [evalReal_rawGroupCalendarTerm, hcalendar]
      exact (profile who).property.1 choice
    · intro who
      simp only [evalReal_rawGroupCalendarTerm, hcalendar]
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
    evalReal_rawGroupLambdaTerm,
    evalReal_rawGroupSingletonSurplusTerm_profile parameters calendar lambda profile
      hcalendar first,
    evalReal_rawGroupSingletonSurplusTerm_profile parameters calendar lambda profile
      hcalendar second]

private theorem rawGroupFormula_forall_iff
    [Nonempty (Fin players)]
    (parameters : Fin (rewardCount players) → ℝ) (lambda : ℝ) :
    (∀ calendar,
      (quittingFiniteCalendarRawOrderedPairFormulaWithTerms rawGroupRewardTerm
        rawGroupCalendarTerm rawGroupLambdaTerm).HoldsAt
          (rawGroupEnvironment calendar lambda parameters)) ↔
      HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
        (quittingRewardFromParameters parameters) lambda := by
  unfold HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
  constructor
  · intro hformula profile
    apply (rawGroupFormula_holdsAt_profile_iff parameters
      (quittingFiniteCalendarParameters fun pair => profile pair.1 pair.2) lambda
      profile (fun who choice => by
        rw [quittingFiniteCalendarFromParameters_encode])).mp
    exact hformula _
  · intro hraw calendar
    by_cases hsimplex :
        (quittingFiniteCalendarSimplexFormulaWithTerms rawGroupCalendarTerm).HoldsAt
          (rawGroupEnvironment calendar lambda parameters)
    · have hconditions :=
        (quittingFiniteCalendarSimplexFormulaWithTerms_holdsAt_iff _ _).mp hsimplex
      have hspecialized :
          (quittingFiniteCalendarSimplexFormula players (rawDeadline players)).HoldsAt
            calendar := by
        apply (quittingFiniteCalendarSimplexFormula_holdsAt_iff calendar).mpr
        simpa only [evalReal_rawGroupCalendarTerm] using hconditions
      let profile := quittingFiniteCalendarProfileOfParameters calendar hspecialized
      apply (rawGroupFormula_holdsAt_profile_iff parameters calendar lambda profile
        (fun _ _ => rfl)).mpr
      exact hraw profile
    · apply
        (quittingFiniteCalendarRawOrderedPairFormulaWithTerms_holdsAt_iff
          rawGroupRewardTerm rawGroupCalendarTerm rawGroupLambdaTerm
          (rawGroupEnvironment calendar lambda parameters)).mpr
      exact Or.inl hsimplex

@[simp]
theorem rawGroupExclusionParameterFormula_holdsAt_iff
    [Nonempty (Fin players)] (parameters : Fin (rewardCount players) → ℝ) :
    rawGroupExclusionParameterFormula.HoldsAt parameters ↔
      ∃ beta < 1, HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion
        (quittingRewardFromParameters parameters) beta := by
  rw [rawGroupExclusionParameterFormula]
  change (∃ lambda : ℝ,
    (PolynomialFormula.ofQuantifierFree
      (rawGroupLambdaRangeFormula (players := players))).HoldsAt
        (Fin.cases lambda parameters) ∧
      (PolynomialFormula.universallyQuantifyFirst (calendarCount players)
        (PolynomialFormula.ofQuantifierFree
          (quittingFiniteCalendarRawOrderedPairFormulaWithTerms rawGroupRewardTerm
            rawGroupCalendarTerm rawGroupLambdaTerm))).HoldsAt
              (Fin.cases lambda parameters)) ↔ _
  have hfree (lambda : ℝ) :
      Fin.cases lambda parameters = rawGroupFreeEnvironment lambda parameters := rfl
  simp only [PolynomialFormula.holdsAt_ofQuantifierFree_iff, hfree,
    rawGroupLambdaRangeFormula_holdsAt_iff,
    PolynomialFormula.holdsAt_universallyQuantifyFirst_iff]
  rw [exists_finiteCalendarRawNonconcentratedGroupExclusion_iff_orderedPair]
  apply exists_congr
  intro lambda
  rw [and_assoc]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  exact rawGroupFormula_forall_iff parameters lambda

end GameTheory
