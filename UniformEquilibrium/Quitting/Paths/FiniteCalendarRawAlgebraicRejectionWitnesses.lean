import MathUE.RealQuantifierElimination.AlgebraicWitnesses
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawRejectionWitnesses
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawStrictDecision
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawWeakSubsetDecision

/-! # Algebraic calendar witnesses for rejected rational raw tests -/

noncomputable section

namespace GameTheory

open MathUE.RealQuantifierElimination

variable {players : Nat}

private theorem exists_algebraic_rejection_of_not_universallyClose
    (formula : QuantifierFreeFormula n)
    (hnot : ¬(PolynomialFormula.ofQuantifierFree formula).universallyClose.HoldsAt
      Fin.elim0) :
    ∃ environment : Fin n → ℝ,
      (∀ index, IsAlgebraic ℚ (environment index)) ∧
        ¬formula.HoldsAt environment := by
  have hnotAll : ¬∀ environment : Fin n → ℝ, formula.HoldsAt environment := by
    intro hall
    apply hnot
    apply (PolynomialFormula.holdsAt_universallyClose_iff _).mpr
    simpa only [PolynomialFormula.holdsAt_ofQuantifierFree_iff] using hall
  push Not at hnotAll
  let negFormula : QuantifierFreeFormula n :=
    Math.PolynomialSignCell.SignFormula.not formula
  have hexists : ∃ environment : Fin n → ℝ,
      negFormula.HoldsAt environment := hnotAll
  obtain ⟨environment, halgebraic, hformula⟩ :=
    negFormula.exists_isAlgebraic_environment_of_exists_holdsAt hexists
  exact ⟨environment, halgebraic, hformula⟩

/-- A rational strict test is rejected exactly when a genuine finite-calendar
profile with algebraic probabilities has nonnegative surplus everywhere. -/
theorem not_hasQuittingFiniteCalendarRawStrictExclusion_iff_exists_algebraic
    [Nonempty (Fin players)] (reward : RationalQuittingReward players) :
    ¬HasQuittingFiniteCalendarRawStrictExclusion
        (rationalQuittingRewardToReal reward) ↔
      ∃ profile : MixedSimplex (Fin players)
          (fun _ => QuittingFiniteDeadlineTimingAction
            (quittingRawExclusionDeadline players)),
        (∀ who choice, IsAlgebraic ℚ (profile who choice)) ∧
          ∀ who,
            rationalQuittingRewardToReal reward
                (quittingSingletonTerminal who) who ≤
              quittingFiniteCalendarRawPayoff
                (rationalQuittingRewardToReal reward)
                (quittingRawExclusionDeadline players) profile who := by
  constructor
  · intro hnot
    have hnotSentence :
        ¬(rationalQuittingFiniteCalendarRawStrictSentence reward).HoldsAt
          Fin.elim0 := by
      intro hsentence
      exact hnot
        ((rationalQuittingFiniteCalendarRawStrictSentence_holdsAt_iff reward).mp
          hsentence)
    rw [rationalQuittingFiniteCalendarRawStrictSentence] at hnotSentence
    obtain ⟨environment, halgebraic, hformula⟩ :=
      exists_algebraic_rejection_of_not_universallyClose
        (rationalQuittingFiniteCalendarRawStrictFormula reward) hnotSentence
    rw [rationalQuittingFiniteCalendarRawStrictFormula,
      quittingFiniteCalendarRawStrictFormulaWithTerms_holdsAt_iff] at hformula
    push Not at hformula
    have hsimplex :
        (quittingFiniteCalendarSimplexFormula players
          (quittingRawExclusionDeadline players)).HoldsAt environment := by
      simpa [quittingFiniteCalendarSimplexFormula] using hformula.1
    let profile := quittingFiniteCalendarProfileOfParameters environment hsimplex
    refine ⟨profile, ?_, ?_⟩
    · intro who choice
      change IsAlgebraic ℚ
        (quittingFiniteCalendarFromParameters environment (who, choice))
      exact halgebraic (quittingFiniteCalendarVariableIndex (who, choice))
    · intro who
      have hsurplus := hformula.2 who
      rw [evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms,
        evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
          (fun terminal observer => RingExpression.const (reward terminal observer))
          quittingFiniteCalendarVariableTerm who environment profile
          (fun _ _ => rfl)] at hsurplus
      simp only [RingExpression.evalReal_const] at hsurplus
      change (reward (quittingSingletonTerminal who) who : ℝ) ≤
        quittingFiniteCalendarRawPayoff
          (fun terminal observer => (reward terminal observer : ℝ))
          (quittingRawExclusionDeadline players) profile who
      rw [← sub_nonneg]
      exact hsurplus
  · rintro ⟨profile, _, hprofile⟩
    apply
      (not_hasQuittingFiniteCalendarRawStrictExclusion_iff_exists_nonnegative
        (rationalQuittingRewardToReal reward)).mpr
    exact ⟨profile, hprofile⟩

/-- Weak-subset rejection either fails its singleton-sign premise or has a
genuine algebraic-coordinate calendar profile with every owner surplus
strictly positive. -/
theorem not_hasQuittingFiniteCalendarRawWeakSubsetExclusion_iff_exists_algebraic
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    (owners : Finset (Fin players)) :
    ¬HasQuittingFiniteCalendarRawWeakSubsetExclusion
        (rationalQuittingRewardToReal reward) owners ↔
      (∃ who ∈ owners,
        rationalQuittingRewardToReal reward
          (quittingSingletonTerminal who) who < 0) ∨
      ∃ profile : MixedSimplex (Fin players)
          (fun _ => QuittingFiniteDeadlineTimingAction
            (quittingRawExclusionDeadline players)),
        (∀ who choice, IsAlgebraic ℚ (profile who choice)) ∧
          ∀ who ∈ owners,
            rationalQuittingRewardToReal reward
                (quittingSingletonTerminal who) who <
              quittingFiniteCalendarRawPayoff
                (rationalQuittingRewardToReal reward)
                (quittingRawExclusionDeadline players) profile who := by
  constructor
  · intro hnot
    by_cases hsigns : ∀ who ∈ owners,
        0 ≤ rationalQuittingRewardToReal reward
          (quittingSingletonTerminal who) who
    · right
      have hnotSentence :
          ¬(rationalQuittingFiniteCalendarRawWeakSubsetSentence reward owners).HoldsAt
            Fin.elim0 := by
        intro hsentence
        exact hnot
          ((rationalQuittingFiniteCalendarRawWeakSubsetSentence_holdsAt_iff
            reward owners).mp hsentence)
      rw [rationalQuittingFiniteCalendarRawWeakSubsetSentence] at hnotSentence
      obtain ⟨environment, halgebraic, hformula⟩ :=
        exists_algebraic_rejection_of_not_universallyClose
          (rationalQuittingFiniteCalendarRawWeakSubsetFormula reward owners)
          hnotSentence
      rw [rationalQuittingFiniteCalendarRawWeakSubsetFormula,
        quittingFiniteCalendarRawWeakSubsetFormulaWithTerms_holdsAt_iff]
        at hformula
      have hformulaSigns : ∀ who ∈ owners,
          0 ≤ (RingExpression.const
            (reward (quittingSingletonTerminal who) who)).evalReal environment := by
        simpa only [RingExpression.evalReal_const, rationalQuittingRewardToReal]
          using hsigns
      have htail : ¬
          (¬(quittingFiniteCalendarSimplexFormulaWithTerms
              (quittingFiniteCalendarVariableTerm
                (players := players)
                (deadline := quittingRawExclusionDeadline players))).HoldsAt
              environment ∨
            ∃ who ∈ owners,
              (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
                (fun terminal observer =>
                  RingExpression.const (reward terminal observer))
                quittingFiniteCalendarVariableTerm who).evalReal environment ≤ 0) := by
        exact fun htail => hformula ⟨hformulaSigns, htail⟩
      push Not at htail
      have hsimplex :
          (quittingFiniteCalendarSimplexFormula players
            (quittingRawExclusionDeadline players)).HoldsAt environment := by
        simpa [quittingFiniteCalendarSimplexFormula] using htail.1
      let profile := quittingFiniteCalendarProfileOfParameters environment hsimplex
      refine ⟨profile, ?_, ?_⟩
      · intro who choice
        change IsAlgebraic ℚ
          (quittingFiniteCalendarFromParameters environment (who, choice))
        exact halgebraic (quittingFiniteCalendarVariableIndex (who, choice))
      · intro who hwho
        have hsurplus := htail.2 who hwho
        rw [evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms,
          evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
            (fun terminal observer => RingExpression.const (reward terminal observer))
            quittingFiniteCalendarVariableTerm who environment profile
            (fun _ _ => rfl)] at hsurplus
        simp only [RingExpression.evalReal_const] at hsurplus
        change (reward (quittingSingletonTerminal who) who : ℝ) <
          quittingFiniteCalendarRawPayoff
            (fun terminal observer => (reward terminal observer : ℝ))
            (quittingRawExclusionDeadline players) profile who
        rw [← sub_pos]
        exact hsurplus
    · left
      push Not at hsigns
      exact hsigns
  · rintro (hsigns | ⟨profile, _, hprofile⟩)
    · exact
        (not_hasQuittingFiniteCalendarRawWeakSubsetExclusion_iff
          (rationalQuittingRewardToReal reward) owners).mpr (Or.inl hsigns)
    · exact
        (not_hasQuittingFiniteCalendarRawWeakSubsetExclusion_iff
          (rationalQuittingRewardToReal reward) owners).mpr
          (Or.inr ⟨profile, hprofile⟩)

end GameTheory
