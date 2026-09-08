import MathUE.Logic.SignFormulaFiniteFolds
import MathUE.RealQuantifierElimination.QuantifierFreeFormula
import UniformEquilibrium.Quitting.Paths.FiniteCalendarParameters
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPayoff
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort

/-!
# Rational-expression frontend for finite-calendar quitting payoffs

These computable constructors accept arbitrary reward and calendar terms.
Their evaluation agrees with the raw payoff map, including the Never
coordinates. They do not bind calendar variables or decide a closed sentence;
those operations belong to the caller.
-/

namespace GameTheory

open Math.PolynomialSignCell.SignFormula
open MathUE.RealQuantifierElimination
open scoped BigOperators

variable {players deadline arity : Nat}

private theorem sum_map_ofFn_eq_fintype_sum
    {count : Nat} (value : Fin count → ℝ) :
    ((List.ofFn value).sum : ℝ) = ∑ index, value index := by
  exact List.sum_ofFn

private theorem sum_map_sort_eq_finset_sum
    {alpha : Type} [LinearOrder alpha] (set : Finset alpha) (value : alpha → ℝ) :
    ((set.sort (· ≤ ·)).map value).sum = ∑ item ∈ set, value item := by
  rw [Finset.sum_eq_multiset_sum]
  change (Multiset.map value ↑(set.sort (· ≤ ·))).sum = _
  rw [Finset.sort_eq]

private theorem product_map_sort_eq_finset_product
    {alpha : Type} [LinearOrder alpha] (set : Finset alpha) (value : alpha → ℝ) :
    ((set.sort (· ≤ ·)).map value).prod = ∏ item ∈ set, value item := by
  rw [Finset.prod_eq_multiset_prod]
  change (Multiset.map value ↑(set.sort (· ≤ ·))).prod = _
  rw [Finset.sort_eq]

private def quittingTerminalOrderKey
    (terminal : {S : Finset (Fin players) // S.Nonempty}) :
    Colex (Finset (Fin players)) :=
  toColex terminal.val

private theorem quittingTerminalOrderKey_injective :
    Function.Injective (@quittingTerminalOrderKey players) := by
  intro left right hequal
  apply Subtype.ext
  exact toColex.injective hequal

private def quittingTerminalLE
    (left right : {S : Finset (Fin players) // S.Nonempty}) : Prop :=
  quittingTerminalOrderKey left ≤ quittingTerminalOrderKey right

private instance : DecidableRel (@quittingTerminalLE players) :=
  fun left right => by
    unfold quittingTerminalLE
    infer_instance

private instance : Std.Total (@quittingTerminalLE players) where
  total left right := le_total (quittingTerminalOrderKey left)
    (quittingTerminalOrderKey right)

private instance : IsTrans {S : Finset (Fin players) // S.Nonempty}
    (@quittingTerminalLE players) where
  trans _ _ _ := le_trans

private instance : Std.Antisymm (@quittingTerminalLE players) where
  antisymm _ _ hleft hright :=
    quittingTerminalOrderKey_injective (le_antisymm hleft hright)

private theorem sum_map_terminal_sort_eq_finset_sum
    (set : Finset {S : Finset (Fin players) // S.Nonempty})
    (value : {S : Finset (Fin players) // S.Nonempty} → ℝ) :
    ((set.sort quittingTerminalLE).map value).sum = ∑ item ∈ set, value item := by
  rw [Finset.sum_eq_multiset_sum]
  change (Multiset.map value ↑(set.sort quittingTerminalLE)).sum = _
  rw [Finset.sort_eq]

/-- The strict tail of one supplied finite-calendar row. -/
def quittingFiniteCalendarStrictTailExpressionWithTerms
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (who : Fin players) (time : Fin deadline) : RingExpression arity :=
  calendarTerm (who, none) +
    RingExpression.sum (List.ofFn fun later : Fin deadline =>
      if time < later then calendarTerm (who, some later) else 0)

/-- The mass of a supplied first-quitter coalition on a finite calendar. -/
def quittingFiniteCalendarCoalitionMassExpressionWithTerms
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (terminal : {S : Finset (Fin players) // S.Nonempty}) : RingExpression arity :=
  RingExpression.sum (List.ofFn fun time : Fin deadline =>
    RingExpression.product
        ((terminal.val.sort (· ≤ ·)).map fun who => calendarTerm (who, some time)) *
      RingExpression.product ((terminal.valᶜ.sort (· ≤ ·)).map fun who =>
        quittingFiniteCalendarStrictTailExpressionWithTerms calendarTerm who time))

/-- The prescribed payoff expression with arbitrary reward and calendar terms. -/
def quittingFiniteCalendarRawPayoffExpressionWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (observer : Fin players) : RingExpression arity :=
  RingExpression.sum
    (((Finset.univ : Finset {S : Finset (Fin players) // S.Nonempty}).sort
      quittingTerminalLE).map fun terminal =>
        quittingFiniteCalendarCoalitionMassExpressionWithTerms calendarTerm terminal *
          rewardTerm terminal observer)

/-- The prescribed payoff minus the observer's singleton reward. -/
def quittingFiniteCalendarSingletonSurplusExpressionWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (observer : Fin players) : RingExpression arity :=
  quittingFiniteCalendarRawPayoffExpressionWithTerms rewardTerm calendarTerm observer +
    -rewardTerm (quittingSingletonTerminal observer) observer

@[simp]
theorem evalReal_quittingFiniteCalendarStrictTailExpressionWithTerms
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (who : Fin players) (time : Fin deadline) (environment : Fin arity → ℝ) :
    (quittingFiniteCalendarStrictTailExpressionWithTerms calendarTerm who time).evalReal
        environment =
      (calendarTerm (who, none)).evalReal environment +
        ∑ later : Fin deadline, if time < later then
          (calendarTerm (who, some later)).evalReal environment else 0 := by
  rw [quittingFiniteCalendarStrictTailExpressionWithTerms,
    RingExpression.evalReal_add, RingExpression.evalReal_sum, List.map_ofFn,
    sum_map_ofFn_eq_fintype_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro later _
  by_cases hlater : time < later <;> simp [hlater]

@[simp]
theorem evalReal_quittingFiniteCalendarCoalitionMassExpressionWithTerms
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (terminal : {S : Finset (Fin players) // S.Nonempty})
    (environment : Fin arity → ℝ) :
    (quittingFiniteCalendarCoalitionMassExpressionWithTerms calendarTerm terminal).evalReal
        environment =
      ∑ time : Fin deadline,
        (∏ who ∈ terminal.val,
          (calendarTerm (who, some time)).evalReal environment) *
          ∏ who ∈ terminal.valᶜ,
            ((calendarTerm (who, none)).evalReal environment +
              ∑ later : Fin deadline, if time < later then
                (calendarTerm (who, some later)).evalReal environment else 0) := by
  rw [quittingFiniteCalendarCoalitionMassExpressionWithTerms,
    RingExpression.evalReal_sum, List.map_ofFn, sum_map_ofFn_eq_fintype_sum]
  apply Finset.sum_congr rfl
  intro time _
  change
    ((RingExpression.product
        ((terminal.val.sort (· ≤ ·)).map fun who => calendarTerm (who, some time)) *
      RingExpression.product ((terminal.valᶜ.sort (· ≤ ·)).map fun who =>
        quittingFiniteCalendarStrictTailExpressionWithTerms calendarTerm who time)).evalReal
          environment) = _
  rw [RingExpression.evalReal_mul, RingExpression.evalReal_product,
    RingExpression.evalReal_product, List.map_map, List.map_map,
    product_map_sort_eq_finset_product, product_map_sort_eq_finset_product]
  simp only [Function.comp_apply,
    evalReal_quittingFiniteCalendarStrictTailExpressionWithTerms]

@[simp]
theorem evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (observer : Fin players) (environment : Fin arity → ℝ) :
    (quittingFiniteCalendarRawPayoffExpressionWithTerms rewardTerm calendarTerm
        observer).evalReal environment =
      ∑ terminal,
        (∑ time : Fin deadline,
          (∏ who ∈ terminal.val,
            (calendarTerm (who, some time)).evalReal environment) *
            ∏ who ∈ terminal.valᶜ,
              ((calendarTerm (who, none)).evalReal environment +
                ∑ later : Fin deadline, if time < later then
                  (calendarTerm (who, some later)).evalReal environment else 0)) *
          (rewardTerm terminal observer).evalReal environment := by
  rw [quittingFiniteCalendarRawPayoffExpressionWithTerms,
    RingExpression.evalReal_sum, List.map_map, sum_map_terminal_sort_eq_finset_sum]
  apply Finset.sum_congr rfl
  intro terminal _
  simp

theorem evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (observer : Fin players) (environment : Fin arity → ℝ)
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (hcalendar : ∀ who choice,
      (calendarTerm (who, choice)).evalReal environment = profile who choice) :
    (quittingFiniteCalendarRawPayoffExpressionWithTerms rewardTerm calendarTerm
        observer).evalReal environment =
      quittingFiniteCalendarRawPayoff
        (fun terminal who => (rewardTerm terminal who).evalReal environment)
        deadline profile observer := by
  rw [evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms]
  unfold quittingFiniteCalendarRawPayoff quittingFiniteCalendarCoalitionMass
    quittingFiniteCalendarStrictTail
  simp only [hcalendar]

@[simp]
theorem evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (observer : Fin players) (environment : Fin arity → ℝ) :
    (quittingFiniteCalendarSingletonSurplusExpressionWithTerms rewardTerm calendarTerm
        observer).evalReal environment =
      (quittingFiniteCalendarRawPayoffExpressionWithTerms rewardTerm calendarTerm
        observer).evalReal environment -
          (rewardTerm (quittingSingletonTerminal observer) observer).evalReal
            environment := by
  simp [quittingFiniteCalendarSingletonSurplusExpressionWithTerms, sub_eq_add_neg]

/-- The supplied calendar coordinates are nonnegative and every player row sums to one. -/
def quittingFiniteCalendarSimplexFormulaWithTerms
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity) : QuantifierFreeFormula arity :=
  .and
    (conjunction (List.ofFn fun who : Fin players =>
      conjunction
        (QuantifierFreeFormula.nonnegative (calendarTerm (who, none)) ::
          List.ofFn fun time : Fin deadline =>
            QuantifierFreeFormula.nonnegative (calendarTerm (who, some time)))))
    (conjunction (List.ofFn fun who : Fin players =>
      .atom
        (calendarTerm (who, none) +
          RingExpression.sum (List.ofFn fun time : Fin deadline =>
            calendarTerm (who, some time)) + -1) .zero))

@[simp]
theorem quittingFiniteCalendarSimplexFormulaWithTerms_holdsAt_iff
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity) (environment : Fin arity → ℝ) :
    (quittingFiniteCalendarSimplexFormulaWithTerms calendarTerm).HoldsAt environment ↔
      (∀ who choice, 0 ≤ (calendarTerm (who, choice)).evalReal environment) ∧
        ∀ who, (calendarTerm (who, none)).evalReal environment +
          ∑ time : Fin deadline,
            (calendarTerm (who, some time)).evalReal environment = 1 := by
  dsimp only [quittingFiniteCalendarSimplexFormulaWithTerms,
    QuantifierFreeFormula.HoldsAt, Holds]
  constructor
  · rintro ⟨hnonnegative, hsums⟩
    rw [holds_conjunction_iff] at hnonnegative hsums
    constructor
    · intro who choice
      have hrow := hnonnegative _ (List.mem_ofFn.mpr ⟨who, rfl⟩)
      rw [holds_conjunction_iff] at hrow
      cases choice with
      | none =>
          exact (QuantifierFreeFormula.holdsAt_nonnegative_iff _ environment).mp
            (hrow _ (by simp))
      | some time =>
          exact (QuantifierFreeFormula.holdsAt_nonnegative_iff _ environment).mp
            (hrow _ (by simp [List.mem_ofFn]))
    · intro who
      have hsum := hsums _ (List.mem_ofFn.mpr ⟨who, rfl⟩)
      simp only [Holds, realSignAssignment, RingExpression.evalReal_add,
        RingExpression.evalReal_neg, RingExpression.evalReal_one,
        RingExpression.evalReal_sum, List.map_ofFn, List.sum_ofFn,
        Function.comp_apply, SignType.zero_eq_zero, sign_eq_zero_iff] at hsum
      linarith
  · rintro ⟨hnonnegative, hsums⟩
    constructor
    · rw [holds_conjunction_iff]
      intro row hrow
      obtain ⟨who, rfl⟩ := List.mem_ofFn.mp hrow
      rw [holds_conjunction_iff]
      intro formula hformula
      rw [List.mem_cons, List.mem_ofFn] at hformula
      rcases hformula with rfl | ⟨time, rfl⟩
      · exact (QuantifierFreeFormula.holdsAt_nonnegative_iff _ environment).mpr
          (hnonnegative who none)
      · exact (QuantifierFreeFormula.holdsAt_nonnegative_iff _ environment).mpr
          (hnonnegative who (some time))
    · rw [holds_conjunction_iff]
      intro formula hformula
      obtain ⟨who, rfl⟩ := List.mem_ofFn.mp hformula
      simp only [Holds, realSignAssignment, RingExpression.evalReal_add,
        RingExpression.evalReal_neg, RingExpression.evalReal_one,
        RingExpression.evalReal_sum, List.map_ofFn, List.sum_ofFn,
        Function.comp_apply, SignType.zero_eq_zero, sign_eq_zero_iff]
      linarith [hsums who]

/-- Every admissible calendar has a strictly negative singleton surplus. -/
def quittingFiniteCalendarRawStrictFormulaWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity) : QuantifierFreeFormula arity :=
  .or (.not (quittingFiniteCalendarSimplexFormulaWithTerms calendarTerm))
    (disjunction (List.ofFn fun observer : Fin players =>
      .atom (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
        rewardTerm calendarTerm observer) .neg))

@[simp]
theorem quittingFiniteCalendarRawStrictFormulaWithTerms_holdsAt_iff
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (environment : Fin arity → ℝ) :
    (quittingFiniteCalendarRawStrictFormulaWithTerms rewardTerm calendarTerm).HoldsAt
        environment ↔
      (¬(quittingFiniteCalendarSimplexFormulaWithTerms calendarTerm).HoldsAt
          environment) ∨
        ∃ observer,
          (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
            rewardTerm calendarTerm observer).evalReal environment < 0 := by
  change
    (¬(quittingFiniteCalendarSimplexFormulaWithTerms calendarTerm).HoldsAt
        environment) ∨
      (disjunction (List.ofFn fun observer : Fin players =>
        .atom (quittingFiniteCalendarSingletonSurplusExpressionWithTerms
          rewardTerm calendarTerm observer) .neg)).Holds
          (realSignAssignment environment) ↔ _
  rw [holds_disjunction_iff]
  constructor
  · rintro (hnot | ⟨formula, hformula, hholds⟩)
    · exact Or.inl hnot
    · right
      obtain ⟨observer, rfl⟩ := List.mem_ofFn.mp hformula
      exact ⟨observer, sign_eq_neg_one_iff.mp hholds⟩
  · rintro (hnot | ⟨observer, hobserver⟩)
    · exact Or.inl hnot
    · right
      exact ⟨_, List.mem_ofFn.mpr ⟨observer, rfl⟩,
        sign_eq_neg_one_iff.mpr hobserver⟩

theorem quittingFiniteCalendarRawStrictFormulaWithTerms_holdsAt_profile_iff
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (calendarTerm : QuittingFiniteCalendarVariable (Fin players) deadline →
      RingExpression arity)
    (environment : Fin arity → ℝ)
    (profile : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (hcalendar : ∀ who choice,
      (calendarTerm (who, choice)).evalReal environment = profile who choice) :
    (quittingFiniteCalendarRawStrictFormulaWithTerms rewardTerm calendarTerm).HoldsAt
        environment ↔
      ∃ observer,
        quittingFiniteCalendarRawPayoff
            (fun terminal who => (rewardTerm terminal who).evalReal environment)
            deadline profile observer <
          (rewardTerm (quittingSingletonTerminal observer) observer).evalReal
            environment := by
  have hsimplex :
      (∀ who choice, 0 ≤ (calendarTerm (who, choice)).evalReal environment) ∧
        ∀ who, (calendarTerm (who, none)).evalReal environment +
          ∑ time : Fin deadline,
            (calendarTerm (who, some time)).evalReal environment = 1 := by
    constructor
    · intro who choice
      rw [hcalendar]
      exact (profile who).property.1 choice
    · intro who
      have htotal := (profile who).property.2
      rw [Fintype.sum_option] at htotal
      calc
        _ = profile who none + ∑ time : Fin deadline, profile who (some time) := by
          congr 1
          · exact hcalendar who none
          · apply Finset.sum_congr rfl
            intro time _
            exact hcalendar who (some time)
        _ = 1 := htotal
  have hsimplexHolds :=
    (quittingFiniteCalendarSimplexFormulaWithTerms_holdsAt_iff
      calendarTerm environment).mpr hsimplex
  rw [quittingFiniteCalendarRawStrictFormulaWithTerms_holdsAt_iff]
  simp only [hsimplexHolds, not_true_eq_false, false_or]
  apply exists_congr
  intro observer
  have hpayoff :=
    evalReal_quittingFiniteCalendarRawPayoffExpressionWithTerms_eq_rawPayoff
      rewardTerm calendarTerm observer environment profile hcalendar
  rw [evalReal_quittingFiniteCalendarSingletonSurplusExpressionWithTerms, hpayoff]
  exact sub_neg

end GameTheory
