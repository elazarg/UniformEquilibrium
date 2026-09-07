import Mathlib.Algebra.MvPolynomial.Degrees
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPayoff

/-! # Polynomial presentation of finite-calendar terminal masses -/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev QuittingFiniteCalendarVariable (ι : Type) (deadline : ℕ) :=
  ι × Option (Fin deadline)

def quittingFiniteCalendarStrictTailPolynomial (deadline : ℕ)
    (who : ι) (time : Fin deadline) :
    MvPolynomial (QuittingFiniteCalendarVariable ι deadline) ℝ :=
  MvPolynomial.X (who, none) +
    ∑ later : Fin deadline, if time < later then
      MvPolynomial.X (who, some later) else 0

def quittingFiniteCalendarCoalitionMassPolynomial (deadline : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    MvPolynomial (QuittingFiniteCalendarVariable ι deadline) ℝ :=
  ∑ time : Fin deadline,
    (∏ who ∈ terminal.val, MvPolynomial.X (who, some time)) *
      ∏ who ∈ terminal.valᶜ,
        quittingFiniteCalendarStrictTailPolynomial deadline who time

def quittingFiniteCalendarRawPayoffPolynomial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (observer : ι) :
    MvPolynomial (QuittingFiniteCalendarVariable ι deadline) ℝ :=
  ∑ terminal, MvPolynomial.C (reward terminal observer) *
    quittingFiniteCalendarCoalitionMassPolynomial deadline terminal

omit [Fintype ι] [DecidableEq ι] in
theorem eval_quittingFiniteCalendarStrictTailPolynomial (deadline : ℕ)
    (who : ι) (time : Fin deadline)
    (values : QuittingFiniteCalendarVariable ι deadline → ℝ) :
    MvPolynomial.eval values
        (quittingFiniteCalendarStrictTailPolynomial deadline who time) =
      values (who, none) + ∑ later : Fin deadline,
        if time < later then values (who, some later) else 0 := by
  simp only [quittingFiniteCalendarStrictTailPolynomial,
    map_add, MvPolynomial.eval_X, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro later _
  by_cases hlater : time < later <;> simp [hlater]

theorem eval_quittingFiniteCalendarCoalitionMassPolynomial (deadline : ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (values : QuittingFiniteCalendarVariable ι deadline → ℝ) :
    MvPolynomial.eval values
        (quittingFiniteCalendarCoalitionMassPolynomial deadline terminal) =
      ∑ time : Fin deadline,
        (∏ who ∈ terminal.val, values (who, some time)) *
          ∏ who ∈ terminal.valᶜ,
            (values (who, none) + ∑ later : Fin deadline,
              if time < later then values (who, some later) else 0) := by
  simp [quittingFiniteCalendarCoalitionMassPolynomial,
    eval_quittingFiniteCalendarStrictTailPolynomial]

theorem eval_quittingFiniteCalendarRawPayoffPolynomial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (observer : ι)
    (x : MixedSimplex ι
      (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    MvPolynomial.eval (fun pair => x pair.1 pair.2)
        (quittingFiniteCalendarRawPayoffPolynomial reward deadline observer) =
      quittingFiniteCalendarRawPayoff reward deadline x observer := by
  simp [quittingFiniteCalendarRawPayoffPolynomial,
    quittingFiniteCalendarRawPayoff,
    quittingFiniteCalendarCoalitionMass,
    eval_quittingFiniteCalendarCoalitionMassPolynomial]
  apply Finset.sum_congr rfl
  intro terminal _
  simp only [quittingFiniteCalendarStrictTail]
  ring_nf

omit [Fintype ι] [DecidableEq ι] in
theorem totalDegree_quittingFiniteCalendarStrictTailPolynomial_le
    (deadline : ℕ) (who : ι) (time : Fin deadline) :
    (quittingFiniteCalendarStrictTailPolynomial deadline who time).totalDegree ≤ 1 := by
  unfold quittingFiniteCalendarStrictTailPolynomial
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_X]
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    apply Finset.sup_le
    intro later _
    by_cases hlater : time < later
    · simp [hlater, MvPolynomial.totalDegree_X]
    · simp [hlater]

omit [Fintype ι] [DecidableEq ι] in
theorem totalDegree_finiteCalendar_quitterProduct_le
    (deadline : ℕ) (coalition : Finset ι) (time : Fin deadline) :
    (∏ who ∈ coalition,
      (MvPolynomial.X (who, some time) :
        MvPolynomial (QuittingFiniteCalendarVariable ι deadline) ℝ)).totalDegree ≤
      coalition.card := by
  calc
    _ ≤ ∑ who ∈ coalition,
        (MvPolynomial.X (who, some time) :
          MvPolynomial (QuittingFiniteCalendarVariable ι deadline) ℝ).totalDegree :=
      MvPolynomial.totalDegree_finsetProd coalition _
    _ = coalition.card := by simp [MvPolynomial.totalDegree_X]

omit [Fintype ι] [DecidableEq ι] in
theorem totalDegree_finiteCalendar_tailProduct_le
    (deadline : ℕ) (coalition : Finset ι) (time : Fin deadline) :
    (∏ who ∈ coalition,
      quittingFiniteCalendarStrictTailPolynomial deadline who time).totalDegree ≤
      coalition.card := by
  calc
    _ ≤ ∑ who ∈ coalition,
        (quittingFiniteCalendarStrictTailPolynomial deadline who time).totalDegree :=
      MvPolynomial.totalDegree_finsetProd coalition _
    _ ≤ ∑ _who ∈ coalition, 1 := by
      apply Finset.sum_le_sum
      intro who _
      exact totalDegree_quittingFiniteCalendarStrictTailPolynomial_le
        deadline who time
    _ = coalition.card := by simp

theorem totalDegree_quittingFiniteCalendarCoalitionMassPolynomial_le
    (deadline : ℕ) (terminal : {S : Finset ι // S.Nonempty}) :
    (quittingFiniteCalendarCoalitionMassPolynomial deadline terminal).totalDegree ≤
      Fintype.card ι := by
  unfold quittingFiniteCalendarCoalitionMassPolynomial
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  apply Finset.sup_le
  intro time _
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hquit := totalDegree_finiteCalendar_quitterProduct_le
    deadline terminal.val time
  have htail := totalDegree_finiteCalendar_tailProduct_le
    deadline terminal.valᶜ time
  rw [← Finset.card_add_card_compl terminal.val]
  exact Nat.add_le_add hquit htail

theorem totalDegree_quittingFiniteCalendarRawPayoffPolynomial_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (observer : ι) :
    (quittingFiniteCalendarRawPayoffPolynomial reward deadline observer).totalDegree ≤
      Fintype.card ι := by
  unfold quittingFiniteCalendarRawPayoffPolynomial
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  apply Finset.sup_le
  intro terminal _
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact totalDegree_quittingFiniteCalendarCoalitionMassPolynomial_le
    deadline terminal

end GameTheory
