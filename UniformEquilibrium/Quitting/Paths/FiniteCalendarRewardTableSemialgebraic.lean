import MathUE.Semialgebraic.FiniteQuantification
import UniformEquilibrium.Quitting.Paths.FiniteCalendarJointPolynomial
import UniformEquilibrium.Quitting.Paths.FiniteCalendarPayoffSemialgebraic
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates

/-! Semialgebraic acceptance sets in the raw reward-table coordinates. -/

noncomputable section

namespace GameTheory

open Math.PolynomialSignCell

variable {n : ℕ}


/-- The joint surplus polynomial in a reward-first finite coordinate layout. -/
def quittingFiniteCalendarCoordinateSingletonSurplusPolynomial
    (deadline : ℕ) (observer : Fin n) :
    MvPolynomial
      (Fin (Fintype.card (QuittingRewardTableVariable (Fin n)) +
        Fintype.card (QuittingFiniteCalendarVariable (Fin n) deadline))) ℝ :=
  MvPolynomial.rename (quittingFiniteCalendarJointCoordinates deadline)
    (quittingFiniteCalendarJointSingletonSurplusPolynomial deadline observer)

theorem quittingFiniteCalendarJointValues_coordinates
    (table : Fin (Fintype.card (QuittingRewardTableVariable (Fin n))) → ℝ)
    (deadline : ℕ)
    (calendar : Fin (Fintype.card (QuittingFiniteCalendarVariable (Fin n) deadline)) → ℝ) :
    Fin.append table calendar ∘ quittingFiniteCalendarJointCoordinates deadline =
      quittingFiniteCalendarJointValues (quittingRewardTableFromCoordinates table)
        (calendar ∘ Fintype.equivFin (QuittingFiniteCalendarVariable (Fin n) deadline)) := by
  funext entry
  cases entry with
  | inl entry =>
      simp only [Function.comp_apply, quittingFiniteCalendarJointCoordinates_reward,
        Fin.append_left, quittingFiniteCalendarJointValues, Sum.elim_inl,
        quittingRewardTableFromCoordinates]
  | inr entry =>
      simp only [Function.comp_apply, quittingFiniteCalendarJointCoordinates_calendar,
        Fin.append_right, quittingFiniteCalendarJointValues, Sum.elim_inr]

theorem eval_quittingFiniteCalendarCoordinateSingletonSurplusPolynomial
    (table : Fin (Fintype.card (QuittingRewardTableVariable (Fin n))) → ℝ)
    (deadline : ℕ)
    (calendar : Fin (Fintype.card (QuittingFiniteCalendarVariable (Fin n) deadline)) → ℝ)
    (observer : Fin n) :
    MvPolynomial.eval (Fin.append table calendar)
      (quittingFiniteCalendarCoordinateSingletonSurplusPolynomial deadline observer) =
        MvPolynomial.eval
          (calendar ∘ Fintype.equivFin (QuittingFiniteCalendarVariable (Fin n) deadline))
          (quittingFiniteCalendarRawPayoffPolynomial
            (quittingRewardTableFromCoordinates table) deadline observer) -
              quittingRewardTableFromCoordinates table
                (quittingSingletonTerminal observer) observer := by
  rw [quittingFiniteCalendarCoordinateSingletonSurplusPolynomial, MvPolynomial.eval_rename,
    quittingFiniteCalendarJointValues_coordinates,
    eval_quittingFiniteCalendarJointSingletonSurplusPolynomial]
  rfl

theorem forall_quittingFiniteCalendarCoordinates_iff
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n)) (deadline : ℕ)
    (predicate : Payoff (Fin n) → Prop) :
    (∀ calendar,
      calendar ∈ quittingFiniteCalendarCoordinateSimplex
        (Fintype.equivFin (QuittingFiniteCalendarVariable (Fin n) deadline)) →
      predicate (fun observer => MvPolynomial.eval
        (calendar ∘ Fintype.equivFin (QuittingFiniteCalendarVariable (Fin n) deadline))
        (quittingFiniteCalendarRawPayoffPolynomial reward deadline observer))) ↔
      ∀ profile : MixedSimplex (Fin n)
        (fun _ => QuittingFiniteDeadlineTimingAction deadline),
        predicate (quittingFiniteCalendarRawPayoff reward deadline profile) := by
  let coordinates := Fintype.equivFin (QuittingFiniteCalendarVariable (Fin n) deadline)
  constructor
  · intro h profile
    have hp := h (quittingFiniteCalendarCoordinates coordinates profile)
      (quittingFiniteCalendarCoordinates_mem_simplex coordinates profile)
    have heval := evaluate_quittingFiniteCalendarCoordinates reward coordinates profile
    unfold MathUE.evaluatePolynomialMap quittingFiniteCalendarCoordinatePayoffPolynomials at heval
    simp only [MvPolynomial.eval_rename] at heval
    rwa [heval] at hp
  · intro h calendar hcalendar
    have hp := h (quittingFiniteCalendarSimplexFromCoordinates coordinates calendar hcalendar)
    have heval := evaluate_quittingFiniteCalendarCoordinatePayoffPolynomials
      reward coordinates calendar hcalendar
    unfold MathUE.evaluatePolynomialMap quittingFiniteCalendarCoordinatePayoffPolynomials at heval
    simp only [MvPolynomial.eval_rename] at heval
    rwa [← heval] at hp

/-- Any fixed Boolean test of the actual singleton-surplus signs, required on
every calendar profile, defines a semialgebraic set of raw reward tables. -/
theorem isSemialgebraic_forall_quittingFiniteCalendarSurplusSigns
    (deadline : ℕ) (formula : SignFormula (Fin n)) :
    MathUE.IsSemialgebraic {table |
      ∀ profile : MixedSimplex (Fin n)
        (fun _ => QuittingFiniteDeadlineTimingAction deadline),
        formula.Holds (fun observer => SignType.sign
          (quittingFiniteCalendarRawPayoff (quittingRewardTableFromCoordinates table)
            deadline profile observer - quittingRewardTableFromCoordinates table
              (quittingSingletonTerminal observer) observer))} := by
  let coordinates := Fintype.equivFin (QuittingFiniteCalendarVariable (Fin n) deadline)
  let jointFormula := formula.mapAtoms
    (quittingFiniteCalendarCoordinateSingletonSurplusPolynomial deadline)
  have hformula : MathUE.IsSemialgebraic {point | jointFormula.Holds
      (fun polynomial => SignType.sign (MvPolynomial.eval point polynomial))} :=
    ⟨jointFormula, fun _ => Iff.rfl⟩
  have hadmissible :=
    (isSemialgebraic_quittingFiniteCalendarCoordinateSimplex coordinates).preimage_coordinates
      (Fin.natAdd (Fintype.card (QuittingRewardTableVariable (Fin n))))
  have hresult := (hadmissible.compl.union hformula).forall_last_coordinates
  convert hresult using 1
  ext table
  simp only [Set.mem_setOf_eq]
  rw [← forall_quittingFiniteCalendarCoordinates_iff
    (quittingRewardTableFromCoordinates table) deadline
      (fun value => formula.Holds (fun observer => SignType.sign
        (value observer - quittingRewardTableFromCoordinates table
          (quittingSingletonTerminal observer) observer)))]
  apply forall_congr'
  intro calendar
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff,
    jointFormula, SignFormula.holds_mapAtoms, Function.comp_def,
    eval_quittingFiniteCalendarCoordinateSingletonSurplusPolynomial,
    Fin.append_right]
  exact imp_iff_not_or

/-- Strict exclusion: every calendar payoff has a strictly negative singleton surplus. -/
theorem isSemialgebraic_quittingRewardTables_rawStrictExclusion [Nonempty (Fin n)] :
    MathUE.IsSemialgebraic {table |
      HasQuittingFiniteCalendarRawStrictExclusion
        (quittingRewardTableFromCoordinates (n := n) table)} := by
  have hresult := isSemialgebraic_forall_quittingFiniteCalendarSurplusSigns
    (Fintype.card (Fin n) * (Fintype.card (Fin n) + 1))
    (SignFormula.disjunction (List.ofFn (fun observer : Fin n => .atom observer (-1))))
  simpa only [HasQuittingFiniteCalendarRawStrictExclusion,
    SignFormula.holds_disjunction_iff, List.mem_ofFn, exists_exists_eq_and,
    SignFormula.Holds, sign_eq_neg_one_iff, sub_neg] using hresult

/-- Weak subset exclusion includes singleton nonnegativity and weak payoff exclusion. -/
theorem isSemialgebraic_quittingRewardTables_rawWeakSubsetExclusion
    [Nonempty (Fin n)] (owners : Finset (Fin n)) :
    MathUE.IsSemialgebraic {table |
      HasQuittingFiniteCalendarRawWeakSubsetExclusion
        (quittingRewardTableFromCoordinates table) owners} := by
  have hsingleton := MathUE.IsSemialgebraic.forall_finset owners
    (fun observer table => 0 ≤ quittingRewardTableFromCoordinates table
      (quittingSingletonTerminal observer) observer) (fun observer _ => by
        simpa only [MvPolynomial.eval_X, quittingRewardTableFromCoordinates] using
          MathUE.IsSemialgebraic.polynomial_nonneg (MvPolynomial.X
          (Fintype.equivFin (QuittingRewardTableVariable (Fin n))
            (quittingSingletonTerminal observer, observer))))
  have hraw := isSemialgebraic_forall_quittingFiniteCalendarSurplusSigns
    (Fintype.card (Fin n) * (Fintype.card (Fin n) + 1))
    (SignFormula.disjunction (owners.toList.map (fun observer => .not (.atom observer 1))))
  have hexclusion : MathUE.IsSemialgebraic {table |
      ∀ profile : MixedSimplex (Fin n) (fun _ => QuittingFiniteDeadlineTimingAction
        (Fintype.card (Fin n) * (Fintype.card (Fin n) + 1))),
        ∃ observer ∈ owners,
          quittingFiniteCalendarRawPayoff (quittingRewardTableFromCoordinates table)
            _ profile observer ≤ quittingRewardTableFromCoordinates table
              (quittingSingletonTerminal observer) observer} := by
    simpa only [SignFormula.holds_disjunction_iff, List.mem_map, Finset.mem_toList,
      exists_exists_and_eq_and, SignFormula.Holds, sign_eq_one_iff, not_lt,
      sub_nonpos] using hraw
  exact hsingleton.inter hexclusion

end GameTheory
