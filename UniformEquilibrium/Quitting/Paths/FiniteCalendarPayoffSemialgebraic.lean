import MathUE.Semialgebraic.PolynomialMap
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPolynomial

/-!
# Semialgebraicity of actual prescribed terminal payoffs

The literal finite-calendar product simplex maps to prescribed payoffs by the
existing payoff polynomials. The existing exact finite-calendar realization
theorem identifies that image with all actual behavioral prescribed payoffs.
No response-cap coordinate or cap-preserving compression is used.
-/

namespace GameTheory

open scoped BigOperators

variable {n dimensions deadline : ℕ}

/-- The literal finite-calendar probability constraints in flat real coordinates. -/
def quittingFiniteCalendarCoordinateSimplex
    (coordinates : QuittingFiniteCalendarVariable (Fin n) deadline ≃ Fin dimensions) :
    Set (Fin dimensions → ℝ) :=
  {point | (∀ index, 0 ≤ point index) ∧
    ∀ who : Fin n, ∑ choice : Option (Fin deadline), point (coordinates (who, choice)) = 1}

/-- Flat simplex coordinates define genuine independent finite-calendar marginals. -/
def quittingFiniteCalendarSimplexFromCoordinates
    (coordinates : QuittingFiniteCalendarVariable (Fin n) deadline ≃ Fin dimensions)
    (point : Fin dimensions → ℝ) (hpoint : point ∈ quittingFiniteCalendarCoordinateSimplex
      coordinates) : MixedSimplex (Fin n)
        (fun _ => QuittingFiniteDeadlineTimingAction deadline) :=
  fun who => ⟨fun choice => point (coordinates (who, choice)),
    ⟨fun choice => hpoint.1 (coordinates (who, choice)), hpoint.2 who⟩⟩

/-- Encode a genuine finite-calendar profile in the chosen flat coordinate order. -/
def quittingFiniteCalendarCoordinates
    (coordinates : QuittingFiniteCalendarVariable (Fin n) deadline ≃ Fin dimensions)
    (profile : MixedSimplex (Fin n)
      (fun _ => QuittingFiniteDeadlineTimingAction deadline)) : Fin dimensions → ℝ :=
  fun index => profile (coordinates.symm index).1 (coordinates.symm index).2

theorem quittingFiniteCalendarCoordinates_mem_simplex
    (coordinates : QuittingFiniteCalendarVariable (Fin n) deadline ≃ Fin dimensions)
    (profile : MixedSimplex (Fin n)
      (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    quittingFiniteCalendarCoordinates coordinates profile ∈
      quittingFiniteCalendarCoordinateSimplex coordinates := by
  constructor
  · intro index
    exact (profile (coordinates.symm index).1).property.1 (coordinates.symm index).2
  · intro who
    calc
      _ = ∑ choice, profile who choice := by
        apply Finset.sum_congr rfl
        intro choice _
        change profile (coordinates.symm (coordinates (who, choice))).1
          (coordinates.symm (coordinates (who, choice))).2 = profile who choice
        rw [coordinates.symm_apply_apply]
      _ = 1 := (profile who).property.2

/-- The source simplex is a finite conjunction of polynomial nonnegativity and row sums. -/
theorem isSemialgebraic_quittingFiniteCalendarCoordinateSimplex
    (coordinates : QuittingFiniteCalendarVariable (Fin n) deadline ≃ Fin dimensions) :
    MathUE.IsSemialgebraic (quittingFiniteCalendarCoordinateSimplex coordinates) := by
  let sums : Fin n → MvPolynomial (Fin dimensions) ℝ := fun who =>
    (∑ choice : Option (Fin deadline), MvPolynomial.X (coordinates (who, choice))) - 1
  refine ⟨.and
    (Math.PolynomialSignCell.SignFormula.conjunction (List.ofFn
      (fun index : Fin dimensions => .not (.atom (MvPolynomial.X index) (-1)))))
    (Math.PolynomialSignCell.SignFormula.conjunction (List.ofFn
      (fun who : Fin n => .atom (sums who) 0))), ?_⟩
  intro point
  simp only [quittingFiniteCalendarCoordinateSimplex, Set.mem_setOf_eq,
    MathUE.RealPolynomialSignFormula.HoldsAt, Math.PolynomialSignCell.SignFormula.Holds,
    Math.PolynomialSignCell.SignFormula.holds_conjunction_iff,
    List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    sign_eq_neg_one_iff, not_lt, sign_eq_zero_iff, sums, map_sub, map_sum,
    MvPolynomial.eval_X, map_one, sub_eq_zero]

/-- The existing raw payoff polynomials, with only their finite variables renamed. -/
noncomputable def quittingFiniteCalendarCoordinatePayoffPolynomials
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (coordinates : QuittingFiniteCalendarVariable (Fin n) deadline ≃ Fin dimensions) :
    Fin n → MvPolynomial (Fin dimensions) ℝ :=
  fun observer => MvPolynomial.rename coordinates
    (quittingFiniteCalendarRawPayoffPolynomial reward deadline observer)

theorem evaluate_quittingFiniteCalendarCoordinatePayoffPolynomials
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (coordinates : QuittingFiniteCalendarVariable (Fin n) deadline ≃ Fin dimensions)
    (point : Fin dimensions → ℝ)
    (hpoint : point ∈ quittingFiniteCalendarCoordinateSimplex coordinates) :
    MathUE.evaluatePolynomialMap (quittingFiniteCalendarCoordinatePayoffPolynomials
      reward coordinates) point =
        quittingFiniteCalendarRawPayoff reward deadline
          (quittingFiniteCalendarSimplexFromCoordinates coordinates point hpoint) := by
  funext observer
  rw [MathUE.evaluatePolynomialMap, quittingFiniteCalendarCoordinatePayoffPolynomials,
    MvPolynomial.eval_rename]
  exact eval_quittingFiniteCalendarRawPayoffPolynomial reward deadline observer
    (quittingFiniteCalendarSimplexFromCoordinates coordinates point hpoint)

theorem evaluate_quittingFiniteCalendarCoordinates
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (coordinates : QuittingFiniteCalendarVariable (Fin n) deadline ≃ Fin dimensions)
    (profile : MixedSimplex (Fin n)
      (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    MathUE.evaluatePolynomialMap (quittingFiniteCalendarCoordinatePayoffPolynomials
      reward coordinates) (quittingFiniteCalendarCoordinates coordinates profile) =
        quittingFiniteCalendarRawPayoff reward deadline profile := by
  funext observer
  rw [MathUE.evaluatePolynomialMap, quittingFiniteCalendarCoordinatePayoffPolynomials,
    MvPolynomial.eval_rename]
  have heq : quittingFiniteCalendarCoordinates coordinates profile ∘ coordinates =
      fun pair => profile pair.1 pair.2 := by
    funext pair
    change profile (coordinates.symm (coordinates pair)).1
      (coordinates.symm (coordinates pair)).2 = profile pair.1 pair.2
    rw [coordinates.symm_apply_apply]
  rw [heq]
  exact eval_quittingFiniteCalendarRawPayoffPolynomial reward deadline observer profile

/-- The image of the literal flat simplex is exactly the original raw payoff range. -/
theorem image_quittingFiniteCalendarCoordinatePayoffPolynomials
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (coordinates : QuittingFiniteCalendarVariable (Fin n) deadline ≃ Fin dimensions) :
    MathUE.evaluatePolynomialMap (quittingFiniteCalendarCoordinatePayoffPolynomials
      reward coordinates) '' quittingFiniteCalendarCoordinateSimplex coordinates =
        Set.range (quittingFiniteCalendarRawPayoff reward deadline) := by
  ext value
  constructor
  · rintro ⟨point, hpoint, rfl⟩
    refine ⟨quittingFiniteCalendarSimplexFromCoordinates coordinates point hpoint, ?_⟩
    exact (evaluate_quittingFiniteCalendarCoordinatePayoffPolynomials
      reward coordinates point hpoint).symm
  · rintro ⟨profile, rfl⟩
    exact ⟨quittingFiniteCalendarCoordinates coordinates profile,
      quittingFiniteCalendarCoordinates_mem_simplex coordinates profile,
      evaluate_quittingFiniteCalendarCoordinates reward coordinates profile⟩

/-- Prescribed payoffs on any fixed finite calendar form a semialgebraic set. -/
theorem isSemialgebraic_range_quittingFiniteCalendarRawPayoff
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n)) (deadline : ℕ) :
    MathUE.IsSemialgebraic (Set.range (quittingFiniteCalendarRawPayoff reward deadline)) := by
  let coordinates := Fintype.equivFin (QuittingFiniteCalendarVariable (Fin n) deadline)
  have himage := MathUE.IsSemialgebraic.image_polynomialMap
    (isSemialgebraic_quittingFiniteCalendarCoordinateSimplex coordinates)
    (quittingFiniteCalendarCoordinatePayoffPolynomials reward coordinates)
  simpa only [image_quittingFiniteCalendarCoordinatePayoffPolynomials] using himage

/-- All actual behavioral prescribed terminal payoffs form a semialgebraic set.
The fixed-calendar equality is the existing payoff-only realization theorem. -/
theorem isSemialgebraic_quittingActualTerminalPayoffSet [Nonempty (Fin n)]
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n)) :
    MathUE.IsSemialgebraic (quittingActualTerminalPayoffSet reward) := by
  rw [quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff]
  have heq : quittingFiniteCalendarRawPayoff reward
      (Fintype.card (Fin n) * (Fintype.card (Fin n) + 1)) =
        quittingFiniteDeadlineTimingPayoffMap reward
          (Fintype.card (Fin n) * (Fintype.card (Fin n) + 1)) := by
    funext profile
    exact quittingFiniteCalendarRawPayoff_eq_timingPayoffMap reward profile
  rw [← heq]
  exact isSemialgebraic_range_quittingFiniteCalendarRawPayoff reward _

end GameTheory
