import MathUE.DirectedTransport.FiniteInequality.Arithmetic

/-!
# Finite inequalities with nonnegative potentials

This file augments a finite inequality system by one coordinate row per
potential coordinate. The existing real and rational alternatives then give
the exact dual condition with nonpositive weighted columns.
-/

noncomputable section

namespace Math
namespace FiniteInequality

open scoped BigOperators

universe uS uR

variable {State : Type uS} {Row : Type uR}

/-- Add coordinate rows imposing nonnegativity of a potential. -/
def nonnegativePotentialDelta {K : Type*} [Zero K] [One K]
    (delta : Row → State → K) : Row ⊕ State → State → K := by
  classical
  exact fun action => match action with
    | Sum.inl row => delta row
    | Sum.inr coordinate => fun state => if state = coordinate then 1 else 0

/-- Coordinate nonnegativity rows have zero right-hand side. -/
def nonnegativePotentialBase {K : Type*} [Zero K]
    (base : Row → K) : Row ⊕ State → K
  | Sum.inl row => base row
  | Sum.inr _ => 0

theorem nonnegativePotential_constraints_iff_real
    [Fintype State] [Fintype Row]
    (delta : Row → State → ℝ) (base : Row → ℝ)
    (potential : State → ℝ) :
    (∀ action, nonnegativePotentialBase base action ≤
      dotProduct (nonnegativePotentialDelta delta action) potential) ↔
      (∀ state, 0 ≤ potential state) ∧
        ∀ row, base row ≤ dotProduct (delta row) potential := by
  classical
  constructor
  · intro h
    constructor
    · intro state
      have hstate := h (Sum.inr state)
      simpa [nonnegativePotentialBase, nonnegativePotentialDelta, dotProduct] using hstate
    · intro row
      simpa [nonnegativePotentialBase, nonnegativePotentialDelta] using h (Sum.inl row)
  · rintro ⟨hnonnegative, hrow⟩ action
    cases action with
    | inl row =>
        simpa [nonnegativePotentialBase, nonnegativePotentialDelta] using hrow row
    | inr state =>
        simpa [nonnegativePotentialBase, nonnegativePotentialDelta, dotProduct] using
          hnonnegative state

theorem nonnegativePotential_constraints_iff_rat
    [Fintype State] [Fintype Row]
    (delta : Row → State → ℚ) (base : Row → ℚ)
    (potential : State → ℚ) :
    (∀ action, nonnegativePotentialBase base action ≤
      ratDotProduct (nonnegativePotentialDelta delta action) potential) ↔
      (∀ state, 0 ≤ potential state) ∧
        ∀ row, base row ≤ ratDotProduct (delta row) potential := by
  classical
  constructor
  · intro h
    constructor
    · intro state
      have hstate := h (Sum.inr state)
      simpa [nonnegativePotentialBase, nonnegativePotentialDelta, ratDotProduct] using hstate
    · intro row
      simpa [nonnegativePotentialBase, nonnegativePotentialDelta] using h (Sum.inl row)
  · rintro ⟨hnonnegative, hrow⟩ action
    cases action with
    | inl row =>
        simpa [nonnegativePotentialBase, nonnegativePotentialDelta] using hrow row
    | inr state =>
        simpa [nonnegativePotentialBase, nonnegativePotentialDelta, ratDotProduct] using
          hnonnegative state

/-- Real finite inequalities have either a nonnegative feasible potential or
a nonnegative row combination with nonpositive columns and positive base. -/
theorem exists_nonnegativePotential_or_nonpositiveCertificate
    [Fintype State] [Fintype Row]
    (delta : Row → State → ℝ) (base : Row → ℝ) :
    (∃ potential : State → ℝ,
      (∀ state, 0 ≤ potential state) ∧
      ∀ row, base row ≤ dotProduct (delta row) potential) ∨
    (∃ coefficient : Row → ℝ,
      (∀ row, 0 ≤ coefficient row) ∧
      (∀ state, ∑ row, coefficient row * delta row state ≤ 0) ∧
      0 < ∑ row, coefficient row * base row) := by
  classical
  rcases Math.exists_potential_or_nonnegative_incompatibility
      (nonnegativePotentialDelta delta) (nonnegativePotentialBase base) with
    hpotential | ⟨coefficient, hnonnegative, hbalance, hpositive⟩
  · left
    obtain ⟨potential, hpotential⟩ := hpotential
    exact ⟨potential,
      (nonnegativePotential_constraints_iff_real delta base potential).mp hpotential⟩
  · right
    let rowCoefficient : Row → ℝ := fun row => coefficient (Sum.inl row)
    refine ⟨rowCoefficient, fun row => hnonnegative (Sum.inl row), ?_, ?_⟩
    · intro state
      have hstate := hbalance state
      have hcoordinate : 0 ≤ coefficient (Sum.inr state) :=
        hnonnegative (Sum.inr state)
      simp only [Fintype.sum_sum_type, nonnegativePotentialDelta] at hstate
      have hsingle :
          (∑ coordinate, coefficient (Sum.inr coordinate) *
            (if state = coordinate then (1 : ℝ) else 0)) =
            coefficient (Sum.inr state) := by
        simp
      rw [hsingle] at hstate
      dsimp [rowCoefficient]
      linarith
    · simpa [rowCoefficient, nonnegativePotentialBase] using hpositive

/-- Rational finite inequalities have the analogous exact rational
alternative with a nonnegative potential or a nonpositive-column dual. -/
theorem exists_rationalNonnegativePotential_or_nonpositiveCertificate
    [Fintype State] [Fintype Row]
    (delta : Row → State → ℚ) (base : Row → ℚ) :
    (∃ potential : State → ℚ,
      (∀ state, 0 ≤ potential state) ∧
      ∀ row, base row ≤ ratDotProduct (delta row) potential) ∨
    (∃ coefficient : Row → ℚ,
      (∀ row, 0 ≤ coefficient row) ∧
      (∀ state, ∑ row, coefficient row * delta row state ≤ 0) ∧
      0 < ∑ row, coefficient row * base row) := by
  classical
  rcases exists_rationalPotential_or_rationalCertificate
      (nonnegativePotentialDelta delta) (nonnegativePotentialBase base) with
    hpotential | ⟨coefficient, hnonnegative, hbalance, hpositive⟩
  · left
    obtain ⟨potential, hpotential⟩ := hpotential
    exact ⟨potential,
      (nonnegativePotential_constraints_iff_rat delta base potential).mp hpotential⟩
  · right
    let rowCoefficient : Row → ℚ := fun row => coefficient (Sum.inl row)
    refine ⟨rowCoefficient, fun row => hnonnegative (Sum.inl row), ?_, ?_⟩
    · intro state
      have hstate := hbalance state
      have hcoordinate : 0 ≤ coefficient (Sum.inr state) :=
        hnonnegative (Sum.inr state)
      simp only [Fintype.sum_sum_type, nonnegativePotentialDelta] at hstate
      have hsingle :
          (∑ coordinate, coefficient (Sum.inr coordinate) *
            (if state = coordinate then (1 : ℚ) else 0)) =
            coefficient (Sum.inr state) := by
        simp
      rw [hsingle] at hstate
      dsimp [rowCoefficient]
      linarith
    · simpa [rowCoefficient, nonnegativePotentialBase] using hpositive

/-- For rational data, allowing real nonnegative potentials does not change
feasibility. -/
theorem exists_rationalNonnegativePotential_iff_exists_realNonnegativePotential
    [Fintype State] [Fintype Row]
    (delta : Row → State → ℚ) (base : Row → ℚ) :
    (∃ potential : State → ℚ,
      (∀ state, 0 ≤ potential state) ∧
      ∀ row, base row ≤ ratDotProduct (delta row) potential) ↔
    ∃ potential : State → ℝ,
      (∀ state, 0 ≤ potential state) ∧
      ∀ row, (base row : ℝ) ≤
        dotProduct (fun state => (delta row state : ℝ)) potential := by
  classical
  constructor
  · rintro ⟨potential, hnonnegative, hrow⟩
    refine ⟨fun state => (potential state : ℝ), fun state => ?_, fun row => ?_⟩
    · exact Rat.cast_nonneg.mpr (hnonnegative state)
    · have hcast := Rat.cast_mono (K := ℝ) (hrow row)
      simpa only [ratDotProduct, Rat.cast_sum, Rat.cast_mul, dotProduct] using hcast
  · rintro ⟨potential, hnonnegative, hrow⟩
    have haugmented : ∃ potential : State → ℝ,
        ∀ action, ((nonnegativePotentialBase base action : ℚ) : ℝ) ≤
          dotProduct
            (fun state =>
              ((nonnegativePotentialDelta delta action state : ℚ) : ℝ))
            potential := by
      refine ⟨potential, ?_⟩
      intro action
      cases action with
      | inl row =>
          simpa [nonnegativePotentialBase, nonnegativePotentialDelta] using hrow row
      | inr state =>
          simp only [nonnegativePotentialBase, nonnegativePotentialDelta, dotProduct]
          have hcast (current : State) :
              (((if current = state then 1 else 0 : ℚ) : ℝ)) =
                if current = state then 1 else 0 := by
            split_ifs <;> simp
          simp_rw [hcast]
          simpa using hnonnegative state
    obtain ⟨rational, hrational⟩ :=
      (exists_rationalPotential_iff_exists_realPotential
        (nonnegativePotentialDelta delta) (nonnegativePotentialBase base)).mpr haugmented
    exact ⟨rational,
      (nonnegativePotential_constraints_iff_rat delta base rational).mp hrational⟩

private theorem nonpositiveCertificate_excludes_realPotential
    [Fintype State] [Fintype Row]
    {delta : Row → State → ℝ} {base : Row → ℝ}
    {potential : State → ℝ}
    (hpotentialNonnegative : ∀ state, 0 ≤ potential state)
    (hpotential : ∀ row, base row ≤ dotProduct (delta row) potential)
    {coefficient : Row → ℝ}
    (hcoefficientNonnegative : ∀ row, 0 ≤ coefficient row)
    (hcolumns : ∀ state, ∑ row, coefficient row * delta row state ≤ 0) :
    ∑ row, coefficient row * base row ≤ 0 := by
  classical
  calc
    ∑ row, coefficient row * base row ≤
        ∑ row, coefficient row * dotProduct (delta row) potential := by
      apply Finset.sum_le_sum
      intro row _
      exact mul_le_mul_of_nonneg_left (hpotential row) (hcoefficientNonnegative row)
    _ = ∑ state, (∑ row, coefficient row * delta row state) * potential state := by
      simp only [dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro state _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      ring
    _ ≤ 0 := by
      exact Finset.sum_nonpos fun state _ =>
        mul_nonpos_of_nonpos_of_nonneg (hcolumns state) (hpotentialNonnegative state)

private theorem nonpositiveCertificate_excludes_rationalPotential
    [Fintype State] [Fintype Row]
    {delta : Row → State → ℚ} {base : Row → ℚ}
    {potential : State → ℚ}
    (hpotentialNonnegative : ∀ state, 0 ≤ potential state)
    (hpotential : ∀ row, base row ≤ ratDotProduct (delta row) potential)
    {coefficient : Row → ℚ}
    (hcoefficientNonnegative : ∀ row, 0 ≤ coefficient row)
    (hcolumns : ∀ state, ∑ row, coefficient row * delta row state ≤ 0) :
    ∑ row, coefficient row * base row ≤ 0 := by
  classical
  calc
    ∑ row, coefficient row * base row ≤
        ∑ row, coefficient row * ratDotProduct (delta row) potential := by
      apply Finset.sum_le_sum
      intro row _
      exact mul_le_mul_of_nonneg_left (hpotential row) (hcoefficientNonnegative row)
    _ = ∑ state, (∑ row, coefficient row * delta row state) * potential state := by
      simp only [ratDotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro state _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      ring
    _ ≤ 0 := by
      exact Finset.sum_nonpos fun state _ =>
        mul_nonpos_of_nonpos_of_nonneg (hcolumns state) (hpotentialNonnegative state)

/-- Real nonnegative-potential infeasibility is exactly witnessed by the
clean nonpositive-column certificate. -/
theorem not_exists_nonnegativePotential_iff_exists_nonpositiveCertificate
    [Fintype State] [Fintype Row]
    (delta : Row → State → ℝ) (base : Row → ℝ) :
    (¬∃ potential : State → ℝ,
      (∀ state, 0 ≤ potential state) ∧
      ∀ row, base row ≤ dotProduct (delta row) potential) ↔
    ∃ coefficient : Row → ℝ,
      (∀ row, 0 ≤ coefficient row) ∧
      (∀ state, ∑ row, coefficient row * delta row state ≤ 0) ∧
      0 < ∑ row, coefficient row * base row := by
  constructor
  · intro hinfeasible
    rcases exists_nonnegativePotential_or_nonpositiveCertificate delta base with
      hpotential | hcertificate
    · exact False.elim (hinfeasible hpotential)
    · exact hcertificate
  · rintro ⟨coefficient, hnonnegative, hcolumns, hpositive⟩
    rintro ⟨potential, hpotentialNonnegative, hpotential⟩
    exact (not_lt_of_ge (nonpositiveCertificate_excludes_realPotential
      hpotentialNonnegative hpotential hnonnegative hcolumns)) hpositive

/-- Rational nonnegative-potential infeasibility has the same exact rational
dual characterization. -/
theorem not_exists_rationalNonnegativePotential_iff_exists_nonpositiveCertificate
    [Fintype State] [Fintype Row]
    (delta : Row → State → ℚ) (base : Row → ℚ) :
    (¬∃ potential : State → ℚ,
      (∀ state, 0 ≤ potential state) ∧
      ∀ row, base row ≤ ratDotProduct (delta row) potential) ↔
    ∃ coefficient : Row → ℚ,
      (∀ row, 0 ≤ coefficient row) ∧
      (∀ state, ∑ row, coefficient row * delta row state ≤ 0) ∧
      0 < ∑ row, coefficient row * base row := by
  constructor
  · intro hinfeasible
    rcases exists_rationalNonnegativePotential_or_nonpositiveCertificate delta base with
      hpotential | hcertificate
    · exact False.elim (hinfeasible hpotential)
    · exact hcertificate
  · rintro ⟨coefficient, hnonnegative, hcolumns, hpositive⟩
    rintro ⟨potential, hpotentialNonnegative, hpotential⟩
    exact (not_lt_of_ge (nonpositiveCertificate_excludes_rationalPotential
      hpotentialNonnegative hpotential hnonnegative hcolumns)) hpositive

end FiniteInequality
end Math

end
