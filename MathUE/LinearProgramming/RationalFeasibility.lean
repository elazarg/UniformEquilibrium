import Maths.LinearProgramming.FourierMotzkin
import MathUE.LinearAlgebra.RationalAffineCoefficients
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.BigOperators

/-!
# Exact rational feasibility

Weak finite rational linear systems have a rational point whenever they have a real point.
The theorem of the alternative supplies the proof: a rational infeasibility certificate
would remain an infeasibility certificate after casting to the reals. Equalities may be
encoded by their two weak inequalities; no interior point is required.
-/

open scoped BigOperators

namespace Math.LinearProgramming

variable {Row Col : Type*} [Fintype Row] [Fintype Col]

omit [Fintype Col] in
private theorem exists_rational_solution_fin {n : ℕ} (A : Row → Fin n → ℚ)
    (b : Row → ℚ)
    (hreal : ∃ x : Fin n → ℝ, ∀ row,
      (b row : ℝ) ≤ ∑ column, (A row column : ℝ) * x column) :
    ∃ x : Fin n → ℚ, ∀ row, b row ≤ ∑ column, A row column * x column := by
  by_contra hnone
  have hinfeasible : ¬ Maths.LinearProgramming.IsFeasible A b := hnone
  obtain ⟨certificate, hnonneg, hzero, hpositive⟩ :=
    (Maths.LinearProgramming.theorem_of_alternative A b).mp hinfeasible
  apply Maths.LinearProgramming.feas_cert_disjoint
    (fun row column => (A row column : ℝ)) (fun row => (b row : ℝ))
    hreal
  refine ⟨fun row => (certificate row : ℝ), ?_, ?_, ?_⟩
  · intro row
    change 0 ≤ (certificate row : ℝ)
    exact Rat.cast_nonneg.mpr (hnonneg row)
  · intro column
    change (∑ row, (certificate row : ℝ) * (A row column : ℝ)) = 0
    have hcast := congrArg (fun value : ℚ => (value : ℝ)) (hzero column)
    simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_zero] using hcast
  · change 0 < ∑ row, (certificate row : ℝ) * (b row : ℝ)
    have hcast := (Rat.cast_pos (K := ℝ)).mpr hpositive
    simpa only [Rat.cast_sum, Rat.cast_mul] using hcast

/-- Exact rational feasibility, with arbitrary finite row and coordinate types. -/
theorem exists_rational_solution (A : Row → Col → ℚ) (b : Row → ℚ)
    (hreal : ∃ x : Col → ℝ, ∀ row,
      (b row : ℝ) ≤ ∑ column, (A row column : ℝ) * x column) :
    ∃ x : Col → ℚ, ∀ row, b row ≤ ∑ column, A row column * x column := by
  classical
  let coordinates := Fintype.equivFin Col
  obtain ⟨x, hx⟩ := hreal
  have hindexed : ∃ y : Fin (Fintype.card Col) → ℝ, ∀ row,
      (b row : ℝ) ≤
        ∑ column, (A row (coordinates.symm column) : ℝ) * y column := by
    refine ⟨fun column => x (coordinates.symm column), ?_⟩
    intro row
    have hsum :
        (∑ column : Fin (Fintype.card Col),
          (A row (coordinates.symm column) : ℝ) * x (coordinates.symm column)) =
          ∑ column : Col, (A row column : ℝ) * x column :=
      Equiv.sum_comp coordinates.symm (fun column : Col => (A row column : ℝ) * x column)
    rw [hsum]
    exact hx row
  obtain ⟨rational, hrational⟩ := exists_rational_solution_fin
    (fun row column => A row (coordinates.symm column)) b hindexed
  refine ⟨fun column => rational (coordinates column), ?_⟩
  intro row
  have hsum := Equiv.sum_comp coordinates.symm
    (fun column => A row column * rational (coordinates column))
  calc
    b row ≤ ∑ column, A row (coordinates.symm column) * rational column :=
      hrational row
    _ = ∑ column, A row column * rational (coordinates column) := by
      simpa only [Equiv.apply_symm_apply] using hsum

/-- Semantic real coefficients may be used when every coefficient is exactly rational. -/
theorem exists_rational_solution_of_coefficients (A : Row → Col → ℝ) (b : Row → ℝ)
    (hA : ∀ row column, IsRationalReal (A row column))
    (hb : ∀ row, IsRationalReal (b row))
    (hreal : ∃ x : Col → ℝ, ∀ row, b row ≤ ∑ column, A row column * x column) :
    ∃ x : Col → ℚ, ∀ row, b row ≤ ∑ column, A row column * (x column : ℝ) := by
  classical
  choose rationalA hAeq using hA
  choose rationalB hBeq using hb
  have hcast : ∃ x : Col → ℝ, ∀ row,
      (rationalB row : ℝ) ≤ ∑ column, (rationalA row column : ℝ) * x column := by
    simpa only [hAeq, hBeq] using hreal
  obtain ⟨x, hx⟩ := exists_rational_solution rationalA rationalB hcast
  refine ⟨x, ?_⟩
  intro row
  rw [hBeq row]
  simp only [hAeq]
  have hrow : (rationalB row : ℝ) ≤
      ((∑ column, rationalA row column * x column : ℚ) : ℝ) :=
    Rat.cast_le.mpr (hx row)
  simpa only [Rat.cast_sum, Rat.cast_mul] using hrow

/-- Nonnegative coordinates are weak rational rows, not an interiority requirement. -/
theorem exists_nonnegative_rational_solution (A : Row → Col → ℝ) (b : Row → ℝ)
    (hA : ∀ row column, IsRationalReal (A row column))
    (hb : ∀ row, IsRationalReal (b row))
    (hreal : ∃ x : Col → ℝ, (∀ column, 0 ≤ x column) ∧
      ∀ row, b row ≤ ∑ column, A row column * x column) :
    ∃ x : Col → ℚ, (∀ column, 0 ≤ x column) ∧
      ∀ row, b row ≤ ∑ column, A row column * (x column : ℝ) := by
  classical
  let combinedA : Row ⊕ Col → Col → ℝ
    | .inl row, column => A row column
    | .inr coordinate, column => if coordinate = column then 1 else 0
  let combinedB : Row ⊕ Col → ℝ
    | .inl row => b row
    | .inr _ => 0
  have hcombinedA : ∀ row column, IsRationalReal (combinedA row column) := by
    intro row column
    cases row with
    | inl row => exact hA row column
    | inr coordinate =>
        dsimp only [combinedA]
        split_ifs
        · exact IsRationalReal.one
        · exact IsRationalReal.zero
  have hcombinedB : ∀ row, IsRationalReal (combinedB row) := by
    intro row
    cases row with
    | inl row => exact hb row
    | inr _ => exact IsRationalReal.zero
  have hcombined : ∃ x : Col → ℝ, ∀ row,
      combinedB row ≤ ∑ column, combinedA row column * x column := by
    obtain ⟨x, hx, hrows⟩ := hreal
    refine ⟨x, ?_⟩
    intro row
    cases row with
    | inl row => exact hrows row
    | inr coordinate => simpa [combinedA, combinedB] using hx coordinate
  obtain ⟨x, hx⟩ := exists_rational_solution_of_coefficients
    combinedA combinedB hcombinedA hcombinedB hcombined
  refine ⟨x, ?_, fun row => hx (.inl row)⟩
  intro coordinate
  have h := hx (.inr coordinate)
  have hcast : (0 : ℝ) ≤ x coordinate := by
    simpa [combinedA, combinedB] using h
  exact_mod_cast hcast

end Math.LinearProgramming

namespace Math.IsRationalReal

theorem min {first second : ℝ} (hfirst : Math.IsRationalReal first)
    (hsecond : Math.IsRationalReal second) : Math.IsRationalReal (min first second) := by
  by_cases h : first ≤ second
  · simpa only [min_eq_left h] using hfirst
  · simpa only [min_eq_right (le_of_not_ge h)] using hsecond

theorem max {first second : ℝ} (hfirst : Math.IsRationalReal first)
    (hsecond : Math.IsRationalReal second) : Math.IsRationalReal (max first second) := by
  by_cases h : second ≤ first
  · simpa only [max_eq_left h] using hfirst
  · simpa only [max_eq_right (le_of_not_ge h)] using hsecond

theorem finset_min (values : Finset ℝ) (hnonempty : values.Nonempty)
    (hvalues : ∀ value ∈ values, Math.IsRationalReal value) :
    Math.IsRationalReal (values.min' hnonempty) :=
  hvalues _ (Finset.min'_mem values hnonempty)

end Math.IsRationalReal
