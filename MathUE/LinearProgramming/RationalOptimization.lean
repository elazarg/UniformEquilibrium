import MathUE.LinearProgramming.RationalFeasibility
import MathUE.LinearProgramming.StrongDuality

/-!
# Exact rational optimizers

A feasible, bounded finite rational LP has rational primal and dual optimizers.
We reuse real attainment and strong duality, then rationalize the combined weak
feasibility and zero-gap system. This permits optimal coordinates equal to zero.
-/

open scoped BigOperators

namespace Math.LinearProgramming

variable {Row Col : Type*} [Fintype Row] [Fintype Col]

/-- Rational data give rational optimizers, optimal also against real feasible points.
The returned zero gap is exact, rather than an accuracy-dependent approximation. -/
theorem exists_rational_minPrimalOptimal
    (A : Row → Col → ℝ) (b : Row → ℝ) (c : Col → ℝ)
    (hA : ∀ row column, IsRationalReal (A row column))
    (hb : ∀ row, IsRationalReal (b row))
    (hc : ∀ column, IsRationalReal (c column))
    (hfeasible : ∃ x, MinPrimalFeasible A b x)
    (hbounded : ∃ lower : ℝ,
      ∀ x, MinPrimalFeasible A b x → lower ≤ minPrimalValue c x) :
    ∃ (x : Col → ℚ) (y : Row → ℚ),
      MinPrimalFeasible A b (fun column => (x column : ℝ)) ∧
      MaxDualFeasible A c (fun row => (y row : ℝ)) ∧
      maxDualValue b (fun row => (y row : ℝ)) =
        minPrimalValue c (fun column => (x column : ℝ)) ∧
      ∀ z, MinPrimalFeasible A b z →
        minPrimalValue c (fun column => (x column : ℝ)) ≤ minPrimalValue c z := by
  classical
  obtain ⟨realPrimal, hprimal, hoptimal⟩ :=
    exists_minPrimalOptimal_of_feasible_of_bounded hfeasible hbounded
  obtain ⟨realDual, hdual, hgap⟩ := lp_strong_duality hprimal hoptimal
  have hgapSum : (∑ row, b row * realDual row) =
      ∑ column, c column * realPrimal column := hgap
  let combinedA : (Row ⊕ Col) ⊕ Bool → Col ⊕ Row → ℝ
    | .inl (.inl row), .inl column => A row column
    | .inl (.inl _), .inr _ => 0
    | .inl (.inr _), .inl _ => 0
    | .inl (.inr column), .inr row => -A row column
    | .inr false, .inl column => c column
    | .inr false, .inr row => -b row
    | .inr true, .inl column => -c column
    | .inr true, .inr row => b row
  let combinedB : (Row ⊕ Col) ⊕ Bool → ℝ
    | .inl (.inl row) => b row
    | .inl (.inr column) => -c column
    | .inr _ => 0
  have hneg {value : ℝ} (h : IsRationalReal value) : IsRationalReal (-value) := by
    simpa using IsRationalReal.zero.sub h
  have hcombinedA : ∀ row column, IsRationalReal (combinedA row column) := by
    intro row column
    rcases row with (row | column') | side
    · cases column with
      | inl column => exact hA row column
      | inr _ => exact IsRationalReal.zero
    · cases column with
      | inl _ => exact IsRationalReal.zero
      | inr row => exact hneg (hA row column')
    · cases side <;> cases column
      · exact hc _
      · exact hneg (hb _)
      · exact hneg (hc _)
      · exact hb _
  have hcombinedB : ∀ row, IsRationalReal (combinedB row) := by
    intro row
    rcases row with (row | column) | side
    · exact hb row
    · exact hneg (hc column)
    · exact IsRationalReal.zero
  have hcombined : ∃ point : Col ⊕ Row → ℝ, (∀ coordinate, 0 ≤ point coordinate) ∧
      ∀ row, combinedB row ≤ ∑ coordinate, combinedA row coordinate * point coordinate := by
    refine ⟨Sum.elim realPrimal realDual, ?_, ?_⟩
    · intro coordinate
      cases coordinate with
      | inl column => exact hprimal.1 column
      | inr row => exact hdual.1 row
    · intro row
      rcases row with (row | column) | side
      · simpa [combinedA, combinedB, Fintype.sum_sum_type, rowEval] using hprimal.2 row
      · have h := hdual.2 column
        simp only [colEval] at h
        simpa [combinedA, combinedB, Fintype.sum_sum_type, Finset.sum_neg_distrib,
          neg_mul, mul_comm] using neg_le_neg h
      · cases side <;>
          simp [combinedA, combinedB, Fintype.sum_sum_type, Finset.sum_neg_distrib,
            neg_mul, hgapSum]
  obtain ⟨point, hnonneg, hrows⟩ := exists_nonnegative_rational_solution
    combinedA combinedB hcombinedA hcombinedB hcombined
  let x : Col → ℚ := fun column => point (.inl column)
  let y : Row → ℚ := fun row => point (.inr row)
  have hx : MinPrimalFeasible A b (fun column => (x column : ℝ)) := by
    constructor
    · intro column
      change 0 ≤ (point (.inl column) : ℝ)
      exact Rat.cast_nonneg.mpr (hnonneg (.inl column))
    · intro row
      simpa [combinedA, combinedB, Fintype.sum_sum_type, rowEval, x] using
        hrows (.inl (.inl row))
  have hy : MaxDualFeasible A c (fun row => (y row : ℝ)) := by
    constructor
    · intro row
      change 0 ≤ (point (.inr row) : ℝ)
      exact Rat.cast_nonneg.mpr (hnonneg (.inr row))
    · intro column
      have h := hrows (.inl (.inr column))
      have hnegative : -c column ≤ -colEval A (fun row => (y row : ℝ)) column := by
        simpa [combinedA, combinedB, Fintype.sum_sum_type, Finset.sum_neg_distrib,
          neg_mul, colEval, y, mul_comm] using h
      exact neg_le_neg_iff.mp hnegative
  have hzero : maxDualValue b (fun row => (y row : ℝ)) =
      minPrimalValue c (fun column => (x column : ℝ)) := by
    have hfirst := hrows (.inr false)
    have hsecond := hrows (.inr true)
    simp only [combinedA, combinedB, Fintype.sum_sum_type, neg_mul,
      Finset.sum_neg_distrib] at hfirst hsecond
    dsimp [minPrimalValue, maxDualValue, dot, x, y]
    linarith
  refine ⟨x, y, hx, hy, hzero, ?_⟩
  intro z hz
  rw [← hzero]
  exact min_weak_duality hz hy

end Math.LinearProgramming
