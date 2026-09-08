import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Real.Basic

/-! # Algebraic roots of polynomials with algebraic coefficients -/

namespace Polynomial

/-- A root of a nonzero real polynomial whose coefficients are all algebraic
over the rationals is itself algebraic over the rationals. -/
theorem isAlgebraic_of_eval_eq_zero_of_coeff_isAlgebraic
    (polynomial : Polynomial ℝ) (hnonzero : polynomial ≠ 0)
    (hcoefficients : ∀ degree, IsAlgebraic ℚ (polynomial.coeff degree))
    {value : ℝ} (hroot : polynomial.eval value = 0) :
    IsAlgebraic ℚ value := by
  let algebraicReals := Subalgebra.algebraicClosure ℚ ℝ
  have hcoeffs : (↑polynomial.coeffs : Set ℝ) ⊆ algebraicReals := by
    intro coefficient hcoefficient
    obtain ⟨degree, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hcoefficient
    exact hcoefficients degree
  let lifted : Polynomial algebraicReals :=
    polynomial.toSubring algebraicReals.toSubring hcoeffs
  have hmap : lifted.map (Subring.subtype algebraicReals.toSubring) = polynomial := by
    exact Polynomial.map_toSubring polynomial algebraicReals.toSubring hcoeffs
  have hlifted : lifted ≠ 0 := by
    intro hzero
    apply hnonzero
    calc
      polynomial = lifted.map (Subring.subtype algebraicReals.toSubring) := hmap.symm
      _ = (0 : Polynomial algebraicReals).map
          (Subring.subtype algebraicReals.toSubring) := congrArg _ hzero
      _ = 0 := by simp
  have halgebraicOverCoefficients : IsAlgebraic algebraicReals value := by
    have halgebraMap :
        (algebraMap algebraicReals ℝ : algebraicReals →+* ℝ) =
          Subring.subtype algebraicReals.toSubring := by
      ext coefficient
      rfl
    refine ⟨lifted, hlifted, ?_⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, halgebraMap, hmap]
    exact hroot
  exact halgebraicOverCoefficients.restrictScalars ℚ

end Polynomial
