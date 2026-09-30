import MathUE.DirectedTransport.FiniteInequality.Nonnegative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Quantitative stability of a literal nonnegative finite LP dual -/

noncomputable section

namespace Maths.FiniteInequality

open scoped BigOperators

variable {State Row : Type*} [Fintype State] [Fintype Row]

/-- The difference of two coordinates changes by at most twice their common error. -/
theorem abs_sub_differences_le (firstLeft firstRight secondLeft secondRight error : ℝ)
    (hleft : |secondLeft - firstLeft| ≤ error)
    (hright : |secondRight - firstRight| ≤ error) :
    |(secondLeft - secondRight) - (firstLeft - firstRight)| ≤ 2 * error := by
  obtain ⟨hlower, hupper⟩ := abs_le.mp hleft
  obtain ⟨hlower', hupper'⟩ := abs_le.mp hright
  apply abs_le.mpr
  constructor <;> linarith

/-- A nonnegative weighted row sum loses at most the row error times total weight. -/
theorem abs_weightedSum_sub_le
    (coefficient first second : Row → ℝ) (error : ℝ)
    (hcoefficient : ∀ row, 0 ≤ coefficient row)
    (hclose : ∀ row, |second row - first row| ≤ error) :
    |(∑ row, coefficient row * second row) -
        ∑ row, coefficient row * first row| ≤ error * ∑ row, coefficient row := by
  classical
  calc
    _ = |∑ row, coefficient row * (second row - first row)| := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ row, |coefficient row * (second row - first row)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ row, coefficient row * error := by
      apply Finset.sum_le_sum
      intro row _
      rw [abs_mul, abs_of_nonneg (hcoefficient row)]
      exact mul_le_mul_of_nonneg_left (hclose row) (hcoefficient row)
    _ = error * ∑ row, coefficient row := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro row _
      ring

/-- Literal strict dual margins survive entrywise perturbation. The conclusion
delegates infeasibility to the existing exact finite-inequality alternative. -/
theorem not_exists_nonnegativePotential_of_perturbation
    (delta otherDelta : Row → State → ℝ) (base otherBase coefficient : Row → ℝ)
    (error : ℝ) (hcoefficient : ∀ row, 0 ≤ coefficient row)
    (hdelta : ∀ row state, |otherDelta row state - delta row state| ≤ error)
    (hbase : ∀ row, |otherBase row - base row| ≤ error)
    (hcolumns : ∀ state,
      (∑ row, coefficient row * delta row state) + error * ∑ row, coefficient row ≤ 0)
    (hobjective : error * ∑ row, coefficient row < ∑ row, coefficient row * base row) :
    ¬∃ potential : State → ℝ, (∀ state, 0 ≤ potential state) ∧
      ∀ row, otherBase row ≤ dotProduct (otherDelta row) potential := by
  apply (not_exists_nonnegativePotential_iff_exists_nonpositiveCertificate
    otherDelta otherBase).mpr
  refine ⟨coefficient, hcoefficient, ?_, ?_⟩
  · intro state
    have h := (abs_le.mp (abs_weightedSum_sub_le coefficient
      (fun row => delta row state) (fun row => otherDelta row state) error
      hcoefficient (fun row => hdelta row state))).2
    linarith [hcolumns state]
  · have h := (abs_le.mp (abs_weightedSum_sub_le coefficient base otherBase error
      hcoefficient hbase)).1
    linarith

end Maths.FiniteInequality
