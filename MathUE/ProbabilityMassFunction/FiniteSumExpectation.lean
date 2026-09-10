import MathUE.Probability

/-!
# Finite sums under PMF expectation

Finite sums of bounded real integrands commute with expectation on arbitrary
discrete sample spaces.
-/

namespace Math.Probability

open scoped BigOperators

/-- A finite sum of pointwise bounded real integrands commutes with expectation
over an arbitrary discrete probability mass function. -/
theorem expect_finset_sum_of_bounded
    {Ω κ : Type*} (law : PMF Ω) (S : Finset κ) (f : κ → Ω → ℝ)
    (bound : κ → ℝ) (hbound : ∀ i ∈ S, ∀ ω, |f i ω| ≤ bound i) :
    expect law (fun ω => ∑ i ∈ S, f i ω) =
      ∑ i ∈ S, expect law (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      simp_rw [Finset.sum_insert hi]
      rw [expect_add_of_summable]
      · rw [ih]
        intro j hj
        exact hbound j (Finset.mem_insert_of_mem hj)
      · exact expect_summable_of_bounded law (f i)
          (hbound i (Finset.mem_insert_self i S))
      · apply expect_summable_of_bounded law
        intro ω
        calc
          |∑ j ∈ S, f j ω| ≤ ∑ j ∈ S, |f j ω| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ S, bound j := by
            exact Finset.sum_le_sum fun j hj => hbound j
              (Finset.mem_insert_of_mem hj) ω

end Math.Probability
