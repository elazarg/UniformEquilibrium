import MathUE.TwoCoordinateSparseSimplex
import MathUE.ProbabilityMassFunction.Simplex

/-! # Sparse mixtures for two expectations of three independent finite laws -/

noncomputable section

namespace Math
namespace Probability

section ThreeFiniteLaws

variable {First Second Third : Type*}
variable [Fintype First] [Fintype Second] [Fintype Third]

/-- Expectation of a finite kernel under three independent complete marginals. -/
def threeIndependentValue (kernel : First → Second → Third → ℝ)
    (first : PMF First) (second : PMF Second) (third : PMF Third) : ℝ :=
  expect first (fun i => expect second (fun j => expect third (kernel i j)))

theorem threeIndependentValue_eq_simplex (kernel : First → Second → Third → ℝ)
    (first : PMF First) (second : PMF Second) (third : PMF Third) :
    threeIndependentValue kernel first second third =
      threeMarginalValue kernel (ProbabilityMassFunction.stdSimplexEquiv first)
        (ProbabilityMassFunction.stdSimplexEquiv second)
        (ProbabilityMassFunction.stdSimplexEquiv third) := by
  simp only [threeIndependentValue, expect_eq_sum, threeMarginalValue, wsum, dotProduct]
  rfl

/-- Passing from a simplex vector to its PMF preserves the actual support cardinality. -/
theorem card_support_simplexLaw {Atom : Type*} [Fintype Atom]
    (source : stdSimplex ℝ Atom) :
    Fintype.card {atom // ProbabilityMassFunction.ofVector source.val source.property atom ≠ 0} =
      Fintype.card {atom // source.val atom ≠ 0} := by
  classical
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun atom => by
    rw [ProbabilityMassFunction.ofVector_ne_zero_iff]
    exact ⟨ne_of_gt, fun hne => lt_of_le_of_ne (source.property.1 atom) hne.symm⟩

/-- The sparse global maximizer is a product of genuine finite PMFs, with the
cardinality bound stated on their actual nonzero supports. -/
theorem exists_three_twoSupported_pmf_sqrt_maximizer
    [Nonempty First] [Nonempty Second] [Nonempty Third]
    (firstKernel secondKernel : First → Second → Third → ℝ) :
    ∃ first : PMF First, ∃ second : PMF Second, ∃ third : PMF Third,
      Fintype.card {i // first i ≠ 0} ≤ 2 ∧
      Fintype.card {j // second j ≠ 0} ≤ 2 ∧
      Fintype.card {k // third k ≠ 0} ≤ 2 ∧
      ∀ otherFirst : PMF First, ∀ otherSecond : PMF Second, ∀ otherThird : PMF Third,
        Real.sqrt (threeIndependentValue firstKernel otherFirst otherSecond otherThird) +
            Real.sqrt (threeIndependentValue secondKernel otherFirst otherSecond otherThird) ≤
          Real.sqrt (threeIndependentValue firstKernel first second third) +
            Real.sqrt (threeIndependentValue secondKernel first second third) := by
  obtain ⟨first, second, third, hfirst, hsecond, hthird, hmax⟩ :=
    exists_three_twoSupported_marginals_sqrt_maximizer firstKernel secondKernel
  refine ⟨ProbabilityMassFunction.stdSimplexEquiv.symm first,
    ProbabilityMassFunction.stdSimplexEquiv.symm second,
    ProbabilityMassFunction.stdSimplexEquiv.symm third, ?_, ?_, ?_, ?_⟩
  · exact (card_support_simplexLaw first).trans_le hfirst
  · exact (card_support_simplexLaw second).trans_le hsecond
  · exact (card_support_simplexLaw third).trans_le hthird
  · intro otherFirst otherSecond otherThird
    simp only [threeIndependentValue_eq_simplex, Equiv.apply_symm_apply]
    exact hmax _ _ _

end ThreeFiniteLaws

/-- Three independent finite laws can be compressed while preserving the
first kernel expectation exactly and weakly increasing the second. -/
theorem exists_three_twoSupported_pmf_preserving_first_improving_second
    {First Second Third : Type*}
    [Fintype First] [Fintype Second] [Fintype Third]
    (firstKernel secondKernel : First → Second → Third → ℝ)
    (first : PMF First) (second : PMF Second) (third : PMF Third) :
    ∃ nextFirst : PMF First, ∃ nextSecond : PMF Second, ∃ nextThird : PMF Third,
      Fintype.card {i // nextFirst i ≠ 0} ≤ 2 ∧
      Fintype.card {j // nextSecond j ≠ 0} ≤ 2 ∧
      Fintype.card {k // nextThird k ≠ 0} ≤ 2 ∧
      threeIndependentValue firstKernel nextFirst nextSecond nextThird =
        threeIndependentValue firstKernel first second third ∧
      threeIndependentValue secondKernel first second third ≤
        threeIndependentValue secondKernel nextFirst nextSecond nextThird := by
  classical
  obtain ⟨nextFirst, nextSecond, nextThird, hfirst, hsecond, hthird, heq, hle⟩ :=
    exists_three_twoSupported_marginals_preserving_first_improving_second
      firstKernel secondKernel (ProbabilityMassFunction.stdSimplexEquiv first)
        (ProbabilityMassFunction.stdSimplexEquiv second)
        (ProbabilityMassFunction.stdSimplexEquiv third)
  refine ⟨ProbabilityMassFunction.stdSimplexEquiv.symm nextFirst,
    ProbabilityMassFunction.stdSimplexEquiv.symm nextSecond,
    ProbabilityMassFunction.stdSimplexEquiv.symm nextThird,
    (card_support_simplexLaw nextFirst).trans_le hfirst,
    (card_support_simplexLaw nextSecond).trans_le hsecond,
    (card_support_simplexLaw nextThird).trans_le hthird, ?_, ?_⟩
  · simpa only [threeIndependentValue_eq_simplex, Equiv.apply_symm_apply] using heq
  · simpa only [threeIndependentValue_eq_simplex, Equiv.apply_symm_apply] using hle

end Probability
end Math
