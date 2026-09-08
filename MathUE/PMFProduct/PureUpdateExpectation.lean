import MathUE.PMFProduct.Update

/-! # Expectations after pinning one independent coordinate -/

namespace Math.PMFProduct

/-- Integrating after replacing one product marginal by a point mass equals
integrating the same coordinate overwrite against the original product law. -/
theorem expect_pmfPi_update_pure
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {A : ι → Type*} [∀ index, Finite (A index)]
    (marginals : ∀ index, PMF (A index)) (selected : ι) (value : A selected)
    (observable : (∀ index, A index) → ℝ) :
    Math.Probability.expect
        (pmfPi (Function.update marginals selected (PMF.pure value))) observable =
      Math.Probability.expect (pmfPi marginals)
        (fun draw => observable (Function.update draw selected value)) := by
  classical
  letI (index : ι) : Fintype (A index) := Fintype.ofFinite (A index)
  rw [← pmfPi_bind_update_pure]
  simp only [Math.Probability.expect_bind, Math.Probability.expect_pure]

end Math.PMFProduct
