import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingBernstein

/-! # Strict signs from all nine half-ceiling Bernstein coefficients -/

noncomputable section

namespace GameTheory

private theorem halfBasis_nonneg (index : Fin 3) (rate : ℝ)
    (hrate : 0 ≤ rate ∧ rate ≤ 1) :
    0 ≤ quittingHalfBernsteinBasis index rate := by
  fin_cases index <;> simp [quittingHalfBernsteinBasis] <;> nlinarith [sq_nonneg (1 - rate)]

private theorem sum_halfBasis (rate : ℝ) :
    (∑ index : Fin 3, quittingHalfBernsteinBasis index rate) = 1 := by
  simp [quittingHalfBernsteinBasis, Fin.sum_univ_succ]
  ring

private theorem exists_halfBasis_pos (rate : ℝ) (hrate : 0 ≤ rate ∧ rate ≤ 1) :
    ∃ index : Fin 3, 0 < quittingHalfBernsteinBasis index rate := by
  by_contra hnone
  have hzero (index : Fin 3) : quittingHalfBernsteinBasis index rate = 0 :=
    le_antisymm (le_of_not_gt (fun hpos => hnone ⟨index, hpos⟩))
      (halfBasis_nonneg index rate hrate)
  have hsum := sum_halfBasis rate
  simp [hzero] at hsum

/-- Nine strictly negative coefficients make their tensor Bernstein polynomial
strictly negative throughout the closed unit square. -/
theorem quittingHalfTensor_sum_neg_of_coefficients_neg
    (coefficient : Fin 3 → Fin 3 → ℝ) (x y : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hcoeff : ∀ first second, coefficient first second < 0) :
    (∑ first : Fin 3, ∑ second : Fin 3,
      coefficient first second * quittingHalfBernsteinBasis first x *
        quittingHalfBernsteinBasis second y) < 0 := by
  obtain ⟨first, hfirst⟩ := exists_halfBasis_pos x hx
  obtain ⟨second, hsecond⟩ := exists_halfBasis_pos y hy
  have hpositive : 0 < ∑ first : Fin 3, ∑ second : Fin 3,
      (-coefficient first second) * quittingHalfBernsteinBasis first x *
        quittingHalfBernsteinBasis second y := by
    apply Finset.sum_pos'
    · intro index _
      apply Finset.sum_nonneg
      intro coordinate _
      exact mul_nonneg
        (mul_nonneg (neg_nonneg.mpr (hcoeff index coordinate).le)
          (halfBasis_nonneg index x hx))
        (halfBasis_nonneg coordinate y hy)
    · refine ⟨first, Finset.mem_univ first, ?_⟩
      apply Finset.sum_pos'
      · intro coordinate _
        exact mul_nonneg
          (mul_nonneg (neg_nonneg.mpr (hcoeff first coordinate).le)
            (halfBasis_nonneg first x hx))
          (halfBasis_nonneg coordinate y hy)
      · exact ⟨second, Finset.mem_univ second,
          mul_pos (mul_pos (neg_pos.mpr (hcoeff first second)) hfirst) hsecond⟩
  have hneg :
      (∑ first : Fin 3, ∑ second : Fin 3,
        coefficient first second * quittingHalfBernsteinBasis first x *
          quittingHalfBernsteinBasis second y) =
        -(∑ first : Fin 3, ∑ second : Fin 3,
          (-coefficient first second) * quittingHalfBernsteinBasis first x *
            quittingHalfBernsteinBasis second y) := by
    simp_rw [← Finset.sum_neg_distrib]
    congr 1
    funext first
    congr 1
    funext second
    ring
  rw [hneg]
  linarith

end GameTheory
