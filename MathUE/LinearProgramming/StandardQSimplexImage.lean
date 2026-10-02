import MathUE.LinearProgramming.CopositiveQ

/-! # A standard-Q matrix produces a simplex point with strictly positive image

Normalize the actual standard LCP solution at right-hand side minus one.
This is not homogeneous complementarity or `SingletonLCPFeasible`.
-/

noncomputable section

namespace Math.LinearProgramming

open GameTheory.Math.Probability
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Standard Q internally produces a simplex vector with strictly positive
matrix image. No zero-diagonal, reward, copositivity, or R₀ premise is needed. -/
theorem exists_simplex_positive_residual_of_standardQ
    (matrix : ι → ι → ℝ) (hQ : IsStandardQ matrix) :
    ∃ weight : Convexity.StdSimplex ℝ ι,
      ∀ receiver, 0 < singletonLCPResidual matrix weight receiver := by
  classical
  obtain ⟨unnormalized, hsolution⟩ := hQ (fun _ => -1)
  have hrow : ∀ receiver, 1 ≤ ∑ owner, unnormalized owner * matrix receiver owner := by
    intro receiver
    have hnonnegative := hsolution.residual_nonneg receiver
    dsimp [lcpResidual] at hnonnegative
    linarith
  have hpositiveWeight : ∃ owner, 0 < unnormalized owner := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ owner, unnormalized owner = 0 :=
      fun owner => le_antisymm (hnone owner) (hsolution.weight_nonneg owner)
    have hrowOne := hrow (Classical.arbitrary ι)
    simp [hzero] at hrowOne
    linarith
  obtain ⟨owner, howner⟩ := hpositiveWeight
  have hmass : 0 < ∑ index, unnormalized index :=
    Finset.sum_pos' (fun index _ => hsolution.weight_nonneg index)
      ⟨owner, Finset.mem_univ _, howner⟩
  have hsimplex : (fun index => unnormalized index / ∑ other, unnormalized other) ∈
      simplexWeights ι :=
    mem_simplexWeights.mpr
      ⟨fun index => div_nonneg (hsolution.weight_nonneg index) hmass.le,
        by rw [← Finset.sum_div]; exact div_self hmass.ne'⟩
  let weight : Convexity.StdSimplex ℝ ι :=
    ⟨Finsupp.equivFunOnFinite.symm
      (fun index => unnormalized index / ∑ other, unnormalized other),
      (mem_simplexWeights.mp hsimplex).1,
      (by rw [Finsupp.equivFunOnFinite_symm_sum]; exact (mem_simplexWeights.mp hsimplex).2)⟩
  have hresidual : ∀ receiver, singletonLCPResidual matrix weight receiver =
      (∑ index, unnormalized index * matrix receiver index) / ∑ index, unnormalized index := by
    intro receiver
    rw [singletonLCPResidual_eq]
    change (∑ index, (unnormalized index / ∑ other, unnormalized other) *
      matrix receiver index) = _
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun index _ => by ring
  refine ⟨weight, fun receiver => ?_⟩
  rw [hresidual receiver]
  exact div_pos (lt_of_lt_of_le zero_lt_one (hrow receiver)) hmass

/-- The packet's weak nonnegative-image simplex premise is produced by Q;
the strict image theorem above is stronger and remains separate from feasibility. -/
theorem exists_simplex_nonnegative_residual_of_standardQ
    (matrix : ι → ι → ℝ) (hQ : IsStandardQ matrix) :
    ∃ weight : Convexity.StdSimplex ℝ ι,
      ∀ receiver, 0 ≤ singletonLCPResidual matrix weight receiver := by
  obtain ⟨weight, hpositive⟩ := exists_simplex_positive_residual_of_standardQ matrix hQ
  exact ⟨weight, fun receiver => (hpositive receiver).le⟩

end Math.LinearProgramming
