import MathUE.LinearProgramming.CopositiveQ

/-! # Canonical projectivization of standard LCP solutions

The weight sum is normalized by one plus its total mass. The resulting cemetery
coefficient is strictly positive before any compact limit is taken.
-/

noncomputable section

namespace Math.LinearProgramming

open scoped BigOperators

variable {ι : Type} [Fintype ι]

/-- A solution of the normalized simplex/projective LCP
`w = z₀ q + Mz`, with `z₀ + ∑ zᵢ = 1`. -/
structure ProjectiveLCPSolution (M : ι → ι → ℝ) (q : ι → ℝ) where
  cemetery : ℝ
  singleton : ι → ℝ
  cemetery_nonneg : 0 ≤ cemetery
  singleton_nonneg : ∀ i, 0 ≤ singleton i
  total : cemetery + ∑ i, singleton i = 1
  residual_nonneg : ∀ i,
    0 ≤ cemetery * q i + ∑ j, singleton j * M i j
  complementary : ∀ i,
    singleton i * (cemetery * q i + ∑ j, singleton j * M i j) = 0

private theorem sum_weight_nonneg
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    0 ≤ ∑ i, weight i :=
  Finset.sum_nonneg fun i _ => hweight i

/-- Normalize a standard LCP solution into a projective one with positive
cemetery coefficient. -/
def projectivizeStandardLCPSolution
    {M : ι → ι → ℝ} {q z : ι → ℝ}
    (solution : IsStandardLCPSolution M q z) : ProjectiveLCPSolution M q := by
  classical
  let mass : ℝ := 1 + ∑ i, z i
  have hsum : 0 ≤ ∑ i, z i :=
    sum_weight_nonneg z solution.weight_nonneg
  have hmass : 0 < mass := by
    dsimp [mass]
    linarith
  have hmass0 : mass ≠ 0 := ne_of_gt hmass
  refine
    { cemetery := mass⁻¹
      singleton := fun i => z i * mass⁻¹
      cemetery_nonneg := inv_nonneg.mpr hmass.le
      singleton_nonneg := fun i =>
        mul_nonneg (solution.weight_nonneg i) (inv_nonneg.mpr hmass.le)
      total := ?_
      residual_nonneg := ?_
      complementary := ?_ }
  · rw [← Finset.sum_mul]
    calc
      mass⁻¹ + (∑ i, z i) * mass⁻¹ =
          (1 + ∑ i, z i) * mass⁻¹ := by ring
      _ = mass * mass⁻¹ := by rfl
      _ = 1 := mul_inv_cancel₀ hmass0
  · intro i
    have heq :
        mass⁻¹ * q i +
            ∑ j, (z j * mass⁻¹) * M i j =
          mass⁻¹ * (q i + ∑ j, z j * M i j) := by
      rw [mul_add, Finset.mul_sum]
      apply congrArg (fun x => mass⁻¹ * q i + x)
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [heq]
    exact mul_nonneg (inv_nonneg.mpr hmass.le)
      (solution.residual_nonneg i)
  · intro i
    have heq :
        mass⁻¹ * q i +
            ∑ j, (z j * mass⁻¹) * M i j =
          mass⁻¹ * (q i + ∑ j, z j * M i j) := by
      rw [mul_add, Finset.mul_sum]
      apply congrArg (fun x => mass⁻¹ * q i + x)
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [heq]
    calc
      (z i * mass⁻¹) *
          (mass⁻¹ * (q i + ∑ j, z j * M i j)) =
          mass⁻¹ ^ 2 *
            (z i *
              (q i + ∑ j, z j * M i j)) := by ring
      _ = 0 := by
        have hcomplementary : z i * (q i + ∑ j, z j * M i j) = 0 :=
          solution.complementary i
        rw [hcomplementary, mul_zero]

/-- The cemetery coefficient of an actual standard solution is strictly positive. -/
theorem projectivizeStandardLCPSolution_cemetery_pos
    {matrix : ι → ι → ℝ} {offset weight : ι → ℝ}
    (solution : IsStandardLCPSolution matrix offset weight) :
    0 < (projectivizeStandardLCPSolution solution).cemetery := by
  change 0 < (1 + ∑ who, weight who)⁻¹
  have hsum : 0 ≤ ∑ who, weight who :=
    Finset.sum_nonneg fun who _ => solution.weight_nonneg who
  positivity

end Math.LinearProgramming
