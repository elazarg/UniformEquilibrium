import MathUE.LinearProgramming.PositiveInverseOpenness

/-!
# Inverse formulas for a strict three-cycle matrix

The canonical six-parameter matrix and its determinant retain the ordering
used by the three-dimensional zero-diagonal Q classification. The explicit
inverse and its column weights are finite linear algebra. No assertion about
the blocks or vertex visits of an actual quitting schedule is made here.
-/

noncomputable section

namespace Math.LinearProgramming.ThreeCycleInverseFormulas

/-- Six magnitudes in one directed-cycle orientation. -/
def directedCycleMatrix (a b c d e f : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun who owner =>
    if who = 0 then
      if owner = 0 then 0 else if owner = 1 then -a else b
    else if who = 1 then
      if owner = 0 then c else if owner = 1 then 0 else -d
    else
      if owner = 0 then -e else if owner = 1 then f else 0

/-- The positive-cycle product minus the negative-cycle product. -/
def cycleGap (a b c d e f : ℝ) : ℝ := b * c * f - a * d * e

theorem directedCycleMatrix_det (a b c d e f : ℝ) :
    (directedCycleMatrix a b c d e f).det = cycleGap a b c d e f := by
  simp [Matrix.det_fin_three, directedCycleMatrix, cycleGap]
  ring

/-- The actual inverse formula also respects the zero inverse convention
when the determinant vanishes. -/
theorem directedCycleMatrix_inverse (a b c d e f : ℝ) :
    (directedCycleMatrix a b c d e f)⁻¹ =
      (cycleGap a b c d e f)⁻¹ •
        !![d * f, b * f, a * d; d * e, b * e, b * c; c * f, a * e, a * c] := by
  rw [Matrix.inv_def, directedCycleMatrix_det, Ring.inverse_eq_inv']
  congr 1
  rw [Matrix.adjugate_fin_three]
  ext row column
  fin_cases row <;> fin_cases column <;> simp [directedCycleMatrix]

/-- Every entry of the inverse is positive in the strict product-gap chamber. -/
theorem directedCycleMatrix_inverse_pos
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f) (row column : Fin 3) :
    0 < (directedCycleMatrix a b c d e f)⁻¹ row column := by
  rw [directedCycleMatrix_inverse]
  fin_cases row <;> fin_cases column <;> norm_num <;> positivity

theorem directedCycleMatrix_hasStrictlyPositiveInverse
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f) :
    HasStrictlyPositiveInverse (directedCycleMatrix a b c d e f) := by
  refine ⟨?_, directedCycleMatrix_inverse_pos ha hb hc hd he hf hgap⟩
  rw [directedCycleMatrix_det]
  exact hgap.ne'

/-- Column sums of the actual inverse, viewed as a row vector. -/
def columnWeight (a b c d e f : ℝ) : Fin 3 → ℝ :=
  Matrix.vecMul (1 : Fin 3 → ℝ) (directedCycleMatrix a b c d e f)⁻¹

theorem columnWeight_eq_sum (a b c d e f : ℝ) (column : Fin 3) :
    columnWeight a b c d e f column =
      ∑ row, (directedCycleMatrix a b c d e f)⁻¹ row column := by
  simp [columnWeight, Matrix.vecMul, dotProduct]

theorem columnWeight_pos
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f) (column : Fin 3) :
    0 < columnWeight a b c d e f column := by
  rw [columnWeight_eq_sum]
  exact Finset.sum_pos
    (fun row _ => directedCycleMatrix_inverse_pos ha hb hc hd he hf hgap row column)
    Finset.univ_nonempty

/-- The column-weight row times the original matrix is the all-ones row. -/
theorem columnWeight_vecMul (a b c d e f : ℝ)
    (hgap : cycleGap a b c d e f ≠ 0) :
    Matrix.vecMul (columnWeight a b c d e f) (directedCycleMatrix a b c d e f) = 1 := by
  have hdet : IsUnit (directedCycleMatrix a b c d e f).det := by
    rw [isUnit_iff_ne_zero, directedCycleMatrix_det]
    exact hgap
  rw [columnWeight, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet,
    Matrix.vecMul_one]

/-- The three scalar balances used to normalize the source's arc fractions. -/
theorem columnWeight_balances (a b c d e f : ℝ)
    (hgap : cycleGap a b c d e f ≠ 0) :
    let h := columnWeight a b c d e f
    c * h 1 - e * h 2 = 1 ∧
      f * h 2 - a * h 0 = 1 ∧
      b * h 0 - d * h 1 = 1 := by
  have hzero := congrFun (columnWeight_vecMul a b c d e f hgap) 0
  have hone := congrFun (columnWeight_vecMul a b c d e f hgap) 1
  have htwo := congrFun (columnWeight_vecMul a b c d e f hgap) 2
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, directedCycleMatrix]
    at hzero hone htwo
  dsimp only
  constructor
  · nlinarith [hzero]
  constructor
  · nlinarith [hone]
  · nlinarith [htwo]

/-- The source's candidate absorption fractions, indexed by the block owner.
Identifying them with an actual schedule requires a separate block argument. -/
def absorptionFraction (a b c d e f : ℝ) : Fin 3 → ℝ :=
  let h := columnWeight a b c d e f
  ![1 / (c * h 1), 1 / (f * h 2), 1 / (b * h 0)]

/-- The source's candidate survival fractions, with the same owner indexing. -/
def survivalFraction (a b c d e f : ℝ) : Fin 3 → ℝ :=
  let h := columnWeight a b c d e f
  ![(e * h 2) / (c * h 1), (a * h 0) / (f * h 2), (d * h 1) / (b * h 0)]

private theorem fractions_of_balance {denominator numerator : ℝ}
    (hnum : 0 < numerator) (hbalance : denominator - numerator = 1) :
    0 < 1 / denominator ∧ 1 / denominator < 1 ∧
      0 < numerator / denominator ∧ numerator / denominator < 1 ∧
      1 / denominator + numerator / denominator = 1 := by
  have hden : 0 < denominator := by linarith
  refine ⟨by positivity, (div_lt_one hden).mpr (by linarith),
    div_pos hnum hden, (div_lt_one hden).mpr (by linarith), ?_⟩
  rw [← add_div]
  apply (div_eq_one_iff_eq hden.ne').mpr
  linarith

/-- Each algebraic absorption/survival pair lies strictly inside the unit
interval and sums to one. -/
theorem fractions_pos_lt_one_add_eq_one
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f) (owner : Fin 3) :
    0 < absorptionFraction a b c d e f owner ∧
      absorptionFraction a b c d e f owner < 1 ∧
      0 < survivalFraction a b c d e f owner ∧
      survivalFraction a b c d e f owner < 1 ∧
      absorptionFraction a b c d e f owner + survivalFraction a b c d e f owner = 1 := by
  have hweight := columnWeight_pos ha hb hc hd he hf hgap
  obtain ⟨hzero, hone, htwo⟩ := columnWeight_balances a b c d e f hgap.ne'
  fin_cases owner
  · exact fractions_of_balance (mul_pos he (hweight 2)) hzero
  · exact fractions_of_balance (mul_pos ha (hweight 0)) hone
  · exact fractions_of_balance (mul_pos hd (hweight 1)) htwo

/-- The three algebraic survival fractions multiply to the ratio of the
negative-cycle product to the positive-cycle product. -/
theorem prod_survivalFraction
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f) :
    ∏ owner, survivalFraction a b c d e f owner = a * d * e / (b * c * f) := by
  have hzero := (columnWeight_pos ha hb hc hd he hf hgap 0).ne'
  have hone := (columnWeight_pos ha hb hc hd he hf hgap 1).ne'
  have htwo := (columnWeight_pos ha hb hc hd he hf hgap 2).ne'
  simp only [survivalFraction, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change
    (e * columnWeight a b c d e f 2) / (c * columnWeight a b c d e f 1) *
      ((a * columnWeight a b c d e f 0) / (f * columnWeight a b c d e f 2) *
        ((d * columnWeight a b c d e f 1) / (b * columnWeight a b c d e f 0))) =
      a * d * e / (b * c * f)
  field_simp [hzero, hone, htwo]

/-- The cycle product ratio is a strict contraction in the product-gap chamber. -/
theorem cycle_productRatio_mem_Ioo
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f) :
    a * d * e / (b * c * f) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hden : 0 < b * c * f := by positivity
  refine ⟨by positivity, (div_lt_one hden).mpr ?_⟩
  dsimp [cycleGap] at hgap
  linarith

end Math.LinearProgramming.ThreeCycleInverseFormulas
