import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CyclicChildSingletonAdapter
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.RawPassiveRowInverseCriterion

/-! # Actual cyclic-child passive inverse exit

The literal singleton rows determine the deleted child's matrix and the
exterior row. Canonical inverse algebra computes every outside weight; no
child strategy certificate or favorable inverse is a source hypothesis.
Unspecified terminal coalition entries remain arbitrary.
-/

noncomputable section

namespace GameTheory.CyclicChildSingleton

open QuittingLCPClassification Math.LinearProgramming
open _root_.Math.CyclicChildJointPhase
open Math.LinearProgramming.ThreeCycleInverseFormulas
open scoped Matrix

def deleted (who : Fin 4) : Prop := who = 0

instance : DecidablePred deleted := fun who => inferInstanceAs (Decidable (who = 0))

abbrev Child := {who : Fin 4 // ¬ deleted who}

def childEquiv : Fin 3 ≃ Child := finSuccAboveEquiv 0

@[simp] theorem childEquiv_val (who : Fin 3) : (childEquiv who).val = who.succ := by
  change (0 : Fin 4).succAbove who = who.succ
  exact congrFun Fin.succAbove_zero who

theorem deleted_childMatrix_eq {a b c h₁ h₂ h₃ u v R : ℝ} {reward : Reward}
    (hrows : RawRows a b c h₁ h₂ h₃ u v R reward) :
    (PassiveRowInverseCriterion.childMatrix reward deleted).submatrix childEquiv childEquiv =
      _root_.Math.CyclicChildJointPhase.childMatrix a b c := by
  ext who owner
  rw [Matrix.submatrix_apply, PassiveRowInverseCriterion.childMatrix, Matrix.of_apply,
    normalizedSoloMatrix_eq_soloReward_sub]
  change quittingSingletonMatrix reward (childEquiv who).val (childEquiv owner).val = _
  rw [singletonMatrix_eq hrows, childEquiv_val, childEquiv_val]
  fin_cases who <;> fin_cases owner <;>
    simp [exteriorMatrix, _root_.Math.CyclicChildJointPhase.childMatrix,
      Math.LinearProgramming.ThreeCycleInverseFormulas.directedCycleMatrix]

theorem deleted_outsideRow_eq {a b c h₁ h₂ h₃ u v R : ℝ} {reward : Reward}
    (hrows : RawRows a b c h₁ h₂ h₃ u v R reward) (who : Fin 3) :
    PassiveRowInverseCriterion.outsideRow reward deleted 0 (childEquiv who) =
      ![u - 1, v - 1, R - 1] who := by
  change quittingSingletonMatrix reward 0 (childEquiv who).val = _
  rw [singletonMatrix_eq hrows, childEquiv_val]
  fin_cases who <;> simp [exteriorMatrix]

def outsideInverseWeight (a b c u v R : ℝ) : Fin 3 → ℝ :=
  ![u - 1, v - 1, R - 1] ᵥ* (_root_.Math.CyclicChildJointPhase.childMatrix a b c)⁻¹

theorem outsideInverseWeight_eq (a b c u v R : ℝ) :
    outsideInverseWeight a b c u v R =
      ![(c * (u - 1) + (v - 1) + b * c * (R - 1)) / gap a b c,
        (a * c * (u - 1) + a * (v - 1) + (R - 1)) / gap a b c,
        ((u - 1) + a * b * (v - 1) + b * (R - 1)) / gap a b c] := by
  rw [outsideInverseWeight, childMatrix_inverse]
  ext who
  fin_cases who <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, div_eq_mul_inv] <;> ring

theorem deleted_inverseWeight_eq {a b c h₁ h₂ h₃ u v R : ℝ} {reward : Reward}
    (hrows : RawRows a b c h₁ h₂ h₃ u v R reward) (inside : Child) :
    PassiveRowInverseCriterion.inverseWeight reward deleted 0 inside =
      outsideInverseWeight a b c u v R (childEquiv.symm inside) := by
  let matrix := PassiveRowInverseCriterion.childMatrix reward deleted
  have hinverse := Matrix.inv_submatrix_equiv matrix childEquiv childEquiv
  rw [deleted_childMatrix_eq hrows] at hinverse
  have hentry (who : Fin 3) : matrix⁻¹ (childEquiv who) inside =
      (_root_.Math.CyclicChildJointPhase.childMatrix a b c)⁻¹ who
        (childEquiv.symm inside) := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      M who (childEquiv.symm inside)) hinverse
    simpa [Matrix.submatrix_apply] using h.symm
  rw [PassiveRowInverseCriterion.inverseWeight, outsideInverseWeight,
    Matrix.vecMul_apply_eq_sum, Matrix.vecMul_apply_eq_sum]
  rw [← childEquiv.sum_comp (fun who : Child =>
    PassiveRowInverseCriterion.outsideRow reward deleted 0 who * matrix⁻¹ who inside)]
  apply Finset.sum_congr rfl
  intro who _
  rw [deleted_outsideRow_eq hrows, hentry]

/-- Literal raw exterior numerator tests supply the computed inverse weights.
The child strategy and the original fixed target are selected internally. -/
theorem exists_uniformPayoff_of_passiveNumerators {a b c h₁ h₂ h₃ u v R : ℝ}
    {reward : Reward} (hrows : RawRows a b c h₁ h₂ h₃ u v R reward)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hgap : 0 < gap a b c)
    (hfirst : 0 ≤ c * (u - 1) + (v - 1) + b * c * (R - 1))
    (hsecond : 0 ≤ a * c * (u - 1) + a * (v - 1) + (R - 1))
    (hthird : 0 ≤ (u - 1) + a * b * (v - 1) + b * (R - 1)) :
    ∃ payoff : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hpositive := directedCycleMatrix_hasStrictlyPositiveInverse
      (by norm_num : (0 : ℝ) < 1) ha hb (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1) hc (by simpa [gap,
        Math.LinearProgramming.ThreeCycleInverseFormulas.cycleGap] using hgap)
  change HasStrictlyPositiveInverse (_root_.Math.CyclicChildJointPhase.childMatrix a b c)
    at hpositive
  have hdet : (PassiveRowInverseCriterion.childMatrix reward deleted).det ≠ 0 := by
    rw [← Matrix.det_submatrix_equiv_self childEquiv, deleted_childMatrix_eq hrows]
    exact hpositive.1
  have hinverse (row column : Child) :
      0 ≤ (PassiveRowInverseCriterion.childMatrix reward deleted)⁻¹ row column := by
    have h := Matrix.inv_submatrix_equiv
      (PassiveRowInverseCriterion.childMatrix reward deleted) childEquiv childEquiv
    rw [deleted_childMatrix_eq hrows] at h
    have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      M (childEquiv.symm row) (childEquiv.symm column)) h
    have hstrict := hpositive.2 (childEquiv.symm row) (childEquiv.symm column)
    rw [Matrix.submatrix_apply, childEquiv.apply_symm_apply,
      childEquiv.apply_symm_apply] at hentry
    rw [hentry] at hstrict
    exact hstrict.le
  have houtside (outside : Fin 4) (houtside : deleted outside) (inside : Child) :
      0 ≤ PassiveRowInverseCriterion.inverseWeight reward deleted outside inside := by
    have heq : outside = 0 := houtside
    subst outside
    rw [deleted_inverseWeight_eq hrows, outsideInverseWeight_eq]
    generalize childEquiv.symm inside = who
    fin_cases who <;> dsimp only
    · exact div_nonneg hfirst hgap.le
    · exact div_nonneg hsecond hgap.le
    · exact div_nonneg hthird hgap.le
  have hcard : Fintype.card Child = 3 := Fintype.card_congr childEquiv.symm
  exact PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple
    reward deleted hcard hdet hinverse houtside

def passiveThresholdFirst (b c u v : ℝ) : ℝ :=
  1 - (c * (u - 1) + (v - 1)) / (b * c)

def passiveThresholdSecond (a c u v : ℝ) : ℝ :=
  1 - a * c * (u - 1) - a * (v - 1)

def passiveThresholdThird (a b u v : ℝ) : ℝ :=
  1 - ((u - 1) + a * b * (v - 1)) / b

def passiveThreshold (a b c u v : ℝ) : ℝ :=
  max (passiveThresholdFirst b c u v)
    (max (passiveThresholdSecond a c u v) (passiveThresholdThird a b u v))

/-- The general high exit retains all three raw exterior thresholds. -/
theorem exists_uniformPayoff_of_passiveThreshold {a b c h₁ h₂ h₃ u v R : ℝ}
    {reward : Reward} (hrows : RawRows a b c h₁ h₂ h₃ u v R reward)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hgap : 0 < gap a b c)
    (hR : passiveThreshold a b c u v ≤ R) :
    ∃ payoff : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hR₁ : passiveThresholdFirst b c u v ≤ R := (le_max_left _ _).trans hR
  have hR₂ : passiveThresholdSecond a c u v ≤ R :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hR₃ : passiveThresholdThird a b u v ≤ R :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  apply exists_uniformPayoff_of_passiveNumerators hrows ha hb hc hgap
  · have heq : c * (u - 1) + (v - 1) + b * c * (R - 1) =
        (b * c) * (R - passiveThresholdFirst b c u v) := by
      unfold passiveThresholdFirst
      field_simp [hb.ne', hc.ne']
      ring
    rw [heq]
    exact mul_nonneg (mul_pos hb hc).le (sub_nonneg.mpr hR₁)
  · have heq : a * c * (u - 1) + a * (v - 1) + (R - 1) =
        R - passiveThresholdSecond a c u v := by
      unfold passiveThresholdSecond
      ring
    rw [heq]
    exact sub_nonneg.mpr hR₂
  · have heq : (u - 1) + a * b * (v - 1) + b * (R - 1) =
        b * (R - passiveThresholdThird a b u v) := by
      unfold passiveThresholdThird
      field_simp [hb.ne']
      ring
    rw [heq]
    exact mul_nonneg hb.le (sub_nonneg.mpr hR₃)

theorem passiveThresholdFirst_lt_third {a b c : ℝ} (u : ℝ) {v : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hgap : 0 < gap a b c) (hv : v < 1) :
    passiveThresholdFirst b c u v < passiveThresholdThird a b u v := by
  have heq : passiveThresholdThird a b u v - passiveThresholdFirst b c u v =
      gap a b c * (1 - v) / (b * c) := by
    unfold passiveThresholdThird passiveThresholdFirst gap
    field_simp [hb.ne', hc.ne']
    ring
  apply sub_pos.mp
  rw [heq]
  exact div_pos (mul_pos hgap (sub_pos.mpr hv)) (mul_pos hb hc)

/-- The one-joint packet's two-threshold bound is sufficient, including equality. -/
theorem exists_uniformPayoff_of_twoPassiveThresholds {a b c h₁ h₂ h₃ u v R : ℝ}
    {reward : Reward} (hrows : RawRows a b c h₁ h₂ h₃ u v R reward)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hgap : 0 < gap a b c) (hv : v < 1)
    (hR : max (passiveThresholdSecond a c u v) (passiveThresholdThird a b u v) ≤ R) :
    ∃ payoff : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformPayoff_of_passiveThreshold hrows ha hb hc hgap
  apply max_le
  · exact (passiveThresholdFirst_lt_third u hb hc hgap hv).le.trans
      ((le_max_right _ _).trans hR)
  · exact hR

/-- For exterior singleton values at least one, every nonnegative exterior
row at pivot value at least one passes the same internally computed test. -/
theorem exists_uniformPayoff_of_exterior_at_least_one {a b c h₁ h₂ h₃ u v R : ℝ}
    {reward : Reward} (hrows : RawRows a b c h₁ h₂ h₃ u v R reward)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hgap : 0 < gap a b c)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hR : 1 ≤ R) :
    ∃ payoff : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hu' := sub_nonneg.mpr hu
  have hv' := sub_nonneg.mpr hv
  have hR' := sub_nonneg.mpr hR
  apply exists_uniformPayoff_of_passiveNumerators hrows ha hb hc hgap
  · exact add_nonneg (add_nonneg (mul_nonneg hc.le hu') hv')
      (mul_nonneg (mul_pos hb hc).le hR')
  · exact add_nonneg (add_nonneg (mul_nonneg (mul_pos ha hc).le hu')
      (mul_nonneg ha.le hv')) hR'
  · exact add_nonneg (add_nonneg hu' (mul_nonneg (mul_pos ha hb).le hv'))
      (mul_nonneg hb.le hR')

end GameTheory.CyclicChildSingleton
