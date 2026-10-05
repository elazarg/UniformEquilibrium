import MathUE.CubicAnchorRoot
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.QuadraticDiscriminant

/-! # Rationalized quadratic selection across every leading-coefficient sign

Opposite bracket signs select the unique interior root and its positive
derivative, without monotonicity on the whole bracket. The rationalized
formula stays meaningful through the linear case and zero endpoint roots.
-/

noncomputable section

namespace Math

/-- The same expression covers genuine quadratics and linear polynomials. -/
def quadraticBracketValue (leading linear constant point : ℝ) : ℝ :=
  leading * point ^ 2 + linear * point + constant

/-- Rationalized positive-crossing root, avoiding division by the leading
coefficient. Its denominator hypotheses are supplied by the bracket theorem. -/
def rationalizedQuadraticRoot (leading linear constant : ℝ) : ℝ :=
  -2 * constant / (linear + Real.sqrt (discrim leading linear constant))

theorem quadraticBracketRoot_derivative_pos
    {leading linear constant cap root : ℝ}
    (hconstant : constant < 0) (hcap : 0 < quadraticBracketValue leading linear constant cap)
    (hroot : root ∈ Set.Ioo (0 : ℝ) cap)
    (hzero : quadraticBracketValue leading linear constant root = 0) :
    0 < 2 * leading * root + linear := by
  have hrootPos := hroot.1
  have hgap : 0 < cap - root := sub_pos.mpr hroot.2
  have hrootPolynomial : leading * root ^ 2 + linear * root + constant = 0 := hzero
  have hrootFactor : 0 < leading * root + linear := by
    have hproduct : 0 < root * (leading * root + linear) := by
      nlinarith only [hrootPolynomial, hconstant]
    exact pos_of_mul_pos_right hproduct hrootPos.le
  have hcapFactor : 0 < leading * (cap + root) + linear := by
    have hidentity : quadraticBracketValue leading linear constant cap =
        (cap - root) * (leading * (cap + root) + linear) := by
      unfold quadraticBracketValue at *
      nlinarith only [hrootPolynomial]
    rw [hidentity] at hcap
    exact pos_of_mul_pos_right hcap hgap.le
  by_cases hleading : leading < 0
  · have hnegative := mul_neg_of_neg_of_pos hleading hgap
    nlinarith only [hcapFactor, hnegative]
  · have hnonnegative := mul_nonneg (le_of_not_gt hleading) hrootPos.le
    linarith

theorem exists_quadraticBracketRoot
    {leading linear constant cap : ℝ} (hconstant : constant < 0) (hcapPos : 0 < cap)
    (hcap : 0 < quadraticBracketValue leading linear constant cap) :
    ∃ root ∈ Set.Ioo (0 : ℝ) cap,
      quadraticBracketValue leading linear constant root = 0 := by
  obtain ⟨rate, hrate, hzero⟩ := exists_quadratic_root_mem_Ioo
    (a := constant) (b := linear * cap) (c := leading * cap ^ 2) hconstant
    (by unfold quadraticBracketValue at hcap; linarith)
  refine ⟨cap * rate, ⟨mul_pos hcapPos hrate.1, ?_⟩, ?_⟩
  · nlinarith only [mul_pos hcapPos (sub_pos.mpr hrate.2)]
  · unfold quadraticBracketValue
    nlinarith only [hzero]

theorem quadraticBracketRoot_unique
    {leading linear constant cap first second : ℝ}
    (hconstant : constant < 0) (hcap : 0 < quadraticBracketValue leading linear constant cap)
    (hfirst : first ∈ Set.Ioo (0 : ℝ) cap)
    (hfirstZero : quadraticBracketValue leading linear constant first = 0)
    (hsecond : second ∈ Set.Ioo (0 : ℝ) cap)
    (hsecondZero : quadraticBracketValue leading linear constant second = 0) :
    first = second := by
  have hfirstDerivative := quadraticBracketRoot_derivative_pos hconstant hcap hfirst hfirstZero
  have hsecondDerivative :=
    quadraticBracketRoot_derivative_pos hconstant hcap hsecond hsecondZero
  have hfactor : (first - second) * (leading * (first + second) + linear) = 0 := by
    unfold quadraticBracketValue at *
    nlinarith only [hfirstZero, hsecondZero]
  rcases mul_eq_zero.mp hfactor with heq | heq
  · exact sub_eq_zero.mp heq
  · linarith

/-- Literal formula, interior bracket, simple positive-crossing derivative,
and uniqueness, for negative, zero, or positive leading coefficient. -/
theorem rationalizedQuadraticRoot_spec
    {leading linear constant cap : ℝ} (hconstant : constant < 0) (hcapPos : 0 < cap)
    (hcap : 0 < quadraticBracketValue leading linear constant cap) :
    0 < discrim leading linear constant ∧
      0 < linear + Real.sqrt (discrim leading linear constant) ∧
      rationalizedQuadraticRoot leading linear constant ∈ Set.Ioo (0 : ℝ) cap ∧
      quadraticBracketValue leading linear constant
        (rationalizedQuadraticRoot leading linear constant) = 0 ∧
      0 < 2 * leading * rationalizedQuadraticRoot leading linear constant + linear ∧
      ∀ root ∈ Set.Ioo (0 : ℝ) cap,
        quadraticBracketValue leading linear constant root = 0 →
          root = rationalizedQuadraticRoot leading linear constant := by
  obtain ⟨root, hroot, hzero⟩ := exists_quadraticBracketRoot hconstant hcapPos hcap
  have hderivative := quadraticBracketRoot_derivative_pos hconstant hcap hroot hzero
  have hdiscriminant : discrim leading linear constant = (2 * leading * root + linear) ^ 2 := by
    apply discrim_eq_sq_of_quadratic_eq_zero
    simpa only [quadraticBracketValue, sq] using hzero
  have hdiscriminantPos : 0 < discrim leading linear constant := by
    rw [hdiscriminant]
    exact sq_pos_of_pos hderivative
  have hsqrt : Real.sqrt (discrim leading linear constant) =
      2 * leading * root + linear := by
    rw [hdiscriminant, Real.sqrt_sq_eq_abs, abs_of_pos hderivative]
  have hproduct : (linear + Real.sqrt (discrim leading linear constant)) * root =
      -2 * constant := by
    rw [hsqrt]
    unfold quadraticBracketValue at hzero
    nlinarith only [hzero]
  have hdenominator : 0 < linear + Real.sqrt (discrim leading linear constant) := by
    have hpositive : 0 <
        (linear + Real.sqrt (discrim leading linear constant)) * root := by
      rw [hproduct]
      linarith
    exact pos_of_mul_pos_left hpositive hroot.1.le
  have hformula : rationalizedQuadraticRoot leading linear constant = root := by
    unfold rationalizedQuadraticRoot
    apply (div_eq_iff (ne_of_gt hdenominator)).mpr
    simpa only [mul_comm] using hproduct.symm
  refine ⟨hdiscriminantPos, hdenominator, hformula.symm ▸ hroot,
    hformula.symm ▸ hzero, hformula.symm ▸ hderivative, ?_⟩
  intro other hother hotherZero
  rw [hformula]
  exact quadraticBracketRoot_unique hconstant hcap hother hotherZero hroot hzero

/-- At the linear coefficient boundary, the same selector is the linear root. -/
theorem rationalizedQuadraticRoot_leading_zero
    (linear constant : ℝ) (hlinear : 0 < linear) :
    rationalizedQuadraticRoot 0 linear constant = -constant / linear := by
  unfold rationalizedQuadraticRoot discrim
  simp only [mul_zero, zero_mul, sub_zero]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hlinear]
  field_simp [ne_of_gt hlinear]
  ring

/-- Every zero constant endpoint has zero selected value. Continuity at that
endpoint separately requires a nonzero denominator. -/
theorem rationalizedQuadraticRoot_constant_zero (leading linear : ℝ) :
    rationalizedQuadraticRoot leading linear 0 = 0 := by
  simp [rationalizedQuadraticRoot]

/-- Coefficient continuity is enough across the leading-coefficient boundary;
the formula never divides by that coefficient. -/
theorem continuousOn_rationalizedQuadraticRoot
    {X : Type*} [TopologicalSpace X] (region : Set X)
    (leading linear constant : X → ℝ)
    (hleading : ContinuousOn leading region) (hlinear : ContinuousOn linear region)
    (hconstant : ContinuousOn constant region)
    (hdenominator : ∀ point ∈ region,
      linear point + Real.sqrt (discrim (leading point) (linear point) (constant point)) ≠ 0) :
    ContinuousOn (fun point =>
      rationalizedQuadraticRoot (leading point) (linear point) (constant point)) region := by
  unfold rationalizedQuadraticRoot discrim at *
  apply ContinuousOn.div
  · exact continuousOn_const.mul hconstant
  · exact hlinear.add ((hlinear.pow 2).sub
      ((continuousOn_const.mul hleading).mul hconstant)).sqrt
  · exact hdenominator

/-- Positive linear coefficients supply the nonvanishing denominator needed
for coefficient continuity, without a leading-coefficient sign restriction. -/
theorem continuousOn_rationalizedQuadraticRoot_of_linear_pos
    {X : Type*} [TopologicalSpace X] (region : Set X)
    (leading linear constant : X → ℝ)
    (hleading : ContinuousOn leading region) (hlinear : ContinuousOn linear region)
    (hconstant : ContinuousOn constant region)
    (hpositive : ∀ point ∈ region, 0 < linear point) :
    ContinuousOn (fun point =>
      rationalizedQuadraticRoot (leading point) (linear point) (constant point)) region := by
  apply continuousOn_rationalizedQuadraticRoot region leading linear constant
    hleading hlinear hconstant
  intro point hpoint
  exact ne_of_gt ((hpositive point hpoint).trans_le
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)))

/-- Interior bracket signs and positive endpoint linear coefficients produce
one continuous closed-interval selector, including both zero endpoint values.
No root-selection witness or sign of the leading coefficient is supplied. -/
theorem rationalizedQuadraticRoot_closedInterval
    (left right : ℝ) (leading linear constant cap : ℝ → ℝ)
    (hleading : ContinuousOn leading (Set.Icc left right))
    (hlinear : ContinuousOn linear (Set.Icc left right))
    (hconstant : ContinuousOn constant (Set.Icc left right))
    (hleft : constant left = 0) (hright : constant right = 0)
    (hleftLinear : 0 < linear left) (hrightLinear : 0 < linear right)
    (hnegative : ∀ point ∈ Set.Ioo left right, constant point < 0)
    (hcapPositive : ∀ point ∈ Set.Ioo left right, 0 < cap point)
    (hcap : ∀ point ∈ Set.Ioo left right,
      0 < quadraticBracketValue (leading point) (linear point) (constant point) (cap point)) :
    ContinuousOn (fun point =>
      rationalizedQuadraticRoot (leading point) (linear point) (constant point))
        (Set.Icc left right) ∧
      rationalizedQuadraticRoot (leading left) (linear left) (constant left) = 0 ∧
      rationalizedQuadraticRoot (leading right) (linear right) (constant right) = 0 ∧
      ∀ point ∈ Set.Ioo left right,
        rationalizedQuadraticRoot (leading point) (linear point) (constant point) ∈
            Set.Ioo (0 : ℝ) (cap point) ∧
          quadraticBracketValue (leading point) (linear point) (constant point)
            (rationalizedQuadraticRoot (leading point) (linear point) (constant point)) = 0 ∧
          0 < 2 * leading point *
            rationalizedQuadraticRoot (leading point) (linear point) (constant point) +
              linear point ∧
          ∀ root ∈ Set.Ioo (0 : ℝ) (cap point),
            quadraticBracketValue (leading point) (linear point) (constant point) root = 0 →
              root = rationalizedQuadraticRoot (leading point) (linear point) (constant point) := by
  have hdenominator : ∀ point ∈ Set.Icc left right,
      linear point + Real.sqrt (discrim (leading point) (linear point) (constant point)) ≠ 0 := by
    intro point hpoint
    by_cases hpointLeft : point = left
    · subst point
      exact ne_of_gt (hleftLinear.trans_le (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
    · by_cases hpointRight : point = right
      · subst point
        exact ne_of_gt (hrightLinear.trans_le (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
      · have hinterior : point ∈ Set.Ioo left right :=
          ⟨lt_of_le_of_ne hpoint.1 (Ne.symm hpointLeft),
            lt_of_le_of_ne hpoint.2 hpointRight⟩
        exact ne_of_gt (rationalizedQuadraticRoot_spec
          (hnegative point hinterior) (hcapPositive point hinterior) (hcap point hinterior)).2.1
  refine ⟨continuousOn_rationalizedQuadraticRoot (Set.Icc left right) leading linear constant
    hleading hlinear hconstant hdenominator, ?_, ?_, ?_⟩
  · rw [hleft]
    exact rationalizedQuadraticRoot_constant_zero _ _
  · rw [hright]
    exact rationalizedQuadraticRoot_constant_zero _ _
  · intro point hpoint
    exact (rationalizedQuadraticRoot_spec (hnegative point hpoint)
      (hcapPositive point hpoint) (hcap point hpoint)).2.2

end Math
