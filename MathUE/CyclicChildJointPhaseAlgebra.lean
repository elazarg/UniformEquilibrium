import MathUE.LinearProgramming.ThreeCycleInverseFormulas
import MathUE.RationalizedQuadraticBracketRoot

/-! # Actual cyclic-child balance and joint-phase scalar algebra

The child inverse determines the positive balance vector from the raw positive
reward magnitudes. The joint-phase scalar producer uses these same parameters;
no favorable inverse weights, root or continuation path is supplied.
-/

noncomputable section

namespace Math.CyclicChildJointPhase

open Math.LinearProgramming.ThreeCycleInverseFormulas
open scoped Matrix

/-- The actual receiver-first child singleton matrix. -/
def childMatrix (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  directedCycleMatrix 1 a b 1 1 c

/-- Positive-cycle excess, with the negative edges normalized to one. -/
def gap (a b c : ℝ) : ℝ := a * b * c - 1

theorem childMatrix_det (a b c : ℝ) : (childMatrix a b c).det = gap a b c := by
  rw [childMatrix, directedCycleMatrix_det]
  simp [cycleGap, gap]

theorem childMatrix_inverse (a b c : ℝ) :
    (childMatrix a b c)⁻¹ = (gap a b c)⁻¹ •
      !![c, a * c, 1; 1, a, a * b; b * c, 1, b] := by
  rw [childMatrix, directedCycleMatrix_inverse]
  simp [cycleGap, gap]

/-- The balance vector is computed by the actual child inverse. -/
def balanceVector (a b c h₁ h₂ h₃ : ℝ) : Fin 3 → ℝ :=
  (childMatrix a b c)⁻¹ *ᵥ ![h₁, h₂, h₃]

/-- Literal packet formula, retaining receiver-first indexing. -/
theorem balanceVector_eq (a b c h₁ h₂ h₃ : ℝ) :
    balanceVector a b c h₁ h₂ h₃ =
      ![(a * c * h₂ + c * h₁ + h₃) / gap a b c,
        (a * b * h₃ + a * h₂ + h₁) / gap a b c,
        (b * c * h₁ + b * h₃ + h₂) / gap a b c] := by
  rw [balanceVector, childMatrix_inverse]
  ext who
  fin_cases who <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, div_eq_mul_inv] <;> ring

theorem balanceVector_pos
    {a b c h₁ h₂ h₃ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h₁pos : 0 < h₁) (h₂pos : 0 < h₂) (h₃pos : 0 < h₃)
    (hgap : 0 < gap a b c) (who : Fin 3) :
    0 < balanceVector a b c h₁ h₂ h₃ who := by
  rw [balanceVector_eq]
  fin_cases who <;> dsimp only <;> apply div_pos _ hgap <;> positivity

/-- Invertibility, not a supplied balance certificate, produces the source
equation for every raw right-hand side. -/
theorem childMatrix_mulVec_balanceVector
    (a b c h₁ h₂ h₃ : ℝ) (hgap : gap a b c ≠ 0) :
    childMatrix a b c *ᵥ balanceVector a b c h₁ h₂ h₃ = ![h₁, h₂, h₃] := by
  have hunit : IsUnit (childMatrix a b c).det := by
    rw [childMatrix_det]
    exact isUnit_iff_ne_zero.mpr hgap
  rw [balanceVector, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
    Matrix.one_mulVec]

theorem balanceVector_balances
    (a b c h₁ h₂ h₃ : ℝ) (hgap : gap a b c ≠ 0) :
    let ν := balanceVector a b c h₁ h₂ h₃
    a * ν 2 - ν 1 = h₁ ∧ b * ν 0 - ν 2 = h₂ ∧ c * ν 1 - ν 0 = h₃ := by
  have heq := childMatrix_mulVec_balanceVector a b c h₁ h₂ h₃ hgap
  have hzero := congrFun heq 0
  have hone := congrFun heq 1
  have htwo := congrFun heq 2
  simp [childMatrix, directedCycleMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at hzero hone htwo
  dsimp only
  constructor
  · linarith
  constructor <;> linarith

/-- Upper joint hazard in the packet's closed selection interval. -/
def jointHazardCap (a b c : ℝ) : ℝ := gap a b c / (b * (a * c + a + 1))

theorem jointHazardCap_bounds {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hgap : 0 < gap a b c) :
    0 < jointHazardCap a b c ∧ jointHazardCap a b c < c / (c + 1) ∧
      jointHazardCap a b c < 1 := by
  have hden : 0 < b * (a * c + a + 1) := by positivity
  have hc1 : 0 < c + 1 := by positivity
  unfold jointHazardCap
  refine ⟨div_pos hgap hden, ?_, ?_⟩
  · apply (div_lt_div_iff₀ hden hc1).mpr
    unfold gap
    nlinarith only [mul_pos hb hc, hc]
  · apply (div_lt_one hden).mpr
    unfold gap
    nlinarith only [mul_pos ha hb, hb]

/-- Actual nonpivot loss after mixing the pivot singleton and joint row. -/
def jointLoss (harm collision hazard : ℝ) : ℝ :=
  harm * (1 - hazard) - collision * hazard

theorem jointLoss_pos {harm collision hazard : ℝ}
    (hharm : 0 < harm) (hcollision : collision ≤ 0)
    (hhazard : hazard ∈ Set.Ico (0 : ℝ) 1) :
    0 < jointLoss harm collision hazard := by
  have hfirst := mul_pos hharm (sub_pos.mpr hhazard.2)
  have hsecond := mul_nonpos_of_nonpos_of_nonneg hcollision hhazard.1
  unfold jointLoss
  linarith

/-- The admissible root bracket is computed from the raw nonpivot losses. -/
def balanceCap (b c H₂ H₃ y : ℝ) : ℝ :=
  min (b * y / H₂) ((c - (c + 1) * y) / H₃)

def soloSecondHazard (c H₃ k y : ℝ) : ℝ := (H₃ * k + y) / (c * (1 - y))

def balanceDenominator (b H₂ k y : ℝ) : ℝ := 1 + b * y + (1 - H₂) * k

def soloThirdHazard (b H₂ k y : ℝ) : ℝ :=
  (b * y - H₂ * k) / balanceDenominator b H₂ k y

/-- All rates and denominators are produced on the computed closed bracket,
with strict rates in its interior. -/
theorem balanceCap_rate_bounds {b c H₂ H₃ k y : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hH₂ : 0 < H₂) (hH₃ : 0 < H₃)
    (hy : y ∈ Set.Ioo (0 : ℝ) (c / (c + 1)))
    (hk : k ∈ Set.Icc (0 : ℝ) (balanceCap b c H₂ H₃ y)) :
    0 < balanceCap b c H₂ H₃ y ∧
      0 < balanceDenominator b H₂ k y ∧
      soloSecondHazard c H₃ k y ∈ Set.Ioc (0 : ℝ) 1 ∧
      soloThirdHazard b H₂ k y ∈ Set.Ico (0 : ℝ) 1 ∧
      (k < balanceCap b c H₂ H₃ y →
        soloSecondHazard c H₃ k y < 1 ∧ 0 < soloThirdHazard b H₂ k y) := by
  have hc1 : 0 < c + 1 := by positivity
  have hyc : y * (c + 1) < c := (lt_div_iff₀ hc1).mp hy.2
  have hy1 : y < 1 := by nlinarith only [hyc, hc, hy.1]
  have hE : 0 < c - (c + 1) * y := by nlinarith only [hyc]
  have hC : 0 < c * (1 - y) := mul_pos hc (sub_pos.mpr hy1)
  have hk₂ : k * H₂ ≤ b * y :=
    (le_div_iff₀ hH₂).mp (hk.2.trans (min_le_left _ _))
  have hk₃ : k * H₃ ≤ c - (c + 1) * y :=
    (le_div_iff₀ hH₃).mp (hk.2.trans (min_le_right _ _))
  have hden : 0 < balanceDenominator b H₂ k y := by
    unfold balanceDenominator
    nlinarith only [hk.1, hk₂]
  refine ⟨lt_min (div_pos (mul_pos hb hy.1) hH₂) (div_pos hE hH₃), hden,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · apply div_pos _ hC
    nlinarith only [mul_nonneg hH₃.le hk.1, hy.1]
  · apply (div_le_one hC).mpr
    nlinarith only [hk₃]
  · exact div_nonneg (by nlinarith only [hk₂]) hden.le
  · apply (div_lt_one hden).mpr
    unfold balanceDenominator
    nlinarith only [hk.1]
  · intro hkstrict
    have hk₂strict : k * H₂ < b * y :=
      (lt_div_iff₀ hH₂).mp (hkstrict.trans_le (min_le_left _ _))
    have hk₃strict : k * H₃ < c - (c + 1) * y :=
      (lt_div_iff₀ hH₃).mp (hkstrict.trans_le (min_le_right _ _))
    constructor
    · apply (div_lt_one hC).mpr
      nlinarith only [hk₃strict]
    · exact div_pos (by nlinarith only [hk₂strict]) hden

def balanceValue (a b c h₁ η H₂ H₃ k y : ℝ) : ℝ :=
  let z := soloSecondHazard c H₃ k y
  let w := soloThirdHazard b H₂ k y
  h₁ * k + z - a * w * (1 - z) + η * k * (1 - (1 - z) * (1 - w) / (1 + k))

def quadraticLeading (a c h₁ η H₂ H₃ y : ℝ) : ℝ :=
  h₁ * (c * (1 - y)) * (1 - H₂) + H₃ * (1 - H₂) - a * H₂ * H₃ +
    η * (c * (1 - y) * (1 - H₂) + H₃)

def quadraticLinear (a b c h₁ η H₂ H₃ y : ℝ) : ℝ :=
  h₁ * (c * (1 - y)) * (1 + b * y) + H₃ * (1 + b * y + a * b * y) + y +
    H₂ * (a * (c - (c + 1) * y) - y) + η * y * (c * (1 - y) * b + 1)

def quadraticConstant (a b c y : ℝ) : ℝ :=
  y * (b * (a * c + a + 1) * y - gap a b c)

/-- Clearing only the actual positive denominators yields the packet's
quadratic, including the collision-adjusted eta term. -/
theorem balanceValue_quadratic_identity (a b c h₁ η H₂ H₃ k y : ℝ)
    (hC : c * (1 - y) ≠ 0) (hd : balanceDenominator b H₂ k y ≠ 0)
    (hk : 1 + k ≠ 0) :
    c * (1 - y) * balanceDenominator b H₂ k y * balanceValue a b c h₁ η H₂ H₃ k y =
      quadraticBracketValue (quadraticLeading a c h₁ η H₂ H₃ y)
        (quadraticLinear a b c h₁ η H₂ H₃ y) (quadraticConstant a b c y) k := by
  unfold balanceValue soloSecondHazard soloThirdHazard quadraticBracketValue
    quadraticLeading quadraticLinear quadraticConstant gap
  dsimp only
  generalize hCeq : c * (1 - y) = C at *
  field_simp [hC, hd, hk]
  rw [← hCeq]
  unfold balanceDenominator at *
  ring

theorem quadraticConstant_neg {a b c y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hy : y ∈ Set.Ioo (0 : ℝ) (jointHazardCap a b c)) :
    quadraticConstant a b c y < 0 := by
  have hden : 0 < b * (a * c + a + 1) := by positivity
  have hybound := (lt_div_iff₀ hden).mp hy.2
  apply mul_neg_of_pos_of_neg hy.1
  nlinarith only [hybound]

theorem quadraticConstant_endpoints (a b c : ℝ) :
    quadraticConstant a b c 0 = 0 ∧
      quadraticConstant a b c (jointHazardCap a b c) = 0 := by
  constructor
  · simp [quadraticConstant]
  · unfold quadraticConstant jointHazardCap
    by_cases hden : b * (a * c + a + 1) = 0
    · simp [hden]
    · rw [mul_div_cancel₀ _ hden, sub_self, mul_zero]

theorem quadraticLinear_pos {a b c h₁ η H₂ H₃ y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hh₁ : 0 < h₁)
    (hη : 0 ≤ η) (hH₂ : 0 < H₂) (hH₃ : 0 < H₃)
    (hgap : 0 < gap a b c) (hy : y ∈ Set.Icc (0 : ℝ) (jointHazardCap a b c)) :
    0 < quadraticLinear a b c h₁ η H₂ H₃ y := by
  have hden : 0 < b * (a * c + a + 1) := by positivity
  have hy0 : 0 ≤ y := hy.1
  have hybound := (le_div_iff₀ hden).mp hy.2
  have hy1 : y < 1 := hy.2.trans_lt (jointHazardCap_bounds ha hb hc hgap).2.2
  have hC : 0 < c * (1 - y) := mul_pos hc (sub_pos.mpr hy1)
  have hE : 0 < a * (c - (c + 1) * y) - y := by
    unfold gap at hybound
    have hproduct : 0 < b * (a * (c - (c + 1) * y) - y) := by
      nlinarith only [hybound]
    exact pos_of_mul_pos_right hproduct hb.le
  have hfirst : 0 < h₁ * (c * (1 - y)) * (1 + b * y) := by positivity
  have hsecond : 0 ≤ H₃ * (1 + b * y + a * b * y) := by positivity
  have hthird : 0 ≤ H₂ * (a * (c - (c + 1) * y) - y) := mul_nonneg hH₂.le hE.le
  have hfourth : 0 ≤ η * y * (c * (1 - y) * b + 1) := by positivity
  unfold quadraticLinear
  linarith only [hfirst, hsecond, hthird, hfourth, hy.1]

theorem balanceValue_at_cap_pos {a b c h₁ η H₂ H₃ y : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hh₁ : 0 < h₁) (hη : 0 ≤ η)
    (hH₂ : 0 < H₂) (hH₃ : 0 < H₃)
    (hy : y ∈ Set.Ioo (0 : ℝ) (c / (c + 1))) :
    0 < balanceValue a b c h₁ η H₂ H₃ (balanceCap b c H₂ H₃ y) y := by
  have hc1 : 0 < c + 1 := by positivity
  have hyc := (lt_div_iff₀ hc1).mp hy.2
  have hE : 0 < c - (c + 1) * y := by nlinarith only [hyc]
  have hK : 0 < balanceCap b c H₂ H₃ y :=
    lt_min (div_pos (mul_pos hb hy.1) hH₂) (div_pos hE hH₃)
  obtain ⟨_, hd, hz, _hw, _⟩ := balanceCap_rate_bounds hb hc hH₂ hH₃ hy
    (show balanceCap b c H₂ H₃ y ∈ Set.Icc (0 : ℝ) (balanceCap b c H₂ H₃ y) from
      ⟨hK.le, le_rfl⟩)
  rcases le_total (b * y / H₂) ((c - (c + 1) * y) / H₃) with hleft | hright
  · have hcap : balanceCap b c H₂ H₃ y = b * y / H₂ := min_eq_left hleft
    have hwzero : soloThirdHazard b H₂ (balanceCap b c H₂ H₃ y) y = 0 := by
      unfold soloThirdHazard
      rw [hcap]
      have hnum : b * y - H₂ * (b * y / H₂) = 0 := by
        field_simp
        ring
      rw [hnum, zero_div]
    have hk1 : 0 < 1 + balanceCap b c H₂ H₃ y := by positivity
    have hbonus : 0 ≤ 1 -
        (1 - soloSecondHazard c H₃ (balanceCap b c H₂ H₃ y) y) /
          (1 + balanceCap b c H₂ H₃ y) := by
      have hquot := (div_le_one hk1).mpr
        (show 1 - soloSecondHazard c H₃ (balanceCap b c H₂ H₃ y) y ≤
          1 + balanceCap b c H₂ H₃ y by linarith only [hz.1, hK])
      linarith only [hquot]
    have hcharge := mul_nonneg (mul_nonneg hη hK.le) hbonus
    unfold balanceValue
    dsimp only
    rw [hwzero]
    simp only [mul_zero, sub_zero, mul_one]
    have hbase := mul_pos hh₁ hK
    linarith only [hbase, hz.1, hcharge]
  · have hcap : balanceCap b c H₂ H₃ y = (c - (c + 1) * y) / H₃ :=
      min_eq_right hright
    have hzone : soloSecondHazard c H₃ (balanceCap b c H₂ H₃ y) y = 1 := by
      unfold soloSecondHazard
      rw [hcap]
      have hnum : H₃ * ((c - (c + 1) * y) / H₃) + y = c * (1 - y) := by
        field_simp
        ring
      rw [hnum, div_self (by nlinarith only [hyc, hc, hy.1])]
    unfold balanceValue
    dsimp only
    rw [hzone]
    simp only [sub_self, mul_zero, zero_mul, zero_div, sub_zero, mul_one]
    positivity

/-- Actual admissible root computed from the collision-adjusted raw data. -/
def selectedBalanceRoot (a b c h₁ h₂ h₃ η q₂ q₃ y : ℝ) : ℝ :=
  rationalizedQuadraticRoot
    (quadraticLeading a c h₁ η (jointLoss h₂ q₂ y) (jointLoss h₃ q₃ y) y)
    (quadraticLinear a b c h₁ η (jointLoss h₂ q₂ y) (jointLoss h₃ q₃ y) y)
    (quadraticConstant a b c y)

theorem quadratic_at_balanceCap_pos {a b c h₁ η H₂ H₃ y : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hh₁ : 0 < h₁) (hη : 0 ≤ η)
    (hH₂ : 0 < H₂) (hH₃ : 0 < H₃)
    (hy : y ∈ Set.Ioo (0 : ℝ) (c / (c + 1))) :
    0 < quadraticBracketValue (quadraticLeading a c h₁ η H₂ H₃ y)
      (quadraticLinear a b c h₁ η H₂ H₃ y) (quadraticConstant a b c y)
      (balanceCap b c H₂ H₃ y) := by
  have hc1 : 0 < c + 1 := by positivity
  have hyc := (lt_div_iff₀ hc1).mp hy.2
  have hy1 : y < 1 := by nlinarith only [hyc, hc, hy.1]
  have hK : 0 < balanceCap b c H₂ H₃ y := lt_min
    (div_pos (mul_pos hb hy.1) hH₂)
    (div_pos (by nlinarith only [hyc]) hH₃)
  have hrate := balanceCap_rate_bounds hb hc hH₂ hH₃ hy ⟨hK.le, le_rfl⟩
  have hC : 0 < c * (1 - y) := mul_pos hc (sub_pos.mpr hy1)
  rw [← balanceValue_quadratic_identity a b c h₁ η H₂ H₃ _ y hC.ne'
    hrate.2.1.ne' (show 1 + balanceCap b c H₂ H₃ y ≠ 0 by positivity)]
  exact mul_pos (mul_pos hC hrate.2.1)
    (balanceValue_at_cap_pos (a := a) hb hc hh₁ hη hH₂ hH₃ hy)

/-- Raw positive magnitudes and nonpositive collision rewards produce the
nonlinear balance root, with no root-selection witness supplied. -/
theorem selectedBalanceRoot_spec {a b c h₁ h₂ h₃ η q₂ q₃ y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃)
    (hη : 0 ≤ η) (hq₂ : q₂ ≤ 0) (hq₃ : q₃ ≤ 0) (hgap : 0 < gap a b c)
    (hy : y ∈ Set.Ioo (0 : ℝ) (jointHazardCap a b c)) :
    let H₂ := jointLoss h₂ q₂ y
    let H₃ := jointLoss h₃ q₃ y
    let k := selectedBalanceRoot a b c h₁ h₂ h₃ η q₂ q₃ y
    k ∈ Set.Ioo (0 : ℝ) (balanceCap b c H₂ H₃ y) ∧
      soloSecondHazard c H₃ k y ∈ Set.Ioo (0 : ℝ) 1 ∧
      soloThirdHazard b H₂ k y ∈ Set.Ioo (0 : ℝ) 1 ∧
      balanceValue a b c h₁ η H₂ H₃ k y = 0 := by
  have hY := jointHazardCap_bounds ha hb hc hgap
  have hy1 : y < 1 := hy.2.trans hY.2.2
  have hyc : y ∈ Set.Ioo (0 : ℝ) (c / (c + 1)) := ⟨hy.1, hy.2.trans hY.2.1⟩
  have hH₂ := jointLoss_pos hh₂ hq₂ ⟨hy.1.le, hy1⟩
  have hH₃ := jointLoss_pos hh₃ hq₃ ⟨hy.1.le, hy1⟩
  let H₂ := jointLoss h₂ q₂ y
  let H₃ := jointLoss h₃ q₃ y
  let K := balanceCap b c H₂ H₃ y
  have hK : 0 < K := lt_min (div_pos (mul_pos hb hy.1) hH₂)
    (div_pos (by
      have hbound := (lt_div_iff₀ (show 0 < c + 1 by positivity)).mp hyc.2
      nlinarith only [hbound]) hH₃)
  have hC : 0 < c * (1 - y) := mul_pos hc (sub_pos.mpr hy1)
  have hcapPolynomial := quadratic_at_balanceCap_pos
    (a := a) hb hc hh₁ hη hH₂ hH₃ hyc
  have hroot := rationalizedQuadraticRoot_spec (quadraticConstant_neg ha hb hc hy)
    hK hcapPolynomial
  let k := selectedBalanceRoot a b c h₁ h₂ h₃ η q₂ q₃ y
  have hk : k ∈ Set.Ioo (0 : ℝ) K := hroot.2.2.1
  have hk0 : 0 < k := hk.1
  have hrate := balanceCap_rate_bounds hb hc hH₂ hH₃ hyc ⟨hk.1.le, hk.2.le⟩
  dsimp only
  refine ⟨hk, ⟨hrate.2.2.1.1, (hrate.2.2.2.2 hk.2).1⟩,
    ⟨(hrate.2.2.2.2 hk.2).2, hrate.2.2.2.1.2⟩, ?_⟩
  have hidentity := balanceValue_quadratic_identity a b c h₁ η H₂ H₃ k y
    hC.ne' hrate.2.1.ne' (show 1 + k ≠ 0 by positivity)
  have hzero : quadraticBracketValue (quadraticLeading a c h₁ η H₂ H₃ y)
      (quadraticLinear a b c h₁ η H₂ H₃ y) (quadraticConstant a b c y) k = 0 :=
    hroot.2.2.2.1
  rw [hzero] at hidentity
  exact (mul_eq_zero.mp hidentity).resolve_left (mul_ne_zero hC.ne' hrate.2.1.ne')

/-- The actual raw-data selector is continuous on the whole closed interval,
including zero endpoint roots and a vanishing leading coefficient. -/
theorem selectedBalanceRoot_continuous_endpoints {a b c h₁ h₂ h₃ η q₂ q₃ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃)
    (hη : 0 ≤ η) (hq₂ : q₂ ≤ 0) (hq₃ : q₃ ≤ 0) (hgap : 0 < gap a b c) :
    ContinuousOn (selectedBalanceRoot a b c h₁ h₂ h₃ η q₂ q₃)
      (Set.Icc (0 : ℝ) (jointHazardCap a b c)) ∧
      selectedBalanceRoot a b c h₁ h₂ h₃ η q₂ q₃ 0 = 0 ∧
      selectedBalanceRoot a b c h₁ h₂ h₃ η q₂ q₃ (jointHazardCap a b c) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold selectedBalanceRoot
    apply continuousOn_rationalizedQuadraticRoot_of_linear_pos
    · unfold quadraticLeading jointLoss
      fun_prop
    · unfold quadraticLinear jointLoss
      fun_prop
    · unfold quadraticConstant
      fun_prop
    · intro y hy
      have hy1 : y < 1 := hy.2.trans_lt (jointHazardCap_bounds ha hb hc hgap).2.2
      exact quadraticLinear_pos ha hb hc hh₁ hη
        (jointLoss_pos hh₂ hq₂ ⟨hy.1, hy1⟩)
        (jointLoss_pos hh₃ hq₃ ⟨hy.1, hy1⟩) hgap hy
  · unfold selectedBalanceRoot
    rw [(quadraticConstant_endpoints a b c).1]
    exact rationalizedQuadraticRoot_constant_zero _ _
  · unfold selectedBalanceRoot
    rw [(quadraticConstant_endpoints a b c).2]
    exact rationalizedQuadraticRoot_constant_zero _ _

/-- The actual raw selector exposes the simple positive crossing and unique
nonlinear balance root inside its computed admissible bracket. -/
theorem selectedBalanceRoot_crossing_and_unique {a b c h₁ h₂ h₃ η q₂ q₃ y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃)
    (hη : 0 ≤ η) (hq₂ : q₂ ≤ 0) (hq₃ : q₃ ≤ 0) (hgap : 0 < gap a b c)
    (hy : y ∈ Set.Ioo (0 : ℝ) (jointHazardCap a b c)) :
    let H₂ := jointLoss h₂ q₂ y
    let H₃ := jointLoss h₃ q₃ y
    let k := selectedBalanceRoot a b c h₁ h₂ h₃ η q₂ q₃ y
    0 < 2 * quadraticLeading a c h₁ η H₂ H₃ y * k +
        quadraticLinear a b c h₁ η H₂ H₃ y ∧
      ∀ other ∈ Set.Ioo (0 : ℝ) (balanceCap b c H₂ H₃ y),
        balanceValue a b c h₁ η H₂ H₃ other y = 0 → other = k := by
  have hY := jointHazardCap_bounds ha hb hc hgap
  have hy1 : y < 1 := hy.2.trans hY.2.2
  have hyc : y ∈ Set.Ioo (0 : ℝ) (c / (c + 1)) := ⟨hy.1, hy.2.trans hY.2.1⟩
  have hH₂ := jointLoss_pos hh₂ hq₂ ⟨hy.1.le, hy1⟩
  have hH₃ := jointLoss_pos hh₃ hq₃ ⟨hy.1.le, hy1⟩
  have hselected := selectedBalanceRoot_spec ha hb hc hh₁ hh₂ hh₃ hη hq₂ hq₃ hgap hy
  have hK : 0 < balanceCap b c (jointLoss h₂ q₂ y) (jointLoss h₃ q₃ y) y :=
    hselected.1.1.trans hselected.1.2
  have hroot := rationalizedQuadraticRoot_spec (quadraticConstant_neg ha hb hc hy) hK
    (quadratic_at_balanceCap_pos (a := a) hb hc hh₁ hη hH₂ hH₃ hyc)
  dsimp only
  refine ⟨hroot.2.2.2.2.1, ?_⟩
  intro other hother hzero
  have hother0 : 0 < other := hother.1
  have hrate := balanceCap_rate_bounds hb hc hH₂ hH₃ hyc ⟨hother.1.le, hother.2.le⟩
  have hC : 0 < c * (1 - y) := mul_pos hc (sub_pos.mpr hy1)
  have hidentity := balanceValue_quadratic_identity a b c h₁ η
    (jointLoss h₂ q₂ y) (jointLoss h₃ q₃ y) other y hC.ne' hrate.2.1.ne'
    (show 1 + other ≠ 0 by positivity)
  rw [hzero, mul_zero] at hidentity
  exact hroot.2.2.2.2.2 other hother hidentity.symm

end Math.CyclicChildJointPhase
