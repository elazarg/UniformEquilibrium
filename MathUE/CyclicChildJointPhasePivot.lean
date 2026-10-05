import MathUE.CyclicChildJointPhaseAlgebra

/-! # Canceled endpoint ratios for the actual cyclic-child pivot

Only the packet's raw scalar parameters are recorded. The balance root and
its normalized endpoint ratios are computed, not supplied as certificates.
-/

noncomputable section

namespace Math.CyclicChildJointPhase

/-- Raw cycle, harm and collision parameters; no strategic witness is stored. -/
structure JointPhaseData where
  a : ℝ
  b : ℝ
  c : ℝ
  h₁ : ℝ
  h₂ : ℝ
  h₃ : ℝ
  η : ℝ
  q₂ : ℝ
  q₃ : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  h₁_pos : 0 < h₁
  h₂_pos : 0 < h₂
  h₃_pos : 0 < h₃
  eta_nonneg : 0 ≤ η
  q₂_nonpos : q₂ ≤ 0
  q₃_nonpos : q₃ ≤ 0
  gap_pos : 0 < gap a b c

namespace JointPhaseData

def upper (data : JointPhaseData) : ℝ := jointHazardCap data.a data.b data.c

def root (data : JointPhaseData) (y : ℝ) : ℝ :=
  selectedBalanceRoot data.a data.b data.c data.h₁ data.h₂ data.h₃ data.η data.q₂ data.q₃ y

def leading (data : JointPhaseData) (y : ℝ) : ℝ :=
  quadraticLeading data.a data.c data.h₁ data.η
    (jointLoss data.h₂ data.q₂ y) (jointLoss data.h₃ data.q₃ y) y

def linear (data : JointPhaseData) (y : ℝ) : ℝ :=
  quadraticLinear data.a data.b data.c data.h₁ data.η
    (jointLoss data.h₂ data.q₂ y) (jointLoss data.h₃ data.q₃ y) y

def denominator (data : JointPhaseData) (y : ℝ) : ℝ :=
  data.linear y + Real.sqrt (discrim (data.leading y) (data.linear y)
    (quadraticConstant data.a data.b data.c y))

/-- The canceled formula extends `root y / y` through the zero endpoint. -/
def rootRatio (data : JointPhaseData) (y : ℝ) : ℝ :=
  -2 * (data.b * (data.a * data.c + data.a + 1) * y - gap data.a data.b data.c) /
    data.denominator y

def balance (data : JointPhaseData) : Fin 3 → ℝ :=
  balanceVector data.a data.b data.c data.h₁ data.h₂ data.h₃

theorem balance_pos (data : JointPhaseData) (who : Fin 3) : 0 < data.balance who :=
  balanceVector_pos data.a_pos data.b_pos data.c_pos data.h₁_pos data.h₂_pos
    data.h₃_pos data.gap_pos who

theorem upper_bounds (data : JointPhaseData) :
    0 < data.upper ∧ data.upper < data.c / (data.c + 1) ∧ data.upper < 1 :=
  jointHazardCap_bounds data.a_pos data.b_pos data.c_pos data.gap_pos

theorem linear_pos (data : JointPhaseData) {y : ℝ} (hy : y ∈ Set.Icc 0 data.upper) :
    0 < data.linear y := by
  have hy1 : y < 1 := hy.2.trans_lt data.upper_bounds.2.2
  exact quadraticLinear_pos data.a_pos data.b_pos data.c_pos data.h₁_pos
    data.eta_nonneg (jointLoss_pos data.h₂_pos data.q₂_nonpos ⟨hy.1, hy1⟩)
    (jointLoss_pos data.h₃_pos data.q₃_nonpos ⟨hy.1, hy1⟩) data.gap_pos hy

theorem denominator_pos (data : JointPhaseData) {y : ℝ}
    (hy : y ∈ Set.Icc 0 data.upper) : 0 < data.denominator y :=
  (data.linear_pos hy).trans_le (le_add_of_nonneg_right (Real.sqrt_nonneg _))

theorem root_eq_mul_rootRatio (data : JointPhaseData) (y : ℝ) :
    data.root y = y * data.rootRatio y := by
  unfold root selectedBalanceRoot rationalizedQuadraticRoot rootRatio denominator
    leading linear quadraticConstant
  ring

theorem rootRatio_eq_div (data : JointPhaseData) {y : ℝ} (hy : y ≠ 0) :
    data.rootRatio y = data.root y / y := by
  rw [data.root_eq_mul_rootRatio, mul_div_cancel_left₀ _ hy]

theorem rootRatio_continuous (data : JointPhaseData) :
    ContinuousOn data.rootRatio (Set.Icc 0 data.upper) := by
  unfold rootRatio
  apply ContinuousOn.div
  · fun_prop
  · unfold denominator linear leading quadraticLeading quadraticLinear jointLoss
      quadraticConstant discrim
    fun_prop
  · exact fun _ hy => (data.denominator_pos hy).ne'

theorem linear_zero (data : JointPhaseData) :
    data.linear 0 = data.a * data.c * data.h₂ + data.c * data.h₁ + data.h₃ := by
  simp [linear, quadraticLinear, jointLoss]
  ring

theorem rootRatio_zero (data : JointPhaseData) : data.rootRatio 0 = 1 / data.balance 0 := by
  have hlinear := data.linear_pos (show (0 : ℝ) ∈ Set.Icc 0 data.upper from
    ⟨le_rfl, data.upper_bounds.1.le⟩)
  have hgap := data.gap_pos
  unfold rootRatio denominator
  rw [(quadraticConstant_endpoints data.a data.b data.c).1]
  simp only [discrim, mul_zero, sub_zero, Real.sqrt_sq_eq_abs, abs_of_pos hlinear,
    mul_zero, zero_sub]
  rw [data.linear_zero]
  have hbalance : data.balance 0 =
      (data.a * data.c * data.h₂ + data.c * data.h₁ + data.h₃) /
        gap data.a data.b data.c :=
    congrFun (balanceVector_eq data.a data.b data.c data.h₁ data.h₂ data.h₃) 0
  rw [hbalance]
  have hβ : data.a * data.c * data.h₂ + data.c * data.h₁ + data.h₃ ≠ 0 := by
    rw [← data.linear_zero]
    exact hlinear.ne'
  generalize hβeq : data.a * data.c * data.h₂ + data.c * data.h₁ + data.h₃ = B at *
  field_simp [hgap.ne', hβ]
  ring

def second (data : JointPhaseData) (y : ℝ) : ℝ :=
  soloSecondHazard data.c (jointLoss data.h₃ data.q₃ y) (data.root y) y

def third (data : JointPhaseData) (y : ℝ) : ℝ :=
  soloThirdHazard data.b (jointLoss data.h₂ data.q₂ y) (data.root y) y

def secondRatio (data : JointPhaseData) (y : ℝ) : ℝ :=
  (jointLoss data.h₃ data.q₃ y * data.rootRatio y + 1) / (data.c * (1 - y))

def thirdRatio (data : JointPhaseData) (y : ℝ) : ℝ :=
  (data.b - jointLoss data.h₂ data.q₂ y * data.rootRatio y) /
    balanceDenominator data.b (jointLoss data.h₂ data.q₂ y) (data.root y) y

theorem root_zero (data : JointPhaseData) : data.root 0 = 0 := by
  rw [data.root_eq_mul_rootRatio, zero_mul]

theorem root_upper (data : JointPhaseData) : data.root data.upper = 0 :=
  (selectedBalanceRoot_continuous_endpoints data.a_pos data.b_pos data.c_pos data.h₁_pos
    data.h₂_pos data.h₃_pos data.eta_nonneg data.q₂_nonpos data.q₃_nonpos data.gap_pos).2.2

theorem root_continuous (data : JointPhaseData) :
    ContinuousOn data.root (Set.Icc 0 data.upper) :=
  (selectedBalanceRoot_continuous_endpoints data.a_pos data.b_pos data.c_pos data.h₁_pos
    data.h₂_pos data.h₃_pos data.eta_nonneg data.q₂_nonpos data.q₃_nonpos data.gap_pos).1

theorem second_eq_mul_ratio (data : JointPhaseData) (y : ℝ) :
    data.second y = y * data.secondRatio y := by
  unfold second soloSecondHazard secondRatio
  rw [data.root_eq_mul_rootRatio]
  ring

theorem third_eq_mul_ratio (data : JointPhaseData) (y : ℝ) :
    data.third y = y * data.thirdRatio y := by
  unfold third soloThirdHazard thirdRatio
  rw [data.root_eq_mul_rootRatio]
  ring

theorem secondRatio_zero (data : JointPhaseData) :
    data.secondRatio 0 = data.balance 1 / data.balance 0 := by
  have hbalance := balanceVector_balances data.a data.b data.c data.h₁ data.h₂ data.h₃
    data.gap_pos.ne'
  have hthird : data.c * data.balance 1 - data.balance 0 = data.h₃ := hbalance.2.2
  unfold secondRatio
  rw [data.rootRatio_zero]
  simp only [jointLoss, sub_zero, mul_one, mul_zero]
  field_simp [data.c_pos.ne', (data.balance_pos 0).ne']
  nlinarith only [hthird]

theorem thirdRatio_zero (data : JointPhaseData) :
    data.thirdRatio 0 = data.balance 2 / data.balance 0 := by
  have hbalance := balanceVector_balances data.a data.b data.c data.h₁ data.h₂ data.h₃
    data.gap_pos.ne'
  have hsecond : data.b * data.balance 0 - data.balance 2 = data.h₂ := hbalance.2.1
  unfold thirdRatio
  rw [data.rootRatio_zero, data.root_zero]
  simp only [jointLoss, balanceDenominator, mul_zero, sub_zero, mul_one, add_zero, div_one]
  field_simp [(data.balance_pos 0).ne']
  nlinarith only [hsecond]

theorem selected_denominator_pos (data : JointPhaseData) {y : ℝ}
    (hy : y ∈ Set.Icc 0 data.upper) :
    0 < balanceDenominator data.b (jointLoss data.h₂ data.q₂ y) (data.root y) y := by
  by_cases hyzero : y = 0
  · subst y
    rw [data.root_zero]
    norm_num [balanceDenominator]
  · by_cases hyupper : y = data.upper
    · subst y
      rw [data.root_upper]
      have hb := data.b_pos
      have hY := data.upper_bounds.1
      simp only [balanceDenominator, mul_zero, add_zero]
      exact add_pos zero_lt_one (mul_pos hb hY)
    · have hinterior : y ∈ Set.Ioo 0 data.upper :=
        ⟨lt_of_le_of_ne hy.1 (Ne.symm hyzero), lt_of_le_of_ne hy.2 hyupper⟩
      have hsource := selectedBalanceRoot_spec data.a_pos data.b_pos data.c_pos
        data.h₁_pos data.h₂_pos data.h₃_pos data.eta_nonneg data.q₂_nonpos data.q₃_nonpos
        data.gap_pos hinterior
      have hy1 := hinterior.2.trans data.upper_bounds.2.2
      have hz := hinterior.2.trans data.upper_bounds.2.1
      have hrate := balanceCap_rate_bounds data.b_pos data.c_pos
        (jointLoss_pos data.h₂_pos data.q₂_nonpos ⟨hy.1, hy1⟩)
        (jointLoss_pos data.h₃_pos data.q₃_nonpos ⟨hy.1, hy1⟩)
        ⟨hinterior.1, hz⟩ ⟨hsource.1.1.le, hsource.1.2.le⟩
      exact hrate.2.1

theorem secondRatio_continuous (data : JointPhaseData) :
    ContinuousOn data.secondRatio (Set.Icc 0 data.upper) := by
  unfold secondRatio
  apply ContinuousOn.div
  · have hloss : ContinuousOn (jointLoss data.h₃ data.q₃) (Set.Icc 0 data.upper) := by
      unfold jointLoss
      fun_prop
    exact (hloss.mul data.rootRatio_continuous).add continuousOn_const
  · fun_prop
  · intro y hy
    exact (mul_pos data.c_pos (sub_pos.mpr
      (hy.2.trans_lt data.upper_bounds.2.2))).ne'

theorem thirdRatio_continuous (data : JointPhaseData) :
    ContinuousOn data.thirdRatio (Set.Icc 0 data.upper) := by
  have hloss : ContinuousOn (jointLoss data.h₂ data.q₂) (Set.Icc 0 data.upper) := by
    unfold jointLoss
    fun_prop
  unfold thirdRatio
  apply ContinuousOn.div
  · exact continuousOn_const.sub (hloss.mul data.rootRatio_continuous)
  · unfold balanceDenominator
    have hroot := data.root_continuous
    fun_prop
  · exact fun _ hy => (data.selected_denominator_pos hy).ne'

theorem second_lt_one (data : JointPhaseData) {y : ℝ}
    (hy : y ∈ Set.Icc 0 data.upper) : data.second y < 1 := by
  by_cases hzero : y = 0
  · subst y
    rw [data.second_eq_mul_ratio, zero_mul]
    exact zero_lt_one
  by_cases hupper : y = data.upper
  · subst y
    unfold second soloSecondHazard
    rw [data.root_upper]
    simp only [mul_zero, zero_add]
    apply (div_lt_one (mul_pos data.c_pos
      (sub_pos.mpr data.upper_bounds.2.2))).mpr
    have hbound := (lt_div_iff₀ (add_pos data.c_pos zero_lt_one)).mp
      data.upper_bounds.2.1
    nlinarith only [hbound]
  have hinterior : y ∈ Set.Ioo 0 data.upper :=
    ⟨lt_of_le_of_ne hy.1 (Ne.symm hzero), lt_of_le_of_ne hy.2 hupper⟩
  exact (selectedBalanceRoot_spec data.a_pos data.b_pos data.c_pos data.h₁_pos
    data.h₂_pos data.h₃_pos data.eta_nonneg data.q₂_nonpos data.q₃_nonpos
    data.gap_pos hinterior).2.1.2

theorem thirdRatio_pos (data : JointPhaseData) {y : ℝ}
    (hy : y ∈ Set.Icc 0 data.upper) : 0 < data.thirdRatio y := by
  by_cases hzero : y = 0
  · subst y
    rw [data.thirdRatio_zero]
    exact div_pos (data.balance_pos 2) (data.balance_pos 0)
  by_cases hupper : y = data.upper
  · subst y
    have hratio : data.rootRatio data.upper = 0 := by
      rw [data.rootRatio_eq_div data.upper_bounds.1.ne', data.root_upper, zero_div]
    unfold thirdRatio
    rw [hratio, data.root_upper]
    simp only [mul_zero, sub_zero, balanceDenominator, add_zero]
    exact div_pos data.b_pos (add_pos zero_lt_one
      (mul_pos data.b_pos data.upper_bounds.1))
  have hinterior : y ∈ Set.Ioo 0 data.upper :=
    ⟨lt_of_le_of_ne hy.1 (Ne.symm hzero), lt_of_le_of_ne hy.2 hupper⟩
  have hthird := (selectedBalanceRoot_spec data.a_pos data.b_pos data.c_pos data.h₁_pos
    data.h₂_pos data.h₃_pos data.eta_nonneg data.q₂_nonpos data.q₃_nonpos
    data.gap_pos hinterior).2.2.1.1
  change 0 < data.third y at hthird
  rw [data.third_eq_mul_ratio] at hthird
  exact pos_of_mul_pos_right hthird hinterior.1.le

/-- Canceled pivot payoff, including the zero-hazard endpoint. -/
def pivot (data : JointPhaseData) (u v ξ y : ℝ) : ℝ :=
  let p := 1 + ξ * y
  p + ((p - u) / (1 - y) + (p - v) * data.secondRatio y) /
    ((1 - data.second y) * data.thirdRatio y)

def pivotLower (data : JointPhaseData) (u v : ℝ) : ℝ :=
  1 + ((1 - u) * data.balance 0 + (1 - v) * data.balance 1) / data.balance 2

theorem pivot_continuous (data : JointPhaseData) (u v ξ : ℝ) :
    ContinuousOn (data.pivot u v ξ) (Set.Icc 0 data.upper) := by
  have hp : ContinuousOn (fun y : ℝ => 1 + ξ * y) (Set.Icc 0 data.upper) := by
    fun_prop
  have hsecond : ContinuousOn data.second (Set.Icc 0 data.upper) := by
    have hrewrite : data.second = fun y => y * data.secondRatio y :=
      funext data.second_eq_mul_ratio
    rw [hrewrite]
    exact continuousOn_id.mul data.secondRatio_continuous
  unfold pivot
  apply hp.add
  apply ContinuousOn.div
  · exact ((hp.sub continuousOn_const).div (by fun_prop)
      (fun y hy => (sub_pos.mpr (hy.2.trans_lt data.upper_bounds.2.2)).ne')).add
      ((hp.sub continuousOn_const).mul data.secondRatio_continuous)
  · exact (continuousOn_const.sub hsecond).mul data.thirdRatio_continuous
  · intro y hy
    exact (mul_pos (sub_pos.mpr (data.second_lt_one hy)) (data.thirdRatio_pos hy)).ne'

theorem pivot_zero (data : JointPhaseData) (u v ξ : ℝ) :
    data.pivot u v ξ 0 = data.pivotLower u v := by
  unfold pivot pivotLower
  rw [data.second_eq_mul_ratio, data.secondRatio_zero, data.thirdRatio_zero]
  simp only [mul_zero, add_zero, sub_zero, div_one]
  field_simp [(data.balance_pos 0).ne', (data.balance_pos 2).ne']
  ring

theorem pivot_eq_uncanceled (data : JointPhaseData) (u v ξ : ℝ) {y : ℝ}
    (hy : y ≠ 0) :
    data.pivot u v ξ y = 1 + ξ * y +
      (((1 + ξ * y - u) * y / (1 - y) + (1 + ξ * y - v) * data.second y) /
        ((1 - data.second y) * data.third y)) := by
  unfold pivot
  rw [data.second_eq_mul_ratio, data.third_eq_mul_ratio]
  field_simp [hy]

def pivotUpper (data : JointPhaseData) (u v ξ : ℝ) : ℝ :=
  1 + data.a * data.c * (1 - u) + data.a * (1 - v) + ξ * gap data.a data.b data.c / data.b

theorem pivot_at_zero_root (data : JointPhaseData) (u v ξ : ℝ) {y : ℝ}
    (hy : 0 < y) (hyc : y < data.c / (data.c + 1)) (hroot : data.root y = 0) :
    data.pivot u v ξ y = 1 + ξ * y +
      ((data.c + 1) * (1 + ξ * y) - data.c * u - v) * (1 + data.b * y) /
        (data.b * (data.c - (data.c + 1) * y)) := by
  have hcy := (lt_div_iff₀ (add_pos data.c_pos zero_lt_one)).mp hyc
  have hy1 : y < 1 := by nlinarith [data.c_pos]
  have hE : 0 < data.c - (data.c + 1) * y := by linarith only [hcy]
  have hC := mul_pos data.c_pos (sub_pos.mpr hy1)
  have hd := add_pos zero_lt_one (mul_pos data.b_pos hy)
  have hratio : data.rootRatio y = 0 := by
    rw [data.rootRatio_eq_div hy.ne', hroot, zero_div]
  unfold pivot secondRatio thirdRatio second soloSecondHazard
  rw [hratio, hroot]
  simp only [mul_zero, zero_add, sub_zero, balanceDenominator, add_zero]
  have hden : 1 - y / (data.c * (1 - y)) =
      (data.c - (data.c + 1) * y) / (data.c * (1 - y)) := by
    generalize hCeq : data.c * (1 - y) = C at *
    field_simp [hC.ne']
    rw [← hCeq]
    ring
  rw [hden]
  generalize hCeq : data.c * (1 - y) = C at *
  generalize hEeq : data.c - (data.c + 1) * y = E at *
  field_simp [data.b_pos.ne', (sub_pos.mpr hy1).ne', hC.ne', hd.ne', hE.ne']
  rw [← hCeq, ← hEeq]
  ring

theorem upper_ratio (data : JointPhaseData) :
    (1 + data.b * data.upper) /
      (data.b * (data.c - (data.c + 1) * data.upper)) = data.a := by
  have hL : 0 < data.a * data.c + data.a + 1 :=
    add_pos (add_pos (mul_pos data.a_pos data.c_pos) data.a_pos) zero_lt_one
  have hcy := (lt_div_iff₀ (add_pos data.c_pos zero_lt_one)).mp data.upper_bounds.2.1
  have hE : data.c - (data.c + 1) * data.upper ≠ 0 := by
    apply ne_of_gt
    linarith only [hcy]
  apply (div_eq_iff (mul_ne_zero data.b_pos.ne' hE)).mpr
  unfold upper jointHazardCap gap
  generalize hLeq : data.a * data.c + data.a + 1 = L at *
  field_simp [data.b_pos.ne', hL.ne']
  rw [← hLeq]
  ring

theorem pivot_upper (data : JointPhaseData) (u v ξ : ℝ) :
    data.pivot u v ξ data.upper = data.pivotUpper u v ξ := by
  rw [data.pivot_at_zero_root u v ξ data.upper_bounds.1
    data.upper_bounds.2.1 data.root_upper, mul_div_assoc, data.upper_ratio]
  unfold pivotUpper upper jointHazardCap
  have hL : 0 < data.a * data.c + data.a + 1 :=
    add_pos (add_pos (mul_pos data.a_pos data.c_pos) data.a_pos) zero_lt_one
  generalize hLeq : data.a * data.c + data.a + 1 = L at *
  field_simp [data.b_pos.ne', hL.ne']
  rw [← hLeq]
  ring

/-- An actual proper joint hazard selected from the literal pivot interval. -/
theorem exists_pivot (data : JointPhaseData) (u v ξ R : ℝ)
    (hR : R ∈ Set.Ioo (data.pivotLower u v) (data.pivotUpper u v ξ)) :
    ∃ y ∈ Set.Ioo 0 data.upper, data.pivot u v ξ y = R := by
  have hvalues : R ∈ Set.Ioo (data.pivot u v ξ 0) (data.pivot u v ξ data.upper) := by
    rwa [data.pivot_zero, data.pivot_upper]
  exact intermediate_value_Ioo data.upper_bounds.1.le (data.pivot_continuous u v ξ) hvalues

end JointPhaseData
end Math.CyclicChildJointPhase
