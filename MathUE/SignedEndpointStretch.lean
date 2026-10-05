import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Signed stretching of paired endpoints in [-1,1]

For a stretch parameter in `[0,1]`, the larger endpoint moves toward one
and the smaller toward minus one. Equal endpoints stay fixed. These are
real-valued semantic definitions; the directed-gap transform retains its
zero case explicitly.
-/

noncomputable section

namespace Math

/-- Stretch an endpoint away from its paired endpoint toward the unit boundary. -/
def unitEndpointStretch (alpha value other : ℝ) : ℝ :=
  if value < other then (1 - alpha) * value - alpha
  else if other < value then (1 - alpha) * value + alpha
  else value

/-- The signed difference induced by stretching a pair of endpoints. -/
def signedEndpointGapStretch (alpha gap : ℝ) : ℝ :=
  if 0 < gap then (1 - alpha) * gap + 2 * alpha
  else if gap < 0 then (1 - alpha) * gap - 2 * alpha
  else 0

@[simp] theorem unitEndpointStretch_self (alpha value : ℝ) :
    unitEndpointStretch alpha value value = value := by
  simp [unitEndpointStretch]

@[simp] theorem signedEndpointGapStretch_zero (alpha : ℝ) :
    signedEndpointGapStretch alpha 0 = 0 := by
  simp [signedEndpointGapStretch]

theorem unitEndpointStretch_sub_reverse (alpha value other : ℝ) :
    unitEndpointStretch alpha value other - unitEndpointStretch alpha other value =
      signedEndpointGapStretch alpha (value - other) := by
  rcases lt_trichotomy value other with hlt | rfl | hgt
  · have hgap : value - other < 0 := sub_neg.mpr hlt
    simp only [unitEndpointStretch, hlt, not_lt_of_gt hlt, ite_true, ite_false,
      signedEndpointGapStretch, not_lt_of_gt hgap, hgap]
    ring
  · simp
  · have hgap : 0 < value - other := sub_pos.mpr hgt
    simp only [unitEndpointStretch, hgt, not_lt_of_gt hgt, ite_true, ite_false,
      signedEndpointGapStretch, hgap]
    ring

theorem signedEndpointGapStretch_neg (alpha gap : ℝ) :
    signedEndpointGapStretch alpha (-gap) = -signedEndpointGapStretch alpha gap := by
  have h := unitEndpointStretch_sub_reverse alpha 0 gap
  have hreverse := unitEndpointStretch_sub_reverse alpha gap 0
  simp only [zero_sub, sub_zero] at h hreverse
  linarith

/-- Endpoint stretching preserves the interval `[-1,1]`. -/
theorem unitEndpointStretch_mem_Icc {alpha value other : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hvalue : value ∈ Set.Icc (-1 : ℝ) 1) :
    unitEndpointStretch alpha value other ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases hvalue with ⟨hlower, hupper⟩
  unfold unitEndpointStretch
  split_ifs
  · constructor <;> nlinarith
  · constructor <;> nlinarith
  · exact ⟨hlower, hupper⟩

/-- The displacement estimate concerns the constructed stretched endpoint. -/
theorem abs_unitEndpointStretch_sub_le {alpha value other : ℝ}
    (halpha0 : 0 ≤ alpha)
    (hvalue : value ∈ Set.Icc (-1 : ℝ) 1) :
    |unitEndpointStretch alpha value other - value| ≤ 2 * alpha := by
  rcases hvalue with ⟨hlower, hupper⟩
  unfold unitEndpointStretch
  split_ifs
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith
  · simp only [sub_self, abs_zero]
    linarith

theorem signedEndpointGapStretch_pos_iff {alpha gap : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    0 < signedEndpointGapStretch alpha gap ↔ 0 < gap := by
  rcases lt_trichotomy gap 0 with hnegative | rfl | hpositive
  · have hvalue : signedEndpointGapStretch alpha gap < 0 := by
      rw [signedEndpointGapStretch, ite_eq_right (not_lt_of_gt hnegative), ite_eq_left hnegative]
      by_cases ha : alpha = 0
      · simp [ha, hnegative]
      · have ha : 0 < alpha := lt_of_le_of_ne halpha0 (Ne.symm ha)
        nlinarith
    exact iff_of_false (not_lt_of_gt hvalue) (not_lt_of_gt hnegative)
  · simp
  · have hvalue : 0 < signedEndpointGapStretch alpha gap := by
      rw [signedEndpointGapStretch, ite_eq_left hpositive]
      by_cases ha : alpha = 0
      · simp [ha, hpositive]
      · have ha : 0 < alpha := lt_of_le_of_ne halpha0 (Ne.symm ha)
        nlinarith
    exact iff_of_true hvalue hpositive

theorem signedEndpointGapStretch_neg_iff {alpha gap : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    signedEndpointGapStretch alpha gap < 0 ↔ gap < 0 := by
  have h := signedEndpointGapStretch_pos_iff (gap := -gap) halpha0 halpha1
  rw [signedEndpointGapStretch_neg] at h
  simpa only [neg_pos] using h

theorem signedEndpointGapStretch_nonneg_iff {alpha gap : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    0 ≤ signedEndpointGapStretch alpha gap ↔ 0 ≤ gap := by
  simpa only [not_lt] using
    not_congr (signedEndpointGapStretch_neg_iff (gap := gap) halpha0 halpha1)

theorem signedEndpointGapStretch_eq_zero_iff {alpha gap : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    signedEndpointGapStretch alpha gap = 0 ↔ gap = 0 := by
  constructor
  · intro heq
    apply le_antisymm
    · by_contra hnot
      have hpos := (signedEndpointGapStretch_pos_iff halpha0 halpha1).2
        (lt_of_not_ge hnot)
      linarith
    · exact (signedEndpointGapStretch_nonneg_iff halpha0 halpha1).1 (by rw [heq])
  · rintro rfl
    exact signedEndpointGapStretch_zero alpha

/-- Every nonnegative unit-pair gap weakly expands. -/
theorem le_signedEndpointGapStretch {alpha gap : ℝ}
    (halpha0 : 0 ≤ alpha) (hgap0 : 0 ≤ gap) (hgap2 : gap ≤ 2) :
    gap ≤ signedEndpointGapStretch alpha gap := by
  rcases eq_or_lt_of_le hgap0 with heq | hpositive
  · subst gap
    simp
  · rw [signedEndpointGapStretch, ite_eq_left hpositive]
    nlinarith

/-- A positive stretch fixes precisely zero and saturated nonnegative gaps. -/
theorem signedEndpointGapStretch_eq_self_iff_of_nonneg {alpha gap : ℝ}
    (halpha : 0 < alpha) (hgap0 : 0 ≤ gap) :
    signedEndpointGapStretch alpha gap = gap ↔ gap = 0 ∨ gap = 2 := by
  rcases eq_or_lt_of_le hgap0 with heq | hpositive
  · subst gap
    simp
  · rw [signedEndpointGapStretch, ite_eq_left hpositive]
    constructor
    · intro heq
      right
      nlinarith
    · rintro (rfl | rfl)
      · linarith
      · ring

/-- The signed fixed gaps of any strictly positive stretch are minus two, zero, and two. -/
theorem signedEndpointGapStretch_eq_self_iff {alpha gap : ℝ}
    (halpha : 0 < alpha) :
    signedEndpointGapStretch alpha gap = gap ↔ gap = -2 ∨ gap = 0 ∨ gap = 2 := by
  by_cases hgap0 : 0 ≤ gap
  · rw [signedEndpointGapStretch_eq_self_iff_of_nonneg halpha hgap0]
    constructor
    · exact Or.inr
    · rintro (hnegative | hzero | htwo)
      · linarith
      · exact Or.inl hzero
      · exact Or.inr htwo
  · have hnegative : gap < 0 := lt_of_not_ge hgap0
    have h := signedEndpointGapStretch_eq_self_iff_of_nonneg
      (gap := -gap) halpha (by linarith)
    rw [signedEndpointGapStretch_neg, neg_inj] at h
    constructor
    · intro heq
      rcases h.mp heq with hzero | htwo
      · right; left; linarith
      · left; linarith
    · rintro (hminus | hzero | htwo)
      · apply h.mpr
        right
        linarith
      · linarith
      · linarith

theorem signedEndpointGapStretch_pos_iff_of_abs_le_two {alpha gap : ℝ}
    (halpha : 0 ≤ alpha) (hgap : |gap| ≤ 2) :
    0 < signedEndpointGapStretch alpha gap ↔ 0 < gap := by
  rcases abs_le.mp hgap with ⟨hlower, hupper⟩
  rcases lt_trichotomy gap 0 with hnegative | rfl | hpositive
  · have hexpand := le_signedEndpointGapStretch (gap := -gap)
      halpha (by linarith) (by linarith)
    rw [signedEndpointGapStretch_neg] at hexpand
    have hstretched : signedEndpointGapStretch alpha gap < 0 := by linarith
    exact iff_of_false (not_lt_of_gt hstretched) (not_lt_of_gt hnegative)
  · simp
  · exact iff_of_true
      (hpositive.trans_le (le_signedEndpointGapStretch halpha hpositive.le hupper)) hpositive

theorem signedEndpointGapStretch_neg_iff_of_abs_le_two {alpha gap : ℝ}
    (halpha : 0 ≤ alpha) (hgap : |gap| ≤ 2) :
    signedEndpointGapStretch alpha gap < 0 ↔ gap < 0 := by
  have h := signedEndpointGapStretch_pos_iff_of_abs_le_two
    (gap := -gap) halpha (by rwa [abs_neg])
  rw [signedEndpointGapStretch_neg] at h
  simpa only [neg_pos] using h

theorem signedEndpointGapStretch_at_quarter_zero_one_two :
    signedEndpointGapStretch ((1 : ℝ) / 4) 0 = 0 ∧
      signedEndpointGapStretch ((1 : ℝ) / 4) 1 = (5 : ℝ) / 4 ∧
      signedEndpointGapStretch ((1 : ℝ) / 4) 2 = 2 := by
  norm_num [signedEndpointGapStretch]

/-- A zero stretch fixes a strictly intermediate gap, so saturation needs positive stretch. -/
theorem signedEndpointGapStretch_zero_fixes_nonsaturated_one :
    signedEndpointGapStretch 0 1 = 1 ∧ (1 : ℝ) ≠ 0 ∧ (1 : ℝ) ≠ 2 := by
  norm_num [signedEndpointGapStretch]

/-- The supplied signed two-atom mean decreases despite its positive original value. -/
theorem signedEndpointGapStretch_two_atom_signed_mean (alpha : ℝ) :
    (2 : ℝ) / 5 * 2 + (3 : ℝ) / 5 * (-(1 : ℝ) / 2) = (1 : ℝ) / 2 ∧
      (2 : ℝ) / 5 * signedEndpointGapStretch alpha 2 +
        (3 : ℝ) / 5 * signedEndpointGapStretch alpha (-(1 : ℝ) / 2) =
          (1 : ℝ) / 2 - 9 * alpha / 10 := by
  constructor
  · norm_num
  · norm_num [signedEndpointGapStretch]
    ring

theorem signedEndpointGapStretch_two_atom_signed_mean_lt_original {alpha : ℝ}
    (halpha : 0 < alpha) :
    (2 : ℝ) / 5 * signedEndpointGapStretch alpha 2 +
      (3 : ℝ) / 5 * signedEndpointGapStretch alpha (-(1 : ℝ) / 2) < (1 : ℝ) / 2 := by
  rw [(signedEndpointGapStretch_two_atom_signed_mean alpha).2]
  linarith

/-- The positive denominator used by the common affine-row reselection.
Its positivity holds throughout the source parameter range, before comparing
the original reversing-row value with the minimum. -/
theorem signedEndpointGapStretch_reselection_denominator_pos {alpha m p : ℝ}
    (halpha : 0 < alpha) (halpham : alpha < m / 4) (hp : 0 < p) :
    0 < m + 2 * alpha * (2 * p - 1) := by
  have hproduct := mul_pos halpha hp
  nlinarith

/-- The strict rational comparison numerator remains positive for the entire
parameter range, including both same-root comparison branches. -/
theorem signedEndpointGapStretch_reselection_numerator_pos {alpha m p : ℝ}
    (hmhalf : m < 1 / 2)
    (halpha : 0 < alpha) (halpham : alpha < m / 4)
    (hp : 0 < p) :
    0 < m * (2 - m - 6 * p * (1 - p)) +
      2 * alpha * p * ((4 - 3 * m) * p + 2 * m - 2) := by
  have hm : 0 < m := by linarith
  let coefficient := (4 - 3 * m) * p + 2 * m - 2
  have hbase : 0 < 2 - m - 6 * p * (1 - p) := by
    nlinarith [sq_nonneg (p - 1 / 2)]
  by_cases hcoefficient : 0 ≤ coefficient
  · have hfirst := mul_pos hm hbase
    have hsecond := mul_nonneg (mul_nonneg (by linarith : 0 ≤ 2 * alpha) hp.le)
      hcoefficient
    dsimp only [coefficient] at hsecond
    linarith
  · have hcoefficient : coefficient < 0 := lt_of_not_ge hcoefficient
    have hphalf : p < 1 / 2 := by
      by_contra hnot
      have hslope : 0 ≤ 4 - 3 * m := by linarith
      have hproduct := mul_nonneg hslope (sub_nonneg.mpr (le_of_not_gt hnot))
      dsimp only [coefficient] at hcoefficient
      nlinarith
    let displacement := 1 / 2 - p
    have hdisplacement : 0 < displacement := sub_pos.mpr hphalf
    have hidentity :
        (2 - m - 6 * p * (1 - p)) + p * coefficient / 2 -
          (2 * displacement - 1 / 4) ^ 2 =
        (7 / 8) * (1 / 2 - m) + (m / 2) * displacement +
          (4 - 3 * m / 2) * displacement ^ 2 := by
      dsimp only [coefficient, displacement]
      ring
    have hpositive : 0 < (7 / 8) * (1 / 2 - m) := by positivity
    have hlinear : 0 ≤ (m / 2) * displacement := by positivity
    have hquadratic : 0 ≤ (4 - 3 * m / 2) * displacement ^ 2 := by
      apply mul_nonneg (by linarith) (sq_nonneg _)
    have hlower : 0 < (2 - m - 6 * p * (1 - p)) + p * coefficient / 2 := by
      nlinarith only [hidentity, hpositive, hlinear, hquadratic,
        sq_nonneg (2 * displacement - 1 / 4)]
    have hscaled := mul_pos hm hlower
    have hnegative := mul_neg_of_pos_of_neg hp hcoefficient
    have hterm := mul_lt_mul_of_neg_right
      (show 2 * alpha < m / 2 by linarith) hnegative
    dsimp only [coefficient] at hscaled hterm
    nlinarith only [hscaled, hterm]

/-- Clearing only positive denominators reduces the coherent-row protection
bound to the strictly positive numerator above. -/
theorem signedEndpointGapStretch_reselection_crossProduct_lt {alpha m p : ℝ}
    (hmhalf : m < 1 / 2)
    (halpha : 0 < alpha) (halpham : alpha < m / 4) (hp : 0 < p) :
    (m + 2 * alpha * (2 * p - 1) - (1 - p) * m * (1 - alpha)) *
        (m - 2 * alpha * p) <
      m * p * (1 - alpha) * (m + 2 * alpha * (2 * p - 1)) := by
  have hpositive := mul_pos halpha
    (signedEndpointGapStretch_reselection_numerator_pos hmhalf halpha halpham hp)
  have hidentity :
      m * p * (1 - alpha) * (m + 2 * alpha * (2 * p - 1)) -
        (m + 2 * alpha * (2 * p - 1) - (1 - p) * m * (1 - alpha)) *
          (m - 2 * alpha * p) =
      alpha * (m * (2 - m - 6 * p * (1 - p)) +
        2 * alpha * p * ((4 - 3 * m) * p + 2 * m - 2)) := by ring
  linarith

end Math
