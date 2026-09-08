import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring

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
    simp only [unitEndpointStretch, hlt, not_lt_of_gt hlt, if_true, if_false,
      signedEndpointGapStretch, not_lt_of_gt hgap, hgap]
    ring
  · simp
  · have hgap : 0 < value - other := sub_pos.mpr hgt
    simp only [unitEndpointStretch, hgt, not_lt_of_gt hgt, if_true, if_false,
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
      rw [signedEndpointGapStretch, if_neg (not_lt_of_gt hnegative), if_pos hnegative]
      by_cases ha : alpha = 0
      · simp [ha, hnegative]
      · have ha : 0 < alpha := lt_of_le_of_ne halpha0 (Ne.symm ha)
        nlinarith
    exact iff_of_false (not_lt_of_gt hvalue) (not_lt_of_gt hnegative)
  · simp
  · have hvalue : 0 < signedEndpointGapStretch alpha gap := by
      rw [signedEndpointGapStretch, if_pos hpositive]
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
  · rw [signedEndpointGapStretch, if_pos hpositive]
    nlinarith

/-- A positive stretch fixes precisely zero and saturated nonnegative gaps. -/
theorem signedEndpointGapStretch_eq_self_iff_of_nonneg {alpha gap : ℝ}
    (halpha : 0 < alpha) (hgap0 : 0 ≤ gap) :
    signedEndpointGapStretch alpha gap = gap ↔ gap = 0 ∨ gap = 2 := by
  rcases eq_or_lt_of_le hgap0 with heq | hpositive
  · subst gap
    simp
  · rw [signedEndpointGapStretch, if_pos hpositive]
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

end Math
