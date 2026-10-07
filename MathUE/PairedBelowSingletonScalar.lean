import MathUE.CubicAnchorRoot
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The selected scalar root and passive cap for below-singleton pairs

The root is produced in the strict interval needed for the passive inequality.
No claim is made for other proper roots of the same cubic.
-/

noncomputable section

namespace Math.PairedBelowSingleton

def polynomial (favorable premium passive t : ℝ) : ℝ :=
  cubicAnchor (-(premium + 1)) passive (favorable - 1 - passive) premium t

theorem exists_selected_root {favorable premium passive : ℝ}
    (hfavorable : 2 < favorable)
    (hpassive : passive < (7 * premium + 10 - 2 * favorable) / 2) :
    ∃ t ∈ Set.Ioo (1 / 2 : ℝ) 1, polynomial favorable premium passive t = 0 := by
  have hleft : polynomial favorable premium passive (1 / 2) < 0 := by
    unfold polynomial cubicAnchor
    norm_num
    linarith
  have hright : 0 < polynomial favorable premium passive 1 := by
    unfold polynomial cubicAnchor
    norm_num
    linarith
  exact exists_cubicAnchor_root_mem_Ioo_of_neg_of_pos
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hleft hright

theorem passive_continue_identity {favorable premium passive t : ℝ}
    (ht : 0 < t) (hroot : polynomial favorable premium passive t = 0) :
    (1 - t) * t * (favorable - 1) + (1 - t) ^ 2 * passive +
        t ^ 2 * (1 - t) * premium = (1 - t) * (premium + 1) / t := by
  apply (eq_div_iff ht.ne').2
  calc
    ((1 - t) * t * (favorable - 1) + (1 - t) ^ 2 * passive +
        t ^ 2 * (1 - t) * premium) * t =
        (1 - t) * (premium + 1) + (1 - t) * polynomial favorable premium passive t := by
      unfold polynomial cubicAnchor
      ring
    _ = _ := by rw [hroot]; ring

theorem passive_cap_lt_post {premium t b : ℝ} (singleton : ℝ)
    (hpremium : premium < -1) (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1) (hb : 0 < b) :
    t ^ 2 * singleton + (1 - t ^ 2) * (singleton - (4 * (-premium - 1) / 3) * b) <
      singleton + (1 - t) * (premium + 1) * b / t := by
  have htpositive : 0 < t := by linarith [ht.1]
  have hfactor : 0 < 4 * t ^ 2 + 4 * t - 3 := by
    have hproduct : 0 < (2 * t - 1) * (2 * t + 3) :=
      mul_pos (by linarith [ht.1]) (by linarith [ht.1])
    nlinarith
  have hpositive : 0 < (1 - t) * b * (-premium - 1) *
      (4 * t ^ 2 + 4 * t - 3) / 3 := by
    exact div_pos (mul_pos (mul_pos (mul_pos (by linarith [ht.2]) hb)
      (by linarith)) hfactor) (by norm_num)
  have hidentity : t *
      ((singleton + (1 - t) * (premium + 1) * b / t) -
        (t ^ 2 * singleton + (1 - t ^ 2) *
          (singleton - (4 * (-premium - 1) / 3) * b))) =
      (1 - t) * b * (-premium - 1) * (4 * t ^ 2 + 4 * t - 3) / 3 := by
    field_simp
    ring
  by_contra hnot
  have hgap : (singleton + (1 - t) * (premium + 1) * b / t) -
      (t ^ 2 * singleton + (1 - t ^ 2) *
        (singleton - (4 * (-premium - 1) / 3) * b)) ≤ 0 :=
    sub_nonpos.mpr (le_of_not_gt hnot)
  have hmul := mul_nonpos_of_nonneg_of_nonpos htpositive.le hgap
  linarith [hidentity, hpositive]

end Math.PairedBelowSingleton
