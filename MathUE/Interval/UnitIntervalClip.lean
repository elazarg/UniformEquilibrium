import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!

# Fixed points of a clipped scalar displacement

The three closed-unit-interval face conditions retain weak boundary signs.
-/

namespace Math
namespace UnitIntervalClip

/-- All three face conditions, with weak signs on both boundary faces. -/
theorem clipped_unitInterval_add_eq_self_iff {x displacement : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    min 1 (max 0 (x + displacement)) = x ↔
      (x = 0 → displacement ≤ 0) ∧
      (0 < x → x < 1 → displacement = 0) ∧
      (x = 1 → 0 ≤ displacement) := by
  by_cases hzero : x = 0
  · subst x
    constructor
    · intro h
      have hd : displacement ≤ 0 := by
        by_contra hn
        have hp : 0 < min (1 : ℝ) (max 0 displacement) :=
          lt_min zero_lt_one (lt_max_of_lt_right (lt_of_not_ge hn))
        simp only [zero_add] at h
        linarith
      exact ⟨fun _ => hd, by simp, by simp⟩
    · rintro ⟨h, _, _⟩
      simp [max_eq_left (h rfl)]
  by_cases hone : x = 1
  · subst x
    constructor
    · intro h
      have hd : 0 ≤ displacement := by
        have hm : (1 : ℝ) ≤ max 0 (1 + displacement) := by
          calc
            1 = min 1 (max 0 (1 + displacement)) := h.symm
            _ ≤ max 0 (1 + displacement) := min_le_right _ _
        rcases le_max_iff.mp hm with hz | hd
        · norm_num at hz
        · linarith
      exact ⟨by simp, by simp, fun _ => hd⟩
    · rintro ⟨_, _, h⟩
      apply min_eq_left
      exact (by linarith [h rfl] : (1 : ℝ) ≤ 1 + displacement).trans (le_max_right _ _)
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hzero)
  have hxlt : x < 1 := lt_of_le_of_ne hx1 hone
  constructor
  · intro h
    have hsumpos : 0 < x + displacement := by
      by_contra hn
      rw [max_eq_left (le_of_not_gt hn), min_eq_right zero_le_one] at h
      linarith
    have hsumlt : x + displacement < 1 := by
      by_contra hn
      rw [max_eq_right hsumpos.le,
        min_eq_left (le_of_not_gt hn)] at h
      linarith
    rw [max_eq_right hsumpos.le, min_eq_right hsumlt.le] at h
    exact ⟨fun hz => (hzero hz).elim, fun _ _ => by linarith,
      fun ho => (hone ho).elim⟩
  · rintro ⟨_, h, _⟩
    rw [h hxpos hxlt, add_zero, max_eq_right hx0, min_eq_right hx1]

end UnitIntervalClip
end Math
