import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponse

/-! # Face signs of the crossed auxiliary response map -/

noncomputable section

namespace GameTheory

open Set

variable {n : ℕ}

private theorem clipped_add_eq_self_iff
    {ceiling x displacement : ℝ} (hceiling : 0 < ceiling)
    (hx0 : 0 ≤ x) (hxc : x ≤ ceiling) :
    min ceiling (max 0 (x + displacement)) = x ↔
      (x = 0 → displacement ≤ 0) ∧
      (0 < x → x < ceiling → displacement = 0) ∧
      (x = ceiling → 0 ≤ displacement) := by
  by_cases hzero : x = 0
  · subst x
    constructor
    · intro h
      have hd : displacement ≤ 0 := by
        by_contra hn
        have hp : 0 < min ceiling (max 0 displacement) :=
          lt_min hceiling (lt_max_of_lt_right (lt_of_not_ge hn))
        simp only [zero_add] at h
        linarith
      exact ⟨fun _ => hd, fun hpos _ => (lt_irrefl (0 : ℝ) hpos).elim,
        fun heq => (hceiling.ne' heq.symm).elim⟩
    · rintro ⟨h, _, _⟩
      simp [max_eq_left (h rfl), hceiling.le]
  by_cases htop : x = ceiling
  · subst x
    constructor
    · intro h
      have hd : 0 ≤ displacement := by
        have hm : ceiling ≤ max 0 (ceiling + displacement) := by
          calc
            ceiling = min ceiling (max 0 (ceiling + displacement)) := h.symm
            _ ≤ max 0 (ceiling + displacement) := min_le_right _ _
        rcases le_max_iff.mp hm with hz | hd
        · linarith
        · linarith
      exact ⟨by simp [hceiling.ne'], by simp, fun _ => hd⟩
    · rintro ⟨_, _, h⟩
      apply min_eq_left
      exact (by linarith [h rfl] : ceiling ≤ ceiling + displacement).trans
        (le_max_right _ _)
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hzero)
  have hxlt : x < ceiling := lt_of_le_of_ne hxc htop
  constructor
  · intro h
    have hsumpos : 0 < x + displacement := by
      by_contra hn
      rw [max_eq_left (le_of_not_gt hn), min_eq_right hceiling.le] at h
      linarith
    have hsumlt : x + displacement < ceiling := by
      by_contra hn
      rw [max_eq_right hsumpos.le, min_eq_left (le_of_not_gt hn)] at h
      linarith
    rw [max_eq_right hsumpos.le, min_eq_right hsumlt.le] at h
    exact ⟨fun hz => (hzero hz).elim, fun _ _ => by linarith,
      fun ht => (htop ht).elim⟩
  · rintro ⟨_, h, _⟩
    rw [h hxpos hxlt, add_zero, max_eq_right hx0, min_eq_right hxc]

/-- A crossed fixed point has the correct weak face signs with respect to
the auxiliary ceiling; no original-game Nash condition is claimed here. -/
theorem quittingCrossedClippedMap_eq_self_iff
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ)
    (hheight : 0 < height) (hazard : Fin n → ℝ)
    (hzero : ∀ coordinate, 0 ≤ hazard coordinate)
    (hupper : ∀ coordinate,
      hazard coordinate ≤ quittingCrossedCeiling first second height coordinate) :
    quittingCrossedClippedMap reward first second height hazard = hazard ↔
      ∀ coordinate,
        (hazard coordinate = 0 →
          quittingCrossedResponse reward first second hazard coordinate ≤ 0) ∧
        (0 < hazard coordinate →
          hazard coordinate < quittingCrossedCeiling first second height coordinate →
          quittingCrossedResponse reward first second hazard coordinate = 0) ∧
        (hazard coordinate = quittingCrossedCeiling first second height coordinate →
          0 ≤ quittingCrossedResponse reward first second hazard coordinate) := by
  rw [funext_iff]
  exact forall_congr' fun coordinate => by
    have hceiling : 0 < quittingCrossedCeiling first second height coordinate := by
      unfold quittingCrossedCeiling
      split_ifs <;> positivity
    exact clipped_add_eq_self_iff hceiling (hzero coordinate) (hupper coordinate)

/-- Every crossed fixed point is in the displayed capped strategy box. -/
theorem quittingCrossedClippedMap_fixed_mem_box
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ)
    (hheight : 0 ≤ height)
    (hazard : Fin n → ℝ)
    (hfixed : quittingCrossedClippedMap reward first second height hazard = hazard) :
    ∀ coordinate, 0 ≤ hazard coordinate ∧
      hazard coordinate ≤ quittingCrossedCeiling first second height coordinate := by
  intro coordinate
  have h := congrFun hfixed coordinate
  dsimp [quittingCrossedClippedMap] at h
  rw [← h]
  constructor
  · apply le_min
    · unfold quittingCrossedCeiling
      split_ifs <;> linarith
    · exact le_max_left _ _
  · exact min_le_left _ _

end GameTheory
