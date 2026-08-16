/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# Elementary periodicity lemmas
-/

namespace Math

/-- A sequence with a positive additive period has finite range. -/
theorem finite_range_of_add_period {α : Type*} (sequence : ℕ → α)
    (period : ℕ) (hperiodPos : 0 < period)
    (hperiod : ∀ n, sequence (n + period) = sequence n) :
    Set.Finite (Set.range sequence) := by
  have hremainder : ∀ n, ∃ r < period, sequence n = sequence r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hn : n < period
        · exact ⟨n, hn, rfl⟩
        · let earlier := n - period
          have hearlier : earlier < n := by
            dsimp [earlier]
            omega
          obtain ⟨r, hr, her⟩ := ih earlier hearlier
          refine ⟨r, hr, ?_⟩
          have hnEq : earlier + period = n := by
            dsimp [earlier]
            omega
          rw [← hnEq, hperiod earlier]
          exact her
  have hfiniteDomain : Set.Finite (↑(Finset.range period) : Set ℕ) :=
    Finset.finite_toSet _
  refine (hfiniteDomain.image sequence).subset ?_
  rintro value ⟨n, rfl⟩
  obtain ⟨r, hr, heq⟩ := hremainder n
  refine ⟨r, ?_, heq.symm⟩
  simpa using hr

/-! ## Exact rational rates on finite orbits -/

/-- If `k * b = a * L` and `a` is coprime to `b`, then `b` divides `L`.
No periodic sequence or counting presentation is needed for this arithmetic
core. -/
theorem denominator_dvd_of_coprime_cross_mul
    (k a b L : ℕ) (hrate : k * b = a * L)
    (hcoprime : Nat.Coprime a b) :
    b ∣ L := by
  have hdvd : b ∣ a * L := ⟨k, by rw [← hrate]; ring⟩
  exact hcoprime.symm.dvd_of_dvd_mul_left hdvd

/-- Rational-density formulation of
`denominator_dvd_of_coprime_cross_mul`. -/
theorem denominator_dvd_of_rational_eq
    (k a b L : ℕ) (hL : 0 < L) (hb : 0 < b)
    (hrate : (k : ℚ) / (L : ℚ) = (a : ℚ) / (b : ℚ))
    (hcoprime : Nat.Coprime a b) :
    b ∣ L := by
  have hLQ : (L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hcross : (k : ℚ) * (b : ℚ) = (a : ℚ) * (L : ℚ) :=
    (div_eq_div_iff hLQ hbQ).mp hrate
  have hcrossN : k * b = a * L := by exact_mod_cast hcross
  exact denominator_dvd_of_coprime_cross_mul k a b L hcrossN hcoprime

/-- An injective deterministic controller on `Fin n` has a positive pure
orbit period at most `n`. -/
theorem exists_orbit_period {n : ℕ} (f : Fin n → Fin n) (o : Fin n → Bool)
    (s : Fin n) (hf : Function.Injective f) :
    ∃ L, 0 < L ∧ L ≤ n ∧ Function.Periodic (fun i => o (f^[i] s)) L := by
  obtain ⟨x, y, hxy, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun m : Fin (n + 1) => f^[(m : ℕ)] s) (by simp)
  have hvalne : (x : ℕ) ≠ (y : ℕ) := fun he => hxy (Fin.ext he)
  have build : ∀ i j : ℕ, i < j → j ≤ n → f^[i] s = f^[j] s →
      ∃ L, 0 < L ∧ L ≤ n ∧
        Function.Periodic (fun t => o (f^[t] s)) L := by
    intro i j hij hjn heq
    refine ⟨j - i, by omega, by omega, ?_⟩
    have hji : i + (j - i) = j := by omega
    have hcomm : f^[j] s = f^[i] (f^[j - i] s) := by
      have h := Function.iterate_add_apply f i (j - i) s
      rwa [hji] at h
    have heq2 : f^[i] s = f^[i] (f^[j - i] s) := by rw [heq, hcomm]
    have hcancel : f^[j - i] s = s := ((hf.iterate i) heq2).symm
    intro t
    change o (f^[t + (j - i)] s) = o (f^[t] s)
    rw [Function.iterate_add_apply, hcancel]
  rcases lt_or_gt_of_ne hvalne with hlt | hgt
  · exact build (x : ℕ) (y : ℕ) hlt (by omega) hg
  · exact build (y : ℕ) (x : ℕ) hgt (by omega) hg.symm

/-- An exact reduced rate on a positive orbit window of length at most the
controller state count has denominator at most that state count.  Pair this
with `exists_orbit_period` when the window is a period of an injective
controller. -/
theorem denominator_le_card_of_orbit_window_rate
    {n : ℕ} (f : Fin n → Fin n) (o : Fin n → Bool) (s : Fin n)
    (L : ℕ) (hL : 0 < L) (hLn : L ≤ n) (a b : ℕ)
    (hrate : ((Finset.range L).filter (fun i => o (f^[i] s))).card * b =
      a * L)
    (hcoprime : Nat.Coprime a b) :
    b ≤ n := by
  have hdvd : b ∣ L :=
    denominator_dvd_of_coprime_cross_mul
      ((Finset.range L).filter (fun i => o (f^[i] s))).card
      a b L hrate hcoprime
  exact (Nat.le_of_dvd hL hdvd).trans hLn

end Math
