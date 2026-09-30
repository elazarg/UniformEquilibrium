import Mathlib.Algebra.BigOperators.Fin
import MathUE.CyclicContraction

/-!
# Chronological indexing for variable-length finite cycles

The standard `finSigmaFinEquiv` orders blocks by their coarse `Fin` index and
then orders dates within each block. These lemmas retain that chronological
order when a periodic compiler rotates the flattened index.
-/

noncomputable section

open scoped BigOperators

namespace Math

variable {L : ℕ}

/-- Number of dates before the first `k` blocks. -/
def finVariablePrefix (length : Fin L → ℕ) (k : ℕ) (hk : k ≤ L) : ℕ :=
  ∑ p : Fin k, length (Fin.castLE hk p)

@[simp] theorem finVariablePrefix_zero (length : Fin L → ℕ) :
    finVariablePrefix length 0 (Nat.zero_le L) = 0 := by
  simp [finVariablePrefix]

@[simp] theorem finVariablePrefix_total (length : Fin L → ℕ) :
    finVariablePrefix length L le_rfl = ∑ p, length p := by
  simp [finVariablePrefix]

theorem finVariablePrefix_succ (length : Fin L → ℕ) (k : ℕ) (hk : k + 1 ≤ L) :
    finVariablePrefix length (k + 1) hk =
      finVariablePrefix length k (by omega) + length ⟨k, by omega⟩ := by
  unfold finVariablePrefix
  rw [Fin.sum_univ_castSucc]
  rfl

/-- Coarse block and local date in the canonical chronological ordering. -/
def finVariablePhase (length : Fin L → ℕ) (p : Fin L) (l : Fin (length p)) :
    Fin (∑ p, length p) :=
  finSigmaFinEquiv ⟨p, l⟩

/-- Equal block lengths transport the same chronological phase and local date. -/
theorem finVariablePhase_cast {n m : Fin L → ℕ} (h : n = m)
    (phase : Fin L) (localDate : Fin (n phase)) :
    Fin.cast (congrArg (fun length => ∑ phase, length phase) h)
        (finVariablePhase n phase localDate) =
      finVariablePhase m phase (Fin.cast (congrFun h phase) localDate) := by
  subst m
  rfl

theorem finVariablePhase_val (length : Fin L → ℕ) (p : Fin L)
    (l : Fin (length p)) :
    (finVariablePhase length p l).val =
      finVariablePrefix length p.val p.isLt.le + l.val := by
  exact finSigmaFinEquiv_apply ⟨p, l⟩

theorem finRotate_finVariablePhase_inside (length : Fin L → ℕ)
    (p : Fin L) (l : Fin (length p)) (hl : l.val + 1 < length p) :
    finRotate (∑ p, length p) (finVariablePhase length p l) =
      finVariablePhase length p ⟨l.val + 1, hl⟩ := by
  apply Fin.eq_of_val_eq
  rw [val_finRotate, finVariablePhase_val, finVariablePhase_val]
  have hnext := (finVariablePhase length p ⟨l.val + 1, hl⟩).isLt
  rw [finVariablePhase_val] at hnext
  change finVariablePrefix length p.val p.isLt.le + (l.val + 1) <
    ∑ p, length p at hnext
  change (finVariablePrefix length p.val p.isLt.le + l.val + 1) % (∑ p, length p) =
    finVariablePrefix length p.val p.isLt.le + (l.val + 1)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Final dates advance to the next coarse block; the last block wraps to zero. -/
theorem finRotate_finVariablePhase_boundary (length : Fin L → ℕ)
    (hpositive : ∀ p, 0 < length p) (p : Fin L) (l : Fin (length p))
    (hl : l.val + 1 = length p) :
    finRotate (∑ p, length p) (finVariablePhase length p l) =
      finVariablePhase length (finRotate L p)
        ⟨0, hpositive (finRotate L p)⟩ := by
  apply Fin.eq_of_val_eq
  rw [val_finRotate, finVariablePhase_val, finVariablePhase_val]
  have hp : p.val + 1 ≤ L := p.isLt
  have hprefix := finVariablePrefix_succ length p.val hp
  change finVariablePrefix length (p.val + 1) hp =
    finVariablePrefix length p.val p.isLt.le + length p at hprefix
  by_cases hlast : p.val + 1 = L
  · have hrotate : finRotate L p = ⟨0, by omega⟩ := by
      apply Fin.eq_of_val_eq
      rw [val_finRotate, hlast, Nat.mod_self]
    rw [hrotate]
    simp only [finVariablePrefix_zero, add_zero]
    have htotal : finVariablePrefix length p.val p.isLt.le + length p =
        ∑ p, length p := by
      rw [← hprefix]
      simpa only [hlast] using finVariablePrefix_total length
    rw [show finVariablePrefix length p.val p.isLt.le + l.val + 1 =
      ∑ p, length p by omega, Nat.mod_self]
  · have hnext : p.val + 1 < L := by omega
    have hrotate : finRotate L p = ⟨p.val + 1, hnext⟩ := by
      apply Fin.eq_of_val_eq
      rw [val_finRotate, Nat.mod_eq_of_lt hnext]
    rw [hrotate]
    simp only [add_zero]
    have hbound :=
      (finVariablePhase length ⟨p.val + 1, hnext⟩
        ⟨0, hpositive ⟨p.val + 1, hnext⟩⟩).isLt
    rw [finVariablePhase_val] at hbound
    change finVariablePrefix length (p.val + 1) hnext.le + 0 <
      ∑ p, length p at hbound
    simp only [add_zero] at hbound
    rw [hprefix] at hbound ⊢
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Products factor into the chronological coarse blocks. -/
theorem prod_finVariablePhase {A : Type*} [CommMonoid A]
    (length : Fin L → ℕ) (factor : Fin (∑ p, length p) → A) :
    (∏ phase, factor phase) =
      ∏ p, ∏ l, factor (finVariablePhase length p l) := by
  rw [← finSigmaFinEquiv.prod_comp factor, Fintype.prod_sigma]
  rfl

end Math
