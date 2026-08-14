/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ThreePlayer.SharedPunishmentThreePlayer

/-!
# The sharp cyclic exposure bound

This is a game-free core extracted from
`QuittingSharedPunishmentThreePlayer.lean`.  If `x i` is the probability that
player `i` quits, the directed cyclic bad event for `i` has probability

`x (next i) * (1 - x (prev i))`.

For every finite nonempty collection of coordinates with mutually inverse
neighbour maps, some bad-event probability is at most `1 / 4`.  The constant
is sharp at the fair row.  The proof deliberately needs neither a single
orbit nor lower bounds on the orbit length: the useful statement is therefore
available for each component of any finite permutation.
-/

noncomputable section

namespace GameTheory.Experiments

open scoped BigOperators

/-- Two cyclic neighbour maps.  The two inverse laws make `next` a
permutation; the exposure result below uses only `prev (next i) = i`. -/
structure CyclicNeighbours (ι : Type) where
  next : ι → ι
  prev : ι → ι
  prev_next : Function.LeftInverse prev next
  next_prev : Function.RightInverse prev next

namespace CyclicNeighbours

variable {ι : Type} (C : CyclicNeighbours ι)

/-- The permutation induced by `next`. -/
def nextEquiv : ι ≃ ι where
  toFun := C.next
  invFun := C.prev
  left_inv := C.prev_next
  right_inv := C.next_prev

/-- The product that occurs when a player quits immediately in the directed
cyclic shared-punishment table. -/
def exposure (x : ι → ℝ) (i : ι) : ℝ :=
  x (C.next i) * (1 - x (C.prev i))

/-- The elementary quadratic fence behind the sharp constant. -/
theorem selfExposure_le_quarter (z : ℝ) :
    z * (1 - z) ≤ (1 / 4 : ℝ) := by
  nlinarith [sq_nonneg (z - 1 / 2)]

/-- An argmax of the quitting marginals gives a good cyclic coordinate one
step ahead.  This is the local, non-finite form of the product bound. -/
theorem exposure_successor_argmax_le_quarter
    (x : ι → ℝ) (hunit : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (k : ι) (hmax : ∀ j, x j ≤ x k) :
    C.exposure x (C.next k) ≤ (1 / 4 : ℝ) := by
  have hprev : C.prev (C.next k) = k := C.prev_next k
  have hnonneg : 0 ≤ 1 - x k := by linarith [(hunit k).2]
  calc
    C.exposure x (C.next k) =
        x (C.next (C.next k)) * (1 - x k) := by
          simp only [exposure, hprev]
    _ ≤ x k * (1 - x k) := by
          exact mul_le_mul_of_nonneg_right (hmax (C.next (C.next k))) hnonneg
    _ ≤ (1 / 4 : ℝ) := selfExposure_le_quarter (x k)

/-- **Sharp finite directed-cycle product bound.**  For probabilities on a
finite nonempty cyclic coordinate system, at least one directed exposure is
at most one quarter. -/
theorem exists_exposure_le_quarter [Finite ι] [Nonempty ι]
    (x : ι → ℝ) (hunit : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ i, C.exposure x i ≤ (1 / 4 : ℝ) := by
  classical
  obtain ⟨k, hk⟩ := Finite.exists_max x
  exact ⟨C.next k,
    C.exposure_successor_argmax_le_quarter x hunit k hk⟩

/-- The fair row attains the bound at every coordinate, so `1/4` cannot be
improved in `exists_exposure_le_quarter`. -/
theorem exposure_fair (i : ι) :
    C.exposure (fun _ => (1 / 2 : ℝ)) i = (1 / 4 : ℝ) := by
  simp [exposure]
  norm_num

/-- A compact sharpness package: the universal upper bound on the best cyclic
coordinate and its fair-row equality witness. -/
theorem exists_exposure_le_quarter_sharp [Finite ι] [Nonempty ι]
    (x : ι → ℝ) (hunit : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    (∃ i, C.exposure x i ≤ (1 / 4 : ℝ)) ∧
      (∀ i, C.exposure (fun _ => (1 / 2 : ℝ)) i = (1 / 4 : ℝ)) := by
  exact ⟨C.exists_exposure_le_quarter x hunit, C.exposure_fair⟩

/-- If every cyclic exposure is at least one quarter, the row is fair.

The key intermediate fact is that the inequalities make `x` nondecreasing
under `next²`.  Since `next²` is a finite permutation, the sum of its
nonnegative coordinate increments is zero, hence every increment vanishes.
The exposure at `next i` then becomes the sharp scalar product
`x i * (1 - x i)`. -/
theorem eq_fair_of_forall_quarter_le_exposure [Finite ι] [Nonempty ι]
    (x : ι → ℝ) (hunit : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hall : ∀ i, (1 / 4 : ℝ) ≤ C.exposure x i) :
    x = fun _ => (1 / 2 : ℝ) := by
  classical
  obtain ⟨k, hkmax⟩ := Finite.exists_max x
  have hnonneg : 0 ≤ 1 - x k := by linarith [(hunit k).2]
  have htop : C.exposure x (C.next k) ≤ x k * (1 - x k) := by
    calc
      C.exposure x (C.next k) =
          x (C.next (C.next k)) * (1 - x k) := by
            rw [exposure, C.prev_next k]
      _ ≤ x k * (1 - x k) := by
            exact mul_le_mul_of_nonneg_right
              (hkmax (C.next (C.next k))) hnonneg
  have hkquarter : (1 / 4 : ℝ) ≤ x k * (1 - x k) :=
    (hall (C.next k)).trans htop
  have hkquad : x k * (1 - x k) ≤ (1 / 4 : ℝ) :=
    selfExposure_le_quarter (x k)
  have hkhalf : x k = (1 / 2 : ℝ) := by
    nlinarith [sq_nonneg (x k - 1 / 2)]
  have hlehalf : ∀ i, x i ≤ (1 / 2 : ℝ) := by
    intro i
    linarith [hkmax i]
  have hstep : ∀ i, x i ≤ x (C.next (C.next i)) := by
    intro i
    by_contra hnot
    have hlt : x (C.next (C.next i)) < x i := lt_of_not_ge hnot
    have hpos : 0 < 1 - x i := by linarith [hlehalf i]
    have hstrict :
        x (C.next (C.next i)) * (1 - x i) < x i * (1 - x i) :=
      mul_lt_mul_of_pos_right hlt hpos
    have hquad : x i * (1 - x i) ≤ (1 / 4 : ℝ) :=
      selfExposure_le_quarter (x i)
    have hbound : (1 / 4 : ℝ) ≤
        x (C.next (C.next i)) * (1 - x i) := by
      have h := hall (C.next i)
      rw [exposure, C.prev_next i] at h
      exact h
    linarith
  letI : Fintype ι := Fintype.ofFinite ι
  have hsumperm : (∑ i, x (C.next (C.next i))) = ∑ i, x i := by
    simpa [nextEquiv] using (C.nextEquiv.trans C.nextEquiv).sum_comp x
  have hsumzero : ∑ i, (x (C.next (C.next i)) - x i) = 0 := by
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hsumperm
  have hstepEq : ∀ i, x i = x (C.next (C.next i)) := by
    intro i
    have hzeros : (fun j => x (C.next (C.next j)) - x j) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg
        (fun j => sub_nonneg.mpr (hstep j))).mp hsumzero
    have hzero : x (C.next (C.next i)) - x i = 0 :=
      congrFun hzeros i
    exact (sub_eq_zero.mp hzero).symm
  funext i
  have hbound : (1 / 4 : ℝ) ≤ x i * (1 - x i) := by
    have h := hall (C.next i)
    rw [exposure, C.prev_next i, ← hstepEq i] at h
    exact h
  have hquad : x i * (1 - x i) ≤ (1 / 4 : ℝ) :=
    selfExposure_le_quarter (x i)
  nlinarith [sq_nonneg (x i - 1 / 2)]

/-- **Equality/optimizer core for the finite directed-cycle bound.**  All
cyclic bad-event probabilities are at least one quarter exactly at the fair
row.  Together with `exists_exposure_le_quarter`, this states that the fair
row maximizes the minimum exposure, with optimal value `1/4`. -/
theorem forall_quarter_le_exposure_iff_eq_fair [Finite ι] [Nonempty ι]
    (x : ι → ℝ) (hunit : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    (∀ i, (1 / 4 : ℝ) ≤ C.exposure x i) ↔
      x = fun _ => (1 / 2 : ℝ) := by
  constructor
  · exact C.eq_fair_of_forall_quarter_le_exposure x hunit
  · intro h
    subst x
    intro i
    rw [C.exposure_fair i]

end CyclicNeighbours

/-! ## Compatibility check: the existing three-player table -/

namespace ThreePlayerInstance

open QuittingSharedThreePlayer

/-- The `next` and `other` coordinates of the existing three-player cyclic
table are inverse neighbour maps. -/
def neighbours : CyclicNeighbours Player where
  next := next
  prev := other
  prev_next := by
    intro i
    cases i <;> rfl
  next_prev := by
    intro i
    cases i <;> rfl

/-- The arbitrary-finite core specializes exactly to the three products used
by `QuittingSharedPunishmentThreePlayer`. -/
theorem exists_bad_probability_le_quarter
    (x : Player → ℝ) (hunit : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ who, x (next who) * (1 - x (other who)) ≤ (1 / 4 : ℝ) := by
  simpa [neighbours, CyclicNeighbours.exposure] using
    (neighbours.exists_exposure_le_quarter x hunit)

end ThreePlayerInstance

end GameTheory.Experiments

/-! ## Evaluation audit -/
