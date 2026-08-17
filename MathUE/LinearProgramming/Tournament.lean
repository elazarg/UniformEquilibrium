/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.SingletonLCP

/-!
# Tournament matrices and the homogeneous LCP obstruction

This file records the part of the tournament argument which is independent of
quitting-game semantics.  A fractional tournament has nonnegative pair weights
which sum to one in opposite directions.  The matrix `t A - Aᵀ` therefore
has a quadratic form which is a positive multiple of the weighted pair sum
when `t > 1`.  Consequently a homogeneous simplex LCP solution can only have
singleton support; an exact outgoing edge rules out that support.

The results below prove homogeneous infeasibility and positive-right-hand-side
uniqueness.  They do not assert existence for arbitrary nonhomogeneous LCPs or
a standard-Q conclusion.
-/

noncomputable section

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι]

/-- A real-valued adjacency matrix for a tournament. -/
def IsFractionalTournament (A : ι → ι → ℝ) : Prop :=
  (∀ i, A i i = 0) ∧ (∀ i j, 0 ≤ A i j) ∧
    ∀ i j, i ≠ j → A i j + A j i = 1

/-- Every vertex has an outgoing edge of full unit weight. -/
def FractionalTournamentHasUnitOutneighbor (A : ι → ι → ℝ) : Prop :=
  ∀ i, ∃ j, i ≠ j ∧ A i j = 1

/-- The skew-dominant matrix associated with a fractional tournament. -/
def tournamentSkewMatrix (t : ℝ) (A : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i j => t * A i j - A j i

private theorem tournament_quadratic_identity
    (t : ℝ) (A : ι → ι → ℝ) (z : ι → ℝ) :
    (∑ i, z i * ∑ j, z j * tournamentSkewMatrix t A i j) =
      (t - 1) * ∑ i, ∑ j, z i * z j * A i j := by
  classical
  unfold tournamentSkewMatrix
  have hexpand :
      (∑ i, z i * ∑ j, z j * (t * A i j - A j i)) =
        t * (∑ i, ∑ j, z i * z j * A i j) -
          ∑ i, ∑ j, z i * z j * A j i := by
    have hfactor :
        (∑ i, ∑ j, t * (z i * z j * A i j)) =
          t * (∑ i, ∑ j, z i * z j * A i j) := by
      simp only [Finset.mul_sum]
    calc
      (∑ i, z i * ∑ j, z j * (t * A i j - A j i)) =
          (∑ i, ∑ j, t * (z i * z j * A i j)) -
            ∑ i, ∑ j, z i * z j * A j i := by
        simp_rw [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        · apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ = t * (∑ i, ∑ j, z i * z j * A i j) -
            ∑ i, ∑ j, z i * z j * A j i := by rw [hfactor]
  have htranspose :
      (∑ i, ∑ j, z i * z j * A j i) = ∑ i, ∑ j, z i * z j * A i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hexpand, htranspose]
  ring

/-- The tournament quadratic form is nonnegative for nonnegative vectors. -/
theorem tournamentSkewMatrix_quadratic_nonneg
    (t : ℝ) (A : ι → ι → ℝ) (hA : IsFractionalTournament A)
    (ht : 1 ≤ t) (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ ∑ i, z i * ∑ j, z j * tournamentSkewMatrix t A i j := by
  rw [tournament_quadratic_identity t A z]
  apply mul_nonneg (sub_nonneg.mpr ht)
  exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
    mul_nonneg (mul_nonneg (hz i) (hz j)) (hA.2.1 i j)

/-- The zero-weight conclusion for the positive-right-hand-side standard LCP,
stated directly over raw weights. -/
theorem positive_rhs_tournament_weight_eq_zero
    (t : ℝ) (A : ι → ι → ℝ) (hA : IsFractionalTournament A)
    (ht : 1 ≤ t) (d z : ι → ℝ) (hd : ∀ i, 0 < d i)
    (hz : ∀ i, 0 ≤ z i)
    (hcomp : ∀ i, z i * (d i + ∑ j,
      z j * tournamentSkewMatrix t A i j) = 0) :
    ∀ i, z i = 0 := by
  classical
  have hquad : 0 ≤ ∑ i, z i * ∑ j,
      z j * tournamentSkewMatrix t A i j :=
    tournamentSkewMatrix_quadratic_nonneg t A hA ht z hz
  have hcomp_sum : ∑ i, z i * (d i + ∑ j,
      z j * tournamentSkewMatrix t A i j) = 0 :=
    Finset.sum_eq_zero fun i hi => hcomp i
  have hidentity :
      (∑ i, z i * d i) + ∑ i, z i * ∑ j,
          z j * tournamentSkewMatrix t A i j = 0 := by
    calc
      (∑ i, z i * d i) + ∑ i, z i * ∑ j,
          z j * tournamentSkewMatrix t A i j =
          ∑ i, z i * (d i + ∑ j,
            z j * tournamentSkewMatrix t A i j) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
      _ = 0 := hcomp_sum
  have hd_sum : ∑ i, z i * d i = 0 := by
    have hd_nonneg : 0 ≤ ∑ i, z i * d i :=
      Finset.sum_nonneg fun i hi => mul_nonneg (hz i) (le_of_lt (hd i))
    nlinarith [hidentity, hquad]
  intro i
  have hterm_le : z i * d i ≤ ∑ j, z j * d j := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset ι))
      (f := fun j => z j * d j)
      (fun j hj => mul_nonneg (hz j) (le_of_lt (hd j)))
      (a := i) (Finset.mem_univ i)
    simpa using h
  have hterm_nonneg : 0 ≤ z i * d i :=
    mul_nonneg (hz i) (le_of_lt (hd i))
  have hterm_zero : z i * d i = 0 :=
    le_antisymm (by simpa [hd_sum] using hterm_le) hterm_nonneg
  nlinarith [hd i, hz i, hterm_zero]

/-- Equality in the tournament energy forces at most one positive coordinate
when `t > 1`. -/
theorem tournamentSkewMatrix_support_le_one_of_quadratic_eq_zero
    (t : ℝ) (A : ι → ι → ℝ) (hA : IsFractionalTournament A) (ht : 1 < t)
    (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hzero : ∑ i, z i * ∑ j, z j * tournamentSkewMatrix t A i j = 0) :
    ∀ i j, z i ≠ 0 → z j ≠ 0 → i = j := by
  classical
  intro i j hi hj
  by_contra hne
  have henergy := tournament_quadratic_identity t A z
  have hS : ∑ i, ∑ j, z i * z j * A i j = 0 := by
    rw [hzero] at henergy
    nlinarith [henergy]
  have hpairpos : 0 < z i * z j * A i j + z j * z i * A j i := by
    have hzi : 0 < z i := lt_of_le_of_ne (hz i) (Ne.symm hi)
    have hzj : 0 < z j := lt_of_le_of_ne (hz j) (Ne.symm hj)
    have horient := hA.2.2 i j hne
    have hzprod : 0 < z i * z j := mul_pos hzi hzj
    calc
      z i * z j * A i j + z j * z i * A j i =
          z i * z j * (A i j + A j i) := by ring
      _ = z i * z j := by rw [horient]; simp
      _ > 0 := hzprod
  have hsum_nonneg : 0 ≤ ∑ i, ∑ j, z i * z j * A i j :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
      mul_nonneg (mul_nonneg (hz i) (hz j)) (hA.2.1 i j)
  have hrow_nonneg : ∀ k, 0 ≤ ∑ l, z k * z l * A k l := fun k =>
    Finset.sum_nonneg fun l hl =>
      mul_nonneg (mul_nonneg (hz k) (hz l)) (hA.2.1 k l)
  have hrow_le : z i * z j * A i j ≤ ∑ l, z i * z l * A i l := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset ι))
      (f := fun l => z i * z l * A i l)
      (fun l hl => mul_nonneg (mul_nonneg (hz i) (hz l)) (hA.2.1 i l))
      (a := j) (Finset.mem_univ j)
    simpa using h
  have hterm_le : z i * z j * A i j ≤ ∑ k, ∑ l,
      z k * z l * A k l := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset ι))
      (f := fun k => ∑ l, z k * z l * A k l)
      (fun k hk => hrow_nonneg k) (a := i) (Finset.mem_univ i)
    exact hrow_le.trans (by simpa using h)
  have hzero_term : z i * z j * A i j = 0 := by
    exact le_antisymm (by simpa [hS] using hterm_le)
      (mul_nonneg (mul_nonneg (hz i) (hz j)) (hA.2.1 i j))
  have hzero_reverse : z j * z i * A j i = 0 := by
    have hrow_le' : z j * z i * A j i ≤ ∑ l, z j * z l * A j l := by
      have h := Finset.single_le_sum (s := (Finset.univ : Finset ι))
        (f := fun l => z j * z l * A j l)
        (fun l hl => mul_nonneg (mul_nonneg (hz j) (hz l)) (hA.2.1 j l))
        (a := i) (Finset.mem_univ i)
      simpa using h
    have hterm_le' : z j * z i * A j i ≤ ∑ k, ∑ l,
        z k * z l * A k l := by
      have h := Finset.single_le_sum (s := (Finset.univ : Finset ι))
        (f := fun k => ∑ l, z k * z l * A k l)
        (fun k hk => hrow_nonneg k) (a := j) (Finset.mem_univ j)
      exact hrow_le'.trans (by simpa using h)
    exact le_antisymm (by simpa [hS] using hterm_le')
      (mul_nonneg (mul_nonneg (hz j) (hz i)) (hA.2.1 j i))
  nlinarith [hpairpos, hzero_term, hzero_reverse]

/-- A no-sink tournament has no homogeneous simplex-LCP solution for its
skew-dominant matrix. -/
theorem not_singletonLCPFeasible_tournamentSkewMatrix
    (t : ℝ) (A : ι → ι → ℝ) (hA : IsFractionalTournament A)
    (hunit : FractionalTournamentHasUnitOutneighbor A) (ht : 1 < t) :
    ¬SingletonLCPFeasible (tournamentSkewMatrix t A) := by
  classical
  rintro ⟨lam, hresidual, hcomp⟩
  have henergy :
      ∑ i, (lam i) * ∑ j, (lam j) * tournamentSkewMatrix t A i j = 0 := by
    have hsum : ∑ i, (lam i) *
        singletonLCPResidual (tournamentSkewMatrix t A) lam i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hc := hcomp i
      change lam.val i * singletonLCPResidual
        (tournamentSkewMatrix t A) lam i = 0 at hc
      exact hc
    simpa [singletonLCPResidual, wsum, dotProduct] using hsum
  have hsupport := tournamentSkewMatrix_support_le_one_of_quadratic_eq_zero
    t A hA ht (fun i => lam i) lam.property.1 henergy
  have hnonempty : ∃ i, lam i ≠ 0 := by
    by_contra hnone
    have hzero : ∀ i, lam.val i = 0 := by
      intro i
      exact Classical.byContradiction fun hi => hnone ⟨i, hi⟩
    have := lam.property.2
    simp [hzero] at this
  obtain ⟨i, hi⟩ := hnonempty
  obtain ⟨j, hij, hout⟩ := hunit i
  have hres := hresidual j
  have hsingle : ∀ k, k ≠ i → lam k = 0 := by
    intro k hki
    by_contra hk
    exact hki (hsupport i k hi hk).symm
  change 0 ≤ ∑ k, lam k * tournamentSkewMatrix t A j k at hres
  have hsum : (∑ k, lam k * tournamentSkewMatrix t A j k) =
      lam i * tournamentSkewMatrix t A j i := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro k hk hki
      rw [hsingle k hki, zero_mul]
    · intro hiempty
      exact False.elim (hiempty (Finset.mem_univ i))
  rw [hsum] at hres
  have hback := hA.2.2 j i (Ne.symm hij)
  have hzero : A j i = 0 := by nlinarith [hback, hout]
  rw [tournamentSkewMatrix, hzero] at hres
  rw [hout] at hres
  norm_num at hres
  have hpos : 0 < lam i := lt_of_le_of_ne (lam.property.1 i) (Ne.symm hi)
  linarith

end Math.LinearProgramming
