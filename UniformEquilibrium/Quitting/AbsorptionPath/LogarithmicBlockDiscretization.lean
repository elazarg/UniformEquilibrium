/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import MathUE.PMFProduct.CollisionMass
import UniformEquilibrium.Quitting.AbsorptionPath.ContinuousPath
import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses

/-!
# Elementary logarithmic-time block estimates

This module records the checked finite estimates used by the continuous
absorption-path discretization.  The analytic construction of the derivative
path and its Bellman values remains a separate adapter; these declarations
make its quantitative bookkeeping reusable without assuming that adapter.
-/

noncomputable section

namespace GameTheory

open QuittingAbsorptionPath
open QuittingLCPClassification
open Real

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exponential approximation for one integrated hazard. -/
theorem exp_neg_mul_le_one_sub_exp_neg_of_nonneg_of_le
    {A h : ℝ} (hA : 0 ≤ A) (hAh : A ≤ h) :
    exp (-h) * A ≤ 1 - exp (-A) ∧ 1 - exp (-A) ≤ A := by
  have h1 : A + 1 ≤ exp A := add_one_le_exp A
  have hAexp : A * exp (-A) ≤ 1 - exp (-A) := by
    have hmul := mul_le_mul_of_nonneg_right h1 (exp_pos (-A)).le
    rw [← Real.exp_add, show A + -A = 0 by ring, Real.exp_zero] at hmul
    nlinarith
  have hmono : exp (-h) ≤ exp (-A) := by
    exact (exp_le_exp).2 (by linarith)
  constructor
  · calc
      exp (-h) * A ≤ exp (-A) * A := by gcongr
      _ = A * exp (-A) := by ring
      _ ≤ 1 - exp (-A) := hAexp
  · have hup : -A + 1 ≤ exp (-A) := by
      simpa [add_comm] using add_one_le_exp (-A)
    linarith

/-- The sharper lower estimate needed after multiplying by the remaining
continuation probability. -/
theorem exp_neg_mul_self_le_one_sub_exp_neg {A : ℝ} :
    exp (-A) * A ≤ 1 - exp (-A) := by
  have h1 : A + 1 ≤ exp A := add_one_le_exp A
  have hmul := mul_le_mul_of_nonneg_right h1 (exp_pos (-A)).le
  rw [← Real.exp_add, show A + -A = 0 by ring, Real.exp_zero] at hmul
  nlinarith

/-- A block's exact unique-quitter mass. -/
def logarithmicBlockUniqueMass (A h : ℝ) : ℝ :=
  (1 - exp (-A)) * exp (-(h - A))

omit [DecidableEq ι] in
/-- If the integrated hazards in a block are nonnegative and sum to its clock,
the exact unique-quitter masses lie between `exp (-h) A` and `A`. -/
theorem logarithmicBlockUniqueMass_bounds
    (A : ι → ℝ) (hA : ∀ j, 0 ≤ A j)
    (hAh : ∀ j, A j ≤ ∑ k, A k) (j : ι) :
    exp (-(∑ k, A k)) * A j ≤
        logarithmicBlockUniqueMass (A j) (∑ k, A k) ∧
      logarithmicBlockUniqueMass (A j) (∑ k, A k) ≤ A j := by
  let hsum : ℝ := ∑ k, A k
  have hAj : 0 ≤ A j := hA j
  have hAjh : A j ≤ hsum := hAh j
  have hfactor0 : 0 ≤ exp (-(hsum - A j)) := exp_nonneg _
  have hfactor1 : exp (-(hsum - A j)) ≤ 1 := by
    rw [exp_le_one_iff]
    linarith
  constructor
  · calc
      exp (-hsum) * A j =
          (exp (-A j) * A j) * exp (-(hsum - A j)) := by
        have hexp : exp (-hsum) =
            exp (-A j) * exp (-(hsum - A j)) := by
          rw [show -hsum = -A j + -(hsum - A j) by ring, Real.exp_add]
        rw [hexp]
        ring
      _ ≤ (1 - exp (-A j)) * exp (-(hsum - A j)) := by
        exact mul_le_mul_of_nonneg_right
          exp_neg_mul_self_le_one_sub_exp_neg hfactor0
      _ = logarithmicBlockUniqueMass (A j) hsum := rfl
  · calc
      logarithmicBlockUniqueMass (A j) hsum ≤
          A j * exp (-(hsum - A j)) := by
        dsimp [logarithmicBlockUniqueMass]
        exact mul_le_mul_of_nonneg_right
          (exp_neg_mul_le_one_sub_exp_neg_of_nonneg_of_le hAj hAjh).2
          hfactor0
      _ ≤ A j * 1 := mul_le_mul_of_nonneg_left hfactor1 hAj
      _ = A j := mul_one _

omit [DecidableEq ι] in
/-- The abstract continuous-versus-discrete singleton mass comparison. -/
theorem sum_abs_sub_of_between_same_nonneg
    (A μ P : ι → ℝ)
    (hμ0 : ∀ j, exp (-(∑ k, A k)) * A j ≤ μ j)
    (hμ1 : ∀ j, μ j ≤ A j)
    (hP0 : ∀ j, exp (-(∑ k, A k)) * A j ≤ P j)
    (hP1 : ∀ j, P j ≤ A j) :
    ∑ j, |μ j - P j| ≤
      (∑ j, A j) * (1 - exp (-(∑ j, A j))) := by
  have habs : ∀ j, |μ j - P j| ≤
      A j - exp (-(∑ k, A k)) * A j := by
    intro j
    rw [abs_le]
    constructor <;> linarith [hμ0 j, hμ1 j, hP0 j, hP1 j]
  calc
    ∑ j, |μ j - P j| ≤
        ∑ j, (A j - exp (-(∑ k, A k)) * A j) :=
      Finset.sum_le_sum fun j _ => habs j
    _ = (∑ j, A j) * (1 - exp (-(∑ j, A j))) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring

omit [DecidableEq ι] in
/-- Exact product rows have total continuation `exp (-h)` when their
integrated hazards sum to `h`. -/
theorem exp_neg_sum_eq_prod_exp_neg
    (A : ι → ℝ) :
    exp (-(∑ j, A j)) = ∏ j, exp (-A j) := by
  simpa only [Finset.sum_neg_distrib] using
    (Real.exp_sum Finset.univ (fun j => -A j))

/-- The product-row collision mass is quadratic in a block whose integrated
hazards sum to `h`. -/
theorem collisionMass_logarithmicBlock_le_sq
    (A : ι → ℝ) (h : ℝ) (hA : ∀ j, 0 ≤ A j)
    (hsum : ∑ j, A j = h) :
    Math.PMFProduct.collisionMass (fun j => 1 - exp (-A j)) ≤ h ^ 2 / 2 := by
  let q : ι → ℝ := fun j => 1 - exp (-A j)
  have hq0 : ∀ j, 0 ≤ q j := by
    intro j
    dsimp [q]
    rw [sub_nonneg, exp_le_one_iff]
    linarith [hA j]
  have hq1 : ∀ j, q j ≤ 1 := by
    intro j
    dsimp [q]
    linarith [exp_pos (-A j)]
  have hqA : ∀ j, q j ≤ A j := by
    intro j
    dsimp [q]
    exact (exp_neg_mul_le_one_sub_exp_neg_of_nonneg_of_le
      (hA j) (Finset.single_le_sum (fun k _ => hA k)
        (Finset.mem_univ j))).2
  have hqsum : ∑ j, q j ≤ h := by
    rw [← hsum]
    exact Finset.sum_le_sum fun j _ => hqA j
  have hcollision := Math.PMFProduct.collisionMass_le_sq_sum_div_two q hq0 hq1
  have hqsum0 : 0 ≤ ∑ j, q j := Finset.sum_nonneg fun j _ => hq0 j
  calc
    Math.PMFProduct.collisionMass q ≤ (∑ j, q j) ^ 2 / 2 := hcollision
    _ ≤ h ^ 2 / 2 := by nlinarith

/-- A quadratic collision error can be charged to the one-block loss of an
opponent-deleted survival clock.  This is the denominator-free estimate used
when the deleted clock may retain a positive survival atom. -/
theorem sq_div_two_le_collisionScale_mul_one_sub_exp_neg
    {H h : ℝ} (hH : 0 ≤ H) (hHh : H ≤ h) :
    H ^ 2 / 2 ≤ h * exp h / 2 * (1 - exp (-H)) := by
  have hhexp : H ≤ exp h * (1 - exp (-H)) := by
    have hlocal := exp_neg_mul_self_le_one_sub_exp_neg (A := H)
    have hscale := mul_le_mul_of_nonneg_left hlocal (exp_nonneg h)
    have hscale' : H * exp (h - H) ≤ exp h * (1 - exp (-H)) := by
      calc
        H * exp (h - H) = exp h * (exp (-H) * H) := by
          rw [show h - H = h + -H by ring, Real.exp_add]
          ring
        _ ≤ exp h * (1 - exp (-H)) := hscale
    have hexpOne : 1 ≤ exp (h - H) := by
      rw [← Real.exp_zero, Real.exp_le_exp]
      linarith
    calc
      H ≤ H * exp (h - H) := by
        nlinarith [mul_le_mul_of_nonneg_left hexpOne hH]
      _ ≤ exp h * (1 - exp (-H)) := hscale'
  have hh : 0 ≤ h := hH.trans hHh
  nlinarith [mul_le_mul_of_nonneg_left hhexp hh]

/-- Survival of an opponent-deleted logarithmic clock through the first `n`
blocks. -/
def logarithmicDeletedSurvival (H : ℕ → ℝ) (n : ℕ) : ℝ :=
  exp (-(∑ k ∈ Finset.range n, H k))

@[simp] theorem logarithmicDeletedSurvival_zero (H : ℕ → ℝ) :
    logarithmicDeletedSurvival H 0 = 1 := by
  simp [logarithmicDeletedSurvival]

/-- One-block evolution of logarithmic deleted survival. -/
theorem logarithmicDeletedSurvival_succ (H : ℕ → ℝ) (n : ℕ) :
    logarithmicDeletedSurvival H (n + 1) =
      logarithmicDeletedSurvival H n * exp (-H n) := by
  simp only [logarithmicDeletedSurvival, Finset.sum_range_succ]
  rw [show -(∑ k ∈ Finset.range n, H k + H n) =
      -(∑ k ∈ Finset.range n, H k) + -H n by ring, Real.exp_add]

/-- Exact finite deleted-survival telescope.  No limit-zero assumption is
present: any residual survival is retained by the final term. -/
theorem sum_logarithmicDeletedSurvival_mul_one_sub_exp_neg
    (H : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n,
      logarithmicDeletedSurvival H k * (1 - exp (-H k))) =
      1 - logarithmicDeletedSurvival H n := by
  have hterm (k : ℕ) :
      logarithmicDeletedSurvival H k * (1 - exp (-H k)) =
        logarithmicDeletedSurvival H k - logarithmicDeletedSurvival H (k + 1) := by
    rw [logarithmicDeletedSurvival_succ]
    ring
  simp_rw [hterm]
  rw [Finset.sum_range_sub']
  simp

/-- Global finite-prefix version of the opponent-only comparison budget.  A
local singleton discrepancy `H(1-exp(-H))` plus collision error `H²/2`, when
weighted by the deleted survival, costs at most
`h + h*exp(h)/2`, uniformly in the prefix length. -/
theorem sum_logarithmicDeletedSurvival_mul_blockError_le
    (H : ℕ → ℝ) {h : ℝ} (hH0 : ∀ k, 0 ≤ H k)
    (hHh : ∀ k, H k ≤ h) (n : ℕ) :
    (∑ k ∈ Finset.range n, logarithmicDeletedSurvival H k *
      (H k * (1 - exp (-H k)) + (H k) ^ 2 / 2)) ≤
      h + h * exp h / 2 := by
  let scale : ℝ := h + h * exp h / 2
  have hh : 0 ≤ h := (hH0 0).trans (hHh 0)
  have hscale0 : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hlocal (k : ℕ) :
      H k * (1 - exp (-H k)) + (H k) ^ 2 / 2 ≤
        scale * (1 - exp (-H k)) := by
    have hone : 0 ≤ 1 - exp (-H k) := by
      rw [sub_nonneg, exp_le_one_iff]
      linarith [hH0 k]
    have hfirst := mul_le_mul_of_nonneg_right (hHh k) hone
    have hsecond := sq_div_two_le_collisionScale_mul_one_sub_exp_neg
      (hH0 k) (hHh k)
    dsimp [scale]
    nlinarith
  calc
    (∑ k ∈ Finset.range n, logarithmicDeletedSurvival H k *
        (H k * (1 - exp (-H k)) + (H k) ^ 2 / 2)) ≤
        ∑ k ∈ Finset.range n, logarithmicDeletedSurvival H k *
          (scale * (1 - exp (-H k))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hlocal k) (exp_nonneg _)
    _ = scale * (1 - logarithmicDeletedSurvival H n) := by
      calc
        (∑ k ∈ Finset.range n, logarithmicDeletedSurvival H k *
            (scale * (1 - exp (-H k)))) =
            ∑ k ∈ Finset.range n, scale *
              (logarithmicDeletedSurvival H k * (1 - exp (-H k))) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = scale * (∑ k ∈ Finset.range n,
            logarithmicDeletedSurvival H k * (1 - exp (-H k))) := by
          rw [Finset.mul_sum]
        _ = scale * (1 - logarithmicDeletedSurvival H n) := by
          rw [sum_logarithmicDeletedSurvival_mul_one_sub_exp_neg]
    _ ≤ scale := by
      have hsurvival0 : 0 ≤ logarithmicDeletedSurvival H n := exp_nonneg _
      nlinarith [mul_nonneg hscale0 hsurvival0]
    _ = h + h * exp h / 2 := rfl

/-- No homogeneous singleton solution forces a strict negative entry in every
singleton column of the normalized comparison matrix. -/
theorem exists_negative_singleton_column_of_noHomogeneous
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬HasHomogeneousSimplexSolution (normalizedSoloMatrix reward))
    (column : ι) :
    ∃ row, reward (quittingProjectiveSingletonTerminal column) row -
      reward (quittingProjectiveSingletonTerminal row) row < 0 := by
  obtain ⟨row, hrow⟩ :=
    exists_negative_entry_in_column_of_noHomogeneous
      (normalizedSoloMatrix reward)
      (fun who => normalizedSoloMatrix_diagonal reward who) hno column
  refine ⟨row, ?_⟩
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix] at hrow
  exact hrow

end GameTheory
