/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import MathUE.SurvivalWeightedObstructionAction

/-!
# Lower-face work for a constrained affine coordinate

These scalar identities separate the reusable ordered-ring algebra behind a
lower-bounded binary best response from its quitting-game interpretation.
They make no equilibrium-existence or dynamical claim.
-/

namespace Math

/-- Complementarity on `[lower, 1]` leaves exactly the lower-face normal work
in the ordinary unconstrained two-action defect. -/
theorem affineBinaryDefect_eq_lowerFaceNormalWork
    (lower probability gap : ℝ)
    (hpositive : (1 - probability) * max gap 0 = 0)
    (hnegative : (probability - lower) * max (-gap) 0 = 0) :
    (1 - probability) * max gap 0 + probability * max (-gap) 0 =
      lower * max (-gap) 0 := by
  nlinarith

/-- Best-response inequalities against the two endpoints of `[lower, 1]`
are equivalent to the two exact lower/upper complementarity products. -/
theorem lowerBoundComplementarity_of_endpoint_bounds
    (lower probability gap : ℝ)
    (hlower : lower ≤ probability) (hupper : probability ≤ 1)
    (htoUpper : (1 - probability) * gap ≤ 0)
    (htoLower : (lower - probability) * gap ≤ 0) :
    (1 - probability) * max gap 0 = 0 ∧
      (probability - lower) * max (-gap) 0 = 0 := by
  constructor
  · by_cases hgap : gap ≤ 0
    · simp [max_eq_right hgap]
    · rw [max_eq_left (le_of_not_ge hgap)]
      exact le_antisymm htoUpper
        (mul_nonneg (sub_nonneg.mpr hupper) (le_of_not_ge hgap))
  · by_cases hgap : 0 ≤ gap
    · rw [max_eq_right (by linarith : -gap ≤ 0), mul_zero]
    · rw [max_eq_left (by linarith : 0 ≤ -gap)]
      have hproduct : (probability - lower) * (-gap) ≤ 0 := by
        nlinarith [htoLower]
      exact le_antisymm hproduct
        (mul_nonneg (sub_nonneg.mpr hlower) (by linarith))

/-- A rowwise work decomposition telescopes over every finite backward
block.  The terms are intentionally unweighted: chronological reach is a
separate datum. -/
theorem sum_range_work_eq_excess_telescope
    (work excess killed shield : ℕ → ℝ)
    (hrow : ∀ time,
      work time = excess time - excess (time + 1) +
        killed time + shield time)
    (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon, work time) =
      excess 0 - excess horizon +
        ∑ time ∈ Finset.range horizon, killed time +
        ∑ time ∈ Finset.range horizon, shield time := by
  simp_rw [hrow, Finset.sum_add_distrib]
  rw [Finset.sum_range_sub']

/-- Raising one affine option by a nonnegative amount spends the smaller of
that amount and the old positive advantage of the competing option. -/
theorem max_add_sub_max_eq_addend_sub_min
    (quitValue continueValue addend : ℝ) (haddend : 0 ≤ addend) :
    max quitValue (continueValue + addend) -
        max quitValue continueValue =
      addend - min addend (max (quitValue - continueValue) 0) := by
  rw [SurvivalWeightedObstruction.Block.max_add_sub_max_eq_posPart_sub_posPart
    quitValue continueValue addend haddend]
  rw [max_comm (quitValue - continueValue) 0]
  by_cases hle : addend ≤ max 0 (quitValue - continueValue)
  · rw [min_eq_left hle, max_eq_left (sub_nonpos.mpr hle)]
    ring
  · have hge : max 0 (quitValue - continueValue) ≤ addend :=
      le_of_not_ge hle
    rw [min_eq_right hge, max_eq_right (sub_nonneg.mpr hge)]

/-- Exact one-coordinate repayment account.  Removing `work` from the mover
changes the complementary aggregate by total-potential change plus `work`. -/
theorem complementChange_eq_totalChange_add_work
    (sourceMover targetMover sourceOther targetOther work : ℝ)
    (hmover : targetMover = sourceMover - work) :
    targetOther - sourceOther =
      (targetMover + targetOther) - (sourceMover + sourceOther) + work := by
  rw [hmover]
  ring

/-- A global lower bound turns the exact repayment account into the sharp
near-minimum lower bound on complementary leakage. -/
theorem work_sub_targetExcess_le_complementChange
    (minimum sourceMover targetMover sourceOther targetOther work : ℝ)
    (hmover : targetMover = sourceMover - work)
    (htarget : minimum ≤ targetMover + targetOther) :
    work - (sourceMover + sourceOther - minimum) ≤
      targetOther - sourceOther := by
  rw [hmover] at htarget
  linarith

/-- One exact mover-debt drop decomposes the change on any label set into
the mover's outgoing work and the signed change on the other labels. -/
theorem finsetDebtChange_eq_moverWork_add_complement
    {label : Type*} [DecidableEq label]
    (source target : label → ℝ) (mover : label) (work : ℝ)
    (hmover : target mover = source mover - work)
    (labels : Finset label) :
    Finset.sum labels (fun player => target player - source player) =
      -(if mover ∈ labels then work else 0) +
        Finset.sum (labels.erase mover)
          (fun player => target player - source player) := by
  by_cases hmemb : mover ∈ labels
  · rw [← Finset.sum_erase_add _ _ hmemb, hmover]
    simp [hmemb]
    ring
  · rw [Finset.erase_eq_self.mpr hmemb]
    simp [hmemb]

/-- Finite cut balance for a sequence of exact mover-debt drops.  It is a
signed conservation law and supplies no recipient orientation. -/
theorem finiteDebtCutBalance
    {label : Type*} [DecidableEq label]
    (debt : ℕ → label → ℝ) (mover : ℕ → label) (work : ℕ → ℝ)
    (hmover : ∀ time,
      debt (time + 1) (mover time) = debt time (mover time) - work time)
    (labels : Finset label) (horizon : ℕ) :
    Finset.sum labels
        (fun player => debt horizon player - debt 0 player) =
      -(∑ time ∈ Finset.range horizon,
          if mover time ∈ labels then work time else 0) +
        ∑ time ∈ Finset.range horizon,
          Finset.sum (labels.erase (mover time))
            (fun player => debt (time + 1) player - debt time player) := by
  have hpoint : ∀ time,
      Finset.sum labels
          (fun player => debt (time + 1) player - debt time player) =
        -(if mover time ∈ labels then work time else 0) +
          Finset.sum (labels.erase (mover time))
            (fun player => debt (time + 1) player - debt time player) := by
    intro time
    exact finsetDebtChange_eq_moverWork_add_complement
      (debt time) (debt (time + 1)) (mover time) (work time)
        (hmover time) labels
  calc
    Finset.sum labels
        (fun player => debt horizon player - debt 0 player) =
        Finset.sum labels (fun player =>
          ∑ time ∈ Finset.range horizon,
            (debt (time + 1) player - debt time player)) := by
      apply Finset.sum_congr rfl
      intro player _
      exact (Finset.sum_range_sub (fun time => debt time player) horizon).symm
    _ = ∑ time ∈ Finset.range horizon,
        Finset.sum labels (fun player =>
          debt (time + 1) player - debt time player) := by
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]

end Math
