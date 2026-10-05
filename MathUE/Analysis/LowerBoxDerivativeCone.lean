import MathUE.Analysis.LowerBoxBoundaryMinimum

/-! # The derivative cone at a lower-box boundary minimum

Only lower-binding coordinates need target lower bounds. Unprotected interior
coordinates have zero partial derivative; upper-face signs have the opposite orientation.
-/

namespace Math

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The partial signs force a nonnegative derivative toward every target
below the upper box and above the singleton floor at the binding coordinates. -/
theorem lowerBox_partial_signs_apply_sub_nonneg
    (lower upper point target : ι → ℝ) (derivative : (ι → ℝ) →L[ℝ] ℝ)
    (hpoint : point ∈ Set.Icc lower upper)
    (hsigns : ∀ player,
      (point player = lower player → 0 ≤ derivative (Pi.single player 1)) ∧
      (lower player < point player → point player < upper player →
        derivative (Pi.single player 1) = 0) ∧
      (point player = upper player → derivative (Pi.single player 1) ≤ 0))
    (htargetBinding : ∀ player, point player = lower player → lower player ≤ target player)
    (htargetUpper : target ≤ upper) :
    0 ≤ derivative (target - point) := by
  conv_rhs => rw [pi_eq_sum_univ' (target - point)]
  rw [map_sum]
  apply Finset.sum_nonneg
  intro player _
  rw [map_smul]
  change 0 ≤ (target player - point player) * derivative (Pi.single player 1)
  by_cases hlower : point player = lower player
  · exact mul_nonneg (by rw [hlower]; exact sub_nonneg.mpr (htargetBinding player hlower))
      ((hsigns player).1 hlower)
  · by_cases hupper : point player = upper player
    · exact mul_nonneg_of_nonpos_of_nonpos
        (by rw [hupper]; exact sub_nonpos.mpr (htargetUpper player))
        ((hsigns player).2.2 hupper)
    · have hstrictLower : lower player < point player :=
        lt_of_le_of_ne (hpoint.1 player) (Ne.symm hlower)
      have hstrictUpper : point player < upper player :=
        lt_of_le_of_ne (hpoint.2 player) hupper
      rw [(hsigns player).2.1 hstrictLower hstrictUpper]
      simp

end Math
