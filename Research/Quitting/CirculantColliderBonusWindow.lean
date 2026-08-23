/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.CoerciveIntervalMinimum
import Research.Quitting.CirculantColliderBonusStationary

/-!
# The exact window of the candidate family

`Research/Quitting/CirculantColliderBonusFamily.lean` closes the candidate
family for `bonus ≤ 0` by the step-four cycle and shows that no constant-step
cycle closes it for `bonus > 0`.
`Research/Quitting/CirculantColliderBonusStationary.lean` closes it, at each
continuation rate `u` in the open unit interval, at the one bonus that rate
forces.  This module identifies the region the second producer covers.

Write `candidateBonusCurve` for the forced bonus as a function of the rate.
At the candidate's data it is the explicit rational curve

`candidateBonusCurve u = (2 - 3 u³) / ((1 - u) u³) + (9/2) / (1 - u⁴)`.

Two algebraic bounds delimit it.  Clearing denominators against
`1 - u⁴ = (1 - u)(1 + u + u² + u³)` shows

`(1 - u) u³ * candidateBonusCurve u ≥ 1/8`,

with equality only in the limit at `u = 1`, because the difference factors as
`(1 - u)(25 u⁵ + 50 u⁴ + 75 u³ + 48 u² + 32 u + 16)` over a positive
denominator.  Since `u³ ≤ 1` and `1 - u ≤ 1`, the curve therefore exceeds both
`1 / (8 (1 - u))` and `1 / (8 u³)`, so it blows up at both ends of the
interval and its sublevel sets are compact.

Those two bounds are exactly the escape hypothesis
`Math.IsCoerciveOn` of `MathUE/CoerciveIntervalMinimum.lean`, which turns them
into the shape of the range: the curve attains a minimum
`candidateBonusThreshold`, and its range is exactly the closed ray above that
minimum, so the stationary all-quitter block closes the family at
`bonus ≥ candidateBonusThreshold` and at no smaller bonus.  Together with the step-four closure at `bonus ≤ 0`, the two producers
leave exactly the open interval `0 < bonus < candidateBonusThreshold`
untouched.

`candidateBonusThreshold` is the exact minimum of the displayed curve.  No
decimal expansion of it is used or needed here.

## Main definitions

* `candidateBonusCurve` — the bonus a continuation rate forces
* `candidateBonusThreshold` — its minimum over the open unit interval

## Main results

* `candidateBonusCurve_eq` — the explicit rational form
* `one_eighth_le_mul_candidateBonusCurve` — the algebraic lower bound
* `isEmpty_terminalExploitabilityWitness_candidateReward_curve` — the closure at every
  forced bonus
* `exists_eq_candidateBonusCurve_of_le` — the range is closed upwards
* `isCoerciveOn_candidateBonusCurve` — the escape hypothesis
* `isLeast_candidateBonusThreshold` — the minimum is attained and is the least
  value the curve takes
* `candidateBonusRange_eq_Ici` — the range is exactly the closed ray
* `isEmpty_terminalExploitabilityWitness_candidateReward_of_threshold_le` — the closure
  above the threshold
* `not_exists_eq_candidateBonusCurve_of_lt` — and nothing below it
* `isEmpty_terminalExploitabilityWitness_candidateReward_outside_window` — the two-sided
  closure
* `one_lt_candidateBonusThreshold` — the window contains the bonus `1`
-/

noncomputable section

namespace GameTheory
namespace CirculantColliderBonus

open Set

/-! ## The forced bonus as a curve in the rate -/

/-- The collider bonus at which the all-quitter block of continuation rate `u`
is an exact equilibrium of the candidate family. -/
def candidateBonusCurve (u : ℝ) : ℝ := stationaryBonus 1 (-2) (1 / 2) u

/-- **The closure at every forced bonus.**  At each continuation rate in the
open unit interval the candidate family is refuted at the bonus that rate
forces. -/
theorem isEmpty_terminalExploitabilityWitness_candidateReward_curve {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) :
    IsEmpty (QuittingTerminalExploitabilityWitness (candidateReward (candidateBonusCurve u))) := by
  have hsum := sum_candidateMargin
  rw [candidateReward, candidateBonusCurve, ← hsum]
  exact isEmpty_terminalExploitabilityWitness_colliderBonusReward_stationary candidateMargin_zero
    zero_le_one hu0 hu1

/-- The explicit rational form of the curve. -/
theorem candidateBonusCurve_eq {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    candidateBonusCurve u = (2 - 3 * u ^ 3) / ((1 - u) * u ^ 3) + (9 / 2) / (1 - u ^ 4) := by
  have hu3 : u ^ 3 ≠ 0 := ne_of_gt (pow_pos hu0 3)
  have hone : (1 : ℝ) - u ≠ 0 := ne_of_gt (by linarith)
  have hfour : (1 : ℝ) - u ^ 4 ≠ 0 := by
    have : u ^ 4 < 1 := pow_lt_one₀ hu0.le hu1 (by norm_num)
    exact ne_of_gt (by linarith)
  rw [candidateBonusCurve, stationaryBonus, stationaryValue]
  field_simp
  ring

/-! ## The algebraic lower bound -/

theorem factor_one_sub_pow_four {u : ℝ} :
    (1 : ℝ) - u ^ 4 = (1 - u) * (1 + u + u ^ 2 + u ^ 3) := by ring

/-- **The curve blows up at both ends.**  Clearing the denominators leaves a
polynomial with the factor `1 - u` and positive cofactor, so the product of
the curve with `(1 - u) u³` never falls below `1/8`. -/
theorem one_eighth_le_mul_candidateBonusCurve {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    1 / 8 ≤ (1 - u) * u ^ 3 * candidateBonusCurve u := by
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hone : (0 : ℝ) < 1 - u := by linarith
  have hgeom : (0 : ℝ) < 1 + u + u ^ 2 + u ^ 3 := by positivity
  have hfour : (0 : ℝ) < 1 - u ^ 4 := by
    rw [factor_one_sub_pow_four]
    exact mul_pos hone hgeom
  have hexpand : (1 - u) * u ^ 3 * candidateBonusCurve u =
      (2 - 3 * u ^ 3) + (9 / 2) * u ^ 3 / (1 + u + u ^ 2 + u ^ 3) := by
    rw [candidateBonusCurve_eq hu0 hu1, factor_one_sub_pow_four]
    field_simp
  rw [hexpand, ← sub_nonneg]
  have hkey : (2 - 3 * u ^ 3) + (9 / 2) * u ^ 3 / (1 + u + u ^ 2 + u ^ 3) - 1 / 8 =
      ((1 - u) * (3 * u ^ 5 + 6 * u ^ 4 + 9 * u ^ 3 + 45 / 8 * u ^ 2 + 15 / 4 * u + 15 / 8)) /
        (1 + u + u ^ 2 + u ^ 3) := by
    field_simp
    ring
  rw [hkey]
  positivity

/-- The curve exceeds `1 / (8 (1 - u))`. -/
theorem inv_le_candidateBonusCurve_right {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    1 / (8 * (1 - u)) ≤ candidateBonusCurve u := by
  have hone : (0 : ℝ) < 1 - u := by linarith
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hu3le : u ^ 3 ≤ 1 := pow_le_one₀ hu0.le hu1.le
  have hbound := one_eighth_le_mul_candidateBonusCurve hu0 hu1
  have hprod : 0 < (1 - u) * u ^ 3 := mul_pos hone hu3
  have hpos : 0 < candidateBonusCurve u := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg hprod.le (neg_nonneg.mpr hcon)]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The curve exceeds `1 / (8 u³)`. -/
theorem inv_le_candidateBonusCurve_left {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    1 / (8 * u ^ 3) ≤ candidateBonusCurve u := by
  have hone : (0 : ℝ) < 1 - u := by linarith
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hbound := one_eighth_le_mul_candidateBonusCurve hu0 hu1
  have hprod : 0 < (1 - u) * u ^ 3 := mul_pos hone hu3
  have hpos : 0 < candidateBonusCurve u := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg hprod.le (neg_nonneg.mpr hcon)]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem candidateBonusCurve_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 < candidateBonusCurve u := by
  have hone : (0 : ℝ) < 1 - u := by linarith
  have h := inv_le_candidateBonusCurve_right hu0 hu1
  have : 0 < 1 / (8 * (1 - u)) := by positivity
  linarith

/-! ## Continuity of the curve -/

theorem continuousOn_candidateBonusCurve (lo hi : ℝ) (hlo : 0 < lo) (hhi : hi < 1) :
    ContinuousOn candidateBonusCurve (Set.Icc lo hi) := by
  have hbounds : ∀ u ∈ Set.Icc lo hi, 0 < u ∧ u < 1 := by
    intro u hu
    exact ⟨lt_of_lt_of_le hlo hu.1, lt_of_le_of_lt hu.2 hhi⟩
  have hden1 : ∀ u ∈ Set.Icc lo hi, (1 : ℝ) - u ^ 4 ≠ 0 := by
    intro u hu
    obtain ⟨hu0, hu1⟩ := hbounds u hu
    have : u ^ 4 < 1 := pow_lt_one₀ hu0.le hu1 (by norm_num)
    exact ne_of_gt (by linarith)
  have hden2 : ∀ u ∈ Set.Icc lo hi, (1 - u) * u ^ 3 ≠ 0 := by
    intro u hu
    obtain ⟨hu0, hu1⟩ := hbounds u hu
    exact ne_of_gt (mul_pos (by linarith) (pow_pos hu0 3))
  have hexplicit : ContinuousOn
      (fun u : ℝ ↦ (2 - 3 * u ^ 3) / ((1 - u) * u ^ 3) + (9 / 2) / (1 - u ^ 4))
      (Set.Icc lo hi) :=
    ContinuousOn.add (ContinuousOn.div (by fun_prop) (by fun_prop) hden2)
      (ContinuousOn.div (by fun_prop) (by fun_prop) hden1)
  refine hexplicit.congr ?_
  intro u hu
  obtain ⟨hu0, hu1⟩ := hbounds u hu
  exact candidateBonusCurve_eq hu0 hu1

/-! ## Escape at both ends -/

/-- **The escape hypothesis.**  Beyond the level `d = max c 1`, every rate
outside the subinterval `[1/(16 d), 1 - 1/(16 d)]` carries the curve past `c`:
near zero through the bound `1 / (8 u³)` and near one through the bound
`1 / (8 (1 - u))`. -/
theorem isCoerciveOn_candidateBonusCurve :
    Math.IsCoerciveOn candidateBonusCurve 0 1 := by
  intro c
  set d := max c 1 with hddef
  have hd1 : (1 : ℝ) ≤ d := le_max_right _ _
  have hdc : c ≤ d := le_max_left _ _
  have hdpos : (0 : ℝ) < d := by linarith
  have hstep : 1 / (16 * d) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hsmallpos : (0 : ℝ) < 1 / (16 * d) := by positivity
  refine ⟨1 / (16 * d), 1 - 1 / (16 * d), hsmallpos, by linarith, by linarith, ?_⟩
  intro u hu hnot
  obtain ⟨hu0, hu1⟩ := hu
  have hcube : u ^ 3 ≤ u := by
    nlinarith [mul_nonneg (mul_nonneg hu0.le (by linarith : (0 : ℝ) ≤ 1 - u))
      (by linarith : (0 : ℝ) ≤ 1 + u)]
  rcases not_and_or.mp (fun h ↦ hnot (Set.mem_Icc.mpr h)) with h | h
  · have hlt : u < 1 / (16 * d) := not_le.mp h
    have hclear : u * (16 * d) < 1 := (lt_div_iff₀ (by positivity)).mp hlt
    have hleft := inv_le_candidateBonusCurve_left hu0 hu1
    have hgap : c < 1 / (8 * u ^ 3) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hdc (by positivity : (0 : ℝ) ≤ 8 * u ^ 3),
        mul_le_mul_of_nonneg_left hcube (by positivity : (0 : ℝ) ≤ 16 * d)]
    linarith
  · have hgt : 1 - 1 / (16 * d) < u := not_le.mp h
    have hpos : (0 : ℝ) < 1 - u := by linarith
    have hclear : (1 - u) * (16 * d) < 1 := by
      rw [← lt_div_iff₀ (by positivity)]
      linarith
    have hright := inv_le_candidateBonusCurve_right hu0 hu1
    have hgap : c < 1 / (8 * (1 - u)) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hdc (by positivity : (0 : ℝ) ≤ 8 * (1 - u))]
    linarith

/-! ## The threshold and the window -/

/-- The set of bonuses the stationary all-quitter block closes. -/
def candidateBonusRange : Set ℝ := candidateBonusCurve '' Set.Ioo 0 1

/-- The exact algebraic threshold: the minimum of the forced-bonus curve. -/
def candidateBonusThreshold : ℝ := sInf candidateBonusRange

theorem isLeast_candidateBonusThreshold :
    IsLeast candidateBonusRange candidateBonusThreshold :=
  Math.image_Ioo_subset_Ici (by norm_num) continuousOn_candidateBonusCurve
    isCoerciveOn_candidateBonusCurve

/-- **Above any value it takes, the curve takes every value.** -/
theorem exists_eq_candidateBonusCurve_of_le {u₀ δ : ℝ} (hu0 : 0 < u₀) (hu1 : u₀ < 1)
    (hδ : candidateBonusCurve u₀ ≤ δ) :
    ∃ u, 0 < u ∧ u < 1 ∧ candidateBonusCurve u = δ := by
  obtain ⟨u, hu, heq⟩ := Math.Ici_subset_image_Ioo continuousOn_candidateBonusCurve
    isCoerciveOn_candidateBonusCurve (Set.mem_Ioo.mpr ⟨hu0, hu1⟩) hδ
  exact ⟨u, hu.1, hu.2, heq⟩

theorem candidateBonusThreshold_pos : 0 < candidateBonusThreshold := by
  obtain ⟨u, hu, heq⟩ := isLeast_candidateBonusThreshold.1
  rw [← heq]
  exact candidateBonusCurve_pos hu.1 hu.2

/-- **The closed region above.**  The stationary all-quitter block closes the
candidate family at every bonus at or above the threshold, and at no other. -/
theorem candidateBonusRange_eq_Ici :
    candidateBonusRange = Set.Ici candidateBonusThreshold :=
  Math.image_Ioo_eq_Ici_sInf (by norm_num) continuousOn_candidateBonusCurve
    isCoerciveOn_candidateBonusCurve

theorem isEmpty_terminalExploitabilityWitness_candidateReward_of_threshold_le {bonus : ℝ}
    (h : candidateBonusThreshold ≤ bonus) :
    IsEmpty (QuittingTerminalExploitabilityWitness (candidateReward bonus)) := by
  have hmem : bonus ∈ candidateBonusRange := by
    rw [candidateBonusRange_eq_Ici]
    exact h
  obtain ⟨u, hu, heq⟩ := hmem
  rw [← heq]
  exact isEmpty_terminalExploitabilityWitness_candidateReward_curve hu.1 hu.2

/-- Below the threshold the stationary all-quitter block is unavailable: no
continuation rate forces such a bonus. -/
theorem not_exists_eq_candidateBonusCurve_of_lt {bonus : ℝ}
    (h : bonus < candidateBonusThreshold) :
    ¬ ∃ u, 0 < u ∧ u < 1 ∧ candidateBonusCurve u = bonus := by
  rintro ⟨u, h0, h1, rfl⟩
  exact absurd (isLeast_candidateBonusThreshold.2
    ⟨u, Set.mem_Ioo.mpr ⟨h0, h1⟩, rfl⟩) (not_le.mpr h)

/-- **The two-sided closure.**  The candidate family is refuted at every bonus
outside the open interval between zero and the threshold: below by the
step-four cycle of `Research/Quitting/CirculantColliderBonusFamily.lean`, above
by the stationary all-quitter block. -/
theorem isEmpty_terminalExploitabilityWitness_candidateReward_outside_window {bonus : ℝ}
    (h : bonus ≤ 0 ∨ candidateBonusThreshold ≤ bonus) :
    IsEmpty (QuittingTerminalExploitabilityWitness (candidateReward bonus)) := by
  rcases h with h | h
  · exact isEmpty_terminalExploitabilityWitness_candidateReward_of_nonpos h
  · exact isEmpty_terminalExploitabilityWitness_candidateReward_of_threshold_le h

/-! ## The window is not empty -/

/-- The weight `(1 - u) u³` peaks at `u = 3/4`, where it is `27/256`.  The
difference factors as `(u - 3/4)² (u² + u/2 + 3/16)`, whose second factor has
negative discriminant. -/
theorem mul_le_twentySeven_over_twoFiftySix {u : ℝ} (hu0 : 0 ≤ u) :
    (1 - u) * u ^ 3 ≤ 27 / 256 := by
  nlinarith [mul_nonneg (sq_nonneg (u - 3 / 4))
    (by nlinarith [sq_nonneg (u + 1 / 4)] : (0 : ℝ) ≤ u ^ 2 + u / 2 + 3 / 16)]

/-- **The curve never drops to one.**  Dividing the lower bound `1/8` by the
largest possible weight `27/256` leaves `32/27`. -/
theorem thirtyTwo_over_twentySeven_le_candidateBonusCurve {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) : 32 / 27 ≤ candidateBonusCurve u := by
  have hbound := one_eighth_le_mul_candidateBonusCurve hu0 hu1
  have hweight := mul_le_twentySeven_over_twoFiftySix hu0.le
  have hpos := candidateBonusCurve_pos hu0 hu1
  nlinarith [mul_le_mul_of_nonneg_right hweight hpos.le]

/-- **Candidate H's own bonus lies strictly inside the window.**  The
threshold exceeds `32/27`, so at `bonus = 1` neither the step-four cycle nor
the stationary all-quitter block closes the family. -/
theorem thirtyTwo_over_twentySeven_le_candidateBonusThreshold :
    32 / 27 ≤ candidateBonusThreshold := by
  obtain ⟨u, hu, heq⟩ := isLeast_candidateBonusThreshold.1
  rw [← heq]
  exact thirtyTwo_over_twentySeven_le_candidateBonusCurve hu.1 hu.2

theorem one_lt_candidateBonusThreshold : 1 < candidateBonusThreshold := by
  have := thirtyTwo_over_twentySeven_le_candidateBonusThreshold
  linarith

end CirculantColliderBonus
end GameTheory
