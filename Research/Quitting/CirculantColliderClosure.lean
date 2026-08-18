/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CirculantColliderCompletion

/-!
# The distant pocket, and the closure of the collider-completion family

`Research/Quitting/CirculantColliderCompletion.lean` leaves one sign pattern of
the five-player collider completion open: the *distant pocket*, in which the
two distant margins `m 2` and `m 3` are negative, the two neighbour margins
`m 1` and `m 4` are nonnegative, and the margin sum is positive.  This module
closes it, and with it the whole family.

Write `low - s` for the join margin the completion pays at every distance other
than four, at which it pays zero.  Four producers divide the pocket, cut by the
position of `low - s` against the two negative margins.

* `low - s ≤ m 3`: the step-two cycle.  Its floor at the deepest elapsed phase
  is exactly that inequality, and the floor one phase earlier follows from it,
  because `m 1 + q * m 3` exceeds `m 3` whenever `m 1` is nonnegative, `m 3`
  negative and `q` below one.
* `m 2 ≤ low - s` as well: then both distant margins sit below the join margin,
  which is exactly the condition for a *skip pair* `{y, y + 2}` to be a sure
  exit set in the sense of
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.  Its own row is then a
  uniform-equilibrium payoff, with no cycle involved.
* `m 3 < low - s < m 2`: the step-two floor fails and the step-three floor at
  the deepest phase holds instead.  What step three still needs is
  `0 ≤ m 4 + q * m 2` at its anchor root.  That holds at every root when
  `0 ≤ m 2 + m 4`, and otherwise at a root no larger than `m 4 / -m 2`, which
  exists exactly when `m 2 * m 3 ≤ m 1 * m 4`: the two deepest terms of the
  anchor cancel at that point and leave `(m 1 * m 4 - m 2 * m 3) / -m 2`.
* The remainder, `m 1 * m 4 < m 2 * m 3` with `m 2 + m 4 < 0`: the step-four
  cycle, at a root beyond `m 4 / (s - low)`.  The join margin's own weight
  cancels the anchor's constant term at that point, leaving `m 3 - (low - s)`
  to drive the rest, and that is negative in this branch.

## Main results

* `isQuittingSureExitSet_skip_of_le` — a skip pair is a sure exit set when both
  distant margins are at most the join margin
* `exists_uniformEquilibriumPayoff_colliderDistantStepTwo`,
  `exists_uniformEquilibriumPayoff_colliderDistantStepThree` and
  `exists_uniformEquilibriumPayoff_colliderDistantStepFour` — the three cycles
* `exists_stepThree_root_of_mul_le` and `exists_stepFour_root_of_lt_mul` — the
  two located anchor roots
* `exists_uniformEquilibriumPayoff_colliderDistantPocket` and
  `isEmpty_counterexampleRegime_colliderDistantPocket` — the pocket
* `isEmpty_counterexampleRegime_colliderReward` — **the family**: no
  five-player collider completion with nonnegative solo self value and
  nonpositive joint value is in a counterexample regime
-/

noncomputable section

namespace GameTheory
namespace CirculantColliderCompletion

open CirculantConstantStepCycle CirculantTrichotomyClosure
open QuittingSureSetOwnerRepair

/-! ## Skip pairs of the five-cycle -/

theorem card_skip (y : ZMod 5) : ({y, y + 2} : Finset (ZMod 5)).card = 2 := by
  revert y
  decide

theorem erase_skip_left (y : ZMod 5) :
    ({y, y + 2} : Finset (ZMod 5)).erase y = {y + 2} := by
  revert y
  decide

theorem erase_skip_right (y : ZMod 5) :
    ({y, y + 2} : Finset (ZMod 5)).erase (y + 2) = {y} := by
  revert y
  decide

theorem skip_ne_collider_left (y : ZMod 5) :
    ({y, y + 2} : Finset (ZMod 5)) ≠ {y - 1, y} := by
  revert y
  decide

theorem skip_ne_collider_right (y : ZMod 5) :
    ({y, y + 2} : Finset (ZMod 5)) ≠ {y + 2 - 1, y + 2} := by
  revert y
  decide

theorem sub_skip_self (y : ZMod 5) : y - (y + 2) = 3 := by
  revert y
  decide

theorem card_insert_skip {y j : ZMod 5} (hj : j ∉ ({y, y + 2} : Finset (ZMod 5))) :
    (insert j ({y, y + 2} : Finset (ZMod 5))).card = 3 := by
  revert hj
  revert j
  revert y
  decide

theorem insert_skip_ne_collider {y j : ZMod 5}
    (hj : j ∉ ({y, y + 2} : Finset (ZMod 5))) :
    insert j ({y, y + 2} : Finset (ZMod 5)) ≠ {j - 1, j} := by
  revert hj
  revert j
  revert y
  decide

/-! ## The rows at a skip pair -/

variable (s low : ℝ) (m : ZMod 5 → ℝ)

theorem quittingSetReward_skip_left (y : ZMod 5) :
    quittingSetReward (colliderReward s low m) {y, y + 2} y = low := by
  rw [quittingSetReward_of_nonempty _ (Finset.insert_nonempty y {y + 2})]
  refine colliderReward_of_mem s low m _ ?_ y (by simp) (skip_ne_collider_left y)
  rw [card_skip]
  decide

theorem quittingSetReward_skip_right (y : ZMod 5) :
    quittingSetReward (colliderReward s low m) {y, y + 2} (y + 2) = low := by
  rw [quittingSetReward_of_nonempty _ (Finset.insert_nonempty y {y + 2})]
  refine colliderReward_of_mem s low m _ ?_ (y + 2) (by simp)
    (skip_ne_collider_right y)
  rw [card_skip]
  decide

theorem quittingSetReward_skip_outsider {y j : ZMod 5}
    (hj : j ∉ ({y, y + 2} : Finset (ZMod 5))) :
    quittingSetReward (colliderReward s low m) {y, y + 2} j = 0 := by
  rw [quittingSetReward_of_nonempty _ (Finset.insert_nonempty y {y + 2})]
  refine colliderReward_of_notMem s low m _ ?_ j hj
  rw [card_skip]
  decide

theorem quittingSetReward_insert_skip {y j : ZMod 5}
    (hj : j ∉ ({y, y + 2} : Finset (ZMod 5))) :
    quittingSetReward (colliderReward s low m) (insert j {y, y + 2}) j = low := by
  rw [quittingSetReward_of_nonempty _ (Finset.insert_nonempty j _)]
  refine colliderReward_of_mem s low m _ ?_ j (Finset.mem_insert_self _ _)
    (insert_skip_ne_collider hj)
  rw [card_insert_skip hj]
  decide

/-- **When a skip pair is a sure exit set.**  At a skip pair of a collider
table neither member is the other's collider, so both are paid the joint value;
the two membership toggles are worth `s + m 2` and `s + m 3` against `low`, and
an outsider joining is worth `low` against `0`. -/
theorem isQuittingSureExitSet_skip_of_le (hlow : low ≤ 0)
    (h2 : m 2 ≤ low - s) (h3 : m 3 ≤ low - s) (y : ZMod 5) :
    IsQuittingSureExitSet (colliderReward s low m) {y, y + 2} := by
  constructor
  · intro member hmem
    have hy : member = y ∨ member = y + 2 := by simpa using hmem
    rcases hy with hy | hy <;> subst hy
    · rw [erase_skip_left, quittingSetReward_singleton, quittingSetReward_skip_left,
        show member + 2 - member = 2 from by ring]
      linarith
    · rw [erase_skip_right, quittingSetReward_singleton,
        quittingSetReward_skip_right, sub_skip_self y]
      linarith
  · intro outsider hout
    rw [quittingSetReward_insert_skip s low m hout,
      quittingSetReward_skip_outsider s low m hout]
    exact hlow

/-! ## The three cycles of the distant pocket -/

variable {s low m}

/-- The margin sum of a table whose margin at distance zero vanishes. -/
theorem sum_margin_eq (hm0 : m 0 = 0) :
    (∑ e : ZMod 5, m e) = m 1 + m 2 + m 3 + m 4 := by
  rw [show (∑ e : ZMod 5, m e) = m 0 + m 1 + m 2 + m 3 + m 4 from
    Fin.sum_univ_five (fun e : ZMod 5 => m e), hm0]
  ring

/-- **Step two closes the far side of the distant pocket.**  When the join
margin is at most `m 3`, the step-two cycle's floor at the deepest elapsed
phase is that inequality, and the floor one phase earlier follows from it. -/
theorem exists_uniformEquilibriumPayoff_colliderDistantStepTwo
    (hm0 : m 0 = 0) (hs : 0 ≤ s)
    (hm1 : 0 ≤ m 1) (hm2 : m 2 < 0) (hm3 : m 3 < 0)
    (hsum : 0 < m 1 + m 2 + m 3 + m 4) (hfloor : low - s ≤ m 3) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame (colliderReward s low m)).IsUniformEquilibriumPayoff none payoff := by
  have hsum' : 0 < ∑ e, m e := by rw [sum_margin_eq hm0]; exact hsum
  obtain ⟨q, hq, hroot⟩ := exists_stepAnchor_root m (c := 2) hm0 (by decide) hm2 hsum'
  have hq0 : 0 < q := hq.1
  have hq1 : q < 1 := hq.2
  have h22 : (2 : ZMod 5) * 2 = 4 := by decide
  have h32 : (3 : ZMod 5) * 2 = 1 := by decide
  have h42 : (4 : ZMod 5) * 2 = 3 := by decide
  have hroot' : m 2 + m 4 * q + m 1 * q ^ 2 + m 3 * q ^ 3 = 0 := by
    rw [stepAnchor_eq, h22, h32, h42] at hroot
    exact hroot
  have htail : 0 < m 4 + q * m 1 + q ^ 2 * m 3 := by
    rcases le_or_gt (m 4 + q * m 1 + q ^ 2 * m 3) 0 with hle | hgt
    · nlinarith
    · exact hgt
  refine ⟨_, isUniformEquilibriumPayoff_constantStep (c' := 2)
    (isCirculantPairTable_colliderReward s low m hm0) (by decide) hs hq0 hq1 hroot
    ?_ ?_ ?_ ?_⟩
  · rw [colliderJoin_of_ne s low (by decide)]
    linarith
  · rw [h22, h32, h42, colliderJoin_four]
    linarith
  · rw [h32, h42, colliderJoin_of_ne s low (by decide)]
    nlinarith [mul_pos (sub_pos.mpr hq1) (neg_pos.mpr hm3)]
  · rw [h42, colliderJoin_of_ne s low (by decide)]
    exact hfloor

/-- **Step three closes the near side of the distant pocket.**  Its floor at
the deepest elapsed phase is `low - s ≤ m 2`; the remaining floor reads the
anchor root, and is supplied by the caller. -/
theorem exists_uniformEquilibriumPayoff_colliderDistantStepThree
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ 0) (hm3 : m 3 < 0)
    (hfloor : low - s ≤ m 2)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hroot : stepAnchor m 3 q = 0)
    (hstep : 0 ≤ m 4 + q * m 2) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame (colliderReward s low m)).IsUniformEquilibriumPayoff none payoff := by
  have h23 : (2 : ZMod 5) * 3 = 1 := by decide
  have h33 : (3 : ZMod 5) * 3 = 4 := by decide
  have h43 : (4 : ZMod 5) * 3 = 2 := by decide
  have hroot' : m 3 + m 1 * q + m 4 * q ^ 2 + m 2 * q ^ 3 = 0 := by
    rw [stepAnchor_eq, h23, h33, h43] at hroot
    exact hroot
  have htail : 0 < m 1 + q * m 4 + q ^ 2 * m 2 := by
    rcases le_or_gt (m 1 + q * m 4 + q ^ 2 * m 2) 0 with hle | hgt
    · nlinarith
    · exact hgt
  refine ⟨_, isUniformEquilibriumPayoff_constantStep (c' := 3)
    (isCirculantPairTable_colliderReward s low m hm0) (by decide) hs hq0 hq1 hroot
    ?_ ?_ ?_ ?_⟩
  · rw [colliderJoin_of_ne s low (by decide)]
    linarith
  · rw [h23, h33, h43, colliderJoin_of_ne s low (by decide)]
    linarith
  · rw [h33, h43, colliderJoin_four]
    linarith
  · rw [h43, colliderJoin_of_ne s low (by decide)]
    exact hfloor

/-- **Step four closes what the other two cycles miss.**  Its floors at the two
shallowest elapsed phases are free, the floor at the deepest phase asks
`low - s < m 2`, and the remaining one asks the anchor root to lie beyond
`m 4 / (s - low)`, which is what the supplied inequality says. -/
theorem exists_uniformEquilibriumPayoff_colliderDistantStepFour
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ 0) (hm1 : 0 ≤ m 1)
    (hfloor : low - s < m 2)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hroot : stepAnchor m 4 q = 0)
    (hstep : m 4 + (low - s) * q ≤ 0) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame (colliderReward s low m)).IsUniformEquilibriumPayoff none payoff := by
  have h24 : (2 : ZMod 5) * 4 = 3 := by decide
  have h34 : (3 : ZMod 5) * 4 = 2 := by decide
  have h44 : (4 : ZMod 5) * 4 = 1 := by decide
  have hroot' : m 4 + m 3 * q + m 2 * q ^ 2 + m 1 * q ^ 3 = 0 := by
    rw [stepAnchor_eq, h24, h34, h44] at hroot
    exact hroot
  have htail : low - s ≤ m 3 + q * m 2 + q ^ 2 * m 1 := by
    rcases le_or_gt (low - s) (m 3 + q * m 2 + q ^ 2 * m 1) with hle | hgt
    · exact hle
    · nlinarith
  refine ⟨_, isUniformEquilibriumPayoff_constantStep (c' := 1)
    (isCirculantPairTable_colliderReward s low m hm0) (by decide) hs hq0 hq1 hroot
    ?_ ?_ ?_ ?_⟩
  · rw [colliderJoin_four]
  · rw [h24, h34, h44, colliderJoin_of_ne s low (by decide)]
    linarith
  · rw [h34, h44, colliderJoin_of_ne s low (by decide)]
    nlinarith
  · rw [h44, colliderJoin_of_ne s low (by decide)]
    linarith

/-! ## Locating the step-three and step-four roots -/

/-- **The step-three root no larger than `m 4 / -m 2`.**  At that point the two
deepest terms of the anchor cancel and what is left is
`(m 1 * m 4 - m 2 * m 3) / -m 2`, so the anchor is nonnegative there exactly
when `m 2 * m 3 ≤ m 1 * m 4`.  A root that early keeps `m 4 + q * m 2`
nonnegative, which is the floor step three cannot supply for itself. -/
theorem exists_stepThree_root_of_mul_le
    (hm1 : 0 ≤ m 1) (hm2 : m 2 < 0) (hm3 : m 3 < 0) (hsmall : m 2 + m 4 < 0)
    (hmul : m 2 * m 3 ≤ m 1 * m 4) :
    ∃ q, 0 < q ∧ q < 1 ∧ stepAnchor m 3 q = 0 ∧ 0 ≤ m 4 + q * m 2 := by
  have hm2ne : m 2 ≠ 0 := ne_of_lt hm2
  have hpos : (0 : ℝ) < -m 2 := by linarith
  have hm1m4 : 0 < m 1 * m 4 :=
    lt_of_lt_of_le (mul_pos_of_neg_of_neg hm2 hm3) hmul
  have hm4pos : 0 < m 4 := by
    rcases le_or_gt (m 4) 0 with h | h
    · nlinarith [mul_nonneg hm1 (neg_nonneg.mpr h)]
    · exact h
  have hupos : 0 < m 4 / -m 2 := div_pos hm4pos hpos
  have hult : m 4 / -m 2 < 1 := by
    rw [div_lt_one hpos]
    linarith
  have hzero : stepAnchor m 3 0 = m 3 := by
    rw [stepAnchor_eq]
    ring
  have hcancel : m 4 * (m 4 / -m 2) ^ 2 + m 2 * (m 4 / -m 2) ^ 3 = 0 := by
    field_simp
    ring
  have hvalue : stepAnchor m 3 (m 4 / -m 2) = m 3 + m 1 * (m 4 / -m 2) := by
    rw [stepAnchor_eq, show (2 : ZMod 5) * 3 = 1 from by decide,
      show (3 : ZMod 5) * 3 = 4 from by decide,
      show (4 : ZMod 5) * 3 = 2 from by decide]
    linarith [hcancel]
  have hkey : (m 3 + m 1 * (m 4 / -m 2)) * -m 2 = -(m 2 * m 3) + m 1 * m 4 := by
    field_simp
    ring
  have hnonneg : 0 ≤ stepAnchor m 3 (m 4 / -m 2) := by
    rw [hvalue]
    rcases le_or_gt 0 (m 3 + m 1 * (m 4 / -m 2)) with h | h
    · exact h
    · nlinarith [mul_neg_of_neg_of_pos h hpos]
  obtain ⟨q, hq, hroot⟩ :=
    exists_stepAnchor_root_mem_Ioc m 3 hupos.le (by rw [hzero]; exact hm3) hnonneg
  refine ⟨q, hq.1, lt_of_le_of_lt hq.2 hult, hroot, ?_⟩
  have hmono : m 4 / -m 2 * m 2 ≤ q * m 2 :=
    mul_le_mul_of_nonpos_right hq.2 hm2.le
  have hcancel' : m 4 / -m 2 * m 2 = -m 4 := by
    field_simp
  linarith

/-- **The step-four root beyond `m 4 / (s - low)`.**  The join margin's own
weight cancels the anchor's constant term at that point, leaving
`m 3 - (low - s)` to drive the remainder, so the anchor is negative there
whenever `m 3 < low - s`, `m 2 + m 4 < 0` and `m 1 * m 4 < m 2 * m 3`.  A root
that late keeps `m 4 + (low - s) * q` nonpositive, which is the floor step four
cannot supply for itself. -/
theorem exists_stepFour_root_of_lt_mul
    (hsum : 0 < m 1 + m 2 + m 3 + m 4) (hm4 : 0 ≤ m 4)
    (hm3 : m 3 < low - s) (hm2 : low - s < m 2) (hm2neg : m 2 < 0)
    (hsmall : m 2 + m 4 < 0) (hmul : m 1 * m 4 < m 2 * m 3) :
    ∃ q, 0 < q ∧ q < 1 ∧ stepAnchor m 4 q = 0 ∧ m 4 + (low - s) * q ≤ 0 := by
  have h24 : (2 : ZMod 5) * 4 = 3 := by decide
  have h34 : (3 : ZMod 5) * 4 = 2 := by decide
  have h44 : (4 : ZMod 5) * 4 = 1 := by decide
  have hone : stepAnchor m 4 1 = m 4 + m 3 + m 2 + m 1 := by
    rw [stepAnchor_eq, h24, h34, h44]
    ring
  have hlampos : (0 : ℝ) < s - low := by linarith
  have hlamne : s - low ≠ 0 := ne_of_gt hlampos
  have hm4lam : m 4 < s - low := by linarith
  rcases eq_or_lt_of_le hm4 with hm4zero | hm4pos
  · obtain ⟨q, hq, hquad⟩ :=
      Math.exists_cubicAnchor_root_mem_Ioo (a := m 3) (b := m 2) (c := m 1) (d := 0)
        (by linarith) (by rw [← hm4zero] at hsum; linarith)
    refine ⟨q, hq.1, hq.2, ?_, ?_⟩
    · rw [stepAnchor_eq, h24, h34, h44, ← hm4zero]
      rw [Math.cubicAnchor] at hquad
      linear_combination q * hquad
    · rw [← hm4zero]
      nlinarith [mul_neg_of_neg_of_pos (by linarith : low - s < 0) hq.1]
  · have hwpos : 0 < m 4 / (s - low) := div_pos hm4pos hlampos
    have hwlt : m 4 / (s - low) < 1 := by
      rw [div_lt_one hlampos]
      exact hm4lam
    have hH : (s - low) ^ 2 * (m 3 + (s - low)) + m 2 * m 4 * (s - low)
        + m 1 * m 4 ^ 2 < 0 := by
      have hcube : m 1 * m 4 ^ 2 < m 2 * m 3 * m 4 := by
        nlinarith [mul_lt_mul_of_pos_right hmul hm4pos]
      have hquad : 0 < (s - low) ^ 2 + m 2 * m 4 := by
        nlinarith [mul_pos hlampos (by linarith : (0 : ℝ) < s - low - m 4),
          mul_pos (by linarith : (0 : ℝ) < m 2 + (s - low)) hm4pos]
      nlinarith [mul_neg_of_neg_of_pos
        (by linarith : m 3 + (s - low) < 0) hquad]
    have hscaled : stepAnchor m 4 (m 4 / (s - low)) * (s - low) ^ 3 =
        m 4 * ((s - low) ^ 2 * (m 3 + (s - low)) + m 2 * m 4 * (s - low)
          + m 1 * m 4 ^ 2) := by
      rw [stepAnchor_eq, h24, h34, h44]
      field_simp
      ring
    have hneg : stepAnchor m 4 (m 4 / (s - low)) < 0 := by
      have hprod : stepAnchor m 4 (m 4 / (s - low)) * (s - low) ^ 3 < 0 := by
        rw [hscaled]
        exact mul_neg_of_pos_of_neg hm4pos hH
      nlinarith [pow_pos hlampos 3]
    obtain ⟨q, hq, hroot⟩ :=
      exists_stepAnchor_root_mem_Ioo m 4 hwlt.le hneg (by rw [hone]; linarith)
    refine ⟨q, lt_trans hwpos hq.1, hq.2, hroot, ?_⟩
    have hmono : (low - s) * q < (low - s) * (m 4 / (s - low)) :=
      mul_lt_mul_of_neg_left hq.1 (by linarith)
    have hcancel : (low - s) * (m 4 / (s - low)) = -m 4 := by
      field_simp
      ring
    linarith

/-! ## The pocket, and the family -/

/-- **The distant pocket has a uniform-equilibrium payoff.**  Four producers
divide it: the step-two cycle when the join margin is at most `m 3`, the sure
exit of a skip pair when both distant margins are at most the join margin, the
step-three cycle when the join margin lies between them and either
`0 ≤ m 2 + m 4` or `m 2 * m 3 ≤ m 1 * m 4`, and the step-four cycle on what is
left. -/
theorem exists_uniformEquilibriumPayoff_colliderDistantPocket
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ 0)
    (hm1 : 0 ≤ m 1) (hm2 : m 2 < 0) (hm3 : m 3 < 0) (hm4 : 0 ≤ m 4)
    (hsum : 0 < m 1 + m 2 + m 3 + m 4) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame (colliderReward s low m)).IsUniformEquilibriumPayoff none payoff := by
  have hsum' : 0 < ∑ e, m e := by rw [sum_margin_eq hm0]; exact hsum
  rcases le_or_gt (low - s) (m 3) with hfar | hfar
  · exact exists_uniformEquilibriumPayoff_colliderDistantStepTwo hm0 hs hm1 hm2 hm3
      hsum hfar
  rcases le_or_gt (m 2) (low - s) with hnear | hnear
  · exact ⟨_, isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet _
      (isQuittingSureExitSet_skip_of_le s low m hlow hnear hfar.le 0)⟩
  rcases le_or_gt 0 (m 2 + m 4) with hwide | hwide
  · obtain ⟨q, hq, hroot⟩ := exists_stepAnchor_root m (c := 3) hm0 (by decide) hm3 hsum'
    refine exists_uniformEquilibriumPayoff_colliderDistantStepThree hm0 hs hlow hm3
      hnear.le hq.1 hq.2 hroot ?_
    nlinarith [mul_pos (sub_pos.mpr hq.2) (neg_pos.mpr hm2)]
  rcases le_or_gt (m 2 * m 3) (m 1 * m 4) with hmul | hmul
  · obtain ⟨q, hq0, hq1, hroot, hstep⟩ :=
      exists_stepThree_root_of_mul_le hm1 hm2 hm3 hwide hmul
    exact exists_uniformEquilibriumPayoff_colliderDistantStepThree hm0 hs hlow hm3
      hnear.le hq0 hq1 hroot hstep
  · obtain ⟨q, hq0, hq1, hroot, hstep⟩ :=
      exists_stepFour_root_of_lt_mul hsum hm4 hfar hnear hm2 hwide hmul
    exact exists_uniformEquilibriumPayoff_colliderDistantStepFour hm0 hs hlow hm1
      hnear hq0 hq1 hroot hstep

/-- The distant pocket, as emptiness of the counterexample regime. -/
theorem isEmpty_counterexampleRegime_colliderDistantPocket
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ 0)
    (hm1 : 0 ≤ m 1) (hm2 : m 2 < 0) (hm3 : m 3 < 0) (hm4 : 0 ≤ m 4)
    (hsum : 0 < m 1 + m 2 + m 3 + m 4) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) :=
  ⟨fun regime => regime.not_exists_uniformEquilibriumPayoff
    (exists_uniformEquilibriumPayoff_colliderDistantPocket hm0 hs hlow hm1 hm2 hm3
      hm4 hsum)⟩

/-- **The collider-completion family carries no counterexample regime.**  Every
five-player collider completion whose margin at distance zero vanishes, whose
solo self value is nonnegative and whose joint value is nonpositive has an
ordinary uniform-equilibrium payoff.  No sign pattern, screen, or regime
hypothesis is left over. -/
theorem isEmpty_counterexampleRegime_colliderReward
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) := by
  rcases isEmpty_counterexampleRegime_or_distantPocket hm0 hs hlow with
    hempty | ⟨hsum, hm2, hm3, hm4, hm1⟩
  · exact hempty
  · exact isEmpty_counterexampleRegime_colliderDistantPocket hm0 hs hlow hm1 hm2
      hm3 hm4 hsum

end CirculantColliderCompletion
end GameTheory
