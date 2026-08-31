/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Finite paid-collision extraction

This file isolates a finite pigeonhole step used by deletion near-cap
arguments.  On any nonempty finite index set, nonnegative masses and signed
increments with a positive weighted sum select one positive increment, its
average product share, and the corresponding quantitative mass floor.  The
original seven-subset interfaces are retained as specializations for a
three-element survivor set.

The result is game-independent: it does not mention rewards, profiles,
terminal laws, or a supplied collision atom.
-/

namespace Math.FinitePaidCollision

noncomputable section

open scoped BigOperators

def nonemptyCoalitions (C : Type*) [Fintype C] [DecidableEq C] :
    Finset (Finset C) :=
  (Finset.univ : Finset (Finset C)).filter Finset.Nonempty

theorem nonemptyCoalitions_card
    (C : Type*) [Fintype C] [DecidableEq C] :
    (nonemptyCoalitions C).card = 2 ^ Fintype.card C - 1 := by
  have hcoalitions :
      nonemptyCoalitions C =
        (Finset.powerset (Finset.univ : Finset C)).erase ∅ := by
    ext coalition
    simp [nonemptyCoalitions, Finset.nonempty_iff_ne_empty]
  rw [hcoalitions, Finset.card_erase_of_mem]
  · rw [Finset.card_powerset]
    simp
  · simp

/-- The subtype of nonempty finite subsets has exactly `2^n - 1` elements. -/
theorem nonemptyCoalitionSubtype_card
    (C : Type*) [Fintype C] [DecidableEq C] :
    Fintype.card {S : Finset C // S.Nonempty} =
      2 ^ Fintype.card C - 1 := by
  rw [Fintype.card_subtype]
  exact nonemptyCoalitions_card C

@[simp] theorem nonemptyCoalitions_fin3_card :
    (nonemptyCoalitions (Fin 3)).card = 7 := by
  rw [nonemptyCoalitions_card]
  norm_num

private theorem exists_sum_le_card_mul_of_nonempty
    {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    ∃ a ∈ s, ∑ b ∈ s, f b ≤ (s.card : ℝ) * f a := by
  classical
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := hs
  have hsum_lt :
      ∑ b ∈ s, (s.card : ℝ) * f b <
        ∑ _b ∈ s, ∑ c ∈ s, f c := by
    apply Finset.sum_lt_sum
    · intro b hb
      exact (h b hb).le
    · exact ⟨a, ha, h a ha⟩
  have hirrefl :
      (s.card : ℝ) * (∑ b ∈ s, f b) <
        (s.card : ℝ) * (∑ b ∈ s, f b) := by
    calc
      (s.card : ℝ) * (∑ b ∈ s, f b) =
          ∑ b ∈ s, (s.card : ℝ) * f b := by
            rw [Finset.mul_sum]
      _ < ∑ _b ∈ s, ∑ c ∈ s, f c := hsum_lt
      _ = (s.card : ℝ) * (∑ b ∈ s, f b) := by
        simp [nsmul_eq_mul]
  exact (lt_irrefl _ hirrefl)

/-- Paid-collision extraction on a nonempty finite index set, retaining the
average product and mass floors.  Increments remain signed; positivity is a
conclusion. -/
theorem exists_paid_collision_of_nonempty_finset_with_product
    {α : Type*} (indices : Finset α) (hindices : indices.Nonempty)
    (mass increment : α → ℝ) (residual cap : ℝ)
    (hmass : ∀ a ∈ indices, 0 ≤ mass a)
    (hresidual : 0 < residual)
    (hsum : residual ≤ ∑ a ∈ indices, mass a * increment a)
    (hincrement : ∀ a ∈ indices, increment a ≤ cap)
    (hcap : 0 < cap) :
    ∃ a ∈ indices,
      residual / (indices.card : ℝ) ≤ mass a * increment a ∧
      0 < mass a * increment a ∧ 0 < increment a ∧
      residual / ((indices.card : ℝ) * cap) ≤ mass a := by
  classical
  obtain ⟨a, ha, haverage⟩ :=
    exists_sum_le_card_mul_of_nonempty indices hindices
      (fun a => mass a * increment a)
  have hcard : 0 < (indices.card : ℝ) := by
    exact_mod_cast hindices.card_pos
  have hterm :
      residual / (indices.card : ℝ) ≤ mass a * increment a := by
    apply (div_le_iff₀ hcard).2
    simpa [mul_comm] using hsum.trans haverage
  have htermPos : 0 < mass a * increment a := by
    exact (div_pos hresidual hcard).trans_le hterm
  have hincrementPos : 0 < increment a := by
    by_contra hnot
    have hnonpos : increment a ≤ 0 := le_of_not_gt hnot
    have : mass a * increment a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hmass a ha) hnonpos
    linarith
  have hproductBound : mass a * increment a ≤ mass a * cap :=
    mul_le_mul_of_nonneg_left (hincrement a ha) (hmass a ha)
  have hmassBound :
      residual / (indices.card : ℝ) ≤ mass a * cap :=
    hterm.trans hproductBound
  have hdenom : 0 < (indices.card : ℝ) * cap := mul_pos hcard hcap
  refine ⟨a, ha, hterm, htermPos, hincrementPos, ?_⟩
  apply (div_le_iff₀ hdenom).2
  nlinarith [hmassBound]

/-- Private strongest form of the seven-term paid-collision extraction.

The increments may be signed.  Positivity of the total weighted sum forces
the selected increment, rather than merely its weighted product, to be
positive because all masses are nonnegative.
-/
private theorem exists_paid_collision_of_card_seven_core
    {α : Type*} (coalitions : Finset α)
    (mass increment : α → ℝ) (residual c : ℝ)
    (hcard : coalitions.card = 7)
    (hmass : ∀ a ∈ coalitions, 0 ≤ mass a)
    (hresidual : 0 < residual)
    (hsum : residual ≤ ∑ a ∈ coalitions, mass a * increment a)
    (hincrement : ∀ a ∈ coalitions, increment a ≤ c)
    (hc : 0 < c) :
    ∃ a ∈ coalitions, residual / 7 ≤ mass a * increment a ∧
      0 < mass a * increment a ∧ 0 < increment a ∧
      residual / (7 * c) ≤ mass a := by
  have hnonempty : coalitions.Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨a, ha, hterm, htermPos, hincrementPos, hmassFloor⟩ :=
    exists_paid_collision_of_nonempty_finset_with_product
      coalitions hnonempty mass increment residual c hmass hresidual hsum
        hincrement hc
  have hcardReal : (coalitions.card : ℝ) = 7 := by
    exact_mod_cast hcard
  rw [hcardReal] at hterm hmassFloor
  exact ⟨a, ha, hterm, htermPos, hincrementPos, hmassFloor⟩

/-- Seven-term paid-collision extraction with an explicit seven-element index.

The increments may be signed.  Positivity of the total weighted sum forces
the selected increment, rather than merely its weighted product, to be
positive because all masses are nonnegative.
-/
theorem exists_paid_collision_of_card_seven
    {α : Type*} (coalitions : Finset α)
    (mass increment : α → ℝ) (residual c : ℝ)
    (hcard : coalitions.card = 7)
    (hmass : ∀ a ∈ coalitions, 0 ≤ mass a)
    (hresidual : 0 < residual)
    (hsum : residual ≤ ∑ a ∈ coalitions, mass a * increment a)
    (hincrement : ∀ a ∈ coalitions, increment a ≤ c)
    (hc : 0 < c) :
    ∃ a ∈ coalitions, 0 < mass a * increment a ∧ 0 < increment a ∧
      residual / (7 * c) ≤ mass a := by
  obtain ⟨a, ha, _hterm, hprod, hinc, hmass⟩ :=
    exists_paid_collision_of_card_seven_core coalitions mass increment residual c
      hcard hmass hresidual hsum hincrement hc
  exact ⟨a, ha, hprod, hinc, hmass⟩

/-- Seven-term extraction retaining the paid-product lower bound. -/
theorem exists_paid_collision_of_card_seven_with_product
    {α : Type*} (coalitions : Finset α)
    (mass increment : α → ℝ) (residual c : ℝ)
    (hcard : coalitions.card = 7)
    (hmass : ∀ a ∈ coalitions, 0 ≤ mass a)
    (hresidual : 0 < residual)
    (hsum : residual ≤ ∑ a ∈ coalitions, mass a * increment a)
    (hincrement : ∀ a ∈ coalitions, increment a ≤ c)
    (hc : 0 < c) :
    ∃ a ∈ coalitions, residual / 7 ≤ mass a * increment a ∧
      0 < increment a ∧ residual / (7 * c) ≤ mass a := by
  obtain ⟨a, ha, hterm, _hprod, hinc, hmass⟩ :=
    exists_paid_collision_of_card_seven_core coalitions mass increment residual c
      hcard hmass hresidual hsum hincrement hc
  exact ⟨a, ha, hterm, hinc, hmass⟩

/-- Near-cap form of the product-retaining seven-term extraction. -/
theorem exists_paid_collision_of_gain_ge_sub_with_product
    {α : Type*} (coalitions : Finset α)
    (mass increment : α → ℝ)
    (gamma delta Pi solo gain c : ℝ)
    (hcard : coalitions.card = 7)
    (hmass : ∀ a ∈ coalitions, 0 ≤ mass a)
    (hgain : gamma - delta ≤ gain)
    (hsolo : solo ≤ Pi)
    (hdecomp : gain = solo + ∑ a ∈ coalitions, mass a * increment a)
    (hresidual : 0 < gamma - Pi - delta)
    (hincrement : ∀ a ∈ coalitions, increment a ≤ c)
    (hc : 0 < c) :
    ∃ a ∈ coalitions, (gamma - Pi - delta) / 7 ≤ mass a * increment a ∧
      0 < increment a ∧ (gamma - Pi - delta) / (7 * c) ≤ mass a := by
  apply exists_paid_collision_of_card_seven_with_product coalitions mass increment
    (gamma - Pi - delta) c hcard hmass hresidual
  · linarith [hgain, hsolo, hdecomp]
  · exact hincrement
  · exact hc

/-- The same extraction with the near-cap variables exposed literally. -/
theorem exists_paid_collision_of_gain_ge_sub
    {α : Type*} (coalitions : Finset α)
    (mass increment : α → ℝ)
    (gamma delta Pi solo gain c : ℝ)
    (hcard : coalitions.card = 7)
    (hmass : ∀ a ∈ coalitions, 0 ≤ mass a)
    (hgain : gamma - delta ≤ gain)
    (hsolo : solo ≤ Pi)
    (hdecomp : gain = solo + ∑ a ∈ coalitions, mass a * increment a)
    (hresidual : 0 < gamma - Pi - delta)
    (hincrement : ∀ a ∈ coalitions, increment a ≤ c)
    (hc : 0 < c) :
    ∃ a ∈ coalitions, 0 < mass a * increment a ∧ 0 < increment a ∧
      (gamma - Pi - delta) / (7 * c) ≤ mass a := by
  apply exists_paid_collision_of_card_seven coalitions mass increment
    (gamma - Pi - delta) c hcard hmass hresidual
  · linarith [hgain, hsolo, hdecomp]
  · exact hincrement
  · exact hc

theorem nonemptyCoalitions_card_eq_seven
    (C : Type*) [Fintype C] [DecidableEq C]
    (hcard : Fintype.card C = 3) :
    (nonemptyCoalitions C).card = 7 := by
  rw [nonemptyCoalitions_card, hcard]
  norm_num

/- The all-subsets interface used by a three-player deletion complement. -/
theorem exists_paid_collision_of_gain_ge_sub_nonemptyCoalitions
    {C : Type*} [Fintype C] [DecidableEq C]
    (mass increment : Finset C → ℝ)
    (gamma delta Pi solo gain c : ℝ)
    (hcard : Fintype.card C = 3)
    (hmass : ∀ a ∈ nonemptyCoalitions C, 0 ≤ mass a)
    (hgain : gamma - delta ≤ gain)
    (hsolo : solo ≤ Pi)
    (hdecomp : gain = solo +
      ∑ a ∈ nonemptyCoalitions C, mass a * increment a)
    (hresidual : 0 < gamma - Pi - delta)
    (hincrement : ∀ a ∈ nonemptyCoalitions C, increment a ≤ c)
    (hc : 0 < c) :
    ∃ a ∈ nonemptyCoalitions C, 0 < mass a * increment a ∧ 0 < increment a ∧
      (gamma - Pi - delta) / (7 * c) ≤ mass a := by
  apply exists_paid_collision_of_gain_ge_sub
    (nonemptyCoalitions C) mass increment gamma delta Pi solo gain c
    (nonemptyCoalitions_card_eq_seven C hcard)
  · exact hmass
  · exact hgain
  · exact hsolo
  · exact hdecomp
  · exact hresidual
  · exact hincrement
  · exact hc

@[simp] theorem nonemptyCoalitions_fin3_nonempty :
    (nonemptyCoalitions (Fin 3)).Nonempty := by
  exact Finset.card_pos.mp (by
    rw [nonemptyCoalitions_fin3_card]
    norm_num)

/-- Tail-arm algebra: a seven-term mass lower bound gives the `1/14` scale. -/
theorem tail_scale_of_paid_collision
    {residual c mass debt excess live : ℝ}
    (hc : 0 < c) (hdebt : 0 ≤ debt)
    (hmass : residual / (7 * c) ≤ mass)
    (htail : mass * debt / 2 ≤ live * excess) :
    residual * debt / (14 * c) ≤ live * excess := by
  have hmass' :=
    mul_le_mul_of_nonneg_right hmass (by positivity : 0 ≤ debt / 2)
  calc
    residual * debt / (14 * c) =
        (residual / (7 * c)) * (debt / 2) := by
          field_simp
          ring
    _ ≤ mass * (debt / 2) := hmass'
    _ = mass * debt / 2 := by ring
    _ ≤ live * excess := htail

/-- Endpoint-arm algebra: a seven-term mass lower bound gives the `1/56`
scale after the four-player `1/8` consumer bound. -/
theorem endpoint_scale_of_paid_collision
    {residual c mass debt gain : ℝ}
    (hc : 0 < c) (hdebt : 0 ≤ debt)
    (hmass : residual / (7 * c) ≤ mass)
    (hgain : mass * debt / 8 ≤ gain) :
    residual * debt / (56 * c) ≤ gain := by
  have hmass' := mul_le_mul_of_nonneg_right hmass (by positivity : 0 ≤ debt / 8)
  calc
    residual * debt / (56 * c) =
        (residual / (7 * c)) * (debt / 8) := by
          field_simp
          ring
    _ ≤ mass * (debt / 8) := hmass'
    _ = mass * debt / 8 := by ring
    _ ≤ gain := hgain

end

end Math.FinitePaidCollision
