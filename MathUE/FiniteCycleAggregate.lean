/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import MathUE.BonferroniProductBounds
import MathUE.CyclicContraction
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-!
# Finite cyclic weighted aggregation

This file gives a game-independent finite-cycle estimate for nonnegative
forcing terms.  Playerwise cyclic inequalities are unrolled with survival
weights, then a joint-survival union bound aggregates the forcing terms.  The
result is a player whose base value reaches the average forcing level.
-/

namespace Math.FiniteCycleAggregate

noncomputable section

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {K : ℕ} [NeZero K]

def prefixWeight (coefficient : Fin K → ℝ) (phase : Fin K) (fuel : ℕ) : ℝ :=
  ∏ offset ∈ Finset.range fuel, coefficient ((finRotate K)^[offset] phase)

def residualCharge (coefficient residual : Fin K → ℝ)
    (phase : Fin K) (fuel : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range fuel,
    prefixWeight coefficient phase offset * residual ((finRotate K)^[offset] phase)

omit [NeZero K] in
@[simp] theorem prefixWeight_zero (coefficient : Fin K → ℝ) (phase : Fin K) :
    prefixWeight coefficient phase 0 = 1 := by
  simp [prefixWeight]

omit [NeZero K] in
theorem prefixWeight_succ (coefficient : Fin K → ℝ) (phase : Fin K) (fuel : ℕ) :
    prefixWeight coefficient phase (fuel + 1) =
      prefixWeight coefficient phase fuel * coefficient ((finRotate K)^[fuel] phase) := by
  simp [prefixWeight, Finset.prod_range_succ]

omit [NeZero K] in
theorem residualCharge_succ (coefficient residual : Fin K → ℝ)
    (phase : Fin K) (fuel : ℕ) :
    residualCharge coefficient residual phase (fuel + 1) =
      residualCharge coefficient residual phase fuel +
        prefixWeight coefficient phase fuel * residual ((finRotate K)^[fuel] phase) := by
  simp [residualCharge, Finset.sum_range_succ]

omit [NeZero K] in
theorem prefixWeight_nonneg (coefficient : Fin K → ℝ)
    (hcoefficient : ∀ phase, 0 ≤ coefficient phase)
    (phase : Fin K) (fuel : ℕ) :
    0 ≤ prefixWeight coefficient phase fuel := by
  exact Finset.prod_nonneg fun offset _ => hcoefficient _

omit [NeZero K] in
theorem prefixWeight_le_one (coefficient : Fin K → ℝ)
    (hcoefficient0 : ∀ phase, 0 ≤ coefficient phase)
    (hcoefficient1 : ∀ phase, coefficient phase ≤ 1)
    (phase : Fin K) (fuel : ℕ) :
    prefixWeight coefficient phase fuel ≤ 1 := by
  exact Finset.prod_le_one (fun offset _ => hcoefficient0 _)
    (fun offset _ => hcoefficient1 _)

omit [NeZero K] in
theorem prefixWeight_card (coefficient : Fin K → ℝ) (phase : Fin K) :
    prefixWeight coefficient phase K = ∏ cyclePhase : Fin K, coefficient cyclePhase := by
  have horbit : ∀ offset : Fin K,
      ((finRotate K)^[offset.val] phase) = finCycle phase offset := by
    intro offset
    apply Fin.ext
    rw [Math.val_iterate_finRotate]
    simp [finCycle_apply, Fin.add_def, Nat.add_comm]
  rw [prefixWeight, Finset.prod_range]
  simp_rw [horbit]
  exact Equiv.prod_comp (finCycle phase) coefficient

omit [NeZero K] in
theorem cyclicValue_le_residualCharge_add_weight
    (coefficient residual value : Fin K → ℝ)
    (hcoefficient : ∀ phase, 0 ≤ coefficient phase)
    (hstep : ∀ phase,
      value phase ≤ residual phase +
        coefficient phase * value (finRotate K phase)) :
    ∀ (phase : Fin K) (fuel : ℕ),
      value phase ≤
        residualCharge coefficient residual phase fuel +
          prefixWeight coefficient phase fuel * value ((finRotate K)^[fuel] phase) := by
  intro phase fuel
  induction fuel with
  | zero => simp [residualCharge, prefixWeight]
  | succ fuel ih =>
      have hnext := hstep ((finRotate K)^[fuel] phase)
      have hweight := prefixWeight_nonneg coefficient hcoefficient phase fuel
      have hscaled := mul_le_mul_of_nonneg_left hnext hweight
      rw [residualCharge_succ, prefixWeight_succ,
        Function.iterate_succ_apply']
      calc
        value phase ≤ residualCharge coefficient residual phase fuel +
            prefixWeight coefficient phase fuel * value ((finRotate K)^[fuel] phase) := ih
        _ ≤ residualCharge coefficient residual phase fuel +
            prefixWeight coefficient phase fuel *
              (residual ((finRotate K)^[fuel] phase) +
                coefficient ((finRotate K)^[fuel] phase) *
                  value (finRotate K ((finRotate K)^[fuel] phase))) :=
          add_le_add_right hscaled _
        _ = residualCharge coefficient residual phase fuel +
              prefixWeight coefficient phase fuel * residual ((finRotate K)^[fuel] phase) +
            (prefixWeight coefficient phase fuel *
              coefficient ((finRotate K)^[fuel] phase)) *
                value (finRotate K ((finRotate K)^[fuel] phase)) := by ring

omit [NeZero K] in
theorem cyclicValue_le_residualCharge_div_one_sub_prod
    (coefficient residual value : Fin K → ℝ)
    (hcoefficient0 : ∀ phase, 0 ≤ coefficient phase)
    (hcycle : ∏ phase : Fin K, coefficient phase < 1)
    (hstep : ∀ phase,
      value phase ≤ residual phase +
        coefficient phase * value (finRotate K phase))
    (phase : Fin K) :
    value phase ≤ residualCharge coefficient residual phase K /
        (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) := by
  have hunroll := cyclicValue_le_residualCharge_add_weight
    coefficient residual value hcoefficient0 hstep phase K
  rw [prefixWeight_card, Math.iterate_finRotate_period] at hunroll
  have hdenom : 0 < 1 - ∏ cyclePhase : Fin K, coefficient cyclePhase :=
    sub_pos.mpr hcycle
  apply (le_div_iff₀ hdenom).2
  nlinarith

omit [NeZero K] in
theorem cyclicValue_ge_residualCharge_div_one_sub_prod
    (coefficient residual value : Fin K → ℝ)
    (hcoefficient : ∀ phase, 0 ≤ coefficient phase)
    (hcycle : ∏ phase : Fin K, coefficient phase < 1)
    (hstep : ∀ phase,
      value phase ≥ residual phase +
        coefficient phase * value (finRotate K phase))
    (phase : Fin K) :
    residualCharge coefficient residual phase K /
        (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) ≤ value phase := by
  let negResidual : Fin K → ℝ := fun cyclePhase => -residual cyclePhase
  let negValue : Fin K → ℝ := fun cyclePhase => -value cyclePhase
  have hstep_neg : ∀ cyclePhase,
      negValue cyclePhase ≤ negResidual cyclePhase +
        coefficient cyclePhase * negValue (finRotate K cyclePhase) := by
    intro cyclePhase
    dsimp [negValue, negResidual]
    nlinarith [hstep cyclePhase]
  have hneg := cyclicValue_le_residualCharge_add_weight
    coefficient negResidual negValue hcoefficient hstep_neg phase K
  rw [prefixWeight_card, Math.iterate_finRotate_period] at hneg
  have hcharge_neg : residualCharge coefficient negResidual phase K =
      -residualCharge coefficient residual phase K := by
    unfold residualCharge negResidual
    simp only [mul_neg, Finset.sum_neg_distrib]
  rw [hcharge_neg] at hneg
  have hdenom : 0 < 1 - ∏ cyclePhase : Fin K, coefficient cyclePhase :=
    sub_pos.mpr hcycle
  apply (div_le_iff₀ hdenom).2
  dsimp [negValue] at hneg
  nlinarith

omit [DecidableEq ι] in
omit [NeZero K] in
theorem exists_player_base_ge_eta_div_two_card
    (q coefficient value : Fin K → ι → ℝ) (beta : Fin K → ℝ)
    (eta : ℝ) (base : Fin K)
    (hη : 0 ≤ eta)
    (hq0 : ∀ phase player, 0 ≤ q phase player)
    (hq1 : ∀ phase player, q phase player ≤ 1)
    (hcoef0 : ∀ phase player, 0 ≤ coefficient phase player)
    (hbeta0 : ∀ phase, 0 ≤ beta phase)
    (hcbeta : ∀ phase player, beta phase ≤ coefficient phase player)
    (hbeta_eq : ∀ phase, beta phase = ∏ player : ι, (1 - q phase player))
    (hjoint : ∏ phase : Fin K, beta phase < 1)
    (hcontracts : ∀ player, ∏ phase : Fin K, coefficient phase player < 1)
    (hstep : ∀ phase player,
      value phase player ≥ eta / 2 * q phase player +
        coefficient phase player * value (finRotate K phase) player) :
    ∃ player, eta / (2 * (Fintype.card ι : ℝ)) ≤ value base player := by
  have hcharge_le : ∀ player,
      residualCharge beta (fun phase => eta / 2 * q phase player) base K ≤
        residualCharge (fun phase => coefficient phase player)
          (fun phase => eta / 2 * q phase player) base K := by
    intro player
    unfold residualCharge
    apply Finset.sum_le_sum
    intro offset hoffset
    apply mul_le_mul_of_nonneg_right
    · unfold prefixWeight
      apply Finset.prod_le_prod
      · intro index hindex
        exact hbeta0 _
      · intro index hindex
        exact hcbeta _ _
    · exact mul_nonneg (div_nonneg hη (by norm_num))
        (hq0 _ _)
  have hbeta_prod_le : ∀ player,
      ∏ phase : Fin K, beta phase ≤ ∏ phase : Fin K, coefficient phase player := by
    intro player
    apply Finset.prod_le_prod
    · intro phase hphase
      exact hbeta0 phase
    · intro phase hphase
      exact hcbeta phase player
  have hbeta_denom : 0 < 1 - ∏ phase : Fin K, beta phase :=
    sub_pos.mpr hjoint
  have hplayer_lower : ∀ player,
      residualCharge beta (fun phase => eta / 2 * q phase player) base K /
        (1 - ∏ phase : Fin K, beta phase) ≤ value base player := by
    intro player
    have hbound := cyclicValue_ge_residualCharge_div_one_sub_prod
      (fun phase => coefficient phase player)
      (fun phase => eta / 2 * q phase player)
      (fun phase => value phase player)
      (fun phase => hcoef0 phase player)
      (hcontracts player)
      (fun phase => hstep phase player) base
    have hcharge0 : 0 ≤ residualCharge
        (fun phase => coefficient phase player)
        (fun phase => eta / 2 * q phase player) base K := by
      unfold residualCharge
      exact Finset.sum_nonneg fun offset hoffset => mul_nonneg
        (prefixWeight_nonneg _ (fun phase => hcoef0 phase player) _ _)
        (mul_nonneg (div_nonneg hη (by norm_num)) (hq0 _ _))
    have hdenom_i : 0 < 1 - ∏ phase : Fin K, coefficient phase player :=
      sub_pos.mpr (hcontracts player)
    have hdenom_le : 1 - ∏ phase : Fin K, coefficient phase player ≤
        1 - ∏ phase : Fin K, beta phase := by
      exact sub_le_sub_left (hbeta_prod_le player) _
    exact (div_le_div₀ hcharge0 (hcharge_le player) hdenom_i hdenom_le).trans hbound
  have hunion : ∀ phase, 1 - beta phase ≤ ∑ player, q phase player := by
    intro phase
    rw [hbeta_eq phase]
    exact Math.one_sub_prod_one_sub_le_sum _ Finset.univ
      (fun player _ => hq0 phase player)
      (fun player _ => hq1 phase player)
  have hstop : 1 - ∏ phase : Fin K, beta phase ≤
      residualCharge beta (fun phase => 1 - beta phase) base K := by
    have hstep_beta : ∀ phase,
        (1 : ℝ) ≤ (1 - beta phase) + beta phase * 1 := by
      intro phase
      norm_num
    have hbound := cyclicValue_le_residualCharge_add_weight
      beta (fun phase => 1 - beta phase) (fun _ => (1 : ℝ)) hbeta0 hstep_beta base K
    rw [prefixWeight_card] at hbound
    linarith
  have hsum_charge :
      eta / 2 * residualCharge beta (fun phase => 1 - beta phase) base K ≤
        ∑ player, residualCharge beta
          (fun phase => eta / 2 * q phase player) base K := by
    have hswap :
        ∑ player, residualCharge beta
            (fun phase => eta / 2 * q phase player) base K =
          ∑ offset ∈ Finset.range K,
            prefixWeight beta base offset *
              ∑ player, eta / 2 * q ((finRotate K)^[offset] base) player := by
      unfold residualCharge
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro offset hoffset
      rw [Finset.mul_sum]
    have hweighted :
        ∑ offset ∈ Finset.range K,
            prefixWeight beta base offset * (eta / 2 *
              (1 - beta ((finRotate K)^[offset] base))) ≤
          ∑ offset ∈ Finset.range K,
            prefixWeight beta base offset *
              ∑ player, eta / 2 * q ((finRotate K)^[offset] base) player := by
      apply Finset.sum_le_sum
      intro offset hoffset
      apply mul_le_mul_of_nonneg_left
      · have heta2 : 0 ≤ eta / 2 := by positivity
        simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left
          (hunion ((finRotate K)^[offset] base)) heta2
      · exact prefixWeight_nonneg beta hbeta0 base offset
    rw [hswap]
    calc
      eta / 2 * residualCharge beta (fun phase => 1 - beta phase) base K =
          ∑ offset ∈ Finset.range K,
            prefixWeight beta base offset * (eta / 2 *
              (1 - beta ((finRotate K)^[offset] base))) := by
        unfold residualCharge
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset hoffset
        ring
      _ ≤ _ := hweighted
  have hsum_lower : eta / 2 ≤ ∑ player, value base player := by
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
      (fun player _ => hplayer_lower player)
    rw [← Finset.sum_div] at hsum
    have hsum_charge' := hsum_charge
    have hquotient : eta / 2 ≤
        (eta / 2 * residualCharge beta (fun phase => 1 - beta phase) base K) /
          (1 - ∏ phase : Fin K, beta phase) := by
      apply (le_div_iff₀ hbeta_denom).2
      nlinarith [hstop]
    have hcharge_div := div_le_div_of_nonneg_right hsum_charge hbeta_denom.le
    exact hquotient.trans (hcharge_div.trans hsum)
  by_contra hnone
  have hnone' : ∀ player, value base player <
      eta / (2 * (Fintype.card ι : ℝ)) := by
    intro player
    exact lt_of_not_ge (fun hge => hnone ⟨player, hge⟩)
  have hsum_upper : ∑ player, value base player <
      ∑ player : ι, eta / (2 * (Fintype.card ι : ℝ)) := by
    apply Finset.sum_lt_sum (s := (Finset.univ : Finset ι))
    · intro player hplayer
      exact (hnone' player).le
    · let player0 : ι := Classical.choice ‹Nonempty ι›
      exact ⟨player0, Finset.mem_univ _, hnone' player0⟩
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [Finset.sum_const, nsmul_eq_mul] at hsum_upper
  have htarget :
      (Fintype.card ι : ℝ) * (eta / (2 * (Fintype.card ι : ℝ))) = eta / 2 := by
    field_simp
  rw [Finset.card_univ] at hsum_upper
  rw [htarget] at hsum_upper
  linarith

end

end Math.FiniteCycleAggregate
