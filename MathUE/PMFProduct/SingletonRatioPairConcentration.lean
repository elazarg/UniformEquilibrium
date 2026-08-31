/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.SmallHazardBounds
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences

/-!
# Pair concentration from a vanishing singleton ratio

This module is independent of quitting-game semantics.  It treats a finite
family of Bernoulli rates and shows that a positive-absorption family whose
exact singleton mass is a vanishing fraction of absorption concentrates on a
fixed pair of coordinates acting with probability one.
-/

noncomputable section

namespace Math.PMFProduct

open Filter
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem continuous_one_sub_continueMass :
    Continuous fun rates : ι → ℝ => 1 - continueMass rates := by
  unfold continueMass
  exact continuous_const.sub
    (continuous_finsetProd _ fun player _ =>
      continuous_const.sub (continuous_apply player))

private theorem continuous_singletonMass :
    Continuous (singletonMass : (ι → ℝ) → ℝ) := by
  unfold singletonMass coalitionMass
  exact continuous_finsetSum _ fun player _ =>
    (continuous_finsetProd _ fun coordinate _ => continuous_apply coordinate).mul
      (continuous_finsetProd _ fun coordinate _ =>
        continuous_const.sub (continuous_apply coordinate))

private theorem singletonMass_nonneg
    (rates : ι → ℝ) (h0 : ∀ player, 0 ≤ rates player)
    (h1 : ∀ player, rates player ≤ 1) :
    0 ≤ singletonMass rates := by
  unfold singletonMass
  exact Finset.sum_nonneg fun player _ =>
    coalitionMass_nonneg rates h0 h1 {player}

private theorem singletonMass_term_nonneg
    {rates : ι → ℝ} (h0 : ∀ player, 0 ≤ rates player)
    (h1 : ∀ player, rates player ≤ 1) (player : ι) :
    0 ≤ rates player *
      ∏ other ∈ Finset.univ.erase player, (1 - rates other) :=
  mul_nonneg (h0 player)
    (Finset.prod_nonneg fun other _ => by linarith [h1 other])

/-- If singleton mass is a vanishing fraction of positive absorption, then a
fixed pair of distinct coordinates has product tending to one along a strict
subsequence. -/
theorem exists_pair_subsequence_mul_tendsto_one_of_singletonMass_ratio_tendsto_zero
    (rates : ℕ → ι → ℝ) (delta : ℕ → ℝ)
    (h0 : ∀ n player, 0 ≤ rates n player)
    (h1 : ∀ n player, rates n player ≤ 1)
    (hdelta : Tendsto delta atTop (nhds 0))
    (hratio : ∀ n, singletonMass (rates n) ≤
      delta n * (1 - continueMass (rates n)))
    (habsorption : ∀ n, 0 < 1 - continueMass (rates n))
    (hcard : 1 < Fintype.card ι) :
    ∃ (first second : ι) (subsequence : ℕ → ℕ),
      first ≠ second ∧ StrictMono subsequence ∧
        Tendsto (fun k =>
          rates (subsequence k) first * rates (subsequence k) second)
          atTop (nhds 1) := by
  classical
  have hchoose : (0 : ℝ) < ((Fintype.card ι).choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hcard
  have hfloor : ∀ n, 1 - delta n ≤
      ((Fintype.card ι).choose 2 : ℝ) *
        (1 - continueMass (rates n)) := by
    intro n
    have hsplit := singletonMass_add_collisionMass (rates n)
    have hcollision := collisionMass_le_choose_card_mul_absorption_sq
      (rates n) (h0 n) (h1 n)
    have hkey : (1 - delta n) * (1 - continueMass (rates n)) ≤
        (((Fintype.card ι).choose 2 : ℝ) *
          (1 - continueMass (rates n))) *
            (1 - continueMass (rates n)) := by
      nlinarith [hratio n]
    exact le_of_mul_le_mul_right hkey (habsorption n)
  have hdeltaSmall : ∀ᶠ n in atTop, delta n < 1 / 2 :=
    hdelta.eventually_lt_const (by norm_num)
  have hafloor : ∀ᶠ n in atTop,
      (1 : ℝ) ≤ 2 * ((Fintype.card ι).choose 2 : ℝ) *
        (1 - continueMass (rates n)) := by
    filter_upwards [hdeltaSmall] with n hn
    nlinarith [hfloor n]
  have hbox : IsCompact (Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, rates n ∈
      Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1 := by
    intro n player _
    exact ⟨h0 n player, h1 n player⟩
  obtain ⟨limit, hlimitMem, subsequence, hsubsequence, hlimit⟩ :=
    hbox.tendsto_subseq hmem
  have hlimit0 : ∀ player, 0 ≤ limit player :=
    fun player => (hlimitMem player (Set.mem_univ player)).1
  have hlimit1 : ∀ player, limit player ≤ 1 :=
    fun player => (hlimitMem player (Set.mem_univ player)).2
  have hAbsorptionLimit : Tendsto (fun k =>
      1 - continueMass (rates (subsequence k))) atTop
      (nhds (1 - continueMass limit)) :=
    (continuous_one_sub_continueMass.tendsto limit).comp hlimit
  have hSingletonLimit : Tendsto (fun k =>
      singletonMass (rates (subsequence k))) atTop
      (nhds (singletonMass limit)) :=
    (continuous_singletonMass.tendsto limit).comp hlimit
  have hlimitAbsorptionPositive : 0 < 1 - continueMass limit := by
    have heventual : ∀ᶠ k in atTop,
        (1 : ℝ) ≤ 2 * ((Fintype.card ι).choose 2 : ℝ) *
          (1 - continueMass (rates (subsequence k))) :=
      hsubsequence.tendsto_atTop.eventually hafloor
    have hscaled : Tendsto (fun k =>
        2 * ((Fintype.card ι).choose 2 : ℝ) *
          (1 - continueMass (rates (subsequence k)))) atTop
        (nhds (2 * ((Fintype.card ι).choose 2 : ℝ) *
          (1 - continueMass limit))) :=
      hAbsorptionLimit.const_mul _
    nlinarith [ge_of_tendsto hscaled heventual, hchoose]
  have hSingletonZero : Tendsto (fun n => singletonMass (rates n)) atTop
      (nhds 0) := by
    have habsDelta : Tendsto (fun n => |delta n|) atTop (nhds 0) := by
      simpa using hdelta.abs
    refine squeeze_zero (g := fun n => |delta n|) (fun n => ?_)
      (fun n => ?_) habsDelta
    · exact singletonMass_nonneg (rates n) (h0 n) (h1 n)
    · have habsorption0 := (habsorption n).le
      have habsorption1 : 1 - continueMass (rates n) ≤ 1 := by
        have := continueMass_nonneg (h1 n)
        linarith
      nlinarith [hratio n, abs_nonneg (delta n), le_abs_self (delta n)]
  have hlimitSingletonZero : singletonMass limit = 0 :=
    tendsto_nhds_unique hSingletonLimit
      (hSingletonZero.comp hsubsequence.tendsto_atTop)
  have hterms : ∀ player,
      limit player *
        ∏ other ∈ Finset.univ.erase player, (1 - limit other) = 0 := by
    have hnonnegative : ∀ player ∈ (Finset.univ : Finset ι),
        0 ≤ limit player *
          ∏ other ∈ Finset.univ.erase player, (1 - limit other) :=
      fun player _ => singletonMass_term_nonneg hlimit0 hlimit1 player
    have hsum : (∑ player,
        limit player *
          ∏ other ∈ Finset.univ.erase player, (1 - limit other)) = 0 := by
      rw [← hlimitSingletonZero]
      unfold singletonMass
      apply Finset.sum_congr rfl
      intro player _
      exact (coalitionMass_singleton limit player).symm
    intro player
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonnegative).mp hsum
      player (Finset.mem_univ player)
  let sure : Finset ι := Finset.univ.filter fun player => limit player = 1
  have hsureCard : 1 < sure.card := by
    by_contra hnot
    rcases Nat.lt_or_ge sure.card 1 with hzero | hone
    · have hsureEmpty : sure = ∅ :=
        Finset.card_eq_zero.mp (Nat.lt_one_iff.mp hzero)
      have hnotSure : ∀ player, limit player ≠ 1 := by
        intro player hplayer
        have : player ∈ sure := by simp [sure, hplayer]
        rw [hsureEmpty] at this
        exact (Finset.notMem_empty player) this
      have hlimitZero : ∀ player, limit player = 0 := by
        intro player
        have hproduct : 0 <
            ∏ other ∈ Finset.univ.erase player, (1 - limit other) :=
          Finset.prod_pos fun other _ =>
            sub_pos.mpr (lt_of_le_of_ne (hlimit1 other) (hnotSure other))
        rcases mul_eq_zero.mp (hterms player) with hleft | hright
        · exact hleft
        · exact (hproduct.ne' hright).elim
      have : 1 - continueMass limit = 0 := by
        simp [continueMass, hlimitZero]
      rw [this] at hlimitAbsorptionPositive
      exact (lt_irrefl 0) hlimitAbsorptionPositive
    · have hsureOne : sure.card = 1 :=
        le_antisymm (Nat.not_lt.mp hnot) hone
      obtain ⟨only, honly⟩ := Finset.card_eq_one.mp hsureOne
      have honlySure : limit only = 1 := by
        have : only ∈ sure := by rw [honly]; simp
        simpa [sure] using this
      have hnotSure : ∀ player, player ≠ only → limit player ≠ 1 := by
        intro player hne hplayer
        have : player ∈ sure := by simp [sure, hplayer]
        rw [honly, Finset.mem_singleton] at this
        exact hne this
      have hproduct : 0 <
          ∏ other ∈ Finset.univ.erase only, (1 - limit other) :=
        Finset.prod_pos fun other hother =>
          sub_pos.mpr (lt_of_le_of_ne (hlimit1 other)
            (hnotSure other (Finset.ne_of_mem_erase hother)))
      have hzeroTerm := hterms only
      rw [honlySure, one_mul] at hzeroTerm
      exact (hproduct.ne' hzeroTerm).elim
  obtain ⟨first, hfirst, second, hsecond, hne⟩ :=
    Finset.one_lt_card.mp hsureCard
  have hfirstLimit : limit first = 1 := by
    simpa [sure] using hfirst
  have hsecondLimit : limit second = 1 := by
    simpa [sure] using hsecond
  refine ⟨first, second, subsequence, hne, hsubsequence, ?_⟩
  have hfirstTendsto : Tendsto (fun k => rates (subsequence k) first)
      atTop (nhds (limit first)) := (tendsto_pi_nhds.mp hlimit) first
  have hsecondTendsto : Tendsto (fun k => rates (subsequence k) second)
      atTop (nhds (limit second)) := (tendsto_pi_nhds.mp hlimit) second
  have hmul := hfirstTendsto.mul hsecondTendsto
  rw [hfirstLimit, hsecondLimit, one_mul] at hmul
  exact hmul

end Math.PMFProduct
