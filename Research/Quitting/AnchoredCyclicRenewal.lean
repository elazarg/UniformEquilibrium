/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.AnchoredCyclicScreen

/-!
# The anchored cyclic renewal system solved in closed form

`quittingAnchoredCyclicOnPathValue_renewal`
(`Research/Quitting/AnchoredCyclicScreen.lean`) records one step of the linear
recursion `U^k = p_k * r({w k}) + (1 - p_k) * U^{k+1}` around a period-`m`
single-quitter cycle.  This module iterates that step and solves the system.

* `IsAnchoredCyclicRenewalSolution` names the recursion as a property of a
  phase-indexed family, and
  `quittingAnchoredCyclicOnPathValue_isAnchoredCyclicRenewalSolution` shows the
  on-path value has it.
* `isAnchoredCyclicRenewalSolution_iterate` unrolls any solution `fuel` phases:
  the value is the renewal-weighted sum of the singleton rows visited, plus the
  surviving mass times the value at the phase reached.  One full turn closes
  the loop, because a turn returns to the starting phase and multiplies the
  survival by `∏ k, (1 - p_k)`.
* Under `∏ k, (1 - p_k) ≠ 1` the system has exactly one solution
  (`eq_of_isAnchoredCyclicRenewalSolution`), given in closed form by
  `isAnchoredCyclicRenewalSolution_eq_div`.
* Under `∏ k, (1 - p_k) < 1` the renewal weights, normalized by `1 - ∏ k,
  (1 - p_k)`, are nonnegative and sum to one, so the on-path value of every
  anchored cyclic profile lies in the convex hull of the singleton rows of the
  scheduled players
  (`quittingAnchoredCyclicOnPathValue_mem_convexHull`).

The convex-hull placement is a restriction on what a single-quitter periodic
profile can pay: it is decided by the schedule's singleton geometry alone,
before any best-response statistic is computed.

The last section identifies the refusal branch of the periodic best-response
statistic.  Refusing to quit against an anchored cyclic profile leaves the same
schedule with the refuser's own phases carrying hazard zero, so
`quittingPeriodicWindowRefusalValue_anchoredCyclic` equates
`quittingPeriodicWindowRefusalValue` with the on-path value of that zeroed
schedule, in the absorbing and the never-absorbing branch alike.  Combined with
the closed form this turns the refusal hypothesis of
`exists_anchoredCyclicResponse_gain` into a comparison of finite sums, which is
`exists_anchoredCyclicResponse_gain_of_refusalOnPathValue_le`.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-! ## Survival and renewal weights around the cycle -/

/-- Survival through the `fuel` phases starting at `phase`: the product of the
continuation probabilities `1 - p` along the orbit. -/
def quittingAnchoredCyclicPrefixSurvival
    (hazard : Fin m → ℝ) (phase : Fin m) (fuel : ℕ) : ℝ :=
  quittingCyclicPrefixWeight (fun k ↦ 1 - hazard k) phase fuel

@[simp] theorem quittingAnchoredCyclicPrefixSurvival_zero
    (hazard : Fin m → ℝ) (phase : Fin m) :
    quittingAnchoredCyclicPrefixSurvival hazard phase 0 = 1 :=
  quittingCyclicPrefixWeight_zero _ _

theorem quittingAnchoredCyclicPrefixSurvival_succ
    (hazard : Fin m → ℝ) (phase : Fin m) (fuel : ℕ) :
    quittingAnchoredCyclicPrefixSurvival hazard phase (fuel + 1) =
      quittingAnchoredCyclicPrefixSurvival hazard phase fuel *
        (1 - hazard (quittingCyclicOrbit phase fuel)) :=
  quittingCyclicPrefixWeight_succ _ _ _

/-- One full turn multiplies the survival by the product of all the cycle's
continuation probabilities, whatever the starting phase. -/
theorem quittingAnchoredCyclicPrefixSurvival_card
    (hazard : Fin m → ℝ) (phase : Fin m) :
    quittingAnchoredCyclicPrefixSurvival hazard phase m =
      ∏ k, (1 - hazard k) :=
  quittingCyclicPrefixWeight_card _ _

theorem quittingAnchoredCyclicPrefixSurvival_nonneg
    {hazard : Fin m → ℝ} (h1 : ∀ k, hazard k ≤ 1) (phase : Fin m) (fuel : ℕ) :
    0 ≤ quittingAnchoredCyclicPrefixSurvival hazard phase fuel :=
  quittingCyclicPrefixWeight_nonneg _ (fun k ↦ by linarith [h1 k]) phase fuel

/-- The renewal weight of the exit scheduled `offset` phases after `phase`:
survival through the intervening phases times the hazard of the phase
reached. -/
def quittingAnchoredCyclicRenewalWeight
    (hazard : Fin m → ℝ) (phase : Fin m) (offset : ℕ) : ℝ :=
  quittingAnchoredCyclicPrefixSurvival hazard phase offset *
    hazard (quittingCyclicOrbit phase offset)

theorem quittingAnchoredCyclicRenewalWeight_nonneg
    {hazard : Fin m → ℝ} (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (phase : Fin m) (offset : ℕ) :
    0 ≤ quittingAnchoredCyclicRenewalWeight hazard phase offset :=
  mul_nonneg (quittingAnchoredCyclicPrefixSurvival_nonneg h1 phase offset) (h0 _)

/-- The renewal weights telescope against the survival product: absorbing
within the first `fuel` phases and surviving them are complementary. -/
theorem sum_quittingAnchoredCyclicRenewalWeight
    (hazard : Fin m → ℝ) (phase : Fin m) (fuel : ℕ) :
    ∑ offset ∈ Finset.range fuel,
        quittingAnchoredCyclicRenewalWeight hazard phase offset =
      1 - quittingAnchoredCyclicPrefixSurvival hazard phase fuel := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [Finset.sum_range_succ, ih, quittingAnchoredCyclicPrefixSurvival_succ,
        quittingAnchoredCyclicRenewalWeight]
      ring

/-- Over one full turn the renewal weights sum to the cycle's total absorption
probability. -/
theorem sum_range_card_quittingAnchoredCyclicRenewalWeight
    (hazard : Fin m → ℝ) (phase : Fin m) :
    ∑ offset ∈ Finset.range m,
        quittingAnchoredCyclicRenewalWeight hazard phase offset =
      1 - ∏ k, (1 - hazard k) := by
  rw [sum_quittingAnchoredCyclicRenewalWeight,
    quittingAnchoredCyclicPrefixSurvival_card]

/-- The renewal numerator seen from `phase`: the renewal-weighted sum of the
singleton rows of the players scheduled around one turn. -/
def quittingAnchoredCyclicRenewalSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (phase : Fin m) : Payoff ι :=
  fun who ↦ ∑ offset ∈ Finset.range m,
    quittingAnchoredCyclicRenewalWeight hazard phase offset *
      reward (quittingSingletonTerminal (w (quittingCyclicOrbit phase offset))) who

/-! ## Solutions of the renewal system -/

/-- A phase-indexed family solving the anchored cyclic renewal recursion
`V^k = p_k * r({w k}) + (1 - p_k) * V^{k+1}`. -/
def IsAnchoredCyclicRenewalSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (value : Fin m → Payoff ι) : Prop :=
  ∀ phase who,
    value phase who =
      hazard phase * reward (quittingSingletonTerminal (w phase)) who +
        (1 - hazard phase) * value (finRotate m phase) who

/-- The anchored cyclic on-path value solves the renewal system. -/
theorem quittingAnchoredCyclicOnPathValue_isAnchoredCyclicRenewalSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) :
    IsAnchoredCyclicRenewalSolution reward w hazard
      (quittingAnchoredCyclicOnPathValue reward w hazard h0 h1) :=
  fun phase who ↦
    quittingAnchoredCyclicOnPathValue_renewal reward w hazard h0 h1 phase who

omit [Fintype ι] [DecidableEq ι] in
/-- **Unrolling the renewal system.**  After `fuel` phases a solution has paid
the renewal-weighted singleton rows of the phases passed and retains the
surviving mass against the value at the phase reached. -/
theorem isAnchoredCyclicRenewalSolution_iterate
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {w : Fin m → ι} {hazard : Fin m → ℝ} {value : Fin m → Payoff ι}
    (hvalue : IsAnchoredCyclicRenewalSolution reward w hazard value)
    (phase : Fin m) (who : ι) (fuel : ℕ) :
    value phase who =
      (∑ offset ∈ Finset.range fuel,
          quittingAnchoredCyclicRenewalWeight hazard phase offset *
            reward (quittingSingletonTerminal
              (w (quittingCyclicOrbit phase offset))) who) +
        quittingAnchoredCyclicPrefixSurvival hazard phase fuel *
          value (quittingCyclicOrbit phase fuel) who := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      have hstep := hvalue (quittingCyclicOrbit phase fuel) who
      rw [Finset.sum_range_succ, quittingAnchoredCyclicPrefixSurvival_succ,
        quittingCyclicOrbit_succ, quittingAnchoredCyclicRenewalWeight]
      linear_combination ih +
        quittingAnchoredCyclicPrefixSurvival hazard phase fuel * hstep

omit [Fintype ι] [DecidableEq ι] in
/-- **One full turn closes the system.**  A solution reproduces itself after
`m` phases, with the cycle's total absorption paying the renewal sum. -/
theorem isAnchoredCyclicRenewalSolution_turn
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {w : Fin m → ι} {hazard : Fin m → ℝ} {value : Fin m → Payoff ι}
    (hvalue : IsAnchoredCyclicRenewalSolution reward w hazard value)
    (phase : Fin m) (who : ι) :
    value phase who =
      quittingAnchoredCyclicRenewalSum reward w hazard phase who +
        (∏ k, (1 - hazard k)) * value phase who := by
  have hiterate := isAnchoredCyclicRenewalSolution_iterate hvalue phase who m
  rwa [quittingCyclicOrbit_card, quittingAnchoredCyclicPrefixSurvival_card] at hiterate

omit [Fintype ι] [DecidableEq ι] in
/-- **The closed form.**  Away from the degenerate case `∏ k, (1 - p_k) = 1`
the renewal system determines its solution as a ratio of finite sums. -/
theorem isAnchoredCyclicRenewalSolution_eq_div
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {w : Fin m → ι} {hazard : Fin m → ℝ} {value : Fin m → Payoff ι}
    (hvalue : IsAnchoredCyclicRenewalSolution reward w hazard value)
    (hcontraction : ∏ k, (1 - hazard k) ≠ 1) (phase : Fin m) (who : ι) :
    value phase who =
      quittingAnchoredCyclicRenewalSum reward w hazard phase who /
        (1 - ∏ k, (1 - hazard k)) := by
  have hne : (1 : ℝ) - ∏ k, (1 - hazard k) ≠ 0 := sub_ne_zero_of_ne (Ne.symm hcontraction)
  rw [eq_div_iff hne]
  linear_combination isAnchoredCyclicRenewalSolution_turn hvalue phase who

omit [Fintype ι] [DecidableEq ι] in
/-- **Uniqueness.**  Away from `∏ k, (1 - p_k) = 1` the renewal system has at
most one solution. -/
theorem eq_of_isAnchoredCyclicRenewalSolution
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {w : Fin m → ι} {hazard : Fin m → ℝ} {first second : Fin m → Payoff ι}
    (hfirst : IsAnchoredCyclicRenewalSolution reward w hazard first)
    (hsecond : IsAnchoredCyclicRenewalSolution reward w hazard second)
    (hcontraction : ∏ k, (1 - hazard k) ≠ 1) :
    first = second := by
  funext phase who
  rw [isAnchoredCyclicRenewalSolution_eq_div hfirst hcontraction phase who,
    isAnchoredCyclicRenewalSolution_eq_div hsecond hcontraction phase who]

/-- The on-path value in closed form: the renewal-weighted average of the
scheduled singleton rows, normalized by the cycle's total absorption. -/
theorem quittingAnchoredCyclicOnPathValue_eq_div
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hcontraction : ∏ k, (1 - hazard k) ≠ 1) (phase : Fin m) (who : ι) :
    quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase who =
      quittingAnchoredCyclicRenewalSum reward w hazard phase who /
        (1 - ∏ k, (1 - hazard k)) :=
  isAnchoredCyclicRenewalSolution_eq_div
    (quittingAnchoredCyclicOnPathValue_isAnchoredCyclicRenewalSolution reward w
      hazard h0 h1) hcontraction phase who

/-! ## Convex-hull placement of the on-path value -/

/-- **The on-path value is an average of the scheduled singleton rows.**  When
the cycle absorbs — `∏ k, (1 - p_k) < 1` — the normalized renewal weights are
nonnegative and sum to one, so the anchored cyclic on-path value lies in the
convex hull of the singleton reward rows of the scheduled players. -/
theorem quittingAnchoredCyclicOnPathValue_mem_convexHull
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hcontraction : ∏ k, (1 - hazard k) < 1) (phase : Fin m) :
    quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase ∈
      convexHull ℝ (Set.range fun k : Fin m ↦
        reward (quittingSingletonTerminal (w k))) := by
  set total : ℝ := 1 - ∏ k, (1 - hazard k) with htotal
  have hpos : 0 < total := by rw [htotal]; linarith
  set weight : ℕ → ℝ := fun offset ↦
    quittingAnchoredCyclicRenewalWeight hazard phase offset / total with hweight
  set point : ℕ → Payoff ι := fun offset ↦
    reward (quittingSingletonTerminal (w (quittingCyclicOrbit phase offset)))
    with hpoint
  have hsum : ∑ offset ∈ Finset.range m, weight offset = 1 := by
    rw [hweight, ← Finset.sum_div,
      sum_range_card_quittingAnchoredCyclicRenewalWeight, ← htotal]
    exact div_self hpos.ne'
  have hmem : quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase =
      ∑ offset ∈ Finset.range m, weight offset • point offset := by
    funext player
    rw [Finset.sum_apply]
    rw [quittingAnchoredCyclicOnPathValue_eq_div reward w hazard h0 h1
      (by rw [htotal] at hpos; linarith) phase player, ← htotal,
      quittingAnchoredCyclicRenewalSum, eq_comm, Finset.sum_div]
    exact Finset.sum_congr rfl fun offset _ ↦ by
      rw [Pi.smul_apply, smul_eq_mul, hweight, hpoint, div_mul_eq_mul_div]
  rw [hmem]
  refine (convex_convexHull ℝ _).sum_mem (fun offset _ ↦ ?_) hsum
    (fun offset _ ↦ subset_convexHull ℝ _ (Set.mem_range_self _))
  exact div_nonneg
    (quittingAnchoredCyclicRenewalWeight_nonneg h0 h1 phase offset) hpos.le

/-! ## Refusal is the anchored cyclic profile with the refuser's phases zeroed

A player who refuses to quit against an anchored cyclic profile faces exactly
the anchored cyclic cycle of the same schedule with its own phases carrying
hazard zero: at a phase it owns, the prescribed quit is deleted by the refusal,
and at every other phase nothing changes.  The refusal value is therefore the
on-path value of that zeroed profile.
-/

/-- The anchored cyclic hazard vector with the phases owned by `who` zeroed. -/
def quittingAnchoredCyclicRefusalHazard
    (w : Fin m → ι) (hazard : Fin m → ℝ) (who : ι) : Fin m → ℝ :=
  fun phase ↦ if w phase = who then 0 else hazard phase

omit [Fintype ι] in
theorem quittingAnchoredCyclicRefusalHazard_nonneg
    {hazard : Fin m → ℝ} (h0 : ∀ k, 0 ≤ hazard k) (w : Fin m → ι) (who : ι) :
    ∀ k, 0 ≤ quittingAnchoredCyclicRefusalHazard w hazard who k := by
  intro k
  unfold quittingAnchoredCyclicRefusalHazard
  split_ifs with hk
  · exact le_refl 0
  · exact h0 k

omit [Fintype ι] in
theorem quittingAnchoredCyclicRefusalHazard_le_one
    {hazard : Fin m → ℝ} (h1 : ∀ k, hazard k ≤ 1) (w : Fin m → ι) (who : ι) :
    ∀ k, quittingAnchoredCyclicRefusalHazard w hazard who k ≤ 1 := by
  intro k
  unfold quittingAnchoredCyclicRefusalHazard
  split_ifs with hk
  · norm_num
  · exact h1 k

omit [Fintype ι] [DecidableEq ι] in
/-- A quitting coin with no Quit mass is pure Continue. -/
theorem quittingHazardCoin_eq_pure_false {rate : ℝ} (hrate0 : 0 ≤ rate)
    (hrate1 : rate ≤ 1)
    (hzero : (quittingHazardCoin rate hrate0 hrate1 true).toReal = 0) :
    quittingHazardCoin rate hrate0 hrate1 = PMF.pure false := by
  have hrate : rate = 0 := by
    rw [← quittingHazardCoin_true_toReal rate hrate0 hrate1]
    exact hzero
  subst hrate
  refine PMF.ext fun action ↦ ?_
  cases action <;> simp [quittingHazardCoin, PMF.ofFintype_apply]

omit [Fintype ι] in
/-- The one-phase Continue value against an anchored cyclic root, written with
the zeroed hazard: a phase owned by `who` contributes no absorption to a
refusing `who`. -/
theorem quittingAnchoredCyclicContinueValue_eq_refusalHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (phase : Fin m) (who : ι) (next : ℝ) :
    quittingAnchoredCyclicContinueValue reward w hazard phase who next =
      quittingAnchoredCyclicRefusalHazard w hazard who phase *
          reward (quittingSingletonTerminal (w phase)) who +
        (1 - quittingAnchoredCyclicRefusalHazard w hazard who phase) * next := by
  unfold quittingAnchoredCyclicContinueValue quittingAnchoredCyclicRefusalHazard
  by_cases hwho : who = w phase
  · rw [if_pos hwho, if_pos hwho.symm]
    ring
  · rw [if_neg hwho, if_neg (fun hcontra ↦ hwho hcontra.symm)]

/-- Refusal satisfies the zeroed renewal recursion date by date. -/
theorem quittingAnchoredCyclicRefusal_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (phase : Fin m) (who : ι) (time : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward
        (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
          phase) who none time =
      quittingAnchoredCyclicRefusalHazard w hazard who
            (quittingCyclicOrbit phase time) *
          reward (quittingSingletonTerminal
            (w (quittingCyclicOrbit phase time))) who +
        (1 - quittingAnchoredCyclicRefusalHazard w hazard who
            (quittingCyclicOrbit phase time)) *
          quittingRootSequencePureTimeTerminalValue reward
            (quittingCyclicRootSequence
              (quittingAnchoredCyclicCycle w hazard h0 h1) phase) who none
            (time + 1) := by
  rw [quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents,
    quittingFixedOpponentsContinue_anchoredCyclic reward w hazard h0 h1 phase who
      time _,
    quittingAnchoredCyclicContinueValue_eq_refusalHazard]

omit [Fintype ι] [DecidableEq ι] in
/-- Two families obeying the same one-step renewal recursion — one along the
calendar, one around the cycle — differ by the survival factor accumulated
between the dates compared. -/
theorem sub_eq_quittingAnchoredCyclicPrefixSurvival_mul
    {rate atom : Fin m → ℝ} {phase : Fin m}
    {calendar : ℕ → ℝ} {cyclic : Fin m → ℝ}
    (hcalendar : ∀ time, calendar time =
      rate (quittingCyclicOrbit phase time) *
          atom (quittingCyclicOrbit phase time) +
        (1 - rate (quittingCyclicOrbit phase time)) * calendar (time + 1))
    (hcyclic : ∀ k, cyclic k =
      rate k * atom k + (1 - rate k) * cyclic (finRotate m k))
    (fuel : ℕ) :
    calendar 0 - cyclic phase =
      quittingAnchoredCyclicPrefixSurvival rate phase fuel *
        (calendar fuel - cyclic (quittingCyclicOrbit phase fuel)) := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      have hstepCalendar := hcalendar fuel
      have hstepCyclic := hcyclic (quittingCyclicOrbit phase fuel)
      rw [quittingAnchoredCyclicPrefixSurvival_succ, quittingCyclicOrbit_succ]
      linear_combination ih +
        quittingAnchoredCyclicPrefixSurvival rate phase fuel *
          (hstepCalendar - hstepCyclic)

/-- A hazard vector with one positive entry has cycle survival below one. -/
theorem prod_one_sub_lt_one_of_pos {rate : Fin m → ℝ}
    (h0 : ∀ k, 0 ≤ rate k) (h1 : ∀ k, rate k ≤ 1) {k₀ : Fin m}
    (hpos : 0 < rate k₀) :
    ∏ k, (1 - rate k) < 1 := by
  have hrest : ∏ k ∈ Finset.univ.erase k₀, (1 - rate k) ≤ 1 :=
    Finset.prod_le_one (fun k _ ↦ by linarith [h1 k]) (fun k _ ↦ by linarith [h0 k])
  have hnonneg : (0 : ℝ) ≤ 1 - rate k₀ := by linarith [h1 k₀]
  have hsplit : ∏ k, (1 - rate k) =
      (∏ k ∈ Finset.univ.erase k₀, (1 - rate k)) * (1 - rate k₀) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ k₀)).symm
  calc ∏ k, (1 - rate k) =
        (∏ k ∈ Finset.univ.erase k₀, (1 - rate k)) * (1 - rate k₀) := hsplit
    _ ≤ 1 * (1 - rate k₀) := mul_le_mul_of_nonneg_right hrest hnonneg
    _ < 1 := by linarith

/-- **The refusal identity, nondegenerate branch.**  When the zeroed cycle
still absorbs, refusal against an anchored cyclic profile pays exactly the
on-path value of the same schedule with the refuser's phases zeroed. -/
theorem quittingPeriodicWindowRefusalValue_anchoredCyclic_of_ne_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (phase : Fin m) (who : ι)
    (hcontraction :
      ∏ k, (1 - quittingAnchoredCyclicRefusalHazard w hazard who k) ≠ 1) :
    quittingPeriodicWindowRefusalValue reward
        (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
          phase) who =
      quittingAnchoredCyclicOnPathValue reward w
        (quittingAnchoredCyclicRefusalHazard w hazard who)
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
        (quittingAnchoredCyclicRefusalHazard_le_one h1 w who) phase who := by
  have hdiff := sub_eq_quittingAnchoredCyclicPrefixSurvival_mul
    (rate := quittingAnchoredCyclicRefusalHazard w hazard who)
    (atom := fun k ↦ reward (quittingSingletonTerminal (w k)) who)
    (phase := phase)
    (calendar := fun time ↦ quittingRootSequencePureTimeTerminalValue reward
      (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
        phase) who none time)
    (cyclic := fun k ↦ quittingAnchoredCyclicOnPathValue reward w
      (quittingAnchoredCyclicRefusalHazard w hazard who)
      (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
      (quittingAnchoredCyclicRefusalHazard_le_one h1 w who) k who)
    (quittingAnchoredCyclicRefusal_succ reward w hazard h0 h1 phase who)
    (fun k ↦ quittingAnchoredCyclicOnPathValue_renewal reward w
      (quittingAnchoredCyclicRefusalHazard w hazard who)
      (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
      (quittingAnchoredCyclicRefusalHazard_le_one h1 w who) k who) m
  rw [quittingAnchoredCyclicPrefixSurvival_card, quittingCyclicOrbit_card] at hdiff
  have hpos : 0 < m := phase.pos
  obtain ⟨pred, hpred⟩ : ∃ pred, m = pred + 1 := ⟨m - 1, by omega⟩
  have hreturn : quittingRootSequencePureTimeTerminalValue reward
      (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
        phase) who none m =
    quittingRootSequencePureTimeTerminalValue reward
      (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
        phase) who none 0 := by
    have hshift := quittingRootSequencePureTimeTerminalValue_none_shift_period
      reward (quittingCyclicRootSequence
        (quittingAnchoredCyclicCycle w hazard h0 h1) phase) who pred
      (fun k ↦ by
        rw [← hpred]
        exact quittingCyclicRootSequence_add_period _ _ k) 0
    rw [← hpred] at hshift
    simpa using hshift
  rw [hreturn] at hdiff
  have hne : (1 : ℝ) -
      ∏ k, (1 - quittingAnchoredCyclicRefusalHazard w hazard who k) ≠ 0 :=
    sub_ne_zero_of_ne (Ne.symm hcontraction)
  have hzero : quittingRootSequencePureTimeTerminalValue reward
      (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
        phase) who none 0 -
      quittingAnchoredCyclicOnPathValue reward w
        (quittingAnchoredCyclicRefusalHazard w hazard who)
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
        (quittingAnchoredCyclicRefusalHazard_le_one h1 w who) phase who = 0 := by
    refine (mul_eq_zero.1 ?_).resolve_left hne
    linarith [hdiff]
  unfold quittingPeriodicWindowRefusalValue
  linarith [hzero]

/-- **The refusal identity, degenerate branch.**  When the refuser owns every
phase carrying positive hazard, the zeroed cycle never absorbs; refusal and the
zeroed on-path value are both zero. -/
theorem quittingPeriodicWindowRefusalValue_anchoredCyclic_of_forall_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (phase : Fin m) (who : ι)
    (hzero : ∀ k, quittingAnchoredCyclicRefusalHazard w hazard who k = 0) :
    quittingPeriodicWindowRefusalValue reward
        (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
          phase) who = 0 ∧
      quittingAnchoredCyclicOnPathValue reward w
        (quittingAnchoredCyclicRefusalHazard w hazard who)
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
        (quittingAnchoredCyclicRefusalHazard_le_one h1 w who) phase who = 0 := by
  have hcoinZero : ∀ k : Fin m, w k ≠ who → hazard k = 0 := by
    intro k hk
    have := hzero k
    rwa [quittingAnchoredCyclicRefusalHazard, if_neg hk] at this
  have hrefusalRoot : ∀ time,
      quittingRootSequenceUpdate
          (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
            phase) who (quittingPureTimeHazard none) time =
        (quittingAllContinueRoot : ι → PMF Bool) := by
    intro time
    funext player
    by_cases hplayer : player = who
    · subst hplayer
      simp [quittingRootSequenceUpdate, quittingAllContinueRoot]
    · rw [quittingRootSequenceUpdate, Function.update_of_ne hplayer]
      show quittingAnchoredCyclicCycle w hazard h0 h1
        (quittingCyclicOrbit phase time) player = _
      by_cases howner : player = w (quittingCyclicOrbit phase time)
      · have hne : w (quittingCyclicOrbit phase time) ≠ who := by
          rw [← howner]; exact hplayer
        rw [quittingAnchoredCyclicCycle, howner, quittingSoloMixedRoot_self,
          quittingHazardCoin_eq_pure_false _ _
            (by simp [hcoinZero (quittingCyclicOrbit phase time) hne])]
        rfl
      · rw [quittingAnchoredCyclicCycle, quittingSoloMixedRoot_of_ne howner]
        rfl
  have hcycleRoot : ∀ time,
      quittingCyclicRootSequence (quittingAnchoredCyclicCycle w
          (quittingAnchoredCyclicRefusalHazard w hazard who)
          (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
          (quittingAnchoredCyclicRefusalHazard_le_one h1 w who)) phase time =
        (quittingAllContinueRoot : ι → PMF Bool) := by
    intro time
    show quittingAnchoredCyclicCycle w _ _ _ (quittingCyclicOrbit phase time) = _
    rw [quittingAnchoredCyclicCycle, quittingHazardCoin_eq_pure_false _ _
      (by simp [hzero (quittingCyclicOrbit phase time)]), quittingSoloMixedRoot,
      quittingAllContinueRoot_update_false]
  refine ⟨?_, ?_⟩
  · unfold quittingPeriodicWindowRefusalValue
      quittingRootSequencePureTimeTerminalValue
      quittingRootSequenceHazardTerminalValue
    exact quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from reward _
      who 0 (fun time _ ↦ hrefusalRoot time)
  · show quittingCyclicTerminalValue reward _ phase who = 0
    rw [quittingCyclicTerminalValue]
    exact quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from reward _
      who 0 (fun time _ ↦ hcycleRoot time)

/-- **The refusal identity.**  Refusal by `who` against an anchored cyclic
profile is worth exactly the on-path value of the same schedule with `who`'s
own phases carrying hazard zero. -/
theorem quittingPeriodicWindowRefusalValue_anchoredCyclic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (phase : Fin m) (who : ι) :
    quittingPeriodicWindowRefusalValue reward
        (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
          phase) who =
      quittingAnchoredCyclicOnPathValue reward w
        (quittingAnchoredCyclicRefusalHazard w hazard who)
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
        (quittingAnchoredCyclicRefusalHazard_le_one h1 w who) phase who := by
  by_cases hzero : ∀ k, quittingAnchoredCyclicRefusalHazard w hazard who k = 0
  · obtain ⟨hleft, hright⟩ :=
      quittingPeriodicWindowRefusalValue_anchoredCyclic_of_forall_eq_zero reward w
        hazard h0 h1 phase who hzero
    rw [hleft, hright]
  · obtain ⟨k₀, hk₀⟩ := not_forall.1 hzero
    refine quittingPeriodicWindowRefusalValue_anchoredCyclic_of_ne_one reward w
      hazard h0 h1 phase who (ne_of_lt ?_)
    exact prod_one_sub_lt_one_of_pos
      (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
      (quittingAnchoredCyclicRefusalHazard_le_one h1 w who)
      (lt_of_le_of_ne
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who k₀) (Ne.symm hk₀))

/-- **The screen against the max-linear system, with its refusal branch read
as a zeroed on-path value.**  The hypothesis compares the solution `S` with the
on-path value of the schedule whose phases owned by the deviator carry hazard
zero, which the renewal closed form `quittingAnchoredCyclicOnPathValue_eq_div`
evaluates as a ratio of finite sums. -/
theorem exists_anchoredCyclicResponse_gain_of_refusalOnPathValue_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) [NeZero m]
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (hzeroed : ∀ who,
      quittingAnchoredCyclicOnPathValue reward w
          (quittingAnchoredCyclicRefusalHazard w hazard who)
          (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
          (quittingAnchoredCyclicRefusalHazard_le_one h1 w who)
          (quittingAnchoredCyclicStart m) who ≤
        S (quittingAnchoredCyclicStart m) who) :
    ∃ who,
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
          (quittingAnchoredCyclicStart m) who + regime.terminalGap ≤
        S (quittingAnchoredCyclicStart m) who :=
  exists_anchoredCyclicResponse_gain regime w hazard h0 h1 S hS fun who ↦
    (quittingPeriodicWindowRefusalValue_anchoredCyclic reward w hazard h0 h1
      (quittingAnchoredCyclicStart m) who).trans_le (hzeroed who)

end GameTheory
