/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.AnchoredCyclicScreen
import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile

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
before any best-response statistic is computed.  Its contrapositive
`quittingAnchoredCyclicOnPathValue_ne_of_not_mem_convexHull` is a prescreen on
candidate targets, and `range_quittingSingletonTerminal_comp` shows the hull
depends only on the set of players the schedule visits.

The last section identifies the refusal branch of the periodic best-response
statistic.  Deleting a player from an anchored cyclic cycle — forcing it to
continue at every phase — leaves the anchored cyclic cycle of the same schedule
with the refuser's own phases carrying hazard zero
(`quittingCyclicDeletedCycle_anchoredCyclicCycle`), so the general refusal
identity `quittingPeriodicWindowRefusalValue_eq_cyclicTerminalValue_deleted`
specializes to `quittingPeriodicWindowRefusalValue_anchoredCyclic`: refusal is
the on-path value of that zeroed schedule, in the absorbing and the
never-absorbing branch alike.  Combined with the closed form this turns the
refusal hypothesis of `exists_anchoredCyclicResponse_gain` into a comparison of
finite sums, which is
`exists_anchoredCyclicResponse_gain_of_refusalOnPathValue_le`.

That comparison is in turn a consequence of the max-linear response system
itself.  The anchored system is the single-quitter case of the general periodic
response system (`isQuittingCyclicResponseSolution_of_isAnchoredCyclicResponseSolution`),
and the deviator's one-turn opponent survival along an anchored cyclic cycle is
the zeroed survival `∏ k, (1 - p_k)` of
`quittingStationaryFixedOpponentsContinueMass_anchoredCyclicCycle`.  So
`quittingAnchoredCyclicResponseCap_le_of_response` bounds the *exact behavioral*
best response of the anchored cyclic profile by a solution of the finite max
recursion, with the single residual that a player owning every positive-hazard
phase — for whom refusal is worth nothing — needs a nonnegative solution
coordinate.  The spectator condition "every player is a spectator at some phase
carrying positive hazard" removes that residual, giving
`quittingAnchoredCyclicResponseCap_le_of_response_of_spectatorHazard` and the
contrapositive screen `isEmpty_of_anchoredCyclicResponseSolution_le`, whose
inputs are all finite.
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

/-! ### A convex-hull prescreen on candidate targets -/

omit [Fintype ι] [DecidableEq ι] in
/-- The hull the placement lives in depends only on the set of players the
schedule visits, not on the order or the multiplicities. -/
theorem range_quittingSingletonTerminal_comp
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (w : Fin m → ι) :
    (Set.range fun k : Fin m ↦ reward (quittingSingletonTerminal (w k))) =
      (fun owner ↦ reward (quittingSingletonTerminal owner)) '' Set.range w := by
  rw [← Set.range_comp]
  rfl

/-- **A convex-hull prescreen for anchored cyclic targets.**  A payoff outside
the convex hull of the singleton rows of the players a schedule visits is not
the on-path value of any absorbing anchored cyclic profile on that schedule.
The test reads only the table's singleton rows and the schedule's image, so it
runs before any response-cap computation. -/
theorem quittingAnchoredCyclicOnPathValue_ne_of_not_mem_convexHull
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hcontraction : ∏ k, (1 - hazard k) < 1) (phase : Fin m) {payoff : Payoff ι}
    (hpayoff : payoff ∉ convexHull ℝ
      ((fun owner ↦ reward (quittingSingletonTerminal owner)) '' Set.range w)) :
    quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase ≠ payoff := by
  intro hcontra
  refine hpayoff ?_
  rw [← range_quittingSingletonTerminal_comp, ← hcontra]
  exact quittingAnchoredCyclicOnPathValue_mem_convexHull reward w hazard h0 h1
    hcontraction phase

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

omit [Fintype ι] in
/-- At a phase the refuser does not own, the zeroed hazard is the original
hazard. -/
theorem quittingAnchoredCyclicRefusalHazard_of_ne
    (w : Fin m → ι) (hazard : Fin m → ℝ) {who : ι} {k : Fin m}
    (hk : w k ≠ who) :
    quittingAnchoredCyclicRefusalHazard w hazard who k = hazard k := by
  rw [quittingAnchoredCyclicRefusalHazard, if_neg hk]

omit [Fintype ι] in
/-- At a phase the refuser owns, the zeroed hazard is zero. -/
theorem quittingAnchoredCyclicRefusalHazard_self
    (w : Fin m → ι) (hazard : Fin m → ℝ) {who : ι} {k : Fin m}
    (hk : w k = who) :
    quittingAnchoredCyclicRefusalHazard w hazard who k = 0 := by
  rw [quittingAnchoredCyclicRefusalHazard, if_pos hk]

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

omit [Fintype ι] in
/-- **Deleting the refuser zeroes its own phases.**  Forcing `who` to continue
at every phase of an anchored cyclic cycle leaves the anchored cyclic cycle of
the same schedule with `who`'s own phases carrying hazard zero. -/
theorem quittingCyclicDeletedCycle_anchoredCyclicCycle
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (who : ι) :
    quittingCyclicDeletedCycle (quittingAnchoredCyclicCycle w hazard h0 h1) who =
      quittingAnchoredCyclicCycle w
        (quittingAnchoredCyclicRefusalHazard w hazard who)
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
        (quittingAnchoredCyclicRefusalHazard_le_one h1 w who) := by
  funext k
  show Function.update (quittingSoloMixedRoot (w k)
      (quittingHazardCoin (hazard k) (h0 k) (h1 k))) who (PMF.pure false) =
    quittingSoloMixedRoot (w k)
      (quittingHazardCoin (quittingAnchoredCyclicRefusalHazard w hazard who k)
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who k)
        (quittingAnchoredCyclicRefusalHazard_le_one h1 w who k))
  by_cases hk : w k = who
  · have hcoin : quittingHazardCoin
        (quittingAnchoredCyclicRefusalHazard w hazard who k)
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who k)
        (quittingAnchoredCyclicRefusalHazard_le_one h1 w who k) = PMF.pure false :=
      quittingHazardCoin_eq_pure_false_of_quitMass_zero _ _
        (by rw [quittingHazardCoin_true_toReal,
          quittingAnchoredCyclicRefusalHazard_self w hazard hk])
    rw [hcoin, hk]
    simp only [quittingSoloMixedRoot]
    rw [Function.update_idem]
  · have hcoin : quittingHazardCoin (hazard k) (h0 k) (h1 k) =
        quittingHazardCoin (quittingAnchoredCyclicRefusalHazard w hazard who k)
          (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who k)
          (quittingAnchoredCyclicRefusalHazard_le_one h1 w who k) :=
      quittingHazardCoin_congr _ _ _ _
        (by rw [quittingHazardCoin_true_toReal, quittingHazardCoin_true_toReal,
          quittingAnchoredCyclicRefusalHazard_of_ne w hazard hk])
    rw [← hcoin, ← quittingSoloMixedRoot_of_ne (Ne.symm hk)
      (quittingHazardCoin (hazard k) (h0 k) (h1 k))]
    exact Function.update_eq_self who _

/-- **The refusal identity.**  Refusal by `who` against an anchored cyclic
profile is worth exactly the on-path value of the same schedule with `who`'s
own phases carrying hazard zero.  No absorption hypothesis is used. -/
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
  rw [quittingPeriodicWindowRefusalValue_eq_cyclicTerminalValue_deleted,
    quittingCyclicDeletedCycle_anchoredCyclicCycle]
  rfl

/-- **One-turn opponent survival of an anchored cyclic cycle.**  A phase owned
by the deviator contributes no absorption against it, and every other phase
contributes its continuation probability. -/
theorem quittingStationaryFixedOpponentsContinueMass_anchoredCyclicCycle
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (k : Fin m) (who : ι) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingAnchoredCyclicCycle w hazard h0 h1 k) who =
      1 - quittingAnchoredCyclicRefusalHazard w hazard who k := by
  rw [← quittingStationaryContinueMass_quittingCyclicDeletedCycle
      (quittingAnchoredCyclicCycle w hazard h0 h1) who k,
    quittingCyclicDeletedCycle_anchoredCyclicCycle]
  show quittingStationaryContinueMass (quittingSoloMixedRoot (w k)
    (quittingHazardCoin (quittingAnchoredCyclicRefusalHazard w hazard who k)
      (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who k)
      (quittingAnchoredCyclicRefusalHazard_le_one h1 w who k))) = _
  rw [quittingStationaryContinueMass_soloMixedRoot, quittingHazardCoin_false_toReal]

/-- The deviator's one-turn opponent survival is the zeroed schedule's own
survival product. -/
theorem prod_quittingStationaryFixedOpponentsContinueMass_anchoredCyclicCycle
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (who : ι) :
    (∏ k, quittingStationaryFixedOpponentsContinueMass
        (quittingAnchoredCyclicCycle w hazard h0 h1 k) who) =
      ∏ k, (1 - quittingAnchoredCyclicRefusalHazard w hazard who k) :=
  Finset.prod_congr rfl fun k _ ↦
    quittingStationaryFixedOpponentsContinueMass_anchoredCyclicCycle w hazard h0 h1
      k who

/-- **The degenerate branch read off the cycle.**  When the deviator's
opponents never absorb over one turn, the deviator owns every phase that
carries positive hazard. -/
theorem hazard_eq_zero_of_not_contracts_anchoredCyclic
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) {who : ι}
    (hcontracts : ¬ (∏ k, quittingStationaryFixedOpponentsContinueMass
      (quittingAnchoredCyclicCycle w hazard h0 h1 k) who) < 1)
    (k : Fin m) (hk : w k ≠ who) :
    hazard k = 0 := by
  have hmass := quittingStationaryFixedOpponentsContinueMass_eq_one_of_not_contracts
    hcontracts k
  rw [quittingStationaryFixedOpponentsContinueMass_anchoredCyclicCycle,
    quittingAnchoredCyclicRefusalHazard_of_ne w hazard hk] at hmass
  linarith

/-- **Refusal on the degenerate branch.**  A refuser owning every phase that
carries positive hazard faces a schedule that never absorbs, so refusal is
worth nothing. -/
theorem quittingPeriodicWindowRefusalValue_anchoredCyclic_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (phase : Fin m) {who : ι} (hzero : ∀ k, w k ≠ who → hazard k = 0) :
    quittingPeriodicWindowRefusalValue reward
        (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
          phase) who = 0 := by
  refine quittingPeriodicWindowRefusalValue_eq_zero_of_not_contracts reward phase ?_
  have hone : ∀ k : Fin m,
      1 - quittingAnchoredCyclicRefusalHazard w hazard who k = 1 := by
    intro k
    by_cases hk : w k = who
    · rw [quittingAnchoredCyclicRefusalHazard_self w hazard hk]
      ring
    · rw [quittingAnchoredCyclicRefusalHazard_of_ne w hazard hk, hzero k hk]
      ring
  rw [prod_quittingStationaryFixedOpponentsContinueMass_anchoredCyclicCycle,
    Finset.prod_congr rfl fun k (_ : k ∈ Finset.univ) ↦ hone k,
    Finset.prod_const_one]
  exact lt_irrefl 1

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

/-! ## Discharging the screen's refusal hypothesis

The refusal identity turns `hrefusal` into a comparison between the zeroed
on-path value and the candidate solution.  That comparison is a consequence of
the max-linear system: the anchored system is the single-quitter case of the
general periodic response system, and the deviator's one-turn opponent survival
along the anchored cyclic cycle is the zeroed schedule's own survival product.
-/

/-- **A response solution dominates the zeroed on-path value.**  When the
cycle with `who`'s phases zeroed still absorbs, every solution of the
max-linear response system is at least the on-path value of that zeroed
schedule. -/
theorem quittingAnchoredCyclicOnPathValue_refusalHazard_le_of_response
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (phase : Fin m) (who : ι)
    (hcontraction :
      ∏ k, (1 - quittingAnchoredCyclicRefusalHazard w hazard who k) < 1) :
    quittingAnchoredCyclicOnPathValue reward w
        (quittingAnchoredCyclicRefusalHazard w hazard who)
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
        (quittingAnchoredCyclicRefusalHazard_le_one h1 w who) phase who ≤
      S phase who := by
  rw [← quittingPeriodicWindowRefusalValue_anchoredCyclic reward w hazard h0 h1
    phase who]
  refine quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution
    (isQuittingCyclicResponseSolution_of_isAnchoredCyclicResponseSolution reward w
      hazard h0 h1 hS) phase who ?_
  rw [prod_quittingStationaryFixedOpponentsContinueMass_anchoredCyclicCycle]
  exact hcontraction

/-- **The screen's refusal hypothesis, discharged.**  Against a solution of the
max-linear response system, refusal is dominated as soon as the refuser does
not own every phase carrying positive hazard; on the degenerate branch refusal
is worth nothing, so nonnegativity of the solution is all that is left. -/
theorem quittingPeriodicWindowRefusalValue_le_of_response
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (phase : Fin m) (who : ι)
    (hdegenerate : (∀ k, w k ≠ who → hazard k = 0) → 0 ≤ S phase who) :
    quittingPeriodicWindowRefusalValue reward
        (quittingCyclicRootSequence (quittingAnchoredCyclicCycle w hazard h0 h1)
          phase) who ≤
      S phase who :=
  quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution_of_nonneg
    (isQuittingCyclicResponseSolution_of_isAnchoredCyclicResponseSolution reward w
      hazard h0 h1 hS) phase who fun hcontracts ↦
    hdegenerate (hazard_eq_zero_of_not_contracts_anchoredCyclic h0 h1 hcontracts)

/-- **The max-linear solution caps the exact behavioral best response.**  The
anchored response cap is the general periodic response cap of the anchored
cyclic cycle, so a solution of the scalar recursion caps it.  The only residual
is nonnegativity of the solution for a player owning every phase that carries
positive hazard, for whom refusal is worth nothing. -/
theorem quittingAnchoredCyclicResponseCap_le_of_response
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} [NeZero m]
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S) (who : ι)
    (hdegenerate : (∀ k, w k ≠ who → hazard k = 0) →
      0 ≤ S (quittingAnchoredCyclicStart m) who) :
    quittingAnchoredCyclicResponseCap reward w hazard h0 h1 who ≤
      S (quittingAnchoredCyclicStart m) who := by
  rw [quittingAnchoredCyclicResponseCap_eq_quittingCyclicResponseCap]
  exact quittingCyclicResponseCap_le_of_isQuittingCyclicResponseSolution_of_nonneg
    (isQuittingCyclicResponseSolution_of_isAnchoredCyclicResponseSolution reward w
      hazard h0 h1 hS) (quittingAnchoredCyclicStart m) who fun hcontracts ↦
    hdegenerate (hazard_eq_zero_of_not_contracts_anchoredCyclic h0 h1 hcontracts)

omit [Fintype ι] in
/-- Every phase not owned by `who` and carrying positive hazard keeps the
zeroed cycle absorbing. -/
theorem prod_one_sub_refusalHazard_lt_one
    {w : Fin m → ι} {hazard : Fin m → ℝ} (h0 : ∀ k, 0 ≤ hazard k)
    (h1 : ∀ k, hazard k ≤ 1) {who : ι} {k₀ : Fin m} (hne : w k₀ ≠ who)
    (hpos : 0 < hazard k₀) :
    ∏ k, (1 - quittingAnchoredCyclicRefusalHazard w hazard who k) < 1 := by
  refine Math.PMFProduct.continueMass_lt_one_of_pos
    (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
    (quittingAnchoredCyclicRefusalHazard_le_one h1 w who) (i₀ := k₀) ?_
  rwa [quittingAnchoredCyclicRefusalHazard, if_neg hne]

/-- **The response cap bound with no residual.**  When every player is a
spectator at some phase carrying positive hazard, the max-linear solution caps
the exact behavioral best response outright. -/
theorem quittingAnchoredCyclicResponseCap_le_of_response_of_spectatorHazard
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} [NeZero m]
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S) (who : ι)
    (hspectator : ∃ k, w k ≠ who ∧ 0 < hazard k) :
    quittingAnchoredCyclicResponseCap reward w hazard h0 h1 who ≤
      S (quittingAnchoredCyclicStart m) who := by
  obtain ⟨k₀, hne, hpos⟩ := hspectator
  refine quittingAnchoredCyclicResponseCap_le_of_response w hazard h0 h1 S hS who
    fun hall ↦ ?_
  exact absurd (hall k₀ hne) (ne_of_gt hpos)

/-- **The screen against the max-linear system with no refusal hypothesis.**
The only residual is nonnegativity of the solution for the players who own
every positive-hazard phase. -/
theorem exists_anchoredCyclicResponse_gain_of_degenerate_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) [NeZero m]
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (hdegenerate : ∀ who, (∀ k, w k ≠ who → hazard k = 0) →
      0 ≤ S (quittingAnchoredCyclicStart m) who) :
    ∃ who,
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
          (quittingAnchoredCyclicStart m) who + regime.terminalGap ≤
        S (quittingAnchoredCyclicStart m) who := by
  obtain ⟨who, hgain⟩ := regime.exists_anchoredCyclicCap_gain w hazard h0 h1
  exact ⟨who, hgain.trans (quittingAnchoredCyclicResponseCap_le_of_response w
    hazard h0 h1 S hS who (hdegenerate who))⟩

/-- **The screen against the max-linear system, unconditionally.**  When every
player is a spectator at some phase carrying positive hazard, the refusal
hypothesis of `exists_anchoredCyclicResponse_gain` is discharged outright. -/
theorem exists_anchoredCyclicResponse_gain_of_exists_spectatorHazard
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) [NeZero m]
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (hspectator : ∀ who, ∃ k, w k ≠ who ∧ 0 < hazard k) :
    ∃ who,
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
          (quittingAnchoredCyclicStart m) who + regime.terminalGap ≤
        S (quittingAnchoredCyclicStart m) who := by
  obtain ⟨who, hgain⟩ := regime.exists_anchoredCyclicCap_gain w hazard h0 h1
  exact ⟨who, hgain.trans
    (quittingAnchoredCyclicResponseCap_le_of_response_of_spectatorHazard w hazard
      h0 h1 S hS who (hspectator who))⟩

/-- **The screen's contrapositive against the max-linear system.**  A schedule
whose response system has a solution no larger than the on-path value at the
starting phase excludes every counterexample regime.  Every input is finite:
the max recursion, the spectator condition, and one comparison per player. -/
theorem isEmpty_of_anchoredCyclicResponseSolution_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} [NeZero m]
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (hspectator : ∀ who, ∃ k, w k ≠ who ∧ 0 < hazard k)
    (hle : ∀ who, S (quittingAnchoredCyclicStart m) who ≤
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
        (quittingAnchoredCyclicStart m) who) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  QuittingCounterexampleRegime.isEmpty_of_anchoredCyclicCap_le w hazard h0 h1
    fun who ↦
      (quittingAnchoredCyclicResponseCap_le_of_response_of_spectatorHazard w hazard
        h0 h1 S hS who (hspectator who)).trans (hle who)

end GameTheory
