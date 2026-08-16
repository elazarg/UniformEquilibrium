/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite weighted-clock rank reduction

This module develops reusable finite estimates for a nonnegative weighted
clock whose stage mass is dominated by loss of live mass.

The file records two complementary layers.

* `FiniteWeightedClock` is an abstract finite chronology. Its stage clock is
  dominated by loss of live mass.  This gives an unconditional stopping-time
  bulk/tail hierarchy.
* `SharpClockCut` exposes the one genuinely analytic input used by the sharp
  logarithmic estimate.  The logarithmic potential inequality itself is
  proved below; it is not an axiom.

Rank is the exponent of the dominated hazard moment. The estimates do not
assert that any ambient finite type has been reduced to that cardinality.
-/


noncomputable section

namespace Math.Probability.WeightedClockRankReduction

open scoped BigOperators
open Finset

/-! ## 1. Finite weighted clocks -/

/-- A finite weighted clock of length `horizon`.

`stage time = live time * hazard time` is the stopped mass at `time`.
`weighted_hazard_le_drop` is the only chronological input needed for tail
domination. -/
structure FiniteWeightedClock (horizon : ℕ) where
  live : ℕ → ℝ
  hazard : ℕ → ℝ
  live_nonneg : ∀ time, 0 ≤ live time
  hazard_nonneg : ∀ time, 0 ≤ hazard time
  weighted_hazard_le_drop : ∀ time < horizon,
    live time * hazard time ≤ live time - live (time + 1)

namespace FiniteWeightedClock

variable {horizon : ℕ} (clock : FiniteWeightedClock horizon)

/-- Survival-weighted hazard mass at one stage. -/
def stage (time : ℕ) : ℝ :=
  clock.live time * clock.hazard time

@[simp] theorem stage_eq (time : ℕ) :
    clock.stage time = clock.live time * clock.hazard time := rfl

theorem stage_le_drop {time : ℕ} (htime : time < horizon) :
    clock.stage time ≤ clock.live time - clock.live (time + 1) :=
  clock.weighted_hazard_le_drop time htime

theorem hazard_le_one_of_live_pos {time : ℕ} (htime : time < horizon)
    (hlive : 0 < clock.live time) :
    clock.hazard time ≤ 1 := by
  have hdrop := clock.stage_le_drop htime
  have hnext0 := clock.live_nonneg (time + 1)
  rw [clock.stage_eq] at hdrop
  apply le_of_mul_le_mul_left _ hlive
  simpa using hdrop.trans (by linarith :
    clock.live time - clock.live (time + 1) ≤ clock.live time)

/-- After weighting by live mass, higher hazard powers are smaller at every
chronological stage. No upper bound on an irrelevant zero-live hazard is
needed. -/
theorem live_mul_hazard_pow_antitone {time lower upper : ℕ}
    (htime : time < horizon) (hexponent : lower ≤ upper) :
    clock.live time * clock.hazard time ^ upper ≤
      clock.live time * clock.hazard time ^ lower := by
  by_cases hliveZero : clock.live time = 0
  · simp [hliveZero]
  · have hlive : 0 < clock.live time :=
      lt_of_le_of_ne (clock.live_nonneg time) (Ne.symm hliveZero)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (clock.hazard_nonneg time)
        (clock.hazard_le_one_of_live_pos htime hlive) hexponent)
      hlive.le

/-- Clock mass in the half-open chronological interval `[start,horizon)`. -/
def tail (start : ℕ) : ℝ :=
  ∑ time ∈ Finset.Ico start horizon, clock.stage time

/-- Total clock mass. -/
def total : ℝ := clock.tail 0

/-- The `k`-th survival-weighted hazard moment. -/
def moment (k : ℕ) : ℝ :=
  ∑ time ∈ Finset.range horizon,
    clock.live time * clock.hazard time ^ k

theorem stage_nonneg (time : ℕ) :
    0 ≤ clock.stage time := by
  rw [clock.stage_eq time]
  exact mul_nonneg (clock.live_nonneg time) (clock.hazard_nonneg time)

theorem tail_nonneg (start : ℕ) : 0 ≤ clock.tail start := by
  exact Finset.sum_nonneg fun time _ ↦ clock.stage_nonneg time

@[simp] theorem tail_horizon : clock.tail horizon = 0 := by
  simp [tail]

theorem total_eq_sum_range :
    clock.total = ∑ time ∈ Finset.range horizon, clock.stage time := by
  simp [total, tail]

/-- Exact one-step removal of a clock atom from its future tail. -/
theorem tail_succ {time : ℕ} (htime : time < horizon) :
    clock.tail (time + 1) = clock.tail time - clock.stage time := by
  have hset : Finset.Ico time horizon =
      insert time (Finset.Ico (time + 1) horizon) := by
    ext index
    simp [Finset.mem_Ico]
    omega
  have hnot : time ∉ Finset.Ico (time + 1) horizon := by simp
  unfold tail
  rw [hset, Finset.sum_insert hnot]
  ring

/-- Later clock tails are smaller. -/
theorem tail_antitone {first second : ℕ}
    (hfirst : first ≤ second) :
    clock.tail second ≤ clock.tail first := by
  by_cases hsecond : horizon ≤ second
  · have hfirstTail : 0 ≤ clock.tail first := clock.tail_nonneg first
    have hzero : clock.tail second = 0 := by
      simp [tail, Finset.Ico_eq_empty (by omega : ¬ second < horizon)]
    linarith
  · have hsecondHorizon : second ≤ horizon := Nat.le_of_lt (lt_of_not_ge hsecond)
    rw [show clock.tail first =
        (∑ time ∈ Finset.Ico first second, clock.stage time) +
          clock.tail second by
      unfold tail
      exact (Finset.sum_Ico_consecutive clock.stage hfirst hsecondHorizon).symm]
    exact le_add_of_nonneg_left
      (Finset.sum_nonneg fun time _ ↦ clock.stage_nonneg time)

/-- **Tail domination.** All future clock mass is paid by current live mass.
This is derived from the one-step live-mass drop, rather than stored in the
clock structure. -/
theorem tail_le_live (start : ℕ) :
    clock.tail start ≤ clock.live start := by
  by_cases hstart : start ≤ horizon
  · have hsum : clock.tail start ≤
        ∑ time ∈ Finset.Ico start horizon,
          (clock.live time - clock.live (time + 1)) := by
      exact Finset.sum_le_sum fun time htime ↦
        clock.stage_le_drop (Finset.mem_Ico.mp htime).2
    have htelescope :
        (∑ time ∈ Finset.Ico start horizon,
          (clock.live time - clock.live (time + 1))) =
            clock.live start - clock.live horizon := by
      rw [Finset.sum_Ico_eq_sub _ hstart]
      simp only [Finset.sum_range_sub']
      ring
    rw [htelescope] at hsum
    linarith [clock.live_nonneg horizon]
  · rw [show clock.tail start = 0 by
      simp [tail, Finset.Ico_eq_empty (by omega : ¬ start < horizon)]]
    exact clock.live_nonneg start

theorem total_nonneg : 0 ≤ clock.total := clock.tail_nonneg 0

theorem total_le_live_zero : clock.total ≤ clock.live 0 := by
  exact clock.tail_le_live 0

/-! ## 2. A fully unconditional bulk/tail hierarchy -/

/-- A cut before which hazards are at most `threshold`, while the whole
remaining clock tail has already fallen below `mesh / threshold`.

This is a predicate, not an assumption about all clocks: the producer below
constructs such a cut from a positive threshold and a stage-mesh bound. -/
structure HasBulkTailCut (mesh threshold : ℝ) where
  cut : ℕ
  cut_le : cut ≤ horizon
  before : ∀ time < cut, clock.hazard time ≤ threshold
  tail_le : clock.tail cut ≤ mesh / threshold

/-- A stage mesh bound and tail domination produce a bulk/tail cut at every
positive hazard threshold. -/
noncomputable def bulkTailCut
    {mesh threshold : ℝ} (hmesh0 : 0 ≤ mesh) (hthreshold : 0 < threshold)
    (hmesh : ∀ time < horizon, clock.stage time ≤ mesh) :
    clock.HasBulkTailCut mesh threshold := by
  classical
  by_cases hhigh : ∃ time, time < horizon ∧ threshold < clock.hazard time
  · let cut := Nat.find hhigh
    have hspec : cut < horizon ∧ threshold < clock.hazard cut :=
      Nat.find_spec hhigh
    have hbefore : ∀ time < cut, clock.hazard time ≤ threshold := by
      intro time htime
      exact le_of_not_gt fun hgt ↦
        (not_le_of_gt htime)
          (Nat.find_min' hhigh ⟨lt_trans htime hspec.1, hgt⟩)
    have hstageEq := clock.stage_eq cut
    have htailLive := clock.tail_le_live cut
    have hstageMesh := hmesh cut hspec.1
    have hliveLe : clock.live cut ≤ mesh / threshold := by
      have hhazard0 := clock.hazard_nonneg cut
      have hlive0 := clock.live_nonneg cut
      rw [hstageEq] at hstageMesh
      apply (le_div_iff₀ hthreshold).2
      nlinarith
    exact ⟨cut, hspec.1.le, hbefore, htailLive.trans hliveLe⟩
  · refine ⟨horizon, le_rfl, ?_, ?_⟩
    · intro time htime
      exact le_of_not_gt fun hgt ↦ hhigh ⟨time, htime, hgt⟩
    · simpa [tail] using div_nonneg hmesh0 hthreshold.le

/-- Generic summation engine: charge the bulk at `coefficient * stage` and
the remaining suffix once at full stage mass. -/
theorem sum_le_coefficient_total_add_tail
    (quantity : ℕ → ℝ) {cut : ℕ}
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient)
    (hbulk : ∀ time < cut,
      quantity time ≤ coefficient * clock.stage time)
    (hsuffix : ∀ time, cut ≤ time → time < horizon →
      quantity time ≤ clock.stage time) :
    (∑ time ∈ Finset.range horizon, quantity time) ≤
      coefficient * clock.total + clock.tail cut := by
  have hpoint : ∀ time ∈ Finset.range horizon,
      quantity time ≤ coefficient * clock.stage time +
        if cut ≤ time then clock.stage time else 0 := by
    intro time htime
    have htimeHorizon := Finset.mem_range.mp htime
    by_cases hlate : cut ≤ time
    · simp only [if_pos hlate]
      exact (hsuffix time hlate htimeHorizon).trans
        (le_add_of_nonneg_left
          (mul_nonneg hcoefficient (clock.stage_nonneg time)))
    · simp only [if_neg hlate]
      simpa using hbulk time (Nat.lt_of_not_ge hlate)
  calc
    (∑ time ∈ Finset.range horizon, quantity time) ≤
        ∑ time ∈ Finset.range horizon,
          (coefficient * clock.stage time +
            if cut ≤ time then clock.stage time else 0) :=
      Finset.sum_le_sum hpoint
    _ = coefficient * clock.total + clock.tail cut := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [← clock.total_eq_sum_range]
      congr 1
      unfold tail
      rw [show Finset.Ico cut horizon =
          (Finset.range horizon).filter (fun time ↦ cut ≤ time) by
        ext time
        simp [Finset.mem_Ico, and_comm]]
      rw [Finset.sum_filter]

/-- On the bulk, the `k`-th hazard moment costs `threshold^(k-1)` per clock
atom; on the suffix it costs at most the clock atom itself. -/
theorem moment_le_of_bulkTailCut
    {mesh threshold : ℝ} (hthreshold0 : 0 < threshold)
    (k : ℕ) (hk : 1 ≤ k)
    (cut : clock.HasBulkTailCut mesh threshold) :
    clock.moment k ≤
      threshold ^ (k - 1) * clock.total + mesh / threshold := by
  have hcoefficient : 0 ≤ threshold ^ (k - 1) :=
    pow_nonneg hthreshold0.le _
  have hbulk : ∀ time < cut.cut,
      clock.live time * clock.hazard time ^ k ≤
        threshold ^ (k - 1) * clock.stage time := by
    intro time htime
    have htimeHorizon := lt_of_lt_of_le htime cut.cut_le
    have ha0 := clock.hazard_nonneg time
    have haThreshold := cut.before time htime
    have hpow : clock.hazard time ^ (k - 1) ≤ threshold ^ (k - 1) :=
      pow_le_pow_left₀ ha0 haThreshold _
    rw [clock.stage_eq time]
    calc
      clock.live time * clock.hazard time ^ k =
          clock.live time *
            (clock.hazard time * clock.hazard time ^ (k - 1)) := by
        rw [← pow_succ', Nat.sub_add_cancel hk]
      _ ≤ clock.live time *
          (clock.hazard time * threshold ^ (k - 1)) := by
        gcongr
        exact clock.live_nonneg time
      _ = threshold ^ (k - 1) *
          (clock.live time * clock.hazard time) := by ring
  have hsuffix : ∀ time, cut.cut ≤ time → time < horizon →
      clock.live time * clock.hazard time ^ k ≤ clock.stage time := by
    intro time _htimeCut htimeHorizon
    rw [clock.stage_eq time]
    simpa using clock.live_mul_hazard_pow_antitone htimeHorizon hk
  exact (clock.sum_le_coefficient_total_add_tail
    (fun time ↦ clock.live time * clock.hazard time ^ k)
      hcoefficient hbulk hsuffix).trans
    (add_le_add le_rfl cut.tail_le)

/-- Fully unconditional threshold hierarchy.  No logarithm and no hidden
analytic premise: every positive threshold gives a valid estimate. -/
theorem moment_le_thresholdHierarchy
    {mesh threshold : ℝ} (hmesh0 : 0 ≤ mesh)
    (hthreshold0 : 0 < threshold)
    (k : ℕ) (hk : 1 ≤ k)
    (hmesh : ∀ time < horizon, clock.stage time ≤ mesh) :
    clock.moment k ≤
      threshold ^ (k - 1) * clock.total + mesh / threshold := by
  exact clock.moment_le_of_bulkTailCut hthreshold0 k hk
    (clock.bulkTailCut hmesh0 hthreshold0 hmesh)

end FiniteWeightedClock

/-! ## 3. The logarithmic potential, proved independently -/

/-- The discrete logarithmic inequality behind the sharp quadratic clock
bound.  It is stated for an arbitrary positive tail recursion so that the
analysis is reusable outside quitting games. -/
theorem sum_ratio_le_log_ratio
    (mass tail : ℕ → ℝ) (cut : ℕ)
    (htailPos : ∀ time ≤ cut, 0 < tail time)
    (hrec : ∀ time < cut,
      tail (time + 1) = tail time - mass time) :
    (∑ time ∈ Finset.range cut, mass time / tail time) ≤
      Real.log (tail 0 / tail cut) := by
  have hstep : ∀ time < cut,
      mass time / tail time ≤
        Real.log (tail time) - Real.log (tail (time + 1)) := by
    intro time htime
    have htail := htailPos time (Nat.le_of_lt htime)
    have htailNext := htailPos (time + 1) (Nat.succ_le_iff.mpr htime)
    have hratio : 0 < tail (time + 1) / tail time :=
      div_pos htailNext htail
    have hlog := Real.log_le_sub_one_of_pos hratio
    rw [Real.log_div htailNext.ne' htail.ne'] at hlog
    have hratioEq :
        tail (time + 1) / tail time - 1 =
          -(mass time / tail time) := by
      rw [hrec time htime]
      field_simp
      ring
    rw [hratioEq] at hlog
    linarith
  calc
    (∑ time ∈ Finset.range cut, mass time / tail time) ≤
        ∑ time ∈ Finset.range cut,
          (Real.log (tail time) - Real.log (tail (time + 1))) :=
      Finset.sum_le_sum fun time htime ↦
        hstep time (Finset.mem_range.mp htime)
    _ = Real.log (tail 0) - Real.log (tail cut) := by
      exact Finset.sum_range_sub' (fun time ↦ Real.log (tail time)) cut
    _ = Real.log (tail 0 / tail cut) := by
      rw [Real.log_div (htailPos 0 (Nat.zero_le cut)).ne'
        (htailPos cut le_rfl).ne']

/-- Reciprocal-potential analogue of `sum_ratio_le_log_ratio`.  This is the
integrable estimate which removes the logarithm at cubic and higher rank. -/
theorem sum_mass_div_tail_sq_le
    (mass tail : ℕ → ℝ) (cut : ℕ)
    (htailPos : ∀ time ≤ cut, 0 < tail time)
    (hrec : ∀ time < cut,
      tail (time + 1) = tail time - mass time) :
    (∑ time ∈ Finset.range cut, mass time / tail time ^ 2) ≤
      1 / tail cut - 1 / tail 0 := by
  have hstep : ∀ time < cut,
      mass time / tail time ^ 2 ≤
        1 / tail (time + 1) - 1 / tail time := by
    intro time htime
    have htail := htailPos time (Nat.le_of_lt htime)
    have htailNext := htailPos (time + 1) (Nat.succ_le_iff.mpr htime)
    have hid : 1 / tail (time + 1) - 1 / tail time =
        mass time / (tail (time + 1) * tail time) := by
      field_simp [htail.ne', htailNext.ne']
      rw [hrec time htime]
      ring
    rw [hid]
    apply (div_le_div_iff₀ (sq_pos_of_pos htail)
      (mul_pos htailNext htail)).2
    rw [hrec time htime]
    nlinarith [sq_nonneg (mass time), mul_pos htailNext htail]
  calc
    (∑ time ∈ Finset.range cut, mass time / tail time ^ 2) ≤
        ∑ time ∈ Finset.range cut,
          (1 / tail (time + 1) - 1 / tail time) :=
      Finset.sum_le_sum fun time htime ↦
        hstep time (Finset.mem_range.mp htime)
    _ = 1 / tail cut - 1 / tail 0 := by
      have htel := Finset.sum_range_sub'
        (fun time ↦ 1 / tail time) cut
      calc
        (∑ time ∈ Finset.range cut,
            (1 / tail (time + 1) - 1 / tail time)) =
            -(∑ time ∈ Finset.range cut,
              (1 / tail time - 1 / tail (time + 1))) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro time _
          ring
        _ = 1 / tail cut - 1 / tail 0 := by rw [htel]; ring

namespace FiniteWeightedClock

variable {horizon : ℕ} (clock : FiniteWeightedClock horizon)

/-- The canonical two-mesh cut used by both sharp estimates. -/
structure SharpClockCut (mesh : ℝ) where
  cut : ℕ
  cut_le : cut ≤ horizon
  stage_le_mesh : ∀ time < horizon, clock.stage time ≤ mesh
  tail_gt_mesh : mesh < clock.tail cut
  tail_le_two_mesh : clock.tail cut ≤ 2 * mesh

theorem SharpClockCut.mesh_pos {mesh : ℝ}
    (cut : clock.SharpClockCut mesh) :
    0 < mesh := by
  linarith [cut.tail_gt_mesh, cut.tail_le_two_mesh]

theorem SharpClockCut.tail_pos {mesh : ℝ}
    (cut : clock.SharpClockCut mesh) :
    0 < clock.tail cut.cut := cut.mesh_pos.trans cut.tail_gt_mesh

theorem SharpClockCut.tail_pos_before {mesh : ℝ}
    (cut : clock.SharpClockCut mesh) {time : ℕ}
    (htime : time ≤ cut.cut) :
    0 < clock.tail time := by
  exact cut.tail_pos.trans_le (clock.tail_antitone htime)

/-- A mesh smaller than half the total clock mass canonically supplies the
two-mesh cut.  Thus the sharp estimates below have no unproduced stopping
premise. -/
noncomputable def sharpClockCut
    {mesh : ℝ} (hmeshPos : 0 < mesh)
    (htotal : 2 * mesh < clock.total)
    (hmesh : ∀ time < horizon, clock.stage time ≤ mesh) :
    clock.SharpClockCut mesh := by
  classical
  have hexists : ∃ time, time ≤ horizon ∧ clock.tail time ≤ 2 * mesh := by
    exact ⟨horizon, le_rfl, by simp [hmeshPos.le]⟩
  let cut := Nat.find hexists
  have hspec : cut ≤ horizon ∧ clock.tail cut ≤ 2 * mesh :=
    Nat.find_spec hexists
  have hcutPos : 0 < cut := by
    by_contra hnot
    have hzero : cut = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hspec
    exact (not_lt_of_ge hspec.2) htotal
  let before := cut - 1
  have hbeforeSucc : before + 1 = cut := by
    dsimp only [before]
    omega
  have hbeforeLt : before < cut := by omega
  have hbeforeHorizon : before < horizon := hbeforeLt.trans_le hspec.1
  have hbeforeTail : 2 * mesh < clock.tail before := by
    by_contra hnot
    have hwitness : before ≤ horizon ∧
        clock.tail before ≤ 2 * mesh :=
      ⟨le_trans (Nat.le_of_lt hbeforeLt) hspec.1, le_of_not_gt hnot⟩
    exact (not_le_of_gt hbeforeLt) (Nat.find_min' hexists hwitness)
  have htailStep := clock.tail_succ hbeforeHorizon
  rw [hbeforeSucc] at htailStep
  have hstage := hmesh before hbeforeHorizon
  refine ⟨cut, hspec.1, hmesh, ?_, hspec.2⟩
  linarith

/-- Sharp quadratic/log estimate at a supplied two-mesh cut. -/
theorem moment_two_le_mesh_log_add_two_mesh
    {mesh : ℝ} (cut : clock.SharpClockCut mesh) :
    clock.moment 2 ≤
      mesh * Real.log (clock.total / mesh) + 2 * mesh := by
  let ratio : ℕ → ℝ := fun time ↦
    clock.stage time / clock.tail time
  have hprefixPoint : ∀ time < cut.cut,
      clock.live time * clock.hazard time ^ 2 ≤ mesh * ratio time := by
    intro time htime
    have htimeHorizon := lt_of_lt_of_le htime cut.cut_le
    have htailPos := cut.tail_pos_before clock (Nat.le_of_lt htime)
    have htailLive := clock.tail_le_live time
    have hstage0 := clock.stage_nonneg time
    have hstageMesh := cut.stage_le_mesh time htimeHorizon
    dsimp only [ratio]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ htailPos).2
    have hfirst :
        (clock.live time * clock.hazard time ^ 2) * clock.tail time ≤
          (clock.live time * clock.hazard time ^ 2) * clock.live time :=
      mul_le_mul_of_nonneg_left htailLive
        (mul_nonneg (clock.live_nonneg time) (sq_nonneg _))
    have hsquare :
        (clock.live time * clock.hazard time ^ 2) * clock.live time =
          clock.stage time * clock.stage time := by
      rw [clock.stage_eq time]
      ring
    rw [hsquare] at hfirst
    exact hfirst.trans
      (mul_le_mul_of_nonneg_right hstageMesh hstage0)
  have hprefix :
      (∑ time ∈ Finset.range cut.cut,
          clock.live time * clock.hazard time ^ 2) ≤
        mesh * Real.log (clock.total / clock.tail cut.cut) := by
    calc
      _ ≤ ∑ time ∈ Finset.range cut.cut, mesh * ratio time :=
        Finset.sum_le_sum fun time htime ↦
          hprefixPoint time (Finset.mem_range.mp htime)
      _ = mesh * (∑ time ∈ Finset.range cut.cut, ratio time) := by
        rw [Finset.mul_sum]
      _ ≤ mesh * Real.log (clock.tail 0 / clock.tail cut.cut) := by
        gcongr
        exact cut.mesh_pos.le
        exact sum_ratio_le_log_ratio clock.stage clock.tail cut.cut
          (fun time htime ↦ cut.tail_pos_before clock htime)
          (fun time htime ↦ clock.tail_succ
            (lt_of_lt_of_le htime cut.cut_le))
      _ = mesh * Real.log (clock.total / clock.tail cut.cut) := by
        rfl
  have htailPoint : ∀ time, cut.cut ≤ time → time < horizon →
      clock.live time * clock.hazard time ^ 2 ≤ clock.stage time := by
    intro time _ htime
    rw [clock.stage_eq time]
    simpa using clock.live_mul_hazard_pow_antitone htime (by omega : 1 ≤ 2)
  have htail :
      (∑ time ∈ Finset.Ico cut.cut horizon,
          clock.live time * clock.hazard time ^ 2) ≤ clock.tail cut.cut :=
    Finset.sum_le_sum fun time htime ↦
      htailPoint time (Finset.mem_Ico.mp htime).1
        (Finset.mem_Ico.mp htime).2
  have hlogMono :
      Real.log (clock.total / clock.tail cut.cut) ≤
        Real.log (clock.total / mesh) := by
    have htotalPos : 0 < clock.total := by
      exact cut.tail_pos.trans_le (clock.tail_antitone (Nat.zero_le cut.cut))
    rw [Real.log_div htotalPos.ne' cut.tail_pos.ne',
      Real.log_div htotalPos.ne' cut.mesh_pos.ne']
    have hlog := Real.strictMonoOn_log.monotoneOn
      cut.mesh_pos cut.tail_pos cut.tail_gt_mesh.le
    linarith
  unfold moment
  rw [← Finset.sum_range_add_sum_Ico
    (fun time ↦ clock.live time * clock.hazard time ^ 2) cut.cut_le]
  calc
    _ ≤ mesh * Real.log (clock.total / clock.tail cut.cut) +
        clock.tail cut.cut := add_le_add hprefix htail
    _ ≤ mesh * Real.log (clock.total / mesh) + 2 * mesh :=
      add_le_add
        (mul_le_mul_of_nonneg_left hlogMono cut.mesh_pos.le)
        cut.tail_le_two_mesh

/-- Cubic and all higher moments have no logarithmic loss.  The constant `3`
is uniform in the rank. -/
theorem moment_higher_le_three_mesh
    {mesh : ℝ} (cut : clock.SharpClockCut mesh)
    (k : ℕ) (hk : 3 ≤ k) :
    clock.moment k ≤ 3 * mesh := by
  -- The reciprocal-potential proof is factored as a reusable bound on the
  -- cubic moment; higher powers only decrease on `[0,1]`.
  have hcubicPrefixPoint : ∀ time < cut.cut,
      clock.live time * clock.hazard time ^ 3 ≤
        mesh ^ 2 * (clock.stage time / clock.tail time ^ 2) := by
    intro time htime
    have htimeHorizon := lt_of_lt_of_le htime cut.cut_le
    have htailPos := cut.tail_pos_before clock (Nat.le_of_lt htime)
    have htailLive := clock.tail_le_live time
    have hstage0 := clock.stage_nonneg time
    have hstageMesh := cut.stage_le_mesh time htimeHorizon
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos htailPos)).2
    have hfirst :
        (clock.live time * clock.hazard time ^ 3) * clock.tail time ^ 2 ≤
          (clock.live time * clock.hazard time ^ 3) * clock.live time ^ 2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (clock.tail_nonneg time) (clock.live_nonneg time)).2
          htailLive)
        (mul_nonneg (clock.live_nonneg time) (pow_nonneg (clock.hazard_nonneg time) _))
    have hrewrite :
        (clock.live time * clock.hazard time ^ 3) * clock.live time ^ 2 =
          clock.stage time ^ 3 := by
      rw [clock.stage_eq time]
      ring
    rw [hrewrite] at hfirst
    have hcubic : clock.stage time ^ 3 ≤ mesh ^ 2 * clock.stage time := by
      have hfactor := mul_nonneg
        (mul_nonneg (sub_nonneg.mpr hstageMesh)
          (add_nonneg cut.mesh_pos.le hstage0)) hstage0
      nlinarith
    exact hfirst.trans hcubic
  have hcubicPrefix :
      (∑ time ∈ Finset.range cut.cut,
          clock.live time * clock.hazard time ^ 3) ≤ mesh := by
    calc
      _ ≤ ∑ time ∈ Finset.range cut.cut,
          mesh ^ 2 * (clock.stage time / clock.tail time ^ 2) :=
        Finset.sum_le_sum fun time htime ↦
          hcubicPrefixPoint time (Finset.mem_range.mp htime)
      _ = mesh ^ 2 * (∑ time ∈ Finset.range cut.cut,
          clock.stage time / clock.tail time ^ 2) := by rw [Finset.mul_sum]
      _ ≤ mesh ^ 2 * (1 / clock.tail cut.cut - 1 / clock.tail 0) := by
        gcongr
        exact sum_mass_div_tail_sq_le clock.stage clock.tail cut.cut
          (fun time htime ↦ cut.tail_pos_before clock htime)
          (fun time htime ↦ clock.tail_succ
            (lt_of_lt_of_le htime cut.cut_le))
      _ ≤ mesh := by
        have htailInv : 1 / clock.tail cut.cut ≤ 1 / mesh := by
          exact one_div_le_one_div_of_le cut.mesh_pos cut.tail_gt_mesh.le
        have hzeroInv : 0 ≤ 1 / clock.tail 0 :=
          div_nonneg zero_le_one
            (cut.tail_pos_before clock (Nat.zero_le cut.cut)).le
        have hmesh0 := cut.mesh_pos.le
        calc
          mesh ^ 2 * (1 / clock.tail cut.cut - 1 / clock.tail 0) ≤
              mesh ^ 2 * (1 / mesh) := by nlinarith [sq_nonneg mesh]
          _ = mesh := by field_simp
  have hcubicTail :
      (∑ time ∈ Finset.Ico cut.cut horizon,
          clock.live time * clock.hazard time ^ 3) ≤ 2 * mesh := by
    calc
      _ ≤ ∑ time ∈ Finset.Ico cut.cut horizon, clock.stage time := by
        apply Finset.sum_le_sum
        intro time htime
        have ht := (Finset.mem_Ico.mp htime).2
        rw [clock.stage_eq time]
        simpa using clock.live_mul_hazard_pow_antitone ht (by omega : 1 ≤ 3)
      _ = clock.tail cut.cut := rfl
      _ ≤ 2 * mesh := cut.tail_le_two_mesh
  have hcubic : clock.moment 3 ≤ 3 * mesh := by
    unfold moment
    rw [← Finset.sum_range_add_sum_Ico
      (fun time ↦ clock.live time * clock.hazard time ^ 3) cut.cut_le]
    linarith
  calc
    clock.moment k ≤ clock.moment 3 := by
      unfold moment
      apply Finset.sum_le_sum
      intro time htime
      exact clock.live_mul_hazard_pow_antitone
        (Finset.mem_range.mp htime) hk
    _ ≤ 3 * mesh := hcubic

/-- A rowwise union-bound interface for events requiring `rank` distinct
coordinates. `coordinateCount` supplies the combinatorial coefficient. -/
def RankDominatedMass
    (coordinateCount rank : ℕ) (mass : ℕ → ℝ) : Prop :=
  ∀ time < horizon,
    mass time ≤ (coordinateCount.choose rank : ℝ) *
      (clock.live time * clock.hazard time ^ rank)

theorem sum_rankDominatedMass_le_moment
    {coordinateCount rank : ℕ} {mass : ℕ → ℝ}
    (dominated : clock.RankDominatedMass coordinateCount rank mass) :
    (∑ time ∈ Finset.range horizon, mass time) ≤
      (coordinateCount.choose rank : ℝ) * clock.moment rank := by
  unfold moment
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun time htime ↦
    dominated time (Finset.mem_range.mp htime)

/-- Quadratic/log union-bound hierarchy. -/
theorem sum_rankTwoMass_le
    {mesh : ℝ} (cut : clock.SharpClockCut mesh)
    {coordinateCount : ℕ} {mass : ℕ → ℝ}
    (dominated : clock.RankDominatedMass coordinateCount 2 mass) :
    (∑ time ∈ Finset.range horizon, mass time) ≤
      (coordinateCount.choose 2 : ℝ) *
        (mesh * Real.log (clock.total / mesh) + 2 * mesh) := by
  exact (clock.sum_rankDominatedMass_le_moment dominated).trans
    (mul_le_mul_of_nonneg_left
      (clock.moment_two_le_mesh_log_add_two_mesh cut)
      (Nat.cast_nonneg _))

/-- Every rank at least three is mesh-scale, with one constant
uniform in the rank. -/
theorem sum_higherRankMass_le
    {mesh : ℝ} (cut : clock.SharpClockCut mesh)
    {coordinateCount rank : ℕ} (hrank : 3 ≤ rank)
    {mass : ℕ → ℝ}
    (dominated : clock.RankDominatedMass coordinateCount rank mass) :
    (∑ time ∈ Finset.range horizon, mass time) ≤
      (coordinateCount.choose rank : ℝ) * (3 * mesh) := by
  exact (clock.sum_rankDominatedMass_le_moment dominated).trans
    (mul_le_mul_of_nonneg_left
      (clock.moment_higher_le_three_mesh cut rank hrank)
      (Nat.cast_nonneg _))

end FiniteWeightedClock

/-! ## 4. Scale comparison -/

/-- An `O(mesh)` remainder remains small after division by a larger positive
scale. -/
theorem div_scale_le_of_mass_le_mesh
    {mass mesh scale coefficient epsilon : ℝ}
    (hcoefficient : 0 ≤ coefficient)
    (hscale : 0 < scale)
    (hmass : mass ≤ coefficient * mesh)
    (hmesh : mesh ≤ epsilon * scale) :
    mass / scale ≤ coefficient * epsilon := by
  apply (div_le_iff₀ hscale).2
  calc
    mass ≤ coefficient * mesh := hmass
    _ ≤ coefficient * (epsilon * scale) :=
      mul_le_mul_of_nonneg_left hmesh hcoefficient
    _ = coefficient * epsilon * scale := by ring

end Math.Probability.WeightedClockRankReduction
