/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Sequences

/-!
# Square-root budgets for disjoint coalition clocks

Independent Quit hazards cannot put arbitrary first-absorption mass on two disjoint pairs.  This
file isolates the game-independent probability core: the local square-root inequality, its exact
nonnegative defect ledger, and a finite-horizon global telescope.  It does not assert that a
strategic construction forces the inequality to be nearly sharp.
-/

namespace Math.Probability

noncomputable section

/-- A real sequence converging to zero and positive somewhere attains a global maximum. -/
theorem exists_maximal_of_tendsto_zero_of_exists_pos
    (f : ℕ → ℝ) (hf : Filter.Tendsto f Filter.atTop (nhds 0))
    (hpos : ∃ n, 0 < f n) :
    ∃ peak, ∀ n, f n ≤ f peak := by
  obtain ⟨anchor, hanchor⟩ := hpos
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.mp hf) (f anchor) hanchor
  let cutoff := max threshold (anchor + 1)
  have hcutoff : (Finset.range cutoff).Nonempty := by
    exact ⟨anchor, Finset.mem_range.mpr
      (lt_of_lt_of_le (Nat.lt_succ_self anchor) (le_max_right _ _))⟩
  have himage : ((Finset.range cutoff).image f).Nonempty := hcutoff.image f
  let peakValue := ((Finset.range cutoff).image f).max' himage
  have hpeakValueMem : peakValue ∈ (Finset.range cutoff).image f :=
    Finset.max'_mem _ _
  obtain ⟨peak, _hpeakMem, hpeakEq⟩ := Finset.mem_image.mp hpeakValueMem
  refine ⟨peak, ?_⟩
  intro n
  have hfinite (k : ℕ) (hk : k ∈ Finset.range cutoff) : f k ≤ f peak := by
    have himem : f k ∈ (Finset.range cutoff).image f :=
      Finset.mem_image.mpr ⟨k, hk, rfl⟩
    have hmax := Finset.le_max' ((Finset.range cutoff).image f) (f k) himem
    simpa [peakValue, hpeakEq] using hmax
  by_cases hn : n < cutoff
  · exact hfinite n (Finset.mem_range.mpr hn)
  · have hnThreshold : threshold ≤ n :=
      le_trans (le_max_left _ _) (Nat.le_of_not_gt hn)
    have hclose := hthreshold n hnThreshold
    rw [Real.dist_eq, sub_zero] at hclose
    have hn_lt_anchor : f n < f anchor := (abs_lt.mp hclose).2
    have hanchor_mem : anchor ∈ Finset.range cutoff := by
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Nat.lt_succ_self anchor) (le_max_right _ _))
    exact hn_lt_anchor.le.trans (hfinite anchor hanchor_mem)

/-- Complement amplitude of a two-member independent gate. -/
def pairContinueAmplitude (first second : ℝ) : ℝ :=
  Real.sqrt ((1 - first) * (1 - second))

/-- Joint-event amplitude of a two-member independent gate. -/
def pairQuitAmplitude (first second : ℝ) : ℝ :=
  Real.sqrt (first * second)

/-- Normalized mass retained by the two target atoms and all-Continue event. -/
def twoPairNormalizedBudget
    (first second third fourth background : ℝ) : ℝ :=
  background *
    (pairQuitAmplitude first second * pairContinueAmplitude third fourth +
      pairContinueAmplitude first second * pairQuitAmplitude third fourth +
      pairContinueAmplitude first second * pairContinueAmplitude third fourth)

theorem continuous_twoPairNormalizedBudget :
    Continuous fun point : ℝ × ℝ × ℝ × ℝ × ℝ =>
      twoPairNormalizedBudget point.1 point.2.1 point.2.2.1 point.2.2.2.1
        point.2.2.2.2 := by
  unfold twoPairNormalizedBudget pairQuitAmplitude pairContinueAmplitude
  fun_prop

/-- The Hellinger affinity of two Bernoulli laws is at most one.  In gate language, the
all-Continue and all-Quit amplitudes of one pair have sum at most one. -/
theorem pairContinueAmplitude_add_pairQuitAmplitude_le_one
    {first second : ℝ} (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1) :
    pairContinueAmplitude first second + pairQuitAmplitude first second ≤ 1 := by
  let f : Bool → ℝ := fun bit => if bit then first else 1 - first
  let g : Bool → ℝ := fun bit => if bit then second else 1 - second
  have hf : ∀ i, 0 ≤ f i := by
    intro i
    cases i <;> simp [f] <;> linarith [hfirst.1, hfirst.2]
  have hg : ∀ i, 0 ≤ g i := by
    intro i
    cases i <;> simp [g] <;> linarith [hsecond.1, hsecond.2]
  have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset Bool) hf hg
  have hleft :
      ∑ i : Bool, Real.sqrt (f i) * Real.sqrt (g i) =
        pairContinueAmplitude first second + pairQuitAmplitude first second := by
    rw [Fintype.sum_bool]
    simp only [f, g, Bool.false_eq_true, ↓reduceIte, pairContinueAmplitude,
      pairQuitAmplitude]
    rw [Real.sqrt_mul (by linarith [hfirst.2])]
    rw [Real.sqrt_mul hfirst.1]
    ring
  have hf_sum : ∑ i : Bool, f i = 1 := by
    rw [Fintype.sum_bool]
    simp [f]
  have hg_sum : ∑ i : Bool, g i = 1 := by
    rw [Fintype.sum_bool]
    simp [g]
  rw [hleft, hf_sum, hg_sum] at hcs
  simpa using hcs

/-- Equality in the two-Bernoulli Hellinger bound forces the two hazards to agree. -/
theorem eq_of_pairContinueAmplitude_add_pairQuitAmplitude_eq_one
    {first second : ℝ} (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (heq : pairContinueAmplitude first second +
      pairQuitAmplitude first second = 1) :
    first = second := by
  let u := pairContinueAmplitude first second
  let v := pairQuitAmplitude first second
  have hu_nonneg : 0 ≤ u := Real.sqrt_nonneg _
  have hv_nonneg : 0 ≤ v := Real.sqrt_nonneg _
  have hcontinue_nonneg : 0 ≤ (1 - first) * (1 - second) :=
    mul_nonneg (by linarith [hfirst.2]) (by linarith [hsecond.2])
  have hquit_nonneg : 0 ≤ first * second := mul_nonneg hfirst.1 hsecond.1
  have hu_sq : u ^ 2 = (1 - first) * (1 - second) :=
    Real.sq_sqrt hcontinue_nonneg
  have hv_sq : v ^ 2 = first * second := Real.sq_sqrt hquit_nonneg
  have huv_sq : (u * v) ^ 2 =
      ((1 - first) * (1 - second)) * (first * second) := by
    rw [mul_pow, hu_sq, hv_sq]
  have hcross : 2 * u * v = first + second - 2 * first * second := by
    dsimp only [u, v] at heq ⊢
    nlinarith
  have hdiff_sq : (first - second) ^ 2 = 0 := by
    nlinarith [sq_nonneg (2 * u * v), huv_sq]
  nlinarith

/-- Abstract normalized local budget for two disjoint pair gates and an additional all-Continue
factor `background`. -/
theorem twoPair_normalized_local_budget
    {u v r s background : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hub : u + v ≤ 1) (hrb : r + s ≤ 1)
    (hbackground : background ∈ Set.Icc (0 : ℝ) 1) :
    background * (v * r) + background * (u * s) +
        background * (u * r) ≤ 1 := by
  have hinner : v * r + u * s + u * r ≤ 1 := by
    have hur : r * (u + v) ≤ r := by
      simpa using mul_le_mul_of_nonneg_left hub hr
    have hu_one : u ≤ 1 := by linarith
    have hus : u * s ≤ s := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hu_one hs
    calc
      v * r + u * s + u * r = r * (u + v) + u * s := by ring
      _ ≤ r + u * s := by linarith
      _ ≤ r + s := by linarith
      _ ≤ 1 := hrb
  have hinner_nonneg : 0 ≤ v * r + u * s + u * r := by positivity
  calc
    background * (v * r) + background * (u * s) +
        background * (u * r) = background * (v * r + u * s + u * r) := by ring
    _ ≤ 1 * (v * r + u * s + u * r) :=
      mul_le_mul_of_nonneg_right hbackground.2 hinner_nonneg
    _ ≤ 1 := by simpa using hinner

/-- Hazard-level form of the local two-pair square-root budget. -/
theorem twoPair_hazard_local_budget
    {first second third fourth background : ℝ}
    (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (hthird : third ∈ Set.Icc (0 : ℝ) 1)
    (hfourth : fourth ∈ Set.Icc (0 : ℝ) 1)
    (hbackground : background ∈ Set.Icc (0 : ℝ) 1) :
    background *
          (pairQuitAmplitude first second * pairContinueAmplitude third fourth) +
        background *
          (pairContinueAmplitude first second * pairQuitAmplitude third fourth) +
        background *
          (pairContinueAmplitude first second * pairContinueAmplitude third fourth) ≤ 1 := by
  exact twoPair_normalized_local_budget
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (pairContinueAmplitude_add_pairQuitAmplitude_le_one hfirst hsecond)
    (pairContinueAmplitude_add_pairQuitAmplitude_le_one hthird hfourth) hbackground

/-- Source data for a finite or infinite two-pair hazard clock.  `background` is the square-root
all-Continue factor of every player outside the two displayed pairs. -/
structure TwoPairHazardClock where
  first : ℕ → ℝ
  second : ℕ → ℝ
  third : ℕ → ℝ
  fourth : ℕ → ℝ
  background : ℕ → ℝ
  survivalRoot : ℕ → ℝ
  first_mem : ∀ time, first time ∈ Set.Icc (0 : ℝ) 1
  second_mem : ∀ time, second time ∈ Set.Icc (0 : ℝ) 1
  third_mem : ∀ time, third time ∈ Set.Icc (0 : ℝ) 1
  fourth_mem : ∀ time, fourth time ∈ Set.Icc (0 : ℝ) 1
  background_mem : ∀ time, background time ∈ Set.Icc (0 : ℝ) 1
  survivalRoot_nonneg : ∀ time, 0 ≤ survivalRoot time
  survivalRoot_zero : survivalRoot 0 = 1
  survivalRoot_step : ∀ time,
    survivalRoot (time + 1) = survivalRoot time * background time *
      pairContinueAmplitude (first time) (second time) *
        pairContinueAmplitude (third time) (fourth time)

namespace TwoPairHazardClock

/-- Survival-weighted amplitude of the first target pair at a date. -/
def firstTargetAmplitude (clock : TwoPairHazardClock) (time : ℕ) : ℝ :=
  clock.survivalRoot time * clock.background time *
    pairQuitAmplitude (clock.first time) (clock.second time) *
      pairContinueAmplitude (clock.third time) (clock.fourth time)

/-- Survival-weighted amplitude of the second target pair at a date. -/
def secondTargetAmplitude (clock : TwoPairHazardClock) (time : ℕ) : ℝ :=
  clock.survivalRoot time * clock.background time *
    pairContinueAmplitude (clock.first time) (clock.second time) *
      pairQuitAmplitude (clock.third time) (clock.fourth time)

/-- Slack in the exact one-date square-root budget. -/
def localDefect (clock : TwoPairHazardClock) (time : ℕ) : ℝ :=
  clock.survivalRoot time - clock.firstTargetAmplitude time -
    clock.secondTargetAmplitude time - clock.survivalRoot (time + 1)

theorem firstTargetAmplitude_nonneg (clock : TwoPairHazardClock) (time : ℕ) :
    0 ≤ clock.firstTargetAmplitude time := by
  dsimp only [firstTargetAmplitude]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (clock.survivalRoot_nonneg time) (clock.background_mem time).1)
      (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

theorem secondTargetAmplitude_nonneg (clock : TwoPairHazardClock) (time : ℕ) :
    0 ≤ clock.secondTargetAmplitude time := by
  dsimp only [secondTargetAmplitude]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (clock.survivalRoot_nonneg time) (clock.background_mem time).1)
      (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

/-- The hazard-level local inequality makes the clock defect nonnegative. -/
theorem localDefect_nonneg (clock : TwoPairHazardClock) (time : ℕ) :
    0 ≤ clock.localDefect time := by
  have hlocal := twoPair_hazard_local_budget
    (clock.first_mem time) (clock.second_mem time)
    (clock.third_mem time) (clock.fourth_mem time) (clock.background_mem time)
  have hscaled := mul_le_mul_of_nonneg_left hlocal (clock.survivalRoot_nonneg time)
  dsimp only [localDefect, firstTargetAmplitude, secondTargetAmplitude]
  rw [clock.survivalRoot_step time]
  nlinarith

theorem local_conservation (clock : TwoPairHazardClock) (time : ℕ) :
    clock.firstTargetAmplitude time + clock.secondTargetAmplitude time +
        clock.localDefect time + clock.survivalRoot (time + 1) =
      clock.survivalRoot time := by
  dsimp only [localDefect]
  ring

theorem survivalRoot_le_one (clock : TwoPairHazardClock) (time : ℕ) :
    clock.survivalRoot time ≤ 1 := by
  induction time with
  | zero => simp [clock.survivalRoot_zero]
  | succ time ih =>
      have hlocal := clock.local_conservation time
      have hfirst := clock.firstTargetAmplitude_nonneg time
      have hsecond := clock.secondTargetAmplitude_nonneg time
      have hdefect := clock.localDefect_nonneg time
      simpa only [Nat.succ_eq_add_one] using (show
        clock.survivalRoot (time + 1) ≤ 1 by linarith)

/-- The source clock's local defect is survival times the normalized Hellinger slack. -/
theorem localDefect_eq_survivalRoot_mul_one_sub_normalizedBudget
    (clock : TwoPairHazardClock) (time : ℕ) :
    clock.localDefect time = clock.survivalRoot time *
      (1 - twoPairNormalizedBudget (clock.first time) (clock.second time)
        (clock.third time) (clock.fourth time) (clock.background time)) := by
  rw [localDefect, firstTargetAmplitude, secondTargetAmplitude,
    clock.survivalRoot_step]
  unfold twoPairNormalizedBudget
  ring

theorem normalizedBudget_mem_Icc (clock : TwoPairHazardClock) (time : ℕ) :
    twoPairNormalizedBudget (clock.first time) (clock.second time)
      (clock.third time) (clock.fourth time) (clock.background time) ∈
        Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold twoPairNormalizedBudget
    exact mul_nonneg (clock.background_mem time).1 (add_nonneg
      (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  · have h := twoPair_hazard_local_budget (clock.first_mem time)
      (clock.second_mem time) (clock.third_mem time) (clock.fourth_mem time)
      (clock.background_mem time)
    unfold twoPairNormalizedBudget
    nlinarith

end TwoPairHazardClock

/-- Positive reached survival converts vanishing local source defect into normalized equality. -/
theorem selected_normalizedBudget_tendsto_one
    (clock : ℕ → TwoPairHazardClock) (time : ℕ → ℕ) {floor : ℝ}
    (floor_pos : 0 < floor)
    (survival_ge : ∀ n, floor ≤ (clock n).survivalRoot (time n))
    (defect_tendsto : Filter.Tendsto
      (fun n => (clock n).localDefect (time n)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => twoPairNormalizedBudget
      ((clock n).first (time n)) ((clock n).second (time n))
      ((clock n).third (time n)) ((clock n).fourth (time n))
      ((clock n).background (time n))) Filter.atTop (nhds 1) := by
  have hbound : Filter.Tendsto
      (fun n => (clock n).localDefect (time n) / floor)
      Filter.atTop (nhds 0) := by
    simpa using defect_tendsto.div_const floor
  have hgap : Filter.Tendsto (fun n => 1 - twoPairNormalizedBudget
      ((clock n).first (time n)) ((clock n).second (time n))
      ((clock n).third (time n)) ((clock n).fourth (time n))
      ((clock n).background (time n))) Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      have hbudget := (clock n).normalizedBudget_mem_Icc (time n)
      exact sub_nonneg.mpr hbudget.2
    · intro n
      let budget := twoPairNormalizedBudget
        ((clock n).first (time n)) ((clock n).second (time n))
        ((clock n).third (time n)) ((clock n).fourth (time n))
        ((clock n).background (time n))
      have hbudget := (clock n).normalizedBudget_mem_Icc (time n)
      have hdefect := (clock n).localDefect_eq_survivalRoot_mul_one_sub_normalizedBudget
        (time n)
      have hscaled : floor * (1 - budget) ≤ (clock n).localDefect (time n) := by
        rw [hdefect]
        exact mul_le_mul_of_nonneg_right (survival_ge n) (by linarith [hbudget.2])
      exact (le_div_iff₀ floor_pos).2 (by
        simpa [mul_comm] using hscaled)
    · exact hbound
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  simpa only [sub_sub_cancel, sub_zero] using hone.sub hgap

/-- Vanishing post-row survival at a uniformly reached row forces its conditional all-Continue
factor to vanish. -/
theorem selected_allContinueFactor_tendsto_zero
    (clock : ℕ → TwoPairHazardClock) (time : ℕ → ℕ) {floor : ℝ}
    (floor_pos : 0 < floor)
    (survival_ge : ∀ n, floor ≤ (clock n).survivalRoot (time n))
    (next_tendsto : Filter.Tendsto
      (fun n => (clock n).survivalRoot (time n + 1)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => (clock n).background (time n) *
      pairContinueAmplitude ((clock n).first (time n)) ((clock n).second (time n)) *
      pairContinueAmplitude ((clock n).third (time n)) ((clock n).fourth (time n)))
      Filter.atTop (nhds 0) := by
  let factor : ℕ → ℝ := fun n => (clock n).background (time n) *
    pairContinueAmplitude ((clock n).first (time n)) ((clock n).second (time n)) *
    pairContinueAmplitude ((clock n).third (time n)) ((clock n).fourth (time n))
  have hbound : Filter.Tendsto
      (fun n => (clock n).survivalRoot (time n + 1) / floor)
      Filter.atTop (nhds 0) := by
    simpa using next_tendsto.div_const floor
  apply squeeze_zero
  · intro n
    exact mul_nonneg
      (mul_nonneg ((clock n).background_mem (time n)).1 (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  · intro n
    have hstep := (clock n).survivalRoot_step (time n)
    have hfactor_nonneg : 0 ≤ factor n := by
      dsimp only [factor]
      exact mul_nonneg
        (mul_nonneg ((clock n).background_mem (time n)).1 (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    have hscaled : floor * factor n ≤ (clock n).survivalRoot (time n + 1) := by
      rw [hstep]
      simpa only [factor, mul_assoc] using
        mul_le_mul_of_nonneg_right (survival_ge n) hfactor_nonneg
    change factor n ≤ (clock n).survivalRoot (time n + 1) / floor
    exact (le_div_iff₀ floor_pos).2 (by simpa [mul_comm] using hscaled)
  · exact hbound

/-- First exact presentation of the normalized local defect. -/
theorem twoPair_local_defect_eq_first_ledger
    (u v r s background : ℝ) :
    1 - background * (v * r + u * s + u * r) =
      (1 - background) + background *
        ((1 - r - s) + r * (1 - u - v) + s * (1 - u)) := by
  ring

/-- Symmetric exact presentation of the normalized local defect. -/
theorem twoPair_local_defect_eq_second_ledger
    (u v r s background : ℝ) :
    1 - background * (v * r + u * s + u * r) =
      (1 - background) + background *
        ((1 - u - v) + u * (1 - r - s) + v * (1 - r)) := by
  ring

/-- Every term in the first exact local ledger is nonnegative under the pair-amplitude bounds. -/
theorem twoPair_first_ledger_nonneg
    {u v r s background : ℝ}
    (hv : 0 ≤ v) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hub : u + v ≤ 1) (hrb : r + s ≤ 1)
    (hbackground : background ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (1 - background) + background *
      ((1 - r - s) + r * (1 - u - v) + s * (1 - u)) := by
  have hu_one : u ≤ 1 := by linarith
  have hbackground_defect : 0 ≤ 1 - background := sub_nonneg.mpr hbackground.2
  have hr_defect : 0 ≤ 1 - r - s := by linarith
  have hu_defect : 0 ≤ 1 - u - v := by linarith
  have hu_single : 0 ≤ 1 - u := by linarith
  exact add_nonneg hbackground_defect (mul_nonneg hbackground.1
    (add_nonneg (add_nonneg hr_defect (mul_nonneg hr hu_defect))
      (mul_nonneg hs hu_single)))

/-- Equality in the local budget, together with positive first-pair amplitude, forces the second
pair to be inactive and the first pair to saturate its own Hellinger bound. -/
theorem twoPair_local_eq_one_of_first_active
    {u v r s background : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hub : u + v ≤ 1) (hrb : r + s ≤ 1)
    (hbackground : background ∈ Set.Icc (0 : ℝ) 1)
    (local_eq : background * (v * r + u * s + u * r) = 1)
    (first_active : 0 < v * r) :
    background = 1 ∧ s = 0 ∧ r = 1 ∧ u + v = 1 := by
  have hu_one : u ≤ 1 := by linarith
  have hinner_nonneg : 0 ≤ v * r + u * s + u * r := by positivity
  have hinner_le : v * r + u * s + u * r ≤ 1 := by
    have hur : r * (u + v) ≤ r := by
      simpa using mul_le_mul_of_nonneg_left hub hr
    have hus : u * s ≤ s := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hu_one hs
    calc
      v * r + u * s + u * r = r * (u + v) + u * s := by ring
      _ ≤ r + u * s := by linarith
      _ ≤ r + s := by linarith
      _ ≤ 1 := hrb
  have hone_le_background : 1 ≤ background := by
    calc
      1 = background * (v * r + u * s + u * r) := local_eq.symm
      _ ≤ background * 1 := mul_le_mul_of_nonneg_left hinner_le hbackground.1
      _ = background := mul_one background
  have hbackground_eq : background = 1 := le_antisymm hbackground.2 hone_le_background
  have hinner_eq : v * r + u * s + u * r = 1 := by
    simpa [hbackground_eq] using local_eq
  have hfirst_defect :
      r * (1 - u - v) + s * (1 - u) = 0 := by
    nlinarith
  have hr_pos : 0 < r := lt_of_not_ge fun hr_nonpos => by
    have : v * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv hr_nonpos
    linarith
  have hv_pos : 0 < v := lt_of_not_ge fun hv_nonpos => by
    have : v * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hv_nonpos hr
    linarith
  have hfirst_term : 0 ≤ r * (1 - u - v) :=
    mul_nonneg hr (by linarith)
  have hsecond_term : 0 ≤ s * (1 - u) :=
    mul_nonneg hs (by linarith)
  have hsecond_zero : s * (1 - u) = 0 := by linarith
  have hs_zero : s = 0 := by
    rcases mul_eq_zero.mp hsecond_zero with hs_zero | hu_eq
    · exact hs_zero
    · have hu_eq_one : u = 1 := by linarith
      linarith
  have hr_eq : r = 1 := by linarith
  have huv_eq : u + v = 1 := by
    have hfirst_zero : r * (1 - u - v) = 0 := by linarith
    nlinarith
  exact ⟨hbackground_eq, hs_zero, hr_eq, huv_eq⟩

/-- Symmetric equality classification for positive second-pair amplitude. -/
theorem twoPair_local_eq_one_of_second_active
    {u v r s background : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hub : u + v ≤ 1) (hrb : r + s ≤ 1)
    (hbackground : background ∈ Set.Icc (0 : ℝ) 1)
    (local_eq : background * (v * r + u * s + u * r) = 1)
    (second_active : 0 < u * s) :
    background = 1 ∧ v = 0 ∧ u = 1 ∧ r + s = 1 := by
  have h := twoPair_local_eq_one_of_first_active
    hr hs hu hv hrb hub hbackground (by
      convert local_eq using 1
      ring) (by simpa [mul_comm] using second_active)
  exact h

/-- Hazard-coordinate form of the first-active equality classification. -/
theorem twoPair_hazard_local_eq_one_of_first_active
    {first second third fourth background : ℝ}
    (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (hthird : third ∈ Set.Icc (0 : ℝ) 1)
    (hfourth : fourth ∈ Set.Icc (0 : ℝ) 1)
    (hbackground : background ∈ Set.Icc (0 : ℝ) 1)
    (local_eq : background *
      (pairQuitAmplitude first second * pairContinueAmplitude third fourth +
        pairContinueAmplitude first second * pairQuitAmplitude third fourth +
        pairContinueAmplitude first second * pairContinueAmplitude third fourth) = 1)
    (first_active : 0 < pairQuitAmplitude first second *
      pairContinueAmplitude third fourth) :
    background = 1 ∧ third = 0 ∧ fourth = 0 ∧ first = second := by
  have h := twoPair_local_eq_one_of_first_active
    (u := pairContinueAmplitude first second)
    (v := pairQuitAmplitude first second)
    (r := pairContinueAmplitude third fourth)
    (s := pairQuitAmplitude third fourth)
    (background := background)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)
    (pairContinueAmplitude_add_pairQuitAmplitude_le_one hfirst hsecond)
    (pairContinueAmplitude_add_pairQuitAmplitude_le_one hthird hfourth)
    hbackground (by
      simpa only [pairContinueAmplitude, pairQuitAmplitude, add_assoc] using local_eq)
    (by simpa only [pairContinueAmplitude, pairQuitAmplitude] using first_active)
  rcases h with ⟨hbackground_eq, hs, hr, huv⟩
  have hthird_zero : third = 0 := by
    have hprod_nonneg : 0 ≤ (1 - third) * (1 - fourth) :=
      mul_nonneg (by linarith [hthird.2]) (by linarith [hfourth.2])
    have hr_sq := Real.sq_sqrt hprod_nonneg
    change Real.sqrt ((1 - third) * (1 - fourth)) = 1 at hr
    have hmul_le : third * fourth ≤ fourth :=
      mul_le_of_le_one_left hfourth.1 hthird.2
    nlinarith [hthird.1, hfourth.1]
  have hfourth_zero : fourth = 0 := by
    have hprod_nonneg : 0 ≤ (1 - third) * (1 - fourth) :=
      mul_nonneg (by linarith [hthird.2]) (by linarith [hfourth.2])
    have hr_sq := Real.sq_sqrt hprod_nonneg
    change Real.sqrt ((1 - third) * (1 - fourth)) = 1 at hr
    have hmul_le : third * fourth ≤ third :=
      mul_le_of_le_one_right hthird.1 hfourth.2
    nlinarith [hthird.1, hfourth.1]
  have hfirst_second : first = second :=
    eq_of_pairContinueAmplitude_add_pairQuitAmplitude_eq_one hfirst hsecond (by
      simpa only [pairContinueAmplitude, pairQuitAmplitude] using huv)
  exact ⟨hbackground_eq, hthird_zero, hfourth_zero, hfirst_second⟩

/-- Symmetric hazard-coordinate equality classification. -/
theorem twoPair_hazard_local_eq_one_of_second_active
    {first second third fourth background : ℝ}
    (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (hthird : third ∈ Set.Icc (0 : ℝ) 1)
    (hfourth : fourth ∈ Set.Icc (0 : ℝ) 1)
    (hbackground : background ∈ Set.Icc (0 : ℝ) 1)
    (local_eq : background *
      (pairQuitAmplitude first second * pairContinueAmplitude third fourth +
        pairContinueAmplitude first second * pairQuitAmplitude third fourth +
        pairContinueAmplitude first second * pairContinueAmplitude third fourth) = 1)
    (second_active : 0 < pairContinueAmplitude first second *
      pairQuitAmplitude third fourth) :
    background = 1 ∧ first = 0 ∧ second = 0 ∧ third = fourth := by
  have h := twoPair_hazard_local_eq_one_of_first_active hthird hfourth hfirst hsecond
    hbackground (by
      convert local_eq using 1
      ring) (by simpa [mul_comm] using second_active)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- A zero-defect reached row cannot carry both target-pair amplitudes positively. -/
theorem not_both_twoPair_targets_active_of_normalizedBudget_eq_one
    {first second third fourth background : ℝ}
    (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (hthird : third ∈ Set.Icc (0 : ℝ) 1)
    (hfourth : fourth ∈ Set.Icc (0 : ℝ) 1)
    (hbackground : background ∈ Set.Icc (0 : ℝ) 1)
    (local_eq : twoPairNormalizedBudget first second third fourth background = 1) :
    ¬ (0 < pairQuitAmplitude first second * pairContinueAmplitude third fourth ∧
      0 < pairContinueAmplitude first second * pairQuitAmplitude third fourth) := by
  rintro ⟨hfirstActive, hsecondActive⟩
  have hfirstClass := twoPair_hazard_local_eq_one_of_first_active
    hfirst hsecond hthird hfourth hbackground local_eq hfirstActive
  have hsecondClass := twoPair_hazard_local_eq_one_of_second_active
    hfirst hsecond hthird hfourth hbackground local_eq hsecondActive
  rw [hfirstClass.2.1, hfirstClass.2.2.1] at hsecondActive
  simp [pairQuitAmplitude] at hsecondActive

/-- In the pure second-pair equality class, zero conditional survival forces a sure exit. -/
theorem secondPair_hazard_eq_one_of_continueAmplitude_eq_zero
    {hazard : ℝ} (hzero : pairContinueAmplitude hazard hazard = 0) :
    hazard = 1 := by
  have hsquare_nonneg : 0 ≤ (1 - hazard) * (1 - hazard) :=
    mul_self_nonneg (1 - hazard)
  have hsquare := Real.sq_sqrt hsquare_nonneg
  change Real.sqrt ((1 - hazard) * (1 - hazard)) = 0 at hzero
  nlinarith

/-- The two positive target-mass floors give the closed interval for the first gate hazard. -/
theorem mem_gateInterval_of_two_mass_floors
    {alpha hazard : ℝ} (hazard_mem : hazard ∈ Set.Icc (0 : ℝ) 1)
    (first_floor : alpha ≤ hazard ^ 2)
    (second_floor : alpha ≤ (1 - hazard) ^ 2) :
    hazard ∈ Set.Icc (Real.sqrt alpha) (1 - Real.sqrt alpha) := by
  constructor
  · exact Real.sqrt_le_iff.mpr ⟨hazard_mem.1, first_floor⟩
  · have hsqrt_le : Real.sqrt alpha ≤ 1 - hazard :=
      Real.sqrt_le_iff.mpr ⟨by linarith [hazard_mem.2], second_floor⟩
    linarith

/-- Closed limit form of the first-gate equality classification.  This is the local consumer
used after finite-dimensional subsequence extraction. -/
theorem twoPair_hazard_limit_firstGate
    {first second third fourth background : ℕ → ℝ}
    {firstLimit secondLimit thirdLimit fourthLimit backgroundLimit : ℝ}
    (hfirst : Filter.Tendsto first Filter.atTop (nhds firstLimit))
    (hsecond : Filter.Tendsto second Filter.atTop (nhds secondLimit))
    (hthird : Filter.Tendsto third Filter.atTop (nhds thirdLimit))
    (hfourth : Filter.Tendsto fourth Filter.atTop (nhds fourthLimit))
    (hbackground : Filter.Tendsto background Filter.atTop (nhds backgroundLimit))
    (first_mem : ∀ n, first n ∈ Set.Icc (0 : ℝ) 1)
    (second_mem : ∀ n, second n ∈ Set.Icc (0 : ℝ) 1)
    (third_mem : ∀ n, third n ∈ Set.Icc (0 : ℝ) 1)
    (fourth_mem : ∀ n, fourth n ∈ Set.Icc (0 : ℝ) 1)
    (background_mem : ∀ n, background n ∈ Set.Icc (0 : ℝ) 1)
    (budget_tendsto : Filter.Tendsto (fun n => twoPairNormalizedBudget
      (first n) (second n) (third n) (fourth n) (background n))
      Filter.atTop (nhds 1))
    (first_active : 0 < pairQuitAmplitude firstLimit secondLimit *
      pairContinueAmplitude thirdLimit fourthLimit) :
    backgroundLimit = 1 ∧ thirdLimit = 0 ∧ fourthLimit = 0 ∧
      firstLimit = secondLimit := by
  have hfirstLimit : firstLimit ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hfirst (Filter.Eventually.of_forall first_mem)
  have hsecondLimit : secondLimit ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hsecond (Filter.Eventually.of_forall second_mem)
  have hthirdLimit : thirdLimit ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hthird (Filter.Eventually.of_forall third_mem)
  have hfourthLimit : fourthLimit ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hfourth (Filter.Eventually.of_forall fourth_mem)
  have hbackgroundLimit : backgroundLimit ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hbackground
      (Filter.Eventually.of_forall background_mem)
  have hpoint : Filter.Tendsto
      (fun n => (first n, second n, third n, fourth n, background n)) Filter.atTop
      (nhds (firstLimit, secondLimit, thirdLimit, fourthLimit, backgroundLimit)) :=
    by
      simpa only [nhds_prod_eq] using
        hfirst.prodMk (hsecond.prodMk (hthird.prodMk (hfourth.prodMk hbackground)))
  have hcontinuous : Filter.Tendsto (fun n => twoPairNormalizedBudget
      (first n) (second n) (third n) (fourth n) (background n)) Filter.atTop
      (nhds (twoPairNormalizedBudget firstLimit secondLimit thirdLimit fourthLimit
        backgroundLimit)) :=
    continuous_twoPairNormalizedBudget.continuousAt.tendsto.comp hpoint
  have hlocal : twoPairNormalizedBudget firstLimit secondLimit thirdLimit fourthLimit
      backgroundLimit = 1 := tendsto_nhds_unique hcontinuous budget_tendsto
  exact twoPair_hazard_local_eq_one_of_first_active hfirstLimit hsecondLimit
    hthirdLimit hfourthLimit hbackgroundLimit hlocal first_active

/-- Symmetric closed limit classifier for a positive second-gate amplitude. -/
theorem twoPair_hazard_limit_secondGate
    {first second third fourth background : ℕ → ℝ}
    {firstLimit secondLimit thirdLimit fourthLimit backgroundLimit : ℝ}
    (hfirst : Filter.Tendsto first Filter.atTop (nhds firstLimit))
    (hsecond : Filter.Tendsto second Filter.atTop (nhds secondLimit))
    (hthird : Filter.Tendsto third Filter.atTop (nhds thirdLimit))
    (hfourth : Filter.Tendsto fourth Filter.atTop (nhds fourthLimit))
    (hbackground : Filter.Tendsto background Filter.atTop (nhds backgroundLimit))
    (first_mem : ∀ n, first n ∈ Set.Icc (0 : ℝ) 1)
    (second_mem : ∀ n, second n ∈ Set.Icc (0 : ℝ) 1)
    (third_mem : ∀ n, third n ∈ Set.Icc (0 : ℝ) 1)
    (fourth_mem : ∀ n, fourth n ∈ Set.Icc (0 : ℝ) 1)
    (background_mem : ∀ n, background n ∈ Set.Icc (0 : ℝ) 1)
    (budget_tendsto : Filter.Tendsto (fun n => twoPairNormalizedBudget
      (first n) (second n) (third n) (fourth n) (background n))
      Filter.atTop (nhds 1))
    (second_active : 0 < pairContinueAmplitude firstLimit secondLimit *
      pairQuitAmplitude thirdLimit fourthLimit) :
    backgroundLimit = 1 ∧ firstLimit = 0 ∧ secondLimit = 0 ∧
      thirdLimit = fourthLimit := by
  have h := twoPair_hazard_limit_firstGate hthird hfourth hfirst hsecond hbackground
    third_mem fourth_mem first_mem second_mem background_mem (by
      simpa [twoPairNormalizedBudget, add_comm, add_left_comm, add_assoc,
        mul_comm] using budget_tendsto) (by simpa [mul_comm] using second_active)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Quantitative compactness separation: along rows whose normalized defect vanishes, the two
target amplitudes cannot both stay uniformly positive. -/
theorem not_eventually_both_targets_active_of_budget_tendsto_one
    {first second third fourth background : ℕ → ℝ} {floor : ℝ}
    (floor_pos : 0 < floor)
    (first_mem : ∀ n, first n ∈ Set.Icc (0 : ℝ) 1)
    (second_mem : ∀ n, second n ∈ Set.Icc (0 : ℝ) 1)
    (third_mem : ∀ n, third n ∈ Set.Icc (0 : ℝ) 1)
    (fourth_mem : ∀ n, fourth n ∈ Set.Icc (0 : ℝ) 1)
    (background_mem : ∀ n, background n ∈ Set.Icc (0 : ℝ) 1)
    (budget_tendsto : Filter.Tendsto (fun n => twoPairNormalizedBudget
      (first n) (second n) (third n) (fourth n) (background n))
      Filter.atTop (nhds 1)) :
    ¬ Filter.Eventually (fun n : ℕ =>
      floor ≤ pairQuitAmplitude (first n) (second n) *
          pairContinueAmplitude (third n) (fourth n) ∧
        floor ≤ pairContinueAmplitude (first n) (second n) *
          pairQuitAmplitude (third n) (fourth n)) Filter.atTop := by
  intro hboth
  let point : ℕ → ℝ × ℝ × ℝ × ℝ × ℝ := fun n =>
    (first n, second n, third n, fourth n, background n)
  let compactSet : Set (ℝ × ℝ × ℝ × ℝ × ℝ) :=
    Set.Icc 0 1 ×ˢ (Set.Icc 0 1 ×ˢ
      (Set.Icc 0 1 ×ˢ (Set.Icc 0 1 ×ˢ Set.Icc 0 1)))
  have hcompact : IsSeqCompact compactSet :=
    (isCompact_Icc.prod (isCompact_Icc.prod
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)))).isSeqCompact
  have hfrequent : Filter.Frequently (fun n => point n ∈ compactSet) Filter.atTop :=
    (Filter.Eventually.of_forall fun n => ⟨first_mem n, second_mem n,
      third_mem n, fourth_mem n, background_mem n⟩).frequently
  obtain ⟨limit, limit_mem, subsequence, subsequence_strictMono, hlimit⟩ :=
    hcompact.subseq_of_frequently_in hfrequent
  let firstLimit := limit.1
  let secondLimit := limit.2.1
  let thirdLimit := limit.2.2.1
  let fourthLimit := limit.2.2.2.1
  let backgroundLimit := limit.2.2.2.2
  have hfirst : Filter.Tendsto (first ∘ subsequence) Filter.atTop
      (nhds firstLimit) := by
    simpa [point, firstLimit, Function.comp_def] using
      continuous_fst.continuousAt.tendsto.comp hlimit
  have hsecond : Filter.Tendsto (second ∘ subsequence) Filter.atTop
      (nhds secondLimit) := by
    simpa [point, secondLimit, Function.comp_def] using
      (continuous_fst.comp continuous_snd).continuousAt.tendsto.comp hlimit
  have hthird : Filter.Tendsto (third ∘ subsequence) Filter.atTop
      (nhds thirdLimit) := by
    simpa [point, thirdLimit, Function.comp_def] using
      (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt.tendsto.comp
        hlimit
  have hfourth : Filter.Tendsto (fourth ∘ subsequence) Filter.atTop
      (nhds fourthLimit) := by
    simpa [point, fourthLimit, Function.comp_def] using
      (continuous_fst.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd))).continuousAt.tendsto.comp
          hlimit
  have hbackground : Filter.Tendsto (background ∘ subsequence) Filter.atTop
      (nhds backgroundLimit) := by
    simpa [point, backgroundLimit, Function.comp_def] using
      (continuous_snd.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd))).continuousAt.tendsto.comp
          hlimit
  have hbudgetSubsequence := budget_tendsto.comp subsequence_strictMono.tendsto_atTop
  have hfirstActivity : Filter.Tendsto (fun n =>
      pairQuitAmplitude (first (subsequence n)) (second (subsequence n)) *
        pairContinueAmplitude (third (subsequence n)) (fourth (subsequence n)))
      Filter.atTop (nhds (pairQuitAmplitude firstLimit secondLimit *
        pairContinueAmplitude thirdLimit fourthLimit)) := by
    unfold pairQuitAmplitude pairContinueAmplitude
    exact (hfirst.mul hsecond).sqrt.mul
      ((hthird.const_sub 1).mul (hfourth.const_sub 1)).sqrt
  have hsecondActivity : Filter.Tendsto (fun n =>
      pairContinueAmplitude (first (subsequence n)) (second (subsequence n)) *
        pairQuitAmplitude (third (subsequence n)) (fourth (subsequence n)))
      Filter.atTop (nhds (pairContinueAmplitude firstLimit secondLimit *
        pairQuitAmplitude thirdLimit fourthLimit)) := by
    unfold pairQuitAmplitude pairContinueAmplitude
    exact ((hfirst.const_sub 1).mul (hsecond.const_sub 1)).sqrt.mul
      (hthird.mul hfourth).sqrt
  have hbothSubsequence := subsequence_strictMono.tendsto_atTop.eventually hboth
  have hfirstFloor : floor ≤ pairQuitAmplitude firstLimit secondLimit *
      pairContinueAmplitude thirdLimit fourthLimit :=
    ge_of_tendsto hfirstActivity (hbothSubsequence.mono fun _ h => h.1)
  have hsecondFloor : floor ≤ pairContinueAmplitude firstLimit secondLimit *
      pairQuitAmplitude thirdLimit fourthLimit :=
    ge_of_tendsto hsecondActivity (hbothSubsequence.mono fun _ h => h.2)
  have hlocalClass := twoPair_hazard_limit_firstGate hfirst hsecond hthird hfourth
    hbackground (fun n => first_mem (subsequence n))
    (fun n => second_mem (subsequence n)) (fun n => third_mem (subsequence n))
    (fun n => fourth_mem (subsequence n)) (fun n => background_mem (subsequence n))
    (by simpa [Function.comp_def] using hbudgetSubsequence) (by linarith)
  rw [hlocalClass.2.1, hlocalClass.2.2.1] at hsecondFloor
  simp [pairQuitAmplitude] at hsecondFloor
  linarith

/-- Dominant dates with uniformly positive target amplitudes are eventually distinct once the
selected local defect vanishes. -/
theorem eventually_selected_target_dates_ne
    (clock : ℕ → TwoPairHazardClock) (firstTime secondTime : ℕ → ℕ)
    {survivalFloor targetFloor : ℝ}
    (survivalFloor_pos : 0 < survivalFloor) (targetFloor_pos : 0 < targetFloor)
    (survival_ge : ∀ n, survivalFloor ≤ (clock n).survivalRoot (firstTime n))
    (defect_tendsto : Filter.Tendsto
      (fun n => (clock n).localDefect (firstTime n)) Filter.atTop (nhds 0))
    (firstTarget_ge : ∀ n, targetFloor ≤
      (clock n).firstTargetAmplitude (firstTime n))
    (secondTarget_ge : ∀ n, targetFloor ≤
      (clock n).secondTargetAmplitude (secondTime n)) :
    Filter.Eventually (fun n => firstTime n ≠ secondTime n) Filter.atTop := by
  by_contra hnot
  have hequal : Filter.Frequently (fun n => firstTime n = secondTime n) Filter.atTop := by
    simpa only [Filter.Eventually, Filter.Frequently, not_not] using hnot
  obtain ⟨subsequence, subsequence_strictMono, hsubsequence⟩ :=
    Filter.extraction_of_frequently_atTop hequal
  let selectedClock : ℕ → TwoPairHazardClock := clock ∘ subsequence
  let selectedTime : ℕ → ℕ := firstTime ∘ subsequence
  have hbudget := selected_normalizedBudget_tendsto_one selectedClock selectedTime
    survivalFloor_pos (fun n => survival_ge (subsequence n))
    (defect_tendsto.comp subsequence_strictMono.tendsto_atTop)
  have hboth : Filter.Eventually (fun n =>
      targetFloor ≤ pairQuitAmplitude
          ((selectedClock n).first (selectedTime n))
          ((selectedClock n).second (selectedTime n)) *
        pairContinueAmplitude ((selectedClock n).third (selectedTime n))
          ((selectedClock n).fourth (selectedTime n)) ∧
      targetFloor ≤ pairContinueAmplitude
          ((selectedClock n).first (selectedTime n))
          ((selectedClock n).second (selectedTime n)) *
        pairQuitAmplitude ((selectedClock n).third (selectedTime n))
          ((selectedClock n).fourth (selectedTime n))) Filter.atTop := by
    apply Filter.Eventually.of_forall
    intro n
    have hsurvival := (selectedClock n).survivalRoot_le_one (selectedTime n)
    have hbackground := ((selectedClock n).background_mem (selectedTime n)).2
    have hfirstFactor : 0 ≤ pairQuitAmplitude
        ((selectedClock n).first (selectedTime n))
        ((selectedClock n).second (selectedTime n)) *
          pairContinueAmplitude ((selectedClock n).third (selectedTime n))
            ((selectedClock n).fourth (selectedTime n)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsecondFactor : 0 ≤ pairContinueAmplitude
        ((selectedClock n).first (selectedTime n))
        ((selectedClock n).second (selectedTime n)) *
          pairQuitAmplitude ((selectedClock n).third (selectedTime n))
            ((selectedClock n).fourth (selectedTime n)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hscale : (selectedClock n).survivalRoot (selectedTime n) *
        (selectedClock n).background (selectedTime n) ≤ 1 := by
      calc
        _ ≤ 1 * (selectedClock n).background (selectedTime n) :=
          mul_le_mul_of_nonneg_right hsurvival
            ((selectedClock n).background_mem (selectedTime n)).1
        _ ≤ 1 := by simpa using hbackground
    constructor
    · calc
        targetFloor ≤ (selectedClock n).firstTargetAmplitude (selectedTime n) :=
          firstTarget_ge (subsequence n)
        _ ≤ _ := by
          unfold TwoPairHazardClock.firstTargetAmplitude
          simpa only [mul_assoc] using mul_le_of_le_one_left hfirstFactor hscale
    · calc
        targetFloor ≤ (selectedClock n).secondTargetAmplitude (selectedTime n) := by
          rw [show selectedTime n = secondTime (subsequence n) from
            hsubsequence n]
          exact secondTarget_ge (subsequence n)
        _ ≤ _ := by
          unfold TwoPairHazardClock.secondTargetAmplitude
          simpa only [mul_assoc] using mul_le_of_le_one_left hsecondFactor hscale
  exact (not_eventually_both_targets_active_of_budget_tendsto_one targetFloor_pos
    (fun n => (selectedClock n).first_mem (selectedTime n))
    (fun n => (selectedClock n).second_mem (selectedTime n))
    (fun n => (selectedClock n).third_mem (selectedTime n))
    (fun n => (selectedClock n).fourth_mem (selectedTime n))
    (fun n => (selectedClock n).background_mem (selectedTime n)) hbudget) hboth

/-- Two eventually distinct date sequences have a subsequence with one fixed orientation. -/
theorem exists_oriented_subsequence_of_eventually_ne
    (firstTime secondTime : ℕ → ℕ)
    (hne : Filter.Eventually (fun n => firstTime n ≠ secondTime n) Filter.atTop) :
    (∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      ∀ n, firstTime (subsequence n) < secondTime (subsequence n)) ∨
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      ∀ n, secondTime (subsequence n) < firstTime (subsequence n) := by
  by_cases hfrequent : Filter.Frequently
      (fun n => firstTime n < secondTime n) Filter.atTop
  · left
    exact Filter.extraction_of_frequently_atTop hfrequent
  · right
    have hnot : Filter.Eventually
        (fun n => ¬ firstTime n < secondTime n) Filter.atTop := by
      simpa only [Filter.Frequently, not_not] using hfrequent
    have horiented : Filter.Eventually
        (fun n => secondTime n < firstTime n) Filter.atTop := by
      filter_upwards [hne, hnot] with n hn hnotn
      omega
    exact Filter.extraction_of_eventually_atTop horiented

/-! ## More than two disjoint target coalitions -/

/-- All-Continue amplitude of one target coalition. -/
def coalitionContinueAmplitude
    {Player : Type*} [DecidableEq Player]
    (coalition : Finset Player) (hazard : Player → ℝ) : ℝ :=
  Real.sqrt (∏ player ∈ coalition, (1 - hazard player))

/-- All-Quit amplitude of one target coalition. -/
def coalitionQuitAmplitude
    {Player : Type*} [DecidableEq Player]
    (coalition : Finset Player) (hazard : Player → ℝ) : ℝ :=
  Real.sqrt (∏ player ∈ coalition, hazard player)

/-- Every coalition with at least two independent members has complementary all-Continue and
all-Quit amplitudes summing to at most one. -/
theorem coalitionContinueAmplitude_add_quitAmplitude_le_one
    {Player : Type*} [DecidableEq Player]
    (coalition : Finset Player) (hazard : Player → ℝ)
    (card_ge_two : 2 ≤ coalition.card)
    (hazard_mem : ∀ player ∈ coalition, hazard player ∈ Set.Icc (0 : ℝ) 1) :
    coalitionContinueAmplitude coalition hazard +
        coalitionQuitAmplitude coalition hazard ≤ 1 := by
  have hcard : 1 < coalition.card := lt_of_lt_of_le Nat.one_lt_two card_ge_two
  obtain ⟨first, first_mem, second, second_mem, distinct⟩ :=
    Finset.one_lt_card.mp hcard
  have hpair_subset : ({first, second} : Finset Player) ⊆ coalition := by
    intro player hplayer
    simp only [Finset.mem_insert, Finset.mem_singleton] at hplayer
    rcases hplayer with rfl | rfl
    · exact first_mem
    · exact second_mem
  have hquit_prod :
      (∏ player ∈ coalition, hazard player) ≤ hazard first * hazard second := by
    have h := Finset.prod_le_prod_of_subset_of_le_one hpair_subset
      (fun player hplayer => (hazard_mem player hplayer).1)
      (fun player hplayer _ => (hazard_mem player hplayer).2)
    simpa [distinct, mul_comm] using h
  have hcontinue_prod :
      (∏ player ∈ coalition, (1 - hazard player)) ≤
        (1 - hazard first) * (1 - hazard second) := by
    have h := Finset.prod_le_prod_of_subset_of_le_one hpair_subset
      (fun player hplayer => sub_nonneg.mpr (hazard_mem player hplayer).2)
      (fun player hplayer _ => by linarith [(hazard_mem player hplayer).1])
    simpa [distinct, mul_comm] using h
  calc
    coalitionContinueAmplitude coalition hazard +
        coalitionQuitAmplitude coalition hazard ≤
      pairContinueAmplitude (hazard first) (hazard second) +
        pairQuitAmplitude (hazard first) (hazard second) :=
      add_le_add (Real.sqrt_le_sqrt hcontinue_prod) (Real.sqrt_le_sqrt hquit_prod)
    _ ≤ 1 := pairContinueAmplitude_add_pairQuitAmplitude_le_one
      (hazard_mem first first_mem) (hazard_mem second second_mem)

/-- Total normalized amplitude of zero or exactly one target coalition firing. -/
def zeroOrOneActivationAmplitude
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (stay fire : Index → ℝ) : ℝ :=
  (∏ index ∈ indices, stay index) +
    ∑ active ∈ indices,
      fire active * ∏ index ∈ indices.erase active, stay index

theorem zeroOrOneActivationAmplitude_insert
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (stay fire : Index → ℝ)
    {new : Index} (new_not_mem : new ∉ indices) :
    zeroOrOneActivationAmplitude (insert new indices) stay fire =
      stay new * zeroOrOneActivationAmplitude indices stay fire +
        fire new * ∏ index ∈ indices, stay index := by
  simp only [zeroOrOneActivationAmplitude, Finset.prod_insert new_not_mem,
    Finset.sum_insert new_not_mem, Finset.erase_insert new_not_mem]
  have herase (active : Index) (hactive : active ∈ indices) :
      (insert new indices).erase active = insert new (indices.erase active) := by
    ext index
    simp only [Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨index_ne, rfl | index_mem⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨index_ne, index_mem⟩
    · rintro (rfl | ⟨index_ne, index_mem⟩)
      · exact ⟨by exact fun h => new_not_mem (h ▸ hactive), Or.inl rfl⟩
      · exact ⟨index_ne, Or.inr index_mem⟩
  rw [Finset.sum_congr rfl fun active hactive => show
      fire active * ∏ index ∈ (insert new indices).erase active, stay index =
        stay new *
          (fire active * ∏ index ∈ indices.erase active, stay index) by
    rw [herase active hactive, Finset.prod_insert]
    · ring
    · simp [new_not_mem]]
  rw [← Finset.mul_sum]
  ring

/-- The zero-or-one part of a product expansion is bounded by the complete product. -/
theorem zeroOrOneActivationAmplitude_le_prod_add
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (stay fire : Index → ℝ)
    (stay_nonneg : ∀ index ∈ indices, 0 ≤ stay index)
    (fire_nonneg : ∀ index ∈ indices, 0 ≤ fire index) :
    zeroOrOneActivationAmplitude indices stay fire ≤
      ∏ index ∈ indices, (stay index + fire index) := by
  induction indices using Finset.induction_on with
  | empty => simp [zeroOrOneActivationAmplitude]
  | @insert new indices new_not_mem ih =>
      rw [zeroOrOneActivationAmplitude_insert indices stay fire new_not_mem,
        Finset.prod_insert new_not_mem]
      have hstay := stay_nonneg new (Finset.mem_insert_self new indices)
      have hfire := fire_nonneg new (Finset.mem_insert_self new indices)
      have ih' := ih
        (fun index hindex => stay_nonneg index (Finset.mem_insert_of_mem hindex))
        (fun index hindex => fire_nonneg index (Finset.mem_insert_of_mem hindex))
      have hprod_nonneg :
          0 ≤ ∏ index ∈ indices, stay index :=
        Finset.prod_nonneg fun index hindex =>
          stay_nonneg index (Finset.mem_insert_of_mem hindex)
      have hfull_nonneg :
          0 ≤ ∏ index ∈ indices, (stay index + fire index) :=
        Finset.prod_nonneg fun index hindex => add_nonneg
          (stay_nonneg index (Finset.mem_insert_of_mem hindex))
          (fire_nonneg index (Finset.mem_insert_of_mem hindex))
      calc
        stay new * zeroOrOneActivationAmplitude indices stay fire +
            fire new * ∏ index ∈ indices, stay index ≤
          stay new * ∏ index ∈ indices, (stay index + fire index) +
            fire new * ∏ index ∈ indices, (stay index + fire index) :=
          add_le_add (mul_le_mul_of_nonneg_left ih' hstay)
            (mul_le_mul_of_nonneg_left
              (show (∏ index ∈ indices, stay index) ≤
                  ∏ index ∈ indices, (stay index + fire index) by
                apply Finset.prod_le_prod
                · exact fun index hindex =>
                    stay_nonneg index (Finset.mem_insert_of_mem hindex)
                · intro index hindex
                  exact le_add_of_nonneg_right
                    (fire_nonneg index (Finset.mem_insert_of_mem hindex)))
              hfire)
        _ = (stay new + fire new) *
            ∏ index ∈ indices, (stay index + fire index) := by ring

/-- Square-root simplex law for any finite family of disjoint non-singleton gate amplitudes,
expressed at the normalized local level. -/
theorem zeroOrOneActivationAmplitude_le_one
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (stay fire : Index → ℝ)
    (stay_nonneg : ∀ index ∈ indices, 0 ≤ stay index)
    (fire_nonneg : ∀ index ∈ indices, 0 ≤ fire index)
    (pair_bound : ∀ index ∈ indices, stay index + fire index ≤ 1) :
    zeroOrOneActivationAmplitude indices stay fire ≤ 1 := by
  calc
    zeroOrOneActivationAmplitude indices stay fire ≤
        ∏ index ∈ indices, (stay index + fire index) :=
      zeroOrOneActivationAmplitude_le_prod_add
        indices stay fire stay_nonneg fire_nonneg
    _ ≤ ∏ _index ∈ indices, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · exact fun index hindex => add_nonneg
          (stay_nonneg index hindex) (fire_nonneg index hindex)
      · exact pair_bound
    _ = 1 := by simp

/-- Hazard adapter for the multi-coalition square-root simplex law.  When the displayed
coalitions are pairwise disjoint, this zero-or-one activation amplitude is exactly the normalized
amplitude of all-Continue together with the displayed exact-coalition atoms. -/
theorem coalitionFamily_zeroOrOneActivationAmplitude_le_one
    {Player Group : Type*} [DecidableEq Player] [DecidableEq Group]
    (targets : Finset Group) (coalition : Group → Finset Player)
    (hazard : Player → ℝ)
    (card_ge_two : ∀ group ∈ targets, 2 ≤ (coalition group).card)
    (hazard_mem : ∀ group ∈ targets, ∀ player ∈ coalition group,
      hazard player ∈ Set.Icc (0 : ℝ) 1) :
    zeroOrOneActivationAmplitude targets
        (fun group => coalitionContinueAmplitude (coalition group) hazard)
        (fun group => coalitionQuitAmplitude (coalition group) hazard) ≤ 1 := by
  apply zeroOrOneActivationAmplitude_le_one
  · exact fun _ _ => Real.sqrt_nonneg _
  · exact fun _ _ => Real.sqrt_nonneg _
  · intro group hgroup
    exact coalitionContinueAmplitude_add_quitAmplitude_le_one
      (coalition group) hazard (card_ge_two group hgroup)
      (hazard_mem group hgroup)

/-! ## Counterfactual reach after deleting one player's hazards -/

/-- All-player Continue probability over a finite set of dates and players. -/
def finiteJointContinueClock
    {Player : Type*} [DecidableEq Player]
    (dates : Finset ℕ) (players : Finset Player)
    (hazard : ℕ → Player → ℝ) : ℝ :=
  ∏ time ∈ dates, ∏ player ∈ players, (1 - hazard time player)

/-- Opponent Continue probability over the same dates, after forcing `who` to Continue. -/
def finiteDeletedContinueClock
    {Player : Type*} [DecidableEq Player]
    (dates : Finset ℕ) (players : Finset Player)
    (hazard : ℕ → Player → ℝ) (who : Player) : ℝ :=
  ∏ time ∈ dates,
    ∏ player ∈ players.erase who, (1 - hazard time player)

theorem finiteJointContinueClock_nonneg
    {Player : Type*} [DecidableEq Player]
    (dates : Finset ℕ) (players : Finset Player)
    (hazard : ℕ → Player → ℝ)
    (hazard_le_one : ∀ time ∈ dates, ∀ player ∈ players, hazard time player ≤ 1) :
    0 ≤ finiteJointContinueClock dates players hazard := by
  apply Finset.prod_nonneg
  intro time htime
  apply Finset.prod_nonneg
  intro player hplayer
  exact sub_nonneg.mpr (hazard_le_one time htime player hplayer)

theorem finiteDeletedContinueClock_nonneg
    {Player : Type*} [DecidableEq Player]
    (dates : Finset ℕ) (players : Finset Player)
    (hazard : ℕ → Player → ℝ) (who : Player)
    (hazard_le_one : ∀ time ∈ dates, ∀ player ∈ players, hazard time player ≤ 1) :
    0 ≤ finiteDeletedContinueClock dates players hazard who := by
  apply Finset.prod_nonneg
  intro time htime
  apply Finset.prod_nonneg
  intro player hplayer
  exact sub_nonneg.mpr
    (hazard_le_one time htime player (Finset.mem_of_mem_erase hplayer))

theorem finiteDeletedContinueClock_le_one
    {Player : Type*} [DecidableEq Player]
    (dates : Finset ℕ) (players : Finset Player)
    (hazard : ℕ → Player → ℝ) (who : Player)
    (hazard_mem : ∀ time ∈ dates, ∀ player ∈ players,
      hazard time player ∈ Set.Icc (0 : ℝ) 1) :
    finiteDeletedContinueClock dates players hazard who ≤ 1 := by
  apply Finset.prod_le_one
  · intro time htime
    exact Finset.prod_nonneg fun player hplayer => sub_nonneg.mpr
      (hazard_mem time htime player (Finset.mem_of_mem_erase hplayer)).2
  · intro time htime
    apply Finset.prod_le_one
    · intro player hplayer
      exact sub_nonneg.mpr
        (hazard_mem time htime player (Finset.mem_of_mem_erase hplayer)).2
    · intro player hplayer
      linarith [
        (hazard_mem time htime player (Finset.mem_of_mem_erase hplayer)).1]

/-- Deleting one coordinate can only increase the all-Continue clock. -/
theorem finiteJointContinueClock_le_deleted
    {Player : Type*} [DecidableEq Player]
    (dates : Finset ℕ) (players : Finset Player)
    (hazard : ℕ → Player → ℝ) (who : Player) (who_mem : who ∈ players)
    (hazard_mem : ∀ time ∈ dates, ∀ player ∈ players,
      hazard time player ∈ Set.Icc (0 : ℝ) 1) :
    finiteJointContinueClock dates players hazard ≤
      finiteDeletedContinueClock dates players hazard who := by
  apply Finset.prod_le_prod
  · intro time htime
    exact Finset.prod_nonneg fun player hplayer =>
      sub_nonneg.mpr (hazard_mem time htime player hplayer).2
  · intro time htime
    have hdeleted_nonneg :
        0 ≤ ∏ player ∈ players.erase who, (1 - hazard time player) :=
      Finset.prod_nonneg fun player hplayer => sub_nonneg.mpr
        (hazard_mem time htime player (Finset.mem_of_mem_erase hplayer)).2
    have hfactor :
        (∏ player ∈ players.erase who, (1 - hazard time player)) *
            (1 - hazard time who) =
          ∏ player ∈ players, (1 - hazard time player) :=
      Finset.prod_erase_mul (s := players)
        (f := fun player => 1 - hazard time player) (a := who) who_mem
    rw [← hfactor]
    calc
      (∏ player ∈ players.erase who, (1 - hazard time player)) *
          (1 - hazard time who) ≤
        (∏ player ∈ players.erase who, (1 - hazard time player)) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith [(hazard_mem time htime who who_mem).1])
          hdeleted_nonneg
      _ = ∏ player ∈ players.erase who, (1 - hazard time player) := mul_one _

/-- Explicit changed-reach comparison.  If the baseline reaches a window with probability at
least `reachFloor`, then forcing one player to Continue can increase that window's unconditional
opponent absorption by at most the reciprocal reach factor. -/
theorem deletedCounterfactualAbsorption_le_div
    {jointContinue deletedContinue baselineReach changedReach baselineAbsorption reachFloor : ℝ}
    (joint_nonneg : 0 ≤ jointContinue)
    (joint_le_deleted : jointContinue ≤ deletedContinue)
    (deleted_le_one : deletedContinue ≤ 1)
    (baselineReach_ge : reachFloor ≤ baselineReach)
    (reachFloor_pos : 0 < reachFloor)
    (changedReach_mem : changedReach ∈ Set.Icc (0 : ℝ) 1)
    (baselineAbsorption_eq :
      baselineAbsorption = baselineReach * (1 - jointContinue)) :
    changedReach * (1 - deletedContinue) ≤ baselineAbsorption / reachFloor := by
  have hdeleted_nonneg : 0 ≤ deletedContinue := joint_nonneg.trans joint_le_deleted
  have hone_sub_deleted : 0 ≤ 1 - deletedContinue := sub_nonneg.mpr deleted_le_one
  have hchanged :
      changedReach * (1 - deletedContinue) ≤ 1 - jointContinue := by
    calc
      changedReach * (1 - deletedContinue) ≤ 1 * (1 - deletedContinue) :=
        mul_le_mul_of_nonneg_right changedReach_mem.2 hone_sub_deleted
      _ ≤ 1 - jointContinue := by linarith
  have hone_sub_joint : 0 ≤ 1 - jointContinue := by linarith
  have hscaled :
      reachFloor * (changedReach * (1 - deletedContinue)) ≤ baselineAbsorption := by
    rw [baselineAbsorption_eq]
    exact (mul_le_mul_of_nonneg_left hchanged reachFloor_pos.le).trans
      (mul_le_mul_of_nonneg_right baselineReach_ge hone_sub_joint)
  exact (le_div_iff₀ reachFloor_pos).2
    (by simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled)

/-- Source-native finite-window version of `deletedCounterfactualAbsorption_le_div`. -/
theorem finiteClock_deletedCounterfactualAbsorption_le_div
    {Player : Type*} [DecidableEq Player]
    (dates : Finset ℕ) (players : Finset Player)
    (hazard : ℕ → Player → ℝ) (who : Player) (who_mem : who ∈ players)
    (hazard_mem : ∀ time ∈ dates, ∀ player ∈ players,
      hazard time player ∈ Set.Icc (0 : ℝ) 1)
    {baselineReach changedReach baselineAbsorption reachFloor : ℝ}
    (baselineReach_ge : reachFloor ≤ baselineReach)
    (reachFloor_pos : 0 < reachFloor)
    (changedReach_mem : changedReach ∈ Set.Icc (0 : ℝ) 1)
    (baselineAbsorption_eq : baselineAbsorption = baselineReach *
      (1 - finiteJointContinueClock dates players hazard)) :
    changedReach * (1 - finiteDeletedContinueClock dates players hazard who) ≤
      baselineAbsorption / reachFloor := by
  apply deletedCounterfactualAbsorption_le_div
    (finiteJointContinueClock_nonneg dates players hazard
      (fun time htime player hplayer => (hazard_mem time htime player hplayer).2))
    (finiteJointContinueClock_le_deleted
      dates players hazard who who_mem hazard_mem)
    (finiteDeletedContinueClock_le_one dates players hazard who hazard_mem)
    baselineReach_ge reachFloor_pos changedReach_mem baselineAbsorption_eq

/-- Two-window comparison used around the selected gates.  The pre-gate window has unit source
reach.  The between-gates window costs exactly the reciprocal of its baseline reach floor. -/
theorem finiteClock_twoWindowDeletedAbsorption_le
    {Player : Type*} [DecidableEq Player]
    (before between : Finset ℕ) (players : Finset Player)
    (hazard : ℕ → Player → ℝ) (who : Player) (who_mem : who ∈ players)
    (hazard_mem : ∀ time ∈ before ∪ between, ∀ player ∈ players,
      hazard time player ∈ Set.Icc (0 : ℝ) 1)
    {betweenBaselineReach changedBeforeReach changedBetweenReach : ℝ}
    {beforeAbsorption betweenAbsorption reachFloor : ℝ}
    (betweenBaselineReach_ge : reachFloor ≤ betweenBaselineReach)
    (reachFloor_pos : 0 < reachFloor)
    (changedBeforeReach_mem : changedBeforeReach ∈ Set.Icc (0 : ℝ) 1)
    (changedBetweenReach_mem : changedBetweenReach ∈ Set.Icc (0 : ℝ) 1)
    (beforeAbsorption_eq : beforeAbsorption =
      1 * (1 - finiteJointContinueClock before players hazard))
    (betweenAbsorption_eq : betweenAbsorption = betweenBaselineReach *
      (1 - finiteJointContinueClock between players hazard)) :
    changedBeforeReach *
          (1 - finiteDeletedContinueClock before players hazard who) +
        changedBetweenReach *
          (1 - finiteDeletedContinueClock between players hazard who) ≤
      beforeAbsorption + betweenAbsorption / reachFloor := by
  have hbefore_mem : ∀ time ∈ before, ∀ player ∈ players,
      hazard time player ∈ Set.Icc (0 : ℝ) 1 := by
    intro time htime player hplayer
    exact hazard_mem time (Finset.mem_union_left between htime) player hplayer
  have hbetween_mem : ∀ time ∈ between, ∀ player ∈ players,
      hazard time player ∈ Set.Icc (0 : ℝ) 1 := by
    intro time htime player hplayer
    exact hazard_mem time (Finset.mem_union_right before htime) player hplayer
  have hbefore := finiteClock_deletedCounterfactualAbsorption_le_div
    before players hazard who who_mem hbefore_mem
    (baselineReach_ge := le_rfl) (reachFloor_pos := zero_lt_one)
    changedBeforeReach_mem beforeAbsorption_eq
  have hbetween := finiteClock_deletedCounterfactualAbsorption_le_div
    between players hazard who who_mem hbetween_mem
    betweenBaselineReach_ge reachFloor_pos changedBetweenReach_mem betweenAbsorption_eq
  simpa using add_le_add hbefore hbetween

/-! ## Finite-horizon global ledger -/

/-- A finite local square-root conservation law telescopes exactly. -/
theorem sum_localSquareRootDefect_add_endpoint
    (x y z defect : ℕ → ℝ) (horizon : ℕ)
    (initial : z 0 = 1)
    (local_eq : ∀ time, time < horizon →
      x time + y time + defect time + z (time + 1) = z time) :
    (∑ time ∈ Finset.range horizon, x time) +
        (∑ time ∈ Finset.range horizon, y time) +
        (∑ time ∈ Finset.range horizon, defect time) + z horizon = 1 := by
  induction horizon with
  | zero => simpa using initial
  | succ horizon ih =>
      have ih' := ih (fun time htime =>
        local_eq time (Nat.lt_trans htime (Nat.lt_succ_self _)))
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      have hlocal := local_eq horizon (Nat.lt_succ_self horizon)
      linarith

/-- On a finite index set, the Euclidean norm of a nonnegative vector is at most its `L¹` norm. -/
theorem sqrt_sum_sq_le_sum_of_nonneg
    {Index : Type*} (indices : Finset Index) (amplitude : Index → ℝ)
    (nonneg : ∀ index ∈ indices, 0 ≤ amplitude index) :
    Real.sqrt (∑ index ∈ indices, amplitude index ^ 2) ≤
      ∑ index ∈ indices, amplitude index := by
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg nonneg
  have hsum : 0 ≤ ∑ index ∈ indices, amplitude index :=
    Finset.sum_nonneg nonneg
  calc
    Real.sqrt (∑ index ∈ indices, amplitude index ^ 2) ≤
        Real.sqrt ((∑ index ∈ indices, amplitude index) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = ∑ index ∈ indices, amplitude index := Real.sqrt_sq hsum

/-- A target amplitude whose maximum occurs at `peak` has at most twice its `L¹-L²` defect away
from that date.  This is the scale-free temporal concentration estimate used near equality. -/
theorem sum_erase_le_two_mul_sum_sub_sqrt_sum_sq
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (amplitude : Index → ℝ) (peak : Index)
    (peak_mem : peak ∈ indices)
    (nonneg : ∀ index ∈ indices, 0 ≤ amplitude index)
    (maximal : ∀ index ∈ indices, amplitude index ≤ amplitude peak) :
    (∑ index ∈ indices.erase peak, amplitude index) ≤
      2 * ((∑ index ∈ indices, amplitude index) -
        Real.sqrt (∑ index ∈ indices, amplitude index ^ 2)) := by
  let total := ∑ index ∈ indices, amplitude index
  let squareTotal := ∑ index ∈ indices, amplitude index ^ 2
  have hpeak_nonneg : 0 ≤ amplitude peak := nonneg peak peak_mem
  have htotal_nonneg : 0 ≤ total := Finset.sum_nonneg nonneg
  have hsquare_nonneg : 0 ≤ squareTotal :=
    Finset.sum_nonneg fun index _ => sq_nonneg (amplitude index)
  have hsquare_le : squareTotal ≤ amplitude peak * total := by
    dsimp only [squareTotal, total]
    calc
      (∑ index ∈ indices, amplitude index ^ 2) ≤
          ∑ index ∈ indices, amplitude peak * amplitude index := by
        apply Finset.sum_le_sum
        intro index hindex
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (maximal index hindex) (nonneg index hindex)
      _ = amplitude peak * ∑ index ∈ indices, amplitude index := by
        rw [Finset.mul_sum]
  have hsqrt_sq := Real.sq_sqrt hsquare_nonneg
  have htwice_sqrt :
      2 * Real.sqrt squareTotal ≤ total + amplitude peak := by
    have hsum_nonneg : 0 ≤ total + amplitude peak := add_nonneg htotal_nonneg hpeak_nonneg
    by_contra hnot
    have hstrict : total + amplitude peak < 2 * Real.sqrt squareTotal :=
      lt_of_not_ge hnot
    nlinarith [sq_nonneg (total - amplitude peak), Real.sqrt_nonneg squareTotal]
  have herase :
      (∑ index ∈ indices.erase peak, amplitude index) + amplitude peak = total := by
    simpa [total] using Finset.sum_erase_add indices amplitude peak_mem
  linarith

/-- Division-free exact global defect decomposition.  The last two terms are the temporal
splitting defects of the two target amplitudes. -/
theorem finite_twoTarget_global_defect_eq
    (x y z defect : ℕ → ℝ) (horizon : ℕ)
    (initial : z 0 = 1)
    (local_eq : ∀ time, time < horizon →
      x time + y time + defect time + z (time + 1) = z time) :
    1 - Real.sqrt (∑ time ∈ Finset.range horizon, x time ^ 2) -
        Real.sqrt (∑ time ∈ Finset.range horizon, y time ^ 2) =
      z horizon + (∑ time ∈ Finset.range horizon, defect time) +
        ((∑ time ∈ Finset.range horizon, x time) -
          Real.sqrt (∑ time ∈ Finset.range horizon, x time ^ 2)) +
        ((∑ time ∈ Finset.range horizon, y time) -
          Real.sqrt (∑ time ∈ Finset.range horizon, y time ^ 2)) := by
  have htelescope := sum_localSquareRootDefect_add_endpoint
    x y z defect horizon initial local_eq
  linarith

/-- A local square-root conservation row controls its actual absorption probability. -/
theorem sq_survival_sub_sq_next_le_two_mul_charge
    {current next x y defect : ℝ}
    (current_mem : current ∈ Set.Icc (0 : ℝ) 1)
    (_next_mem : next ∈ Set.Icc (0 : ℝ) 1)
    (local_eq : x + y + defect + next = current)
    (charge_nonneg : 0 ≤ x + y + defect) :
    current ^ 2 - next ^ 2 ≤ 2 * (x + y + defect) := by
  have hsum : current + next ≤ 2 := by linarith [current_mem.2, _next_mem.2]
  have hdiff : current - next = x + y + defect := by linarith
  calc
    current ^ 2 - next ^ 2 = (current - next) * (current + next) := by ring
    _ = (x + y + defect) * (current + next) := by rw [hdiff]
    _ ≤ (x + y + defect) * 2 :=
      mul_le_mul_of_nonneg_left hsum charge_nonneg
    _ = 2 * (x + y + defect) := by ring

/-- The local conservation identity telescopes on any finite half-open interval. -/
theorem sum_Ico_charge_add_endpoint
    (x y defect z : ℕ → ℝ) {start horizon : ℕ} (hle : start ≤ horizon)
    (local_eq : ∀ time, time < horizon →
      x time + y time + defect time + z (time + 1) = z time) :
    (∑ time ∈ Finset.Ico start horizon, x time) +
        (∑ time ∈ Finset.Ico start horizon, y time) +
        (∑ time ∈ Finset.Ico start horizon, defect time) + z horizon =
      z start := by
  have hpointwise : ∀ time ∈ Finset.Ico start horizon,
      x time + y time + defect time = z time - z (time + 1) := by
    intro time htime
    have htime_lt : time < horizon := (Finset.mem_Ico.mp htime).2
    linarith [local_eq time htime_lt]
  have hsum :
      ∑ time ∈ Finset.Ico start horizon,
          (x time + y time + defect time) = z start - z horizon := by
    rw [Finset.sum_congr rfl hpointwise, Finset.sum_Ico_eq_sub _ hle,
      Finset.sum_range_sub', Finset.sum_range_sub']
    ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  linarith

/-- Exact quantitative chronology of two dominant amplitudes.  The constants `10,10,6` are
consequences of the global square-root defect ledger, rather than asymptotic notation. -/
theorem finite_twoTarget_dominant_chronology_bounds
    (x y z defect : ℕ → ℝ) (horizon firstPeak secondPeak : ℕ)
    (firstPeak_mem : firstPeak ∈ Finset.range horizon)
    (secondPeak_mem : secondPeak ∈ Finset.range horizon)
    (peaks_order : firstPeak < secondPeak)
    (x_nonneg : ∀ time, 0 ≤ x time)
    (y_nonneg : ∀ time, 0 ≤ y time)
    (defect_nonneg : ∀ time, 0 ≤ defect time)
    (z_mem : ∀ time, time ≤ horizon → z time ∈ Set.Icc (0 : ℝ) 1)
    (initial : z 0 = 1)
    (local_eq : ∀ time, time < horizon →
      x time + y time + defect time + z (time + 1) = z time)
    (first_maximal : ∀ time ∈ Finset.range horizon, x time ≤ x firstPeak)
    (second_maximal : ∀ time ∈ Finset.range horizon, y time ≤ y secondPeak) :
    let delta := 1 - Real.sqrt (∑ time ∈ Finset.range horizon, x time ^ 2) -
      Real.sqrt (∑ time ∈ Finset.range horizon, y time ^ 2)
    (∑ time ∈ Finset.range firstPeak, (z time ^ 2 - z (time + 1) ^ 2)) ≤
        10 * delta ∧
      (∑ time ∈ Finset.Ico (firstPeak + 1) secondPeak,
        (z time ^ 2 - z (time + 1) ^ 2)) ≤ 10 * delta ∧
      z (secondPeak + 1) ≤ 6 * delta := by
  dsimp only
  let firstSplit := (∑ time ∈ Finset.range horizon, x time) -
    Real.sqrt (∑ time ∈ Finset.range horizon, x time ^ 2)
  let secondSplit := (∑ time ∈ Finset.range horizon, y time) -
    Real.sqrt (∑ time ∈ Finset.range horizon, y time ^ 2)
  let delta := 1 - Real.sqrt (∑ time ∈ Finset.range horizon, x time ^ 2) -
    Real.sqrt (∑ time ∈ Finset.range horizon, y time ^ 2)
  have hledger := finite_twoTarget_global_defect_eq
    x y z defect horizon initial local_eq
  change delta = z horizon + (∑ time ∈ Finset.range horizon, defect time) +
    firstSplit + secondSplit at hledger
  have hfirstSplit_nonneg : 0 ≤ firstSplit := by
    dsimp only [firstSplit]
    exact sub_nonneg.mpr (sqrt_sum_sq_le_sum_of_nonneg
      (Finset.range horizon) x (fun time _ => x_nonneg time))
  have hsecondSplit_nonneg : 0 ≤ secondSplit := by
    dsimp only [secondSplit]
    exact sub_nonneg.mpr (sqrt_sum_sq_le_sum_of_nonneg
      (Finset.range horizon) y (fun time _ => y_nonneg time))
  have hz_endpoint_nonneg : 0 ≤ z horizon := (z_mem horizon le_rfl).1
  have hdefectSum_nonneg : 0 ≤ ∑ time ∈ Finset.range horizon, defect time :=
    Finset.sum_nonneg fun time _ => defect_nonneg time
  have hfirstSplit_le : firstSplit ≤ delta := by linarith
  have hsecondSplit_le : secondSplit ≤ delta := by linarith
  have hdefectSum_le :
      (∑ time ∈ Finset.range horizon, defect time) ≤ delta := by linarith
  have hz_endpoint_le : z horizon ≤ delta := by linarith
  have hxAway := sum_erase_le_two_mul_sum_sub_sqrt_sum_sq
    (Finset.range horizon) x firstPeak firstPeak_mem
    (fun time _ => x_nonneg time) first_maximal
  have hyAway := sum_erase_le_two_mul_sum_sub_sqrt_sum_sq
    (Finset.range horizon) y secondPeak secondPeak_mem
    (fun time _ => y_nonneg time) second_maximal
  change (∑ time ∈ (Finset.range horizon).erase firstPeak, x time) ≤
    2 * firstSplit at hxAway
  change (∑ time ∈ (Finset.range horizon).erase secondPeak, y time) ≤
    2 * secondSplit at hyAway
  have hsubset_bound (dates excluded : Finset ℕ) (amplitude : ℕ → ℝ)
      (subset : dates ⊆ excluded) (nonneg : ∀ time, 0 ≤ amplitude time) :
      (∑ time ∈ dates, amplitude time) ≤
        ∑ time ∈ excluded, amplitude time := by
    apply Finset.sum_le_sum_of_subset_of_nonneg subset
    exact fun time _ _ => nonneg time
  have hbefore_subset_first : Finset.range firstPeak ⊆
      (Finset.range horizon).erase firstPeak := by
    intro time htime
    simp only [Finset.mem_range, Finset.mem_erase]
    have ht := Finset.mem_range.mp htime
    exact ⟨Nat.ne_of_lt ht, ht.trans (Finset.mem_range.mp firstPeak_mem)⟩
  have hbefore_subset_second : Finset.range firstPeak ⊆
      (Finset.range horizon).erase secondPeak := by
    intro time htime
    simp only [Finset.mem_range, Finset.mem_erase]
    have ht := Finset.mem_range.mp htime
    exact ⟨Nat.ne_of_lt (ht.trans peaks_order),
      (ht.trans peaks_order).trans (Finset.mem_range.mp secondPeak_mem)⟩
  let middle := Finset.Ico (firstPeak + 1) secondPeak
  have hmiddle_subset_first : middle ⊆ (Finset.range horizon).erase firstPeak := by
    intro time htime
    have ht := Finset.mem_Ico.mp htime
    simp only [Finset.mem_erase, Finset.mem_range]
    exact ⟨by omega, ht.2.trans (Finset.mem_range.mp secondPeak_mem)⟩
  have hmiddle_subset_second : middle ⊆ (Finset.range horizon).erase secondPeak := by
    intro time htime
    have ht := Finset.mem_Ico.mp htime
    simp only [Finset.mem_erase, Finset.mem_range]
    exact ⟨Nat.ne_of_lt ht.2, ht.2.trans (Finset.mem_range.mp secondPeak_mem)⟩
  have hcharge (time : ℕ) (htime : time < horizon) :
      z time ^ 2 - z (time + 1) ^ 2 ≤ 2 * (x time + y time + defect time) :=
    sq_survival_sub_sq_next_le_two_mul_charge
      (z_mem time htime.le) (z_mem (time + 1) htime) (local_eq time htime)
      (add_nonneg (add_nonneg (x_nonneg time) (y_nonneg time)) (defect_nonneg time))
  have hsum_charge (dates : Finset ℕ) (dates_subset : dates ⊆ Finset.range horizon) :
      (∑ time ∈ dates, (z time ^ 2 - z (time + 1) ^ 2)) ≤
        2 * ((∑ time ∈ dates, x time) +
          (∑ time ∈ dates, y time) +
          (∑ time ∈ dates, defect time)) := by
    calc
      (∑ time ∈ dates, (z time ^ 2 - z (time + 1) ^ 2)) ≤
          ∑ time ∈ dates, 2 * (x time + y time + defect time) := by
        apply Finset.sum_le_sum
        intro time htime
        exact hcharge time (Finset.mem_range.mp (dates_subset htime))
      _ = 2 * ((∑ time ∈ dates, x time) +
          (∑ time ∈ dates, y time) +
          (∑ time ∈ dates, defect time)) := by
        simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hbefore_defect := hsubset_bound (Finset.range firstPeak)
    (Finset.range horizon) defect (Finset.range_mono
      (Finset.mem_range.mp firstPeak_mem).le) defect_nonneg
  have hmiddle_defect := hsubset_bound middle (Finset.range horizon) defect
    (fun time htime => by
      exact Finset.mem_range.mpr ((Finset.mem_Ico.mp htime).2.trans
        (Finset.mem_range.mp secondPeak_mem))) defect_nonneg
  have hbefore_charge := hsum_charge (Finset.range firstPeak)
    (Finset.range_mono (Finset.mem_range.mp firstPeak_mem).le)
  have hmiddle_charge := hsum_charge middle (fun time htime =>
    Finset.mem_range.mpr ((Finset.mem_Ico.mp htime).2.trans
      (Finset.mem_range.mp secondPeak_mem)))
  have htailConservation := sum_Ico_charge_add_endpoint x y defect z
    (Nat.succ_le_of_lt (Finset.mem_range.mp secondPeak_mem)) local_eq
  have htailX := hsubset_bound (Finset.Ico (secondPeak + 1) horizon)
    ((Finset.range horizon).erase firstPeak) x (by
      intro time htime
      have ht := Finset.mem_Ico.mp htime
      simp only [Finset.mem_erase, Finset.mem_range]
      exact ⟨by omega, ht.2⟩) x_nonneg
  have htailY := hsubset_bound (Finset.Ico (secondPeak + 1) horizon)
    ((Finset.range horizon).erase secondPeak) y (by
      intro time htime
      have ht := Finset.mem_Ico.mp htime
      simp only [Finset.mem_erase, Finset.mem_range]
      exact ⟨by omega, ht.2⟩) y_nonneg
  have htailDefect := hsubset_bound (Finset.Ico (secondPeak + 1) horizon)
    (Finset.range horizon) defect (by
      intro time htime
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp htime).2) defect_nonneg
  change (∑ time ∈ Finset.Ico (secondPeak + 1) horizon, x time) +
      (∑ time ∈ Finset.Ico (secondPeak + 1) horizon, y time) +
      (∑ time ∈ Finset.Ico (secondPeak + 1) horizon, defect time) +
        z horizon = z (secondPeak + 1) at htailConservation
  constructor
  · calc
      _ ≤ 2 * ((∑ time ∈ Finset.range firstPeak, x time) +
          (∑ time ∈ Finset.range firstPeak, y time) +
          (∑ time ∈ Finset.range firstPeak, defect time)) := hbefore_charge
      _ ≤ 10 * delta := by
        have hx := hsubset_bound _ _ x hbefore_subset_first x_nonneg
        have hy := hsubset_bound _ _ y hbefore_subset_second y_nonneg
        linarith
  · constructor
    · change (∑ time ∈ middle, (z time ^ 2 - z (time + 1) ^ 2)) ≤ _
      calc
        _ ≤ 2 * ((∑ time ∈ middle, x time) +
            (∑ time ∈ middle, y time) +
            (∑ time ∈ middle, defect time)) := hmiddle_charge
        _ ≤ 10 * delta := by
          have hx := hsubset_bound _ _ x hmiddle_subset_first x_nonneg
          have hy := hsubset_bound _ _ y hmiddle_subset_second y_nonneg
          linarith
    · rw [← htailConservation]
      linarith

/-- Finite-horizon global square-root simplex inequality obtained from the exact local ledger. -/
theorem sqrt_targetMass_add_sqrt_targetMass_le_one
    (x y z defect : ℕ → ℝ) (horizon : ℕ)
    (x_nonneg : ∀ time, 0 ≤ x time) (y_nonneg : ∀ time, 0 ≤ y time)
    (z_endpoint_nonneg : 0 ≤ z horizon)
    (defect_nonneg : ∀ time, 0 ≤ defect time)
    (initial : z 0 = 1)
    (local_eq : ∀ time, time < horizon →
      x time + y time + defect time + z (time + 1) = z time) :
    Real.sqrt (∑ time ∈ Finset.range horizon, x time ^ 2) +
        Real.sqrt (∑ time ∈ Finset.range horizon, y time ^ 2) ≤ 1 := by
  have hx := sqrt_sum_sq_le_sum_of_nonneg (Finset.range horizon) x
    (fun time _ => x_nonneg time)
  have hy := sqrt_sum_sq_le_sum_of_nonneg (Finset.range horizon) y
    (fun time _ => y_nonneg time)
  have htelescope := sum_localSquareRootDefect_add_endpoint
    x y z defect horizon initial local_eq
  have hdefect : 0 ≤ ∑ time ∈ Finset.range horizon, defect time :=
    Finset.sum_nonneg fun time _ => defect_nonneg time
  linarith

namespace TwoPairHazardClock

/-- Actual finite-horizon square-root simplex bound for the first-coalition masses generated by
two disjoint independent pair clocks. -/
theorem finite_targetMass_sqrt_sum_le_one
    (clock : TwoPairHazardClock) (horizon : ℕ) :
    Real.sqrt (∑ time ∈ Finset.range horizon,
        clock.firstTargetAmplitude time ^ 2) +
      Real.sqrt (∑ time ∈ Finset.range horizon,
        clock.secondTargetAmplitude time ^ 2) ≤ 1 := by
  exact sqrt_targetMass_add_sqrt_targetMass_le_one
    clock.firstTargetAmplitude clock.secondTargetAmplitude
    clock.survivalRoot clock.localDefect horizon
    clock.firstTargetAmplitude_nonneg clock.secondTargetAmplitude_nonneg
    (clock.survivalRoot_nonneg horizon) clock.localDefect_nonneg
    clock.survivalRoot_zero (fun time _ => clock.local_conservation time)

end TwoPairHazardClock

/-- The square-root simplex inequality is equivalent to the sharp lower bound on all leftover
mass, including other coalitions and nonabsorption. -/
theorem twoTarget_leftover_ge_two_sqrt_mul
    {firstMass secondMass : ℝ} (hfirst : 0 ≤ firstMass)
    (hsecond : 0 ≤ secondMass)
    (hsimplex : Real.sqrt firstMass + Real.sqrt secondMass ≤ 1) :
    2 * Real.sqrt (firstMass * secondMass) ≤ 1 - firstMass - secondMass := by
  have hsum_nonneg :
      0 ≤ Real.sqrt firstMass + Real.sqrt secondMass := by positivity
  have hsquare := mul_self_le_mul_self hsum_nonneg hsimplex
  have hfirst_sq := Real.sq_sqrt hfirst
  have hsecond_sq := Real.sq_sqrt hsecond
  have hproduct : Real.sqrt (firstMass * secondMass) =
      Real.sqrt firstMass * Real.sqrt secondMass :=
    Real.sqrt_mul hfirst secondMass
  rw [hproduct]
  nlinarith

/-- Squared form of the two-target independent-clock obstruction. -/
theorem four_mul_twoTargetMass_le_leftover_sq
    {firstMass secondMass : ℝ} (hfirst : 0 ≤ firstMass)
    (hsecond : 0 ≤ secondMass)
    (hsimplex : Real.sqrt firstMass + Real.sqrt secondMass ≤ 1) :
    4 * firstMass * secondMass ≤ (1 - firstMass - secondMass) ^ 2 := by
  have hleftover := twoTarget_leftover_ge_two_sqrt_mul hfirst hsecond hsimplex
  have hsqrt_nonneg : 0 ≤ 2 * Real.sqrt (firstMass * secondMass) := by positivity
  have hsquare := mul_self_le_mul_self hsqrt_nonneg hleftover
  have hproduct_nonneg : 0 ≤ firstMass * secondMass := mul_nonneg hfirst hsecond
  have hsqrt_sq := Real.sq_sqrt hproduct_nonneg
  nlinarith

end

end Math.Probability
